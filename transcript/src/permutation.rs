use circuitry::{
    chip::{first_degree::FirstDegreeChip, second_degree::SecondDegreeChip},
    witness::{Scaled, Witness},
};
use halo2::halo2curves::ff::PrimeField;
use poseidon::{SparseMDSMatrix, Spec, State};

/// `PoseidonChip` is basically responsible for contraining permutation part of
/// transcript pipeline
#[derive(Debug, Clone)]
pub struct PoseidonChip<F: PrimeField, const T: usize, const RATE: usize> {
    state: [Witness<F>; T],
    absorbing: Vec<Witness<F>>,
    spec: Spec<F, T, RATE>,
}

impl<F: PrimeField + Ord, const T: usize, const RATE: usize> PoseidonChip<F, T, RATE> {
    // Constructs new hasher chip with assigned initial state
    pub fn new(stack: &mut impl FirstDegreeChip<F>, spec: &Spec<F, T, RATE>) -> Self {
        let initial_state = State::<_, T>::default()
            .words()
            .iter()
            .map(|word| stack.get_constant(*word))
            .collect::<Vec<_>>();

        Self {
            state: initial_state.try_into().unwrap(),
            spec: spec.clone(),
            absorbing: vec![],
        }
    }

    /// Appends field elements to the absorbation line. It won't perform
    /// permutation here
    pub fn update(&mut self, elements: &[Witness<F>]) {
        self.absorbing.extend_from_slice(elements);
    }
}

impl<F: PrimeField, const T: usize, const RATE: usize> PoseidonChip<F, T, RATE> {
    /*
        Internally expose poseidion parameters and matrices
    */

    pub(super) fn r_f_half(&self) -> usize {
        self.spec.r_f() / 2
    }

    pub(super) fn constants_start(&self) -> Vec<[F; T]> {
        self.spec.constants().start().clone()
    }

    pub(super) fn constants_partial(&self) -> Vec<F> {
        self.spec.constants().partial().clone()
    }

    pub(super) fn constants_end(&self) -> Vec<[F; T]> {
        self.spec.constants().end().clone()
    }

    pub(super) fn mds(&self) -> [[F; T]; T] {
        self.spec.mds_matrices().mds().rows()
    }

    pub(super) fn pre_sparse_mds(&self) -> [[F; T]; T] {
        self.spec.mds_matrices().pre_sparse_mds().rows()
    }

    pub(super) fn sparse_matrices(&self) -> Vec<SparseMDSMatrix<F, T, RATE>> {
        self.spec.mds_matrices().sparse_matrices().clone()
    }
}

impl<F: PrimeField + Ord, const T: usize, const RATE: usize> PoseidonChip<F, T, RATE> {
    /// Applies full state sbox then adds constants to each word in the state
    fn sbox_full<S: FirstDegreeChip<F> + SecondDegreeChip<F>>(
        &mut self,
        stack: &mut S,
        constants: &[F; T],
    ) {
        for (word, constant) in self.state.iter_mut().zip(constants.iter()) {
            let t = stack.mul(word, word);
            let t = stack.mul(&t, &t);
            *word = stack.mul_add_constant(&t, word, *constant);
        }
    }

    /// Applies sbox to the first word then adds constants to each word in the
    /// state
    fn sbox_part<S: FirstDegreeChip<F> + SecondDegreeChip<F>>(
        &mut self,
        stack: &mut S,
        constant: F,
    ) {
        let word = &mut self.state[0];
        let t = stack.mul(word, word);
        let t = stack.mul(&t, &t);
        *word = stack.mul_add_constant(&t, word, constant);
    }

    // Adds pre constants and chunked inputs to the state.
    fn absorb_with_pre_constants<S: FirstDegreeChip<F> + SecondDegreeChip<F>>(
        &mut self,
        stack: &mut S,
        //
        // * inputs size equals to RATE: absorbing
        // * inputs size is less then RATE but not 0: padding
        // * inputs size is 0: extra permutation to avoid collution
        inputs: Vec<Witness<F>>,
        pre_constants: &[F; T],
    ) {
        assert!(inputs.len() < T);
        let offset = inputs.len() + 1;

        // Add the first constant to the first word
        self.state[0] = stack.add_constant(&self.state[0], pre_constants[0]);

        // Add inputs along with constants
        for ((word, constant), input) in self
            .state
            .iter_mut()
            .skip(1)
            .zip(pre_constants.iter().skip(1))
            .zip(inputs.iter())
        {
            *word = stack.add_add_constant(word, input, *constant);
        }

        // Padding
        for (i, (word, constant)) in self
            .state
            .iter_mut()
            .skip(offset)
            .zip(pre_constants.iter().skip(offset))
            .enumerate()
        {
            *word = stack.add_constant(
                word,
                if i == 0 {
                    // Mark
                    *constant + F::ONE
                } else {
                    *constant
                },
            );
        }
    }

    /// Applies MDS State multiplication
    fn apply_mds<S: FirstDegreeChip<F> + SecondDegreeChip<F>>(
        &mut self,
        stack: &mut S,
        mds: &[[F; T]; T],
    ) {
        // Calculate new state
        let new_state = mds
            .iter()
            .map(|row| {
                // term_i = s_0 * e_i_0 + s_1 * e_i_1 + ....
                let terms = self
                    .state
                    .iter()
                    .zip(row.iter())
                    .map(|(e, word)| e * *word)
                    .collect::<Vec<Scaled<F>>>();

                stack.compose(&terms[..], F::ZERO)
            })
            .collect::<Vec<_>>();

        // Assign new state
        for (word, new_word) in self.state.iter_mut().zip(new_state.into_iter()) {
            *word = new_word
        }
    }

    /// Applies sparse MDS to the state
    fn apply_sparse_mds<S: FirstDegreeChip<F> + SecondDegreeChip<F>>(
        &mut self,
        stack: &mut S,
        mds: &SparseMDSMatrix<F, T, RATE>,
    ) {
        // For the 0th word
        let terms = self
            .state
            .iter()
            .zip(mds.row().iter())
            .map(|(e, word)| (e * *word))
            .collect::<Vec<Scaled<F>>>();
        let mut new_state = vec![stack.compose(&terms[..], F::ZERO)];

        // Rest of the trainsition ie the sparse part
        for (e, word) in mds.col_hat().iter().zip(self.state.iter().skip(1)) {
            new_state.push(stack.compose(&[(self.state[0] * *e), (word * F::ONE)], F::ZERO));
        }

        // Assign new state
        for (word, new_word) in self.state.iter_mut().zip(new_state.into_iter()) {
            *word = new_word
        }
    }

    /// Constrains poseidon permutation while mutating the given state
    pub fn permutation<S: FirstDegreeChip<F> + SecondDegreeChip<F>>(
        &mut self,
        stack: &mut S,
        inputs: Vec<Witness<F>>,
    ) {
        let r_f = self.r_f_half();
        let mds = self.mds();
        let pre_sparse_mds = self.pre_sparse_mds();
        let sparse_matrices = self.sparse_matrices();

        // First half of the full rounds
        let constants = self.constants_start();
        self.absorb_with_pre_constants(stack, inputs, &constants[0]);
        for constants in constants.iter().skip(1).take(r_f - 1) {
            self.sbox_full(stack, constants);
            self.apply_mds(stack, &mds);
        }
        self.sbox_full(stack, constants.last().unwrap());
        self.apply_mds(stack, &pre_sparse_mds);

        // Partial rounds
        let constants = self.constants_partial();
        for (constant, sparse_mds) in constants.iter().zip(sparse_matrices.iter()) {
            self.sbox_part(stack, *constant);
            self.apply_sparse_mds(stack, sparse_mds);
        }

        // Second half of the full rounds
        let constants = self.constants_end();
        for constants in constants.iter() {
            self.sbox_full(stack, constants);
            self.apply_mds(stack, &mds);
        }
        self.sbox_full(stack, &[F::ZERO; T]);
        self.apply_mds(stack, &mds);
    }

    pub fn hash<S: FirstDegreeChip<F> + SecondDegreeChip<F>>(
        &mut self,
        stack: &mut S,
    ) -> Witness<F> {
        // Get elements to be hashed
        let input_elements = self.absorbing.clone();
        // Flush the input que
        self.absorbing.clear();

        let mut padding_offset = 0;
        // Apply permutation to `RATE`Ï sized chunks
        for chunk in input_elements.chunks(RATE) {
            padding_offset = RATE - chunk.len();
            self.permutation(stack, chunk.to_vec());
        }

        // If last chunking is full apply another permutation for collution resistance
        if padding_offset == 0 {
            self.permutation(stack, vec![]);
        }

        self.state[1]
    }
}
