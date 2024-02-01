use ark_bls12_381::{Fq12, G1Affine, G2Affine};
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        target::Target,
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_bls12_381::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::{fq12_target::Fq12Target, u256_target::U256Target},
};

pub const G1_EXP_INPUT_LEN: usize = 5 * 8;
pub const G2_EXP_INPUT_LEN: usize = 13 * 8;
pub const FQ12_EXP_INPUT_LEN: usize = 12 * 8 * 3 + 8;
pub const FQ12_EXP_U64_INPUT_LEN: usize = 12 * 8 * 3 + 1;

#[derive(Clone, Debug)]
pub struct G1ExpInput {
    pub x: G1Affine,
    pub offset: G1Affine,
    pub exp_val: BigUint,
}

#[derive(Clone, Debug)]
pub struct G2ExpInput {
    pub x: G2Affine,
    pub offset: G2Affine,
    pub exp_val: BigUint,
}

#[derive(Clone, Debug)]
pub struct Fq12ExpInput {
    pub x: Fq12,
    pub offset: Fq12,
    pub exp_val: BigUint,
}

#[derive(Clone, Debug)]
pub struct Fq12ExpU64Input {
    pub x: Fq12,
    pub offset: Fq12,
    pub exp_val: u64,
}

#[derive(Clone, Debug)]
pub struct G1ExpInputTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: G1Target<F, D>,
    pub offset: G1Target<F, D>,
    pub exp_val: U256Target<F, D>,
}
#[derive(Clone, Debug)]
pub struct G2ExpInputTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: G2Target<F, D>,
    pub offset: G2Target<F, D>,
    pub exp_val: U256Target<F, D>,
}

#[derive(Clone, Debug)]
pub struct Fq12ExpInputTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: Fq12Target<F, D>,
    pub offset: Fq12Target<F, D>,
    pub exp_val: U256Target<F, D>,
}

#[derive(Clone, Debug)]
pub struct Fq12ExpU64InputTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: Fq12Target<F, D>,
    pub offset: Fq12Target<F, D>,
    pub exp_val: Target,
}

impl<F: RichField + Extendable<D>, const D: usize> G1ExpInputTarget<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        G1Target::connect(builder, &lhs.x, &rhs.x);
        G1Target::connect(builder, &lhs.offset, &rhs.offset);
        U256Target::connect(builder, &lhs.exp_val, &rhs.exp_val);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> G2ExpInputTarget<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        G2Target::connect(builder, &lhs.x, &rhs.x);
        G2Target::connect(builder, &lhs.offset, &rhs.offset);
        U256Target::connect(builder, &lhs.exp_val, &rhs.exp_val);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpInputTarget<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        Fq12Target::connect(builder, &lhs.x, &rhs.x);
        Fq12Target::connect(builder, &lhs.offset, &rhs.offset);
        U256Target::connect(builder, &lhs.exp_val, &rhs.exp_val);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpU64InputTarget<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        Fq12Target::connect(builder, &lhs.x, &rhs.x);
        Fq12Target::connect(builder, &lhs.offset, &rhs.offset);
        builder.connect(lhs.exp_val, rhs.exp_val);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> G1ExpInputTarget<F, D> {
    pub fn to_vec(&self) -> Vec<Target> {
        self.x
            .to_vec()
            .iter()
            .chain(self.offset.to_vec().iter())
            .chain(self.exp_val.to_vec().iter())
            .cloned()
            .collect_vec()
    }
    pub fn from_vec(
        builder: &mut CircuitBuilder<F, D>,
        input: &[Target],
    ) -> G1ExpInputTarget<F, D> {
        assert!(input.len() == G1_EXP_INPUT_LEN);
        let num_limbs = 8;
        let num_g1_limbs = 2 * num_limbs;
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_g1_limbs).collect_vec();
        let offset_raw = input.drain(0..num_g1_limbs).collect_vec();
        let exp_val_raw = input.drain(0..num_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let x = G1Target::from_vec(builder, &x_raw);
        let offset = G1Target::from_vec(builder, &offset_raw);
        let exp_val = U256Target::from_vec(&exp_val_raw);
        G1ExpInputTarget { x, offset, exp_val }
    }

    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &G1ExpInput) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        self.exp_val.set_witness(pw, &value.exp_val);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> G2ExpInputTarget<F, D> {
    pub fn to_vec(&self) -> Vec<Target> {
        self.x
            .to_vec()
            .iter()
            .chain(self.offset.to_vec().iter())
            .chain(self.exp_val.to_vec().iter())
            .cloned()
            .collect_vec()
    }
    pub fn from_vec(
        builder: &mut CircuitBuilder<F, D>,
        input: &[Target],
    ) -> G2ExpInputTarget<F, D> {
        assert!(input.len() == G2_EXP_INPUT_LEN);
        let num_limbs = 8;
        let num_g2_limbs = 4 * num_limbs;
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_g2_limbs).collect_vec();
        let offset_raw = input.drain(0..num_g2_limbs).collect_vec();
        let exp_val_raw = input.drain(0..num_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let x = G2Target::from_vec(builder, &x_raw);
        let offset = G2Target::from_vec(builder, &offset_raw);
        let exp_val = U256Target::from_vec(&exp_val_raw);
        G2ExpInputTarget { x, offset, exp_val }
    }

    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &G2ExpInput) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        self.exp_val.set_witness(pw, &value.exp_val);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpInputTarget<F, D> {
    pub fn to_vec(&self) -> Vec<Target> {
        self.x
            .to_vec()
            .iter()
            .chain(self.offset.to_vec().iter())
            .chain(self.exp_val.to_vec().iter())
            .cloned()
            .collect_vec()
    }
    pub fn from_vec(
        builder: &mut CircuitBuilder<F, D>,
        input: &[Target],
    ) -> Fq12ExpInputTarget<F, D> {
        assert!(input.len() == FQ12_EXP_INPUT_LEN);
        let num_limbs = 8;
        let num_fq12_limbs = 12 * num_limbs;
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let offset_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let exp_val_raw = input.drain(0..num_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let x = Fq12Target::from_vec(builder, &x_raw);
        let offset = Fq12Target::from_vec(builder, &offset_raw);
        let exp_val = U256Target::from_vec(&exp_val_raw);
        Fq12ExpInputTarget { x, offset, exp_val }
    }

    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &Fq12ExpInput) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        self.exp_val.set_witness(pw, &value.exp_val);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpU64InputTarget<F, D> {
    pub fn to_vec(&self) -> Vec<Target> {
        self.x
            .to_vec()
            .iter()
            .chain(self.offset.to_vec().iter())
            .chain(&[self.exp_val])
            .cloned()
            .collect_vec()
    }
    pub fn from_vec(
        builder: &mut CircuitBuilder<F, D>,
        input: &[Target],
    ) -> Fq12ExpU64InputTarget<F, D> {
        assert!(input.len() == FQ12_EXP_U64_INPUT_LEN);
        let num_limbs = 8;
        let num_fq12_limbs = 12 * num_limbs;
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let offset_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let exp_val = input[0];
        assert_eq!(input.len(), 1);

        let x = Fq12Target::from_vec(builder, &x_raw);
        let offset = Fq12Target::from_vec(builder, &offset_raw);
        Fq12ExpU64InputTarget { x, offset, exp_val }
    }

    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &Fq12ExpU64Input) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        pw.set_target(self.exp_val, F::from_canonical_u64(value.exp_val));
    }
}