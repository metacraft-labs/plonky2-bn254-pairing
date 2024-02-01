use std::marker::PhantomData;

use itertools::Itertools;
use plonky2::{field::extension::Extendable, hash::hash_types::RichField, iop::target::Target, plonk::{circuit_builder::CircuitBuilder, config::{AlgebraicHasher, GenericConfig}}};
use plonky2_bls12_381::fields::{fq12_target::Fq12Target, fq_target::FqTarget};
use starky::{config::StarkConfig, proof::StarkProofWithPublicInputsTarget, recursive_verifier::{add_virtual_stark_proof_with_pis, verify_stark_proof_circuit}};
// use starky_bn254::{circuits::{Fq12ExpU64OutputGenerator, Fq12ExpU64StarkyProofGenerator}, fq12_exp_u64::fq12_exp_u64::Fq12ExpU64Stark};

use crate::exp_inputs::Fq12ExpU64InputTarget;

pub const LIMB_BITS: usize = 16;
pub const N_LIMBS: usize = 16;
pub const NUM_FLAGS_U64_COLS: usize = 6;
const FQ12_EXP_U64_IO_LEN: usize = 36 * N_LIMBS + 1;
pub const NUM_INPUT_LIMBS: usize = 8;
// pub const INPUT_LIMB_BITS: usize = 32;


// 36*N_LIMBS + NUM_INPUT_LIMBS
pub struct Fq12ExpU64IO<F> {
    pub x: [[F; N_LIMBS]; 12],
    pub offset: [[F; N_LIMBS]; 12],
    pub exp_val: F,
    pub output: [[F; N_LIMBS]; 12],
}

pub struct ExpU64StarkConstants {
    pub num_columns: usize,
    pub num_public_inputs: usize,
    pub num_main_cols: usize,
    pub num_io: usize,
    pub start_flags_col: usize,
    pub start_io_pulses_col: usize,
    pub start_lookups_col: usize,
    pub start_range_check_col: usize,
    pub end_range_check_col: usize,
    pub num_range_check_cols: usize,
}

fn constants(num_io: usize) -> ExpU64StarkConstants {
    let start_flags_col = 108 * N_LIMBS;
    let num_main_cols = start_flags_col + NUM_FLAGS_U64_COLS;

    let start_io_pulses_col = num_main_cols;
    let start_lookups_col = start_io_pulses_col + 1 + 4 * num_io;

    let start_range_check_col = 24 * N_LIMBS;
    let num_range_check_cols = 84 * N_LIMBS - 12;
    let end_range_check_col = start_range_check_col + num_range_check_cols;

    let num_columns = start_lookups_col + 1 + 6 * num_range_check_cols;
    let num_public_inputs = FQ12_EXP_U64_IO_LEN * num_io;

    ExpU64StarkConstants {
        num_columns,
        num_public_inputs,
        num_main_cols,
        num_io,
        start_flags_col,
        start_io_pulses_col,
        start_lookups_col,
        start_range_check_col,
        end_range_check_col,
        num_range_check_cols,
    }
}

#[derive(Clone, Debug)]
pub struct Fq12ExpU64OutputGenerator<F: RichField + Extendable<D>, const D: usize> {
    pub input: Fq12ExpU64InputTarget<F, D>,
    pub output: Fq12Target<F, D>,
}

#[derive(Clone, Debug)]
pub struct Fq12ExpU64StarkyProofGenerator<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
> {
    pub inputs: Vec<Fq12ExpU64InputTarget<F, D>>,
    pub outputs: Vec<Fq12Target<F, D>>,
    pub starky_proof: StarkProofWithPublicInputsTarget<D>,
    _config: std::marker::PhantomData<C>,
}

pub fn fq12_exp_u64_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    inputs: &[Fq12ExpU64InputTarget<F, D>],
) -> Vec<Fq12Target<F, D>>
where
    C::Hasher: AlgebraicHasher<F>,
{
    let n = inputs.len();
    let next_power_of_two = n.next_power_of_two();
    let mut inputs = inputs.to_vec();
    inputs.resize(next_power_of_two, inputs.last().unwrap().clone());
    let log_num_io = next_power_of_two.trailing_zeros() as usize;

    let (inputs_constr, outputs, starky_proof) =
        fq12_exp_u64_circuit_with_proof_target::<F, C, D>(builder, log_num_io);

    for (input_c, input) in inputs_constr.iter().zip(inputs.iter()) {
        Fq12ExpU64InputTarget::connect(builder, input_c, input);
    }

    for (input, output) in inputs.iter().zip(outputs.iter()) {
        let output_generator = Fq12ExpU64OutputGenerator {
            input: input.to_owned(),
            output: output.to_owned(),
        };
        builder.add_simple_generator(output_generator);
    }

    let proof_generator = Fq12ExpU64StarkyProofGenerator::<F, C, D> {
        inputs: inputs.to_vec(),
        outputs: outputs.clone(),
        starky_proof,
        _config: PhantomData,
    };
    builder.add_simple_generator(proof_generator);
    outputs[..n].to_vec()
}

#[derive(Clone, Copy)]
pub struct Fq12ExpU64Stark<F: RichField + Extendable<D>, const D: usize> {
    pub num_io: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> Fq12ExpU64Stark<F, D> {
    pub fn new(num_io: usize) -> Self {
        Self {
            num_io,
            _phantom: PhantomData,
        }
    }

    pub fn constants(&self) -> ExpU64StarkConstants {
        constants(self.num_io)
    }

    pub fn config(&self) -> StarkConfig {
        let c = self.constants();
        StarkConfig::standard_fast_config(c.num_columns, c.num_public_inputs)
    }
}

pub fn fq12_exp_u64_circuit_with_proof_target<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    log_num_io: usize,
) -> (
    Vec<Fq12ExpU64InputTarget<F, D>>,
    Vec<Fq12Target<F, D>>,
    StarkProofWithPublicInputsTarget<D>,
)
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let num_io = 1 << log_num_io;
    let stark = Fq12ExpU64Stark::<F, D>::new(num_io);
    let inner_config = stark.config();
    let degree_bits = 7 + log_num_io;
    let starky_proof_t =
        add_virtual_stark_proof_with_pis(builder, stark, &inner_config, degree_bits);
    verify_stark_proof_circuit::<F, C, _, D>(builder, stark, &starky_proof_t, &inner_config);
    assert!(starky_proof_t.public_inputs.len() == FQ12_EXP_U64_IO_LEN * num_io);
    let mut cur_col = 0;
    let mut inputs = vec![];
    let mut outputs = vec![];
    let pi = starky_proof_t.public_inputs.clone();
    for _ in 0..num_io {
        let io = read_fq12_exp_u64_io(&pi, &mut cur_col);
        let x_coeffs =
            io.x.iter()
                .map(|limb| {
                    // range check
                    limb.iter().for_each(|l| builder.range_check(*l, 16));
                    let limb_u32 = u16_columns_to_u32_columns_base_circuit(builder, *limb);
                    FqTarget::from_limbs(builder, &limb_u32)
                })
                .collect_vec();
        let offset_coeffs = io
            .offset
            .iter()
            .map(|limb| {
                // range check
                limb.iter().for_each(|l| builder.range_check(*l, 16));
                let limb_u32 = u16_columns_to_u32_columns_base_circuit(builder, *limb);
                FqTarget::from_limbs(builder, &limb_u32)
            })
            .collect_vec();
        let output_coeffs = io
            .output
            .iter()
            .map(|limb| {
                // range check
                // limb.iter().for_each(|l| builder.range_check(*l, 16));
                let limb_u32 = u16_columns_to_u32_columns_base_circuit(builder, *limb);
                FqTarget::from_limbs(builder, &limb_u32)
            })
            .collect_vec();
        let x = Fq12Target::new(x_coeffs);
        let offset = Fq12Target::new(offset_coeffs);
        let output = Fq12Target::new(output_coeffs);
        let exp_val = io.exp_val;
        let input = Fq12ExpU64InputTarget { x, offset, exp_val };
        inputs.push(input);
        outputs.push(output);
    }
    (inputs, outputs, starky_proof_t)
}

fn u16_columns_to_u32_columns_base_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: [Target; N_LIMBS],
) -> [Target; NUM_INPUT_LIMBS] {
    let base = builder.constant(F::from_canonical_u32(1 << LIMB_BITS));
    x.chunks(2)
        .map(|chunk| builder.mul_add(chunk[1], base, chunk[0]))
        .collect_vec()
        .try_into()
        .unwrap()
}

fn read_fq12_exp_u64_io<F: Clone + core::fmt::Debug>(
    lv: &[F],
    cur_col: &mut usize,
) -> Fq12ExpU64IO<F> {
    let x = [(); 12].map(|_| read_u16_fq(lv, cur_col));
    let offset = [(); 12].map(|_| read_u16_fq(lv, cur_col));
    let exp_val = lv[*cur_col].clone();
    *cur_col += 1;
    let output = [(); 12].map(|_| read_u16_fq(lv, cur_col));
    Fq12ExpU64IO {
        x,
        offset,
        exp_val,
        output,
    }
}

pub fn read_u16_fq<F: Clone + core::fmt::Debug>(lv: &[F], cur_col: &mut usize) -> [F; N_LIMBS] {
    let output = lv[*cur_col..*cur_col + N_LIMBS].to_vec();
    *cur_col += N_LIMBS;
    output.try_into().unwrap()
}