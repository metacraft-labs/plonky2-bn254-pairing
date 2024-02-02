use std::{fmt::Debug, marker::PhantomData};

use ark_bls12_381::Fq12;
use itertools::Itertools;
use plonky2::{
    field::{extension::{Extendable, FieldExtension}, packed::PackedField, polynomial::PolynomialValues},
    hash::hash_types::RichField,
    iop::{ext_target::ExtensionTarget, target::Target},
    plonk::{
        circuit_builder::CircuitBuilder,
        config::{AlgebraicHasher, GenericConfig},
    },
};
use plonky2_bls12_381::fields::{fq12_target::Fq12Target, fq_target::FqTarget};
use starky::{
    config::StarkConfig, constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer}, permutation::PermutationPair, proof::StarkProofWithPublicInputsTarget, recursive_verifier::{add_virtual_stark_proof_with_pis, verify_stark_proof_circuit}, stark::Stark, vars::{StarkEvaluationTargets, StarkEvaluationVars}
};
// use starky_bn254::{
//     circuits::{Fq12ExpU64OutputGenerator, Fq12ExpU64StarkyProofGenerator},
//     fq12_exp_u64::fq12_exp_u64::Fq12ExpU64Stark,
// };

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

    pub fn generate_trace_for_one_block(&self, x: Fq12, offset: Fq12, exp_val: u64) -> Vec<Vec<F>> {
        let c = self.constants();
        let num_rows = 2 * 64;
        let mut lv = vec![F::ZERO; c.num_main_cols];
        generate_flags_u64_first_row(&mut lv, c.start_flags_col, exp_val);
        generate_fq12_exp_u64_first_row(&mut lv, c.start_flags_col, x, offset);
        let mut rows = vec![lv.clone()];
        for i in 0..num_rows - 1 {
            let mut nv = vec![F::ZERO; lv.len()];
            generate_flags_u64_next_row(&lv, &mut nv, i, c.start_flags_col);
            generate_fq12_exp_u64_next_row(&lv, &mut nv, c.start_flags_col);
            rows.push(nv.clone());
            lv = nv;
        }
        let output = {
            let last_row = rows.last().unwrap();
            let mut cur_col = 12 * N_LIMBS;
            let b = read_fq12(last_row, &mut cur_col);
            columns_to_fq12(b)
        };
        // assertion
        let expected: Fq12 = offset * x.pow(&[exp_val]);
        assert!(output == expected);

        rows
    }

    pub fn generate_trace(&self, inputs: &[Fq12ExpU64IONative]) -> Vec<PolynomialValues<F>> {
        let c = self.constants();
        assert!(inputs.len() == c.num_io);

        let mut rows = vec![];
        for input in inputs.clone() {
            let row = self.generate_trace_for_one_block(input.x, input.offset, input.exp_val);
            rows.extend(row);
        }
        let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

        generate_pulse(&mut trace_cols, get_pulse_u64_positions(c.num_io));
        generate_split_u16_range_check(
            c.start_range_check_col..c.end_range_check_col,
            &mut trace_cols,
        );

        trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
    }

    pub fn generate_public_inputs(&self, inputs: &[Fq12ExpU64IONative]) -> Vec<F> {
        inputs
            .iter()
            .flat_map(|input| fq12_exp_u64_io_to_columns::<F>(input))
            .collect_vec()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for Fq12ExpU64Stark<F, D> {
    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<FE, P>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        let c = self.constants();
        let is_final_col = c.start_flags_col;
        let is_sq_col = c.start_flags_col + 1;
        let is_mul_col = c.start_flags_col + 3;
        let exp_val_col = c.start_flags_col + 5;

        let lv = vars.local_values;
        let nv = vars.next_values;

        let mut cur_col = 0;
        let a = read_fq12(lv, &mut cur_col);
        let b = read_fq12(lv, &mut cur_col);
        let output = read_fq12_output(lv, &mut cur_col);
        let is_mul = lv[is_mul_col];
        let is_sq = lv[is_sq_col];
        let is_final = lv[is_final_col];
        let is_not_final = P::ONES - is_final;

        // constraints for is_final
        let mut sum_is_output = P::ZEROS;
        for i in (0..2 * c.num_io).skip(1).step_by(2) {
            sum_is_output = sum_is_output + lv[get_pulse_col(c.start_io_pulses_col, i)];
        }
        yield_constr.constraint(is_final - sum_is_output);

        // public inputs
        let pi: &[P] = &vars.public_inputs.iter().map(|&x| x.into()).collect_vec();
        cur_col = 0;
        for i in (0..2 * c.num_io).step_by(2) {
            let fq12_exp_io = read_fq12_exp_u64_io(pi, &mut cur_col);
            let is_ith_input = lv[get_pulse_col(c.start_io_pulses_col, i)];
            let is_ith_output = lv[get_pulse_col(c.start_io_pulses_col, i + 1)];
            (0..12).for_each(|i| {
                vec_equal(yield_constr, is_ith_input, &fq12_exp_io.x[i], &a[i]);
                vec_equal(yield_constr, is_ith_input, &fq12_exp_io.offset[i], &b[i]);
                vec_equal(yield_constr, is_ith_output, &fq12_exp_io.output[i], &b[i]);
            });
            let bit = is_mul;
            let recovered = lv[exp_val_col] * P::Scalar::TWO + bit;
            yield_constr.constraint(is_ith_input * (fq12_exp_io.exp_val - recovered));
        }

        // transition
        cur_col = 0;
        let next_a = read_fq12(nv, &mut cur_col);
        let next_b = read_fq12(nv, &mut cur_col);
        // if is_double==F::ONE
        {
            fq12_equal_transition(yield_constr, is_not_final * is_sq, next_a, output.output);
            fq12_equal_transition(yield_constr, is_not_final * is_sq, next_b, b);
        }
        // if is_add==F::ONE
        {
            fq12_equal_transition(yield_constr, is_not_final * is_mul, next_a, a);
            fq12_equal_transition(yield_constr, is_not_final * is_mul, next_b, output.output);
        }
        // else
        {
            let is_sq_nor_mul = P::ONES - is_sq - is_mul;
            fq12_equal_transition(yield_constr, is_not_final * is_sq_nor_mul, next_a, a);
            fq12_equal_transition(yield_constr, is_not_final * is_sq_nor_mul, next_b, b);
        }
        eval_flags_u64(yield_constr, lv, nv, c.start_flags_col);
        eval_fq12_mul(yield_constr, is_sq, a, a, &output);
        eval_fq12_mul(yield_constr, is_mul, a, b, &output);

        // flags and lookup
        eval_flags_u64(
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_flags_col,
        );
        eval_pulse(
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_io_pulses_col,
            get_pulse_u64_positions(c.num_io),
        );
        eval_split_u16_range_check(
            vars,
            yield_constr,
            c.start_lookups_col,
            c.start_range_check_col..c.end_range_check_col,
        );
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        let one = builder.one_extension();
        let c = self.constants();
        let is_final_col = c.start_flags_col;
        let is_sq_col = c.start_flags_col + 1;
        let is_mul_col = c.start_flags_col + 3;
        let exp_val_col = c.start_flags_col + 5;

        let lv = vars.local_values;
        let nv = vars.next_values;

        let mut cur_col = 0;
        let a = read_fq12(lv, &mut cur_col);
        let b = read_fq12(lv, &mut cur_col);
        let output = read_fq12_output(lv, &mut cur_col);
        let is_mul = lv[is_mul_col];
        let is_sq = lv[is_sq_col];
        let is_final = lv[is_final_col];
        let is_not_final = builder.sub_extension(one, is_final);

        // constraints for is_final
        let mut sum_is_output = builder.zero_extension();
        for i in (0..2 * c.num_io).skip(1).step_by(2) {
            sum_is_output =
                builder.add_extension(sum_is_output, lv[get_pulse_col(c.start_io_pulses_col, i)]);
        }
        let diff = builder.sub_extension(is_final, sum_is_output);
        yield_constr.constraint(builder, diff);

        // public inputs
        cur_col = 0;
        for i in (0..2 * c.num_io).step_by(2) {
            let fq12_exp_io = read_fq12_exp_u64_io(vars.public_inputs, &mut cur_col);
            let is_ith_input = lv[get_pulse_col(c.start_io_pulses_col, i)];
            let is_ith_output = lv[get_pulse_col(c.start_io_pulses_col, i + 1)];
            (0..12).for_each(|i| {
                vec_equal_circuit(
                    builder,
                    yield_constr,
                    is_ith_input,
                    &fq12_exp_io.x[i],
                    &a[i],
                );
                vec_equal_circuit(
                    builder,
                    yield_constr,
                    is_ith_input,
                    &fq12_exp_io.offset[i],
                    &b[i],
                );
                vec_equal_circuit(
                    builder,
                    yield_constr,
                    is_ith_output,
                    &fq12_exp_io.output[i],
                    &b[i],
                );
            });
            let bit = is_mul;
            let two = builder.two_extension();
            let recovered = builder.mul_add_extension(lv[exp_val_col], two, bit);
            let diff = builder.sub_extension(fq12_exp_io.exp_val, recovered);
            let t = builder.mul_extension(is_ith_input, diff);
            yield_constr.constraint(builder, t);
        }

        // transition
        cur_col = 0;
        let next_a = read_fq12(nv, &mut cur_col);
        let next_b = read_fq12(nv, &mut cur_col);
        // if is_sq==F::ONE
        {
            let is_not_final_and_sq = builder.mul_extension(is_not_final, is_sq);
            fq12_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_sq,
                next_a,
                output.output,
            );
            fq12_equal_transition_circuit(builder, yield_constr, is_not_final_and_sq, next_b, b);
        }
        // if is_mul==F::ONE
        {
            let is_not_final_and_mul = builder.mul_extension(is_not_final, is_mul);
            fq12_equal_transition_circuit(builder, yield_constr, is_not_final_and_mul, next_a, a);
            fq12_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_mul,
                next_b,
                output.output,
            );
        }
        // else
        {
            let is_sq_or_mul = builder.add_extension(is_sq, is_mul);
            let is_not_sq_nor_mul = builder.sub_extension(one, is_sq_or_mul);
            let is_not_final_and_not_sq_nor_mu =
                builder.mul_extension(is_not_final, is_not_sq_nor_mul);
            fq12_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_sq_nor_mu,
                next_a,
                a,
            );
            fq12_equal_transition_circuit(
                builder,
                yield_constr,
                is_not_final_and_not_sq_nor_mu,
                next_b,
                b,
            );
        }
        eval_flags_u64_circuit(builder, yield_constr, lv, nv, c.start_flags_col);
        eval_fq12_mul_circuit(builder, yield_constr, is_sq, a, a, &output);
        eval_fq12_mul_circuit(builder, yield_constr, is_mul, a, b, &output);

        // flags, pulses, and lookup
        eval_flags_u64_circuit(
            builder,
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_flags_col,
        );
        eval_pulse_circuit(
            builder,
            yield_constr,
            vars.local_values,
            vars.next_values,
            c.start_io_pulses_col,
            get_pulse_u64_positions(c.num_io),
        );
        eval_split_u16_range_check_circuit(
            builder,
            vars,
            yield_constr,
            c.start_lookups_col,
            c.start_range_check_col..c.end_range_check_col,
        );
    }

    fn constraint_degree(&self) -> usize {
        3
    }

    fn permutation_pairs(&self) -> Vec<PermutationPair> {
        let c = self.constants();
        split_u16_range_check_pairs(
            c.start_lookups_col,
            c.start_range_check_col..c.end_range_check_col,
        )
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

    let stark = Fq12ExpU64Stark::<F, D>::new(num_io);Fq12ExpStark
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

/// 12*N_LIMBS
pub fn read_fq12<F: Copy + Debug>(lv: &[F], cur_col: &mut usize) -> [[F; N_LIMBS]; 12] {
    (0..12)
        .map(|_| read_u256(lv, cur_col))
        .collect_vec()
        .try_into()
        .unwrap()
}

pub fn fq12_equal_transition<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    x: [[P; N_LIMBS]; 12],
    y: [[P; N_LIMBS]; 12],
) {
    (0..12).for_each(|i| {
        let x_i = x[i];
        let y_i = y[i];
        x_i.iter()
            .zip(y_i.iter())
            .for_each(|(&x, &y)| yield_constr.constraint_transition(filter * (x - y)));
    });
}

pub fn eval_flags_u64_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    lv: &[ExtensionTarget<D>],
    nv: &[ExtensionTarget<D>],
    start_flag_col: usize,
) {
    let one = builder.one_extension();
    let is_final_col = start_flag_col;
    let a_col = start_flag_col + 1;
    let b_col = start_flag_col + 2;
    let filtered_bit_col = start_flag_col + 3;
    let bit_col = start_flag_col + 4;
    let val_col = start_flag_col + 5;

    // initial condition
    yield_constr.constraint_first_row(builder, lv[a_col]);
    let diff = builder.sub_extension(lv[b_col], one);
    yield_constr.constraint_first_row(builder, diff);

    // constraint
    // bit_col is should be 0 or 1.
    let bit = lv[bit_col];
    let t = builder.mul_sub_extension(bit, bit, bit);
    yield_constr.constraint(builder, t);
    // filtered_col is multiplication of bit_col and b_col.
    let t = builder.mul_sub_extension(bit, lv[b_col], lv[filtered_bit_col]);
    yield_constr.constraint(builder, t);

    // transition
    let sum = builder.add_extension(lv[a_col], nv[a_col]);
    let diff = builder.sub_extension(sum, one);
    yield_constr.constraint_transition(builder, diff);
    let sum = builder.add_extension(lv[b_col], nv[b_col]);
    let diff = builder.sub_extension(sum, one);
    yield_constr.constraint_transition(builder, diff);
    // split: first_limb = next_bit + 2*next_first_limb
    let first_limb = lv[val_col];
    let next_first_limb = nv[val_col];
    let next_bit = nv[bit_col];
    let is_split = lv[a_col];
    let is_final = lv[is_final_col];
    let is_not_final = builder.sub_extension(one, is_final);
    let two = builder.two_extension();
    let double_next_first_limb = builder.mul_extension(two, next_first_limb);
    let sum = builder.add_extension(double_next_first_limb, next_bit);
    let diff = builder.sub_extension(first_limb, sum);
    let is_split_and_not_final = builder.mul_extension(is_split, is_not_final);
    let t = builder.mul_extension(is_split_and_not_final, diff);
    yield_constr.constraint_transition(builder, t);
    // not split: first_limb = next_first_limb and next_bit = bit
    let is_not_split = builder.sub_extension(one, is_split);
    let is_not_final = builder.sub_extension(one, is_final);
    let diff = builder.sub_extension(next_bit, bit);
    let t = builder.mul_extension(is_not_split, diff);
    yield_constr.constraint_transition(builder, t);
    let diff = builder.sub_extension(first_limb, next_first_limb);
    let t = builder.mul_extension(is_not_final, is_not_split);
    let t = builder.mul_extension(t, diff);
    yield_constr.constraint_transition(builder, t);
}

pub fn generate_fq12_exp_u64_next_row<F: RichField>(lv: &[F], nv: &mut [F], start_flag_col: usize) {
    let is_sq_col = start_flag_col + 1;
    let is_mul_col = start_flag_col + 3;

    let mut cur_col = 0;
    let a = read_fq12(lv, &mut cur_col);
    let b = read_fq12(lv, &mut cur_col);
    let output = read_fq12_output(lv, &mut cur_col);
    let is_sq = lv[is_sq_col];
    let is_mul = lv[is_mul_col];
    let next_is_sq = nv[is_sq_col];
    let next_is_mul = nv[is_mul_col];

    // calc next a, b
    let (next_a, next_b) = if is_sq == F::ONE {
        (output.output, b)
    } else if is_mul == F::ONE {
        (a, output.output)
    } else {
        (a, b)
    };

    // calc next output
    let next_output = if next_is_sq == F::ONE {
        generate_fq12_mul(next_a, next_a)
    } else if next_is_mul == F::ONE {
        generate_fq12_mul(next_a, next_b)
    } else {
        Fq12Output::default()
    };
    cur_col = 0;
    write_fq12(nv, next_a, &mut cur_col);
    write_fq12(nv, next_b, &mut cur_col);
    write_fq12_output(nv, &next_output, &mut cur_col);
}

pub fn generate_fq12_exp_u64_first_row<F: RichField>(
    lv: &mut [F],
    start_flag_col: usize,
    x: Fq12,
    offset: Fq12,
) {
    let is_mul_col = start_flag_col + 3;
    let a: MyFq12 = x.into();
    let b: MyFq12 = offset.into();
    let a = a
        .coeffs
        .iter()
        .map(|c| fq_to_columns(*c))
        .map(i64_to_column_positive)
        .collect_vec()
        .try_into()
        .unwrap();
    let b = b
        .coeffs
        .iter()
        .map(|c| fq_to_columns(*c))
        .map(i64_to_column_positive)
        .collect_vec()
        .try_into()
        .unwrap();

    let is_mul = lv[is_mul_col];
    let output = if is_mul == F::ONE {
        generate_fq12_mul(a, b)
    } else {
        Fq12Output::default()
    };
    let mut cur_col = 0;
    write_fq12(lv, a, &mut cur_col);
    write_fq12(lv, b, &mut cur_col);
    write_fq12_output(lv, &output, &mut cur_col);
}

pub fn fq12_equal_transition_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: [[ExtensionTarget<D>; N_LIMBS]; 12],
    y: [[ExtensionTarget<D>; N_LIMBS]; 12],
) {
    (0..12).for_each(|i| {
        let x_i = x[i];
        let y_i = y[i];
        x_i.iter().zip(y_i.iter()).for_each(|(&x, &y)| {
            let diff = builder.sub_extension(x, y);
            let t = builder.mul_extension(filter, diff);
            yield_constr.constraint_transition(builder, t);
        });
    });
}

pub fn eval_fq12_mul_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    x: [[ExtensionTarget<D>; N_LIMBS]; 12],
    y: [[ExtensionTarget<D>; N_LIMBS]; 12],
    output: &Fq12Output<ExtensionTarget<D>>,
) {
    let xi = F::Extension::from_canonical_u32(9);
    let input = pol_mul_fq12_ext_circuit(builder, x.to_vec(), y.to_vec(), xi);
    let modulus: [F::Extension; N_LIMBS] = bn254_base_modulus_packfield();
    let modulus = modulus.map(|x| builder.constant_extension(x));
    (0..12).for_each(|i| {
        eval_modular_op_circuit(
            builder,
            yield_constr,
            filter,
            modulus,
            input[i],
            output.output[i],
            output.quot_signs[i],
            &output.auxs[i],
        )
    });
}