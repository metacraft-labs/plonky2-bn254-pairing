#![allow(non_snake_case)]
use ark_bls12_381::{Fq, Fq2};
use ark_ff::{Field, One, Zero};
use num_bigint::BigUint;

use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
};

use plonky2_bls12_381::fields::{fq12_target::Fq12Target, fq2_target::Fq2Target};

use crate::final_exp_native::{experimental_pow, frob_coeffs, get_naf, BLS_X};

fn frobenius_map<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &Fq12Target<F, D>,
    power: usize,
) -> Fq12Target<F, D> {
    let neg_one: BigUint = Fq::from(-1).into();
    let modulus = neg_one + BigUint::from(1u64);
    assert_eq!(modulus.clone() % 4u64, BigUint::from(3u64));
    assert_eq!(modulus % 6u64, BigUint::from(1u64));
    let pow = power % 12;

    let mut out_fp2 = Vec::with_capacity(6);
    for i in 0..6 {
        let frob_coeff = frob_coeffs(pow).pow([i as u64]);
        let mut a_fp2 = Fq2Target {
            coeffs: [a.coeffs[i].clone(), a.coeffs[i + 6].clone()],
        };
        if pow % 2 != 0 {
            a_fp2 = a_fp2.conjugate(builder);
        }
        if frob_coeff == Fq2::one() {
            out_fp2.push(a_fp2);
        } else if frob_coeff.c1 == Fq::zero() {
            let frob_fixed = Fq2::new(frob_coeff.c0, Fq::zero());
            let frob_fixed_t = Fq2Target::constant(builder, frob_fixed);
            let out_nocarry = a_fp2.mul(builder, &frob_fixed_t);
            out_fp2.push(out_nocarry);
        } else {
            let frob_fixed = Fq2::new(frob_coeff.c0, frob_coeff.c1);
            let frob_fixed_t = Fq2Target::constant(builder, frob_fixed);
            let out_nocarry = a_fp2.mul(builder, &frob_fixed_t);
            out_fp2.push(out_nocarry);
        }
    }
    let out_coeffs = out_fp2
        .iter()
        .map(|x| x.coeffs[0].clone())
        .chain(out_fp2.iter().map(|x| x.coeffs[1].clone()))
        .collect::<Vec<_>>();

    Fq12Target {
        coeffs: out_coeffs.try_into().unwrap(),
    }
}

pub fn experimental_pow_target<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: Fq12Target<F, D>,
    exp: Vec<u64>,
) -> Fq12Target<F, D> {
    let mut res = a.clone();
    let mut is_started = false;
    let naf = get_naf(exp);

    for &z in naf.iter().rev() {
        if is_started {
            res = res.mul(builder, &res);
        }

        if z != 0 {
            assert!(z == 1 || z == -1);
            if is_started {
                res = res.mul(builder, &a);
            } else {
                assert_eq!(z, 1);
                is_started = true;
            }
        }
    }

    res
}

fn hard_part<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    m: &Fq12Target<F, D>,
) -> Fq12Target<F, D> {
    let pow1 = experimental_pow_target(builder, m.clone(), vec![(BLS_X + 1) / 3]);
    let pow2 = experimental_pow_target(builder, pow1, vec![BLS_X + 1]);
    let pow3 = frobenius_map(builder, &pow2, 6);
    let pow4 = experimental_pow_target(builder, pow3, vec![BLS_X]);
    let pow5 = frobenius_map(builder, &pow2, 1);
    let pow6 = pow4.mul(builder, &pow5);
    let pow7 = experimental_pow_target(builder, pow6.clone(), vec![BLS_X]);
    let pow8 = experimental_pow_target(builder, pow7, vec![BLS_X]);
    let pow9 = frobenius_map(builder, &pow6, 2);
    let pow10 = frobenius_map(builder, &pow6, 6);
    let pow11 = pow8.mul(builder, &pow9);
    let pow12 = pow10.mul(builder, &pow11);
    let pow13 = pow12.mul(builder, m);
    pow13
}

fn easy_part<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &Fq12Target<F, D>,
) -> Fq12Target<F, D> {
    let f1 = a.confugate(builder);
    let f2 = f1.div(builder, &a);
    let f3 = frobenius_map(builder, &f2, 2);
    let f = f3.mul(builder, &f2);
    f
}

pub fn final_exp_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: Fq12Target<F, D>,
) -> Fq12Target<F, D> {
    let f0 = easy_part(builder, &a);
    let f = hard_part::<F, D>(builder, &f0);
    f
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use ark_bls12_381::{Fq12, G1Affine, G2Affine};
    use ark_std::UniformRand;
    use rand::Rng;

    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use crate::final_exp_target::frobenius_map;
    use crate::miller_loop_native::miller_loop_native;
    use crate::{
        final_exp_native::{final_exp_native, frobenius_map_native},
        final_exp_target::final_exp_circuit,
    };
    use plonky2_bls12_381::fields::fq12_target::Fq12Target;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_frobenius_map() {
        let rng = &mut rand::thread_rng();
        let power = rng.gen();
        let a = Fq12::rand(rng);
        let b_expected = frobenius_map_native(a.into(), power);

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = Fq12Target::constant(&mut builder, a);
        let b_t = frobenius_map(&mut builder, &a_t, power);
        let b_expected_t = Fq12Target::constant(&mut builder, b_expected.into());

        Fq12Target::connect(&mut builder, &b_t, &b_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_final_exp_circuit() {
        let rng = &mut rand::thread_rng();
        let Q = G2Affine::rand(rng);
        let P = G1Affine::rand(rng);
        let input = miller_loop_native(&Q, &P);

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let input_t = Fq12Target::constant(&mut builder, input.into());
        let output = final_exp_circuit::<F, D>(&mut builder, input_t);
        let output_expected = final_exp_native(input);

        let output_expected_t = Fq12Target::constant(&mut builder, output_expected.into());

        Fq12Target::connect(&mut builder, &output, &output_expected_t);

        let now = Instant::now();
        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
        println!("time: {:?}", now.elapsed());
    }
}
