#![allow(non_snake_case)]
use ark_bls12_381::{Fq, Fq2};
use ark_ff::{Field, One, Zero};
use num_bigint::BigUint;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::target::{BoolTarget, Target},
    plonk::{
        circuit_builder::CircuitBuilder,
        config::{AlgebraicHasher, GenericConfig},
    },
};

use plonky2_bls12_381::fields::{fq12_target::Fq12Target, fq2_target::Fq2Target};

use crate::final_exp_native::{frob_coeffs, BLS_X};

pub fn get_naf_target<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    mut exp: Vec<Target>,
) -> Vec<Target> {
    // NAF for exp:
    let mut naf: Vec<Target> = Vec::with_capacity(64 * exp.len());
    let len = exp.len();

    let borrow_zero = builder.zero();
    let borrow_one = builder.one();
    let borrow_two = builder.two();
    let borrow_true = builder._true();
    let four = builder.constant(F::from_canonical_u8(4));

    // generate the NAF for exp
    for idx in 0..len {
        let mut e = exp[idx];
        for _ in 0..64 {
            let e_to_bits = builder.split_le(e, 64); // check num_limbs // use maybe builder.low_bits()?
            let e_to_bits: Vec<BoolTarget> = e_to_bits
                .iter()
                .map(|_e| builder.and(*_e, borrow_true))
                .collect();
            if e_to_bits[e_to_bits.len() - 1].eq(&builder._true()) {
                let e_div_4 = builder.div(e, four);
                let e_div_4_mul_4 = builder.mul(e_div_4, four);
                let e_mod_4 = builder.sub(e, e_div_4_mul_4);
                let z = builder.sub(borrow_two, e_mod_4);
                e = builder.div(e, borrow_two);
                if z.eq(&builder.neg_one()) {
                    e = builder.add(e, borrow_one);
                }
                naf.push(z);
            } else {
                naf.push(borrow_zero);
                e = builder.div(e, borrow_two);
            }
        }
        if !e.eq(&borrow_zero) {
            assert_eq!(e, borrow_one);
            let mut j = idx + 1;
            while j < exp.len() && exp[j].eq(&builder.constant(F::from_canonical_u64(u64::MAX))) {
                exp[j] = borrow_zero;
                j += 1;
            }
            if j < exp.len() {
                exp[j] = builder.add(exp[j], borrow_one);
            } else {
                exp.push(borrow_one);
            }
        }
    }
    if exp.len() != len {
        assert_eq!(len, exp.len() + 1);
        assert!(exp[len] == borrow_one);
        naf.push(borrow_one);
    }
    naf
}

pub fn pow_target<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: Fq12Target<F, D>,
    exp: Vec<Target>,
) -> Fq12Target<F, D> {
    let mut res = a.clone();
    let mut is_started = false;
    let naf = get_naf_target::<F, D>(builder, exp);

    for &z in naf.iter().rev() {
        let z_equals_zero = z.eq(&builder.zero());
        if is_started {
            res = res.mul(builder, &res);
        }
        if !z_equals_zero {
            assert!(z.eq(&builder.one()) || z.eq(&builder.neg_one()));
            if is_started {
                if z.eq(&builder.one()) {
                    res = res.mul(builder, &a);
                } else {
                    res = res.div(builder, &a);
                };
            } else {
                assert_eq!(z, builder.one());
                is_started = true;
            }
        }
    }
    res
}

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

fn hard_part_BN<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    m: &Fq12Target<F, D>,
) -> Fq12Target<F, D>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let exp_val = builder.constant(F::from_canonical_u64(BLS_X as u64));

    let mp = frobenius_map(builder, m, 1);
    let mp2 = frobenius_map(builder, m, 2);
    let mp3 = frobenius_map(builder, m, 3);

    let mp2_mp3 = mp2.mul(builder, &mp3);
    let y0 = mp.mul(builder, &mp2_mp3);
    let y1 = m.confugate(builder);

    let _mx = pow_target(builder, m.clone(), vec![exp_val]);
    let mx = Fq12Target::empty(builder);
    let mxp = frobenius_map(builder, &mx, 1);
    let mx2 = Fq12Target::empty(builder);
    let _mx2 = pow_target(builder, _mx, vec![exp_val]);
    let mx2p = frobenius_map(builder, &mx2, 1);
    let y2 = frobenius_map(builder, &mx2, 2);
    let y5 = mx2.confugate(builder);
    let _mx3 = pow_target(builder, mx2, vec![exp_val]);
    let mx3 = Fq12Target::empty(builder);
    let mx3p = frobenius_map(builder, &mx3, 1);

    let y3 = mxp.confugate(builder);
    let mx_mx2p = mx.mul(builder, &mx2p);
    let y4 = mx_mx2p.confugate(builder);
    let mx3_mx3p = mx3.mul(builder, &mx3p);
    let y6 = mx3_mx3p.confugate(builder);

    let mut T0 = y6.mul(builder, &y6);
    T0 = T0.mul(builder, &y4);
    T0 = T0.mul(builder, &y5);

    let mut T1 = y3.mul(builder, &y5);
    T1 = T1.mul(builder, &T0);
    T0 = y2.mul(builder, &T0);
    T1 = T1.mul(builder, &T1);
    T1 = T1.mul(builder, &T0);
    T1 = T1.mul(builder, &T1);
    T0 = T1.mul(builder, &y1);
    T1 = T1.mul(builder, &y0);
    T0 = T0.mul(builder, &T0);
    T0 = T0.mul(builder, &T1);

    T0
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

pub fn final_exp_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    a: Fq12Target<F, D>,
) -> Fq12Target<F, D>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let f0 = easy_part(builder, &a);
    let f = hard_part_BN::<F, C, D>(builder, &f0);
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
        let output = final_exp_circuit::<F, C, D>(&mut builder, input_t);
        let output_expected = final_exp_native(input);

        let output_expected_t = Fq12Target::constant(&mut builder, output_expected.into());

        Fq12Target::connect(&mut builder, &output, &output_expected_t);
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());

        let now = Instant::now();
        let pw = PartialWitness::new();
        let _proof = data.prove(pw);
        println!("time: {:?}", now.elapsed());
    }
}
