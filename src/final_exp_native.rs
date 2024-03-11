#![allow(non_snake_case)]
use std::{ops::Div, vec};

use ark_bls12_381::{Fq, Fq12, Fq2};
use ark_ff::Field;
use ark_std::Zero;
use group::Wnaf;
use itertools::Itertools;
use num_bigint::BigUint;
use num_traits::One;

use plonky2_bls12_381::fields::native::MyFq12;

use crate::miller_loop_native::conjugate_fp2;

pub const BLS_X: u64 = 15132376222941642752;

pub fn frobenius_map_native(a: MyFq12, power: usize) -> MyFq12 {
    let neg_one: BigUint = Fq::from(-1).into();
    let modulus = neg_one + BigUint::from(1u64);
    assert_eq!(modulus.clone() % 4u64, BigUint::from(3u64));
    assert_eq!(modulus % 6u64, BigUint::from(1u64));
    println!("power % 12: {:?}", power % 12);
    assert!(false);
    let pow = power % 12;

    let mut out_fp2 = Vec::with_capacity(6);

    for i in 0..6 {
        let frob_coeff = frob_coeffs(pow).pow([i as u64]);
        let mut a_fp2 = Fq2::new(a.coeffs[i].clone(), a.coeffs[i + 6].clone());
        if pow % 2 != 0 {
            a_fp2 = conjugate_fp2(a_fp2);
        }

        if frob_coeff == Fq2::one() {
            out_fp2.push(a_fp2);
        } else if frob_coeff.c1 == Fq::zero() {
            let frob_fixed = Fq2::new(frob_coeff.c0, Fq::zero());
            let out_nocarry = a_fp2 * frob_fixed;
            out_fp2.push(out_nocarry);
        } else {
            let frob_fixed = Fq2::new(frob_coeff.c0, frob_coeff.c1);
            out_fp2.push(a_fp2 * frob_fixed);
        }
    }

    let out_coeffs = out_fp2
        .iter()
        .map(|x| x.c0.clone())
        .chain(out_fp2.iter().map(|x| x.c1.clone()))
        .collect_vec();

    MyFq12 {
        coeffs: out_coeffs.try_into().unwrap(),
    }
}

pub fn experimental_pow(a: MyFq12, exp: Vec<u64>) -> MyFq12 {
    let mut res = a.clone();
    let mut is_started = false;
    let naf = get_naf(exp);

    for &z in naf.iter().rev() {
        if is_started {
            res = res * res;
        }

        if z != 0 {
            assert!(z == 1 || z == -1);
            if is_started {
                res = res * a;
            } else {
                assert_eq!(z, 1);
                is_started = true;
            }
        }
    }

    res
}

pub fn pow_native(a: MyFq12, exp: Vec<u64>) -> MyFq12 {
    let mut res = a.clone();
    let mut is_started = false;
    let naf = get_naf(exp);
    // let naf = [
    //     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    //     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    //     1, 0, 1, 1,
    // ];

    for &z in naf.iter().rev() {
        if is_started {
            res = res * res;
        }

        if z != 0 {
            assert!(z == 1 || z == -1);
            if is_started {
                res = if z == 1 {
                    res * a
                } else {
                    let res_fp12: Fq12 = res.into();
                    let a_fp12: Fq12 = a.into();
                    let divided = res_fp12 / a_fp12;
                    divided.into()
                };
            } else {
                assert_eq!(z, 1);
                is_started = true;
            }
        }
    }
    res
}

pub fn get_naf(mut exp: Vec<u64>) -> Vec<i8> {
    // https://en.wikipedia.org/wiki/Non-adjacent_form
    // NAF for exp:
    let mut naf: Vec<i8> = Vec::with_capacity(64 * exp.len());
    println!("exp.len(): {:?}", exp.len());
    let len = exp.len();

    // generate the NAF for exp
    for idx in 0..len {
        let mut e: u64 = exp[idx];
        println!("e:  {:?}", e);
        for _ in 0..64 {
            println!("e & 1:  {:?}", e & 1);
            if e & 1 == 1 {
                let z = 2i8 - (e % 4) as i8;
                // e -= z as u64;
                // Is this useless since our constant in NAF form doesn't contain negative ones?
                // if z == -1 {
                //     e += 1;
                // }
                naf.push(z);
            } else {
                naf.push(0);
            }
            // Moving this outside the if and else statements since we are not checking if z == -1
            e /= 2;
            println!("naf:  {:?}", naf);
        }
        println!("e:  {:?}", e);
        if e != 0 {
            println!("enters e != 0");
            assert_eq!(e, 1);
            let mut j = idx + 1;
            while j < exp.len() && exp[j] == u64::MAX {
                exp[j] = 0;
                j += 1;
            }
            if j < exp.len() {
                exp[j] += 1;
            } else {
                exp.push(1);
            }
        }
    }
    if exp.len() != len {
        println!("enters exp.len() != len");
        assert_eq!(len, exp.len() + 1);
        assert!(exp[len] == 1);
        naf.push(1);
    }
    // Still fails when hardcoded 1 instead of -1
    // let _naf_len = naf.len();
    // let mut naf = naf;
    // naf[_naf_len - 2] = 1;
    println!("naf:  {:?}", naf);

    naf
}

fn hard_part_BN_native(m: MyFq12) -> MyFq12 {
    // let result = Wnaf::new().scalar(&scalar).base(base);
    let mp = frobenius_map_native(m, 1);
    let mp2 = frobenius_map_native(m, 2);
    let mp3 = frobenius_map_native(m, 3);

    let mp2_mp3 = mp2 * mp3;
    let y0 = mp * mp2_mp3;
    let y1 = conjugate_fp12(m);
    let ___m___: Fq12 = m.into();
    let ___m___: MyFq12 = ___m___.inverse().unwrap().into();
    let mx = experimental_pow(___m___, vec![BLS_X]);
    let mxp = frobenius_map_native(mx, 1);
    let ___mx___: Fq12 = mx.into();
    let ___mx___: MyFq12 = ___mx___.inverse().unwrap().into();
    let mx2 = experimental_pow(___mx___, vec![BLS_X]);
    let mx2p = frobenius_map_native(mx2, 1);
    let y2 = frobenius_map_native(mx2, 2);
    let y5 = conjugate_fp12(mx2);
    let ___mx2___: Fq12 = mx2.into();
    let ___mx2___: MyFq12 = ___mx2___.inverse().unwrap().into();
    let mx3 = experimental_pow(___mx2___, vec![BLS_X]);
    let mx3p = frobenius_map_native(mx3, 1);

    let y3 = conjugate_fp12(mxp);
    let mx_mx2p = mx * mx2p;
    let y4 = conjugate_fp12(mx_mx2p);
    let mx3_mx3p = mx3 * mx3p;
    let y6 = conjugate_fp12(mx3_mx3p);

    let mut T0 = y6 * y6;
    T0 = T0 * y4;
    T0 = T0 * y5;

    let mut T1 = y3 * y5;
    T1 = T1 * T0;
    T0 = y2 * T0;
    T1 = T1 * T1;
    T1 = T1 * T0;
    T1 = T1 * T1;
    T0 = T1 * y1;
    T1 = T1 * y0;
    T0 = T0 * T0;
    T0 = T0 * T1;

    T0
}

fn conjugate_fp12(a: MyFq12) -> MyFq12 {
    let coeffs: Vec<Fq> = a
        .coeffs
        .iter()
        .enumerate()
        .map(|(i, c)| if i % 2 == 0 { c.clone() } else { -c.clone() })
        .collect();
    MyFq12 {
        coeffs: coeffs.try_into().unwrap(),
    }
}

pub fn frob_coeffs(index: usize) -> Fq2 {
    let neg_one: BigUint = Fq::from(-1).into();
    let modulus = neg_one + 1u64;

    let num: BigUint = modulus.pow(index as u32) - 1u64;
    let k: BigUint = num.div(6u64);

    let c = Fq2::new(Fq::from(1), Fq::one());
    c.pow(k.to_u64_digits())
}

// out = in^{ (q^6 - 1)*(q^2 + 1) }
fn easy_part<'v>(a: MyFq12) -> MyFq12 {
    let f1 = conjugate_fp12(a);
    let f2 = {
        let f1_fp12: Fq12 = f1.into();
        let a_fp12: Fq12 = a.into();
        let divided = f1_fp12 / a_fp12;
        divided.into()
    };
    let f3 = frobenius_map_native(f2, 2);
    let f = f3 * f2;
    f
}

// out = in^{(q^12 - 1)/r}
pub fn final_exp_native(a: MyFq12) -> MyFq12 {
    let f0 = easy_part(a);
    let f = hard_part_BN_native(f0);
    f
}

#[cfg(test)]
mod tests {
    use std::ops::Mul;

    use ark_bls12_381::{Fq, Fq12, Fr, G1Affine, G2Affine};
    use ark_ec::AffineRepr;
    use ark_ff::Field;
    use ark_std::UniformRand;
    use num_bigint::BigUint;

    use crate::{
        final_exp_native::{experimental_pow, BLS_X},
        miller_loop_native::{miller_loop_native, multi_miller_loop_native},
    };
    use plonky2_bls12_381::fields::debug_tools::print_ark_fq;

    use super::final_exp_native;

    #[test]
    fn test_pairing_final() {
        let Q = G2Affine::generator();
        let P = G1Affine::generator();
        let m = miller_loop_native(&Q, &P);
        let r = final_exp_native(m);
        print_ark_fq(r.coeffs[0], "r.coeffs[0]".to_string());
    }

    #[test]
    fn test_to_one() {
        let G1 = G1Affine::generator();
        let G2 = G2Affine::generator();

        let s = Fr::from(5u64);
        let t = Fr::from(6u64);
        let P0: G1Affine = G1.mul(s).into();
        let Q0: G2Affine = G2.mul(t).into();

        let P1: G1Affine = G1.mul(s * t).into();
        let Q1 = -G2;

        let m = multi_miller_loop_native(vec![(&P0, &Q0), (&P1, &Q1)]);

        let m0 = miller_loop_native(&Q0, &P0);
        let m1 = miller_loop_native(&Q1, &P1);

        assert_eq!(m, m0 * m1);
        let r0 = final_exp_native(m0);
        let r1 = final_exp_native(m1);
        let r_sep = r0 * r1;
        let r_mul = final_exp_native(m);
        assert_eq!(r_sep, r_mul);
    }

    // 322277361516934140462891564586510139908379969514828494218366688025288661041104682794998680497580008899973249814104447692778988208376779573819485263026159588510513834876303014016798809919343532899164848730280942609956670917565618115867287399623286813270357901731510188149934363360381614501334086825442271920079363289954510565375378443704372994881406797882676971082200626541916413184642520269678897559532260949334760604962086348898118982248842634379637598665468817769075878555493752214492790122785850202957575200176084204422751485957336465472324810982833638490904279282696134323072515220044451592646885410572234451732790590013479358343841220074174848221722017083597872017638514103174122784843925578370430843522959600095676285723737049438346544753168912974976791528535276317256904336520179281145394686565050419250614107803233314658825463117900250701199181529205942363159325765991819433914303908860460720581408201373164047773794825411011922305820065611121544561808414055302212057471395719432072209245600258134364584636810093520285711072578721435517884103526483832733289802426157301542744476740008494780363354305116978805620671467071400711358839553375340724899735460480144599782014906586543813292157922220645089192130209334926661588737007768565838519456601560804957985667880395221049249803753582637708560

    #[test]
    fn test_pow() {
        let rng = &mut rand::thread_rng();
        let x = Fq12::rand(rng);
        let output: Fq12 = experimental_pow(x.into(), vec![BLS_X]).into();
        let output2 = x.pow(&[BLS_X]);
        assert_eq!(output, output2);

        let final_x: Fq12 = final_exp_native(x.into()).into();

        use ark_ff::PrimeField;
        let p: BigUint = Fq::MODULUS.into();
        let r: BigUint = Fr::MODULUS.into();
        let exp = (p.pow(12) - 1u32) / r.clone();
        let final_x2 = x.pow(&exp.to_u64_digits());

        // let exp_bits = biguint_to_bits(&exp, 256 * 16);
        // dbg!(exp_bits.len());

        assert_eq!(final_x, final_x2);
    }

    #[test]
    fn test_partial_pow() {
        // 1 / 2 ^ 15132376222941642752
        let two = Fq12::from(2);
        let f_r: Fq12 = experimental_pow(two.into(), vec![BLS_X]).into();
        let f_r = f_r.inverse().unwrap();
        //

        // (1 / 2) ^ 15132376222941642752
        let two = Fq12::from(2);
        let inv_two = two.inverse().unwrap();
        let s_r: Fq12 = experimental_pow(inv_two.into(), vec![BLS_X]).into();

        //
        assert_eq!(f_r, s_r);

        // 1 / 4
        let one_div_4 = Fq12::from(32).inverse().unwrap();
        // 1 / 4 attempt
        let one_div_4_att: Fq12 = experimental_pow(inv_two.into(), vec![5]).into();

        assert_eq!(one_div_4, one_div_4_att);
    }
}
