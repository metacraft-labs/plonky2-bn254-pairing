#![allow(non_snake_case)]

use ark_bls12_381::{Fq, Fq2, G1Affine, G2Affine};
use ark_ff::{Field, Fp2};
use ark_std::{One, Zero};
use num_bigint::BigUint;

use plonky2_bls12_381::fields::native::MyFq12;

// This function representing https://hackmd.io/@Wimet/ry7z1Xj-2#Different-Points
fn sparse_line_function_unequal_native(
    Q: (&G2Affine, &G2Affine),
    P: &G1Affine,
) -> Vec<Option<Fq2>> {
    let (x_1, y_1) = (&Q.0.x, &Q.0.y);
    let (x_2, y_2) = (&Q.1.x, &Q.1.y);
    let (x, y) = (&P.x, &P.y);

    let y1_minus_y2 = y_1 - y_2; // Q.0.y - Q.1.y
    let x2_minus_x1 = x_2 - x_1; // Q.1.x - Q.0.x
    let x1y2 = x_1 * y_2;
    let x2y1 = x_2 * y_1;

    let out3 = y1_minus_y2 * Fq2::new(x.clone(), Fq::zero()); // Q.0.y - Q.1.y * Fq2 (x, 0)
    let out2 = x2_minus_x1 * Fq2::new(y.clone(), Fq::zero()); //  Q.1.x - Q.0.x * Fq2 (y, 0)
    let out5 = x1y2 - x2y1;

    vec![None, None, Some(out2), Some(out3), None, Some(out5)]
}

// Computing the Optimal Ate Pairing
// from https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-08#name-computing-the-optimal-ate-p
fn line_function(Q: (&G2Affine, &G2Affine), P: &G1Affine) -> Fq2 {
    let (x_1, y_1) = (&Q.0.x, &Q.0.y);
    let (x_2, y_2) = (&Q.1.x, &Q.1.y);
    let (x, y) = (&P.x, &P.y);

    // A = B
    let x_1_sq = x_1 * x_1;
    let x_1_sq_times_3 = x_1_sq * Fq2::from(3);
    let y_1_times_2 = y_1 * Fq2::from(2);
    // A != B
    let y_2_minus_y_1 = y_2 - y_1;
    let x_2_minus_x_1 = x_2 - x_1;

    let l;
    if x_1 == x_2 && y_1 == y_2 {
        l = x_1_sq_times_3 / y_1_times_2;
    } else if y_1.eq(&neg_conjugate_fp2(*y_2)) && x_1.eq(&neg_conjugate_fp2(*x_2)) {
        return Fq2::new(x.clone(), Fq::zero()) - x_1;
    } else {
        l = y_2_minus_y_1 / x_2_minus_x_1;
    }

    // IF (P[1] -A[1]) + A[2] -P[2]) IS WITH NEGATION
    // let x_minus_x_1 = Fq2::new(x.clone(), Fq::zero()) + neg_conjugate_fp2(*x_1);
    // let y_1_minus_y = y_1 + neg_conjugate_fp2(Fq2::new(y.clone(), Fq::zero()));

    let x_minus_x_1 = Fq2::new(x.clone(), Fq::zero()) - x_1;
    let y_1_minus_y = y_1 + Fq2::new(y.clone(), Fq::zero());
    let l_times_x_minus_x_1 = l * x_minus_x_1;

    return l_times_x_minus_x_1 + y_1_minus_y;
}

// CRITICAL CONCERN
// Create a function representing the line between P1 and P2, ???
// This function representing https://hackmd.io/@Wimet/ry7z1Xj-2#The-Same-Points
fn sparse_line_function_equal_native(Q: &G2Affine, P: &G1Affine) -> Vec<Option<Fq2>> {
    let (x, y) = (&Q.x, &Q.y);
    let x_sq = x * x;
    let x_cube = x_sq * x;
    let three_x_cu = x_cube * Fq2::from(3); // fq2 3 * x ^ 3
    let y_sq = y * y;
    let two_y_sq = y_sq * Fq2::from(2); //  // fq2 2 * y ^ 2
    let out0_left = three_x_cu - two_y_sq; // (fq2 3 * x ^ 3 - fq2 2 * y ^ 2)
    let out0 = out0_left * Fq2::new(Fq::from(1), Fq::one()); // (fq2 3 * x ^ 3 - fq2 2 * y ^ 2) * fq2(fq9,fq1)
    let x_sq_px: Fq2 = x_sq * Fq2::new(P.x, Fq::zero()); // x^2 * fq2(p.x, Fq0)
    let out4 = x_sq_px * Fq2::from(-3); // x^2 * fq2(p.x, Fq0) * Fq2 -3
    let y_py = y * Fq2::new(P.y, Fq::zero());
    let out3 = y_py * Fq2::from(2);
    vec![Some(out0), None, None, Some(out3), Some(out4), None]
}

fn sparse_fp12_multiply_native(a: &MyFq12, b: Vec<Option<Fq2>>) -> MyFq12 {
    let mut a_fp2_coeffs = Vec::with_capacity(6);
    for i in 0..6 {
        a_fp2_coeffs.push(Fq2::new(a.coeffs[i].clone(), a.coeffs[i + 6].clone()));
    }
    // a * b as element of Fp2[w] without evaluating w^6 = (XI_0 + u)
    let mut prod_2d: Vec<Option<Fq2>> = vec![None; 11];
    for i in 0..6 {
        for j in 0..6 {
            prod_2d[i + j] = match (prod_2d[i + j].clone(), &a_fp2_coeffs[i], b[j].as_ref()) {
                (a, _, None) => a,
                (None, a, Some(b)) => {
                    let ab = a * b;
                    Some(ab)
                }
                (Some(a), b, Some(c)) => {
                    let bc = b * c;
                    let out = a + bc;
                    Some(out)
                }
            };
        }
    }
    let mut out_fp2 = Vec::with_capacity(6);
    for i in 0..6 {
        let prod = if i != 5 {
            let eval_w6 = prod_2d[i + 6]
                .as_ref()
                .map(|a| a * Fq2::new(Fq::from(1), Fq::one()));
            match (prod_2d[i].as_ref(), eval_w6) {
                (None, b) => b.unwrap(),
                (Some(a), None) => a.clone(),
                (Some(a), Some(b)) => a + b,
            }
        } else {
            prod_2d[i].clone().unwrap()
        };
        out_fp2.push(prod);
    }

    let mut out_coeffs = Vec::with_capacity(12);
    for fp2_coeff in &out_fp2 {
        out_coeffs.push(fp2_coeff.c0.clone());
    }
    for fp2_coeff in &out_fp2 {
        out_coeffs.push(fp2_coeff.c1.clone());
    }
    MyFq12 {
        coeffs: out_coeffs.try_into().unwrap(),
    }
}

fn fp12_multiply_with_line_unequal_native(
    g: &MyFq12,
    Q: (&G2Affine, &G2Affine),
    P: &G1Affine,
) -> MyFq12 {
    let line: Vec<Option<Fq2>> = sparse_line_function_unequal_native(Q, P);
    sparse_fp12_multiply_native(g, line)
}

fn fp12_multiply_with_line_equal_native(g: &MyFq12, Q: &G2Affine, P: &G1Affine) -> MyFq12 {
    let line: Vec<Option<Fq2>> = sparse_line_function_equal_native(Q, P);
    sparse_fp12_multiply_native(g, line)
}

fn miller_loop_BN_native(Q: &G2Affine, P: &G1Affine, pseudo_binary_encoding: &[i8]) -> MyFq12 {
    let mut i = pseudo_binary_encoding.len() - 1;
    while pseudo_binary_encoding[i] == 0 {
        i -= 1;
    }
    let last_index = i;
    assert!(pseudo_binary_encoding[i] == 1 || pseudo_binary_encoding[i] == -1);
    let mut R = if pseudo_binary_encoding[i] == 1 {
        Q.clone()
    } else {
        -Q.clone()
    };
    i -= 1;

    // initialize the first line function into Fq12 point
    let sparse_f = sparse_line_function_equal_native(&R, P);
    assert_eq!(sparse_f.len(), 6);

    let zero_fp = Fq::zero();
    let mut f_coeffs = Vec::with_capacity(12);
    for coeff in &sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.c0);
        } else {
            f_coeffs.push(zero_fp);
        }
    }
    for coeff in &sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.c1);
        } else {
            f_coeffs.push(zero_fp);
        }
    }

    let mut f = MyFq12 {
        coeffs: f_coeffs.try_into().unwrap(),
    };

    loop {
        if i != last_index - 1 {
            let f_sq = f * f;
            f = fp12_multiply_with_line_equal_native(&f_sq, &R, P);
        }

        R = (R + R).into();

        assert!(pseudo_binary_encoding[i] <= 1 && pseudo_binary_encoding[i] >= -1);
        if pseudo_binary_encoding[i] != 0 {
            let sign_Q = if pseudo_binary_encoding[i] == 1 {
                Q.clone()
            } else {
                -Q.clone()
            };
            f = fp12_multiply_with_line_unequal_native(&f, (&R, &sign_Q), P);
            R = (R + sign_Q).into();
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }
    let mut R: G2Affine = R;

    let neg_one: BigUint = Fq::from(-1).into();
    let k = neg_one / BigUint::from(6u32);
    let expected_c = Fq2::new(Fq::from(1), Fq::one()).pow(k.to_u64_digits());

    let c2 = expected_c * expected_c;
    let c3 = c2 * expected_c;

    let Q_1 = twisted_frobenius(Q, c2, c3);
    let neg_Q_2 = neg_twisted_frobenius(&Q_1, c2, c3);
    f = fp12_multiply_with_line_unequal_native(&f, (&R, &Q_1), P);
    R = (R + Q_1).into();
    f = fp12_multiply_with_line_unequal_native(&f, (&R, &neg_Q_2), P);

    f
}

fn multi_miller_loop_BN_native(
    pairs: Vec<(&G1Affine, &G2Affine)>,
    pseudo_binary_encoding: &[i8],
) -> MyFq12 {
    let mut i = pseudo_binary_encoding.len() - 1;
    while pseudo_binary_encoding[i] == 0 {
        i -= 1;
    }
    let last_index = i;
    assert_eq!(pseudo_binary_encoding[last_index], 1);

    let neg_b: Vec<G2Affine> = pairs.iter().map(|pair| -pair.1.clone()).collect();

    // initialize the first line function into Fq12 point
    let mut f = {
        let sparse_f = sparse_line_function_equal_native(pairs[0].1, pairs[0].0);
        assert_eq!(sparse_f.len(), 6);

        let zero_fp = Fq::zero();
        let mut f_coeffs = Vec::with_capacity(12);
        for coeff in &sparse_f {
            if let Some(fp2_point) = coeff {
                f_coeffs.push(fp2_point.c0);
            } else {
                f_coeffs.push(zero_fp);
            }
        }
        for coeff in &sparse_f {
            if let Some(fp2_point) = coeff {
                f_coeffs.push(fp2_point.c1);
            } else {
                f_coeffs.push(zero_fp);
            }
        }
        MyFq12 {
            coeffs: f_coeffs.try_into().unwrap(),
        }
    };

    for &(a, b) in pairs.iter().skip(1) {
        f = fp12_multiply_with_line_equal_native(&f, b, a);
    }

    i -= 1;
    let mut r = pairs.iter().map(|pair| pair.1.clone()).collect::<Vec<_>>();
    loop {
        if i != last_index - 1 {
            f = f * f;
            for (r, &(a, _)) in r.iter().zip(pairs.iter()) {
                f = fp12_multiply_with_line_equal_native(&f, r, a);
            }
        }
        for r in r.iter_mut() {
            *r = (r.clone() + r.clone()).into();
        }

        assert!(pseudo_binary_encoding[i] <= 1 && pseudo_binary_encoding[i] >= -1);
        if pseudo_binary_encoding[i] != 0 {
            for ((r, neg_b), &(a, b)) in r.iter_mut().zip(neg_b.iter()).zip(pairs.iter()) {
                let sign_b = if pseudo_binary_encoding[i] == 1 {
                    b
                } else {
                    neg_b
                };
                f = fp12_multiply_with_line_unequal_native(&f, (r, sign_b), a);
                *r = (r.clone() + sign_b.clone()).into();
            }
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }

    let neg_one: BigUint = Fq::from(-1).into();
    let k = neg_one / BigUint::from(6u32);
    let expected_c = Fq2::new(Fq::from(1), Fq::one()).pow(k.to_u64_digits());

    let c2 = expected_c * expected_c;
    let c3 = c2 * expected_c;

    // finish multiplying remaining line functions outside the loop
    for (r, &(a, b)) in r.iter_mut().zip(pairs.iter()) {
        let b_1 = twisted_frobenius(b, c2, c3);
        let neg_b_2 = neg_twisted_frobenius(&b_1, c2, c3);
        f = fp12_multiply_with_line_unequal_native(&f, (r, &b_1), a);
        *r = (r.clone() + b_1).into();
        f = fp12_multiply_with_line_unequal_native(&f, (r, &neg_b_2), a);
    }
    f
}

pub fn conjugate_fp2(x: Fq2) -> Fq2 {
    Fp2 {
        c0: x.c0,
        c1: -x.c1,
    }
}

pub fn neg_conjugate_fp2(x: Fq2) -> Fq2 {
    Fp2 {
        c0: -x.c0,
        c1: x.c1,
    }
}

// PROBLEM BUT NO CONCERN
fn twisted_frobenius(Q: &G2Affine, c2: Fq2, c3: Fq2) -> G2Affine {
    let frob_x = conjugate_fp2(Q.x);
    let frob_y = conjugate_fp2(Q.y);
    let out_x = c2 * frob_x;
    let out_y = c3 * frob_y;
    println!(
        "twisted_frobenius are: (out_x; out_y) are: , {:?}, {:?}",
        out_x, out_y
    );
    G2Affine::new(out_x, out_y)
}

// PROBLEM BUT NO CONCERN
fn neg_twisted_frobenius(Q: &G2Affine, c2: Fq2, c3: Fq2) -> G2Affine {
    let frob_x = conjugate_fp2(Q.x);
    let neg_frob_y = neg_conjugate_fp2(Q.y);
    let out_x = c2 * frob_x;
    let out_y = c3 * neg_frob_y;
    println!(
        "neg_twisted_frobenius are: (out_x; out_y) are: , {:?}, {:?}",
        out_x, out_y
    );
    G2Affine::new(out_x, out_y)
}

// BIG CONCERN
pub const SIX_U_PLUS_2_NAF: [i8; 65] = [
    0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0,
    1, 1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0,
    0, 1, 0, 1, 1,
];

// 0000000000000000100000000000000000000000000000001000000001001011
// -1101001000000001000000000000000000000000000000010000000000000000
// 000000000000000010000000000000000000000000000000100000000100101-1
pub const PSEUDO_BINARY_ENCODING_NEGATIVE: [i8; 64] = [
    -1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,
];

pub const PSEUDO_BINARY_ENCODING_POSITIVE: [i8; 64] = [
    1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

pub const PSEUDO_BINARY_REVERSE_NEGATIVE: [i8; 64] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1,
    -1,
];

pub const PSEUDO_BINARY_ENCODING_REVERSE_POSITIVE: [i8; 64] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1,
];

pub const TEST: [i8; 64] = [
    0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

pub const _TEST: [i8; 381] = [
    1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1,
    1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0,
    0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0,
    0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1,
    0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1,
    1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1,
    0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1,
    1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1,
    1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1,
    0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1,
];

pub const _TEST_REVERSED: [i8; 381] = [
    1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1,
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1,
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0,
    0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1,
    0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0,
    1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1,
    0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0,
    1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0,
    0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0,
    0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0,
    0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1,
];

pub const TEST_PYTHON_CONSTANT: [i8; 64] = [    0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
1,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
1,
0,
0,
0,
0,
0,
0,
0,
0,
1,
0,
0,
1,
0,
1,
1,];

pub const TEST_NOIR_CONSTANT: [i8; 66] = [0, 0, 0, 1, 0, 1, 0, -1, 0, 0, -1, 0, 0, 0, 1, 0, 0, -1, 0, -1, 
0, 0, 0, 1, 0, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, -1, 0, 0, 
0, -1, 0, -1, 0, 0, 0, 1, 0, -1, 0, 1
];

pub const TEST_HASKELL_CONSTANT: [i8; 64] = [-1,-1, 0,-1, 0, 0,-1, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
];

pub fn miller_loop_native(Q: &G2Affine, P: &G1Affine) -> MyFq12 {
    miller_loop_BN_native(Q, P, &TEST_PYTHON_CONSTANT)
}

pub fn multi_miller_loop_native(pairs: Vec<(&G1Affine, &G2Affine)>) -> MyFq12 {
    multi_miller_loop_BN_native(pairs, &TEST_PYTHON_CONSTANT)
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{G1Affine, G2Affine};
    use ark_std::UniformRand;

    use super::{miller_loop_native, multi_miller_loop_native};

    #[test]
    fn test_multi_miller_loop_native() {
        let rng = &mut rand::thread_rng();
        let P0 = G1Affine::rand(rng);
        let P1 = G1Affine::rand(rng);
        let Q0 = G2Affine::rand(rng);
        let Q1 = G2Affine::rand(rng);
        let r0 = miller_loop_native(&Q0, &P0);
        let r1 = miller_loop_native(&Q1, &P1);
        let r_expected = r0 * r1;
        let r = multi_miller_loop_native(vec![(&P0, &Q0), (&P1, &Q1)]);
        assert_eq!(r, r_expected);
    }
}
