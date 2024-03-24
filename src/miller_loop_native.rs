#![allow(non_snake_case)]

use ark_bls12_381::{Fq, Fq2, G1Affine, G2Affine};
use ark_ff::Fp2;
use ark_std::{One, Zero};

use plonky2_bls12_381::fields::native::MyFq12;

// From https://crypto.stanford.edu/pbc/notes/ep/miller.html#:~:text=)-,Lines,-%3A
fn sparse_line_function_unequal_native(
    Q: (&G2Affine, &G2Affine),
    P: &G1Affine,
) -> Vec<Option<Fq2>> {
    let (x_1, y_1) = (&Q.0.x, &Q.0.y);
    let (x_2, y_2) = (&Q.1.x, &Q.1.y);
    let (x, y) = (&P.x, &P.y);

    let y1_minus_y2 = y_1 - y_2;
    let x2_minus_x1 = x_2 - x_1;
    let x1y2 = x_1 * y_2;
    let x2y1 = x_2 * y_1;

    let out3 = y1_minus_y2 * Fq2::new(x.clone(), Fq::zero());
    let out2 = x2_minus_x1 * Fq2::new(y.clone(), Fq::zero());
    let out5 = x1y2 - x2y1;

    vec![None, None, Some(out2), Some(out3), None, Some(out5)]
}

// https://crypto.stanford.edu/pbc/notes/ep/miller.html#:~:text=scaled%20as%20follows%3A-,Tangents%3A,-%E2%88%92
fn sparse_line_function_equal_native(Q: &G2Affine, P: &G1Affine) -> Vec<Option<Fq2>> {
    let (x, y) = (&Q.x, &Q.y);
    let x_sq = x * x;
    let x_cube = x_sq * x;
    let three_x_cu = x_cube * Fq2::from(3);
    let y_sq = y * y;
    let two_y_sq = y_sq * Fq2::from(2);
    let out0_left = three_x_cu - two_y_sq;
    let out0 = out0_left * Fq2::new(Fq::from(1), Fq::one());
    let x_sq_px: Fq2 = x_sq * Fq2::new(P.x, Fq::zero());
    let out4 = x_sq_px * Fq2::from(-3);
    let y_py = y * Fq2::new(P.y, Fq::zero());
    let out3 = y_py * Fq2::from(2);
    vec![Some(out0), None, None, Some(out3), Some(out4), None]
}

fn sparse_fp12_multiply_native(a: &MyFq12, b: Vec<Option<Fq2>>) -> MyFq12 {
    let mut a_fp2_coeffs = Vec::with_capacity(6);
    for i in 0..6 {
        a_fp2_coeffs.push(Fq2::new(a.coeffs[i].clone(), a.coeffs[i + 6].clone()));
    }
    // a * b as element of Fp2[w] without evaluating w^6 = (I_0 + u)
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

fn fp12_multiply_with_line_equal_native(g: &MyFq12, Q: &G2Affine, P: &G1Affine) -> MyFq12 {
    let line: Vec<Option<Fq2>> = sparse_line_function_equal_native(Q, P);
    sparse_fp12_multiply_native(g, line)
}

fn fp12_multiply_with_line_unequal_native(
    g: &MyFq12,
    Q: (&G2Affine, &G2Affine),
    P: &G1Affine,
) -> MyFq12 {
    let line: Vec<Option<Fq2>> = sparse_line_function_unequal_native(Q, P);
    sparse_fp12_multiply_native(g, line)
}

fn _miller_loop_native(Q: &G2Affine, P: &G1Affine, pseudo_binary_encoding: &[u8]) -> MyFq12 {
    let mut i = pseudo_binary_encoding.len() - 1;

    while pseudo_binary_encoding[i] == 0 {
        i -= 1;
    }
    let last_index = i;
    assert!(pseudo_binary_encoding[i] == 1);
    let mut R = Q.clone();
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

        assert!(pseudo_binary_encoding[i] <= 1);
        if pseudo_binary_encoding[i] != 0 {
            let sign_Q = Q.clone();
            f = fp12_multiply_with_line_unequal_native(&f, (&R, &sign_Q), P);
            R = (R + sign_Q).into();
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }

    f
}

fn _multi_miller_loop_native(
    pairs: Vec<(&G1Affine, &G2Affine)>,
    pseudo_binary_encoding: &[u8],
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

        assert!(pseudo_binary_encoding[i] <= 1);
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

pub const PSEUDO_BINARY_ENCODING: [u8; 64] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1,
];

pub fn miller_loop_native(Q: &G2Affine, P: &G1Affine) -> MyFq12 {
    _miller_loop_native(Q, P, &PSEUDO_BINARY_ENCODING)
}

pub fn multi_miller_loop_native(pairs: Vec<(&G1Affine, &G2Affine)>) -> MyFq12 {
    _multi_miller_loop_native(pairs, &PSEUDO_BINARY_ENCODING)
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Fq12, G1Affine, G2Affine};
    use ark_ec::pairing::Pairing;
    use ark_ff::Field;
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

    #[test]
    fn test_miller_loop_ark() {
        let p0 = G1Affine::identity();
        let q0 = G2Affine::identity();
        let one = Fq12::ONE;
        let mlr = ark_bls12_381::Bls12_381::miller_loop(p0, q0);
        assert_eq!(one, mlr.0);
    }
}
