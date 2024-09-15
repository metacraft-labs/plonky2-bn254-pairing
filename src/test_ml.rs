use ark_bls12_381::{Fq, Fq12, Fq2, G1Affine, G2Affine};
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ec::AffineRepr;
use ark_ff::{BitIteratorBE, Field};
use ark_std::cfg_chunks_mut;
use ark_std::One;

use crate::final_exp_native::{BLS_X, BLS_X_IS_NEGATIVE};

pub struct G1Prepared(pub G1Affine);
pub struct G2Prepared {
    /// Stores the coefficients of the line evaluations as calculated in
    /// <https://eprint.iacr.org/2013/722.pdf>
    pub ell_coeffs: Vec<EllCoeff>,
    pub infinity: bool,
}

impl G2Prepared {
    pub fn is_zero(&self) -> bool {
        self.infinity
    }
}

pub(crate) type EllCoeff = (Fq2, Fq2, Fq2);

pub struct G2Projective {
    x: Fq2,
    y: Fq2,
    z: Fq2,
}

impl G2Projective {
    fn double_in_place(&mut self, two_inv: &Fq) -> EllCoeff {
        // Formula for line function when working with
        // homogeneous projective coordinates.

        let mut a = self.x * &self.y;
        a.mul_assign_by_fp(two_inv);
        let b = self.y.square();
        let c = self.z.square();
        let coeff_b = ark_bls12_381::g2::Config::COEFF_B;
        let e = coeff_b * &(c.double() + &c);
        let f = e.double() + &e;
        let mut g = b + &f;
        g.mul_assign_by_fp(two_inv);
        let h = (self.y + &self.z).square() - &(b + &c);
        let i = e - &b;
        let j = self.x.square();
        let e_square = e.square();

        self.x = a * &(b - &f);
        self.y = g.square() - &(e_square.double() + &e_square);
        self.z = b * &h;
        (i, j.double() + &j, -h)
    }

    fn add_in_place(&mut self, q: &G2Affine) -> EllCoeff {
        let (qx, qy) = q.xy().unwrap();
        // Formula for line function when working with
        // homogeneous projective coordinates.
        let theta = self.y - &(qy * &self.z);
        let lambda = self.x - &(qx * &self.z);
        let c = theta.square();
        let d = lambda.square();
        let e = lambda * &d;
        let f = self.z * &c;
        let g = self.x * &d;
        let h = e + &f - &g.double();
        self.x = lambda * &h;
        self.y = theta * &(g - &h) - &(e * &self.y);
        self.z *= &e;
        let j = theta * qx - &(lambda * qy);

        (j, -theta, lambda)
    }
}

impl From<G2Affine> for G2Prepared {
    fn from(q: G2Affine) -> Self {
        let two_inv = Fq::one().double().inverse().unwrap();
        let zero = G2Prepared {
            ell_coeffs: vec![],
            infinity: true,
        };
        q.xy().map_or(zero, |(q_x, q_y)| {
            let mut ell_coeffs = vec![];
            let mut r = G2Projective {
                x: *q_x,
                y: *q_y,
                z: Fq2::one(),
            };

            for i in BitIteratorBE::new([BLS_X]).skip(1) {
                ell_coeffs.push(r.double_in_place(&two_inv));

                if i {
                    ell_coeffs.push(r.add_in_place(&q));
                }
            }

            Self {
                ell_coeffs,
                infinity: false,
            }
        })
    }
}

pub fn test_multi_miller_loop(
    a: impl IntoIterator<Item = impl Into<G1Prepared>>,
    b: impl IntoIterator<Item = impl Into<G2Prepared>>,
) -> Fq12 {
    use itertools::Itertools;

    let mut pairs = a
        .into_iter()
        .zip_eq(b)
        .filter_map(|(p, q)| {
            let (p, q) = (p.into(), q.into());
            match !p.0.is_zero() && !q.is_zero() {
                true => Some((p, q.ell_coeffs.into_iter())),
                false => None,
            }
        })
        .collect::<Vec<_>>();

    let mut f: Fq12 = cfg_chunks_mut!(pairs, 4)
        .map(|pairs| {
            let mut f = Fq12::ONE;
            for i in BitIteratorBE::without_leading_zeros([BLS_X]).skip(1) {
                f.square_in_place();
                for (p, coeffs) in pairs.iter_mut() {
                    ell(&mut f, coeffs.next().unwrap(), p.0);
                }
                if i {
                    for (p, coeffs) in pairs.iter_mut() {
                        ell(&mut f, coeffs.next().unwrap(), p.0);
                    }
                }
            }
            f
        })
        .product();

    if BLS_X_IS_NEGATIVE {
        f.conjugate_in_place();
    }

    f
}

pub fn ell(f: &mut Fq12, g2_coeffs: EllCoeff, p: G1Affine) {
    let c0 = g2_coeffs.0;
    let mut c1 = g2_coeffs.1;
    let mut c2 = g2_coeffs.2;
    let (px, py) = p.xy().unwrap();

    c2.mul_assign_by_fp(&py);
    c1.mul_assign_by_fp(&px);
    f.mul_by_014(&c0, &c1, &c2);
}
