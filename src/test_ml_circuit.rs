use ark_ec::short_weierstrass::SWCurveConfig;
use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_bls12_381::{
    curves::{g1curve_target::G1Target, g2curve_target::G2Target},
    fields::{fq2_target::Fq2Target, fq_target::FqTarget},
};

pub struct G1Prepared<F: RichField + Extendable<D>, const D: usize>(pub G1Target<F, D>);

pub struct G2Prepared<F: RichField + Extendable<D>, const D: usize> {
    /// Stores the coefficients of the line evaluations as calculated in
    /// <https://eprint.iacr.org/2013/722.pdf>
    pub ell_coeffs: Vec<EllCoeff<F, D>>,
    pub infinity: bool,
}

impl<F: RichField + Extendable<D>, const D: usize> G2Prepared<F, D> {
    pub fn is_zero(&self) -> bool {
        self.infinity
    }
}

pub(crate) type EllCoeff<F, const D: usize> = (Fq2Target<F, D>, Fq2Target<F, D>, Fq2Target<F, D>);

pub struct G2Projective<F: RichField + Extendable<D>, const D: usize> {
    x: Fq2Target<F, D>,
    y: Fq2Target<F, D>,
    z: Fq2Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> G2Projective<F, D> {
    fn double_in_place(
        &mut self,
        builder: &mut CircuitBuilder<F, D>,
        two_inv: &FqTarget<F, D>,
    ) -> EllCoeff<F, D> {
        // Formula for line function when working with
        // homogeneous projective coordinates.

        let mut a = self.x.mul(builder, &self.y);
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

    fn add_in_place(&mut self, q: &G2Target<F, D>) -> EllCoeff<F, D> {
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

pub fn miller_loop_circuit<F: RichField + Extendable<D>, const D: usize>(
    a: impl IntoIterator<Item = impl Into<G1Prepared<F, D>>>,
    b: impl IntoIterator<Item = impl Into<G2Prepared<F, D>>>,
) {
}
