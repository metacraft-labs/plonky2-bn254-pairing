use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_bls12_381::fields::{fq12_target::Fq12Target, fq2_target::Fq2Target};

pub fn mul_by_nonresidue<F: RichField + Extendable<D>, const D: usize>(
    a: &Fq2Target<F, D>,
    builder: &mut CircuitBuilder<F, D>,
) -> Fq2Target<F, D> {
    // Multiply a + bu by u + 1, getting
    // au + a + bu^2 + bu
    // and because u^2 = -1, we get
    // (a - b) + (a + b)u

    Fq2Target {
        coeffs: [
            a.coeffs[0].sub(builder, &a.coeffs[1]),
            a.coeffs[0].add(builder, &a.coeffs[1]),
        ],
    }
}

// Algorithm 9 https://eprint.iacr.org/2010/354.pdf
pub fn fq4_square<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: Fq2Target<F, D>,
    b: Fq2Target<F, D>,
) -> (Fq2Target<F, D>, Fq2Target<F, D>) {
    // Consider using optimized squaring instead of multiplication
    let t0 = a.mul(builder, &a);
    // Consider using optimized squaring instead of multiplication
    let t1 = b.mul(builder, &b);

    let mut t2 = mul_by_nonresidue(&t1, builder);
    let c0 = t2.add(builder, &t0);
    t2 = a.add(builder, &b);
    // Consider using optimized squaring instead of multiplication
    t2 = t2.mul(builder, &t2);
    t2 = t2.sub(builder, &t0);
    let c1 = t2.sub(builder, &t1);

    (c0, c1)
}

// https://www.math.u-bordeaux.fr/~damienrobert/csi/book/book.pdf 5.5.4 Arithmetic in Cyclotomic Subgroups
pub fn cyclotomic_square<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    f: Fq12Target<F, D>,
) -> Fq12Target<F, D> {
    let coeffs = f.coeffs;
    let c000 = coeffs[0].clone(); // w^0 u^0
    let c001 = coeffs[6].clone(); // w^0 u^1
    let c010 = coeffs[2].clone(); // w^2 u^0
    let c011 = coeffs[8].clone(); // w^2 u^1
    let c020 = coeffs[4].clone(); // w^4 u^0
    let c021 = coeffs[10].clone(); // w^4 u^1
    let c100 = coeffs[1].clone(); // w^1 u^0
    let c101 = coeffs[7].clone(); // w^1 u^1
    let c110 = coeffs[3].clone(); // w^3 u^0
    let c111 = coeffs[9].clone(); // w^3 u^1
    let c120 = coeffs[5].clone(); // w^5 u^0
    let c121 = coeffs[11].clone(); // w^5 u^1

    let mut z0 = Fq2Target::new(vec![c000, c001]);
    let mut z4 = Fq2Target::new(vec![c010, c011]);
    let mut z3 = Fq2Target::new(vec![c020, c021]);
    let mut z2 = Fq2Target::new(vec![c100, c101]);
    let mut z1 = Fq2Target::new(vec![c110, c111]);
    let mut z5 = Fq2Target::new(vec![c120, c121]);

    let (t0, t1) = fq4_square(builder, z0.clone(), z1.clone());

    // For A
    z0 = t0.sub(builder, &z0);
    z0 = z0.add(builder, &z0);
    z0 = z0.add(builder, &t0);

    z1 = t1.add(builder, &z1);
    z1 = z1.add(builder, &z1);
    z1 = z1.add(builder, &t1);

    let (mut t0, t1) = fq4_square(builder, z2.clone(), z3.clone());
    let (t2, t3) = fq4_square(builder, z4.clone(), z5.clone());

    // For C
    z4 = t0.sub(builder, &z4);
    z4 = z4.add(builder, &z4);
    z4 = z4.add(builder, &t0);

    z5 = t1.add(builder, &z5);
    z5 = z5.add(builder, &z5);
    z5 = z5.add(builder, &t1);

    // For B
    t0 = mul_by_nonresidue(&t3, builder);
    z2 = t0.add(builder, &z2);
    z2 = z2.add(builder, &z2);
    z2 = z2.add(builder, &t0);

    z3 = t2.sub(builder, &z3);
    z3 = z3.add(builder, &z3);
    z3 = z3.add(builder, &t2);

    let coeffs = vec![
        z0.coeffs[0].clone(),
        z4.coeffs[0].clone(),
        z3.coeffs[0].clone(),
        z2.coeffs[0].clone(),
        z1.coeffs[0].clone(),
        z5.coeffs[0].clone(),
        z0.coeffs[1].clone(),
        z4.coeffs[1].clone(),
        z3.coeffs[1].clone(),
        z2.coeffs[1].clone(),
        z1.coeffs[1].clone(),
        z5.coeffs[1].clone(),
    ];

    Fq12Target::new(coeffs)
}

pub fn exponentiate<F: RichField + Extendable<D>, const D: usize>() {}
pub fn exponentiate_drop<F: RichField + Extendable<D>, const D: usize>() {}
