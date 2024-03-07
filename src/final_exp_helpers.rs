use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_bls12_381::fields::{
    bls12_381base::Bls12_381Base, fq12_target::Fq12Target, fq2_target::Fq2Target,
    fq_target::FqTarget,
};

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

// exp raises element by x = -15132376222941642752
pub fn exponentiate<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: Fq12Target<F, D>,
) -> Fq12Target<F, D> {
    let c = a.clone();
    let c = cyclotomic_square(builder, c); // (a ^ 2)

    // (a ^ (2 + 1)) ^ (2 ^ 2) = a ^ 12
    let c = c.mul(builder, &a);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);

    // (a ^ (12 + 1)) ^ (2 ^ 3) = a ^ 104
    let c = c.mul(builder, &a);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);

    // (a ^ (104 + 1)) ^ (2 ^ 9) = a ^ 53760
    let c = c.mul(builder, &a);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);

    // (a ^ (53760 + 1)) ^ (2 ^ 32) = a ^ 230901736800256
    let mut c = c.mul(builder, &a);
    for _ in 0..32 {
        c = cyclotomic_square(builder, c);
    }

    // (a ^ (230901736800256 + 1)) ^ (2 ^ 16) = a ^ 15132376222941642752
    let mut c = c.mul(builder, &a);
    for _ in 0..16 {
        c = cyclotomic_square(builder, c);
    }

    // invert chain result since x is negative
    c.confugate(builder)
}

// exponentiate drop raises element by x = -15132376222941642752 / 2
pub fn exponentiate_drop<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: Fq12Target<F, D>,
) -> Fq12Target<F, D> {
    let c = a.clone();
    let c = cyclotomic_square(builder, c); // (a ^ 2)

    // (a ^ (2 + 1)) ^ (2 ^ 2) = a ^ 12
    let c = c.mul(builder, &a);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);

    // (a ^ (12 + 1)) ^ (2 ^ 3) = a ^ 104
    let c = c.mul(builder, &a);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);

    // (a ^ (104 + 1)) ^ (2 ^ 9) = a ^ 53760
    let c = c.mul(builder, &a);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);
    let c = cyclotomic_square(builder, c);

    // (a ^ (53760 + 1)) ^ (2 ^ 32) = a ^ 230901736800256
    let mut c = c.mul(builder, &a);
    for _ in 0..32 {
        c = cyclotomic_square(builder, c);
    }

    // (a ^ (230901736800256 + 1)) ^ (2 ^ 16) = a ^ 15132376222941642752
    let mut c = c.mul(builder, &a);
    for _ in 0..15 {
        c = cyclotomic_square(builder, c);
    }
    // invert chain result since x is negative
    c.confugate(builder)
}

pub fn final_exponentiation<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    f: Fq12Target<F, D>,
) -> Fq12Target<F, D> {
    // easy part
    let result = f.clone();
    let t0 = f.confugate(builder);
    let result = result.inv(builder);
    let t0 = t0.mul(builder, &result);
    let result = t0.clone(); // frobenius_square
    let _result = result.mul(builder, &t0);

    // hard part

    f
}

pub fn frobenius_coeffs_12<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
) -> Vec<Fq2Target<F, D>> {
    vec![
        // z = u + 1
        // z ^ ((p ^ 0 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x760900000002fffd,
                    0xebf4000bc40c0002,
                    0x5f48985753c758ba,
                    0x77ce585370525745,
                    0x5c071a97a256ec6d,
                    0x15f65ec3fa80e493,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                ]),
            ),
        ]),
        // z ^ ((p ^ 1 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x07089552b319d465,
                    0xc6695f92b50a8313,
                    0x97e83cccd117228f,
                    0xa35baecab2dc29ee,
                    0x1ce393ea5daace4d,
                    0x08f2220fb0fb66eb,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0xb2f66aad4ce5d646,
                    0x5842a06bfc497cec,
                    0xcf4895d42599d394,
                    0xc11b9cba40a8e8d0,
                    0x2e3813cbe5a0de89,
                    0x110eefda88847faf,
                ]),
            ),
        ]),
        // z ^ ((p ^ 2 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0xecfb361b798dba3a,
                    0xc100ddb891865a2c,
                    0x0ec08ff1232bda8e,
                    0xd5c13cc6f1ca4721,
                    0x47222a47bf7b5c04,
                    0x0110f184e51c5f59,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                ]),
            ),
        ]),
        // z ^ ((p ^ 3 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x3e2f585da55c9ad1,
                    0x4294213d86c18183,
                    0x382844c88b623732,
                    0x92ad2afd19103e18,
                    0x1d794e4fac7cf0b9,
                    0x0bd592fc7d825ec8,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x7bcfa7a25aa30fda,
                    0xdc17dec12a927e7c,
                    0x2f088dd86b4ebef1,
                    0xd1ca2087da74d4a7,
                    0x2da2596696cebc1d,
                    0x0e2b7eedbbfd87d2,
                ]),
            ),
        ]),
        // z ^ ((p ^ 4 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x30f1361b798a64e8,
                    0xf3b8ddab7ece5a2a,
                    0x16a8ca3ac61577f7,
                    0xc26a2ff874fd029b,
                    0x3636b76660701c6e,
                    0x051ba4ab241b6160,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                ]),
            ),
        ]),
        // z ^ ((p ^ 5 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x3726c30af242c66c,
                    0x7c2ac1aad1b6fe70,
                    0xa04007fbba4b14a2,
                    0xef517c3266341429,
                    0x0095ba654ed2226b,
                    0x02e370eccc86f7dd,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x82d83cf50dbce43f,
                    0xa2813e53df9d018f,
                    0xc6f0caa53c65e181,
                    0x7525cf528d50fe95,
                    0x4a85ed50f4798a6b,
                    0x171da0fd6cf8eebd,
                ]),
            ),
        ]),
        // z ^ ((p ^ 6 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x43f5fffffffcaaae,
                    0x32b7fff2ed47fffd,
                    0x07e83a49a2e99d69,
                    0xeca8f3318332bb7a,
                    0xef148d1ea0f4c069,
                    0x040ab3263eff0206,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                ]),
            ),
        ]),
        // z ^ ((p ^ 7 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0xb2f66aad4ce5d646,
                    0x5842a06bfc497cec,
                    0xcf4895d42599d394,
                    0xc11b9cba40a8e8d0,
                    0x2e3813cbe5a0de89,
                    0x110eefda88847faf,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x07089552b319d465,
                    0xc6695f92b50a8313,
                    0x97e83cccd117228f,
                    0xa35baecab2dc29ee,
                    0x1ce393ea5daace4d,
                    0x08f2220fb0fb66eb,
                ]),
            ),
        ]),
        // z ^ ((p ^ 8 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0xcd03c9e48671f071,
                    0x5dab22461fcda5d2,
                    0x587042afd3851b95,
                    0x8eb60ebe01bacb9e,
                    0x03f97d6e83d050d2,
                    0x18f0206554638741,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                ]),
            ),
        ]),
        // z ^ ((p ^ 9 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x7bcfa7a25aa30fda,
                    0xdc17dec12a927e7c,
                    0x2f088dd86b4ebef1,
                    0xd1ca2087da74d4a7,
                    0x2da2596696cebc1d,
                    0x0e2b7eedbbfd87d2,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x3e2f585da55c9ad1,
                    0x4294213d86c18183,
                    0x382844c88b623732,
                    0x92ad2afd19103e18,
                    0x1d794e4fac7cf0b9,
                    0x0bd592fc7d825ec8,
                ]),
            ),
        ]),
        // z ^ ((p ^ 10 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x890dc9e4867545c3,
                    0x2af322533285a5d5,
                    0x50880866309b7e2c,
                    0xa20d1b8c7e881024,
                    0x14e4f04fe2db9068,
                    0x14e56d3f1564853a,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                ]),
            ),
        ]),
        // z ^ ((p ^ 11 - 1) / 6)
        Fq2Target::new(vec![
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x82d83cf50dbce43f,
                    0xa2813e53df9d018f,
                    0xc6f0caa53c65e181,
                    0x7525cf528d50fe95,
                    0x4a85ed50f4798a6b,
                    0x171da0fd6cf8eebd,
                ]),
            ),
            FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x3726c30af242c66c,
                    0x7c2ac1aad1b6fe70,
                    0xa04007fbba4b14a2,
                    0xef517c3266341429,
                    0x0095ba654ed2226b,
                    0x02e370eccc86f7dd,
                ]),
            ),
        ]),
    ]
}
