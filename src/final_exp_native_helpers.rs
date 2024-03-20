use crate::final_exp_native::BLS_X;
use ark_bls12_381::{Fq, Fq12, Fq2, Fq6};
use ark_ff::Field;
use ark_std::Zero;
use plonky2::field::types::PrimeField;
use plonky2_bls12_381::fields::bls12_381base::Bls12_381Base;

pub fn fq2_mul_by_nonresidue(a: &Fq2) -> Fq2 {
    let a2 = a.double();
    let a4 = a2.double();
    let a8 = a4.double();

    let t = a8.c0 + a.c0;
    let c0 = t - a.c1;

    let t = a8.c1 + a.c0;
    let c1 = t + a.c1;

    Fq2 { c0, c1 }
}

pub fn fq4_square(c0: &mut Fq2, c1: &mut Fq2, a0: &Fq2, a1: &Fq2) {
    let t0 = a0.square();
    let t1 = a1.square();
    let mut t2 = fq2_mul_by_nonresidue(&t1);
    *c0 = t2 + t0;
    t2 = a0 + a1;
    t2 = t2.square();
    t2 = t2 - t0;
    *c1 = t2 - t1;
}

pub fn fq12_cyclotomic_square(x: &Fq12) -> Fq12 {
    let zero = Fq2::ZERO;
    let mut t3 = zero;
    let mut t4 = zero;
    let mut t5 = zero;
    let mut t6 = zero;

    fq4_square(&mut t3, &mut t4, &x.c0.c0, &x.c1.c1);
    let mut t2 = t3 - x.c0.c0;
    t2 = t2.double();
    let c00 = t2 + t3;

    t2 = t4 + x.c1.c1;
    t2 = t2.double();
    let c11 = t2 + t4;

    fq4_square(&mut t3, &mut t4, &x.c1.c0, &x.c0.c2);
    fq4_square(&mut t5, &mut t6, &x.c0.c1, &x.c1.c2);

    t2 = t3 - x.c0.c1;
    t2 = t2.double();
    let c01 = t2 + t3;
    t2 = t4 + x.c1.c2;
    t2 = t2.double();
    let c12 = t2 + t4;
    t3 = t6;
    t3 = fq2_mul_by_nonresidue(&t3);
    t2 = t3 + x.c1.c0;
    t2 = t2.double();
    let c10 = t2 + t3;
    t2 = t5 - x.c0.c2;
    t2 = t2.double();
    let c02 = t2 + t5;

    Fq12 {
        c0: Fq6 {
            c0: c00,
            c1: c01,
            c2: c02,
        },
        c1: Fq6 {
            c0: c10,
            c1: c11,
            c2: c12,
        },
    }
}

pub fn cycolotomic_exp(f: &Fq12) -> Fq12 {
    let x = BLS_X;
    let mut tmp = Fq12::ONE;
    let mut found_one = false;
    for i in (0..64).rev().map(|b| ((x >> b) & 1) == 1) {
        if found_one {
            tmp = fq12_cyclotomic_square(&tmp)
        } else {
            found_one = i;
        }

        if i {
            tmp = tmp * f;
        }
    }

    fq12_conjugate(&tmp)
}

pub fn fq12_conjugate(x: &Fq12) -> Fq12 {
    let mut r = x.clone();
    let c0 = r.c0;
    let c1 = *r.c1.neg_in_place();
    Fq12 { c0, c1 }
}

pub fn fq2_conjugate(a: &Fq2) -> Fq2 {
    Fq2 {
        c0: a.c0,
        c1: -a.c1,
    }
}

pub fn fq2_frobenius_map(x: Fq2, _power: usize) -> Fq2 {
    fq2_conjugate(&x)
}

pub fn fq6_frobenius_map(x: Fq6, power: usize) -> Fq6 {
    let c0 = fq2_frobenius_map(x.c0, power);
    let c1 = fq2_frobenius_map(x.c1, power);
    let c2 = fq2_frobenius_map(x.c2, power);

    let coeff_c1 = Fq2 {
        c0: Fq::zero(),
        c1: Fq::from(Bls12_381Base::to_canonical_biguint(&Bls12_381Base([
            0xcd03_c9e4_8671_f071,
            0x5dab_2246_1fcd_a5d2,
            0x5870_42af_d385_1b95,
            0x8eb6_0ebe_01ba_cb9e,
            0x03f9_7d6e_83d0_50d2,
            0x18f0_2065_5463_8741,
        ]))),
    };

    let c1 = c1 * coeff_c1;
    let coeff_c2 = Fq2 {
        c0: Fq::from(Bls12_381Base::to_canonical_biguint(&Bls12_381Base([
            0x890d_c9e4_8675_45c3,
            0x2af3_2253_3285_a5d5,
            0x5088_0866_309b_7e2c,
            0xa20d_1b8c_7e88_1024,
            0x14e4_f04f_e2db_9068,
            0x14e5_6d3f_1564_853a,
        ]))),
        c1: Fq::zero(),
    };

    let c2 = c2 * coeff_c2;

    Fq6 { c0, c1, c2 }
}

pub fn fq12_frobenius_map(x: Fq12, power: usize) -> Fq12 {
    let c0 = fq6_frobenius_map(x.c0, power);
    let c1 = fq6_frobenius_map(x.c1, power);

    let coeff = Fq2 {
        c0: Fq::from(Bls12_381Base::to_canonical_biguint(&Bls12_381Base([
            0x0708_9552_b319_d465,
            0xc669_5f92_b50a_8313,
            0x97e8_3ccc_d117_228f,
            0xa35b_aeca_b2dc_29ee,
            0x1ce3_93ea_5daa_ce4d,
            0x08f2_220f_b0fb_66eb,
        ]))),
        c1: Fq::from(Bls12_381Base::to_canonical_biguint(&Bls12_381Base([
            0xb2f6_6aad_4ce5_d646,
            0x5842_a06b_fc49_7cec,
            0xcf48_95d4_2599_d394,
            0xc11b_9cba_40a8_e8d0,
            0x2e38_13cb_e5a0_de89,
            0x110e_efda_8884_7faf,
        ]))),
    };

    let c1c0 = c1.c0 * coeff;
    let c1c1 = c1.c1 * coeff;
    let c1c2 = c1.c2 * coeff;

    Fq12 {
        c0,
        c1: Fq6 {
            c0: c1c0,
            c1: c1c1,
            c2: c1c2,
        },
    }
}

pub fn final_exponentiation(f: Fq12) -> Fq12 {
    const POWER_HOLDER: usize = 1;

    let mut t0 = fq12_frobenius_map(f, POWER_HOLDER);
    t0 = fq12_frobenius_map(t0, POWER_HOLDER);
    t0 = fq12_frobenius_map(t0, POWER_HOLDER);
    t0 = fq12_frobenius_map(t0, POWER_HOLDER);
    t0 = fq12_frobenius_map(t0, POWER_HOLDER);
    t0 = fq12_frobenius_map(t0, POWER_HOLDER);

    let mut t1 = f.inverse().unwrap();

    let mut t2 = t0 * t1;
    t1 = t2.clone();

    t2 = fq12_frobenius_map(t2, POWER_HOLDER);
    t2 = fq12_frobenius_map(t2, POWER_HOLDER);

    t2 = t2 * t1;
    t1 = fq12_cyclotomic_square(&t2);
    t1 = fq12_conjugate(&t1);
    let mut t3 = cycolotomic_exp(&t2);
    let mut t4 = fq12_cyclotomic_square(&t3);
    let mut t5 = t1 * t3;
    t1 = cycolotomic_exp(&t5);
    t0 = cycolotomic_exp(&t1);
    let mut t6 = cycolotomic_exp(&t0);
    t6 = t6 * t4;
    t4 = cycolotomic_exp(&t6);
    t5 = fq12_conjugate(&t5);
    let t = t5 * t2;
    t4 = t4 * t;
    t5 = fq12_conjugate(&t2);
    t1 = t1 * t2;

    for _ in 0..3 {
        t1 = fq12_frobenius_map(t1, POWER_HOLDER)
    }

    t6 = t6 * t5;
    t6 = fq12_frobenius_map(t6, POWER_HOLDER);
    t3 = t3 * t0;

    for _ in 0..2 {
        t3 = fq12_frobenius_map(t3, POWER_HOLDER)
    }

    t3 = t3 * t1;
    t3 = t3 * t6;

    t3 * t4
}
