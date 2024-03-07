use std::ops::Mul;

use ark_bls12_381::{Fq12, Fq2, Fq6};
use num::One;
const BLS_X: u64 = 0xd201_0000_0001_0000;

pub fn mul_by_nonresidue_native(a: Fq2) -> Fq2 {
    // Multiply a + bu by u + 1, getting
    // au + a + bu^2 + bu
    // and because u^2 = -1, we get
    // (a - b) + (a + b)u

    Fq2 {
        c0: a.c0 - a.c1,
        c1: a.c0 + a.c1,
    }
}

fn fp4_square_native(a: Fq2, b: Fq2) -> (Fq2, Fq2) {
    let t0 = a.mul(a);
    let t1 = b.mul(b);
    let mut t2 = mul_by_nonresidue_native(t1);
    let c0 = t2 + t0;
    t2 = a + b;
    t2 = t2.mul(t2);
    t2 -= t0;
    let c1 = t2 - t1;

    (c0, c1)
}

fn cyclotomic_square_native(f: Fq12) -> Fq12 {
    // https://www.math.u-bordeaux.fr/~damienrobert/csi/book/book.pdf 5.5.4
    let mut z0 = f.c0.c0;
    let mut z4 = f.c0.c1;
    let mut z3 = f.c0.c2;
    let mut z2 = f.c1.c0;
    let mut z1 = f.c1.c1;
    let mut z5 = f.c1.c2;

    let (t0, t1) = fp4_square_native(z0, z1);

    // For A
    z0 = t0 - z0;
    z0 = z0 + z0 + t0;

    z1 = t1 + z1;
    z1 = z1 + z1 + t1;

    let (mut t0, t1) = fp4_square_native(z2, z3);
    let (t2, t3) = fp4_square_native(z4, z5);

    // For C
    z4 = t0 - z4;
    z4 = z4 + z4 + t0;

    z5 = t1 + z5;
    z5 = z5 + z5 + t1;

    // For B
    t0 = mul_by_nonresidue_native(t3);
    z2 = t0 + z2;
    z2 = z2 + z2 + t0;

    z3 = t2 - z3;
    z3 = z3 + z3 + t2;

    Fq12 {
        c0: Fq6 {
            c0: z0,
            c1: z4,
            c2: z3,
        },
        c1: Fq6 {
            c0: z2,
            c1: z1,
            c2: z5,
        },
    }
}

pub fn cyclotomic_exp_native(f: Fq12) -> Fq12 {
    let x = BLS_X;
    let mut tmp = Fq12::one();
    let mut found_one = false;
    for i in (0..64).rev().map(|b| ((x >> b) & 1) == 1) {
        if found_one {
            tmp = cyclotomic_square_native(tmp)
        } else {
            found_one = i;
        }

        if i {
            tmp *= f;
        }
    }

    *tmp.conjugate_in_place()
}

// exp raises element by x = -15132376222941642752
pub fn exponentiate_native(a: Fq12) -> Fq12 {
    let c = a.clone();
    let c = cyclotomic_square_native(c); // (a ^ 2)

    // (a ^ (2 + 1)) ^ (2 ^ 2) = a ^ 12
    let c = c.mul(a);
    let c = cyclotomic_square_native(c);
    let c = cyclotomic_square_native(c);

    // (a ^ (12 + 1)) ^ (2 ^ 3) = a ^ 104
    let c = c.mul(a);
    let c = cyclotomic_square_native(c);
    let c = cyclotomic_square_native(c);
    let c = cyclotomic_square_native(c);

    // (a ^ (104 + 1)) ^ (2 ^ 9) = a ^ 53760
    let c = c.mul(a);
    let c = cyclotomic_square_native(c);
    let c = cyclotomic_square_native(c);
    let c = cyclotomic_square_native(c);
    let c = cyclotomic_square_native(c);
    let c = cyclotomic_square_native(c);
    let c = cyclotomic_square_native(c);
    let c = cyclotomic_square_native(c);
    let c = cyclotomic_square_native(c);
    let c = cyclotomic_square_native(c);

    // (a ^ (53760 + 1)) ^ (2 ^ 32) = a ^ 230901736800256
    let mut c = c.mul(a);
    for _ in 0..32 {
        c = cyclotomic_square_native(c);
    }

    // (a ^ (230901736800256 + 1)) ^ (2 ^ 16) = a ^ 15132376222941642752
    let mut c = c.mul(a);
    for _ in 0..16 {
        c = cyclotomic_square_native(c);
    }

    // invert chain result since x is negative
    -c
}

// exp raises element by x = -15132376222941642752
// pub fn alternative_exponentiate_native(a: Fq12) -> Fq12 {

// }
