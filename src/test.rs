use ark_bls12_381::Fq12;
use ark_ff::Field;
use plonky2_bls12_381::fields::native::MyFq12;

use crate::final_exp_native::{conjugate_fp12, experimental_pow, frobenius_map_native, BLS_X};

// out = in^{ (q^6 - 1)*(q^2 + 1) }
pub fn easy_part_native<'v>(a: MyFq12) -> MyFq12 {
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

pub fn hard_part_native(r: Fq12)-> Fq12 {
    // let i1: Fq12 = conjugate_fp12(i).into();
    // let i2: Fq12 = r.into();
    // let i2 = i2.inverse();
    // let temp = i1 * i2.unwrap();
    let mut y0 = r.square();
    let mut y1 = Fq12::ZERO;
    y1 = experimental_pow(r.into(), vec![BLS_X]).into();
    y1 = *y1.conjugate_in_place();
    let mut y2 = r;
    y2 = *y2.conjugate_in_place();

    y1 = y1 * y2;
    y2 = experimental_pow(y1.into(), vec![BLS_X].into()).into();
    y2 = *y2.conjugate_in_place();
    y1 = *y1.conjugate_in_place();
    y1 = y1 * y2;
    y2 = experimental_pow(y1.into(), vec![BLS_X].into()).into();
    y2 = *y2.conjugate_in_place();
    y1 = frobenius_map_native(y1.into(), 1).into();
    y1 = y1 * y2;
    let r = r * y0;
    y0 = experimental_pow(y1.into(), vec![BLS_X].into()).into();
    y0 = *y0.conjugate_in_place();
    y2 = experimental_pow(y0.into(), vec![BLS_X].into()).into();
    y2 = *y2.conjugate_in_place();
    y0 = y1;
    y0 = frobenius_map_native(y0.into(), 2).into();
    y1 = *y1.conjugate_in_place();
    y1 *= y2;
    y1 *= y0;
    let r = r * y1;
    r
}

pub fn test_hard_part_exponentiation(a: MyFq12) -> Fq12{
    let f0 = easy_part_native(a);
    let f = hard_part_native(f0.into());
    f
}
