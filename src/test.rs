use ark_bls12_381::Fq12;
use ark_ff::Field;
use plonky2::{field::extension::Extendable, hash::hash_types::RichField, plonk::circuit_builder::CircuitBuilder};
use plonky2_bls12_381::fields::{fq12_target::Fq12Target, native::MyFq12};

use crate::{final_exp_native::{conjugate_fp12, experimental_pow, frobenius_map_native, BLS_X}, final_exp_target::{experimental_pow_target, frobenius_map}};

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

pub fn hard_part_target<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    r: Fq12Target<F, D>
) -> Fq12Target<F, D> {
    let mut y0 = r.mul(builder, &r); // optimize square
    let mut y1 = experimental_pow_target(builder, r.clone(), vec![BLS_X]);
    y1 = y1.confugate(builder); // Rename to conjugate in the other repo
    let mut y2 = r.clone();
    y2 = y2.confugate(builder);

    y1 = y1.mul(builder, &y2);
    y2 = experimental_pow_target(builder, y1.clone(), vec![BLS_X]);
    y2 = y2.confugate(builder);
    y1 = y1.confugate(builder);
    y1 = y1.mul(builder, &y2);
    y2 = experimental_pow_target(builder, y1.clone(), vec![BLS_X]);
    y2 = y2.confugate(builder);
    y1 = frobenius_map(builder, &y1, 1);
    y1 = y1.mul(builder, &y2);
    let r = r.mul(builder, &y0);
    y0 = experimental_pow_target(builder, y1.clone(), vec![BLS_X]);
    y0 = y0.confugate(builder);
    y2 = experimental_pow_target(builder, y0, vec![BLS_X]);
    y2 = y2.confugate(builder);
    y0 = y1.clone();
    y0 = frobenius_map(builder, &y0, 2);
    y1 = y1.confugate(builder);
    y1 = y1.mul(builder, &y2);
    y1 = y1.mul(builder, &y0);
    let r = r.mul(builder, &y1);

    r
}

pub fn test_hard_part_exponentiation(a: MyFq12) -> Fq12{
    let f0 = easy_part_native(a);
    let f = hard_part_native(f0.into());
    f
}
