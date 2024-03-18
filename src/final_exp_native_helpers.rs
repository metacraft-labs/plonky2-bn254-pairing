use ark_bls12_381::Fq2;
use ark_ff::Field;

pub fn fq2_mul_by_nonresidue(a: Fq2) -> Fq2 {
    let a2 = a.double();
    let a4 = a2.double();
    let a8 = a4.double();

    let t = a8.c0 + a.c0;
    let c0 = t - a.c1;

    let t = a8.c1 + a.c0;
    let c1 = t + a.c1;

    Fq2 { c0, c1 }
}
