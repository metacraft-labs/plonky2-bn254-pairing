use ark_bls12_381::{Fq12, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::{BitIteratorBE, Field};
use ark_std::cfg_chunks_mut;

use crate::final_exp_native::BLS_X;

pub fn test_multi_miller_loop(
    a: impl IntoIterator<Item = impl Into<G1Affine>>,
    b: impl IntoIterator<Item = impl Into<G2Affine>>,
)  {
    use itertools::Itertools;

    let mut pairs = a
    .into_iter()
    .zip_eq(b)
    .filter_map(|(p, q)| {
        let (p, q) = (p.into(), q.into());
        match !p.is_zero() && !q.is_zero() {
            true => Some((p, q)),
            false => None,
        }
    })
    .collect::<Vec<_>>();

    let mut f = cfg_chunks_mut!(pairs, 4).map(|pairs|{
        let mut f = Fq12::ONE;
        for i in BitIteratorBE::without_leading_zeros([BLS_X]).skip(1) {
            f.square_in_place();
            for (p, coeffs) in pairs.iter_mut() {
                // Bls12::<Self>::ell(&mut f, &coeffs.next().unwrap(), &p.0);
            }
        }
    });


    // f
}
