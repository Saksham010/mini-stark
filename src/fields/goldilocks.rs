use ark_ff::{Fp, MontBackend};
use ark_ff_macros::MontConfig;

#[derive(Clone,Copy)]
#[derive(MontConfig)]
#[modulus = "18446744069414584321"] // 2^64 - 2^32 + 1 (Goldilocks)
#[generator = "7"]
pub struct GoldilocksConfig;  

pub type FpGoldilocks = Fp<MontBackend<GoldilocksConfig, 1>, 1>;
