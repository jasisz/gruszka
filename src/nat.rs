//! The kernel's Nat literals behind one thin layer: the bignum type
//! (`BigUint`) and the few operations the kernel calls on it, under
//! num-bigint's names, so that swapping the bignum library touches this file
//! only. The backend is num-bigint (MIT/Apache). Measured and not taken
//! (2026-11-21): malachite-nz (LGPL-3.0) was 10-23% faster in wall time on a
//! few Nat-heavy CFSG certificates and flat elsewhere; dashu-int used up to
//! 17% more memory with no steady gain.
//!
//! The Lean rules (truncated subtraction, division by zero, the size bound)
//! live at the call sites, not here.

/// What the kernel asks of a Nat beyond the operators (`+ - * / % & | ^`,
/// shifts by `usize`, comparisons, hashing). On num-bigint the call sites
/// reach its inherent methods of the same names, so some of these go unused.
#[allow(dead_code)]
pub trait NatExt: Sized {
    fn zero() -> Self;
    fn one() -> Self;
    fn is_zero(&self) -> bool;
    /// Significant bits, 0 for 0.
    fn bits(&self) -> u64;
    /// The 64-bit digits, least significant first (none for 0).
    fn iter_u64_digits(&self) -> impl DoubleEndedIterator<Item = u64> + ExactSizeIterator + '_;
    fn to_u64(&self) -> Option<u64>;
    fn to_u32(&self) -> Option<u32>;
    fn from_bytes_le(b: &[u8]) -> Self;
    /// From 32-bit digits, least significant first.
    fn new(d: Vec<u32>) -> Self;
    fn nat_pow(&self, k: u32) -> Self;
    fn nat_gcd(&self, y: &Self) -> Self;
    /// `self * d` for one 64-bit digit (a copy multiplied in place).
    fn mul_u64(&self, d: u64) -> Self;
    /// From 64-bit digits, least significant first.
    fn from_u64_digits(d: &[u64]) -> Self;
    /// Trailing one bits (0 for 0).
    fn trailing_ones(&self) -> u64;
    /// Trailing zero bits (None for 0).
    fn trailing_zeros(&self) -> Option<u64>;
}

mod backend {
    use num_traits::{One, ToPrimitive, Zero};
    pub use num_bigint::BigUint;

    pub const ZERO: BigUint = BigUint::ZERO;

    impl super::NatExt for BigUint {
        #[inline]
        fn zero() -> Self {
            ZERO
        }
        #[inline]
        fn one() -> Self {
            <BigUint as One>::one()
        }
        #[inline]
        fn is_zero(&self) -> bool {
            Zero::is_zero(self)
        }
        #[inline]
        fn bits(&self) -> u64 {
            BigUint::bits(self)
        }
        #[inline]
        fn iter_u64_digits(&self) -> impl DoubleEndedIterator<Item = u64> + ExactSizeIterator + '_ {
            BigUint::iter_u64_digits(self)
        }
        #[inline]
        fn to_u64(&self) -> Option<u64> {
            ToPrimitive::to_u64(self)
        }
        #[inline]
        fn to_u32(&self) -> Option<u32> {
            ToPrimitive::to_u32(self)
        }
        #[inline]
        fn from_bytes_le(b: &[u8]) -> Self {
            BigUint::from_bytes_le(b)
        }
        #[inline]
        fn new(d: Vec<u32>) -> Self {
            BigUint::new(d)
        }
        #[inline]
        fn nat_pow(&self, k: u32) -> Self {
            BigUint::pow(self, k)
        }
        #[inline]
        fn nat_gcd(&self, y: &Self) -> Self {
            num_integer::Integer::gcd(self, y)
        }
        #[inline]
        fn mul_u64(&self, d: u64) -> Self {
            self.clone() * d
        }
        fn from_u64_digits(d: &[u64]) -> Self {
            match d {
                [] => ZERO,
                [x] => BigUint::from(*x),
                _ => BigUint::new(d.iter().flat_map(|&x| [x as u32, (x >> 32) as u32]).collect()),
            }
        }
        #[inline]
        fn trailing_ones(&self) -> u64 {
            BigUint::trailing_ones(self)
        }
        #[inline]
        fn trailing_zeros(&self) -> Option<u64> {
            BigUint::trailing_zeros(self)
        }
    }
}

pub use backend::{BigUint, ZERO};

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn digits_and_bytes_round_trip() {
        assert_eq!(BigUint::zero().iter_u64_digits().len(), 0);
        assert_eq!(BigUint::zero().bits(), 0);
        assert!(BigUint::from_bytes_le(&[0, 0, 0]).is_zero());
        let n = BigUint::from_bytes_le(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0]);
        let d: Vec<u64> = n.iter_u64_digits().collect();
        assert_eq!(d, vec![0x0807060504030201, 9]);
        assert_eq!(n.bits(), 68);
        assert_eq!(n.to_u64(), None);
        assert_eq!(BigUint::new(vec![7, 0, 0]).to_u32(), Some(7));
        assert_eq!(BigUint::new(vec![0, 1]).to_u64(), Some(1 << 32));
        assert_eq!(BigUint::from(12u32).nat_gcd(&BigUint::from(18u32)), BigUint::from(6u32));
        assert_eq!(BigUint::from(0u32).nat_gcd(&BigUint::from(5u32)), BigUint::from(5u32));
        assert_eq!(BigUint::from(5u32).nat_gcd(&BigUint::from(0u32)), BigUint::from(5u32));
        assert!(BigUint::zero().nat_gcd(&BigUint::zero()).is_zero());
        assert_eq!(BigUint::from(3u32).nat_pow(4), BigUint::from(81u32));
        assert_eq!(BigUint::from(0u32).nat_pow(0), BigUint::one());
        assert_eq!(&BigUint::from(1u32) << 70usize >> 69usize, BigUint::from(2u32));
        assert_eq!(BigUint::from(5u32) - BigUint::one(), BigUint::from(4u32));
        assert_eq!(BigUint::from_u64_digits(&[1, 2, 0]), (BigUint::from(2u32) << 64usize) + 1u32);
        assert!(BigUint::from_u64_digits(&[0, 0]).is_zero());
        assert_eq!(NatExt::trailing_ones(&BigUint::from(0b0111u32)), 3);
        assert_eq!(NatExt::trailing_zeros(&BigUint::from(8u32)), Some(3));
        assert_eq!(NatExt::trailing_zeros(&BigUint::zero()), None);
    }
}
