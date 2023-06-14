use std::{
    fmt, io,
    ops::{BitOr, Deref},
};

use borsh::{BorshDeserialize, BorshSerialize};
use num_traits::cast::ToPrimitive;
use serde::{Deserialize, Serialize};
pub use zkp_u256::{Binary, DivRem};

#[derive(Clone, Default, PartialEq, Eq, Deserialize, Serialize, Debug, Hash)]
pub struct U256(zkp_u256::U256);

impl fmt::Display for U256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_hex())?;
        Ok(())
    }
}

impl BorshSerialize for U256 {
    fn serialize<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        <[u8; 32] as BorshSerialize>::serialize(&self.to_bytes(), writer)?;
        Ok(())
    }
}

impl BorshDeserialize for U256 {
    fn deserialize(buf: &mut &[u8]) -> io::Result<Self> {
        Ok(Self::from(&<[u8; 32] as BorshDeserialize>::deserialize(
            buf,
        )?))
    }

    fn deserialize_reader<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        Ok(Self::from(
            &<[u8; 32] as BorshDeserialize>::deserialize_reader(reader)?,
        ))
    }
}

#[cfg(feature = "jsonschema")]
impl schemars::JsonSchema for U256 {
    fn schema_name() -> String {
        "U256".to_owned()
    }

    fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        let mut schema = <String>::json_schema(gen);
        if let schemars::schema::Schema::Object(obj) = &mut schema {
            obj.string = Some(Box::new(schemars::schema::StringValidation {
                max_length: Some(66),
                min_length: Some(64),
                pattern: Some("^(0x)?[a-fA-F0-9]{64}$".to_owned()),
            }));
        }

        schema
    }
}

impl U256 {
    pub const ZERO: U256 = Self(zkp_u256::U256::ZERO);
    pub const ONE: U256 = Self(zkp_u256::U256::ONE);
    pub const MAX: U256 = Self(zkp_u256::U256::MAX);

    pub const fn from_u64(value: u64) -> U256 {
        U256(zkp_u256::U256::from_limbs([value, 0, 0, 0]))
    }
    pub fn from_decimal_str(input: &str) -> Self {
        U256(zkp_u256::U256::from_decimal_str(input).unwrap())
    }

    #[cfg(feature = "rand")]
    pub fn random<R: rand::Rng>(rng: &mut R) -> Self {
        Self(zkp_u256::U256::from_limbs([
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ]))
    }

    #[cfg(feature = "rand")]
    pub fn unique() -> Self {
        Self::random(&mut rand::thread_rng())
    }

    pub fn to_array(&self) -> [u8; 32] {
        self.0.to_bytes_be()
    }

    pub fn to_decimals_string(&self) -> String {
        self.0.to_decimal_string()
    }

    pub fn to_bytes(&self) -> [u8; 32] {
        self.to_array()
    }

    pub fn to_vec(&self) -> Vec<u8> {
        self.to_array().to_vec()
    }

    pub const fn as_limbs(&self) -> &[u64; 4] {
        self.0.as_limbs()
    }

    pub fn to_u64(&self) -> Option<u64> {
        self.0.to_u64()
    }

    pub fn normalize(self, denominator: Denominator) -> u64 {
        self.div_rem(&Self::from_u64(10u64).pow(denominator.get() as u64))
            .and_then(|(part, _fractal)| part.to_u64())
            .expect("Unreachable. `10 ** denominator != zero`")
    }

    pub fn checked_normalize(self, denominator: Denominator) -> Option<u64> {
        self.div_rem(&Self::from_u64(10u64).pow(denominator.get() as u64))
            .and_then(|(part, fractal)| {
                if fractal.is_zero() {
                    part.to_u64()
                } else {
                    None
                }
            })
    }

    pub fn to_hex(&self) -> String {
        self.0.to_hex_string()
    }

    pub fn pow(&self, exp: u64) -> U256 {
        Self(self.0.pow(exp))
    }

    pub fn from_hex(hex: &str) -> U256 {
        Self(zkp_u256::U256::from_hex_str(hex))
    }

    pub fn bit(&self, i: usize) -> bool {
        self.0.bit(i)
    }
}

impl BitOr for U256 {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0.bitor(&rhs.0))
    }
}

impl From<&[u8; 32]> for U256 {
    fn from(bytes: &[u8; 32]) -> Self {
        Self(zkp_u256::U256::from_bytes_be(bytes))
    }
}

impl From<[u8; 32]> for U256 {
    fn from(bytes: [u8; 32]) -> Self {
        Self(zkp_u256::U256::from_bytes_be(&bytes))
    }
}

impl From<[u64; 4]> for U256 {
    fn from(bytes: [u64; 4]) -> Self {
        Self(zkp_u256::U256::from_limbs(bytes))
    }
}

impl From<U256> for [u64; 4] {
    fn from(val: U256) -> Self {
        *val.as_limbs()
    }
}

impl From<U256> for [u8; 32] {
    fn from(val: U256) -> Self {
        val.to_bytes()
    }
}

impl<'link> From<&'link U256> for &'link [u64; 4] {
    fn from(val: &'link U256) -> Self {
        val.as_limbs()
    }
}

use std::convert::TryFrom;
impl TryFrom<&[u8]> for U256 {
    type Error = &'static str;
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        Ok(Self::from(
            &<[u8; 32]>::try_from(bytes).map_err(|_| "Wrong size for `U256`")?,
        ))
    }
}

fn bytes_to_limbs(bytes: &[u8]) -> Result<[u64; 4], &'static str> {
    if bytes.len() > 32 {
        return Err("bytes slice too long");
    }
    let mut result = [0u64; 4];
    let mut iter = bytes.iter().rev();
    for i in 0..4 {
        for j in 0..8 {
            if let Some(byte) = iter.next() {
                result[i] |= u64::from(*byte) << (8 * j);
            } else {
                return Ok(result);
            }
        }
    }
    Ok(result)
}

impl TryFrom<&str> for U256 {
    type Error = &'static str;
    fn try_from(number: &str) -> Result<Self, Self::Error> {
        Ok(U256::from(bytes_to_limbs(
            &hex::decode(number).map_err(|_| "Error while decode hex")?,
        )?))
    }
}

use std::ops::Add;
impl Add for U256 {
    type Output = U256;
    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0.add(rhs.0))
    }
}

use std::ops::Mul;

impl Mul<u64> for U256 {
    type Output = U256;
    fn mul(self, rhs: u64) -> Self::Output {
        Self(self.0.mul(rhs))
    }
}
impl Mul<u64> for &U256 {
    type Output = U256;
    fn mul(self, rhs: u64) -> Self::Output {
        U256((&self.0).mul(rhs))
    }
}
impl Mul<&U256> for U256 {
    type Output = U256;
    fn mul(self, rhs: &U256) -> Self::Output {
        Self(self.0.mul(&rhs.0))
    }
}

use num_traits::pow::Pow;
impl Pow<u64> for U256 {
    type Output = U256;
    fn pow(self, rhs: u64) -> Self::Output {
        Self(self.0.pow(rhs))
    }
}
use num_traits::Zero;
impl Zero for U256 {
    fn zero() -> Self {
        Self::ZERO
    }
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl DivRem<u64> for U256 {
    type Quotient = U256;
    type Remainder = u64;
    fn div_rem(&self, rhs: u64) -> Option<(Self::Quotient, Self::Remainder)> {
        self.0.div_rem(rhs).map(|(q, r)| (U256(q), r))
    }
}

impl DivRem<&U256> for U256 {
    type Quotient = U256;
    type Remainder = U256;
    fn div_rem(&self, rhs: &U256) -> Option<(Self::Quotient, Self::Remainder)> {
        self.0.div_rem(&rhs.0).map(|(q, r)| (U256(q), U256(r)))
    }
}

use std::ops::Sub;

impl Sub for U256 {
    type Output = U256;
    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0.sub(rhs.0))
    }
}

impl From<u128> for U256 {
    fn from(value: u128) -> Self {
        U256(zkp_u256::U256::from(value))
    }
}

impl From<u64> for U256 {
    fn from(value: u64) -> Self {
        U256(zkp_u256::U256::from(value))
    }
}

/// Denormalize solana amounts to use in debridge protocol
pub trait Denormalize {
    fn denormalize(self, denominator: Denominator) -> U256;
}

impl Denormalize for U256 {
    fn denormalize(self, denominator: Denominator) -> U256 {
        self.mul(&U256::from_u64(10).pow(denominator.get() as u64))
    }
}

impl Denormalize for u64 {
    fn denormalize(self, denominator: Denominator) -> U256 {
        U256::from_u64(self).denormalize(denominator)
    }
}

#[cfg(test)]
mod u256_tests {
    use super::*;

    #[test]
    fn denominate() {
        assert_eq!(
            U256::from(25600000000_u64),
            256.denormalize(Denominator::new(8).unwrap())
        );
    }

    #[test]
    fn zero_denominate() {
        assert_eq!(
            U256::from(256_u64),
            256.denormalize(Denominator::new(0).unwrap())
        );
    }
}

/// Offset of decimals
/// Due to different types for solana and evm networks, you have to shift decimals
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, BorshSerialize, BorshDeserialize)]
pub struct Denominator {
    value: u8,
}

const DENOMINATOR_LIMIT: u8 = 76;

impl Denominator {
    pub const ZERO: Denominator = Denominator { value: 0 };

    pub const DENOMINATION_DELTA: u8 = 8;

    /// Calculate decimals for Solana wrapped token based on common decimals value for EVM networks.
    ///
    /// This is necessary for compatibility with the general protocol. In Solana the amount of tokens
    /// in wallet is stored in the u64 type, and in EVM networks in u256 type.
    /// By agreement, if the token decimal from the EVM network is less than 8, then it remains unchanged in Solana.
    /// If it is more than 8, then the decimals of the wrapped token created in Solana are equal 8.
    pub fn get_wrapper_decimals(decimals: u8) -> Self {
        Self {
            value: decimals.min(Self::DENOMINATION_DELTA),
        }
    }

    /// Calculate the denominator for the solana wrapped token relative to the original token from the EVM network.
    ///
    /// This is necessary for compatibility with the general protocol. In Solana the amount of tokens
    /// in wallet is stored in the u64 type, and in EVM networks in u256 type.
    /// By agreement, the minimum value of the wrapped token in the Solana network will be 10^-8.
    /// Any less token value is rounded up to 0. If in the native network the smallest token value
    /// is more than 10-8, then in Solana the smallest value of the wrapped token
    /// will be the same as in the native network.
    pub fn from_decimals(decimals: u8) -> Option<Denominator> {
        Denominator::new(decimals.saturating_sub(Self::DENOMINATION_DELTA))
    }

    pub fn new(value: u8) -> Option<Self> {
        if value < DENOMINATOR_LIMIT {
            Some(Self { value })
        } else {
            None
        }
    }

    /// Create new `Denominator`
    ///
    /// # Safety
    /// `value` need to be less then `DENOMINATOR_LIMIT`
    pub unsafe fn new_unchecked(value: u8) -> Self {
        Self { value }
    }
    pub fn get(&self) -> u8 {
        self.value
    }
}

impl Deref for Denominator {
    type Target = u8;
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}
