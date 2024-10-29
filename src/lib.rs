use core::str;
use std::{array::TryFromSliceError, num::TryFromIntError, str::Utf8Error};

use num_bigint::{BigInt, ParseBigIntError};
use num_decimal::Num as BigDecimal;
use num_rational::BigRational;
use num_traits::{Signed, Zero};
use wasm_minimal_protocol::*;

enum RationalRepr {
    Integer(BigInt),
    RationalLtOne(BigRational),
    RationalGtOne(BigInt, BigRational),
}

impl RationalRepr {
    fn into_bytes(self) -> Vec<u8> {
        match self {
            RationalRepr::Integer(big_int) => {
                let s = big_int.to_string();
                let mut bytes = Vec::with_capacity(1 + s.len());
                bytes.push(0);
                bytes.extend_from_slice(s.as_bytes());
                bytes
            }
            RationalRepr::RationalLtOne(ratio) => {
                let (numer, denom) = ratio.into_raw();

                let (numer_sign, numer) = numer.into_parts();
                let (denom_sign, denom) = denom.into_parts();
                let sign = numer_sign * denom_sign;

                let numer = numer.to_string();
                let denom = denom.to_string();

                let mut bytes = Vec::with_capacity(1 + 1 + 8 + numer.len() + 8 + denom.len());
                bytes.push(1);
                bytes.push(sign as u8);
                bytes.extend_from_slice(&(numer.len() as i64).to_le_bytes());
                bytes.extend_from_slice(numer.as_bytes());
                bytes.extend_from_slice(&(denom.len() as i64).to_le_bytes());
                bytes.extend_from_slice(denom.as_bytes());
                bytes
            }
            RationalRepr::RationalGtOne(int_part, frac_part) => {
                let s = int_part.to_string();
                let (numer, denom) = frac_part.into_raw();
                let numer = numer.into_parts().1.to_string();
                let denom = denom.into_parts().1.to_string();
                let mut bytes =
                    Vec::with_capacity(1 + 8 + s.len() + 8 + numer.len() + 8 + denom.len());
                bytes.push(2);
                bytes.extend_from_slice(&(s.len() as i64).to_le_bytes());
                bytes.extend_from_slice(s.as_bytes());
                bytes.extend_from_slice(&(numer.len() as i64).to_le_bytes());
                bytes.extend_from_slice(numer.as_bytes());
                bytes.extend_from_slice(&(denom.len() as i64).to_le_bytes());
                bytes.extend_from_slice(denom.as_bytes());
                bytes
            }
        }
    }

    fn new(is_mixed: bool, number: BigRational) -> Self {
        if number.is_integer() {
            RationalRepr::Integer(number.into_raw().0)
        } else if !is_mixed || number.numer().magnitude() < number.denom().magnitude() {
            RationalRepr::RationalLtOne(number)
        } else {
            let big_int = number.numer() / number.denom();
            let ratio = number.fract();
            RationalRepr::RationalGtOne(big_int, ratio)
        }
    }
}

#[derive(Debug, thiserror::Error)]
enum Error {
    #[error("{0}")]
    Utf8(
        #[from]
        #[source]
        Utf8Error,
    ),
    #[error("{0}")]
    ParseBigInt(
        #[from]
        #[source]
        ParseBigIntError,
    ),
    #[error("Bool provided as more than 1 or 0 bytes (`is-mixed`)")]
    IsMixedFromSlice(#[source] TryFromSliceError),
    #[error("Failed to convert byte to bool (`is-mixed`)")]
    IsMixedNotBool,
    #[error("Integer provided as more or less than 8 bytes (`precision`)")]
    PrecisionFromBytes(#[source] TryFromSliceError),
    #[error("Integer provided as more or less than 8 bytes (`power`)")]
    PowerFromBytes(#[source] TryFromSliceError),
    #[error("Power must be less than or equal to {}, but was {0}", i32::MAX)]
    PowerTooBig(i64),
    #[error("Power must be greater than or equal to {}, but was {0}", i32::MIN)]
    PowerTooSmall(i64),
    #[error("Precision must be greater or equal to 0")]
    PrecisionNegative(#[source] TryFromIntError),
    #[error("Input too short: {0}")]
    InputTooShort(#[from] InputTooShortError),
    #[error("Division by zero")]
    DivByZero,
    #[error("`min` is greater than `max`")]
    MinGreaterThanMax,
}

initiate_protocol!();

#[wasm_func]
fn rational(numer: &[u8], denom: &[u8]) -> Result<Vec<u8>, Error> {
    let numer: BigInt = str::from_utf8(numer)?.parse()?;
    let denom: BigInt = str::from_utf8(denom)?.parse()?;
    let number = BigRational::new(numer, denom);

    Ok(big_ratio_to_bytes(number))
}

macro_rules! impl_bin_op {
    ($($(#[$meta:meta])* $name:ident($op1:ident, $op2:ident) => $e:expr);*$(;)?) => {
        $(
            $(#[$meta])*
            #[wasm_func]
            fn $name($op1: &[u8], $op2: &[u8]) -> Result<Vec<u8>, Error> {
                let $op1 = big_ratio_from_bytes($op1)?;
                let $op2 = big_ratio_from_bytes($op2)?;

                Ok(big_ratio_to_bytes($e))
            }
        )*
    };
}

impl_bin_op!(
    /// Add two rational numbers
    add(a, b) => a + b;
    /// Subtract two rational numbers
    sub(a, b) => a - b;
    /// Multiply two rational numbers
    mul(a, b) => a * b;
    /// Divide two rational numbers
    div(a, b) => a / b;
    /// Remainder of two rational numbers
    rem(a, b) => a % b;
    /// Absolute difference of two rational numbers
    abs_diff(a, b) => (a - b).abs();
    /// Compares and returns the minimum of two values.
    min(a, b) => a.min(b);
    /// Compares and returns the maximum of two values.
    max(a, b) => a.max(b);
);

#[wasm_func]
fn cmp(a: &[u8], b: &[u8]) -> Result<Vec<u8>, Error> {
    let a = big_ratio_from_bytes(a)?;
    let b = big_ratio_from_bytes(b)?;

    let result = a.cmp(&b) as i8 as i64;

    Ok(result.to_le_bytes().to_vec())
}

macro_rules! impl_un_op {
    ($($(#[$meta:meta])* $name:ident($op:ident) => $e:expr);*$(;)?) => {
        $(
            $(#[$meta])*
            #[wasm_func]
            fn $name($op: &[u8]) -> Result<Vec<u8>, Error> {
                let $op = big_ratio_from_bytes($op)?;
                Ok(big_ratio_to_bytes($e))
            }
        )*
    };
}

impl_un_op! {
    /// Returns the negation of the number.
    neg(x) => -x;
    /// Returns the absolute value of the number.
    abs(x) => x.abs();
    /// Rounds towards minus infinity.
    floor(x) => x.floor();
    /// Rounds towards plus infinity.
    ceil(x) => x.ceil();
    /// Rounds to the nearest integer. Rounds half-way cases away from zero.
    round(x) => x.round();
    /// Rounds towards zero.
    trunc(x) => x.trunc();
    /// Returns the fractional part of a number, with division rounded towards zero.
    ///
    /// Satisfies `x == add(trunc(x), fract(x))`.
    fract(x) => x.fract();
}

/// Returns the reciprocal.
///
/// Returns error if the number is zero.
#[wasm_func]
fn recip(number: &[u8]) -> Result<Vec<u8>, Error> {
    let number = big_ratio_from_bytes(number)?;
    if number.is_zero() {
        return Err(Error::DivByZero);
    }
    Ok(big_ratio_to_bytes(number.recip()))
}

/// Raises the Ratio to the power of an exponent.
#[wasm_func]
fn pow(number: &[u8], power: &[u8]) -> Result<Vec<u8>, Error> {
    let number = big_ratio_from_bytes(number)?;

    let power: i64 = i64::from_le_bytes(power.try_into().map_err(Error::PowerFromBytes)?);
    let power: i32 = if power > i32::MAX as i64 {
        return Err(Error::PowerTooBig(power));
    } else if power < i32::MIN as i64 {
        return Err(Error::PowerTooSmall(power));
    } else {
        power as i32
    };

    Ok(big_ratio_to_bytes(number.pow(power)))
}

/// Restrict a value to a certain interval.
///
/// Returns `max` if `number` is greater than `max`,
/// and `min` if `number` is less than `min`.
/// Otherwise returns `number`.
///
/// Returns error if `min` is greater than `max`.
#[wasm_func]
fn clamp(number: &[u8], min: &[u8], max: &[u8]) -> Result<Vec<u8>, Error> {
    let number = big_ratio_from_bytes(number)?;
    let min = big_ratio_from_bytes(min)?;
    let max = big_ratio_from_bytes(max)?;

    if min > max {
        return Err(Error::MinGreaterThanMax);
    }

    Ok(big_ratio_to_bytes(number.clamp(min, max)))
}

/// Returns the string representation of the rational number.
#[wasm_func]
fn repr(number: &[u8], is_mixed: &[u8]) -> Result<Vec<u8>, Error> {
    let [is_mixed] = <[u8; 1]>::try_from(is_mixed).map_err(Error::IsMixedFromSlice)?;
    let is_mixed: bool = bool_try_from_byte(is_mixed).ok_or(Error::IsMixedNotBool)?;

    let number = big_ratio_from_bytes(number)?;
    let repr = RationalRepr::new(is_mixed, number);

    Ok(repr.into_bytes())
}

#[wasm_func]
fn numerator(number: &[u8]) -> Result<Vec<u8>, Error> {
    let number = big_ratio_from_bytes(number)?;
    let numer = number.numer().to_string();

    Ok(numer.into_bytes())
}

#[wasm_func]
fn denominator(number: &[u8]) -> Result<Vec<u8>, Error> {
    let number = big_ratio_from_bytes(number)?;
    let denom = number.denom().to_string();

    Ok(denom.into_bytes())
}

fn bool_try_from_byte(byte: u8) -> Option<bool> {
    match byte {
        0 => Some(false),
        1 => Some(true),
        _ => None,
    }
}

#[wasm_func]
fn to_decimal_string(number: &[u8], precision: &[u8]) -> Result<Vec<u8>, Error> {
    let number = big_ratio_from_bytes(number)?;
    let (numer, denom) = number.into_raw();
    let number = BigDecimal::new(numer, denom);

    let precision = usize::try_from(i64::from_le_bytes(
        precision.try_into().map_err(Error::PrecisionFromBytes)?,
    ))
    .map_err(Error::PrecisionNegative)?;

    Ok(format!("{number:#.precision$}").into_bytes())
}

fn big_ratio_to_bytes(number: BigRational) -> Vec<u8> {
    let (numer, denom) = number.into_raw();

    let numer = numer.to_signed_bytes_le();
    let denom = denom.to_signed_bytes_le();

    let mut result =
        Vec::with_capacity(size_of::<usize>() + numer.len() + size_of::<usize>() + denom.len());
    result.extend_from_slice(&numer.len().to_le_bytes());
    result.extend_from_slice(&numer);
    result.extend_from_slice(&denom.len().to_le_bytes());
    result.extend_from_slice(&denom);

    result
}

fn big_ratio_from_bytes(bytes: &[u8]) -> Result<BigRational, Error> {
    let numer_len = usize::from_le_bytes(
        bytes
            .get(..size_of::<usize>())
            .ok_or(InputTooShortError::NumerLen)?
            .try_into()
            .unwrap(),
    );
    let numer = BigInt::from_signed_bytes_le(
        bytes[size_of::<usize>()..]
            .get(..numer_len)
            .ok_or(InputTooShortError::Numer(numer_len))?,
    );
    let denom_len = usize::from_le_bytes(
        bytes[size_of::<usize>() + numer_len..]
            .get(..size_of::<usize>())
            .ok_or(InputTooShortError::DenomLen)?
            .try_into()
            .unwrap(),
    );
    let denom = BigInt::from_signed_bytes_le(
        bytes[size_of::<usize>() + numer_len + size_of::<usize>()..]
            .get(..denom_len)
            .ok_or(InputTooShortError::Denom(denom_len))?,
    );

    Ok(BigRational::new_raw(numer, denom))
}

#[derive(Debug, thiserror::Error)]
enum InputTooShortError {
    #[error("Numerator length")]
    NumerLen,
    #[error("Numerator value (needs {0} bytes)")]
    Numer(usize),
    #[error("Denominator length")]
    DenomLen,
    #[error("Denominator value (needs {0} bytes)")]
    Denom(usize),
}
