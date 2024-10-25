use core::str;
use std::error::Error;

use num_bigint::BigInt;
use num_decimal::Num as BigDecimal;
use num_rational::BigRational;
use wasm_minimal_protocol::*;

initiate_protocol!();

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
                let numer = ratio.numer().to_string();
                let denom = ratio.denom().to_string();
                let mut bytes = Vec::with_capacity(1 + 8 + numer.len() + 8 + denom.len());
                bytes.push(1);
                bytes.extend_from_slice(&(numer.len() as i64).to_le_bytes());
                bytes.extend_from_slice(numer.as_bytes());
                bytes.extend_from_slice(&(denom.len() as i64).to_le_bytes());
                bytes.extend_from_slice(denom.as_bytes());
                bytes
            }
            RationalRepr::RationalGtOne(big_int, ratio) => {
                let s = big_int.to_string();
                let numer = ratio.numer().to_string();
                let denom = ratio.denom().to_string();
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
}

impl From<BigInt> for RationalRepr {
    fn from(big_int: BigInt) -> Self {
        RationalRepr::Integer(big_int)
    }
}

impl From<BigRational> for RationalRepr {
    fn from(value: BigRational) -> Self {
        if value.is_integer() {
            RationalRepr::Integer(value.into_raw().0)
        } else if value.numer() < value.denom() {
            RationalRepr::RationalLtOne(value)
        } else {
            let big_int = value.numer() / value.denom();
            let ratio = value.fract();
            RationalRepr::RationalGtOne(big_int, ratio)
        }
    }
}

#[wasm_func]
fn add(
    a_numer: &[u8],
    a_denom: &[u8],
    b_numer: &[u8],
    b_denom: &[u8],
) -> Result<Vec<u8>, Box<dyn Error>> {
    let a_numer: BigInt = str::from_utf8(a_numer)?.parse()?;
    let a_denom: BigInt = str::from_utf8(a_denom)?.parse()?;
    let a = BigRational::new(a_numer, a_denom);

    let b_numer: BigInt = str::from_utf8(b_numer)?.parse()?;
    let b_denom: BigInt = str::from_utf8(b_denom)?.parse()?;
    let b = BigRational::new(b_numer, b_denom);

    let c = a + b;
    let c_numer = c.numer().to_string();
    let c_denom = c.denom().to_string();

    let mut result = Vec::with_capacity(8 + c_numer.len() + 8 + c_denom.len());
    result.extend_from_slice(&(c_numer.len() as i64).to_le_bytes());
    result.extend_from_slice(c_numer.as_bytes());
    result.extend_from_slice(&(c_denom.len() as i64).to_le_bytes());
    result.extend_from_slice(c_denom.as_bytes());

    Ok(result)
}

#[wasm_func]
fn sub(
    a_numer: &[u8],
    a_denom: &[u8],
    b_numer: &[u8],
    b_denom: &[u8],
) -> Result<Vec<u8>, Box<dyn Error>> {
    let a_numer: BigInt = str::from_utf8(a_numer)?.parse()?;
    let a_denom: BigInt = str::from_utf8(a_denom)?.parse()?;
    let a = BigRational::new(a_numer, a_denom);

    let b_numer: BigInt = str::from_utf8(b_numer)?.parse()?;
    let b_denom: BigInt = str::from_utf8(b_denom)?.parse()?;
    let b = BigRational::new(b_numer, b_denom);

    let c = a - b;
    let c_numer = c.numer().to_string();
    let c_denom = c.denom().to_string();

    let mut result = Vec::with_capacity(8 + c_numer.len() + 8 + c_denom.len());
    result.extend_from_slice(&(c_numer.len() as i64).to_le_bytes());
    result.extend_from_slice(c_numer.as_bytes());
    result.extend_from_slice(&(c_denom.len() as i64).to_le_bytes());
    result.extend_from_slice(c_denom.as_bytes());

    Ok(result)
}

#[wasm_func]
fn mul(
    a_numer: &[u8],
    a_denom: &[u8],
    b_numer: &[u8],
    b_denom: &[u8],
) -> Result<Vec<u8>, Box<dyn Error>> {
    let a_numer: BigInt = str::from_utf8(a_numer)?.parse()?;
    let a_denom: BigInt = str::from_utf8(a_denom)?.parse()?;
    let a = BigRational::new(a_numer, a_denom);

    let b_numer: BigInt = str::from_utf8(b_numer)?.parse()?;
    let b_denom: BigInt = str::from_utf8(b_denom)?.parse()?;
    let b = BigRational::new(b_numer, b_denom);

    let c = a * b;
    let c_numer = c.numer().to_string();
    let c_denom = c.denom().to_string();

    let mut result = Vec::with_capacity(8 + c_numer.len() + 8 + c_denom.len());
    result.extend_from_slice(&(c_numer.len() as i64).to_le_bytes());
    result.extend_from_slice(c_numer.as_bytes());
    result.extend_from_slice(&(c_denom.len() as i64).to_le_bytes());
    result.extend_from_slice(c_denom.as_bytes());

    Ok(result)
}

#[wasm_func]
fn div(
    a_numer: &[u8],
    a_denom: &[u8],
    b_numer: &[u8],
    b_denom: &[u8],
) -> Result<Vec<u8>, Box<dyn Error>> {
    let a_numer: BigInt = str::from_utf8(a_numer)?.parse()?;
    let a_denom: BigInt = str::from_utf8(a_denom)?.parse()?;
    let a = BigRational::new(a_numer, a_denom);

    let b_numer: BigInt = str::from_utf8(b_numer)?.parse()?;
    let b_denom: BigInt = str::from_utf8(b_denom)?.parse()?;
    let b = BigRational::new(b_numer, b_denom);

    let c = a / b;
    let c_numer = c.numer().to_string();
    let c_denom = c.denom().to_string();

    let mut result = Vec::with_capacity(8 + c_numer.len() + 8 + c_denom.len());
    result.extend_from_slice(&(c_numer.len() as i64).to_le_bytes());
    result.extend_from_slice(c_numer.as_bytes());
    result.extend_from_slice(&(c_denom.len() as i64).to_le_bytes());
    result.extend_from_slice(c_denom.as_bytes());

    Ok(result)
}

#[wasm_func]
fn repr(numer: &[u8], denom: &[u8]) -> Result<Vec<u8>, Box<dyn Error>> {
    let numer: BigInt = str::from_utf8(numer)?.parse()?;
    let denom: BigInt = str::from_utf8(denom)?.parse()?;
    let value = BigRational::new(numer, denom);

    let repr = RationalRepr::from(value);

    Ok(repr.into_bytes())
}

#[wasm_func]
fn to_decimal_string(numer: &[u8], denom: &[u8]) -> Result<Vec<u8>, Box<dyn Error>> {
    let numer: BigInt = str::from_utf8(numer)?.parse()?;
    let denom: BigInt = str::from_utf8(denom)?.parse()?;
    let value = BigDecimal::new(numer, denom);

    Ok(value.to_string().into_bytes())
}

#[wasm_func]
fn abs_diff(
    a_numer: &[u8],
    a_denom: &[u8],
    b_numer: &[u8],
    b_denom: &[u8],
) -> Result<Vec<u8>, Box<dyn Error>> {
    let a_numer: BigInt = str::from_utf8(a_numer)?.parse()?;
    let a_denom: BigInt = str::from_utf8(a_denom)?.parse()?;
    let a = BigRational::new(a_numer, a_denom);

    let b_numer: BigInt = str::from_utf8(b_numer)?.parse()?;
    let b_denom: BigInt = str::from_utf8(b_denom)?.parse()?;
    let b = BigRational::new(b_numer, b_denom);

    let (c_numer, c_denom) = (a - b).into_raw();
    let c_numer = c_numer.into_parts().1.to_string();
    let c_denom = c_denom.into_parts().1.to_string();

    let mut result = Vec::with_capacity(8 + c_numer.len() + 8 + c_denom.len());
    result.extend_from_slice(&(c_numer.len() as i64).to_le_bytes());
    result.extend_from_slice(c_numer.as_bytes());
    result.extend_from_slice(&(c_denom.len() as i64).to_le_bytes());
    result.extend_from_slice(c_denom.as_bytes());

    Ok(result)
}

#[wasm_func]
fn cmp(
    a_numer: &[u8],
    a_denom: &[u8],
    b_numer: &[u8],
    b_denom: &[u8],
) -> Result<Vec<u8>, Box<dyn Error>> {
    let a_numer: BigInt = str::from_utf8(a_numer)?.parse()?;
    let a_denom: BigInt = str::from_utf8(a_denom)?.parse()?;
    let a = BigRational::new(a_numer, a_denom);

    let b_numer: BigInt = str::from_utf8(b_numer)?.parse()?;
    let b_denom: BigInt = str::from_utf8(b_denom)?.parse()?;
    let b = BigRational::new(b_numer, b_denom);

    let result = a.cmp(&b) as i8 as i64;

    Ok(result.to_le_bytes().to_vec())
}
