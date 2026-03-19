use std::fmt;
use std::str::FromStr;

use malachite_base::num::logic::traits::SignificantBits;

/// A dense univariate polynomial over a coefficient type `T`.
///
/// Represented as a vector of coefficients `[a_0, a_1, ..., a_n]` where `a_n ≠ 0`
/// (unless the polynomial is zero, in which case the vector is empty).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DensePoly<T> {
    pub coeffs: Vec<T>,
}

impl<T> DensePoly<T> {
    /// The zero polynomial.
    pub fn zero() -> Self {
        DensePoly { coeffs: Vec::new() }
    }
}

// ── SignificantBits ──────────────────────────────────────────────────────────

impl<'a, T> SignificantBits for &'a DensePoly<T>
where
    &'a T: SignificantBits,
{
    /// Sum of the significant bits of all coefficients.
    fn significant_bits(self) -> u64 {
        self.coeffs.iter().map(|c| c.significant_bits()).sum()
    }
}

// ── Display ──────────────────────────────────────────────────────────────────

impl<T: fmt::Display> fmt::Display for DensePoly<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.coeffs.is_empty() {
            return write!(f, "0");
        }
        let mut first = true;
        for (i, c) in self.coeffs.iter().enumerate().rev() {
            if !first {
                write!(f, "+")?;
            }
            match i {
                0 => write!(f, "{c}")?,
                1 => write!(f, "{c}*x")?,
                _ => write!(f, "{c}*x^{i}")?,
            }
            first = false;
        }
        Ok(())
    }
}

// ── Parsing ──────────────────────────────────────────────────────────────────

/// Trait for coefficient types that can be parsed from a monomial's coefficient string.
pub trait ParseCoeff: Sized {
    fn parse_coeff(s: &str) -> Option<Self>;
    fn zero_val() -> Self;
    fn is_zero_val(&self) -> bool;
}

/// Split a polynomial string into monomial chunks, handling `+` and `-` as separators.
/// Matches the Lean `splitPolynomialChars` logic.
fn split_polynomial(s: &str) -> Vec<String> {
    if s.is_empty() {
        return Vec::new();
    }
    let mut result: Vec<String> = Vec::new();
    let mut current = String::new();
    for ch in s.chars() {
        match ch {
            '+' => {
                if !current.is_empty() {
                    result.push(std::mem::take(&mut current));
                }
            }
            '-' => {
                if current.is_empty() {
                    current.push('-');
                } else {
                    result.push(std::mem::take(&mut current));
                    current.push('-');
                }
            }
            _ => current.push(ch),
        }
    }
    if !current.is_empty() {
        result.push(current);
    }
    result
}

/// Parse a single monomial string like "3*x^2", "x", "-5", "x^10", "-x^3", etc.
/// Returns `(degree, coefficient)`.
fn parse_monomial<T: ParseCoeff>(s: &str) -> Option<(usize, T)> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }

    match s.split_once('x') {
        None => {
            // No 'x' → constant term
            let c = T::parse_coeff(s)?;
            Some((0, c))
        }
        Some((prefix, suffix)) => {
            // Has 'x' → parse coefficient prefix and exponent suffix
            let coeff = match prefix {
                "" | "+" => T::parse_coeff("1")?,
                "-" => T::parse_coeff("-1")?,
                p => {
                    // Strip trailing '*' if present
                    let p = p.strip_suffix('*').unwrap_or(p);
                    T::parse_coeff(p)?
                }
            };
            let degree = match suffix {
                "" => 1,
                s => {
                    let s = s.strip_prefix('^')?;
                    s.parse::<usize>().ok()?
                }
            };
            Some((degree, coeff))
        }
    }
}

impl<T: ParseCoeff> FromStr for DensePoly<T> {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        if s == "0" {
            return Ok(DensePoly::zero());
        }

        let parts = split_polynomial(s);
        if parts.is_empty() {
            return Err("empty polynomial string".into());
        }

        let mut monomials: Vec<(usize, T)> = Vec::new();
        for part in &parts {
            let (d, c) = parse_monomial::<T>(part)
                .ok_or_else(|| format!("cannot parse monomial: {:?}", part))?;
            monomials.push((d, c));
        }

        // Check for duplicate exponents
        let mut seen_exps: Vec<usize> = monomials.iter().map(|(d, _)| *d).collect();
        seen_exps.sort_unstable();
        seen_exps.dedup();
        if seen_exps.len() != monomials.len() {
            return Err("duplicate exponents".into());
        }

        // Build coefficient array
        let max_deg = monomials.iter().map(|(d, _)| *d).max().unwrap_or(0);
        let mut coeffs: Vec<T> = (0..=max_deg).map(|_| T::zero_val()).collect();
        for (d, c) in monomials {
            coeffs[d] = c;
        }

        // Normalize: drop trailing zeros
        while coeffs.last().map_or(false, |c| c.is_zero_val()) {
            coeffs.pop();
        }

        Ok(DensePoly { coeffs })
    }
}

// ── ParseCoeff implementations ──────────────────────────────────────────────

use malachite_nz::natural::Natural;
use malachite_nz::integer::Integer;
use malachite_q::Rational;

impl ParseCoeff for Natural {
    fn parse_coeff(s: &str) -> Option<Self> {
        Natural::from_str(s).ok()
    }
    fn zero_val() -> Self {
        Natural::from(0u32)
    }
    fn is_zero_val(&self) -> bool {
        *self == Natural::from(0u32)
    }
}

impl ParseCoeff for Integer {
    fn parse_coeff(s: &str) -> Option<Self> {
        Integer::from_str(s).ok()
    }
    fn zero_val() -> Self {
        Integer::from(0)
    }
    fn is_zero_val(&self) -> bool {
        *self == Integer::from(0)
    }
}

impl ParseCoeff for Rational {
    fn parse_coeff(s: &str) -> Option<Self> {
        // Malachite Rational::from_str handles "num/den" and plain integers
        Rational::from_str(s).ok()
    }
    fn zero_val() -> Self {
        Rational::from(0)
    }
    fn is_zero_val(&self) -> bool {
        *self == Rational::from(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_zero() {
        let p: DensePoly<Integer> = "0".parse().unwrap();
        assert!(p.coeffs.is_empty());
    }

    #[test]
    fn test_parse_constant() {
        let p: DensePoly<Integer> = "42".parse().unwrap();
        assert_eq!(p.coeffs.len(), 1);
        assert_eq!(p.coeffs[0], Integer::from(42));
    }

    #[test]
    fn test_parse_polynomial() {
        let p: DensePoly<Integer> = "3*x^2+2*x-5".parse().unwrap();
        assert_eq!(p.coeffs.len(), 3);
        assert_eq!(p.coeffs[0], Integer::from(-5));
        assert_eq!(p.coeffs[1], Integer::from(2));
        assert_eq!(p.coeffs[2], Integer::from(3));
    }

    #[test]
    fn test_parse_natural() {
        let p: DensePoly<Natural> = "3*x^2+2*x+5".parse().unwrap();
        assert_eq!(p.coeffs.len(), 3);
        assert_eq!(p.coeffs[0], Natural::from(5u32));
        assert_eq!(p.coeffs[1], Natural::from(2u32));
        assert_eq!(p.coeffs[2], Natural::from(3u32));
    }

    #[test]
    fn test_parse_rational() {
        let p: DensePoly<Rational> = "1/2*x+3/4".parse().unwrap();
        assert_eq!(p.coeffs.len(), 2);
    }

    #[test]
    fn test_significant_bits() {
        let p: DensePoly<Natural> = "7*x+3".parse().unwrap();
        // 7 has 3 significant bits, 3 has 2 significant bits
        assert_eq!(p.significant_bits(), 5);
    }

    #[test]
    fn test_bare_x() {
        let p: DensePoly<Integer> = "x".parse().unwrap();
        assert_eq!(p.coeffs.len(), 2);
        assert_eq!(p.coeffs[0], Integer::from(0));
        assert_eq!(p.coeffs[1], Integer::from(1));
    }

    #[test]
    fn test_negative_x() {
        let p: DensePoly<Integer> = "-x^2+1".parse().unwrap();
        assert_eq!(p.coeffs.len(), 3);
        assert_eq!(p.coeffs[0], Integer::from(1));
        assert_eq!(p.coeffs[1], Integer::from(0));
        assert_eq!(p.coeffs[2], Integer::from(-1));
    }
}
