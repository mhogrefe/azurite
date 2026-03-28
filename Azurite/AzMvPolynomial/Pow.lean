import Azurite.AzMvPolynomial.Mul
import Azurite.Algorithm.FastPow
import Azurite.AzMvPolynomial.Equiv.Basic

/-!
# Exponentiation for MonicMonomial, Monomial, and AzMvPolynomial

Computable exponentiation for monic monomials, monomials, and multivariate polynomials.

- **MonicMonomial**: Scale each exponent by `k`. O(n) where n = number of variables.
- **Monomial**: Raise coefficient to `k`-th power, scale monic exponents by `k`.
- **AzMvPolynomial**: Single-monomial fast path (direct monomial pow) or
  `fastPow` for multi-term polynomials.

## Main Definitions and Theorems

### MonicMonomial
- `MonicMonomial.pow m k`: scales each exponent of `m` by `k`.
- `pow_eq_npow`: `m.pow k = m ^ k` (agrees with the `CommMonoid`'s `^`).
- `toFinsupp_pow`: `toFinsupp (m.pow k) = k • toFinsupp m` (Mathlib equivalence).

### Monomial
- `Monomial.pow m k`: raises coefficient to `k`-th power, scales exponents by `k`.
- `pow_eq_npow`: `m.pow k = m ^ k` (agrees with the `CommMonoid`'s `^`).
- `toMvPoly_pow`: `(m.pow k).toMvPoly = m.toMvPoly ^ k` (Mathlib equivalence).

### AzMvPolynomial
- `AzMvPolynomial.pow p k`: computable exponentiation with single-monomial fast path.
-/

-- ═══════════════════════════════════════════════════════════════════
-- MonicMonomial
-- ═══════════════════════════════════════════════════════════════════

namespace Azurite.MonicMonomial

variable {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- Computable exponentiation for monic monomials: scale each exponent by `k`.
    This is O(n) where n is the number of variables. -/
def pow (m : MonicMonomial σ ord) (k : ℕ) : MonicMonomial σ ord :=
  ⟨Vector.ofFn (fun i => k * m.exponents[i])⟩

@[simp] theorem pow_exponents (m : MonicMonomial σ ord) (k : ℕ) :
    (m.pow k).exponents = Vector.ofFn (fun i => k * m.exponents[i]) := rfl

/-- `pow` agrees with the `CommMonoid`'s `^` operator. -/
theorem pow_eq_npow (m : MonicMonomial σ ord) (k : ℕ) : m.pow k = m ^ k := by
  induction k with
  | zero =>
    ext1; simp [pow_zero, one_exponents]
    ext i hi; simp [Vector.getElem_ofFn, Vector.getElem_replicate]
  | succ k ih =>
    rw [pow_succ, ← ih]
    ext1; ext i hi
    simp [pow_exponents, mul_exponents, Vector.getElem_ofFn]
    ring

/-- `toFinsupp` preserves `pow`: `toFinsupp (m.pow k) = k • toFinsupp m`. -/
theorem toFinsupp_pow [DecidableEq σ] (m : MonicMonomial σ ord) (k : ℕ) :
    (m.pow k).toFinsupp = k • m.toFinsupp := by
  rw [pow_eq_npow]
  induction k with
  | zero =>
    simp only [pow_zero, zero_smul]
    show toFinsupp (1 : MonicMonomial σ ord) = 0
    ext v; simp [toFinsupp, Finsupp.onFinset_apply, Vector.getElem_replicate]
  | succ k ih => rw [pow_succ, toFinsupp_mul, ih, succ_nsmul]

section Tests

instance : Fact (3 ≤ 26) := ⟨by omega⟩
private def mm (v : Vector ℕ 3) : MonicMonomial (AbcVar 3) := ⟨v⟩

-- (a^2 * b)^3 = a^6 * b^3
#guard (mm ⟨#[2, 1, 0], rfl⟩).pow 3 == mm ⟨#[6, 3, 0], rfl⟩
-- 1^100 = 1
#guard (mm ⟨#[0, 0, 0], rfl⟩).pow 100 == mm ⟨#[0, 0, 0], rfl⟩
-- m^0 = 1
#guard (mm ⟨#[5, 3, 1], rfl⟩).pow 0 == mm ⟨#[0, 0, 0], rfl⟩
-- m^1 = m
#guard (mm ⟨#[5, 3, 1], rfl⟩).pow 1 == mm ⟨#[5, 3, 1], rfl⟩
-- (a * b * c)^4 = a^4 * b^4 * c^4
#guard (mm ⟨#[1, 1, 1], rfl⟩).pow 4 == mm ⟨#[4, 4, 4], rfl⟩

end Tests

end Azurite.MonicMonomial

-- ═══════════════════════════════════════════════════════════════════
-- Monomial
-- ═══════════════════════════════════════════════════════════════════

namespace Azurite.Monomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- Computable exponentiation for monomials: raise coefficient to `k`-th power,
    scale monic exponents by `k`. -/
def pow (m : Monomial σ R ord) (k : ℕ) : Monomial σ R ord :=
  ⟨⟨m.coeff.val ^ k, pow_ne_zero k m.coeff.property⟩, m.monic.pow k⟩

@[simp] theorem pow_coeff_val (m : Monomial σ R ord) (k : ℕ) :
    (m.pow k).coeff.val = m.coeff.val ^ k := rfl

@[simp] theorem pow_monic (m : Monomial σ R ord) (k : ℕ) :
    (m.pow k).monic = m.monic.pow k := rfl

/-- `pow` agrees with the `CommMonoid`'s `^` operator. -/
theorem pow_eq_npow [Nontrivial R] (m : Monomial σ R ord) (k : ℕ) :
    m.pow k = m ^ k := by
  induction k with
  | zero =>
    apply ext'
    · simp [pow, _root_.pow_zero]
    · simp [pow, MonicMonomial.pow, _root_.pow_zero, one_monic]
      ext i hi; simp [Vector.getElem_ofFn, Vector.getElem_replicate]
  | succ k ih =>
    rw [_root_.pow_succ, ← ih]
    apply ext'
    · simp [pow, mul_coeff_val, _root_.pow_succ]
    · simp [pow, mul_monic, MonicMonomial.pow]
      ext i hi; simp [Vector.getElem_ofFn, MonicMonomial.mul_exponents]; ring

/-- `toMvPoly` preserves `pow`:
    `(m.pow k).toMvPoly = m.toMvPoly ^ k`. -/
theorem toMvPoly_pow [DecidableEq σ] (m : Monomial σ R ord) (k : ℕ) :
    (m.pow k).toMvPoly = m.toMvPoly ^ k := by
  simp only [Monomial.toMvPoly, pow, MonicMonomial.toFinsupp_pow, MvPolynomial.monomial_pow]

section Tests

instance : Fact (3 ≤ 26) := ⟨by omega⟩

-- Use DecidableEq-based BEq for testing
private def eqMon (a b : Monomial (AbcVar 3) ℤ) : Bool :=
  a.coeff.val == b.coeff.val && a.monic == b.monic

private def mkMon (c : ℤ) (hc : c ≠ 0) (v : Vector ℕ 3) : Monomial (AbcVar 3) ℤ :=
  ⟨⟨c, hc⟩, ⟨v⟩⟩

-- (3*a^2*b)^2 = 9*a^4*b^2
#guard eqMon ((mkMon 3 (by omega) ⟨#[2, 1, 0], rfl⟩).pow 2)
             (mkMon 9 (by omega) ⟨#[4, 2, 0], rfl⟩)
-- (-2*a*b*c)^3 = -8*a^3*b^3*c^3
#guard eqMon ((mkMon (-2) (by omega) ⟨#[1, 1, 1], rfl⟩).pow 3)
             (mkMon (-8) (by omega) ⟨#[3, 3, 3], rfl⟩)
-- m^0 = 1
#guard eqMon ((mkMon 5 (by omega) ⟨#[3, 2, 1], rfl⟩).pow 0)
             (mkMon 1 (by omega) ⟨#[0, 0, 0], rfl⟩)
-- m^1 = m
#guard eqMon ((mkMon 7 (by omega) ⟨#[1, 0, 2], rfl⟩).pow 1)
             (mkMon 7 (by omega) ⟨#[1, 0, 2], rfl⟩)

end Tests

end Azurite.Monomial

-- ═══════════════════════════════════════════════════════════════════
-- AzMvPolynomial
-- ═══════════════════════════════════════════════════════════════════

namespace Azurite.AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- Computable exponentiation for multivariate polynomials.
    - **Single-term** (monomial) polynomials: exponentiates the monomial directly
      (raise coefficient to `k`-th power, scale exponents by `k`). O(n) where `n`
      is the number of variables.
    - **Multi-term** polynomials: uses binary exponentiation via `fastPow`, which
      performs O(log k) polynomial multiplications. -/
def pow (p : AzMvPolynomial σ R ord) (k : ℕ) : AzMvPolynomial σ R ord :=
  if h : p.terms.size = 1 then
    AzMvPolynomial.ofMonomial ((p.terms[0]'(by omega)).pow k)
  else
    Azurite.fastPow p k

end Azurite.AzMvPolynomial
