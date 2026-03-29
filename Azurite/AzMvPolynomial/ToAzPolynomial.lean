import Azurite.AzMvPolynomial.MonicMonomialOrder
import Azurite.AzMvPolynomial.Basic
import Azurite.AzPolynomial.Basic
import Azurite.AzMvPolynomial.Vars
import Mathlib.Logic.Unique

/-!
# Conversion from AzMvPolynomial to AzPolynomial

Given an `AzMvPolynomial σ R ord` where `σ` has a single element (`[Unique σ]`),
we convert to a univariate `AzPolynomial R`.

Each term `c * x^k` in the multivariate polynomial becomes coefficient `c` at
position `k` in the coefficient array.

This corresponds to one direction of Mathlib's `MvPolynomial.pUnitAlgEquiv`.
-/

namespace Azurite
open AzMvPolynomial MonomialOrder

variable {R : Type _} [Semiring R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-! ### Var.n_eq_one -/

omit [Semiring R] [DecidableEq R] in
/-- When the variable type has exactly one element, `n = 1`. -/
theorem Var.n_eq_one [Unique σ] : n = 1 := by
  have h := Var.equiv (α := σ) (n := n)
  have : Fintype.card σ = Fintype.card (Fin n) := Fintype.card_of_bijective h.bijective
  simp [Fintype.card_unique] at this
  exact this.symm

/-! ### MonicMonomial.degree -/

omit [Semiring R] [DecidableEq R] in
/-- The degree of a monic monomial when the variable type has a single element.
    This is just the exponent of the unique variable. -/
def MonicMonomial.degree [Unique σ] (m : MonicMonomial σ ord) : ℕ :=
  m.exponent default

/-! ### Coefficient array construction -/

/-- Build a dense coefficient array from the terms of an `AzMvPolynomial`.
    Iterates through the terms (which are sorted descending by degree)
    and places each coefficient at its degree position. -/
def buildCoeffsFromTerms [Unique σ] (terms : Array (Monomial σ R ord))
    (size : ℕ) : Array R :=
  terms.foldl (fun (acc : Array R) m =>
    let deg := m.monic.degree
    if h : deg < acc.size then acc.set deg m.coeff.val
    else acc) (Array.replicate size (0 : R))

/-! ### Main conversion -/

/-- Convert an `AzMvPolynomial σ R ord` with `[Unique σ]` to an `AzPolynomial R`.
    Uses the leading term's degree to determine the array size, then fills in
    each coefficient from the sparse term representation.

    Complexity: O(d + k) where d is the degree and k is the number of nonzero terms. -/
def AzMvPolynomial.toAzPolynomial [Unique σ]
    (p : AzMvPolynomial σ R ord) : AzPolynomial R :=
  if h : p.terms.size = 0 then AzPolynomial.zero
  else
    let leadTerm := p.terms[0]'(by omega)
    let maxDeg := leadTerm.monic.degree
    let coeffs := buildCoeffsFromTerms p.terms (maxDeg + 1)
    AzPolynomial.normalize coeffs

/-! ### Unique instance for IndexedVar 1 -/

instance : Unique (IndexedVar 1) where
  default := ⟨0⟩
  uniq := fun ⟨v⟩ => by congr 1; exact Fin.eq_zero v

/-! ### Tests -/

section Test

-- Zero polynomial
#guard (0 : AzMvPolynomial (IndexedVar 1) Int .Degrevlex).toAzPolynomial = AzPolynomial.zero

-- Constant polynomial 3
#guard (AzMvPolynomial.C (σ := IndexedVar 1) (ord := .Degrevlex) (3 : Int)).toAzPolynomial =
  ⟨#[3], by simp⟩

-- Variable x = [0, 1]
#guard (AzMvPolynomial.ofMonomial
  (⟨⟨(1 : Int), by omega⟩, MonicMonomial.ofVar (⟨0⟩ : IndexedVar 1)⟩ :
    Monomial (IndexedVar 1) Int .Degrevlex)).toAzPolynomial =
  ⟨#[0, 1], by simp⟩

end Test

/-! ### Variant 2: Arbitrary σ with vars witness -/

variable {R : Type _} [Semiring R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- Build a dense coefficient array from terms, using the exponent of a
    designated variable `v` as the array index. -/
def buildCoeffsFromTermsAt (v : σ) (terms : Array (Monomial σ R ord))
    (size : ℕ) : Array R :=
  terms.foldl (fun (acc : Array R) m =>
    let deg := m.monic.exponent v
    if h : deg < acc.size then acc.set deg m.coeff.val
    else acc) (Array.replicate size (0 : R))

/-- Convert an `AzMvPolynomial σ R ord` to an `AzPolynomial R`, given a proof
    that the polynomial uses at most one variable `v`.

    Each term's `v`-exponent determines its position in the coefficient array.
    The `vars` hypothesis ensures no information is lost.

    This generalizes `toAzPolynomial` (which requires `[Unique σ]`) to
    arbitrary variable types.  Complexity: O(d + k) where d is the
    max `v`-exponent and k is the number of nonzero terms. -/
def AzMvPolynomial.toAzPolynomialAt
    (p : AzMvPolynomial σ R ord) {v : σ} (_hv : p.vars ⊆ {v}) : AzPolynomial R :=
  if h : p.terms.size = 0 then AzPolynomial.zero
  else
    let leadTerm := p.terms[0]'(by omega)
    let maxDeg := leadTerm.monic.exponent v
    let coeffs := buildCoeffsFromTermsAt v p.terms (maxDeg + 1)
    AzPolynomial.normalize coeffs

/-! ### Tests for toAzPolynomialAt -/

section TestAt

open Azurite.MonicMonomial in
private abbrev mkMono' {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {R : Type _} [Semiring R] {ord : MonomialOrder}
    (c : R) (hc : c ≠ 0) (exps : Vector ℕ n) : Monomial σ R ord :=
  ⟨⟨c, hc⟩, ⟨exps⟩⟩

-- Zero polynomial (IndexedVar 1)
#guard ((0 : AzMvPolynomial (IndexedVar 1) Int .Degrevlex).toAzPolynomialAt
  (v := ⟨0⟩) (by simp [AzMvPolynomial.vars]) = AzPolynomial.zero)

-- Constant 3 (IndexedVar 1)
#guard ((AzMvPolynomial.C (σ := IndexedVar 1) (ord := .Degrevlex) (3 : Int)).toAzPolynomialAt
  (v := ⟨0⟩) (by
    simp [AzMvPolynomial.vars, AzMvPolynomial.C, Monomial.vars, MonicMonomial.vars]
    decide) = ⟨#[3], by simp⟩)

-- 3x² - 5x + 7 in ℤ[x,y,z] (only involves x) → [7, -5, 3]
instance : Fact (3 ≤ 26) := ⟨by omega⟩

private def p_xyz_x : AzMvPolynomial (XyzVar 3) ℤ .Degrevlex :=
  AzMvPolynomial.ofMonomials #[
    mkMono' 3 (by decide) ⟨#[2, 0, 0], by simp⟩,
    mkMono' (-5) (by decide) ⟨#[1, 0, 0], by simp⟩,
    mkMono' 7 (by decide) ⟨#[0, 0, 0], by simp⟩
  ] (by native_decide)

#guard (p_xyz_x.toAzPolynomialAt
  (v := ⟨'x', by decide⟩)
  (by native_decide) = ⟨#[7, -5, 3], by simp⟩)

-- y⁴ + 2y in ℤ[x,y,z] (only involves y) → [0, 2, 0, 0, 1]
private def p_xyz_y : AzMvPolynomial (XyzVar 3) ℤ .Degrevlex :=
  AzMvPolynomial.ofMonomials #[
    mkMono' 1 (by decide) ⟨#[0, 4, 0], by simp⟩,
    mkMono' 2 (by decide) ⟨#[0, 1, 0], by simp⟩
  ] (by native_decide)

#guard (p_xyz_y.toAzPolynomialAt
  (v := ⟨'y', by decide⟩)
  (by native_decide) = ⟨#[0, 2, 0, 0, 1], by simp⟩)

-- -z³ + 4z² - z + 6 in ℤ[x,y,z] (only involves z) → [6, -1, 4, -1]
private def p_xyz_z : AzMvPolynomial (XyzVar 3) ℤ .Degrevlex :=
  AzMvPolynomial.ofMonomials #[
    mkMono' (-1) (by decide) ⟨#[0, 0, 3], by simp⟩,
    mkMono' 4 (by decide) ⟨#[0, 0, 2], by simp⟩,
    mkMono' (-1) (by decide) ⟨#[0, 0, 1], by simp⟩,
    mkMono' 6 (by decide) ⟨#[0, 0, 0], by simp⟩
  ] (by native_decide)

#guard (p_xyz_z.toAzPolynomialAt
  (v := ⟨'z', by decide⟩)
  (by native_decide) = ⟨#[6, -1, 4, -1], by simp⟩)

-- X₂⁵ - X₂ in ℤ[X₀, X₁, X₂] with Lex ordering (only involves X₂) → [0, -1, 0, 0, 0, 1]
private def p_idx_x2 : AzMvPolynomial (IndexedVar 3) ℤ .Lex :=
  AzMvPolynomial.ofMonomials #[
    mkMono' 1 (by decide) ⟨#[0, 0, 5], by simp⟩,
    mkMono' (-1) (by decide) ⟨#[0, 0, 1], by simp⟩
  ] (by native_decide)

#guard (p_idx_x2.toAzPolynomialAt
  (v := ⟨2⟩)
  (by native_decide) = ⟨#[0, -1, 0, 0, 0, 1], by simp⟩)

end TestAt

end Azurite
