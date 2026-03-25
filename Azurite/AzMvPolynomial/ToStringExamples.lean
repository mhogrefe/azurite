/-
  Examples demonstrating `AzMvPolynomial.toChars` / `toString` with
  a variety of variable types, coefficient rings, and monomial orderings.
-/
import Azurite.AzMvPolynomial.ToString
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.Monomial
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

open Azurite

/-! ### Setup: Fact instances for variable bounds -/

instance : Fact (3 ≤ 26) := ⟨by omega⟩
instance : Fact (2 ≤ 26) := ⟨by omega⟩
instance : Fact (3 ≤ 24) := ⟨by omega⟩
instance : Fact (1 < 5) := ⟨by omega⟩

/-! ### Helper abbreviations -/

/-- Shorthand to make a monomial from a nonzero coefficient and an exponent vector. -/
abbrev mkMono {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {R : Type _} [Semiring R] {ord : MonomialOrder}
    (c : R) (hc : c ≠ 0) (exps : Vector ℕ n) : Monomial σ R ord :=
  ⟨⟨c, hc⟩, ⟨exps⟩⟩

/-! ## 1. ℤ[x, y, z] — Three monomial orderings

    Polynomial: 3x²y − 2xz + 5
    Variables: `XyzVar 3` → x (index 0), y (index 1), z (index 2)
-/

section IntXyz

private def p_degrevlex :=
  AzMvPolynomial.ofMonomials (σ := XyzVar 3) (R := ℤ) (ord := .Degrevlex) #[
    mkMono 3 (by decide) ⟨#[2, 1, 0], by simp⟩,   -- 3x²y
    mkMono (-2) (by decide) ⟨#[1, 0, 1], by simp⟩, -- -2xz
    mkMono 5 (by decide) ⟨#[0, 0, 0], by simp⟩     -- 5
  ] (by native_decide)

-- degrevlex: x²y (deg 3) > xz (deg 2) > 1 (deg 0)
#guard toString p_degrevlex == "3*x^2*y-2*x*z+5"

private def p_lex :=
  AzMvPolynomial.ofMonomials (σ := XyzVar 3) (R := ℤ) (ord := .Lex) #[
    mkMono 3 (by decide) ⟨#[2, 1, 0], by simp⟩,
    mkMono (-2) (by decide) ⟨#[1, 0, 1], by simp⟩,
    mkMono 5 (by decide) ⟨#[0, 0, 0], by simp⟩
  ] (by native_decide)

-- lex: x²y > xz > 1 (same ordering as degrevlex here)
#guard toString p_lex == "3*x^2*y-2*x*z+5"

private def p_deglex :=
  AzMvPolynomial.ofMonomials (σ := XyzVar 3) (R := ℤ) (ord := .Deglex) #[
    mkMono 3 (by decide) ⟨#[2, 1, 0], by simp⟩,
    mkMono (-2) (by decide) ⟨#[1, 0, 1], by simp⟩,
    mkMono 5 (by decide) ⟨#[0, 0, 0], by simp⟩
  ] (by native_decide)

-- deglex: x²y (deg 3) > xz (deg 2) > 1 (deg 0)
#guard toString p_deglex == "3*x^2*y-2*x*z+5"

/-! #### Where orderings differ: y³ vs x²z (both degree 3)
    - **degrevlex**: y³ > x²z (x²z has larger rightmost exponent → smaller)
    - **lex**:       x²z > y³ (first variable exponent 2 > 0)
    - **deglex**:    x²z > y³ (same degree, then lex: 2 > 0 at first position) -/

private def p_diff_degrevlex :=
  AzMvPolynomial.ofMonomials (σ := XyzVar 3) (R := ℤ) (ord := .Degrevlex) #[
    mkMono 1 (by decide) ⟨#[2, 0, 1], by simp⟩,  -- x²z
    mkMono 1 (by decide) ⟨#[0, 3, 0], by simp⟩   -- y³
  ] (by native_decide)

#guard toString p_diff_degrevlex == "y^3+x^2*z"

private def p_diff_lex :=
  AzMvPolynomial.ofMonomials (σ := XyzVar 3) (R := ℤ) (ord := .Lex) #[
    mkMono 1 (by decide) ⟨#[2, 0, 1], by simp⟩,
    mkMono 1 (by decide) ⟨#[0, 3, 0], by simp⟩
  ] (by native_decide)

#guard toString p_diff_lex == "x^2*z+y^3"

private def p_diff_deglex :=
  AzMvPolynomial.ofMonomials (σ := XyzVar 3) (R := ℤ) (ord := .Deglex) #[
    mkMono 1 (by decide) ⟨#[2, 0, 1], by simp⟩,
    mkMono 1 (by decide) ⟨#[0, 3, 0], by simp⟩
  ] (by native_decide)

#guard toString p_diff_deglex == "x^2*z+y^3"

end IntXyz

/-! ## 2. ℚ[X₀, X₁, X₂] — Fractional coefficients with IndexedCapsVar -/

section RatIndexedCaps

private def q1 :=
  AzMvPolynomial.ofMonomials (σ := IndexedCapsVar 3) (R := ℚ) (ord := .Degrevlex) #[
    mkMono (1/2 : ℚ) (by norm_num) ⟨#[2, 0, 0], by simp⟩,   -- ½X₀²
    mkMono (-3/4 : ℚ) (by norm_num) ⟨#[0, 1, 1], by simp⟩,   -- -¾X₁X₂
    mkMono (7 : ℚ) (by norm_num) ⟨#[0, 0, 0], by simp⟩       -- 7
  ] (by native_decide)

#guard toString q1 == "1/2*X₀^2-3/4*X₁*X₂+7"

end RatIndexedCaps

/-! ## 3. (ℤ/5ℤ)[α, β, γ] — Greek variables with modular coefficients -/

section ZMod5Greek

private def z1 :=
  AzMvPolynomial.ofMonomials (σ := GreekVar 3) (R := ZMod 5) (ord := .Degrevlex) #[
    mkMono (3 : ZMod 5) (by decide) ⟨#[1, 1, 0], by simp⟩,  -- 3αβ
    mkMono (2 : ZMod 5) (by decide) ⟨#[0, 2, 0], by simp⟩,  -- 2β²
    mkMono (1 : ZMod 5) (by decide) ⟨#[0, 0, 0], by simp⟩   -- 1
  ] (by native_decide)

#guard toString z1 == "3*α*β+2*β^2+1"

end ZMod5Greek

/-! ## 4. ℤ[♠, ♥, ♦, ♣] — Dingbat variables using ListVar -/

section Dingbats

-- Use single-character strings as labels
def dingbats : List String := ["♠", "♥", "♦", "♣"]
instance : Fact dingbats.Nodup := ⟨by native_decide⟩
instance : Fact (ListVar.ListVarParsable dingbats) := ⟨by native_decide⟩

private def d1 :=
  AzMvPolynomial.ofMonomials (σ := ListVar dingbats) (R := ℤ) (ord := .Degrevlex) #[
    mkMono (1 : ℤ) (by decide) ⟨#[2, 0, 0, 0], by decide⟩,   -- ♠²
    mkMono (-3 : ℤ) (by decide) ⟨#[0, 1, 0, 0], by decide⟩,  -- -3♥
    mkMono (1 : ℤ) (by decide) ⟨#[0, 0, 1, 1], by decide⟩,   -- ♦♣
    mkMono (42 : ℤ) (by decide) ⟨#[0, 0, 0, 0], by decide⟩   -- 42
  ] (by native_decide)

-- degrevlex ordering: ♠² (deg 2, rightmost=0) > ♦♣ (deg 2, rightmost=1) > ♥ (deg 1) > 1
#guard toString d1 == "♠^2+♦*♣-3*♥+42"

end Dingbats

/-! ## Zero polynomial -/

#guard toString (0 : AzMvPolynomial (XyzVar 3) ℤ .Degrevlex) == "0"

private def p_neg_1 :=
  AzMvPolynomial.ofMonomials (σ := XyzVar 2) (R := ℤ) (ord := .Degrevlex) #[
    mkMono (1 : ℤ) (by decide) ⟨#[1, 0], by decide⟩,   -- x
    mkMono (-1 : ℤ) (by decide) ⟨#[0, 1], by decide⟩, -- -y
  ] (by native_decide)

#guard toString p_neg_1 == "x-y"

/-! ## Parse examples -/

section ParseExamples

-- Round-trip: parse ∘ toString = some
#guard (AzMvPolynomial.parse (σ := XyzVar 3) (R := ℤ) (ord := .Degrevlex)
    "3*x^2*y-2*x*z+5".toList).map toString == some "3*x^2*y-2*x*z+5"

-- Out-of-order input: accepted and re-sorted
#guard (AzMvPolynomial.parse (σ := XyzVar 3) (R := ℤ) (ord := .Degrevlex)
    "5+3*x^2*y-2*x*z".toList).map toString == some "3*x^2*y-2*x*z+5"

-- Duplicate monic monomials: rejected
#guard (AzMvPolynomial.parse (σ := XyzVar 3) (R := ℤ) (ord := .Degrevlex)
    "x*y+y*x".toList).isNone

-- Zero polynomial
#guard (AzMvPolynomial.parse (σ := XyzVar 3) (R := ℤ) (ord := .Degrevlex)
    "0".toList).map toString == some "0"

-- Parse with ℚ
#guard (AzMvPolynomial.parse (σ := IndexedCapsVar 3) (R := ℚ) (ord := .Degrevlex)
    "1/2*X₀^2-3/4*X₁*X₂+7".toList).map toString == some "1/2*X₀^2-3/4*X₁*X₂+7"

end ParseExamples
