/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Examples demonstrating `AzMvPolynomial.toCharsWith` / `toStrWith` with
  a variety of variable display types, coefficient rings, and monomial
  orderings.  The math core is Fin-indexed; display is parameterized
  over a `ParsableVar F n` naming scheme.
-/
import Azurite.AzMvPolynomial.ToString
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.Monomial
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Azurite.AzInt.Instances
import Azurite.AzInt.ParsableElement
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Azurite.AzRat.Instances
import Azurite.AzRat.Equiv.RingEquiv
import Azurite.AzMvPolynomial.ParsableCoeff.AzRat
import Azurite.AzZMod.Instances
import Azurite.AzZMod.Equiv.RingEquiv
import Azurite.AzMvPolynomial.ParsableCoeff.AzZMod

open Azurite

/-! ### Setup: Fact instances for variable bounds -/

instance : Fact (3 ≤ 26) := ⟨by omega⟩
instance : Fact (2 ≤ 26) := ⟨by omega⟩
instance : Fact (3 ≤ 24) := ⟨by omega⟩
instance : Fact (1 < (AzNat.ofNat 5).toNat) := ⟨by rw [AzNat.toNat_ofNat]; omega⟩

/-! ### Helper abbreviations -/

/-- Shorthand to make a monomial from a nonzero coefficient and an exponent vector. -/
abbrev mkMono {n : ℕ} {R : Type _} [Semiring R] {ord : MonomialOrder}
    (c : R) (hc : c ≠ 0) (exps : Vector ℕ n) : Monomial n R ord :=
  ⟨⟨c, hc⟩, ⟨exps⟩⟩

/-! ## 1. AzInt[x, y, z] — Three monomial orderings

    Polynomial: 3x²y − 2xz + 5
    Display:    `XyzVar 3` → x (index 0), y (index 1), z (index 2)
-/

section IntXyz

private def p_degrevlex :=
  AzMvPolynomial.ofMonomials (n := 3) (R := AzInt) (ord := .Degrevlex) #[
    mkMono 3 (AzInt.ofNat_ne_zero 3) ⟨#[2, 1, 0], by simp⟩,   -- 3x²y
    mkMono (-2) (AzInt.neg_ofNat_ne_zero 2) ⟨#[1, 0, 1], by simp⟩, -- -2xz
    mkMono 5 (AzInt.ofNat_ne_zero 5) ⟨#[0, 0, 0], by simp⟩     -- 5
  ] (by decide)

-- degrevlex: x²y (deg 3) > xz (deg 2) > 1 (deg 0)
#guard p_degrevlex.toStrWith (XyzVar 3) == "3*x^2*y-2*x*z+5"

private def p_lex :=
  AzMvPolynomial.ofMonomials (n := 3) (R := AzInt) (ord := .Lex) #[
    mkMono 3 (AzInt.ofNat_ne_zero 3) ⟨#[2, 1, 0], by simp⟩,
    mkMono (-2) (AzInt.neg_ofNat_ne_zero 2) ⟨#[1, 0, 1], by simp⟩,
    mkMono 5 (AzInt.ofNat_ne_zero 5) ⟨#[0, 0, 0], by simp⟩
  ] (by decide)

-- lex: x²y > xz > 1 (same ordering as degrevlex here)
#guard p_lex.toStrWith (XyzVar 3) == "3*x^2*y-2*x*z+5"

private def p_deglex :=
  AzMvPolynomial.ofMonomials (n := 3) (R := AzInt) (ord := .Deglex) #[
    mkMono 3 (AzInt.ofNat_ne_zero 3) ⟨#[2, 1, 0], by simp⟩,
    mkMono (-2) (AzInt.neg_ofNat_ne_zero 2) ⟨#[1, 0, 1], by simp⟩,
    mkMono 5 (AzInt.ofNat_ne_zero 5) ⟨#[0, 0, 0], by simp⟩
  ] (by decide)

-- deglex: x²y (deg 3) > xz (deg 2) > 1 (deg 0)
#guard p_deglex.toStrWith (XyzVar 3) == "3*x^2*y-2*x*z+5"

/-! #### Where orderings differ: y³ vs x²z (both degree 3)
    - **degrevlex**: y³ > x²z (x²z has larger rightmost exponent → smaller)
    - **lex**:       x²z > y³ (first variable exponent 2 > 0)
    - **deglex**:    x²z > y³ (same degree, then lex: 2 > 0 at first position) -/

private def p_diff_degrevlex :=
  AzMvPolynomial.ofMonomials (n := 3) (R := AzInt) (ord := .Degrevlex) #[
    mkMono 1 (by decide) ⟨#[2, 0, 1], by simp⟩,  -- x²z
    mkMono 1 (by decide) ⟨#[0, 3, 0], by simp⟩   -- y³
  ] (by decide)

#guard p_diff_degrevlex.toStrWith (XyzVar 3) == "y^3+x^2*z"

private def p_diff_lex :=
  AzMvPolynomial.ofMonomials (n := 3) (R := AzInt) (ord := .Lex) #[
    mkMono 1 (by decide) ⟨#[2, 0, 1], by simp⟩,
    mkMono 1 (by decide) ⟨#[0, 3, 0], by simp⟩
  ] (by decide)

#guard p_diff_lex.toStrWith (XyzVar 3) == "x^2*z+y^3"

private def p_diff_deglex :=
  AzMvPolynomial.ofMonomials (n := 3) (R := AzInt) (ord := .Deglex) #[
    mkMono 1 (by decide) ⟨#[2, 0, 1], by simp⟩,
    mkMono 1 (by decide) ⟨#[0, 3, 0], by simp⟩
  ] (by decide)

#guard p_diff_deglex.toStrWith (XyzVar 3) == "x^2*z+y^3"

end IntXyz

/-! ## 2. AzRat[X₀, X₁, X₂] — Fractional coefficients with IndexedCapsVar -/

section RatIndexedCaps

private def q1 :=
  AzMvPolynomial.ofMonomials (n := 3) (R := AzRat) (ord := .Degrevlex) #[
    mkMono (1/2 : AzRat) (by
      intro h
      have h2 := congrArg AzRat.ringEquivRat h
      simp only [map_div₀, map_one, map_ofNat] at h2
      norm_num at h2) ⟨#[2, 0, 0], by simp⟩,   -- ½X₀²
    mkMono (-3/4 : AzRat) (by
      intro h
      have h2 := congrArg AzRat.ringEquivRat h
      simp only [map_div₀, map_neg, map_ofNat] at h2
      norm_num at h2) ⟨#[0, 1, 1], by simp⟩,   -- -¾X₁X₂
    mkMono (7 : AzRat) (by
      intro h
      have h2 := congrArg AzRat.ringEquivRat h
      simp only [map_ofNat] at h2
      norm_num at h2) ⟨#[0, 0, 0], by simp⟩       -- 7
  ] (by decide)

#guard q1.toStrWith (IndexedCapsVar 3) == "1/2*X₀^2-3/4*X₁*X₂+7"

end RatIndexedCaps

/-! ## 3. (AzInt/5AzInt)[α, β, γ] — Greek variables with modular coefficients -/

section ZMod5Greek

private def z1 :=
  AzMvPolynomial.ofMonomials (n := 3) (R := AzZMod (AzNat.ofNat 5)) (ord := .Degrevlex) #[
    mkMono (3 : AzZMod (AzNat.ofNat 5)) (by
      intro h
      have h2 := congrArg (AzZMod.ringEquivZMod (m := AzNat.ofNat 5)) h
      simp only [map_ofNat, map_zero] at h2
      rw [show ((AzNat.ofNat 5).toNat) = 5 from AzNat.toNat_ofNat 5] at h2
      exact absurd h2 (by decide)) ⟨#[1, 1, 0], by simp⟩,  -- 3αβ
    mkMono (2 : AzZMod (AzNat.ofNat 5)) (by
      intro h
      have h2 := congrArg (AzZMod.ringEquivZMod (m := AzNat.ofNat 5)) h
      simp only [map_ofNat, map_zero] at h2
      rw [show ((AzNat.ofNat 5).toNat) = 5 from AzNat.toNat_ofNat 5] at h2
      exact absurd h2 (by decide)) ⟨#[0, 2, 0], by simp⟩,  -- 2β²
    mkMono (1 : AzZMod (AzNat.ofNat 5)) (by
      intro h
      have h2 := congrArg (AzZMod.ringEquivZMod (m := AzNat.ofNat 5)) h
      simp only [map_one, map_zero] at h2
      rw [show ((AzNat.ofNat 5).toNat) = 5 from AzNat.toNat_ofNat 5] at h2
      exact absurd h2 (by decide)) ⟨#[0, 0, 0], by simp⟩   -- 1
  ] (by decide)

#guard z1.toStrWith (GreekVar 3) == "3*α*β+2*β^2+1"

end ZMod5Greek

/-! ## 4. AzInt[♠, ♥, ♦, ♣] — Dingbat variables using ListVar -/

section Dingbats

-- Use single-character strings as labels
def dingbats : List String := ["♠", "♥", "♦", "♣"]
instance : Fact dingbats.Nodup := ⟨by decide⟩
instance : Fact (ListVar.ListVarParsable dingbats) := ⟨by decide⟩

private def d1 :=
  AzMvPolynomial.ofMonomials (n := dingbats.length) (R := AzInt) (ord := .Degrevlex) #[
    mkMono (1 : AzInt) (by decide) ⟨#[2, 0, 0, 0], by decide⟩,   -- ♠²
    mkMono (-3 : AzInt) (AzInt.neg_ofNat_ne_zero 3) ⟨#[0, 1, 0, 0], by decide⟩,  -- -3♥
    mkMono (1 : AzInt) (by decide) ⟨#[0, 0, 1, 1], by decide⟩,   -- ♦♣
    mkMono (42 : AzInt) (AzInt.ofNat_ne_zero 42) ⟨#[0, 0, 0, 0], by decide⟩   -- 42
  ] (by decide)

-- degrevlex ordering: ♠² (deg 2, rightmost=0) > ♦♣ (deg 2, rightmost=1) > ♥ (deg 1) > 1
#guard d1.toStrWith (ListVar dingbats) == "♠^2+♦*♣-3*♥+42"

end Dingbats

/-! ## Zero polynomial -/

#guard (0 : AzMvPolynomial 3 AzInt .Degrevlex).toStrWith (XyzVar 3) == "0"

private def p_neg_1 :=
  AzMvPolynomial.ofMonomials (n := 2) (R := AzInt) (ord := .Degrevlex) #[
    mkMono (1 : AzInt) (by decide) ⟨#[1, 0], by decide⟩,   -- x
    mkMono (-1 : AzInt) (by decide) ⟨#[0, 1], by decide⟩, -- -y
  ] (by decide)

#guard p_neg_1.toStrWith (XyzVar 2) == "x-y"

/-! ## Parse examples -/

section ParseExamples

-- Round-trip: parseWith ∘ toStrWith = some
#guard (AzMvPolynomial.parseWith (XyzVar 3) (n := 3) (R := AzInt) (ord := .Degrevlex)
    "3*x^2*y-2*x*z+5".toList).map (·.toStrWith (XyzVar 3)) ==
      some "3*x^2*y-2*x*z+5"

-- Out-of-order input: accepted and re-sorted
#guard (AzMvPolynomial.parseWith (XyzVar 3) (n := 3) (R := AzInt) (ord := .Degrevlex)
    "5+3*x^2*y-2*x*z".toList).map (·.toStrWith (XyzVar 3)) ==
      some "3*x^2*y-2*x*z+5"

-- Duplicate monic monomials: rejected
#guard (AzMvPolynomial.parseWith (XyzVar 3) (n := 3) (R := AzInt) (ord := .Degrevlex)
    "x*y+y*x".toList).isNone

-- Zero polynomial
#guard (AzMvPolynomial.parseWith (XyzVar 3) (n := 3) (R := AzInt) (ord := .Degrevlex)
    "0".toList).map (·.toStrWith (XyzVar 3)) == some "0"

-- Parse with AzRat
#guard (AzMvPolynomial.parseWith (IndexedCapsVar 3) (n := 3) (R := AzRat) (ord := .Degrevlex)
    "1/2*X₀^2-3/4*X₁*X₂+7".toList).map (·.toStrWith (IndexedCapsVar 3)) ==
      some "1/2*X₀^2-3/4*X₁*X₂+7"

end ParseExamples
