/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Equiv.Gcd
import Azurite.AzPolynomial.Equiv.DivModByMonic
import Azurite.AzPolynomial.FastMul
import Azurite.AzZMod.Field
import Azurite.AzMvPolynomial.ParsableCoeff.AzZMod
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# The monic gcd over a field by Euclid's algorithm

`gcdMonic` goes through the signed subresultant sequence, which is the right tool over a
ring but costly over a field.  `gcdMonicEuclid` is Euclid's algorithm with the divisor made
monic at every step (one inversion and one scalar multiplication) and the remainder taken by
`modByMonic` (which runs in place).  It has the same value as `gcdMonic` for all inputs
(`gcdMonic_eq_gcdMonicEuclid`: both are Mathlib's normalized gcd), and the compiler uses it
in place of `gcdMonic` (`@[csimp]`), so that the theory keeps talking about `gcdMonic`.
A file that calls `gcdMonic` imports this file.
-/

open Polynomial

namespace Azurite.AzPolynomial

attribute [local instance 0] Azurite.BPR.gcdMonoidPolynomial

variable {K : Type _} [Field K] [DecidableEq K]

/-- `p` divided by its leading coefficient: one inversion, then a scalar multiplication. -/
def monicizeFast (p : AzPolynomial K) : AzPolynomial K :=
  let c := p.leadingCoeff⁻¹
  c • p

/-- Euclid's algorithm on `(a, b)`; the fuel bounds the size of `b`. -/
def euclidMonic : ℕ → AzPolynomial K → AzPolynomial K → AzPolynomial K
  | 0, a, _ => monicizeFast a
  | fuel + 1, a, b =>
    if b = 0 then monicizeFast a
    else
      let b' := monicizeFast b
      euclidMonic fuel b' (modByMonic a b')

/-- **The monic gcd over a field, by Euclid's algorithm.**  What `gcdMonic` compiles to. -/
def gcdMonicEuclid (P Q : AzPolynomial K) : AzPolynomial K :=
  euclidMonic (Q.coeffs.size + 1) P Q

theorem monicizeFast_eq (p : AzPolynomial K) : monicizeFast p = monicize p := by
  unfold monicizeFast monicize
  rw [divByRingElt_eq_smul]

theorem toPoly_monicizeFast (p : AzPolynomial K) :
    AzPolynomial.toPoly (monicizeFast p) = _root_.normalize (AzPolynomial.toPoly p) := by
  by_cases hp : p = 0
  · subst hp
    unfold monicizeFast
    rw [toPoly_smul, toPoly_zero, smul_zero, normalize_zero]
  · rw [monicizeFast_eq, toPoly_monicize p hp]

theorem monicizeFast_size_le (p : AzPolynomial K) :
    (monicizeFast p).coeffs.size ≤ p.coeffs.size := by
  unfold monicizeFast
  show (smul _ p).coeffs.size ≤ _
  unfold smul
  have h : ∀ a : Array K, (normalize a).coeffs.size ≤ a.size := by
    intro a
    change (a.popWhile (· = 0)).size ≤ a.size
    rw [← Array.length_toList, ← Array.length_toList, toList_popWhile_eq_dropTrailingZeros]
    exact (dropTrailingZeros_prefix _).length_le
  exact le_trans (h _) (by rw [Array.size_map])

/-- `gcd x y = gcd y r` when `x = y q + r`. -/
theorem gcd_eq_gcd_of_eq_mul_add {x y q r : K[X]} (h : x = y * q + r) :
    GCDMonoid.gcd x y = GCDMonoid.gcd y r := by
  refine dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) ?_ ?_
  · refine dvd_gcd (gcd_dvd_right _ _) ?_
    have hr : r = x - y * q := by rw [h]; ring
    rw [hr]
    exact dvd_sub (gcd_dvd_left _ _) (dvd_mul_of_dvd_left (gcd_dvd_right _ _) _)
  · refine dvd_gcd ?_ (gcd_dvd_left _ _)
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left _ _) _) (gcd_dvd_right _ _)

theorem gcd_normalize_right' (x y : K[X]) :
    GCDMonoid.gcd x (_root_.normalize y) = GCDMonoid.gcd x y := by
  refine dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) ?_ ?_
  · exact dvd_gcd (gcd_dvd_left _ _) (dvd_trans (gcd_dvd_right _ _) (normalize_dvd_iff.mpr dvd_rfl))
  · exact dvd_gcd (gcd_dvd_left _ _) (dvd_normalize_iff.mpr (gcd_dvd_right _ _))

theorem toPoly_euclidMonic :
    ∀ (fuel : ℕ) (a b : AzPolynomial K), b.coeffs.size < fuel →
      AzPolynomial.toPoly (euclidMonic fuel a b) =
        GCDMonoid.gcd (AzPolynomial.toPoly a) (AzPolynomial.toPoly b) := by
  intro fuel
  induction fuel with
  | zero => intro a b h; omega
  | succ n ih =>
    intro a b hb
    rw [euclidMonic]
    split
    · next hb0 =>
      rw [hb0, toPoly_zero, gcd_zero_right, toPoly_monicizeFast]
    · next hb0 =>
      have hb' : AzPolynomial.toPoly b ≠ 0 := fun h =>
        hb0 (toPoly_inj.mp (h.trans toPoly_zero.symm))
      have hmon : (AzPolynomial.toPoly (monicizeFast b)).Monic := by
        rw [toPoly_monicizeFast]
        exact Polynomial.monic_normalize hb'
      have hne : AzPolynomial.toPoly (monicizeFast b) ≠ 0 := hmon.ne_zero
      have hpos : 0 < (monicizeFast b).coeffs.size := by
        rcases Nat.eq_zero_or_pos (monicizeFast b).coeffs.size with h0 | h
        · exfalso
          apply hne
          have : monicizeFast b = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero h0)
          rw [this, toPoly_zero]
        · exact h
      have hsz := modByMonic_coeffs_size_lt a (monicizeFast b) hpos
      have hle := monicizeFast_size_le b
      simp only []
      rw [ih _ _ (by omega), toPoly_modByMonic hmon hne, Polynomial.modByMonic_eq_mod _ hmon,
        ← gcd_eq_gcd_of_eq_mul_add (EuclideanDomain.div_add_mod _ _).symm,
        toPoly_monicizeFast, gcd_normalize_right']

/-- `gcdMonicEuclid` is Mathlib's normalized gcd. -/
theorem toPoly_gcdMonicEuclid (P Q : AzPolynomial K) :
    AzPolynomial.toPoly (gcdMonicEuclid P Q) =
      GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) :=
  toPoly_euclidMonic _ P Q (Nat.lt_succ_self _)

-- ── Tests (before the `@[csimp]` theorem, so that `gcdMonic` here is the subresultant one) ──

section Tests

set_option maxRecDepth 4096 in
private instance : Fact (Nat.Prime (AzNat.ofNat 1009).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; decide⟩

private def t1009 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 1009)) :=
  (parseAzPolynomial s).get!

private def euclidAgrees (a b : String) : Bool :=
  gcdMonicEuclid (t1009 a) (t1009 b) = gcdMonic (t1009 a) (t1009 b)

#guard euclidAgrees "x^4+3*x^3+2*x+7" "x^3+5*x+1"
#guard euclidAgrees "x^3+5*x+1" "x^4+3*x^3+2*x+7"
#guard euclidAgrees "3*x^5+x+1" "7*x^5+2*x^2+9"
#guard euclidAgrees "x^2+1" "0"
#guard euclidAgrees "0" "5*x^2+1"
#guard euclidAgrees "0" "0"
#guard euclidAgrees "7" "x^3+1"
#guard euclidAgrees "x^3+1" "7"
#guard gcdMonicEuclid (t1009 "x+1008" * t1009 "x+1007" * t1009 "x^2+1")
    (t1009 "5*x+999" * t1009 "x+5")
  = t1009 "x+1007"
#guard (List.range 8).all fun k =>
  let a := t1009 "x^3+2*x+1" * t1009 s!"x^5+{k + 4}*x^2+3" * t1009 s!"x^2+{k + 1}"
  let b := t1009 "x^3+2*x+1" * t1009 s!"x^6+{k + 2}*x+11"
  gcdMonicEuclid a b = gcdMonic a b && gcdMonicEuclid b a = gcdMonic b a

end Tests

@[csimp] theorem gcdMonic_eq_gcdMonicEuclid : @gcdMonic = @gcdMonicEuclid := by
  funext K _ _ P Q
  have : AzPolynomialMulConfig K := .basecase
  exact toPoly_inj.mp ((toPoly_gcdMonic P Q).trans (toPoly_gcdMonicEuclid P Q).symm)

end Azurite.AzPolynomial
