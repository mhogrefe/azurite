/-
Copyright (c) 2025 Azurite contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Azurite contributors
-/
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Order.Ring.Defs

/-!
# The 0₊ Order on F[ε]

**BPR Notation 2.5.** Let F be an ordered field and ε a variable. There is an
order on F(ε), denoted 0₊, defined as follows.

For a polynomial P(ε) = aₚεᵖ + ⋯ + aₘεᵐ with aₘ ≠ 0, we have
P(ε) > 0 in 0₊ if and only if aₘ > 0 (the lowest nonzero coefficient is
positive).

For a rational function P(ε)/Q(ε) ∈ F(ε), P(ε)/Q(ε) > 0 if and only if
P(ε)·Q(ε) > 0.

## Implementation

We build the order in two stages:
1. **Polynomials**: Define positivity on `F[X]` via the trailing coefficient,
   prove it forms a positive cone, and construct a `LinearOrder` instance.
2. **Rational functions**: Extend the order to `RatFunc F` via the standard
   fraction field construction.

## Main definitions

* `Azurite.BPR.ZeroPlus.polyPos` — positivity predicate on `F[X]`
-/

namespace Azurite.BPR.ZeroPlus

open Polynomial

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-! ### The 0₊ positivity predicate on F[X] -/

/-- A nonzero polynomial is *positive in the 0₊ order* when its trailing
    coefficient (the coefficient of the lowest-degree nonzero term) is
    positive. -/
def polyPos (P : F[X]) : Prop := P ≠ 0 ∧ 0 < P.trailingCoeff

/-! #### Infrastructure lemma -/

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- If `P.coeff m ≠ 0` and all coefficients below `m` vanish, then
    `P.natTrailingDegree = m`. -/
lemma natTrailingDegree_eq_of {P : F[X]} {m : ℕ}
    (hcoeff : P.coeff m ≠ 0)
    (hbelow : ∀ i, i < m → P.coeff i = 0) :
    P.natTrailingDegree = m := by
  apply le_antisymm
  · exact natTrailingDegree_le_of_ne_zero hcoeff
  · by_contra h; push_neg at h
    exact (trailingCoeff_nonzero_iff_nonzero.mpr
      (fun hP => hcoeff (by simp [hP]))) (hbelow _ h)

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The trailing coefficient of `-P` is `-P.trailingCoeff`. -/
lemma neg_trailingCoeff (P : F[X]) : (-P).trailingCoeff = -P.trailingCoeff := by
  simp [Polynomial.trailingCoeff, natTrailingDegree_neg, coeff_neg]

/-! #### Positive cone properties -/

/-- **Trichotomy**: Every polynomial is positive, zero, or negative. -/
lemma polyPos_trichotomy (P : F[X]) : polyPos P ∨ P = 0 ∨ polyPos (-P) := by
  by_cases hP : P = 0
  · exact Or.inr (Or.inl hP)
  · rcases lt_trichotomy P.trailingCoeff 0 with h | h | h
    · right; right
      exact ⟨neg_ne_zero.mpr hP, by rw [neg_trailingCoeff]; linarith⟩
    · exact absurd (trailingCoeff_eq_zero.mp h) hP
    · exact Or.inl ⟨hP, h⟩

/-- If P and Q are positive in 0₊, then P + Q is positive in 0₊. -/
lemma polyPos_add {P Q : F[X]} (hP : polyPos P) (hQ : polyPos Q) :
    polyPos (P + Q) := by
  obtain ⟨hP_ne, hP_pos⟩ := hP
  obtain ⟨hQ_ne, hQ_pos⟩ := hQ
  set m := P.natTrailingDegree
  set n := Q.natTrailingDegree
  rcases le_total m n with hmn | hmn
  · -- m ≤ n: trailing degree of sum is m
    have hcoeff_m : 0 < (P + Q).coeff m := by
      rw [coeff_add]
      rcases eq_or_lt_of_le hmn with hmn_eq | hmn_lt
      · exact add_pos hP_pos (hmn_eq ▸ hQ_pos)
      · rwa [coeff_eq_zero_of_lt_natTrailingDegree hmn_lt, add_zero]
    have hbelow : ∀ i, i < m → (P + Q).coeff i = 0 := by
      intro i hi
      rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree hi,
          coeff_eq_zero_of_lt_natTrailingDegree (lt_of_lt_of_le hi hmn), add_zero]
    exact ⟨fun h => by rw [h] at hcoeff_m; simp at hcoeff_m,
           by rw [Polynomial.trailingCoeff,
                  natTrailingDegree_eq_of (ne_of_gt hcoeff_m) hbelow]; exact hcoeff_m⟩
  · -- n ≤ m: symmetric, trailing degree is n
    have hcoeff_n : 0 < (P + Q).coeff n := by
      rw [coeff_add]
      rcases eq_or_lt_of_le hmn with hmn_eq | hmn_lt
      · exact add_pos (hmn_eq ▸ hP_pos) hQ_pos
      · rwa [coeff_eq_zero_of_lt_natTrailingDegree hmn_lt, zero_add]
    have hbelow : ∀ i, i < n → (P + Q).coeff i = 0 := by
      intro i hi
      rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree (lt_of_lt_of_le hi hmn),
          coeff_eq_zero_of_lt_natTrailingDegree hi, zero_add]
    exact ⟨fun h => by rw [h] at hcoeff_n; simp at hcoeff_n,
           by rw [Polynomial.trailingCoeff,
                  natTrailingDegree_eq_of (ne_of_gt hcoeff_n) hbelow]; exact hcoeff_n⟩

/-- If P and Q are positive in 0₊, then P * Q is positive in 0₊. -/
lemma polyPos_mul {P Q : F[X]} (hP : polyPos P) (hQ : polyPos Q) :
    polyPos (P * Q) := by
  obtain ⟨hP_ne, hP_pos⟩ := hP
  obtain ⟨hQ_ne, hQ_pos⟩ := hQ
  refine ⟨mul_ne_zero hP_ne hQ_ne, ?_⟩
  rw [Polynomial.trailingCoeff, natTrailingDegree_mul hP_ne hQ_ne,
      coeff_mul_natTrailingDegree_add_natTrailingDegree]
  exact mul_pos hP_pos hQ_pos

/-- Negation flips positivity. -/
lemma polyPos_neg_iff {P : F[X]} : polyPos (-P) ↔ P ≠ 0 ∧ P.trailingCoeff < 0 := by
  constructor
  · intro ⟨hne, hpos⟩
    rw [neg_trailingCoeff] at hpos
    exact ⟨fun h => by simp [h] at hne, by linarith⟩
  · intro ⟨hne, hneg⟩
    exact ⟨neg_ne_zero.mpr hne, by rw [neg_trailingCoeff]; linarith⟩

/-- P and -P cannot both be positive. -/
lemma not_polyPos_of_polyPos_neg {P : F[X]} (hP : polyPos P) : ¬ polyPos (-P) := by
  rw [polyPos_neg_iff]; push_neg; intro _; linarith [hP.2]

/-! ### LinearOrder construction -/

/-- The 0₊ ordering: P ≤ Q iff Q - P is zero or has positive trailing coeff. -/
instance instLEPoly : LE F[X] where
  le P Q := Q = P ∨ polyPos (Q - P)

/-- The 0₊ strict ordering: P < Q iff Q - P has positive trailing coeff. -/
instance instLTPoly : LT F[X] where
  lt P Q := polyPos (Q - P)

omit [IsStrictOrderedRing F] in
lemma le_def' {P Q : F[X]} : P ≤ Q ↔ Q = P ∨ polyPos (Q - P) := Iff.rfl
omit [IsStrictOrderedRing F] in
lemma lt_def' {P Q : F[X]} : P < Q ↔ polyPos (Q - P) := Iff.rfl

/-- `polyPos` is decidable (since equality and `<` on `F` are decidable). -/
noncomputable instance instDecidablePolyPos (P : F[X]) : Decidable (polyPos P) :=
  instDecidableAnd

/-- The 0₊ `LinearOrder` on `F[X]`. -/
noncomputable instance instLinearOrderPoly : LinearOrder F[X] where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl P := Or.inl rfl
  le_antisymm P Q hPQ hQP := by
    rcases hPQ with rfl | hPQ
    · rfl
    · rcases hQP with rfl | hQP
      · rfl
      · exact absurd (show polyPos (-(Q - P)) by rwa [neg_sub])
            (not_polyPos_of_polyPos_neg hPQ)
  le_trans P Q R hPQ hQR := by
    rcases hPQ with rfl | hPQ
    · exact hQR
    · rcases hQR with rfl | hQR
      · exact Or.inr hPQ
      · exact Or.inr (show polyPos (R - P) by
          have h := polyPos_add hQR hPQ; rwa [sub_add_sub_cancel] at h)
  le_total P Q := by
    rcases polyPos_trichotomy (Q - P) with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (show polyPos (P - Q) by rwa [neg_sub] at h))
  toDecidableLE := fun P Q => instDecidableOr
  lt_iff_le_not_ge := fun P Q => by
    constructor
    · intro h
      exact ⟨Or.inr h, fun hQP => by
        rcases hQP with rfl | hQP
        · exact h.1 (sub_self P)
        · exact not_polyPos_of_polyPos_neg h (show polyPos (-(Q - P)) by rwa [neg_sub])⟩
    · intro ⟨hle, hge⟩
      rcases hle with rfl | h
      · exact absurd (Or.inl rfl) hge
      · exact h

/-! ### Ordered ring -/

noncomputable instance : IsOrderedAddMonoid F[X] where
  add_le_add_left _ _ hab c := by
    rcases hab with rfl | hab
    · exact Or.inl rfl
    · exact Or.inr (show polyPos _ by rwa [add_sub_add_right_eq_sub])

noncomputable instance : IsOrderedCancelAddMonoid F[X] where
  le_of_add_le_add_left a _ _ h := by
    rcases h with heq | hpos
    · exact Or.inl (add_left_cancel heq)
    · exact Or.inr (show polyPos _ by rwa [add_sub_add_left_eq_sub] at hpos)

noncomputable instance : ZeroLEOneClass F[X] where
  zero_le_one := by
    right
    constructor
    · simp
    · simp [Polynomial.trailingCoeff, natTrailingDegree_one, coeff_one_zero]

instance : Nontrivial F[X] := inferInstance

noncomputable instance : PosMulStrictMono F[X] where
  mul_lt_mul_of_pos_left {a} ha {b c} hbc := by
    rw [lt_def'] at ha hbc ⊢
    rw [sub_zero] at ha
    rw [show a * c - a * b = a * (c - b) from by ring]
    exact polyPos_mul ha hbc

noncomputable instance : MulPosStrictMono F[X] where
  mul_lt_mul_of_pos_right {c} hc {a b} hab := by
    rw [lt_def'] at hc hab ⊢
    rw [sub_zero] at hc
    rw [show b * c - a * c = (b - a) * c from by ring]
    exact polyPos_mul hab hc

noncomputable instance : IsStrictOrderedRing F[X] where

/-! ### ε notation and properties -/

/-- The indeterminate ε in `F[X]`, with the 0₊ order making it infinitesimal. -/
noncomputable abbrev ε : F[X] := X

/-- ε is positive in the 0₊ order. -/
lemma ε_pos : (0 : F[X]) < ε := by
  rw [lt_def']
  constructor
  · simp
  · simp [Polynomial.trailingCoeff, natTrailingDegree_X, sub_zero]

/-- ε is infinitesimal over F: 0 < ε and ε < C a for every positive a ∈ F. -/
lemma ε_lt_C {a : F} (ha : 0 < a) : ε < (C a : F[X]) := by
  rw [lt_def']
  constructor
  · intro h
    have : (C a - X).coeff 0 = a := by simp
    rw [h] at this; simp at this; linarith
  · rw [Polynomial.trailingCoeff]
    have hne : (C a - X).coeff 0 ≠ 0 := by simp; linarith
    rw [natTrailingDegree_eq_of hne (fun i hi => by omega)]
    simp; exact ha

/-- The embedding `C : F →+* F[X]` is strictly monotone in the 0₊ order. -/
lemma C_strictMono : StrictMono (C : F → F[X]) := by
  intro a b hab
  show polyPos (C b - C a)
  rw [show C b - C a = C (b - a) from by simp [map_sub]]
  constructor
  · exact C_ne_zero.mpr (ne_of_gt (sub_pos.mpr hab))
  · rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_C, Polynomial.coeff_C_zero]
    exact sub_pos.mpr hab

end Azurite.BPR.ZeroPlus
