/-
Copyright (c) 2025 Azurite contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Azurite contributors
-/
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.FieldTheory.RatFunc.Basic

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
  · by_contra h; push Not at h
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
  rw [polyPos_neg_iff]; push Not; intro _; linarith [hP.2]

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

/-! ### Stage 2: The 0₊ order on F(ε) = RatFunc F

BPR defines: P(ε)/Q(ε) > 0 iff P(ε)·Q(ε) > 0 in the polynomial 0₊ order.

We use the canonical `num`/`denom` decomposition from `RatFunc` to define
positivity, then construct a `LinearOrder`.
-/

/-- Positivity in the 0₊ order on `RatFunc F`:
    a rational function is positive iff `num * denom` is positive
    in the polynomial 0₊ order. -/
def rfPos (r : RatFunc F) : Prop := polyPos (r.num * r.denom)

/-- `rfPos` characterization: r is positive iff r ≠ 0 and
    `(r.num * r.denom).trailingCoeff > 0`. -/
lemma rfPos_def {r : RatFunc F} :
    rfPos r ↔ r ≠ 0 ∧ 0 < (r.num * r.denom).trailingCoeff := by
  simp only [rfPos, polyPos]
  constructor
  · intro ⟨hne, hpos⟩
    exact ⟨fun h => by simp [h] at hne, hpos⟩
  · intro ⟨hne, hpos⟩
    exact ⟨mul_ne_zero (RatFunc.num_ne_zero hne) (RatFunc.denom_ne_zero r), hpos⟩

/-- A nonzero square is positive in the 0₊ order. -/
lemma polyPos_sq {b : F[X]} (hb : b ≠ 0) : polyPos (b ^ 2) :=
  ⟨pow_ne_zero 2 hb, by
    rw [sq, Polynomial.trailingCoeff]
    rw [Polynomial.natTrailingDegree_mul hb hb]
    rw [Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree]
    exact mul_self_pos.mpr (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hb)⟩

omit [IsStrictOrderedRing F] in
/-- `polyPos a` is equivalent to `0 < a` in the custom F[X] order. -/
lemma polyPos_iff_lt {a : F[X]} : polyPos a ↔ (0 : F[X]) < a :=
  ⟨fun h => lt_def'.mpr (by rwa [sub_zero]),
   fun h => by have := lt_def'.mp h; rwa [sub_zero] at this⟩

/-- `polyPos` is invariant under multiplication by a nonzero square.
    Morally: `a * b² > 0 ↔ a > 0` since `b² > 0`. -/
lemma polyPos_mul_sq_iff {a b : F[X]} (hb : b ≠ 0) :
    polyPos (a * b ^ 2) ↔ polyPos a := by
  rw [polyPos_iff_lt, polyPos_iff_lt]
  constructor
  · intro h
    have hb2 := polyPos_iff_lt.mp (polyPos_sq hb)
    exact ((pos_iff_pos_of_mul_pos h).mpr hb2)
  · intro h
    exact mul_pos h (polyPos_iff_lt.mp (polyPos_sq hb))

/-- Negation flips `rfPos`. Uses `num_denom_neg` and the square trick. -/
lemma rfPos_neg_iff (r : RatFunc F) (hr : r ≠ 0) :
    rfPos (-r) ↔ ¬ rfPos r := by
  have hndm := RatFunc.num_denom_neg r
  have hd := RatFunc.denom_ne_zero r
  have hnd := RatFunc.denom_ne_zero (-r)
  have hmul_ne : r.num * r.denom ≠ 0 :=
    mul_ne_zero (RatFunc.num_ne_zero hr) hd
  -- Key algebraic identity: (-r).num * (-r).denom * r.denom² = -(r.num * r.denom) * (-r).denom²
  have key : (-r).num * (-r).denom * r.denom ^ 2 =
      -(r.num * r.denom) * (-r).denom ^ 2 := by
    -- From num_denom_neg: (-r).num * r.denom = -(r.num) * (-r).denom
    -- Rearranging: both sides = (-r).num * r.denom * (-r).denom * r.denom
    calc (-r).num * (-r).denom * r.denom ^ 2
        = (-r).num * r.denom * ((-r).denom * r.denom) := by ring
      _ = -r.num * (-r).denom * ((-r).denom * r.denom) := by rw [hndm]
      _ = -(r.num * r.denom) * (-r).denom ^ 2 := by ring
  rw [rfPos, rfPos, ← polyPos_mul_sq_iff hd, key]
  rw [polyPos_mul_sq_iff hnd]
  constructor
  · intro h hn
    exact not_polyPos_of_polyPos_neg hn h
  · intro hn
    rcases polyPos_trichotomy (r.num * r.denom) with h | h | h
    · exact absurd h hn
    · exact absurd h hmul_ne
    · exact h

/-- Key: a nonzero rational function has `num * denom` nonzero,
    so exactly one of `rfPos r` or `rfPos (-r)` holds. -/
lemma rfPos_trichotomy (r : RatFunc F) : rfPos r ∨ r = 0 ∨ rfPos (-r) := by
  by_cases hr : r = 0
  · exact Or.inr (Or.inl hr)
  · rcases polyPos_trichotomy (r.num * r.denom) with h | h | h
    · exact Or.inl h
    · exact absurd h (mul_ne_zero (RatFunc.num_ne_zero hr) (RatFunc.denom_ne_zero r))
    · right; right
      exact (rfPos_neg_iff r hr).mpr (fun hpos => not_polyPos_of_polyPos_neg hpos h)

/-- If r and -r are both positive, contradiction. -/
lemma not_rfPos_neg {r : RatFunc F} (hr : rfPos r) : ¬ rfPos (-r) := by
  by_cases hrz : r = 0
  · simp [hrz, rfPos, polyPos] at hr
  · exact (rfPos_neg_iff r hrz).not_left.mpr hr

/-- Bridge lemma: `rfPos` of a quotient `algebraMap p / algebraMap q` is equivalent to
    `polyPos (p * q)`. This allows working with arbitrary representatives via `induction_on`.
    Proof: cross-multiply `r.num * q = p * r.denom`, then use the square trick. -/
lemma rfPos_div {p q : F[X]} (hq : q ≠ 0) :
    rfPos (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q) ↔ polyPos (p * q) := by
  set r := algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q with hr_def
  -- Cross-multiplication: r.num * q = p * r.denom
  have hmap_q := (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr hq
  have hmap_d := (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr
    (RatFunc.denom_ne_zero r)
  have hcross_map := (div_eq_div_iff hmap_d hmap_q).mp (RatFunc.num_div_denom r)
  rw [← map_mul, ← map_mul] at hcross_map
  have hcross : r.num * q = p * r.denom := RatFunc.algebraMap_injective F hcross_map
  -- Key: r.num * r.denom * q² = p * q * r.denom²
  have key : r.num * r.denom * q ^ 2 = p * q * r.denom ^ 2 := by
    calc r.num * r.denom * q ^ 2
        = r.num * q * (r.denom * q) := by ring
      _ = p * r.denom * (r.denom * q) := by rw [hcross]
      _ = p * q * r.denom ^ 2 := by ring
  rw [rfPos, ← polyPos_mul_sq_iff hq, key]
  exact polyPos_mul_sq_iff (RatFunc.denom_ne_zero r)

/-- rfPos is preserved by addition. Uses `induction_on` to write rational functions as
    `algebraMap p / algebraMap q`, then reduces to the F[X] ordered ring via `rfPos_div`:
    `a*b > 0` and `c*d > 0` imply `(a*d + b*c)*(b*d) = a*b*d² + c*d*b² > 0`. -/
lemma rfPos_add {r s : RatFunc F} (hr : rfPos r) (hs : rfPos s) :
    rfPos (r + s) := by
  induction r using RatFunc.induction_on with
  | f a b hb =>
  induction s using RatFunc.induction_on with
  | f c d hd =>
  rw [rfPos_div hb] at hr
  rw [rfPos_div hd] at hs
  have hmap_b := (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr hb
  have hmap_d := (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr hd
  rw [div_add_div _ _ hmap_b hmap_d, ← map_mul, ← map_mul, ← map_add, ← map_mul]
  rw [rfPos_div (mul_ne_zero hb hd), polyPos_iff_lt]
  calc (0 : F[X])
      < a * b * d ^ 2 + c * d * b ^ 2 :=
        add_pos (mul_pos (polyPos_iff_lt.mp hr) (polyPos_iff_lt.mp (polyPos_sq hd)))
                (mul_pos (polyPos_iff_lt.mp hs) (polyPos_iff_lt.mp (polyPos_sq hb)))
    _ = (a * d + b * c) * (b * d) := by ring

instance instLERatFunc : LE (RatFunc F) where
  le r s := s = r ∨ rfPos (s - r)

instance instLTRatFunc : LT (RatFunc F) where
  lt r s := rfPos (s - r)

omit [IsStrictOrderedRing F] in
lemma rf_le_def {r s : RatFunc F} : r ≤ s ↔ s = r ∨ rfPos (s - r) := Iff.rfl
omit [IsStrictOrderedRing F] in
lemma rf_lt_def {r s : RatFunc F} : r < s ↔ rfPos (s - r) := Iff.rfl

noncomputable instance instLinearOrderRatFunc : LinearOrder (RatFunc F) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl r := Or.inl rfl
  le_antisymm r s hrs hsr := by
    rcases hrs with rfl | hrs
    · rfl
    · rcases hsr with rfl | hsr
      · rfl
      · exact absurd (show rfPos (-(s - r)) by rwa [neg_sub]) (not_rfPos_neg hrs)
  le_trans r s t hrs hst := by
    rcases hrs with rfl | hrs
    · exact hst
    · rcases hst with rfl | hst
      · exact Or.inr hrs
      · exact Or.inr (by rw [show t - r = (t - s) + (s - r) from by ring]; exact rfPos_add hst hrs)
  le_total r s := by
    rcases rfPos_trichotomy (s - r) with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (show rfPos (r - s) by rwa [neg_sub] at h))
  lt_iff_le_not_ge r s := by
    constructor
    · intro h
      refine ⟨Or.inr h, fun hsr => ?_⟩
      rcases hsr with rfl | hsr
      · have : (r - r).num * (r - r).denom ≠ 0 := h.1
        simp at this
      · exact not_rfPos_neg h (show rfPos (-(s - r)) by rwa [neg_sub])
    · intro ⟨hle, hge⟩
      rcases hle with rfl | h
      · exact absurd (Or.inl rfl) hge
      · exact h
  toDecidableLE := fun r s => by
    change Decidable (s = r ∨ rfPos (s - r))
    haveI : DecidableEq (RatFunc F) := Classical.decEq _
    haveI : Decidable (rfPos (s - r)) := Classical.dec _
    exact instDecidableOr

/-! ### `RatFunc F` is an ordered field in the 0₊ order -/

/-- `rfPos` is preserved by multiplication. As for addition, reduce to the `F[X]` ordered ring via
`rfPos_div`: `(a / b)·(c / d) = (a·c) / (b·d)` with `a·c·(b·d) = (a·b)·(c·d) > 0`. -/
lemma rfPos_mul {r s : RatFunc F} (hr : rfPos r) (hs : rfPos s) : rfPos (r * s) := by
  induction r using RatFunc.induction_on with
  | f a b hb =>
  induction s using RatFunc.induction_on with
  | f c d hd =>
  rw [rfPos_div hb] at hr
  rw [rfPos_div hd] at hs
  rw [div_mul_div_comm, ← map_mul, ← map_mul, rfPos_div (mul_ne_zero hb hd),
    show a * c * (b * d) = a * b * (c * d) from by ring]
  exact polyPos_mul hr hs

noncomputable instance : IsOrderedAddMonoid (RatFunc F) where
  add_le_add_left _ _ hab c := by
    rcases hab with rfl | hab
    · exact Or.inl rfl
    · exact Or.inr (show rfPos _ by rwa [add_sub_add_right_eq_sub])

noncomputable instance : IsOrderedCancelAddMonoid (RatFunc F) where
  le_of_add_le_add_left a _ _ h := by
    rcases h with heq | hpos
    · exact Or.inl (add_left_cancel heq)
    · exact Or.inr (show rfPos _ by rwa [add_sub_add_left_eq_sub] at hpos)

noncomputable instance : ZeroLEOneClass (RatFunc F) where
  zero_le_one := by
    refine Or.inr ?_
    rw [sub_zero,
      show (1 : RatFunc F) = algebraMap F[X] (RatFunc F) 1 / algebraMap F[X] (RatFunc F) 1 from by
        rw [map_one, div_one],
      rfPos_div one_ne_zero, mul_one]
    exact ⟨one_ne_zero, by simp [Polynomial.trailingCoeff, natTrailingDegree_one, coeff_one_zero]⟩

noncomputable instance : PosMulStrictMono (RatFunc F) where
  mul_lt_mul_of_pos_left {a} ha {b c} hbc := by
    rw [rf_lt_def] at ha hbc ⊢
    rw [sub_zero] at ha
    rw [show a * c - a * b = a * (c - b) from by ring]
    exact rfPos_mul ha hbc

noncomputable instance : MulPosStrictMono (RatFunc F) where
  mul_lt_mul_of_pos_right {c} hc {a b} hab := by
    rw [rf_lt_def] at hc hab ⊢
    rw [sub_zero] at hc
    rw [show b * c - a * c = (b - a) * c from by ring]
    exact rfPos_mul hab hc

noncomputable instance : IsStrictOrderedRing (RatFunc F) where

/-! ### ε in RatFunc F and 1/ε -/

/-- ε as an element of `RatFunc F`. -/
noncomputable def εR : RatFunc F := algebraMap F[X] (RatFunc F) X

/-- 1/ε in `RatFunc F`. -/
noncomputable def εR_inv : RatFunc F := εR⁻¹

/-- The embedding of F into `RatFunc F` via `C : F → F[X] → RatFunc F`. -/
noncomputable def ιR (a : F) : RatFunc F := algebraMap F[X] (RatFunc F) (C a)

/-- 1/ε is greater than every element of F in the 0₊ order.
    Proof: `1/X - C(a) = (1 - C(a)·X)/X`, so by `rfPos_div` we need
    `polyPos ((1 - C a * X) * X)`, which holds since `trailingCoeff = 1 > 0`. -/
lemma εR_inv_gt_ιR (a : F) : ιR a < εR_inv := by
  rw [rf_lt_def]
  show rfPos (εR_inv - ιR a)
  have hX : (algebraMap F[X] (RatFunc F)) X ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr X_ne_zero
  have hform : εR_inv - ιR a =
      algebraMap F[X] (RatFunc F) (1 - C a * X) / algebraMap F[X] (RatFunc F) X := by
    simp only [εR_inv, εR, ιR]
    rw [inv_eq_one_div,
        show algebraMap F[X] (RatFunc F) (C a) = algebraMap F[X] (RatFunc F) (C a) / 1
          from (div_one _).symm]
    rw [div_sub_div _ _ hX one_ne_zero, mul_one, mul_one]
    congr 1
    rw [← map_mul, mul_comm,
        show (1 : RatFunc F) = algebraMap F[X] (RatFunc F) 1 from (map_one _).symm,
        ← map_sub]
  rw [hform, rfPos_div X_ne_zero]
  have h1 : (1 - C a * X : F[X]) ≠ 0 := by
    intro h; have := congr_arg (fun p => p.coeff 0) h; simp at this
  exact ⟨mul_ne_zero h1 X_ne_zero, by
    rw [trailingCoeff, natTrailingDegree_mul h1 X_ne_zero,
        natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by simp [constantCoeff_apply])]
    simp [natTrailingDegree_X, coeff_sub, coeff_one, coeff_X]⟩

/-- 1/ε is unbounded over F: for every positive a ∈ F, ι(a) < 1/ε in the 0₊ order. -/
lemma εR_inv_unbounded {a : F} (_ha : 0 < a) : ιR a < εR_inv :=
  εR_inv_gt_ιR a

end Azurite.BPR.ZeroPlus

