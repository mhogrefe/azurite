import Azurite.Rounding.Basic

/-!
# Symmetric Rounding Targets

A `SymmetricRoundingTarget` extends `RoundingTarget` with sign-reversal closure:
`0 ∈ S`, `s ∈ S → -s ∈ S`, and a tiebreaker that commutes with negation in the
swapped order. The main theorem is `round_neg`: rounding `-x` with mode `m`
equals the negation of rounding `x` with mode `-m`.
-/

namespace Azurite

/-- A **symmetric rounding target** is a `RoundingTarget` that contains `0`, is closed
under negation, and whose tiebreak commutes with sign reversal in the swapped order.

`zero_mem` is needed for `round_neg` at `x = 0` for the `Down`/`Up` modes. The
`tiebreak_neg` condition is `tiebreak (-a) (-b) = -(tiebreak b a)` — the swap reflects
that under negation, floor/ceiling roles exchange. The side condition `a.val ≠ -b.val`
excludes the involution fixed-point pairs (where the axiom would force a value of `0`,
incompatible with `tiebreak_mem` unless `a.val = b.val = 0`). For spec-relevant ties
this case forces `F = C = 0` via `zero_mem`, so it is handled trivially in `round_neg`. -/
class SymmetricRoundingTarget (S : Set EReal) extends RoundingTarget S where
  /-- `0` is in `S`. -/
  zero_mem : (0 : EReal) ∈ S
  /-- `S` is closed under negation. -/
  neg_mem : ∀ {s : EReal}, s ∈ S → -s ∈ S
  /-- The tiebreak commutes with negation in the swapped order, away from the
  involution fixed points: `tiebreak (-a) (-b) = -(tiebreak b a)` whenever
  `a.val ≠ -b.val`. -/
  tiebreak_neg : ∀ a b : ↥S, a.val ≠ -b.val →
    (RoundingTarget.tiebreak
      ⟨-a.val, neg_mem a.property⟩
      ⟨-b.val, neg_mem b.property⟩).val =
    -(RoundingTarget.tiebreak b a).val

namespace RoundingTarget

section Symmetric

variable (S : Set EReal) [SymmetricRoundingTarget S]

private lemma coe_neg (x : ℝ) : ((-x : ℝ) : EReal) = -((x : ℝ) : EReal) := by
  push_cast; rfl

/-- Floor of `-x` equals the negation of the ceiling of `x`. -/
lemma val_roundFloor_neg (x : ℝ) :
    (roundFloor S (-x)).val = -(roundCeiling S x).val := by
  apply (isGreatest_roundFloor S (-x)).unique
  refine ⟨⟨SymmetricRoundingTarget.neg_mem (roundCeiling S x).property, ?_⟩, ?_⟩
  · rw [coe_neg]
    exact (EReal.neg_le_neg_iff).mpr (isLeast_roundCeiling S x).1.2
  · rintro s ⟨hs, hsle⟩
    have h_ms : -s ∈ S := SymmetricRoundingTarget.neg_mem hs
    have h_x_le_ms : (x : EReal) ≤ -s := by
      rw [coe_neg] at hsle
      exact (EReal.le_neg).mpr hsle
    have h_le := (isLeast_roundCeiling S x).2 ⟨h_ms, h_x_le_ms⟩
    exact (EReal.le_neg).mp h_le

/-- Ceiling of `-x` equals the negation of the floor of `x`. -/
lemma val_roundCeiling_neg (x : ℝ) :
    (roundCeiling S (-x)).val = -(roundFloor S x).val := by
  apply (isLeast_roundCeiling S (-x)).unique
  refine ⟨⟨SymmetricRoundingTarget.neg_mem (roundFloor S x).property, ?_⟩, ?_⟩
  · rw [coe_neg]
    exact (EReal.neg_le_neg_iff).mpr (isGreatest_roundFloor S x).1.2
  · rintro s ⟨hs, hxle⟩
    have h_ms : -s ∈ S := SymmetricRoundingTarget.neg_mem hs
    have h_ms_le_x : -s ≤ (x : EReal) := by
      rw [coe_neg] at hxle
      exact (EReal.neg_le).mp hxle
    have h_le := (isGreatest_roundFloor S x).2 ⟨h_ms, h_ms_le_x⟩
    exact (EReal.neg_le).mpr h_le

/-- Floor of `0` equals `0`. -/
lemma val_roundFloor_zero : (roundFloor S 0).val = 0 := by
  apply (isGreatest_roundFloor S 0).unique
  refine ⟨⟨SymmetricRoundingTarget.zero_mem, le_refl _⟩, ?_⟩
  rintro s ⟨_, hsle⟩
  exact_mod_cast hsle

/-- Ceiling of `0` equals `0`. -/
lemma val_roundCeiling_zero : (roundCeiling S 0).val = 0 := by
  apply (isLeast_roundCeiling S 0).unique
  refine ⟨⟨SymmetricRoundingTarget.zero_mem, le_refl _⟩, ?_⟩
  rintro s ⟨_, hxle⟩
  exact_mod_cast hxle

/-- Floor of `-x` equals the negated ceiling of `x` as elements of `↥S`. -/
lemma roundFloor_neg (x : ℝ) :
    roundFloor S (-x) =
      ⟨-(roundCeiling S x).val,
        SymmetricRoundingTarget.neg_mem (roundCeiling S x).property⟩ :=
  Subtype.ext (val_roundFloor_neg S x)

/-- Ceiling of `-x` equals the negated floor of `x` as elements of `↥S`. -/
lemma roundCeiling_neg (x : ℝ) :
    roundCeiling S (-x) =
      ⟨-(roundFloor S x).val,
        SymmetricRoundingTarget.neg_mem (roundFloor S x).property⟩ :=
  Subtype.ext (val_roundCeiling_neg S x)

open Classical in
/-- Over a `SymmetricRoundingTarget`, rounding `-x` with mode `m` equals the negation
of rounding `x` with mode `-m`. -/
theorem round_neg (mode : RoundingMode) (x : ℝ) :
    (round S mode (-x)).val = -(round S (-mode) x).val := by
  cases mode with
  | Floor =>
    show (roundFloor S (-x)).val = -(roundCeiling S x).val
    exact val_roundFloor_neg S x
  | Ceiling =>
    show (roundCeiling S (-x)).val = -(roundFloor S x).val
    exact val_roundCeiling_neg S x
  | Down =>
    show (if 0 ≤ -x then roundFloor S (-x) else roundCeiling S (-x)).val =
        -(if 0 ≤ x then roundFloor S x else roundCeiling S x).val
    by_cases hx0 : 0 ≤ x
    · by_cases hnx0 : 0 ≤ -x
      · have hx_eq : x = 0 := by linarith
        rw [hx_eq, neg_zero]
        simp only [le_refl, ↓reduceIte]
        rw [val_roundFloor_zero, neg_zero]
      · simp only [hnx0, ↓reduceIte, hx0]
        exact val_roundCeiling_neg S x
    · have hnx0 : 0 ≤ -x := by linarith
      simp only [hnx0, ↓reduceIte, hx0]
      exact val_roundFloor_neg S x
  | Up =>
    show (if 0 ≤ -x then roundCeiling S (-x) else roundFloor S (-x)).val =
        -(if 0 ≤ x then roundCeiling S x else roundFloor S x).val
    by_cases hx0 : 0 ≤ x
    · by_cases hnx0 : 0 ≤ -x
      · have hx_eq : x = 0 := by linarith
        rw [hx_eq, neg_zero]
        simp only [le_refl, ↓reduceIte]
        rw [val_roundCeiling_zero, neg_zero]
      · simp only [hnx0, ↓reduceIte, hx0]
        exact val_roundFloor_neg S x
    · have hnx0 : 0 ≤ -x := by linarith
      simp only [hnx0, ↓reduceIte, hx0]
      exact val_roundCeiling_neg S x
  | Nearest =>
    show (let F := roundFloor S (-x)
          let C := roundCeiling S (-x)
          let dF : EReal := ((-x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((-x : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C).val =
        -(let F := roundFloor S x
          let C := roundCeiling S x
          let dF : EReal := ((x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((x : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C).val
    simp only
    set F : ↥S := roundFloor S x with hF_def
    set C : ↥S := roundCeiling S x with hC_def
    set Fn : ↥S := roundFloor S (-x) with hFn_def
    set Cn : ↥S := roundCeiling S (-x) with hCn_def
    have hFn_val : Fn.val = -C.val := val_roundFloor_neg S x
    have hCn_val : Cn.val = -F.val := val_roundCeiling_neg S x
    -- Distance comparisons under negation.
    have h_dFn : ((-x : ℝ) : EReal) - Fn.val = C.val - ((x : ℝ) : EReal) := by
      rw [hFn_val, coe_neg, sub_eq_add_neg, neg_neg, add_comm, ← sub_eq_add_neg]
    have h_dCn : Cn.val - ((-x : ℝ) : EReal) = ((x : ℝ) : EReal) - F.val := by
      rw [hCn_val, coe_neg, sub_eq_add_neg, neg_neg, add_comm, ← sub_eq_add_neg]
    rw [h_dFn, h_dCn]
    set dF : EReal := ((x : ℝ) : EReal) - F.val
    set dC : EReal := C.val - ((x : ℝ) : EReal)
    rcases lt_trichotomy dF dC with h1 | h1 | h1
    · -- dF < dC: original picks F, negated picks Cn = -F.
      rw [show compare dC dF = .gt from compare_gt_iff_gt.mpr h1,
          show compare dF dC = .lt from compare_lt_iff_lt.mpr h1]
      exact hCn_val
    · -- Tie: both branches use tiebreak. Split on F = C.
      rw [show compare dC dF = .eq from compare_eq_iff_eq.mpr h1.symm,
          show compare dF dC = .eq from compare_eq_iff_eq.mpr h1]
      show (tiebreak Fn Cn).val = -(tiebreak F C).val
      by_cases hFC : F = C
      · -- F = C: trivial. tiebreak collapses on equal-value pairs.
        have h_val_eq : F.val = C.val := congrArg Subtype.val hFC
        rcases tiebreak_mem Fn Cn with hT | hT <;>
          rcases tiebreak_mem F C with hT' | hT' <;>
          simp [hT, hT', hFn_val, hCn_val, h_val_eq]
      · -- F ≠ C: derive C.val ≠ -F.val from `zero_mem` and the rounding bounds,
        -- then apply the `tiebreak_neg` axiom with `(a := C, b := F)`.
        have hC_ne : C.val ≠ -F.val := by
          intro hC_eq
          apply hFC
          apply Subtype.ext
          -- Goal: F.val = C.val. Derive both equal to 0.
          have hF_le_x : F.val ≤ (x : EReal) := (isGreatest_roundFloor S x).1.2
          have hx_le_C : (x : EReal) ≤ C.val := (isLeast_roundCeiling S x).1.2
          have h0memS : (0 : EReal) ∈ S := SymmetricRoundingTarget.zero_mem
          by_cases hx0 : (0 : ℝ) ≤ x
          · -- x ≥ 0: 0 is a candidate for F, so F.val ≥ 0; combined with
            -- F.val ≤ -F.val gives F.val = 0.
            have h0le_x : (0 : EReal) ≤ (x : EReal) := by exact_mod_cast hx0
            have hF_ge_0 : (0 : EReal) ≤ F.val :=
              (isGreatest_roundFloor S x).2 ⟨h0memS, h0le_x⟩
            have hF_le_neg : F.val ≤ -F.val := by
              rw [← hC_eq]; exact hF_le_x.trans hx_le_C
            have h_neg_F_le_0 : -F.val ≤ 0 := by
              have := (EReal.neg_le_neg_iff).mpr hF_ge_0
              rwa [neg_zero] at this
            have hF_le_0 : F.val ≤ 0 := hF_le_neg.trans h_neg_F_le_0
            have hF_eq_0 : F.val = 0 := le_antisymm hF_le_0 hF_ge_0
            rw [hF_eq_0, hC_eq, hF_eq_0, neg_zero]
          · -- x < 0: 0 is a candidate for C, so C.val ≤ 0, hence F.val = -C.val ≥ 0;
            -- but F.val ≤ x < 0, contradiction.
            push Not at hx0
            have hx_lt_0 : (x : EReal) < 0 := by exact_mod_cast hx0
            have hx_le_0 : (x : EReal) ≤ 0 := hx_lt_0.le
            have hC_le_0 : C.val ≤ 0 :=
              (isLeast_roundCeiling S x).2 ⟨h0memS, hx_le_0⟩
            have h_neg_F_le_0 : -F.val ≤ 0 := by rw [← hC_eq]; exact hC_le_0
            have hF_ge_0 : (0 : EReal) ≤ F.val := by
              have := (EReal.neg_le_neg_iff).mpr h_neg_F_le_0
              rwa [neg_zero, neg_neg] at this
            have hF_lt_0 : F.val < 0 := lt_of_le_of_lt hF_le_x hx_lt_0
            exact absurd hF_ge_0 (not_le.mpr hF_lt_0)
        have hFn_eq : Fn = ⟨-C.val, SymmetricRoundingTarget.neg_mem C.property⟩ :=
          Subtype.ext hFn_val
        have hCn_eq : Cn = ⟨-F.val, SymmetricRoundingTarget.neg_mem F.property⟩ :=
          Subtype.ext hCn_val
        rw [hFn_eq, hCn_eq]
        exact SymmetricRoundingTarget.tiebreak_neg C F hC_ne
    · -- dC < dF: original picks C, negated picks Fn = -C.
      rw [show compare dC dF = .lt from compare_lt_iff_lt.mpr h1,
          show compare dF dC = .gt from compare_gt_iff_gt.mpr h1]
      exact hFn_val

end Symmetric

end RoundingTarget

end Azurite
