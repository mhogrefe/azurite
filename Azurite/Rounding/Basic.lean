import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Order.Bounds.Basic

/-!
# Rounding Targets

A `RoundingTarget` is a subset `S` of the extended reals `EReal` to which every real
number can be rounded up and rounded down, together with a tiebreaking rule used when
rounding-to-nearest is ambiguous.

The defining condition is an order-closedness property: each "slice" of `S` by a real
`x` must attain its extremum. This is neither too sparse nor too dense:

* `ℤ` (in `EReal`) works — discrete, with enough gap that `⌊x⌋` and `⌈x⌉` are visibly
  realised.
* `ℝ` (in `EReal`) works trivially — every real rounds to itself.
* `ℕ` fails in the `≤` direction for negative `x` (no nat is `≤ -1`); adjoining `-∞`
  repairs it.
* `ℚ` fails in *both* directions at any irrational `x` (e.g. `√2`): density of `ℚ`
  yields a strictly larger rational below `√2`, so no maximum exists. Density without
  order-closedness is not enough.

## Main definition

- `Azurite.RoundingTarget S` — a typeclass on `S : Set EReal` carrying:
  * `existsLeastGE`:   for every real `x`, the set of `s ∈ S` with `x ≤ s` has a minimum.
  * `existsGreatestLE`: for every real `x`, the set of `s ∈ S` with `s ≤ x` has a maximum.
  * `tiebreak`:        a choice function `S → S → S` used to pick between two equally-good
    rounding candidates.
  * `tiebreak_mem`:    the tiebreaker always returns one of its two inputs.

The two existence conditions guarantee that rounding up (`⌈·⌉_S`) and rounding down
(`⌊·⌋_S`) are well-defined on every real input. `tiebreak` will be used later to define
round-to-nearest on ties.
-/

namespace Azurite

/-- A **rounding mode** selects how a real number is rounded to a `RoundingTarget`.

* `Floor`   — round toward `−∞` (largest `s ∈ S` with `s ≤ x`).
* `Ceiling` — round toward `+∞` (smallest `s ∈ S` with `x ≤ s`).
* `Down`    — round toward `0`.
* `Up`      — round away from `0`.
* `Nearest` — round to the closest element of `S`, using the `tiebreak` function on ties.
-/
inductive RoundingMode where
  | Floor
  | Ceiling
  | Down
  | Up
  | Nearest
  deriving DecidableEq, Repr, Inhabited

/-- Negation of a `RoundingMode`: swaps `Floor` and `Ceiling`, fixes the rest. The
symmetric modes `Down`/`Up`/`Nearest` are self-dual under sign reversal of the input. -/
def RoundingMode.neg : RoundingMode → RoundingMode
  | .Floor   => .Ceiling
  | .Ceiling => .Floor
  | .Down    => .Down
  | .Up      => .Up
  | .Nearest => .Nearest

instance : Neg RoundingMode := ⟨RoundingMode.neg⟩

/-- A **rounding target** is a subset `S ⊆ EReal` to which every real number can be
rounded up and rounded down, together with a tiebreaking rule for round-to-nearest.

The two existence conditions are stated as `IsLeast` / `IsGreatest` claims on the
intersections of `S` with `[x, ∞]` and `[-∞, x]`. The tiebreaker is a binary choice
function on `S` that is required to return one of its arguments. -/
class RoundingTarget (S : Set EReal) where
  /-- For every real `x`, the set `{s ∈ S | x ≤ s}` has a minimum (the round-up target). -/
  existsLeastGE : ∀ x : ℝ, ∃ m : EReal, IsLeast {s | s ∈ S ∧ (x : EReal) ≤ s} m
  /-- For every real `x`, the set `{s ∈ S | s ≤ x}` has a maximum (the round-down target). -/
  existsGreatestLE : ∀ x : ℝ, ∃ M : EReal, IsGreatest {s | s ∈ S ∧ s ≤ (x : EReal)} M
  /-- Tiebreaker for round-to-nearest: given two candidates in `S`, return one of them. -/
  tiebreak : ↥S → ↥S → ↥S
  /-- The tiebreaker is required to return one of its two inputs. -/
  tiebreak_mem : ∀ a b : ↥S, tiebreak a b = a ∨ tiebreak a b = b

namespace RoundingTarget

variable (S : Set EReal) [RoundingTarget S]

/-- The **floor** of `x : ℝ` in `S`: the greatest element of `S` with `s ≤ x`.
Exists by `RoundingTarget.existsGreatestLE`. -/
noncomputable def roundFloor (x : ℝ) : ↥S :=
  let e := existsGreatestLE (S := S) x
  ⟨e.choose, e.choose_spec.1.1⟩

/-- The **ceiling** of `x : ℝ` in `S`: the least element of `S` with `x ≤ s`.
Exists by `RoundingTarget.existsLeastGE`. -/
noncomputable def roundCeiling (x : ℝ) : ↥S :=
  let e := existsLeastGE (S := S) x
  ⟨e.choose, e.choose_spec.1.1⟩

open Classical in
/-- Round `x : ℝ` to an element of `S` using the given rounding `mode`.

* `Floor`   — `roundFloor S x`.
* `Ceiling` — `roundCeiling S x`.
* `Down`    — toward `0`: floor when `0 ≤ x`, ceiling otherwise.
* `Up`      — away from `0`: ceiling when `0 ≤ x`, floor otherwise.
* `Nearest` — whichever of floor/ceiling is closer to `x` in `EReal`; on ties
  (including the trivial tie `x ∈ S`) uses `tiebreak`. -/
noncomputable def round (mode : RoundingMode) (x : ℝ) : ↥S :=
  match mode with
  | .Floor   => roundFloor S x
  | .Ceiling => roundCeiling S x
  | .Down    => if 0 ≤ x then roundFloor S x else roundCeiling S x
  | .Up      => if 0 ≤ x then roundCeiling S x else roundFloor S x
  | .Nearest =>
      let F := roundFloor S x
      let C := roundCeiling S x
      let dF : EReal := (x : EReal) - F.val
      let dC : EReal := C.val - (x : EReal)
      if dF < dC then F
      else if dC < dF then C
      else tiebreak F C

/-- The floor satisfies the defining `IsGreatest` property. -/
lemma isGreatest_roundFloor (x : ℝ) :
    IsGreatest {s | s ∈ S ∧ s ≤ (x : EReal)} (roundFloor S x).val :=
  (existsGreatestLE (S := S) x).choose_spec

/-- The ceiling satisfies the defining `IsLeast` property. -/
lemma isLeast_roundCeiling (x : ℝ) :
    IsLeast {s | s ∈ S ∧ (x : EReal) ≤ s} (roundCeiling S x).val :=
  (existsLeastGE (S := S) x).choose_spec

/-- If `x` itself lies in `S`, the floor of `x` is `x`. -/
lemma val_roundFloor_of_mem {x : ℝ} (hx : ((x : ℝ) : EReal) ∈ S) :
    (roundFloor S x).val = ((x : ℝ) : EReal) := by
  apply (isGreatest_roundFloor S x).unique
  exact ⟨⟨hx, le_refl _⟩, fun _ ⟨_, hsle⟩ => hsle⟩

/-- If `x` itself lies in `S`, the ceiling of `x` is `x`. -/
lemma val_roundCeiling_of_mem {x : ℝ} (hx : ((x : ℝ) : EReal) ∈ S) :
    (roundCeiling S x).val = ((x : ℝ) : EReal) := by
  apply (isLeast_roundCeiling S x).unique
  exact ⟨⟨hx, le_refl _⟩, fun _ ⟨_, hxle⟩ => hxle⟩

/-- If `x ∈ S`, then rounding `x` (in any mode) returns `x`. -/
theorem val_round_of_mem (mode : RoundingMode) {x : ℝ} (hx : ((x : ℝ) : EReal) ∈ S) :
    (round S mode x).val = ((x : ℝ) : EReal) := by
  have hF : (roundFloor S x).val = ((x : ℝ) : EReal) := val_roundFloor_of_mem S hx
  have hC : (roundCeiling S x).val = ((x : ℝ) : EReal) := val_roundCeiling_of_mem S hx
  cases mode with
  | Floor => exact hF
  | Ceiling => exact hC
  | Down =>
    show (if 0 ≤ x then roundFloor S x else roundCeiling S x).val = ((x : ℝ) : EReal)
    split_ifs <;> [exact hF; exact hC]
  | Up =>
    show (if 0 ≤ x then roundCeiling S x else roundFloor S x).val = ((x : ℝ) : EReal)
    split_ifs <;> [exact hC; exact hF]
  | Nearest =>
    show (let F := roundFloor S x
          let C := roundCeiling S x
          let dF : EReal := ((x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((x : ℝ) : EReal)
          if dF < dC then F
          else if dC < dF then C
          else tiebreak F C).val = ((x : ℝ) : EReal)
    simp only
    have hd_eq : ((x : ℝ) : EReal) - (roundFloor S x).val =
                 (roundCeiling S x).val - ((x : ℝ) : EReal) := by rw [hF, hC]
    have h1 : ¬ ((x : ℝ) : EReal) - (roundFloor S x).val <
                (roundCeiling S x).val - ((x : ℝ) : EReal) := by
      rw [hd_eq]; exact lt_irrefl _
    have h2 : ¬ (roundCeiling S x).val - ((x : ℝ) : EReal) <
                ((x : ℝ) : EReal) - (roundFloor S x).val := by
      rw [← hd_eq]; exact lt_irrefl _
    rw [if_neg h1, if_neg h2]
    rcases tiebreak_mem (roundFloor S x) (roundCeiling S x) with hT | hT
    · rw [hT]; exact hF
    · rw [hT]; exact hC

end RoundingTarget

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
          if dF < dC then F
          else if dC < dF then C
          else tiebreak F C).val =
        -(let F := roundFloor S x
          let C := roundCeiling S x
          let dF : EReal := ((x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((x : ℝ) : EReal)
          if dF < dC then F
          else if dC < dF then C
          else tiebreak F C).val
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
    by_cases h1 : dF < dC
    · -- dF < dC: original picks F, negated picks Cn = -F.
      have h2 : ¬ dC < dF := not_lt.mpr (le_of_lt h1)
      simp only [h1, h2, ↓reduceIte]
      exact hCn_val
    · by_cases h2 : dC < dF
      · -- dC < dF: original picks C, negated picks Fn = -C.
        simp only [h1, h2, ↓reduceIte]
        exact hFn_val
      · -- Tie: both branches use tiebreak. Split on F = C.
        simp only [h1, h2, ↓reduceIte]
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

end Symmetric

end RoundingTarget

end Azurite
