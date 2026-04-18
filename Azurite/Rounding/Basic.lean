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

end RoundingTarget

end Azurite
