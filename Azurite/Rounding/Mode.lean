/-!
# Rounding Modes

Selectors for how a real number is rounded to a `RoundingTarget`. Pure data
with a self-dual involution (`Neg`) under sign reversal of the input.
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

end Azurite
