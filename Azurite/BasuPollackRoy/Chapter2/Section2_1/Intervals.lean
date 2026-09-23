import Mathlib.Order.Interval.Set.Defs
import Mathlib.Basic.Real.Basic

/-! # BPR Section 2.1 — Notation: Intervals

**Notation (BPR p.34).** Closed, open and semi-open intervals in an ordered
field `R` are denoted in the usual way:

* `(a, b) = {x ∈ R | a < x < b}`
* `[a, b] = {x ∈ R | a ≤ x ≤ b}`
* `(a, b] = {x ∈ R | a < x ≤ b}`
* `[a, b) = {x ∈ R | a ≤ x < b}`
* `(a, +∞) = {x ∈ R | a < x}`, `[a, +∞) = {x ∈ R | a ≤ x}`
* `(−∞, a) = {x ∈ R | x < a}`, `(−∞, a] = {x ∈ R | x ≤ a}`

In Mathlib (namespace `Set`, defined in `Mathlib.Order.Interval.Set.Defs`,
requiring only `[Preorder α]`):

| BPR        | Mathlib       | Membership          |
|------------|---------------|---------------------|
| `(a, b)`   | `Set.Ioo a b` | `a < x ∧ x < b`     |
| `[a, b]`   | `Set.Icc a b` | `a ≤ x ∧ x ≤ b`     |
| `[a, b)`   | `Set.Ico a b` | `a ≤ x ∧ x < b`     |
| `(a, b]`   | `Set.Ioc a b` | `a < x ∧ x ≤ b`     |
| `(a, +∞)`  | `Set.Ioi a`   | `a < x`             |
| `[a, +∞)`  | `Set.Ici a`   | `a ≤ x`             |
| `(−∞, a)`  | `Set.Iio a`   | `x < a`             |
| `(−∞, a]`  | `Set.Iic a`   | `x ≤ a`             |

Naming mnemonic: `I{left}{right}` where `c` = closed, `o` = open, `i` =
infinite. Membership lemmas follow the pattern `Set.mem_Ioo` etc.

The `example` definitions below are smoke tests pinning each Mathlib
interval set to its set-builder form by `rfl` — they document the BPR ↔
Mathlib correspondence at the type level.
-/

example : ∀ a b : ℝ, Set.Ioo a b = {x | a < x ∧ x < b} := fun _ _ => rfl
example : ∀ a b : ℝ, Set.Icc a b = {x | a ≤ x ∧ x ≤ b} := fun _ _ => rfl
example : ∀ a b : ℝ, Set.Ioc a b = {x | a < x ∧ x ≤ b} := fun _ _ => rfl
example : ∀ a b : ℝ, Set.Ico a b = {x | a ≤ x ∧ x < b} := fun _ _ => rfl
example : ∀ a : ℝ, Set.Ioi a = {x | a < x} := fun _ => rfl
example : ∀ a : ℝ, Set.Ici a = {x | a ≤ x} := fun _ => rfl
example : ∀ a : ℝ, Set.Iio a = {x | x < a} := fun _ => rfl
example : ∀ a : ℝ, Set.Iic a = {x | x ≤ a} := fun _ => rfl
