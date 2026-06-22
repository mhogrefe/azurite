import Azurite.AzZModPow2.Instances
import Azurite.AzNat.Parity
import Mathlib.Data.Nat.Log

/-!
## Modular inverse of an odd residue in `ℤ / 2^k`

An element of `ℤ / 2^k` is a unit exactly when its representative is odd.  This
file defines the inverse of such a residue by **Hensel / Newton lifting**: from
`x₀ = 1` (which inverts `a` modulo `2¹`, since `a` is odd) iterate

  `x ↦ x · (2 − a · x)`,

which **doubles the 2-adic precision** each step because the residual squares:

  `1 − a · (x · (2 − a · x)) = (1 − a · x)²`.

Hence `1 − a · xₙ = (1 − a)^(2ⁿ)`, and `⌈log₂ k⌉` iterations suffice: once
`2ⁿ ≥ k`, the factor `(1 − a)^(2ⁿ)` — divisible by `2^(2ⁿ)` because `a` odd makes
`1 − a` even — vanishes modulo `2^k`, so `a · xₙ = 1`.  Each iteration is two low
multiplications and a subtraction (the fast masking arithmetic), and there are
only `O(log k)` of them.  Correctness lives in `AzZModPow2/Equiv/Inv.lean`.
-/

namespace Azurite.AzZModPow2

variable {k : Nat}

/-- Parity of the canonical residue: `a` is odd when its representative is. An
odd residue is exactly a unit of `ℤ / 2^k`. -/
def isOdd (a : AzZModPow2 k) : Bool := a.val.isOdd

/-- The Newton/Hensel iteration `x ↦ x · (2 − a · x)`, run `n` times from `x₀ = 1`.
After `n` steps it inverts `a` modulo `2^(2ⁿ)` (see `one_sub_mul_invOddAux`). -/
def invOddAux (a : AzZModPow2 k) : Nat → AzZModPow2 k
  | 0 => 1
  | n + 1 => let x := invOddAux a n; x * (2 - a * x)

/-- **Modular inverse of an odd residue** in `ℤ / 2^k`, by `⌈log₂ k⌉` Newton steps.
Requires a proof that `a` is odd (the exact condition for `a` to be invertible). -/
def invOdd (a : AzZModPow2 k) (_h : a.isOdd = true) : AzZModPow2 k :=
  invOddAux a (Nat.clog 2 k)

end Azurite.AzZModPow2
