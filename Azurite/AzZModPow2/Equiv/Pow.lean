import Azurite.AzZModPow2.Pow
import Azurite.AzZModPow2.Equiv.Basic

/-!
## Correctness of `AzZModPow2` exponentiation

`toZMod (a.pow n) = (toZMod a) ^ n` — a one-line application of the generic
sliding-window transport `Azurite.map_slidingWindowPow` with `f = toZMod`
(which preserves `1` and `*`).
-/

namespace Azurite.AzZModPow2

variable {k : Nat}

/-- **Exponentiation agrees with `ZMod`.** -/
@[simp] theorem toZMod_pow (a : AzZModPow2 k) (n : ℕ) : toZMod (a.pow n) = (toZMod a) ^ n :=
  Azurite.map_slidingWindowPow toZMod toZMod_one toZMod_mul a n

/-- `ofZMod`-phrased companion. -/
@[simp] theorem ofZMod_pow (z : ZMod (2 ^ k)) (n : ℕ) : ofZMod (z ^ n) = (ofZMod z).pow n := by
  apply toZMod_injective
  rw [toZMod_pow, toZMod_ofZMod, toZMod_ofZMod]

end Azurite.AzZModPow2
