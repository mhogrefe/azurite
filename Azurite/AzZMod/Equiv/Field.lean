import Azurite.AzZMod.Field
import Azurite.AzZMod.Equiv.RingEquiv
import Mathlib.Algebra.Field.ZMod

/-!
## Inversion and division agree with `ZMod`

For a prime modulus both `AzZMod p` and `ZMod p.toNat` are fields and `toZMod` is
a ring homomorphism, so it automatically preserves `⁻¹` and `/`
(`map_inv₀` / `map_div₀`).
-/

namespace Azurite.AzZMod

variable {p : AzNat}

/-- **Inversion agrees with `ZMod`.** -/
@[simp] theorem toZMod_inv [Fact (Nat.Prime p.toNat)] (a : AzZMod p) :
    toZMod a⁻¹ = (toZMod a)⁻¹ :=
  map_inv₀ toZModRingHom a

/-- **Division agrees with `ZMod`.** -/
@[simp] theorem toZMod_div [Fact (Nat.Prime p.toNat)] (a b : AzZMod p) :
    toZMod (a / b) = toZMod a / toZMod b :=
  map_div₀ toZModRingHom a b

end Azurite.AzZMod
