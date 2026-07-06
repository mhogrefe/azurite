/-
  `Azurite.NormalizedGcd AzInt` instance: the base of the nested-polynomial
  gcd tower (`Azurite/AzPolynomial/GcdTower.lean`).

  The normalized gcd over `ℤ` is the **nonnegative** gcd, computed
  magnitude-wise by `AzNat.gcd` (binary/Stein) — no `Int`/`Nat` detour.
  The canonical-form convention is documented in
  `Azurite/Algorithm/NormalizedGcd.lean`.
-/
import Azurite.Algorithm.NormalizedGcd
import Azurite.AzInt.ExactDiv
import Azurite.AzInt.Instances
import Azurite.AzNat.Gcd

namespace Azurite.AzInt

/-- The normalized (nonnegative) gcd on `AzInt`: `AzNat.gcd` of the
    magnitudes, with positive sign. Matches Mathlib's normalized `ℤ` gcd. -/
instance : NormalizedGcd AzInt where
  ngcd a b := ⟨true, AzNat.gcd a.abs b.abs, fun _ => rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- normalized gcd is nonnegative regardless of input signs
#guard NormalizedGcd.ngcd (-6 : AzInt) (4 : AzInt) == (2 : AzInt)
#guard NormalizedGcd.ngcd (6 : AzInt) (-4 : AzInt) == (2 : AzInt)
#guard NormalizedGcd.ngcd (-6 : AzInt) (-4 : AzInt) == (2 : AzInt)
-- zero conventions: `ngcd a 0 = |a|`, `ngcd 0 0 = 0`
#guard NormalizedGcd.ngcd (0 : AzInt) (-5 : AzInt) == (5 : AzInt)
#guard NormalizedGcd.ngcd (-5 : AzInt) (0 : AzInt) == (5 : AzInt)
#guard NormalizedGcd.ngcd (0 : AzInt) (0 : AzInt) == (0 : AzInt)
-- derived normalization and unit part
#guard NormalizedGcd.norm (-7 : AzInt) == (7 : AzInt)
#guard NormalizedGcd.norm (7 : AzInt) == (7 : AzInt)
#guard NormalizedGcd.unitPart (-7 : AzInt) == (-1 : AzInt)
#guard NormalizedGcd.unitPart (7 : AzInt) == (1 : AzInt)

end Tests

end Azurite.AzInt
