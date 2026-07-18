/-
  **Modular inversion at limb level**: `invMod a n` — the least
  nonnegative inverse of `a` mod `n` (meaningful for `a`, `n`
  coprime), read off the extended binary GCD: `AzInt.egcd a n`
  returns `(g, s, t)` with `s·a + t·b = g` over `ℤ`, so for coprime
  inputs the Bézout coefficient `s` IS an inverse, and the Euclidean
  reduction `s.emod n` is its least nonnegative representative.

  This is the limb-level counterpart of `Azurite.CP.invMod`
  (`CrandallPomerance/Chapter2/Algorithm_2_1_7.lean`); the two use
  DIFFERENT Bézout pairs (binary vs classical extended Euclid), but
  inverses are unique below the modulus, so the values agree on
  coprime inputs (`AzNat/Equiv/InvMod.lean`).
-/
import Azurite.AzInt.ExtendedGcd
import Azurite.AzInt.DivMod

namespace Azurite

namespace AzNat

/-- **Modular inverse**: the least nonnegative inverse of `a` mod `n`
(for `a`, `n` coprime), via the extended binary GCD. -/
def invMod (a n : AzNat) : AzNat :=
  ((AzInt.egcd a n).2.1.emod n.toAzInt).natAbs

#guard invMod (ofNat 3) (ofNat 7) == ofNat 5
#guard invMod (ofNat 10) (ofNat 17) == ofNat 12
#guard invMod (ofNat 1) (ofNat 2) == ofNat 1

end AzNat

end Azurite
