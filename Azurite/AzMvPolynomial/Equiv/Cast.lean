/-
  Equivalence proofs for `AzMvPolynomial` cast functions.

  The previous Mathlib-bridge theorems (`toMvPoly_mapNatToInt`, …) related the
  cast functions to `MvPolynomial.map (algebraMap ℕ ℤ)` etc. over the GMP-backed
  `ℕ`/`ℤ`/`ℚ`/`ZMod` coefficient types.  Those coefficient types are no longer
  used (the casts now operate between the Az types `AzNat`/`AzInt`/`AzRat`/`AzZMod`
  in `AzMvPolynomial/Cast.lean`), so the bridge theorems have been removed.
-/
import Azurite.AzMvPolynomial.Cast
import Azurite.AzMvPolynomial.Equiv.Map

namespace Azurite

end Azurite
