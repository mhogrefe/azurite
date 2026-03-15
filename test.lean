import Azurite.DensePoly.Equiv.Eval
import Mathlib.Algebra.Polynomial.Roots

open Polynomial

namespace Azurite.DensePoly

variable {R : Type _} [CommRing R] [IsDomain R] [Infinite R]

lemma funext {p q : DensePoly R} (ext : ∀ r : R, p.eval r = q.eval r) : p = q := by
  have heq : DensePoly.toPoly p = DensePoly.toPoly q := Polynomial.funext (fun r => by
    rw [eval_toPoly, eval_toPoly, ext r])
  exact toPoly_inj.mp heq

end Azurite.DensePoly
