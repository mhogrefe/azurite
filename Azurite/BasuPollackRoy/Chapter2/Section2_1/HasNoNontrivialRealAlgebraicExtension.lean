import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealField
import Mathlib.RingTheory.Algebraic.Basic

/-! # BPR Section 2.1 — `HasNoNontrivialRealAlgebraicExtension`

> A field `F` has *no non-trivial real algebraic extension* if `F` is a real
> field and every algebraic extension of `F` that is also real must coincide
> with `F` (i.e.\ the algebra map is surjective).

This is the predicate appearing as condition (d) in BPR Theorem 2.11. It is
extracted to its own file so that the (b ⇒ d) and (d ⇒ a) implication files —
which respectively conclude and consume this predicate — can both import it
without going through the larger Section 2.1 monolith.
-/

namespace Azurite.BPR

variable {u : _} (F : Type u) [Field F]

/-- **BPR Theorem 2.11 (d).** A field `F` has *no non-trivial real algebraic extension*
    if it is a real field and every algebraic extension of `F` that is also real must
    coincide with `F` (i.e., the algebra map is surjective). -/
def HasNoNontrivialRealAlgebraicExtension : Prop :=
  IsRealField F ∧
  ∀ (F₁ : Type u) [Field F₁] [Algebra F F₁],
    Algebra.IsAlgebraic F F₁ → IsRealField F₁ →
    Function.Surjective (algebraMap F F₁)

end Azurite.BPR
