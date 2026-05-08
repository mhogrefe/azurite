import Azurite.BasuPollackRoy.Chapter1.Section1_1.FieldFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Formula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization

/-!
# BPR Section 1.3 — The projection `π`

A basic constructible set `S ⊂ C^{k+1}` is (the `C`-realization of)
a *basic formula* over `Fin (k+1)`-many variables — see
`Formula.IsBasicFormula` in Section 1.1. We define its projection
`π(S) ⊂ C^k`, which forgets the last coordinate.

The projection is defined for an arbitrary formula `Φ` over
`Fin (k+1)` variables: `y ∈ Φ.proj` iff some extension
`Fin.snoc y x` to `C^{k+1}` satisfies `Φ`. In the basic case
described above, this agrees with BPR's form using `specialize`
(established atom-wise in `realization_eq_zero` / `realization_ne_zero`
from Section 1.1 together with `eval_specialize`).
-/

namespace Azurite.BPR

variable {k : ℕ} {C : Type*} [Field C]

namespace Formula

/-- BPR's projection `π(S)`: for a formula `Φ` describing a set in
`C^{k+1}`, `Φ.proj` is the subset of `C^k` consisting of points `y`
such that some extension `Fin.snoc y x : Fin (k+1) → C` lies in
`Φ`'s realization. -/
noncomputable def proj
    (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) C)) :
    Set (Fin k → C) :=
  { y | ∃ x : C, Fin.snoc y x ∈ Φ.realization (C := C) }

end Formula

end Azurite.BPR
