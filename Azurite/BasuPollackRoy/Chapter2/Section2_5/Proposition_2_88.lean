/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_87

/-! # BPR Proposition 2.88: projection of a semialgebraic set, and `Ext` commutes with it

Write `π : R^{k+1} → R^k` for the projection forgetting the last coordinate; in the
`Fin`-indexed encoding this is `Fin.init` (`π x = x ∘ Fin.castSucc`).

**Proposition 2.88.** If `R` is real closed and `S ⊆ R^{k+1}` is semialgebraic, then `π(S)`
is semialgebraic. Moreover, for any real closed extension `R'` of `R`,
`π(Ext(S, R')) = Ext(π(S), R')`.

Both claims rest on the *field-uniform* `Fin.init`-projection formula `initProjFormula_spec`
(the formula-level Theorem 2.76, and the engine behind Theorem 2.80): for a quantifier-free
`Φ` defining `S`, there is a single quantifier-free `Ψ'` with
`Fin.init '' Φ.realization = Ψ'.realization` over *both* `R` and `R'`. Reading this over `R`
gives that `π(S)` is semialgebraic and is defined by `Ψ'`; reading it over `R'` and using
well-definedness of the extension (`ext_eq`) gives the commutation. This is exactly BPR's
argument: "`B = π(S)` is expressed by a formula, true in `R`, hence true in `R'`."
-/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR Proposition 2.88 (first claim).** The projection `π(S) = Fin.init '' S` of a
semialgebraic set `S ⊆ R^{k+1}` is semialgebraic. (Instantiate the field-uniform projection
formula at the trivial extension `R' = R`.) -/
theorem proj_isSemialgebraic {k : ℕ} {S : Set (Fin (k + 1) → R)} (hS : IsSemialgebraicSet S) :
    IsSemialgebraicSet (Fin.init '' S) := by
  obtain ⟨Φ, hqf, hSeq⟩ := semialgebraic_isQFRealizable S hS
  obtain ⟨Ψ', hqf', hR, _⟩ := initProjFormula_spec (R := R) (R' := R) k Φ hqf
  rw [hSeq, hR]
  exact qfRealizable_isSemialgebraic hqf'

variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
variable [Algebra R R']

/-- **BPR Proposition 2.88 (second claim).** The extension commutes with the projection:
`π(Ext(S, R')) = Ext(π(S), R')`, where `π = Fin.init`. The field-uniform projection formula
`Ψ'` defines `π(S)` over `R` and realizes `π(Ext(S, R'))` over `R'`; well-definedness of the
extension (`ext_eq`) identifies the latter with `Ext(π(S), R')`. -/
theorem proposition_2_88 {k : ℕ} {S : Set (Fin (k + 1) → R)} (hS : IsSemialgebraicSet S) :
    Fin.init '' extension (R' := R') S hS
      = extension (R' := R') (Fin.init '' S) (proj_isSemialgebraic hS) := by
  obtain ⟨Φ, hqf, hSeq⟩ := semialgebraic_isQFRealizable S hS
  obtain ⟨Ψ', hqf', hR, hR'⟩ := initProjFormula_spec (R := R) (R' := R') k Φ hqf
  have hπS : Fin.init '' S = Ψ'.realization (C := R) := by rw [hSeq, hR]
  rw [ext_eq hS hSeq, ext_eq (proj_isSemialgebraic hS) hπS]
  exact hR'

end Azurite.BPR
