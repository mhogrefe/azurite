import Azurite.BasuPollackRoy.Chapter2.Section2_6.Lemma_2_93
import Azurite.BasuPollackRoy.Chapter2.Section2_6.RootTelescope
import Mathlib.FieldTheory.IsRealClosed.Basic

/-! # BPR §2.6 Theorem 2.91 — `R⟨⟨ε⟩⟩` is real closed (reduction)

For a real closed (hence ordered) field `R`, the field of Puiseux series `R⟨⟨ε⟩⟩` is real closed.

By Mathlib's Artin–Schreier characterization `IsRealClosed.of_linearOrderedField`, proving
`IsRealClosed (R⟨⟨ε⟩⟩)` (an ordered field) reduces to exactly two obligations:

* **squares:** every nonnegative element is a square — this is Lemma 2.93 (`isSquare_of_nonneg`);
* **odd-degree roots:** every odd-degree polynomial has a root — the Puiseux/Newton-polygon
  construction.

This file discharges the squares obligation and records the reduction
`isRealClosed_puiseux_of_exists_root`, isolating the odd-degree-root existence as the single
remaining (large) obligation. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **The squares half of real-closedness.** Every nonnegative Puiseux series is a square (Lemma
2.93 for the positive case; `0 = 0²` for zero). -/
theorem isSquare_of_nonneg {a : PuiseuxSeries R} (ha : 0 ≤ a) : IsSquare a := by
  rcases ha.lt_or_eq with h | h
  · exact lemma_2_93 h
  · rw [← h]; exact ⟨0, (mul_zero 0).symm⟩

/-- **Reduction of Theorem 2.91.** Given that every odd-degree polynomial over `R⟨⟨ε⟩⟩` has a
root, `R⟨⟨ε⟩⟩` is real closed. The hypothesis is the content of the Newton-polygon root
construction; the squares condition is Lemma 2.93. -/
theorem isRealClosed_puiseux_of_exists_root
    (hroot : ∀ {f : Polynomial (PuiseuxSeries R)}, Odd f.natDegree → ∃ x, f.IsRoot x) :
    IsRealClosed (PuiseuxSeries R) :=
  IsRealClosed.of_linearOrderedField (fun hx => isSquare_of_nonneg hx) (fun hf => hroot hf)

/-- **Theorem 2.91.** For a real closed field `R`, the field of Puiseux series `R⟨⟨ε⟩⟩` is real
closed. Both obligations of `IsRealClosed.of_linearOrderedField` are discharged: squares
(`isSquare_of_nonneg`, Lemma 2.93) and odd-degree roots (`exists_root_of_odd`, the Newton–Puiseux
construction in `RootTelescope.lean`). -/
theorem isRealClosed_puiseuxSeries : IsRealClosed (PuiseuxSeries R) :=
  isRealClosed_puiseux_of_exists_root (fun hf => exists_root_of_odd hf)

end Azurite.BPR
