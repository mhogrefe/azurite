import Azurite.BasuPollackRoy.Chapter3.Section3_2.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # BPR §3.2 — examples of convex sets

The whole space `R^k`, the empty set, and singletons are convex; on the line, every order-connected
subset of `R` (in particular every open or closed interval) is convex. The last statement is the
"a connected subset of `R` is convex" fact — connected subsets of a linearly ordered field are
exactly the order-connected ones. -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **`R^k` is convex.** -/
theorem isConvex_univ : IsConvex (Set.univ : Set (Fin k → R)) :=
  isConvex_iff_convex.mpr convex_univ

/-- **The empty set is convex.** -/
theorem isConvex_empty : IsConvex (∅ : Set (Fin k → R)) :=
  isConvex_iff_convex.mpr convex_empty

/-- **A single point is convex.** -/
theorem isConvex_singleton (p : Fin k → R) : IsConvex ({p} : Set (Fin k → R)) :=
  isConvex_iff_convex.mpr (convex_singleton p)

/-- **A connected (order-connected) subset of `R` is convex.** For a subset `I ⊆ R` that is
order-connected — equivalently, an interval — the corresponding line-set `{v | v₀ ∈ I}` is convex.
The convex combination `(1 − λ) x₀ + λ y₀` of two points of `I` lies in `I` by order-connectedness. -/
theorem isConvex_of_ordConnected_sect {I : Set R} (hI : I.OrdConnected) :
    IsConvex {v : Fin 1 → R | v 0 ∈ I} := by
  have hIconv : Convex R I := convex_iff_ordConnected.mpr hI
  intro x hx y hy l hl
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  exact hIconv hx hy (by linarith [hl.2]) hl.1 (by ring)

/-- **A closed interval of `R` is convex.** -/
theorem isConvex_Icc (a b : R) : IsConvex {v : Fin 1 → R | v 0 ∈ Set.Icc a b} :=
  isConvex_of_ordConnected_sect Set.ordConnected_Icc

/-- **An open interval of `R` is convex.** -/
theorem isConvex_Ioo (a b : R) : IsConvex {v : Fin 1 → R | v 0 ∈ Set.Ioo a b} :=
  isConvex_of_ordConnected_sect Set.ordConnected_Ioo

end Azurite.BPR
