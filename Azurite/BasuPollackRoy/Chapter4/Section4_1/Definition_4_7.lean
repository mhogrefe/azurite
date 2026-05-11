import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# BPR Definition 4.7: Newton sums

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

For a polynomial `P : K[X]` and `i : ℕ`, the **`i`-th Newton sum** of `P` is

  `N_i(P) = ∑_{x ∈ Zer(P, C)} μ(x) · x^i`,

where `Zer(P, C)` is the set of distinct roots of `P` in `C` and `μ(x)` is
the multiplicity of `x`. Equivalently, listing the roots with multiplicity
as `x_1, …, x_p`,

  `N_i(P) = ∑_{j = 1}^p x_j^i`.

In Lean, `P.aroots C : Multiset C` already carries roots with multiplicity,
so the Newton sum is simply the sum of `i`-th powers of `P.aroots C`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {K : Type*} [Field K] {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-- **BPR Definition 4.7** (Newton sum). The `i`-th Newton sum of `P : K[X]`
    is `N_i(P) = ∑_{x ∈ aroots P} x^i` (roots counted with multiplicity in
    the algebraic closure `C`). -/
noncomputable def newtonSum (P : K[X]) (i : ℕ) : C :=
  ((P.aroots C).map (fun x => x ^ i)).sum

end Azurite.BPR.Chapter4
