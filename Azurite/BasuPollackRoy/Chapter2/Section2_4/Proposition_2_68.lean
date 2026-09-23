/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.Definition_2_66

/-!
# BPR Proposition 2.68

If the sign conditions in `Σ` cover the zero set `Z = Zer(P)` — that is,
`⋃_{σ ∈ Σ} Reali(σ, Z) = Z` (equivalently, every root of `P` realizes
some `σ ∈ Σ`) — then

`Mat(A, Σ) · c(Σ, Z) = TaQ(𝒬^A, P)`.

The content is the per-row identity
`TaQ(𝒬^{α}, P) = ∑_{σ ∈ Σ} σ^{α} · c(σ, Z)`: writing `TaQ(𝒬^{α}, P)` as
the sum of `sign(𝒬^{α}(x))` over the roots of `P` and partitioning the
roots by their sign condition `σ` (each contributing `σ^{α}` by
`sign_familyPow_eval_eq_signPow`) yields the weighted count.
-/

open scoped Polynomial

namespace Azurite.BPR

open Polynomial

variable {ι : Type*} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
/-- `TaQ(Q', P)` is the sum of `sign(Q'(x))` over the roots of `P`
(the open interval `(−∞, +∞)` is all of `R`). -/
theorem tarskiQuery_eq_sum_roots (Q' P : R[X]) :
    tarskiQuery Q' P = ∑ x ∈ P.roots.toFinset, (SignType.sign (Q'.eval x) : ℤ) := by
  classical
  rw [tarskiQuery, tarskiQueryOn]
  exact Finset.sum_congr (Finset.filter_true_of_mem (fun x _ => Set.mem_univ x)) (fun _ _ => rfl)

variable [Fintype ι]

/-- **Per-row form of BPR Proposition 2.68.** If `T` covers the sign
conditions of all roots of `P`, then
`TaQ(𝒬^{α}, P) = ∑_{σ ∈ T} σ^{α} · c(σ, Z)`. -/
theorem tarskiQuery_familyPow_eq_sum (P : R[X]) (Q : ι → R[X]) (α : ι → ℕ)
    (T : Finset (SignCondition ι))
    (hcover : ∀ x, P.IsRoot x → (fun i => SignType.sign ((Q i).eval x)) ∈ T) :
    tarskiQuery (familyPow Q α) P =
      ∑ σ ∈ T, (σ.pow α : ℤ) * ((σ.realizationOverFinset P Q).card : ℤ) := by
  classical
  rw [tarskiQuery_eq_sum_roots,
      ← Finset.sum_fiberwise_of_maps_to (s := P.roots.toFinset) (t := T)
        (g := fun x => (fun i => SignType.sign ((Q i).eval x)))
        (f := fun x => (SignType.sign ((familyPow Q α).eval x) : ℤ))
        (fun x hx => hcover x (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hx)).2)]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have hfilter : P.roots.toFinset.filter
        (fun x => (fun i => SignType.sign ((Q i).eval x)) = σ)
      = σ.realizationOverFinset P Q := by
    rw [SignCondition.realizationOverFinset]
    refine Finset.filter_congr (fun x _ => ?_)
    rw [funext_iff]
    rfl
  rw [hfilter,
    Finset.sum_congr rfl (fun x hx => by
      rw [sign_familyPow_eval_eq_signPow σ P Q α
        ⟨(Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp
          (Finset.mem_filter.mp hx).1)).2, (Finset.mem_filter.mp hx).2⟩]),
    Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **BPR Proposition 2.68.** If `Σ` is a duplicate-free list of sign
conditions whose realizations cover the zero set `Z = Zer(P)` — every root
of `P` realizes some `σ ∈ Σ` — then the matrix-of-signs relation holds:

`Mat(A, Σ) · c(Σ, Z) = TaQ(𝒬^A, P)`

(over `ℤ`, casting the `SignType` entries of `Mat(A, Σ)` and the counts
`c(Σ, Z)` to `ℤ`). It is immediate from the per-row identity
`tarskiQuery_familyPow_eq_sum`, since the `(i, j)`-entry of `Mat(A, Σ)` is
`σ_j^{α_i}`. -/
theorem proposition_2_68 (P : R[X]) (Q : ι → R[X]) (A : List (ι → ℕ))
    (S : List (SignCondition ι)) (hS : S.Nodup)
    (hcover : ∀ x, P.IsRoot x → (fun i => SignType.sign ((Q i).eval x)) ∈ S) :
    Matrix.mulVec (fun i j => ((matrixOfSigns A S i j : SignType) : ℤ))
        (fun j => (((S.get j).realizationOverFinset P Q).card : ℤ))
      = fun i => tarskiQuery (familyPow Q (A.get i)) P := by
  classical
  funext i
  show dotProduct (fun j => ((matrixOfSigns A S i j : SignType) : ℤ))
    (fun j => (((S.get j).realizationOverFinset P Q).card : ℤ))
    = tarskiQuery (familyPow Q (A.get i)) P
  rw [dotProduct]
  rw [tarskiQuery_familyPow_eq_sum P Q (A.get i) S.toFinset
    (fun x hx => List.mem_toFinset.mpr (hcover x hx)),
    List.sum_toFinset _ hS]
  simp only [matrixOfSigns_apply]
  rw [← List.sum_ofFn]
  congr 1
  conv_rhs => rw [← List.ofFn_get S, List.map_ofFn]
  rfl

end Azurite.BPR
