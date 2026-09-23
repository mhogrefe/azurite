/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.Proposition_2_72
import Azurite.BasuPollackRoy.Chapter2.Section2_4.Proposition_2_68

/-!
# BPR Corollary 2.73: `Mₛ · c(Σ, Z) = TaQ(𝒬^A, P)`

Combining the matrix-of-signs relation `Mat(A, Σ) · c(Σ, Z) = TaQ(𝒬^A, P)`
(Proposition 2.68) with `Mat(A, Σ) = Mₛ` (Proposition 2.72) gives the
linear system `Mₛ · c(Σ, Z) = TaQ(𝒬^A, P)`.

The lex enumeration `signFn s` is a **bijection** onto the sign conditions
`{0,1,-1}^{Fin s}` (`signFn_injective`, `signFn_surjective`), so the list
`Σ = signList s` is duplicate-free and complete — the `Nodup` and covering
hypotheses of Proposition 2.68 hold automatically, and Corollary 2.73 has
no side conditions.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The lex enumeration `signFn s` is injective. -/
theorem signFn_injective (s : Nat) : Function.Injective (signFn s) := by
  induction s with
  | zero =>
    intro i j _
    exact Fin.ext (by have h1 := i.2; have h2 := j.2; simp only [pow_zero] at h1 h2; omega)
  | succ s ih =>
    intro i j h
    simp only [signFn] at h
    have h2 := congrFun h (Fin.last s)
    rw [Fin.snoc_last, Fin.snoc_last] at h2
    have h1 : signFn s ((@finProdFinEquiv (3 ^ s) 3).symm i).1
            = signFn s ((@finProdFinEquiv (3 ^ s) 3).symm j).1 := by
      funext k
      have hk := congrFun h k.castSucc
      rwa [Fin.snoc_castSucc, Fin.snoc_castSucc] at hk
    have e2 : ((@finProdFinEquiv (3 ^ s) 3).symm i).2 = ((@finProdFinEquiv (3 ^ s) 3).symm j).2 := by
      have hinj : Function.Injective (![(0 : SignType), 1, -1]) := by decide
      exact hinj h2
    exact (@finProdFinEquiv (3 ^ s) 3).symm.injective (Prod.ext (ih h1) e2)

/-- The lex enumeration `signFn s` is surjective onto all sign conditions. -/
theorem signFn_surjective (s : Nat) : Function.Surjective (signFn s) := by
  induction s with
  | zero => intro σ; exact ⟨0, Subsingleton.elim _ _⟩
  | succ s ih =>
    intro σ
    obtain ⟨a, ha⟩ := ih (fun k => σ k.castSucc)
    have hsurj : Function.Surjective (![(0 : SignType), 1, -1]) := by decide
    obtain ⟨b, hb⟩ := hsurj (σ (Fin.last s))
    refine ⟨@finProdFinEquiv (3 ^ s) 3 (a, b), ?_⟩
    simp only [signFn, Equiv.symm_apply_apply]
    rw [ha, hb]
    exact Fin.snoc_init_self σ

/-- `Σ = signList s` is duplicate-free. -/
theorem signList_nodup (s : Nat) : (signList s).Nodup := by
  rw [signList, List.nodup_ofFn]
  exact signFn_injective s

/-- `Σ = signList s` lists *every* sign condition. -/
theorem signList_complete (s : Nat) (τ : SignCondition (Fin s)) : τ ∈ signList s :=
  List.mem_ofFn.mpr (signFn_surjective s τ)

/-- **BPR Corollary 2.73.** `Mₛ · c(Σ, Z) = TaQ(𝒬^A, P)`. The matrix is
`Mₛ` relabeled (`Matrix.submatrix` by `Fin.cast`) to the list-length
indices of `Mat(A, Σ)`; the side conditions of Proposition 2.68 are
discharged automatically since `Σ` is the complete duplicate-free lex
enumeration of all sign conditions. -/
theorem corollary_2_73 (s : Nat) (P : R[X]) (Q : Fin s → R[X]) :
    Matrix.mulVec
        (fun i j => ((Matrix.submatrix (signMatrix s).toFn (Fin.cast (by simp [expList]))
          (Fin.cast (by simp [signList])) i j : SignType) : ℤ))
        (fun j => ((((signList s).get j).realizationOverFinset P Q).card : ℤ))
      = fun i => tarskiQuery (familyPow Q ((expList s).get i)) P := by
  have h68 := proposition_2_68 P Q (expList s) (signList s) (signList_nodup s)
    (fun x _ => signList_complete s _)
  rwa [proposition_2_72] at h68

end Azurite.BPR
