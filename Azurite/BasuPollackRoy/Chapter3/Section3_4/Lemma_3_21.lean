/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_4.BoundedSet
import Azurite.BasuPollackRoy.Chapter3.Section3_3.Proposition_3_16
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_1
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_89

/-! # BPR §3.4 — Lemma 3.21: `lim_ε` commutes with a continuous semialgebraic function

Let `g` be a semialgebraic continuous function on a closed bounded semialgebraic set `S ⊆ Rᵏ`. If
`ϕ ∈ Ext(S, R⟨ε⟩)`, then `g ∘ ϕ` is bounded over `R` and `g(lim_ε ϕ) = lim_ε(g ∘ ϕ)`.

The proof: writing `b = lim_ε ϕ`, `ϕ − b` is infinitesimal (`limEps_infinitesimal`), so `b ∈ S` (as
`S` is closed, `b` is a limit of points of `S`). Then `g` is continuous at `b ∈ S`: for `r > 0` pick
`η` with `‖z − b‖ < η ⇒ ‖g(z) − g(b)‖ < r` on `S`. This is an inclusion of semialgebraic sets on the
graph of `g`; extending to `R⟨ε⟩` (`ext_mono`, `ext_comap`, `ext_openBall`) and feeding in
`(ϕ, g ∘ ϕ) ∈ Ext(graph g)` (Proposition 3.16) with `‖ϕ − b‖ < η` (infinitesimal) gives
`‖g ∘ ϕ − g(b)‖ < r`. As `r` was arbitrary, `g ∘ ϕ − g(b)` is infinitesimal, so `g ∘ ϕ` is bounded
and `lim_ε(g ∘ ϕ) = g(b)`. -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

attribute [local instance] isRealClosed_semialgGerm

/-- **An infinitesimally-close tuple lies in every standard ball.** If each `vᵢ − wᵢ` is
infinitesimal, then `‖v − w‖² < (algebraMap η)²` for every standard `η > 0`. -/
theorem infinitesimal_normSq_lt {m : ℕ} [Nonempty (Fin m)] {v : Fin m → SemialgGerm R}
    {w : Fin m → R} (hinf : ∀ i, IsInfinitesimal (v i - algebraMap R (SemialgGerm R) (w i)))
    (η : R) (hη : 0 < η) :
    euclideanNormSq (v - fun i => algebraMap R (SemialgGerm R) (w i))
      < (algebraMap R (SemialgGerm R) η) ^ 2 := by
  set A := algebraMap R (SemialgGerm R)
  have hbound : (m : R) * (η / ((m : R) + 1)) ^ 2 < η ^ 2 := by
    have hX : 0 < (η / ((m : R) + 1)) ^ 2 := by positivity
    have hmlt : (m : R) < ((m : R) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := R) m]
    have h2 : ((m : R) + 1) ^ 2 * (η / ((m : R) + 1)) ^ 2 = η ^ 2 := by field_simp
    nlinarith [mul_lt_mul_of_pos_right hmlt hX, h2]
  rw [euclideanNormSq]
  calc ∑ i, ((v - fun i => A (w i)) i) ^ 2
      < ∑ _i : Fin m, A ((η / ((m : R) + 1)) ^ 2) := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro i _
        rw [Pi.sub_apply, map_pow]
        have hb := hinf i (η / ((m : R) + 1)) (by positivity)
        rw [abs_lt] at hb
        nlinarith [hb.1, hb.2]
    _ = A ((m : R) * (η / ((m : R) + 1)) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          show ((m : SemialgGerm R)) = A (m : R) from (map_natCast A m).symm, ← map_mul]
    _ < (A η) ^ 2 := by rw [← map_pow]; exact algebraMap_lt_algebraMap_of_lt hbound

/-- If the extension of a semialgebraic set is nonempty, so is the set. -/
theorem ext_nonempty_of_nonempty {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R']
    [IsRealClosed R'] [Algebra R R'] {T : Set (Fin k → R)} (hT : IsSemialgebraicSet T)
    (h : (extension (R' := R') T hT).Nonempty) : T.Nonempty := by
  rcases T.eq_empty_or_nonempty with he | hne
  · exfalso
    obtain ⟨y, hy⟩ := h
    rw [ext_congr hT (he ▸ hT : IsSemialgebraicSet (∅ : Set (Fin k → R))) he,
      ext_empty] at hy
    exact hy.elim
  · exact hne

/-- **BPR Lemma 3.21.** Let `g : Rᵏ → Rˡ` be continuous and semialgebraic on a closed bounded
semialgebraic set `S`, and `ϕ ∈ Ext(S, R⟨ε⟩)`. Then `g ∘ ϕ` (= `Ext(g)(ϕ)`, as graph membership) is
bounded over `R`, and `g(lim_ε ϕ) = lim_ε(g ∘ ϕ)`. -/
theorem lemma_3_21 [Nonempty (Fin k)] {ℓ : ℕ} [Nonempty (Fin ℓ)]
    (S : Set (Fin k → R)) (hS : IsSemialgebraicSet S) (hScl : IsClosed S) (hSb : IsBoundedSet S)
    (g : (Fin k → R) → (Fin ℓ → R)) (hg : ∀ j, IsSemialgContinuousOn S (fun y => g y j))
    (ϕ : Fin k → SemialgGerm R) (hϕ : ϕ ∈ extension (R' := SemialgGerm R) S hS) :
    ∃ (gϕ : Fin ℓ → SemialgGerm R) (hbnd : ∀ j, gϕ j ∈ boundedGerms),
      Fin.append ϕ gϕ ∈ extension (R' := SemialgGerm R) (funGraph S g)
          (isSemialgebraicFunction_of_coords (fun j => (hg j).1)) ∧
      (fun i => limEps ⟨ϕ i, ext_mem_boundedGerms hS hSb hϕ i⟩) ∈ S ∧
      ∀ j, limEps ⟨gϕ j, hbnd j⟩
        = g (fun i => limEps ⟨ϕ i, ext_mem_boundedGerms hS hSb hϕ i⟩) j := by
  set A := algebraMap R (SemialgGerm R) with hA
  set b : Fin k → R := fun i => limEps ⟨ϕ i, ext_mem_boundedGerms hS hSb hϕ i⟩ with hb_def
  have hϕinf : ∀ i, IsInfinitesimal (ϕ i - A (b i)) := fun i =>
    limEps_infinitesimal ⟨ϕ i, ext_mem_boundedGerms hS hSb hϕ i⟩
  -- representatives `ϕ i = germHom t (c i)` with the trajectory landing in `S` on `(0, t)`.
  choose rep hrep using fun i => Quotient.exists_rep (ϕ i)
  obtain ⟨t₀, ht₀, htle⟩ : ∃ t : R, 0 < t ∧ ∀ i, t ≤ (rep i).bound := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty (fun i => (rep i).bound), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]; exact fun i _ => (rep i).bound_pos
    · exact fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set c₀ : Fin k → semialgContSubring t₀ := fun i =>
    ⟨(rep i).toFun, mem_semialgContSubring.mpr ((rep i).isSemialgContinuous.mono
      (isSemialgebraicSet_rightNbhd t₀) (rightNbhd_subset (htle i)))⟩ with hc₀
  have hgi₀ : (fun i => germHom t₀ ht₀ (c₀ i)) = ϕ := by
    funext i; rw [germHom_apply, ← hrep i]; exact Quotient.sound ⟨t₀, ht₀, fun _ _ _ => rfl⟩
  obtain ⟨t₁, ht₁, H₁⟩ := (proposition_3_16_mem t₀ ht₀ c₀ S hS).mp (hgi₀ ▸ hϕ)
  set t := min t₀ t₁ with ht_def
  have ht : 0 < t := lt_min ht₀ ht₁
  set c : Fin k → semialgContSubring t := fun i =>
    ⟨(rep i).toFun, mem_semialgContSubring.mpr ((rep i).isSemialgContinuous.mono
      (isSemialgebraicSet_rightNbhd t) (rightNbhd_subset (le_trans (min_le_left _ _) (htle i))))⟩
    with hc
  have hgi : (fun i => germHom t ht (c i)) = ϕ := by
    funext i; rw [germHom_apply, ← hrep i]; exact Quotient.sound ⟨t, ht, fun _ _ _ => rfl⟩
  have hmaps : Set.MapsTo (fun u : Fin 1 → R => fun i => (c i : (Fin 1 → R) → R) u)
      (rightNbhd t) S := by
    intro u hu
    have hh : (fun i => (c₀ i : (Fin 1 → R) → R) (constPt (u 0))) ∈ S :=
      H₁ (u 0) hu.1 (lt_of_lt_of_le hu.2 (min_le_right _ _))
    have huc : u = constPt (u 0) := by funext j; rw [Subsingleton.elim j 0]; rfl
    have huf : (fun i => (c i : (Fin 1 → R) → R) u)
        = (fun i => (c₀ i : (Fin 1 → R) → R) (constPt (u 0))) :=
      funext fun i => congrArg (rep i).toFun huc
    show (fun i => (c i : (Fin 1 → R) → R) u) ∈ S
    rw [huf]; exact hh
  -- `g ∘ ϕ` and the graph membership (Proposition 3.16).
  set gϕ : Fin ℓ → SemialgGerm R := fun j => germHom t ht (germCompTuple t c g hg hmaps j)
    with hgϕ
  have hcomp : Fin.append ϕ gϕ ∈ extension (R' := SemialgGerm R) (funGraph S g)
      (isSemialgebraicFunction_of_coords (fun j => (hg j).1)) := by
    have hpc := proposition_3_16_comp t ht c g hg hmaps
    rwa [hgi] at hpc
  -- `b ∈ S` (closure of `S`, which is `S`).
  have hbS : b ∈ S := by
    rw [← hScl.closure_eq, mem_closure_iff_ball]
    intro r hr
    have hball : ϕ ∈ openBall (fun i => A (b i)) (A r) := by
      rw [mem_openBall]; exact infinitesimal_normSq_lt hϕinf r hr
    have hext : ϕ ∈ extension (R' := SemialgGerm R) (S ∩ openBall b r)
        (hS.inter (isSemialgebraicSet_openBall b r)) := by
      rw [ext_inter hS (isSemialgebraicSet_openBall b r)]
      refine ⟨hϕ, ?_⟩
      rw [ext_openBall]
      exact hball
    obtain ⟨z, hz⟩ := ext_nonempty_of_nonempty _ ⟨ϕ, hext⟩
    exact ⟨z, hz.1, mem_openBall.mp hz.2⟩
  -- `g ∘ ϕ − g(b)` is infinitesimal: continuity at `b` transferred to `R⟨ε⟩`.
  have hcont : ContinuousOn g S := continuousOn_of_components (fun j => (hg j).2)
  rw [continuousOn_iff_ball] at hcont
  have hgϕinf : ∀ j, IsInfinitesimal (gϕ j - A (g b j)) := by
    intro j r hr
    obtain ⟨η, hη, hηc⟩ := hcont b hbS r hr
    have hincl : funGraph S g ∩ {x : Fin (k + ℓ) → R | x ∘ Fin.castAdd ℓ ∈ openBall b η}
        ⊆ {x : Fin (k + ℓ) → R | x ∘ Fin.natAdd k ∈ openBall (g b) r} := by
      rintro x ⟨hxg, hxz⟩
      rw [mem_funGraph] at hxg
      rw [Set.mem_ofPred_eq, mem_openBall_iff_norm hη] at hxz
      rw [Set.mem_ofPred_eq, mem_openBall_iff_norm hr, hxg.2]
      exact hηc (x ∘ Fin.castAdd ℓ) hxg.1 hxz
    have hsemiZ : IsSemialgebraicSet {x : Fin (k + ℓ) → R | x ∘ Fin.castAdd ℓ ∈ openBall b η} :=
      IsSemialgebraicSet.comap (Fin.castAdd ℓ) (isSemialgebraicSet_openBall b η)
    have hsemiW : IsSemialgebraicSet {x : Fin (k + ℓ) → R | x ∘ Fin.natAdd k ∈ openBall (g b) r} :=
      IsSemialgebraicSet.comap (Fin.natAdd k) (isSemialgebraicSet_openBall (g b) r)
    have hsemiG : IsSemialgebraicSet (funGraph S g) :=
      isSemialgebraicFunction_of_coords (fun j => (hg j).1)
    have hPmem : Fin.append ϕ gϕ ∈ extension (R' := SemialgGerm R)
        (funGraph S g ∩ {x | x ∘ Fin.castAdd ℓ ∈ openBall b η}) (hsemiG.inter hsemiZ) := by
      rw [ext_inter hsemiG hsemiZ]
      refine ⟨hcomp, ?_⟩
      rw [ext_comap (Fin.castAdd ℓ) (Fin.castAdd_injective k ℓ) (isSemialgebraicSet_openBall b η),
        Set.mem_ofPred_eq, ext_openBall,
        show Fin.append ϕ gϕ ∘ Fin.castAdd ℓ = ϕ from funext (fun i => Fin.append_left ϕ gϕ i)]
      rw [mem_openBall]; exact infinitesimal_normSq_lt hϕinf η hη
    have hPW := ext_mono (hsemiG.inter hsemiZ) hsemiW hincl hPmem
    rw [ext_comap (Fin.natAdd k) (Fin.natAdd_injective ℓ k) (isSemialgebraicSet_openBall (g b) r),
      Set.mem_ofPred_eq, ext_openBall,
      show Fin.append ϕ gϕ ∘ Fin.natAdd k = gϕ from funext (fun j => Fin.append_right ϕ gϕ j),
      mem_openBall] at hPW
    have hcomp_j : (gϕ j - A (g b j)) ^ 2
        ≤ euclideanNormSq (gϕ - fun i => A ((g b) i)) := by
      rw [euclideanNormSq]
      have := Finset.single_le_sum (f := fun i => ((gϕ - fun i => A ((g b) i)) i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
      rwa [Pi.sub_apply] at this
    have halgr : (0 : SemialgGerm R) < A r := by
      rw [hA, ← map_zero (algebraMap R (SemialgGerm R))]; exact algebraMap_lt_algebraMap_of_lt hr
    exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt hcomp_j hPW) (le_of_lt halgr)
  -- assemble.
  have hbnd : ∀ j, gϕ j ∈ boundedGerms := fun j =>
    mem_boundedGerms_of_infinitesimal (hgϕinf j)
  exact ⟨gϕ, hbnd, hcomp, hbS, fun j =>
    limEps_eq_of_infinitesimal ⟨gϕ j, hbnd j⟩ (g b j) (hgϕinf j)⟩

end Azurite.BPR
