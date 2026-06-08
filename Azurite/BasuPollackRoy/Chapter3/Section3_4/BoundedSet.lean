import Azurite.BasuPollackRoy.Chapter3.Section3_4.LimEps
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_5

/-! # BPR §3.4 — bounded semialgebraic sets and the extension of a ball

A semialgebraic set `S ⊆ Rᵏ` is **bounded** (`IsBoundedSet`) when it is contained in a closed ball
`closedBall 0 M`. The key fact for `lim_ε` is that the extension of a bounded set to `R⟨ε⟩` is
bounded: every coordinate of a point `ϕ ∈ Ext(S, R⟨ε⟩)` is a bounded germ (so `lim_ε(ϕ_i)` is
defined). This rests on `ext_openBall`: the extension of an open ball is the open ball with the same
(base-field-embedded) centre and radius. -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

attribute [local instance] isRealClosed_semialgGerm

/-- A semialgebraic set is **bounded** if it is contained in a closed ball about the origin. -/
def IsBoundedSet (S : Set (Fin k → R)) : Prop := ∃ M : R, 0 < M ∧ S ⊆ closedBall 0 M

/-- **The extension of a bounded set is bounded.** Each coordinate of a point in `Ext(S, R⟨ε⟩)` is a
bounded germ, so its limit `lim_ε` is defined. -/
theorem ext_mem_boundedGerms {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    (hSb : IsBoundedSet S) {ϕ : Fin k → SemialgGerm R}
    (hϕ : ϕ ∈ extension (R' := SemialgGerm R) S hS) (i : Fin k) :
    ϕ i ∈ boundedGerms := by
  obtain ⟨M, hM, hSsub⟩ := hSb
  -- `S ⊆ B(0, M+1)`.
  have hSopen : S ⊆ openBall (0 : Fin k → R) (M + 1) := fun y hy => by
    rw [mem_openBall]
    have hy' := hSsub hy
    rw [mem_closedBall] at hy'
    nlinarith [hy', hM, euclideanNormSq_nonneg (y - 0)]
  -- push to `R⟨ε⟩`.
  have hext : ϕ ∈ openBall (algebraMap R (SemialgGerm R) ∘ (0 : Fin k → R))
      (algebraMap R (SemialgGerm R) (M + 1)) := by
    rw [← ext_openBall]
    exact ext_mono hS (isSemialgebraicSet_openBall _ _) hSopen hϕ
  have hcenter : (algebraMap R (SemialgGerm R) ∘ (0 : Fin k → R))
      = (0 : Fin k → SemialgGerm R) := by funext j; simp
  rw [mem_openBall, hcenter, sub_zero] at hext
  have hsq : (ϕ i) ^ 2 ≤ euclideanNormSq ϕ := by
    rw [euclideanNormSq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hM1 : (0 : SemialgGerm R) < algebraMap R (SemialgGerm R) (M + 1) := by
    rw [← map_zero (algebraMap R (SemialgGerm R))]
    exact algebraMap_lt_algebraMap_of_lt (by linarith)
  exact ⟨M + 1, by linarith, abs_lt_of_sq_lt_sq (lt_of_le_of_lt hsq hext) (le_of_lt hM1)⟩

end Azurite.BPR
