import Azurite.BasuPollackRoy.Chapter3.Section3_4.Lemma_3_21
import Azurite.BasuPollackRoy.Chapter3.Section3_3.Theorem_3_19
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Exercise_2_17
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83

/-! # BPR §3.4 — Theorem 3.20: the image of a closed bounded set is closed and bounded

Let `S ⊆ Rᵏ` be a closed bounded semialgebraic set and `g` a semialgebraic continuous function on
`S`. Then `g(S)` is closed and bounded.

**Closed.** For `x ∈ closure(g(S))`, the transfer principle gives `ϕ ∈ Ext(g(S), R⟨ε⟩)` with
`lim_ε(ϕ) = x` (`exists_germ_in_ext_ball`). Since `Ext(g(S)) = Ext(g)(Ext S)` (Proposition 2.90,
assembled from the image–projection and graph–extension toolkit), there is `ϕ' ∈ Ext(S)` with
`g ∘ ϕ' = ϕ`. By Lemma 3.21 (`S` closed bounded), `lim_ε(ϕ') ∈ S` and
`g(lim_ε ϕ') = lim_ε(g ∘ ϕ') = lim_ε ϕ = x`, so `x ∈ g(S)`. -/

namespace Azurite.BPR

open MvPolynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The polynomial `ε · ∑ⱼ (w_j)² − 1` over `R[ε]`, where the `w` are the last `ℓ` coordinates
(`ε = Polynomial.X`). Its sign-locus encodes `1 < ε·‖w‖²`. -/
noncomputable def normPolyEps (k ℓ : ℕ) (R : Type*) [Field R] :
    MvPolynomial (Fin (k + ℓ)) (Polynomial R) :=
  C Polynomial.X * (∑ j : Fin ℓ, (X (Fin.natAdd k j)) ^ 2) - 1

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Substituting `ε ↦ t` and evaluating at `z` gives `t·∑ⱼ(z_natAdd j)² − 1`. -/
theorem aeval_substAtom_normPolyEps {ℓ : ℕ} (t : R) (z : Fin (k + ℓ) → R) :
    aeval z ((normPolyEps k ℓ R).map (Polynomial.aeval t).toRingHom)
      = t * (∑ j : Fin ℓ, (z (Fin.natAdd k j)) ^ 2) - 1 := by
  rw [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, normPolyEps]
  simp only [map_sub, map_mul, map_sum, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X, map_one]

/-- Evaluating at a germ tuple `z` (with `ε ↦ idGerm`) gives `idGerm·∑ⱼ(z_natAdd j)² − 1`. -/
theorem aeval_normPolyEps_germ {ℓ : ℕ} (z : Fin (k + ℓ) → SemialgGerm R) :
    aeval z (normPolyEps k ℓ R)
      = idGerm * (∑ j : Fin ℓ, (z (Fin.natAdd k j)) ^ 2) - 1 := by
  rw [normPolyEps]
  simp only [map_sub, map_mul, map_sum, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C, map_one]
  congr 2
  show algebraMap (Polynomial R) (SemialgGerm R) Polynomial.X = idGerm
  rw [RingHom.algebraMap_toAlgebra]
  exact Polynomial.aeval_X _

/-- **BPR Theorem 3.20.** The image `g(S)` of a closed bounded semialgebraic set under a semialgebraic
continuous function is closed and bounded. -/
theorem theorem_3_20 [Nonempty (Fin k)] {ℓ : ℕ} [Nonempty (Fin ℓ)]
    (S : Set (Fin k → R)) (hS : IsSemialgebraicSet S) (hScl : IsClosed S) (hSb : IsBoundedSet S)
    (g : (Fin k → R) → (Fin ℓ → R)) (hg : ∀ j, IsSemialgContinuousOn S (fun y => g y j)) :
    IsClosed (g '' S) ∧ IsBoundedSet (g '' S) := by
  haveI : IsRealClosed (SemialgGerm R) := isRealClosed_semialgGerm
  have hgf : IsSemialgebraicFunction S g := isSemialgebraicFunction_of_coords (fun j => (hg j).1)
  have hgS : IsSemialgebraicSet (g '' S) := (proposition_2_83 hgf).1 hS (subset_refl S)
  have hmaps_g : Set.MapsTo g S (g '' S) := fun x hx => Set.mem_image_of_mem g hx
  obtain ⟨g', hgraph, hmaps'⟩ := proposition_2_89 (R' := SemialgGerm R) hS hgS hgf hmaps_g
  refine ⟨?_, ?_⟩
  · -- `g(S)` is closed.
    have hsub : closure (g '' S) ⊆ g '' S := by
      intro x hx
      obtain ⟨ϕ, hϕext, hϕball⟩ := exists_germ_in_ext_ball (g '' S) hgS x hx
      -- `ϕ` is infinitesimally close to `x`, so `lim_ε ϕ = x`.
      have hinf : ∀ j, IsInfinitesimal (ϕ j - algebraMap R (SemialgGerm R) (x j)) := by
        intro j r hr
        have hsq : (ϕ j - algebraMap R (SemialgGerm R) (x j)) ^ 2 < idGerm ^ 2 :=
          lt_of_le_of_lt (Finset.single_le_sum
            (f := fun i => (ϕ i - algebraMap R (SemialgGerm R) (x i)) ^ 2)
            (fun i _ => sq_nonneg _) (Finset.mem_univ j)) hϕball
        exact lt_trans (abs_lt_of_sq_lt_sq hsq (le_of_lt idGerm_pos)) (idGerm_lt_algebraMap hr)
      have hbϕ : ∀ j, ϕ j ∈ boundedGerms := fun j => mem_boundedGerms_of_infinitesimal (hinf j)
      have hlimϕ : ∀ j, limEps ⟨ϕ j, hbϕ j⟩ = x j := fun j =>
        limEps_eq_of_infinitesimal ⟨ϕ j, hbϕ j⟩ (x j) (hinf j)
      -- pull back: `ϕ = g'(ξ)` for some `ξ ∈ Ext S`.
      have himg : extension (R' := SemialgGerm R) (g '' S) hgS
          = {y' | ∃ x', Fin.append x' y' ∈ extension (R' := SemialgGerm R) (funGraph S g) hgf} := by
        rw [ext_congr hgS (IsSemialgebraicSet.exists_append_left hgf) (image_eq_proj_left S g),
          ext_exists_append_left hgf]
      rw [himg] at hϕext
      obtain ⟨ξ, hξ⟩ := hϕext
      rw [hgraph, append_mem_funGraph] at hξ
      obtain ⟨gϕ', hbnd', happ, hlimξS, hlimeq⟩ := lemma_3_21 S hS hScl hSb g hg ξ hξ.1
      rw [hgraph, append_mem_funGraph] at happ
      have hgϕ'_eq : gϕ' = ϕ := happ.2.trans hξ.2.symm
      -- conclude `g(lim_ε ξ) = x`.
      have hgx : g (fun i => limEps ⟨ξ i, ext_mem_boundedGerms hS hSb hξ.1 i⟩) = x := by
        funext j
        have e1 : limEps ⟨gϕ' j, hbnd' j⟩ = limEps ⟨ϕ j, hbϕ j⟩ := by
          congr 1; exact Subtype.ext (congrFun hgϕ'_eq j)
        rw [← hlimeq j, e1, hlimϕ j]
      exact ⟨_, hlimξS, hgx⟩
    exact isClosed_of_closure_subset hsub
  · -- `g(S)` is bounded.
    by_contra hub
    -- unboundedness: `‖g·‖²` is unbounded above on `S`.
    have hunb : ∀ N : R, ∃ x ∈ S, N < euclideanNormSq (g x) := by
      intro N
      rw [IsBoundedSet] at hub
      push Not at hub
      obtain ⟨y, hyim, hyout⟩ := Set.not_subset.mp (hub (|N| + 1) (by positivity))
      obtain ⟨xx, hxS, rfl⟩ := hyim
      rw [mem_closedBall, sub_zero] at hyout
      push Not at hyout
      exact ⟨xx, hxS, by nlinarith [hyout, le_abs_self N, abs_nonneg N]⟩
    -- the `R[ε]`-sentence `∃ (x, w) ∈ graph g, 1 < ε·‖w‖²`.
    obtain ⟨φG, hφGqf, hφG⟩ := semialgebraic_isQFRealizable (funGraph S g) hgf
    set Ψ : Formula (Fin (k + ℓ)) (OrderedFieldAtom (Fin (k + ℓ)) (Polynomial R)) :=
      (φG.mapCoeffO (D' := Polynomial R)).and
        (Formula.atom ⟨normPolyEps k ℓ R, OrderRel.gt⟩) with hΨ
    set Φ := Formula.existsList (List.finRange (k + ℓ)) Ψ with hΦ
    have hΦsent : Formula.isSentence Φ := isSentence_existsList_finRange Ψ
    have hreal : ∀ t : R, (Ψ.mapAtom (substAtom t)).realization (C := R)
        = funGraph S g ∩ {z | 1 < t * ∑ j : Fin ℓ, (z (Fin.natAdd k j)) ^ 2} := by
      intro t
      rw [hΨ]
      show ((φG.mapCoeffO).mapAtom (substAtom t)).realization (C := R)
          ∩ (Formula.atom (substAtom t ⟨normPolyEps k ℓ R, OrderRel.gt⟩)).realization (C := R) = _
      rw [mapCoeffO_mapAtom_substAtom, ← hφG]
      ext z
      rw [Set.mem_inter_iff, Set.mem_inter_iff]
      refine and_congr_right fun _ => ?_
      show 0 < aeval z ((normPolyEps k ℓ R).map (Polynomial.aeval t).toRingHom)
        ↔ z ∈ {z | 1 < t * ∑ j : Fin ℓ, (z (Fin.natAdd k j)) ^ 2}
      rw [aeval_substAtom_normPolyEps, Set.mem_setOf_eq]
      constructor <;> intro h <;> linarith
    -- discharge over `R`: for `t ∈ (0, 1)`, `‖g x‖² > 1/t` for some `x ∈ S`.
    have hRtrue : ∀ t : R, 0 < t → t < 1 → (Φ.mapAtom (substAtom t)).IsTrue (C := R) := by
      intro t ht _
      rw [hΦ, mapAtom_existsList, isTrue_existsList_finRange_iff, hreal t]
      obtain ⟨xx, hxS, hN⟩ := hunb (1 / t)
      refine ⟨Fin.append xx (g xx), by rw [append_mem_funGraph]; exact ⟨hxS, rfl⟩, ?_⟩
      rw [Set.mem_setOf_eq]
      have hsum : (∑ j : Fin ℓ, ((Fin.append xx (g xx)) (Fin.natAdd k j)) ^ 2)
          = euclideanNormSq (g xx) := by
        rw [euclideanNormSq]
        exact Finset.sum_congr rfl (fun j _ => by rw [Fin.append_right])
      rw [hsum, mul_comm]
      exact (div_lt_iff₀ ht).mp hN
    -- transfer to `R⟨ε⟩`.
    have hgermTrue : Φ.IsTrue (C := SemialgGerm R) :=
      (proposition_3_17 Φ hΦsent).mpr ⟨1, one_pos, hRtrue⟩
    rw [hΦ, isTrue_existsList_finRange_iff] at hgermTrue
    obtain ⟨z, hz⟩ := hgermTrue
    rw [hΨ, Formula.realization] at hz
    obtain ⟨hzG, hzN⟩ := hz
    rw [Formula.realization_mapCoeffO, ← ext_eq hgf hφG] at hzG
    have hzN' : 0 < aeval z (normPolyEps k ℓ R) := hzN
    rw [aeval_normPolyEps_germ] at hzN'
    -- decode `z = (ξ, g ∘ ξ)`.
    rw [hgraph, mem_funGraph] at hzG
    obtain ⟨gϕ, hbnd, happ, -, -⟩ := lemma_3_21 S hS hScl hSb g hg _ hzG.1
    rw [hgraph, append_mem_funGraph] at happ
    have hψ : (z ∘ Fin.natAdd k) = gϕ := hzG.2.trans happ.2.symm
    -- `g ∘ ξ` is bounded (Lemma 3.21), so `ε·‖g ∘ ξ‖² < 1`, contradiction.
    choose B hBpos hB using hbnd
    have hnormbound : euclideanNormSq gϕ < algebraMap R (SemialgGerm R) (∑ j, (B j) ^ 2) := by
      rw [euclideanNormSq, map_sum]
      refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => ?_)
      rw [map_pow]
      have hb := hB j
      rw [abs_lt] at hb
      nlinarith [hb.1, hb.2]
    set C := ∑ j : Fin ℓ, (B j) ^ 2 with hC_def
    have hC : 0 < C := Finset.sum_pos (fun j _ => pow_pos (hBpos j) 2) Finset.univ_nonempty
    have hCpos_germ : (0 : SemialgGerm R) < algebraMap R (SemialgGerm R) C := by
      rw [← map_zero (algebraMap R (SemialgGerm R))]; exact algebraMap_lt_algebraMap_of_lt hC
    have hkey : idGerm * euclideanNormSq gϕ < 1 := by
      have step1 : idGerm * euclideanNormSq gϕ < idGerm * algebraMap R (SemialgGerm R) C :=
        mul_lt_mul_of_pos_left hnormbound idGerm_pos
      have step2 : idGerm * algebraMap R (SemialgGerm R) C
          < algebraMap R (SemialgGerm R) (1 / (C + 1)) * algebraMap R (SemialgGerm R) C :=
        mul_lt_mul_of_pos_right (idGerm_lt_algebraMap (by positivity)) hCpos_germ
      have step3 : algebraMap R (SemialgGerm R) (1 / (C + 1)) * algebraMap R (SemialgGerm R) C
          = algebraMap R (SemialgGerm R) ((1 / (C + 1)) * C) := (map_mul _ _ _).symm
      have step4 : algebraMap R (SemialgGerm R) ((1 / (C + 1)) * C) < 1 := by
        rw [show (1 : SemialgGerm R) = algebraMap R (SemialgGerm R) 1 from (map_one _).symm]
        apply algebraMap_lt_algebraMap_of_lt
        rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
        linarith
      linarith [step1, step2, step3, step4]
    have hψeq : (∑ j : Fin ℓ, (z (Fin.natAdd k j)) ^ 2) = euclideanNormSq gϕ := by
      rw [euclideanNormSq]
      exact Finset.sum_congr rfl (fun j _ => by rw [show z (Fin.natAdd k j) = gϕ j from congrFun hψ j])
    rw [hψeq] at hzN'
    linarith [hkey, hzN']

end Azurite.BPR
