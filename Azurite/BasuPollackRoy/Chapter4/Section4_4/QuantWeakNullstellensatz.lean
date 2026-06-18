import Azurite.BasuPollackRoy.Chapter4.Section4_4.ResultantDegree
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Proposition_4_77
import Azurite.BasuPollackRoy.Chapter4.Section4_4.QuantitativeBound

/-!
# BPR §4.4.2: the quantitative weak Nullstellensatz

If a finite system `𝒫 ⊆ K[X₁, …, X_m]` of polynomials of degree `≤ d` has no common zero in `C^m`
(with `K` of characteristic zero and `C` algebraically closed), then `1 = ∑ Aᵢ Pᵢ` with all `Aᵢ`
of total degree `≤ wBound d m ≤ (2d)^{2^m}`.

The proof is the degree-tracking version of Proposition 4.77's empty-zero-set case, by induction on
`m`: a linear shear (`exists_linear_shear`, degree-preserving) makes one polynomial quasi-monic;
the resultant projection (Proposition 4.76) yields `Proj` in `m-1` variables of degree `≤ 2d²` with
empty zero set; the induction hypothesis gives a combination of degree `≤ wBound (2d²) (m-1)`; and
the per-step lift (`quant_proj_mem`) re-expresses it over `𝒫` adding `≤ 3d²` to the degree, so
`wBound (2d²) (m-1) + 3d² = wBound d m`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {K : Type*} [Field K]

/-- If every member of a finset `T` is the zero polynomial, then `Zer(T) = univ`. -/
private theorem zerOfFinset_eq_univ_of_forall_zero' {C : Type*} [CommRing C] [Algebra K C] {k : ℕ}
    {T : Finset (MvPolynomial (Fin k) K)} (h : ∀ p ∈ T, p = 0) :
    zerOfFinset C T = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x p hp
  rw [h p hp]; simp

/-- `embedX0 P` has the same `X₀`-degree as `finSuccEquiv K m P` (inline bridge). -/
private theorem natDegree_embedX0' {m : ℕ} (P : MvPolynomial (Fin (m + 1)) K) :
    (embedX0 P).natDegree = (finSuccEquiv K m P).natDegree := by
  unfold embedX0
  exact Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective (finSuccEquiv K m P)

/-- **BPR (quantitative weak Nullstellensatz).** A degree-`≤ d` system in `m` variables with no
common zero over an algebraically closed `C` admits `1 = ∑ Aᵢ Pᵢ` with `deg Aᵢ ≤ wBound d m`. -/
theorem quant_weak_nss [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C] :
    ∀ (m d : ℕ) (Ps : List (MvPolynomial (Fin m) K)), (∀ P ∈ Ps, P.totalDegree ≤ d) →
      zerOfFinset C Ps.toFinset = ∅ →
      ∃ A : MvPolynomial (Fin m) K → MvPolynomial (Fin m) K,
        (∀ P ∈ Ps, (A P).totalDegree ≤ wBound d m) ∧ ∑ P ∈ Ps.toFinset, A P * P = 1 := by
  classical
  intro m
  induction m with
  | zero =>
    intro d Ps hdeg hempty
    -- Over `Fin 0`, the unique point lies in `Zer(Ps)` unless some `P₁ = C c` with `c ≠ 0`.
    -- If every `P` evaluated at the unique point is `0`, the point is a common zero.
    have hpt : ∃ P₁ ∈ Ps, (aeval (fun _ => 0 : Fin 0 → C)) P₁ ≠ 0 := by
      by_contra h
      push Not at h
      have : (fun _ => 0 : Fin 0 → C) ∈ zerOfFinset C Ps.toFinset := by
        intro p hp
        exact h p (List.mem_toFinset.mp hp)
      rw [hempty] at this
      exact this
    obtain ⟨P₁, hP₁mem, hP₁0⟩ := hpt
    -- `P₁ = C c` for `c = e P₁`, and `c ≠ 0`.
    set c : K := MvPolynomial.isEmptyAlgEquiv K (Fin 0) P₁ with hc
    have hP₁C : P₁ = MvPolynomial.C c := by
      conv_lhs => rw [← AlgEquiv.symm_apply_apply (MvPolynomial.isEmptyAlgEquiv K (Fin 0)) P₁]
      simp [MvPolynomial.isEmptyAlgEquiv, hc]
    have hcne : c ≠ 0 := by
      intro h0
      apply hP₁0
      rw [hP₁C, h0, map_zero, map_zero]
    refine ⟨fun q => if q = P₁ then MvPolynomial.C c⁻¹ else 0, ?_, ?_⟩
    · intro P hP
      rw [wBound_zero]
      simp only
      split
      · rw [MvPolynomial.totalDegree_C]
      · simp
    · rw [Finset.sum_eq_single P₁]
      · show (if P₁ = P₁ then MvPolynomial.C c⁻¹ else 0) * P₁ = 1
        rw [if_pos rfl, hP₁C, ← map_mul, inv_mul_cancel₀ hcne, map_one]
      · intro q _ hq
        show (if q = P₁ then MvPolynomial.C c⁻¹ else 0) * q = 0
        rw [if_neg hq, zero_mul]
      · intro h
        exact absurd (List.mem_toFinset.mpr hP₁mem) h
  | succ m IH =>
    intro d Ps hdeg hempty
    -- Step 1: find a nonzero `P₁ ∈ Ps`.
    have hP₁exists : ∃ P₁ ∈ Ps, P₁ ≠ 0 := by
      by_contra h
      push Not at h
      have huniv : zerOfFinset C Ps.toFinset = Set.univ := by
        apply zerOfFinset_eq_univ_of_forall_zero'
        intro p hp
        exact h p (List.mem_toFinset.mp hp)
      rw [hempty] at huniv
      exact absurd huniv.symm (by simp [Set.eq_empty_iff_forall_notMem])
    obtain ⟨P₁, hP₁mem, hP₁0⟩ := hP₁exists
    -- Step 2: linear shear making `P₁` quasi-monic.
    obtain ⟨a, hlin, hqm⟩ := exists_linear_shear Ps.toFinset
    set w : MvPolynomial (Fin (m + 1)) K ≃ₐ[K] _ := shearEquiv a with hw
    have hqm₁ : IsQuasiMonic (finSuccEquiv K m (shearHom a P₁)) :=
      hqm P₁ (List.mem_toFinset.mpr hP₁mem) hP₁0
    -- Step 3: sheared system.
    set Q₁ : MvPolynomial (Fin (m + 1)) K := shearHom a P₁ with hQ₁
    set restList : List (MvPolynomial (Fin (m + 1)) K) :=
      (Ps.toFinset.erase P₁).toList.map (shearHom a) with hrestList
    -- `insert Q₁ restList.toFinset = Ps.toFinset.image w` (`w = shearEquiv a`).
    have htfmap : restList.toFinset = (Ps.toFinset.erase P₁).image (shearHom a) := by
      rw [hrestList]; ext z; simp
    have hwins : insert Q₁ restList.toFinset = Ps.toFinset.image w := by
      rw [htfmap, hQ₁,
        show (Ps.toFinset.image w) = Ps.toFinset.image (shearHom a) by
          apply Finset.image_congr; intro z _; rw [hw, shearEquiv_apply],
        ← Finset.image_insert, Finset.insert_erase (List.mem_toFinset.mpr hP₁mem)]
    -- Degree bounds.
    have hdeg_Q₁ : Q₁.totalDegree ≤ d :=
      le_trans (totalDegree_shearHom_le a P₁) (hdeg P₁ hP₁mem)
    have hdeg_rest : ∀ Q ∈ restList, Q.totalDegree ≤ d := by
      intro Q hQ
      rw [hrestList, List.mem_map] at hQ
      obtain ⟨P, hP, rfl⟩ := hQ
      rw [Finset.mem_toList, Finset.mem_erase, List.mem_toFinset] at hP
      exact le_trans (totalDegree_shearHom_le a P) (hdeg P hP.2)
    -- Step 4: empty zero set transfers to the sheared system.
    have hwempty : zerOfFinset C (insert Q₁ restList.toFinset) = ∅ := by
      rw [hwins, Set.eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_zerOfFinset_image_equiv, hempty] at hx
      exact hx
    -- Step 5: split on whether `Q₁` has positive `X₀`-degree.
    by_cases hpos : 0 < (finSuccEquiv K m Q₁).natDegree
    · -- Step 6: empty zero set of `projPolys`.
      have hprojempty : zerOfFinset C (projPolys Q₁ restList) = ∅ := by
        rw [← clause_two hqm₁ hpos, hwempty, Set.image_empty]
      -- Step 7: projPolys members have totalDegree `≤ 2 d²`.
      have hcoeff := coeffTotalDegreeLE_resXk d Q₁ restList hdeg_Q₁ hdeg_rest
      have hprojdeg : ∀ Q ∈ projPolys Q₁ restList, Q.totalDegree ≤ 2 * d ^ 2 := by
        intro Q hQ
        unfold projPolys at hQ
        rw [Finset.mem_insert] at hQ
        rcases hQ with rfl | hQimg
        · simp
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hQimg
          exact hcoeff j
      -- Step 8: apply IH.
      have hprojdegList : ∀ Q ∈ (projPolys Q₁ restList).toList, Q.totalDegree ≤ 2 * d ^ 2 := by
        intro Q hQ
        exact hprojdeg Q (Finset.mem_toList.mp hQ)
      have hprojemptyList :
          zerOfFinset C (projPolys Q₁ restList).toList.toFinset = ∅ := by
        rw [Finset.toList_toFinset]; exact hprojempty
      obtain ⟨A', hA'deg, hA'sum⟩ :=
        IH (2 * d ^ 2) (projPolys Q₁ restList).toList hprojdegList hprojemptyList
      rw [Finset.toList_toFinset] at hA'sum
      -- Step 9: per-`Q` lift via `quant_proj_mem`.
      have hdeg9 : (embedX0 Q₁).natDegree ≠ 0 ∨ (Rbar restList).natDegree ≠ 0 := by
        left
        rw [natDegree_embedX0']
        omega
      have hlift : ∀ Q ∈ projPolys Q₁ restList,
          ∃ B : MvPolynomial (Fin (m + 1)) K → MvPolynomial (Fin (m + 1)) K,
            (∀ P ∈ insert Q₁ restList.toFinset, (B P).totalDegree ≤ 3 * d ^ 2) ∧
              ∑ P ∈ insert Q₁ restList.toFinset, B P * P = rename Fin.succ Q :=
        fun Q hQ => quant_proj_mem d hdeg_Q₁ hdeg_rest hdeg9 hQ
      choose B hBdeg hBsum using hlift
      -- Step 10: regroup.
      -- Apply `rename Fin.succ` to `∑ Q, A' Q * Q = 1`.
      have hrenamed : ∑ Q ∈ projPolys Q₁ restList,
          (rename Fin.succ (A' Q)) * (rename Fin.succ Q) = 1 := by
        have := congrArg (rename (R := K) Fin.succ) hA'sum
        rw [map_sum, map_one] at this
        rw [← this]
        apply Finset.sum_congr rfl
        intro Q _
        rw [map_mul]
      -- Substitute the lift for each `rename Fin.succ Q`.
      set Cf : MvPolynomial (Fin (m + 1)) K → MvPolynomial (Fin (m + 1)) K :=
        fun P => ∑ Q ∈ (projPolys Q₁ restList).attach,
          (rename Fin.succ (A' Q.1)) * B Q.1 Q.2 P with hCf
      have hsum : ∑ P ∈ insert Q₁ restList.toFinset, Cf P * P = 1 := by
        rw [← hrenamed,
          ← Finset.sum_attach (projPolys Q₁ restList)
            (fun Q => (rename Fin.succ (A' Q)) * (rename Fin.succ Q))]
        -- Replace `rename Fin.succ Q.1` by the lifted sum.
        have hstep : ∀ Q ∈ (projPolys Q₁ restList).attach,
            (rename Fin.succ (A' Q.1)) * (rename Fin.succ Q.1)
            = ∑ P ∈ insert Q₁ restList.toFinset,
                (rename Fin.succ (A' Q.1)) * B Q.1 Q.2 P * P := by
          intro Q _
          rw [← hBsum Q.1 Q.2, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro P _; ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro P _
        rw [hCf, Finset.sum_mul]
      have hCfdeg : ∀ P ∈ insert Q₁ restList.toFinset, (Cf P).totalDegree ≤ wBound d (m + 1) := by
        intro P hP
        rw [hCf, wBound_succ]
        refine MvPolynomial.totalDegree_finsetSum_le (fun Q _ => ?_)
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        have h1 : (rename Fin.succ (A' Q.1)).totalDegree ≤ wBound (2 * d ^ 2) m := by
          refine le_trans (MvPolynomial.totalDegree_rename_le _ _) ?_
          exact hA'deg Q.1 (Finset.mem_toList.mpr Q.2)
        have h2 : (B Q.1 Q.2 P).totalDegree ≤ 3 * d ^ 2 := hBdeg Q.1 Q.2 P hP
        omega
      -- Step 11: undo the shear.
      -- We have `∑ P ∈ insert Q₁ restList.toFinset, Cf P * P = 1`.
      -- Apply `shearHom (-a)` to both sides and reindex back to `Ps`.
      have hcancel : ∀ P₀ : MvPolynomial (Fin (m + 1)) K,
          shearHom (fun i => -a i) (shearHom a P₀) = P₀ := by
        intro P₀
        rw [show shearHom (fun i => -a i) (shearHom a P₀) = w.symm (w P₀) from rfl,
          AlgEquiv.symm_apply_apply]
      have hwP₀ : ∀ P₀ : MvPolynomial (Fin (m + 1)) K, w P₀ = shearHom a P₀ := by
        intro P₀; rw [hw, shearEquiv_apply]
      refine ⟨fun P₀ => shearHom (fun i => -a i) (Cf (shearHom a P₀)), ?_, ?_⟩
      · intro P₀ hP₀
        refine le_trans (totalDegree_shearHom_le _ _) ?_
        apply hCfdeg
        rw [hwins, ← hwP₀ P₀]
        exact Finset.mem_image_of_mem w (List.mem_toFinset.mpr hP₀)
      · -- The sum identity over `Ps`.
        have hsheared := congrArg (shearHom (fun i => -a i)) hsum
        rw [map_one, map_sum] at hsheared
        rw [← hsheared, hwins,
          Finset.sum_image (fun P _ P' _ heq => w.injective heq)]
        apply Finset.sum_congr rfl
        intro P₀ _
        rw [map_mul, hwP₀ P₀, hcancel P₀]
    · -- Step 5 constant case: `Q₁ = C c`, `c ≠ 0`, so `P₁ = C c`.
      push Not at hpos
      have h0 : (finSuccEquiv K m Q₁).natDegree = 0 := Nat.le_zero.mp hpos
      obtain ⟨c₀, hc₀⟩ := hqm₁.2
      have hc₀ne : c₀ ≠ 0 := hqm₁.leadingCoeff_const_ne_zero c₀ hc₀
      -- `Q₁ = C c₀`.
      have hQ₁C : Q₁ = MvPolynomial.C c₀ := by
        apply (finSuccEquiv K m).injective
        have hrhs : finSuccEquiv K m (MvPolynomial.C c₀) = Polynomial.C (MvPolynomial.C c₀) := by
          simp [finSuccEquiv_apply]
        have hcoeff0 : (finSuccEquiv K m Q₁).coeff 0 = MvPolynomial.C c₀ := by
          rw [show (0 : ℕ) = (finSuccEquiv K m Q₁).natDegree from h0.symm,
            ← Polynomial.leadingCoeff, hc₀]
        rw [hrhs, Polynomial.eq_C_of_natDegree_eq_zero h0, hcoeff0]
      -- `P₁ = C c₀`: `shearHom` fixes constants and `Q₁ = shearHom a P₁`.
      have hshearC : shearHom a (MvPolynomial.C c₀) = MvPolynomial.C c₀ := by
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq]
      have hP₁C : P₁ = MvPolynomial.C c₀ := by
        have heq : shearHom a P₁ = shearHom a (MvPolynomial.C c₀) := by
          rw [hshearC, ← hQ₁]; exact hQ₁C
        have hinj : Function.Injective (shearHom a) := by
          intro p q hpq; exact w.injective (by rw [hw, shearEquiv_apply, shearEquiv_apply]; exact hpq)
        exact hinj heq
      refine ⟨fun q => if q = P₁ then MvPolynomial.C c₀⁻¹ else 0, ?_, ?_⟩
      · intro P hP
        simp only
        split
        · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
        · simp
      · rw [Finset.sum_eq_single P₁]
        · show (if P₁ = P₁ then MvPolynomial.C c₀⁻¹ else 0) * P₁ = 1
          rw [if_pos rfl, hP₁C, ← map_mul, inv_mul_cancel₀ hc₀ne, map_one]
        · intro q _ hq
          show (if q = P₁ then MvPolynomial.C c₀⁻¹ else 0) * q = 0
          rw [if_neg hq, zero_mul]
        · intro h
          exact absurd (List.mem_toFinset.mpr hP₁mem) h

end Azurite.BPR.Chapter4
