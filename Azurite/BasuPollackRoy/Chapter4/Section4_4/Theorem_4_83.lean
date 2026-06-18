import Azurite.BasuPollackRoy.Chapter4.Section4_4.QuantWeakNullstellensatz
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_78

/-!
# BPR Theorem 4.83: the quantitative Hilbert's Nullstellensatz

Let `𝒫 = {P₁, …, P_s} ⊂ K[X₁, …, X_k]` be a finite set of polynomials of degrees bounded by `d`
(with `K` of characteristic zero and `C` algebraically closed). If a polynomial `P` of degree
`≤ d` vanishes on the common zeros of `𝒫` in `C^k`, then there is `n` and polynomials `Bᵢ`, both `n`
and the degrees of the `Bᵢ` bounded by `(d+1)·(2(d+1))^{2^{k+1}}`, such that `Pⁿ = ∑ᵢ Bᵢ Pᵢ`.

The proof is the degree-tracking version of Theorem 4.78 (Rabinowitsch): the system
`𝒫 ∪ {X₀·P − 1}` in `k+1` variables, of degree `≤ d+1`, has no common zero, so the *quantitative*
weak Nullstellensatz (`quant_weak_nss`) yields `1 = A₀·(X₀ P − 1) + ∑ᵢ Aᵢ Pᵢ` with each `Aᵢ` of
total degree `≤ w := wBound (d+1) (k+1)`. Substituting `X₀ = 1/P` kills the first term; clearing
denominators by `P^w` turns each `Aᵢ(1/P, X)` into `ψ(Aᵢ) := ∑_{a≤w} (finSuccEquiv Aᵢ).coeff a · P^{w-a}`,
a genuine polynomial of degree `≤ w·(d+1)`, and gives `P^w = ∑ᵢ ψ(Aᵢ) Pᵢ`. The displayed bound
follows from `wBound_le : w ≤ (2(d+1))^{2^{k+1}}`.

BPR's stated bound `d·(2d)^{2^{k+1}}` is matched up to the `d → d+1` shift forced by the
Rabinowitsch variable `X₀`. BPR's hypothesis that there are *fewer than `d`* polynomials is not
needed: the bound depends only on the degree and the number of variables.

We single out `X₀` as the Rabinowitsch variable; the original variables `X₁, …, X_k` embed via
`rename Fin.succ`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {K : Type*} [Field K]

/-- **BPR Theorem 4.83 (Quantitative Hilbert's Nullstellensatz).** If `P` of degree `≤ d` vanishes
on `Zer(𝒫, C^k)` for a system `𝒫` of degree `≤ d`, then `P^n = ∑ B_Q · Q` with both `n` and the
degrees of the `B_Q` bounded by `(d+1)·(2(d+1))^{2^{k+1}}`. -/
theorem theorem_4_83 [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C] {k : ℕ}
    (d : ℕ) (Ps : Finset (MvPolynomial (Fin k) K)) (P : MvPolynomial (Fin k) K)
    (hPs : ∀ Q ∈ Ps, Q.totalDegree ≤ d) (hPd : P.totalDegree ≤ d)
    (hvanish : ∀ x ∈ zerOfFinset C Ps, MvPolynomial.aeval x P = 0) :
    ∃ (n : ℕ) (B : MvPolynomial (Fin k) K → MvPolynomial (Fin k) K),
      n ≤ (2 * (d + 1)) ^ (2 ^ (k + 1)) ∧
        (∀ Q ∈ Ps, (B Q).totalDegree ≤ (d + 1) * (2 * (d + 1)) ^ (2 ^ (k + 1))) ∧
          P ^ n = ∑ Q ∈ Ps, B Q * Q := by
  classical
  set bound : ℕ := (d + 1) * (2 * (d + 1)) ^ (2 ^ (k + 1)) with hbound
  by_cases hP0 : P = 0
  · -- Edge case `P = 0`.
    refine ⟨1, fun _ => 0, ?_, fun Q _ => ?_, ?_⟩
    · -- `1 ≤ (2(d+1))^(2^(k+1))`
      exact Nat.one_le_pow _ _ (by positivity)
    · rw [totalDegree_zero]; exact Nat.zero_le _
    · rw [hP0, pow_one, Finset.sum_eq_zero]
      intro Q _; rw [zero_mul]
  -- Main case `P ≠ 0`.
  let R := MvPolynomial (Fin k) K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  have hφinj : Function.Injective φ := IsFractionRing.injective R F
  have hPne : φ P ≠ 0 := fun h => hP0 (hφinj (h.trans (map_zero φ).symm))
  set w : ℕ := wBound (d + 1) (k + 1) with hw
  -- Step 1: Rabinowitsch set.
  let ι : R →ₐ[K] MvPolynomial (Fin (k + 1)) K := rename Fin.succ
  have hι : ι = rename Fin.succ := rfl
  let Ps' : Finset (MvPolynomial (Fin (k + 1)) K) :=
    insert (X 0 * ι P - 1) (Ps.image ι)
  have hPs' : Ps' = insert (X 0 * ι P - 1) (Ps.image ι) := rfl
  -- Step 2: degree bound on members of `Ps'`.
  have hdegι : ∀ q : R, (ι q).totalDegree ≤ q.totalDegree := by
    intro q; rw [hι]; exact MvPolynomial.totalDegree_rename_le _ _
  have hdeg' : ∀ R' ∈ Ps'.toList, R'.totalDegree ≤ d + 1 := by
    intro R' hR'
    rw [Finset.mem_toList, hPs', Finset.mem_insert] at hR'
    rcases hR' with rfl | himg
    · -- `X 0 * ι P - 1`
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      rw [totalDegree_one, Nat.max_zero]
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have hX0 : (X 0 : MvPolynomial (Fin (k + 1)) K).totalDegree = 1 := totalDegree_X 0
      rw [hX0]
      have : (ι P).totalDegree ≤ d := le_trans (hdegι P) hPd
      omega
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp himg
      exact le_trans (hdegι q) (le_trans (hPs q hq) (Nat.le_succ d))
  -- Step 3: no common zero (copied from Theorem 4.78).
  have hzer : zerOfFinset C Ps' = ∅ := by
    ext y
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hy
    have hyP : aeval y (ι P) = 0 := by
      have htail : (y ∘ Fin.succ) ∈ zerOfFinset C Ps := by
        intro q hq
        have : aeval y (ι q) = 0 := hy (ι q) (by
          rw [hPs']; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq))
        rwa [hι, aeval_rename] at this
      have := hvanish _ htail
      rw [hι, aeval_rename]
      exact this
    have hmem0 : aeval y (X 0 * ι P - 1) = 0 :=
      hy _ (by rw [hPs']; exact Finset.mem_insert_self _ _)
    rw [map_sub, map_mul, aeval_X, hyP, mul_zero, map_one, zero_sub] at hmem0
    exact one_ne_zero (neg_eq_zero.mp hmem0)
  -- Step 4: quantitative weak Nullstellensatz.
  have hzerList : zerOfFinset C Ps'.toList.toFinset = ∅ := by
    rw [Finset.toList_toFinset]; exact hzer
  obtain ⟨A, hAdeg, hA⟩ :=
    quant_weak_nss (C := C) (k + 1) (d + 1) Ps'.toList hdeg' hzerList
  rw [Finset.toList_toFinset] at hA
  rw [← hw] at hAdeg
  -- Step 5: substitution g (copied from Theorem 4.78).
  let g : Fin (k + 1) → F := Fin.cons (φ P)⁻¹ (fun i => φ (X i))
  have hg0 : g 0 = (φ P)⁻¹ := Fin.cons_zero _ _
  have hgs : ∀ i : Fin k, g i.succ = φ (X i) := fun i => Fin.cons_succ _ _ i
  have aeval_g_rename : ∀ q : R, aeval g (ι q) = φ q := by
    intro q
    rw [hι, aeval_rename]
    have hcomp : g ∘ Fin.succ = fun i => φ (X i) := by
      funext i; simp only [Function.comp_apply]; exact hgs i
    rw [hcomp]
    have : (aeval (fun i => φ (X i)) : R →ₐ[K] F).toRingHom = φ := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
        rw [IsScalarTower.algebraMap_apply K R F a, MvPolynomial.algebraMap_eq]
      · intro i
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    calc aeval (fun i => φ (X i)) q
        = (aeval (fun i => φ (X i)) : R →ₐ[K] F).toRingHom q := rfl
      _ = φ q := by rw [this]
  -- Apply aeval g to hA.
  have hAg0 : ∑ p ∈ Ps', aeval g (A p) * aeval g p = 1 := by
    have := congrArg (aeval g) hA
    rw [map_sum, map_one] at this
    simp only [map_mul] at this
    exact this
  have hins : aeval g (X 0 * ι P - 1) = 0 := by
    rw [map_sub, map_mul, aeval_X, hg0, map_one, aeval_g_rename P]
    rw [inv_mul_cancel₀ hPne, sub_self]
  have hnotmem : (X 0 * ι P - 1) ∉ Ps.image ι := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨q, _, hq⟩ := hmem
    have eval_rename : ∀ (c : K) (r : R),
        (aeval (Fin.cons (MvPolynomial.C c) (fun i => (X i : R)))) (ι r) = r := by
      intro c r
      rw [hι, aeval_rename]
      have : (Fin.cons (MvPolynomial.C c) (fun i => (X i : R))) ∘ Fin.succ
          = fun i => (X i : R) := by funext i; simp [Fin.cons_succ]
      rw [this]
      exact aeval_X_left_apply r
    have h0 := congrArg (aeval (Fin.cons (MvPolynomial.C (0 : K)) (fun i => (X i : R)))) hq
    rw [eval_rename 0 q, map_sub, map_mul, aeval_X, eval_rename 0 P, Fin.cons_zero,
      map_one, map_zero, zero_mul, zero_sub] at h0
    have h1 := congrArg (aeval (Fin.cons (MvPolynomial.C (1 : K)) (fun i => (X i : R)))) hq
    rw [eval_rename 1 q, map_sub, map_mul, aeval_X, eval_rename 1 P, Fin.cons_zero,
      map_one, one_mul, map_one] at h1
    apply hP0
    linear_combination h0 - h1
  rw [hPs', Finset.sum_insert hnotmem] at hAg0
  rw [hins, mul_zero, zero_add] at hAg0
  rw [Finset.sum_image (fun a _ b _ h => rename_injective _ (Fin.succ_injective k) h)] at hAg0
  rw [← hι] at hAg0
  simp only [aeval_g_rename] at hAg0
  -- Now `hAg0 : ∑ q ∈ Ps, aeval g (A (ι q)) * φ q = 1`.
  -- Step 6: explicit cleared coefficient `ψ`.
  let ψ : MvPolynomial (Fin (k + 1)) K → R :=
    fun Q => ∑ a ∈ Finset.range (w + 1), (finSuccEquiv K k Q).coeff a * P ^ (w - a)
  -- (degree)
  have hψdeg : ∀ Q : MvPolynomial (Fin (k + 1)) K, Q.totalDegree ≤ w →
      (ψ Q).totalDegree ≤ w * (d + 1) := by
    intro Q hQ
    refine MvPolynomial.totalDegree_finsetSum_le (fun a ha => ?_)
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have hca : ((finSuccEquiv K k Q).coeff a).totalDegree ≤ w - a := by
      by_cases hz : (finSuccEquiv K k Q).coeff a = 0
      · rw [hz, totalDegree_zero]; exact Nat.zero_le _
      · have := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le Q a hz
        omega
    have hpw : (P ^ (w - a)).totalDegree ≤ (w - a) * d :=
      le_trans (MvPolynomial.totalDegree_pow P (w - a))
        (Nat.mul_le_mul_left _ hPd)
    have ha' : a ≤ w := by rw [Finset.mem_range] at ha; omega
    calc ((finSuccEquiv K k Q).coeff a).totalDegree + (P ^ (w - a)).totalDegree
        ≤ (w - a) + (w - a) * d := Nat.add_le_add hca hpw
      _ = (w - a) * (d + 1) := by ring
      _ ≤ w * (d + 1) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  -- (value)
  have hψval : ∀ Q : MvPolynomial (Fin (k + 1)) K, Q.totalDegree ≤ w →
      φ (ψ Q) = φ P ^ w * aeval g Q := by
    intro Q hQ
    -- `aeval g Q = ∑ a ∈ range (w+1), φ ((finSuccEquiv K k Q).coeff a) * (φ P)⁻¹ ^ a`.
    have hnd : (finSuccEquiv K k Q).natDegree < w + 1 := by
      rw [MvPolynomial.natDegree_finSuccEquiv]
      have : Q.degreeOf 0 ≤ Q.totalDegree := MvPolynomial.degreeOf_le_totalDegree Q 0
      omega
    have hcomp : ∀ Q' : MvPolynomial (Fin (k + 1)) K, aeval g Q'
        = Polynomial.aeval (φ P)⁻¹ (Polynomial.map φ (finSuccEquiv K k Q')) := by
      intro Q'
      induction Q' using MvPolynomial.induction_on with
      | C c =>
          rw [aeval_C,
            show (MvPolynomial.finSuccEquiv K k) (MvPolynomial.C c)
              = Polynomial.C (MvPolynomial.C c) by simp [finSuccEquiv_apply, eval₂Hom_C],
            Polynomial.map_C, Polynomial.aeval_C, Algebra.algebraMap_self_apply,
            IsScalarTower.algebraMap_apply K R F c, MvPolynomial.algebraMap_eq]
      | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
      | mul_X p j hp =>
          rw [map_mul, map_mul, Polynomial.map_mul, map_mul, hp, aeval_X]
          congr 1
          refine j.cases ?_ ?_
          · rw [finSuccEquiv_X_zero, Polynomial.map_X, Polynomial.aeval_X, hg0]
          · intro i
            rw [finSuccEquiv_X_succ, Polynomial.map_C, Polynomial.aeval_C, hgs i,
              Algebra.algebraMap_self_apply]
    rw [hcomp Q]
    -- expand via aeval_eq_sum_range'
    have hndmap : (Polynomial.map φ (finSuccEquiv K k Q)).natDegree < w + 1 := by
      refine lt_of_le_of_lt (Polynomial.natDegree_map_le) hnd
    rw [Polynomial.aeval_eq_sum_range' hndmap]
    -- LHS: φ (∑ ...) = ∑ φ (...)
    rw [show ψ Q = ∑ a ∈ Finset.range (w + 1), (finSuccEquiv K k Q).coeff a * P ^ (w - a) from rfl,
      map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_range] at ha
    have ha' : a ≤ w := by omega
    rw [Polynomial.coeff_map, map_mul, map_pow, smul_eq_mul]
    -- goal: φ (coeff a) * φ P ^ (w - a) = φ P ^ w * (φ (coeff a) * (φ P)⁻¹ ^ a)
    have hpe : φ P ^ w * (φ P)⁻¹ ^ a = φ P ^ (w - a) := by
      rw [inv_pow, ← pow_sub₀ _ hPne ha']
    calc φ ((finSuccEquiv K k Q).coeff a) * φ P ^ (w - a)
        = φ ((finSuccEquiv K k Q).coeff a) * (φ P ^ w * (φ P)⁻¹ ^ a) := by rw [hpe]
      _ = φ P ^ w * (φ ((finSuccEquiv K k Q).coeff a) * (φ P)⁻¹ ^ a) := by ring
  -- Step 7: assemble.
  have hAιdeg : ∀ q ∈ Ps, (A (ι q)).totalDegree ≤ w := by
    intro q hq
    apply hAdeg
    rw [Finset.mem_toList, hPs']
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq)
  -- Multiply hAg0 by φ P ^ w.
  have key : φ (P ^ w) = φ (∑ q ∈ Ps, ψ (A (ι q)) * q) := by
    rw [map_pow, map_sum]
    have hstart : φ P ^ w = φ P ^ w * 1 := (mul_one _).symm
    rw [hstart, ← hAg0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [map_mul]
    rw [show φ P ^ w * (aeval g (A (ι q)) * φ q)
        = (φ P ^ w * aeval g (A (ι q))) * φ q by ring]
    rw [← hψval (A (ι q)) (hAιdeg q hq)]
  have hReq : P ^ w = ∑ q ∈ Ps, ψ (A (ι q)) * q := hφinj key
  -- Bounds.
  have hdp1 : 1 ≤ d + 1 := Nat.succ_pos d
  have hwle : w ≤ (2 * (d + 1)) ^ (2 ^ (k + 1)) := by
    rw [hw]; exact wBound_le (d + 1) (k + 1)
  refine ⟨w, fun q => ψ (A (ι q)), ?_, ?_, ?_⟩
  · -- n = w ≤ (2(d+1))^(2^(k+1))
    exact hwle
  · -- degrees
    intro Q hQ
    refine le_trans (hψdeg (A (ι Q)) (hAιdeg Q hQ)) ?_
    rw [hbound, Nat.mul_comm w (d + 1)]
    exact Nat.mul_le_mul_left _ hwle
  · exact hReq

end Azurite.BPR.Chapter4
