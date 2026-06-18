import Azurite.BasuPollackRoy.Chapter4.Section4_4.Definition_4_73
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Lemma_4_75
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# BPR Lemma 4.74

Let `𝒫 ⊆ K[X₁, …, X_k]` be a finite subset (over a field of characteristic zero, as the proof
uses Lemma 4.75). Then there is a linear automorphism `v : K^k → K^k` such that for all `P ∈ 𝒫`,
the polynomial `P(v(X))` is quasi-monic in `X_k`.

We single out the variable `X₀` (Mathlib's `finSuccEquiv` distinguishes the first variable) and
use the shear `v : X₀ ↦ X₀`, `X_{i+1} ↦ X_{i+1} + a_i X₀`. Writing `P = Π + ⋯` with `Π` the
top homogeneous part (degree `d`), one has `P(v(X)) = Π(1, a₁, …, a_n) X₀^d + (lower in X₀)`, so
it suffices to choose `a` with `Π(1, a) ≠ 0` for each `P`; this is possible by Lemma 4.75 applied
to the product of the (nonzero) dehomogenized top parts.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {n : ℕ} {K : Type*} [Field K]

/-- The shear substitution `X₀ ↦ X₀`, `X_{i+1} ↦ X_{i+1} + a_i X₀`. -/
noncomputable def shearMap (a : Fin n → K) : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K :=
  Fin.cases (X 0) (fun i => X i.succ + C (a i) * X 0)

/-- The shear as an algebra homomorphism `P ↦ P(v(X))`. -/
noncomputable def shearHom (a : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  aeval (shearMap a)

@[simp] theorem shearMap_zero (a : Fin n → K) : shearMap a 0 = X 0 := by
  simp [shearMap]

@[simp] theorem shearMap_succ (a : Fin n → K) (i : Fin n) :
    shearMap a i.succ = X i.succ + C (a i) * X 0 := by
  simp [shearMap]

/-- The two shears `a` and `-a` are mutually inverse. -/
theorem shearHom_comp_neg (a : Fin n → K) :
    (shearHom a).comp (shearHom (fun i => -a i)) = AlgHom.id K _ := by
  rw [shearHom, shearHom, comp_aeval, ← MvPolynomial.aeval_X_left]
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [shearMap]
  | succ j => simp [shearMap]

/-- The shear is a linear automorphism of `K[X₀, …, X_n]`. -/
noncomputable def shearEquiv (a : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  AlgEquiv.ofAlgHom (shearHom a) (shearHom (fun i => -a i)) (shearHom_comp_neg a)
    (by simpa using shearHom_comp_neg (fun i => -a i))

@[simp] theorem shearEquiv_apply (a : Fin n → K) (P : MvPolynomial (Fin (n + 1)) K) :
    shearEquiv a P = shearHom a P := rfl

/-- The dehomogenized top part `Π(1, X₁, …, X_n)` of `P`, a polynomial in the remaining
variables. -/
noncomputable def topForm (P : MvPolynomial (Fin (n + 1)) K) : MvPolynomial (Fin n) K :=
  aeval (Fin.cons 1 (fun i => X i)) (homogeneousComponent P.totalDegree P)

/-- The dehomogenization map `X₀ ↦ 1`, `X_{i+1} ↦ X_i`, applied to a monomial, drops the
`X₀`-exponent: it maps `X^α ↦ X^(tail α)`. -/
private theorem dehom_monomial (c : K) (α : Fin (n + 1) →₀ ℕ) :
    aeval (Fin.cons (1 : MvPolynomial (Fin n) K) (fun i => X i)) (monomial α c) =
      monomial (α.comapDomain Fin.succ (Fin.succ_injective n).injOn) c := by
  rw [aeval_monomial]
  simp only [MvPolynomial.algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, one_pow, one_mul]
  rw [MvPolynomial.monomial_eq]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finsupp.comapDomain_apply]

/-- Lemma B: the dehomogenized top part of a nonzero polynomial is nonzero. -/
theorem topForm_ne_zero {P : MvPolynomial (Fin (n + 1)) K} (hP : P ≠ 0) : topForm P ≠ 0 := by
  classical
  set d := P.totalDegree with hd
  set H := homogeneousComponent d P with hH
  -- `H` is nonzero: a support element of `P` of maximal degree `d` lies in `H`'s support.
  obtain ⟨α₀, hα0mem, hα0deg⟩ :=
    Finset.exists_mem_eq_sup P.support (MvPolynomial.support_nonempty.mpr hP)
      (fun s => s.sum fun _ e => e)
  have hα0H : α₀ ∈ H.support := by
    rw [hH, support_homogeneousComponent]
    rw [Finset.mem_filter]
    refine ⟨hα0mem, ?_⟩
    show (α₀.sum fun _ e => e) = d
    rw [← hα0deg, hd, totalDegree]
  -- The top form is the image of `H` under dehomogenization.
  have hsum : topForm P = ∑ α ∈ H.support, monomial (α.comapDomain Fin.succ
      (Fin.succ_injective n).injOn) (coeff α H) := by
    rw [topForm, ← hd, ← hH]
    conv_lhs => rw [H.as_sum, map_sum]
    exact Finset.sum_congr rfl (fun α _ => dehom_monomial _ _)
  -- All support elements of `H` have degree `d`.
  have hdeg : ∀ α ∈ H.support, (α.sum fun _ e => e) = d := by
    intro α hα
    rw [hH, support_homogeneousComponent, Finset.mem_filter] at hα
    rw [← hα.2, Finsupp.degree_apply]
    rfl
  -- The tail map is injective on `H.support`, so the coefficient at `tail α₀` is `coeff α₀ H ≠ 0`.
  set β := α₀.comapDomain Fin.succ (Fin.succ_injective n).injOn with hβ
  refine fun hzero => (mem_support_iff.mp hα0H) ?_
  have hco : coeff β (topForm P) = coeff α₀ H := by
    rw [hsum, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single α₀]
    · rw [coeff_monomial, if_pos rfl]
    · intro α hα hne
      rw [coeff_monomial, if_neg]
      intro hcontra
      apply hne
      -- `tail α = tail α₀ = β` and both have degree `d` ⇒ `α 0 = α₀ 0`, hence `α = α₀`.
      have htail : α.comapDomain Fin.succ (Fin.succ_injective n).injOn = β := hcontra
      apply Finsupp.ext
      intro j
      refine Fin.cases ?_ ?_ j
      · have hsa : (α.sum fun _ e => e) = d := hdeg α hα
        have hsa0 : (α₀.sum fun _ e => e) = d := hdeg α₀ hα0H
        have hzero_eq : α 0 = α₀ 0 := by
          have e1 : α 0 + ∑ i : Fin n, α i.succ = d := by
            rw [← hsa]; rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ]
          have e2 : α₀ 0 + ∑ i : Fin n, α₀ i.succ = d := by
            rw [← hsa0]; rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ]
          have etail : ∀ i : Fin n, α i.succ = α₀ i.succ := by
            intro i
            have := DFunLike.congr_fun htail i
            rwa [Finsupp.comapDomain_apply, Finsupp.comapDomain_apply] at this
          have : ∑ i : Fin n, α i.succ = ∑ i : Fin n, α₀ i.succ :=
            Finset.sum_congr rfl (fun i _ => etail i)
          omega
        exact hzero_eq
      · intro i
        have := DFunLike.congr_fun htail i
        rwa [Finsupp.comapDomain_apply, Finsupp.comapDomain_apply] at this
    · intro h
      exact absurd hα0H h
  rw [← hco, hzero, coeff_zero]

/-- If all the images `g j` have total degree at most `1`, then `aeval g` does not increase
total degree. -/
private theorem aeval_totalDegree_le {m : ℕ} (g : Fin m → MvPolynomial (Fin m) K)
    (hg : ∀ j, (g j).totalDegree ≤ 1) (p : MvPolynomial (Fin m) K) :
    (aeval g p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro α hα
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
  refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun i => α i) (fun i _ => ?_)) ?_
  · refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    calc α i * (g i).totalDegree ≤ α i * 1 := Nat.mul_le_mul_left _ (hg i)
      _ = α i := by rw [mul_one]
  · exact MvPolynomial.le_totalDegree hα

/-- Lemma A: the shear does not increase total degree. -/
theorem totalDegree_shearHom_le (a : Fin n → K) (P : MvPolynomial (Fin (n + 1)) K) :
    (shearHom a P).totalDegree ≤ P.totalDegree := by
  rw [shearHom]
  refine aeval_totalDegree_le _ (fun j => ?_) P
  refine Fin.cases ?_ ?_ j
  · rw [shearMap_zero, MvPolynomial.totalDegree_X]
  · intro i
    rw [shearMap_succ]
    refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
    rw [MvPolynomial.totalDegree_X]
    refine max_le le_rfl ?_
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add]

/-- Evaluating the dehomogenized top part at `a` gives `Π(1, a)`. -/
theorem eval_topForm (a : Fin n → K) (P : MvPolynomial (Fin (n + 1)) K) :
    eval a (topForm P) = eval (Fin.cons 1 a) (homogeneousComponent P.totalDegree P) := by
  rw [topForm, ← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, ← AlgHom.comp_apply,
    comp_aeval]
  congr 1
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.cases ?_ ?_ j <;> simp

/-- The composite `X₀ ↦ X₀`, `X_{i+1} ↦ a_i X₀` then set `X₀ := T` (the `Polynomial` variable);
equivalently, `shearHom a` followed by `finSuccEquiv` then `eval 0`. -/
noncomputable def ev0Map (a : Fin n → K) : Fin (n + 1) → Polynomial K :=
  Fin.cons Polynomial.X (fun i => Polynomial.C (a i) * Polynomial.X)

/-- On a monomial of degree `d'`, the map `ev0` produces `Π(1, a)·X^{d'}` (one factor of `X` per
unit of degree), where the leading constant is the evaluation `eval (1, a)`. -/
private theorem ev0_monomial (a : Fin n → K) (α : Fin (n + 1) →₀ ℕ) (cc : K) {d' : ℕ}
    (hα : (α.sum fun _ e => e) = d') :
    aeval (ev0Map a) (monomial α cc) =
      Polynomial.C (eval (Fin.cons 1 a) (monomial α cc)) * Polynomial.X ^ d' := by
  rw [aeval_monomial, eval_monomial]
  simp only [ev0Map]
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_zero]
  simp only [Fin.cons_succ, one_pow, one_mul, mul_pow]
  rw [Polynomial.algebraMap_eq, Polynomial.C_mul, map_prod]
  rw [← hα, Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ]
  rw [pow_add, Finset.prod_mul_distrib]
  simp only [map_pow]
  rw [Finset.prod_pow_eq_pow_sum]
  ring

/-- For a homogeneous polynomial `H` of degree `d'`, `ev0 H = Π(1, a)·X^{d'}`. -/
private theorem ev0_homogeneous (a : Fin n → K) {H : MvPolynomial (Fin (n + 1)) K} {d' : ℕ}
    (hH : H.IsHomogeneous d') :
    aeval (ev0Map a) H = Polynomial.C (eval (Fin.cons 1 a) H) * Polynomial.X ^ d' := by
  conv_lhs => rw [H.as_sum, map_sum]
  conv_rhs => rw [H.as_sum, map_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α hα
  refine ev0_monomial a α (coeff α H) ?_
  by_contra hne
  exact (mem_support_iff.mp hα) (hH.coeff_eq_zero (by rwa [Finsupp.degree_apply]))

/-- Lemma C (core): if `Π(1, a) ≠ 0`, then after the shear `P(v(X))` is quasi-monic in `X₀`,
its leading coefficient being the constant `Π(1, a)`. -/
theorem isQuasiMonic_finSuccEquiv_shearHom (a : Fin n → K)
    {P : MvPolynomial (Fin (n + 1)) K} (hev : eval a (topForm P) ≠ 0) :
    IsQuasiMonic (finSuccEquiv K n (shearHom a P)) := by
  classical
  set Q := finSuccEquiv K n (shearHom a P) with hQ
  set d := P.totalDegree with hd
  set c := eval a (topForm P) with hc
  -- (a) `natDegree Q ≤ d`.
  have hnatle : Q.natDegree ≤ d := by
    rw [hQ, MvPolynomial.natDegree_finSuccEquiv]
    exact le_trans (MvPolynomial.degreeOf_le_totalDegree _ _)
      (totalDegree_shearHom_le a P)
  -- (α) `ev0 P = Polynomial.map (eval 0) Q`.
  have halpha : aeval (ev0Map a) P = Polynomial.map (eval (0 : Fin n → K)) Q := by
    have hfun : (Polynomial.mapAlgHom (MvPolynomial.aeval (0 : Fin n → K))).comp
        (((finSuccEquiv K n).toAlgHom).comp (shearHom a)) = aeval (ev0Map a) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom,
        Polynomial.coe_mapAlgHom, shearHom, aeval_X]
      refine Fin.cases ?_ ?_ j
      · simp only [shearMap_zero, finSuccEquiv_X_zero, Polynomial.map_X, ev0Map, Fin.cons_zero]
      · intro i
        simp only [shearMap_succ, map_add, map_mul, finSuccEquiv_X_succ, finSuccEquiv_X_zero,
          Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
          ev0Map, Fin.cons_succ]
        rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes,
          Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, Polynomial.map_C]
        simp
    rw [← hfun]
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, ← hQ, Polynomial.coe_mapAlgHom]
    rw [MvPolynomial.coe_aeval_eq_eval]
  -- (β) `coeff (ev0 P) d = c`.
  have hbeta : (aeval (ev0Map a) P).coeff d = c := by
    conv_lhs => rw [P.sum_homogeneousComponent.symm]
    rw [map_sum, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single d]
    · rw [ev0_homogeneous a (homogeneousComponent_isHomogeneous d P)]
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      rw [hc, eval_topForm]
    · intro i hi hne
      rw [ev0_homogeneous a (homogeneousComponent_isHomogeneous i P)]
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hne), mul_zero]
    · intro hi
      rw [Finset.mem_range] at hi
      exact absurd (Nat.lt_succ_self d) hi
  -- `coeff Q d = C c`.
  have hcoeffQ : Q.coeff d = MvPolynomial.C c := by
    apply MvPolynomial.ext
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · rw [MvPolynomial.coeff_C, if_pos rfl]
      rw [← hbeta, halpha, Polynomial.coeff_map]
      rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
    · rw [MvPolynomial.coeff_C, if_neg (Ne.symm hm)]
      rw [MvPolynomial.finSuccEquiv_coeff_coeff]
      by_contra hne
      have hmem : (Finsupp.cons d m) ∈ (shearHom a P).support := mem_support_iff.mpr hne
      have hle := MvPolynomial.le_totalDegree hmem
      have hsd : (shearHom a P).totalDegree ≤ d := totalDegree_shearHom_le a P
      have hcons : ((Finsupp.cons d m).sum fun _ e => e) = d + (m.sum fun _ e => e) := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ, Finsupp.cons_zero]
        congr 1
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        exact Finset.sum_congr rfl (fun i _ => Finsupp.cons_succ i d m)
      rw [hcons] at hle
      have hmz : (m.sum fun _ e => e) = 0 := by omega
      apply hm
      apply Finsupp.ext
      intro j
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      by_contra hj
      have : 0 < (m.sum fun _ e => e) := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        exact Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨j, Finset.mem_univ j, Nat.pos_of_ne_zero hj⟩
      omega
  -- Conclude.
  have hcne : Q.coeff d ≠ 0 := by
    rw [hcoeffQ]
    simpa using hev
  have hdle : d ≤ Q.natDegree := Polynomial.le_natDegree_of_ne_zero hcne
  have hnateq : Q.natDegree = d := le_antisymm hnatle hdle
  refine ⟨?_, c, ?_⟩
  · intro h
    rw [h, Polynomial.coeff_zero] at hcne
    exact hcne rfl
  · rw [Polynomial.leadingCoeff, hnateq, hcoeffQ]

/-- **BPR Lemma 4.74.** For a finite set `𝒫 ⊆ K[X₀, …, X_n]` (with `K` of characteristic zero),
there is a linear automorphism `v` such that `P(v(X))` is quasi-monic in `X₀` for every nonzero
`P ∈ 𝒫`. -/
theorem lemma_4_74 [CharZero K] (S : Finset (MvPolynomial (Fin (n + 1)) K)) :
    ∃ v : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K,
      ∀ P ∈ S, P ≠ 0 → IsQuasiMonic (finSuccEquiv K n (v P)) := by
  classical
  set B : MvPolynomial (Fin n) K := ∏ P ∈ S.filter (· ≠ 0), topForm P with hB
  have hBne : B ≠ 0 := by
    rw [hB, Finset.prod_ne_zero_iff]
    exact fun P hP => topForm_ne_zero (Finset.mem_filter.mp hP).2
  obtain ⟨a, -, haB⟩ := lemma_4_75 B hBne
  refine ⟨shearEquiv a, fun P hP hP0 => ?_⟩
  rw [shearEquiv_apply]
  refine isQuasiMonic_finSuccEquiv_shearHom a ?_
  intro h0
  refine haB ?_
  rw [hB, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hP, hP0⟩) h0

end Azurite.BPR.Chapter4
