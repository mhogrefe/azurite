import Azurite.BasuPollackRoy.Chapter4.Section4_4.FiniteMapping
import Azurite.BasuPollackRoy.Chapter4.Section4_4.IdealOfPolynomials
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_16
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_19
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_21
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# BPR Proposition 4.76: the resultant projection

Let `𝒫 = {P₁, …, P_s} ⊂ K[X₁, …, X_k]` with `P₁` quasi-monic in `X_k`. There is a finite set
`Proj_{X_k}(𝒫) ⊂ K[X₁, …, X_{k-1}] ∩ Ideal(𝒫, K)` with
`π(Zer(𝒫, C^k)) = Zer(Proj_{X_k}(𝒫), C^{k-1})`, `π` being a finite mapping (`C` algebraically
closed). `Proj` is built from the resultant with respect to `X_k` of `P₁` and the generic
combination `R = P₂ + U P₃ + ⋯ + U^{s-2} P_s`, expanded in powers of `U`.

As elsewhere in §4.4 we single out `X₀` (Mathlib's `finSuccEquiv`), so `π = Fin.tail`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {n : ℕ} {K : Type*} [Field K]

/-- View `P ∈ K[X₀, …, X_n]` in `K[X₁, …, X_n][U][X₀]`: split off `X₀` (`finSuccEquiv`), then
embed the coefficients `K[X₁, …, X_n]` as `U`-constants. -/
noncomputable def embedX0 (P : MvPolynomial (Fin (n + 1)) K) :
    Polynomial (Polynomial (MvPolynomial (Fin n) K)) :=
  (finSuccEquiv K n P).map
    (Polynomial.C : MvPolynomial (Fin n) K →+* Polynomial (MvPolynomial (Fin n) K))

/-- `U`, as an element of `K[X₁, …, X_n][U][X₀]` (a constant in `X₀`). -/
noncomputable def uVar : Polynomial (Polynomial (MvPolynomial (Fin n) K)) :=
  Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin n) K))

/-- The generic combination `R = P₂ + U P₃ + ⋯ + U^{s-2} P_s`, viewed in `K[X₁,…,X_n][U][X₀]`. -/
noncomputable def Rbar (rest : List (MvPolynomial (Fin (n + 1)) K)) :
    Polynomial (Polynomial (MvPolynomial (Fin n) K)) :=
  ∑ i ∈ Finset.range rest.length, embedX0 (rest.getD i 0) * uVar ^ i

/-- The resultant of `P₁` and `R` with respect to `X₀`, an element of `K[X₁, …, X_n][U]`. -/
noncomputable def resXk (P₁ : MvPolynomial (Fin (n + 1)) K)
    (rest : List (MvPolynomial (Fin (n + 1)) K)) : Polynomial (MvPolynomial (Fin n) K) :=
  Res (embedX0 P₁) (Rbar rest)

/-- `Proj_{X_k}(𝒫)`: the coefficients (in `K[X₁, …, X_{k-1}]`) of the powers of `U` in
`Res_{X_k}(P₁, R)`, together with `0`. -/
noncomputable def projPolys (P₁ : MvPolynomial (Fin (n + 1)) K)
    (rest : List (MvPolynomial (Fin (n + 1)) K)) : Finset (MvPolynomial (Fin n) K) :=
  insert 0 ((Finset.range ((resXk P₁ rest).natDegree + 1)).image (resXk P₁ rest).coeff)

/-- `finSuccEquiv` of `rename Fin.succ q` is the constant polynomial `C q`: `rename Fin.succ`
embeds `K[X₁,…,X_n]` as the `X₀`-constants. -/
private theorem finSuccEquiv_rename_succ (q : MvPolynomial (Fin n) K) :
    finSuccEquiv K n (MvPolynomial.rename Fin.succ q) = Polynomial.C q := by
  have key : ((finSuccEquiv K n).toRingHom.comp (MvPolynomial.rename Fin.succ).toRingHom) =
      (Polynomial.C : MvPolynomial (Fin n) K →+* _) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [finSuccEquiv_apply]
    · intro i; simp [finSuccEquiv_apply]
  have := DFunLike.congr_fun key q
  simpa using this

variable {C : Type*} [Field C] [Algebra K C]

/-- The specialization `θ_u : K[X₁,…,X_n][U] → C` sending `U ↦ u` and substituting `x'` into the
coefficients. -/
noncomputable def specMap (x' : Fin n → C) (u : C) :
    Polynomial (MvPolynomial (Fin n) K) →+* C :=
  Polynomial.eval₂RingHom (MvPolynomial.aeval x' : MvPolynomial (Fin n) K →ₐ[K] C).toRingHom u

/-- Mapping `embedX0 P` through `specMap x' u` (specializing the coefficients at `x'`) gives the
univariate polynomial `P(X₀, x')` in `X₀`. -/
private theorem embedX0_map_specMap (x' : Fin n → C) (u : C) (P : MvPolynomial (Fin (n + 1)) K) :
    (embedX0 P).map (specMap x' u) =
      Polynomial.map (MvPolynomial.aeval x').toRingHom (finSuccEquiv K n P) := by
  unfold embedX0 specMap
  rw [Polynomial.map_map]
  congr 1
  ext q <;> simp

/-- Re-derivation of the `FiniteMapping` bridge: `aeval (cons t y) P = eval t (P(X₀,y))`. -/
private theorem aeval_cons_eq' (y : Fin n → C) (t : C) (P : MvPolynomial (Fin (n + 1)) K) :
    aeval (Fin.cons t y) P =
      Polynomial.eval t (Polynomial.map (MvPolynomial.aeval y).toRingHom (finSuccEquiv K n P)) := by
  have key : (MvPolynomial.aeval (Fin.cons t y) :
        MvPolynomial (Fin (n + 1)) K →ₐ[K] C).toRingHom =
      (Polynomial.evalRingHom t).comp ((Polynomial.mapRingHom (MvPolynomial.aeval y).toRingHom).comp
        (finSuccEquiv K n).toAlgHom.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [finSuccEquiv_apply]
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [finSuccEquiv_X_zero]
      · simp [finSuccEquiv_X_succ]
  have := DFunLike.congr_fun key P
  simpa [Polynomial.coe_mapRingHom] using this

/-- Evaluating `embedX0 P` (specialized at `x'`) at `X₀ ↦ t` gives `aeval (cons t x') P`. -/
private theorem eval_embedX0_map_specMap (x' : Fin n → C) (u t : C)
    (P : MvPolynomial (Fin (n + 1)) K) :
    Polynomial.eval t ((embedX0 P).map (specMap x' u)) = aeval (Fin.cons t x') P := by
  rw [embedX0_map_specMap, ← aeval_cons_eq']

/-- `uVar` maps to the constant `u`. -/
private theorem uVar_map_specMap (x' : Fin n → C) (u : C) :
    (uVar : Polynomial (Polynomial (MvPolynomial (Fin n) K))).map (specMap x' u) =
      Polynomial.C u := by
  unfold uVar specMap
  simp

/-- Evaluating `Rbar` (specialized at `x'`) at `X₀ ↦ ξ` gives `∑ aeval (cons ξ x') rest_i · u^i`. -/
private theorem eval_Rbar_map_specMap (x' : Fin n → C) (u ξ : C)
    (rest : List (MvPolynomial (Fin (n + 1)) K)) :
    Polynomial.eval ξ ((Rbar rest).map (specMap x' u)) =
      ∑ i ∈ Finset.range rest.length, aeval (Fin.cons ξ x') (rest.getD i 0) * u ^ i := by
  unfold Rbar
  rw [Polynomial.map_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.map_mul, Polynomial.map_pow, uVar_map_specMap, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, eval_embedX0_map_specMap]

/-- `embedX0 P` has the same `X₀`-degree as `finSuccEquiv K n P`. -/
private theorem embedX0_natDegree (P : MvPolynomial (Fin (n + 1)) K) :
    (embedX0 P).natDegree = (finSuccEquiv K n P).natDegree := by
  unfold embedX0
  exact Polynomial.natDegree_map_eq_of_injective
    (Polynomial.C_injective) (finSuccEquiv K n P)

/-- The leading coefficient (in `X₀`) of `embedX0 P` is `C (leadingCoeff (finSuccEquiv P))`. -/
private theorem embedX0_leadingCoeff (P : MvPolynomial (Fin (n + 1)) K) :
    (embedX0 P).leadingCoeff =
      Polynomial.C (finSuccEquiv K n P).leadingCoeff := by
  unfold embedX0 Polynomial.leadingCoeff
  rw [Polynomial.natDegree_map_eq_of_injective (Polynomial.C_injective),
    Polynomial.coeff_map]

/-- For a `X₀`-quasi-monic `P₁`, specializing `embedX0 P₁` at `x'` preserves the `X₀`-degree. -/
private theorem natDegree_embedX0_map_specMap (x' : Fin n → C) (u : C)
    {P₁ : MvPolynomial (Fin (n + 1)) K} (hqm : IsQuasiMonic (finSuccEquiv K n P₁)) :
    ((embedX0 P₁).map (specMap x' u)).natDegree = (embedX0 P₁).natDegree := by
  obtain ⟨c, hc⟩ := hqm.2
  have hcne : c ≠ 0 := hqm.leadingCoeff_const_ne_zero c hc
  apply Polynomial.natDegree_map_of_leadingCoeff_ne_zero
  rw [embedX0_leadingCoeff, hc]
  unfold specMap
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
  exact fun h => hcne ((map_eq_zero_iff _ (algebraMap K C).injective).mp h)

/-- Membership in `zerOfFinset C (projPolys P₁ rest)` forces every coefficient of `resXk` to vanish
under `aeval x'`. -/
private theorem aeval_resXk_coeff_eq_zero {P₁ : MvPolynomial (Fin (n + 1)) K}
    {rest : List (MvPolynomial (Fin (n + 1)) K)} {x' : Fin n → C}
    (hx' : x' ∈ zerOfFinset C (projPolys P₁ rest)) (i : ℕ) :
    MvPolynomial.aeval x' ((resXk P₁ rest).coeff i) = 0 := by
  by_cases hi : i ≤ (resXk P₁ rest).natDegree
  · refine hx' _ ?_
    unfold projPolys
    refine Finset.mem_insert_of_mem ?_
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

/-- `resXk` specialized at `x'` (a point of `Zer(projPolys)`) is the zero polynomial in `C[U]`. -/
private theorem resXk_map_aeval_eq_zero {P₁ : MvPolynomial (Fin (n + 1)) K}
    {rest : List (MvPolynomial (Fin (n + 1)) K)} {x' : Fin n → C}
    (hx' : x' ∈ zerOfFinset C (projPolys P₁ rest)) :
    (resXk P₁ rest).map (MvPolynomial.aeval x').toRingHom = 0 := by
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  exact aeval_resXk_coeff_eq_zero hx' i

open Polynomial in
/-- **The specialized resultant vanishes.** For `x' ∈ Zer(projPolys)`, every specialization at
`u ∈ C` of the resultant of `P₁(X₀, x')` and `R(U, x', X₀)` is `0`. -/
private theorem res_specialized_eq_zero {P₁ : MvPolynomial (Fin (n + 1)) K}
    {rest : List (MvPolynomial (Fin (n + 1)) K)} (hqm : IsQuasiMonic (finSuccEquiv K n P₁))
    {x' : Fin n → C} (hx' : x' ∈ zerOfFinset C (projPolys P₁ rest)) (u : C) :
    Res ((embedX0 P₁).map (specMap x' u)) ((Rbar rest).map (specMap x' u)) = 0 := by
  set P₁' := (embedX0 P₁).map (specMap x' u) with hP₁'
  set R' := (Rbar rest).map (specMap x' u) with hR'
  set d₁ := (embedX0 P₁).natDegree with hd₁
  set d₂ := (Rbar rest).natDegree with hd₂
  -- natDegree of P₁' is d₁; natDegree of R' is ≤ d₂.
  have hP₁'deg : P₁'.natDegree = d₁ := natDegree_embedX0_map_specMap x' u hqm
  have hR'deg : R'.natDegree ≤ d₂ := Polynomial.natDegree_map_le
  -- specMap (resXk) = resultant P₁' R' d₁ d₂  (via Res_eq_resultant + resultant_map_map).
  have hmap : specMap x' u (resXk P₁ rest) = Polynomial.resultant P₁' R' d₁ d₂ := by
    unfold resXk
    rw [Res_eq_resultant, ← hd₁, ← hd₂]
    rw [hP₁', hR']
    exact (Polynomial.resultant_map_map (embedX0 P₁) (Rbar rest) d₁ d₂ (specMap x' u)).symm
  -- LHS is 0: resXk specialized at x' is the zero polynomial.
  have hLHS : specMap x' u (resXk P₁ rest) = 0 := by
    unfold specMap
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map, resXk_map_aeval_eq_zero hx',
      Polynomial.eval_zero]
  -- The leading coefficient of P₁' is nonzero (algebraMap c).
  obtain ⟨c, hc⟩ := hqm.2
  have hcne : c ≠ 0 := hqm.leadingCoeff_const_ne_zero c hc
  have hlead : P₁'.coeff d₁ = algebraMap K C c := by
    rw [hP₁', Polynomial.coeff_map, hd₁,
      show (embedX0 P₁).coeff (embedX0 P₁).natDegree = (embedX0 P₁).leadingCoeff from rfl,
      embedX0_leadingCoeff, hc]
    unfold specMap
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    simp
  have hleadne : P₁'.coeff d₁ ≠ 0 := by
    rw [hlead]; exact fun h => hcne ((map_eq_zero_iff _ (algebraMap K C).injective).mp h)
  -- resultant P₁' R' d₁ d₂ = (leadingCoeff P₁')^(d₂ - R'.natDegree) * Res P₁' R'.
  have hk : R'.natDegree + (d₂ - R'.natDegree) = d₂ := by omega
  have hfactor : Polynomial.resultant P₁' R' d₁ d₂ =
      P₁'.coeff d₁ ^ (d₂ - R'.natDegree) * Res P₁' R' := by
    conv_lhs => rw [← hk]
    rw [Polynomial.resultant_add_right_deg P₁' R' d₁ R'.natDegree (d₂ - R'.natDegree) le_rfl]
    congr 1
    rw [Res_eq_resultant, hP₁'deg]
  rw [hmap] at hLHS
  rw [hfactor] at hLHS
  exact (mul_eq_zero.mp hLHS).resolve_left (pow_ne_zero _ hleadne)

open Polynomial in
/-- Two univariate polynomials over an algebraically closed field with vanishing resultant, the
first nonzero of positive degree, share a common root. -/
private theorem exists_common_root [IsAlgClosed C] {P Q : C[X]} (hP : P ≠ 0)
    (hPdeg : 0 < P.natDegree) (hRes : Res P Q = 0) :
    ∃ ξ : C, P.IsRoot ξ ∧ Q.IsRoot ξ := by
  classical
  by_cases hQ : Q = 0
  · subst hQ
    obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_root P (by
      rw [Polynomial.degree_eq_natDegree hP]; exact_mod_cast hPdeg.ne')
    exact ⟨ξ, hξ, by simp⟩
  · -- `Res = 0` over the fraction field `C` of `C` ⟹ not coprime ⟹ gcd non-unit.
    have hnc : ¬ IsCoprime (P.map (algebraMap C C)) (Q.map (algebraMap C C)) :=
      (Res_eq_zero_iff_not_isCoprime P Q hP hQ).mp hRes
    simp only [Algebra.algebraMap_self, Polynomial.map_id] at hnc
    have hgcd_not_unit : ¬ IsUnit (EuclideanDomain.gcd P Q) :=
      fun h => hnc (EuclideanDomain.gcd_isUnit_iff.mp h)
    set g := EuclideanDomain.gcd P Q with hg
    have hgP : g ∣ P := EuclideanDomain.gcd_dvd_left P Q
    have hgQ : g ∣ Q := EuclideanDomain.gcd_dvd_right P Q
    have hgne : g ≠ 0 := fun h => hP (by
      have := EuclideanDomain.gcd_eq_zero_iff.mp h; exact this.1)
    have hgdeg : g.degree ≠ 0 := by
      intro h0
      exact hgcd_not_unit (Polynomial.isUnit_iff_degree_eq_zero.mpr h0)
    obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_root g hgdeg
    exact ⟨ξ, hξ.dvd hgP, hξ.dvd hgQ⟩

variable [IsAlgClosed C]

/-- **Per-`u` common root.** For `x' ∈ Zer(projPolys)`, `P₁` quasi-monic of positive `X₀`-degree,
and any `u`, there is `ξ` with `(ξ, x')` a zero of `P₁` and `∑ rest_i(ξ,x') · u^i = 0`. -/
private theorem exists_root_for_u {P₁ : MvPolynomial (Fin (n + 1)) K}
    {rest : List (MvPolynomial (Fin (n + 1)) K)} (hqm : IsQuasiMonic (finSuccEquiv K n P₁))
    (hpos : 0 < (finSuccEquiv K n P₁).natDegree)
    {x' : Fin n → C} (hx' : x' ∈ zerOfFinset C (projPolys P₁ rest)) (u : C) :
    ∃ ξ : C, aeval (Fin.cons ξ x') P₁ = 0 ∧
      ∑ i ∈ Finset.range rest.length, aeval (Fin.cons ξ x') (rest.getD i 0) * u ^ i = 0 := by
  set P₁' := (embedX0 P₁).map (specMap x' u) with hP₁'
  set R' := (Rbar rest).map (specMap x' u) with hR'
  have hP₁'deg : P₁'.natDegree = (finSuccEquiv K n P₁).natDegree := by
    rw [hP₁', natDegree_embedX0_map_specMap x' u hqm, embedX0_natDegree]
  have hP₁'pos : 0 < P₁'.natDegree := by rw [hP₁'deg]; exact hpos
  have hP₁'ne : P₁' ≠ 0 := fun h => by simp [h] at hP₁'pos
  obtain ⟨ξ, hξP, hξR⟩ := exists_common_root hP₁'ne hP₁'pos (res_specialized_eq_zero hqm hx' u)
  refine ⟨ξ, ?_, ?_⟩
  · have := eval_embedX0_map_specMap x' u ξ P₁
    rw [← hP₁'] at this
    rw [← this]; exact hξP
  · have := eval_Rbar_map_specMap x' u ξ rest
    rw [← hR'] at this
    rw [← this]; exact hξR

omit [IsAlgClosed C] in
/-- The set of `X₀`-values `ξ` making `(ξ, x')` a zero of a positive-`X₀`-degree quasi-monic `P₁`
is finite (the roots of the nonzero univariate `P₁(X₀, x')`). -/
private theorem finite_root_set {P₁ : MvPolynomial (Fin (n + 1)) K}
    (hqm : IsQuasiMonic (finSuccEquiv K n P₁)) (x' : Fin n → C) :
    {ξ : C | aeval (Fin.cons ξ x') P₁ = 0}.Finite := by
  obtain ⟨c, hc⟩ := hqm.2
  have hcne : c ≠ 0 := hqm.leadingCoeff_const_ne_zero c hc
  set Py : Polynomial C :=
    Polynomial.map (MvPolynomial.aeval x').toRingHom (finSuccEquiv K n P₁) with hPy
  have hPyne : Py ≠ 0 := by
    intro h0
    have hcoeff : Py.coeff (finSuccEquiv K n P₁).natDegree = algebraMap K C c := by
      rw [hPy, Polynomial.coeff_map, ← Polynomial.leadingCoeff, hc]; simp
    rw [h0, Polynomial.coeff_zero] at hcoeff
    exact hcne ((map_eq_zero_iff _ (algebraMap K C).injective).mp hcoeff.symm)
  apply Set.Finite.subset (Polynomial.finite_setOf_isRoot hPyne)
  intro ξ hξ
  show Py.IsRoot ξ
  rw [hPy, Polynomial.IsRoot, ← aeval_cons_eq']
  exact hξ

/-- **The backward direction's lift.** For `x' ∈ Zer(projPolys)`, `P₁` quasi-monic of positive
`X₀`-degree, there is `ξ` with `(ξ, x')` a common zero of `P₁` and every member of `rest`. -/
private theorem exists_lift {P₁ : MvPolynomial (Fin (n + 1)) K}
    {rest : List (MvPolynomial (Fin (n + 1)) K)} (hqm : IsQuasiMonic (finSuccEquiv K n P₁))
    (hpos : 0 < (finSuccEquiv K n P₁).natDegree)
    {x' : Fin n → C} (hx' : x' ∈ zerOfFinset C (projPolys P₁ rest)) :
    ∃ ξ : C, aeval (Fin.cons ξ x') P₁ = 0 ∧
      ∀ i, i < rest.length → aeval (Fin.cons ξ x') (rest.getD i 0) = 0 := by
  classical
  -- The finite set of admissible `ξ`.
  have hfin := finite_root_set hqm x'
  set S : Set C := {ξ : C | aeval (Fin.cons ξ x') P₁ = 0} with hS
  haveI : Finite ↥S := hfin
  haveI : Infinite C := by
    have : Infinite C := IsAlgClosed.instInfinite
    exact this
  -- Choose, for each `u`, a root `ξ_u ∈ S` with the `R`-condition.
  choose ξ hξroot hξR using fun u => exists_root_for_u hqm hpos hx' u
  set f : C → ↥S := fun u => ⟨ξ u, hξroot u⟩ with hf
  obtain ⟨⟨z, hz⟩, hinf⟩ := Finite.exists_infinite_fiber f
  -- The `U`-polynomial associated to `z`.
  set Φ : Polynomial C :=
    ∑ i ∈ Finset.range rest.length,
      Polynomial.C (aeval (Fin.cons z x') (rest.getD i 0)) * Polynomial.X ^ i with hΦ
  have hΦeval : ∀ u : C, Polynomial.eval u Φ =
      ∑ i ∈ Finset.range rest.length, aeval (Fin.cons z x') (rest.getD i 0) * u ^ i := by
    intro u
    rw [hΦ, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  -- `Φ` has infinitely many roots, so `Φ = 0`.
  have hΦzero : Φ = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := f ⁻¹' {⟨z, hz⟩})
    · intro u hu
      simp only [hf, Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk.injEq] at hu
      show Φ.IsRoot u
      rw [Polynomial.IsRoot, hΦeval]
      have := hξR u
      rw [hu] at this
      exact this
    · exact Set.infinite_coe_iff.mp hinf
  -- Read off the coefficients of `Φ`.
  refine ⟨z, hz, fun i hi => ?_⟩
  have hcoeff : Φ.coeff i = aeval (Fin.cons z x') (rest.getD i 0) := by
    rw [hΦ, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro j _ hj
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hj.symm, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr hi) h
  rw [← hcoeff, hΦzero, Polynomial.coeff_zero]

/-! ### Clause (1): the projection polynomials lie in the ideal -/

/-- `βHom`: apply `rename Fin.succ` to the `U`-coefficients, taking `K[X₁,…,X_n][U]` to
`K[X₀,…,X_n][U]`. -/
noncomputable def betaHom :
    Polynomial (MvPolynomial (Fin n) K) →+* Polynomial (MvPolynomial (Fin (n + 1)) K) :=
  Polynomial.mapRingHom (MvPolynomial.rename Fin.succ).toRingHom

/-- `gHom`: the transport `K[X₁,…,X_n][U][X₀] → K[X₀,…,X_n][U]` sending `X₀ ↦ X₀`, `U ↦ U`, and a
`X₀`-constant `embedX0 P ↦ C P`. -/
noncomputable def gHom :
    Polynomial (Polynomial (MvPolynomial (Fin n) K)) →+*
      Polynomial (MvPolynomial (Fin (n + 1)) K) :=
  Polynomial.eval₂RingHom (betaHom) (Polynomial.C (MvPolynomial.X 0))

/-- `gHom` sends the `X₀`-constant `embedX0 P` to the genuine `U`-constant `C P`. -/
theorem gHom_embedX0 (P : MvPolynomial (Fin (n + 1)) K) :
    gHom (embedX0 P) = Polynomial.C P := by
  have key : (gHom.comp ((Polynomial.mapRingHom
        (Polynomial.C : MvPolynomial (Fin n) K →+* Polynomial (MvPolynomial (Fin n) K))).comp
        (finSuccEquiv K n).toAlgHom.toRingHom)) =
      (Polynomial.C : MvPolynomial (Fin (n + 1)) K →+* _) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [gHom, betaHom, finSuccEquiv_apply, Polynomial.coe_mapRingHom]
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [gHom, betaHom, finSuccEquiv_X_zero, Polynomial.coe_mapRingHom]
      · simp [gHom, betaHom, finSuccEquiv_X_succ, Polynomial.coe_mapRingHom]
  have := DFunLike.congr_fun key P
  simpa [embedX0, Polynomial.coe_mapRingHom] using this

/-- `gHom` sends `uVar` to the `U` indeterminate. -/
theorem gHom_uVar :
    gHom (uVar : Polynomial (Polynomial (MvPolynomial (Fin n) K))) = Polynomial.X := by
  simp [gHom, uVar, betaHom]

/-- `gHom` sends `Rbar` to the genuine generic combination `∑ rest_i · U^i` in
`K[X₀,…,X_n][U]`. -/
theorem gHom_Rbar (rest : List (MvPolynomial (Fin (n + 1)) K)) :
    gHom (Rbar rest) =
      ∑ i ∈ Finset.range rest.length, Polynomial.C (rest.getD i 0) * Polynomial.X ^ i := by
  unfold Rbar
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_pow, gHom_embedX0, gHom_uVar]

/-- The `U`-coefficient of `gHom (C resXk)` is `rename Fin.succ (resXk.coeff i)`. -/
theorem gHom_C_resXk_coeff (P₁ : MvPolynomial (Fin (n + 1)) K)
    (rest : List (MvPolynomial (Fin (n + 1)) K)) (i : ℕ) :
    (gHom (Polynomial.C (resXk P₁ rest))).coeff i =
      MvPolynomial.rename Fin.succ ((resXk P₁ rest).coeff i) := by
  rw [gHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, betaHom, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map]
  rfl

/-- `P₁` lies in the ideal generated by `{P₁} ∪ rest`. -/
private theorem P₁_mem_ideal (P₁ : MvPolynomial (Fin (n + 1)) K)
    (rest : List (MvPolynomial (Fin (n + 1)) K)) :
    P₁ ∈ idealOfPolys (insert P₁ rest.toFinset) :=
  Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))

/-- Each `rest_j` (for `j < rest.length`) lies in the ideal generated by `{P₁} ∪ rest`. -/
private theorem rest_mem_ideal (P₁ : MvPolynomial (Fin (n + 1)) K)
    (rest : List (MvPolynomial (Fin (n + 1)) K)) {j : ℕ} (hj : j < rest.length) :
    rest.getD j 0 ∈ idealOfPolys (insert P₁ rest.toFinset) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
    (List.mem_toFinset.mpr (List.getElem_mem hj))))

/-- **Clause (1).** Each coefficient of `resXk`, embedded by `rename Fin.succ`, lies in
`Ideal({P₁} ∪ rest)`. -/
theorem clause_one (P₁ : MvPolynomial (Fin (n + 1)) K)
    (rest : List (MvPolynomial (Fin (n + 1)) K))
    (hpos : 0 < (finSuccEquiv K n P₁).natDegree) (i : ℕ) :
    MvPolynomial.rename Fin.succ ((resXk P₁ rest).coeff i) ∈
      idealOfPolys (insert P₁ rest.toFinset) := by
  set I := idealOfPolys (insert P₁ rest.toFinset) with hI
  -- Prop 4.19 over `E`.
  have hH : (embedX0 P₁).natDegree ≠ 0 ∨ (Rbar rest).natDegree ≠ 0 := by
    left; rw [embedX0_natDegree]; omega
  obtain ⟨U₀, V₀, _, _, hUV⟩ := Proposition_4_19 (embedX0 P₁) (Rbar rest) hH
  -- Apply `gHom` and take the `i`-th `U`-coefficient.
  have hgUV := congrArg gHom hUV
  rw [map_add, map_mul, map_mul, gHom_embedX0, gHom_Rbar] at hgUV
  have hcoeff : (gHom (Polynomial.C (resXk P₁ rest))).coeff i =
      (gHom U₀ * Polynomial.C P₁ +
        gHom V₀ *
          ∑ j ∈ Finset.range rest.length, Polynomial.C (rest.getD j 0) * Polynomial.X ^ j).coeff i :=
    congrArg (fun p => Polynomial.coeff p i) hgUV
  rw [gHom_C_resXk_coeff] at hcoeff
  rw [hcoeff]
  -- The RHS coefficient is a combination lying in the ideal.
  rw [Polynomial.coeff_add]
  apply Ideal.add_mem
  · -- `(gHom U₀ * C P₁).coeff i = (gHom U₀).coeff i * P₁ ∈ I`.
    rw [Polynomial.coeff_mul_C]
    exact Ideal.mul_mem_left _ _ (P₁_mem_ideal P₁ rest)
  · -- `(gHom V₀ * ∑ C(rest_j) X^j).coeff i ∈ I`.
    rw [Finset.mul_sum, Polynomial.finsetSum_coeff]
    apply Ideal.sum_mem
    intro j hj
    rw [show gHom V₀ * (Polynomial.C (rest.getD j 0) * Polynomial.X ^ j)
        = (gHom V₀ * Polynomial.X ^ j) * Polynomial.C (rest.getD j 0) by ring,
      Polynomial.coeff_mul_C]
    exact Ideal.mul_mem_left _ _ (rest_mem_ideal P₁ rest (Finset.mem_range.mp hj))

/-! ### Clause (2): the projection identity -/

omit [IsAlgClosed C] in
/-- Membership unfolding for the zero set of `projPolys`. -/
private theorem mem_zerOfFinset_projPolys {P₁ : MvPolynomial (Fin (n + 1)) K}
    {rest : List (MvPolynomial (Fin (n + 1)) K)} {x' : Fin n → C} :
    x' ∈ zerOfFinset C (projPolys P₁ rest) ↔
      ∀ i, MvPolynomial.aeval x' ((resXk P₁ rest).coeff i) = 0 := by
  constructor
  · intro hx' i; exact aeval_resXk_coeff_eq_zero hx' i
  · intro h Q hQ
    unfold projPolys at hQ
    rw [Finset.mem_insert] at hQ
    rcases hQ with hQ | hQ
    · subst hQ; simp
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
      exact h i

/-- **Clause (2).** The `Fin.tail`-image of `Zer({P₁} ∪ rest)` equals `Zer(projPolys)`. -/
theorem clause_two {P₁ : MvPolynomial (Fin (n + 1)) K}
    {rest : List (MvPolynomial (Fin (n + 1)) K)} (hqm : IsQuasiMonic (finSuccEquiv K n P₁))
    (hpos : 0 < (finSuccEquiv K n P₁).natDegree) :
    (Fin.tail : (Fin (n + 1) → C) → (Fin n → C)) ''
        zerOfFinset C (insert P₁ rest.toFinset) = zerOfFinset C (projPolys P₁ rest) := by
  apply Set.Subset.antisymm
  · -- forward: image ⊆ Zer(projPolys)
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_zerOfFinset_projPolys]
    intro i
    have hmem := clause_one P₁ rest hpos i
    have h0 := aeval_eq_zero_of_mem_idealOfPolys hmem x hx
    rw [MvPolynomial.aeval_rename] at h0
    rw [show (x ∘ Fin.succ) = Fin.tail x from rfl] at h0
    exact h0
  · -- backward: Zer(projPolys) ⊆ image
    intro x' hx'
    obtain ⟨ξ, hξP, hξrest⟩ := exists_lift hqm hpos hx'
    refine ⟨Fin.cons ξ x', ?_, by simp [Fin.tail_cons]⟩
    intro p hp
    rw [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact hξP
    · obtain ⟨j, hjlt, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hp)
      have := hξrest j hjlt
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt, Option.getD_some] at this

omit [IsAlgClosed C] in
/-- **Edge case.** If `P₁` is quasi-monic of `X₀`-degree `0`, it is the nonzero constant `c`, so it
takes the nonzero value `algebraMap c` everywhere. -/
private theorem aeval_eq_of_natDegree_zero {P₁ : MvPolynomial (Fin (n + 1)) K}
    (hqm : IsQuasiMonic (finSuccEquiv K n P₁)) (h0 : (finSuccEquiv K n P₁).natDegree = 0)
    (x : Fin (n + 1) → C) : ∃ c : K, c ≠ 0 ∧ aeval x P₁ = algebraMap K C c := by
  obtain ⟨c, hc⟩ := hqm.2
  have hcne : c ≠ 0 := hqm.leadingCoeff_const_ne_zero c hc
  refine ⟨c, hcne, ?_⟩
  -- `finSuccEquiv P₁ = C (C c)` since it has degree 0 and leading coeff `C c`.
  have hP₁eq : finSuccEquiv K n P₁ = Polynomial.C (MvPolynomial.C c) := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    rw [show (finSuccEquiv K n P₁).coeff 0 = (finSuccEquiv K n P₁).leadingCoeff from ?_, hc]
    rw [Polynomial.leadingCoeff, h0]
  have hbridge := aeval_cons_eq' (Fin.tail x) (x 0) P₁
  rw [Fin.cons_self_tail] at hbridge
  rw [hbridge, hP₁eq]
  simp

/-- **BPR Proposition 4.76.** For `𝒫 = {P₁} ∪ rest` with `P₁` quasi-monic in `X₀` and `C`
algebraically closed, `projPolys` lies in `Ideal(𝒫, K) ∩ K[X₁, …, X_{k-1}]`, the projection
`π = Fin.tail` maps `Zer(𝒫, C^k)` onto `Zer(projPolys, C^{k-1})`, and `π` is a finite mapping. -/
theorem proposition_4_76 {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]
    (P₁ : MvPolynomial (Fin (n + 1)) K) (rest : List (MvPolynomial (Fin (n + 1)) K))
    (hqm : IsQuasiMonic (finSuccEquiv K n P₁)) :
    ∃ Proj : Finset (MvPolynomial (Fin n) K),
      (∀ Q ∈ Proj, MvPolynomial.rename Fin.succ Q ∈ idealOfPolys (insert P₁ rest.toFinset)) ∧
      (Fin.tail : (Fin (n + 1) → C) → (Fin n → C)) ''
          zerOfFinset C (insert P₁ rest.toFinset) = zerOfFinset C Proj ∧
      IsFiniteMapping C (insert P₁ rest.toFinset) Proj := by
  by_cases hpos : 0 < (finSuccEquiv K n P₁).natDegree
  · -- Main case: `Proj = projPolys P₁ rest`.
    refine ⟨projPolys P₁ rest, ?_, clause_two hqm hpos, ?_, ⟨P₁, Finset.mem_insert_self _ _, hqm⟩⟩
    · -- Clause (1).
      intro Q hQ
      unfold projPolys at hQ
      rw [Finset.mem_insert] at hQ
      rcases hQ with rfl | hQ
      · rw [map_zero]; exact Submodule.zero_mem _
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
        exact clause_one P₁ rest hpos i
    · -- Clause (3): `SurjOn` is the backward inclusion of clause (2).
      rw [Set.SurjOn, ← clause_two hqm hpos]
  · -- Edge case: `P₁` is a nonzero constant, both zero sets are empty.
    push Not at hpos
    have h0 : (finSuccEquiv K n P₁).natDegree = 0 := Nat.le_zero.mp hpos
    obtain ⟨c₀, hc₀⟩ := hqm.2
    have hc₀ne : c₀ ≠ 0 := hqm.leadingCoeff_const_ne_zero c₀ hc₀
    -- `P₁ = MvPolynomial.C c₀`.
    have hP₁C : P₁ = MvPolynomial.C c₀ := by
      apply (finSuccEquiv K n).injective
      have hrhs : finSuccEquiv K n (MvPolynomial.C c₀) = Polynomial.C (MvPolynomial.C c₀) := by
        simp [finSuccEquiv_apply]
      have hcoeff0 : (finSuccEquiv K n P₁).coeff 0 = MvPolynomial.C c₀ := by
        rw [show (0 : ℕ) = (finSuccEquiv K n P₁).natDegree from h0.symm,
          ← Polynomial.leadingCoeff, hc₀]
      rw [hrhs, Polynomial.eq_C_of_natDegree_eq_zero h0, hcoeff0]
    have hRempty : zerOfFinset C ({MvPolynomial.C c₀} : Finset (MvPolynomial (Fin n) K)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have := hx (MvPolynomial.C c₀) (Finset.mem_singleton_self _)
      rw [MvPolynomial.aeval_C] at this
      exact hc₀ne ((map_eq_zero_iff _ (algebraMap K C).injective).mp this)
    have hLempty : zerOfFinset C (insert P₁ rest.toFinset) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨c, hcne, hval⟩ := aeval_eq_of_natDegree_zero (C := C) hqm h0 x
      have := hx P₁ (Finset.mem_insert_self _ _)
      rw [hval] at this
      exact hcne ((map_eq_zero_iff _ (algebraMap K C).injective).mp this)
    refine ⟨{MvPolynomial.C c₀}, ?_, ?_, ?_, ⟨P₁, Finset.mem_insert_self _ _, hqm⟩⟩
    · -- Clause (1): `rename _ (C c₀) = C c₀ = P₁ ∈ Ideal`.
      intro Q hQ
      rw [Finset.mem_singleton] at hQ
      subst hQ
      rw [MvPolynomial.rename_C, ← hP₁C]
      exact P₁_mem_ideal P₁ rest
    · -- Clause (2): both sides empty.
      rw [hLempty, hRempty, Set.image_empty]
    · -- Clause (3): the `SurjOn` part (the `∃ P` part is supplied above).
      rw [Set.SurjOn, hRempty]
      exact Set.empty_subset _

end Azurite.BPR.Chapter4
