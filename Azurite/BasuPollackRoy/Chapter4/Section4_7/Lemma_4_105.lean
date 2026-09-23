import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectivePathConnected
import Azurite.BasuPollackRoy.Chapter4.Section4_7.Theorem_4_104
import Azurite.BasuPollackRoy.Chapter3.Section3_2.ComplementFinitePathConnected

/-!
# BPR Lemma 4.105: `ℙ₁(C) ∖ Δ` is semialgebraically path connected (`Δ` finite)

For a finite subset `Δ ⊆ ℙ₁(C)`, the complement `ℙ₁(C) ∖ Δ` is semialgebraically path connected.

The affine building block (`isSemialgebraicallyPathConnected_compl_finite`, §3.2) gives that
`R² ∖ Δ'` is semialgebraically path connected for finite `Δ' ⊆ R²`. We lift affine paths through the
charts `φ₀, φ₁` of `ℙ₁(C)` and glue across the two charts.
-/

namespace Azurite.BPR.Chapter4

open Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### (A) `chartMap` is continuous -/

set_option linter.unusedSectionVars false in
/-- The affine chart `φᵢ : Cᵏ → ℙ_k(C)` is continuous. -/
theorem continuous_chartMap {k : ℕ} (i : Fin (k + 1)) :
    Continuous (chartMap i : (Fin k → Ri R) → complexProjectiveSpace R k) := by
  rw [continuous_def]
  intro U hU
  -- `chartMap i ⁻¹' U = chartMap i ⁻¹' (U ∩ chartSet i)` since `chartMap i` lands in `chartSet i`.
  have hpre : chartMap i ⁻¹' U = chartMap i ⁻¹' (U ∩ chartSet i) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    refine ⟨fun h => ⟨h, Set.mem_range_self x⟩, fun h => h.1⟩
  rw [hpre]
  exact (isOpenP_iff.mp hU) i

/-! ### (B) The chart-overlap equality lemma -/

set_option linter.unusedSectionVars false in
/-- For charts `m, i` and points `z' z`, the projective points `φₘ(z')` and `φᵢ(z)` coincide iff
`z'` lies in the overlap `φₘ⁻¹(𝒰ₘ ∩ 𝒰ᵢ)` and the transition map carries it to `z`. -/
theorem chartMap_eq_chartMap_iff {k : ℕ} (m i : Fin (k + 1)) (z' z : Fin k → Ri R) :
    chartMap m z' = chartMap i z ↔
      z' ∈ (chartOverlap m i : Set (Fin k → Ri R)) ∧ transitionMap m i z' = z := by
  constructor
  · intro h
    -- `φᵢ z ∈ 𝒰ᵢ`, so `φₘ z' ∈ 𝒰ᵢ`, i.e. `z' ∈ overlap`.
    have hmem : chartMap m z' ∈ (chartSet i : Set (complexProjectiveSpace R k)) := by
      rw [h]; exact Set.mem_range_self z
    have hov : z' ∈ (chartOverlap m i : Set (Fin k → Ri R)) :=
      (chartMap_mem_chartSet_iff m i z').mp hmem
    refine ⟨hov, ?_⟩
    -- apply `chartInv i` to both sides
    rw [transitionMap_eq_chartInv_chartMap, h, chartInv_chartMap]
  · rintro ⟨hov, htr⟩
    -- `φᵢ (transitionMap m i z') = φₘ z'` since `φₘ z' ∈ 𝒰ᵢ`.
    have hi : (chartMap m z').rep i ≠ 0 := chartMap_rep_ne_zero_of_mem_overlap m i hov
    rw [transitionMap_eq_chartInv_chartMap] at htr
    rw [← htr, chartMap_chartInv i (chartMap m z') hi]

/-! ### Realified transition graph is semialgebraic -/

set_option linter.unusedSectionVars false in
/-- The realified transition map `g wv = realEquiv(φᵢ⁻¹φₘ(realEquiv⁻¹ wv))` has a semialgebraic graph
over the realified overlap `Dov = realEquiv '' (φₘ⁻¹(𝒰ₘ ∩ 𝒰ᵢ))`. -/
theorem isSemialgebraicSet_funGraph_realTransition {k : ℕ} (m i : Fin (k + 1)) :
    IsSemialgebraicSet
      (funGraph (realEquiv '' (chartOverlap m i : Set (Fin k → Ri R)))
        (fun wv : Fin (k + k) → R =>
          realEquiv (transitionMap m i (realEquiv.symm wv)))) := by
  -- The complex graph is semialgebraic over `C`; its realification is a real semialgebraic set.
  have hreal : IsSemialgebraicSet
      ((realEquiv : (Fin (k + k) → Ri R) → _) ''
        (complexFunGraph (chartOverlap m i) (transitionMap m i))) :=
    isSemialgebraicFunctionC_transitionMap m i
  -- Comap along the reindexing `appendReindex k k`.
  have hcomap := IsSemialgebraicSet.comap (appendReindex k k) hreal
  -- `appendReindex k k` is injective, hence surjective on the finite type.
  have hinj : Function.Injective (appendReindex k k) := by
    intro a b hab
    rw [Fin.ext_iff]
    revert hab
    rw [Fin.ext_iff]
    refine Fin.addCases (fun u => ?_) (fun u => ?_) a <;>
      refine Fin.addCases (fun s => ?_) (fun s => ?_) u <;>
      refine Fin.addCases (fun v => ?_) (fun v => ?_) b <;>
      refine Fin.addCases (fun w => ?_) (fun w => ?_) v <;>
      (simp only [appendReindex, Fin.addCases_left, Fin.addCases_right,
         Fin.val_castAdd, Fin.val_natAdd];
       omega)
  have hbij : Function.Surjective (appendReindex k k) :=
    Finite.surjective_of_injective hinj
  have hcompinj : Function.Injective (fun q : Fin ((k + k) + (k + k)) → R => q ∘ appendReindex k k) :=
    hbij.injective_comp_right
  -- Identify `funGraph Dov g` with this comap.
  convert hcomap using 1
  -- both equal the image `{ append (realEquiv a) (realEquiv (trans a)) | a ∈ overlap }`
  set Dov := (realEquiv : (Fin k → Ri R) → _) '' (chartOverlap m i : Set (Fin k → Ri R))
    with hDov
  set g : (Fin (k + k) → R) → (Fin (k + k) → R) :=
    fun wv => realEquiv (transitionMap m i (realEquiv.symm wv)) with hg
  rw [funGraph_eq_image]
  -- `realEquiv '' complexFunGraph = (· ∘ appendReindex) '' (funGraph image)`
  have hCimg : (realEquiv : (Fin (k + k) → Ri R) → _) ''
        (complexFunGraph (chartOverlap m i) (transitionMap m i))
      = (fun q : Fin ((k + k) + (k + k)) → R => q ∘ appendReindex k k) ''
          ((fun wv => Fin.append wv (g wv)) '' Dov) := by
    ext r
    simp only [Set.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨Fin.append (realEquiv (c ∘ Fin.castAdd k)) (realEquiv (c ∘ Fin.natAdd k)), ?_, ?_⟩
      · refine ⟨realEquiv (c ∘ Fin.castAdd k), ⟨c ∘ Fin.castAdd k, hc.1, rfl⟩, ?_⟩
        simp only [hg, Equiv.symm_apply_apply, ← hc.2]
      · rw [← realEquiv_append]
        congr 1
        funext p
        refine Fin.addCases (fun a => ?_) (fun a => ?_) p
        · rw [Fin.append_left, Function.comp_apply]
        · rw [Fin.append_right, Function.comp_apply]
    · rintro ⟨q, ⟨wv, ⟨a, haov, rfl⟩, rfl⟩, rfl⟩
      refine ⟨Fin.append a (transitionMap m i a), ?_, ?_⟩
      · exact ⟨by rw [append_comp_castAdd']; exact haov, by
          rw [append_comp_castAdd', append_comp_natAdd']⟩
      · rw [realEquiv_append]
        congr 1
        simp only [hg, Equiv.symm_apply_apply]
  rw [hCimg, ← Set.image_comp]
  -- comap of `(· ∘ σ) '' A` is `A` when `(· ∘ σ)` injective
  ext q
  simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply]
  constructor
  · intro hq
    exact ⟨q, hq, rfl⟩
  · rintro ⟨r, hr, hrq⟩
    have := hcompinj hrq
    rwa [← this]

/-! ### (B) The path-lifting engine: lifting a realified affine path through a chart -/

set_option linter.unusedSectionVars false in
/-- **Path-lifting engine.** Let `φ_aff : R¹ → R^{2k}` be an affine path with semialgebraic graph
over `[0,1]`, and let `γ = φᵢ ∘ realEquiv⁻¹ ∘ φ_aff` be its lift through chart `i`. Then the graph of
`γ` is a semialgebraic subset of `R¹ × ℙ_k(C)` (`IsSemialgebraicSetRP`). -/
theorem isSemialgebraicSetRP_chartMap_comp {k : ℕ} (i : Fin (k + 1))
    {D : Set (Fin 1 → R)} {φaff : (Fin 1 → R) → (Fin (k + k) → R)}
    (hφ : IsSemialgebraicSet (funGraph D φaff)) :
    IsSemialgebraicSetRP
      {tp : (Fin 1 → R) × complexProjectiveSpace R k |
        tp.1 ∈ D ∧ tp.2 = chartMap i (realEquiv.symm (φaff tp.1))} := by
  intro m
  -- abbreviations
  set g : (Fin (k + k) → R) → (Fin (k + k) → R) :=
    fun wv => realEquiv (transitionMap m i (realEquiv.symm wv)) with hg
  set Dov := (realEquiv : (Fin k → Ri R) → _) '' (chartOverlap m i : Set (Fin k → Ri R)) with hDov
  -- the affine graph and the transition graph
  have hφgraph : IsSemialgebraicSet (funGraph D φaff) := hφ
  have htgraph : IsSemialgebraicSet (funGraph Dov g) :=
    isSemialgebraicSet_funGraph_realTransition m i
  -- reindexings on `u : Fin ((1 + (k + k)) + (k + k)) → R`
  -- σφ picks out `[t (1) | v (k+k)]` for the affine graph
  set σφ : Fin (1 + (k + k)) → Fin ((1 + (k + k)) + (k + k)) :=
    fun p => Fin.addCases
      (fun a : Fin 1 => Fin.castAdd (k + k) (Fin.castAdd (k + k) a))
      (fun b : Fin (k + k) => Fin.natAdd (1 + (k + k)) b) p with hσφ
  -- σg picks out `[wv (k+k) | v (k+k)]` for the transition graph
  set σg : Fin ((k + k) + (k + k)) → Fin ((1 + (k + k)) + (k + k)) :=
    fun p => Fin.addCases
      (fun a : Fin (k + k) => Fin.castAdd (k + k) (Fin.natAdd 1 a))
      (fun b : Fin (k + k) => Fin.natAdd (1 + (k + k)) b) p with hσg
  -- the big intersected set in `u`-space
  have hbig : IsSemialgebraicSet
      ({u : Fin ((1 + (k + k)) + (k + k)) → R | u ∘ σφ ∈ funGraph D φaff}
        ∩ {u | u ∘ σg ∈ funGraph Dov g}) :=
    (IsSemialgebraicSet.comap σφ hφgraph).inter (IsSemialgebraicSet.comap σg htgraph)
  -- project off the last `(k+k)` coordinates `v`, keeping the first `1+(k+k)` (the `w`)
  have hproj := IsSemialgebraicSet.exists_append_right (k := 1 + (k + k)) (ℓ := k + k) hbig
  -- the chart-`m` pullback equals this projection
  convert hproj using 1
  ext w
  -- abbreviations for the slices of `w`
  set t := w ∘ Fin.castAdd (k + k) with ht
  set wv := w ∘ Fin.natAdd 1 with hwv
  -- bridge: `realEquiv.symm wv ∈ chartOverlap ↔ wv ∈ Dov`
  have hbridge_dom : realEquiv.symm wv ∈ (chartOverlap m i : Set (Fin k → Ri R)) ↔ wv ∈ Dov := by
    rw [hDov, Set.mem_image]
    constructor
    · intro h; exact ⟨realEquiv.symm wv, h, by rw [Equiv.apply_symm_apply]⟩
    · rintro ⟨a, ha, hae⟩; rw [← hae, Equiv.symm_apply_apply]; exact ha
  -- bridge: the transition equation ↔ `φaff t = g wv`
  have hbridge_val :
      transitionMap m i (realEquiv.symm wv) = realEquiv.symm (φaff t) ↔ φaff t = g wv := by
    simp only [hg]
    constructor
    · intro h
      have := congrArg realEquiv h
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    · intro h
      apply realEquiv.injective
      rw [Equiv.apply_symm_apply]
      exact h.symm
  -- helper: `(append w v) ∘ σφ = append t v` and `(append w v) ∘ σg = append wv v`
  have hcompφ : ∀ v : Fin (k + k) → R, Fin.append w v ∘ σφ = Fin.append t v := by
    intro v
    funext p
    refine Fin.addCases (fun a => ?_) (fun a => ?_) p
    · simp only [hσφ, Function.comp_apply, Fin.addCases_left, Fin.append_left, ht]
    · simp only [hσφ, Function.comp_apply, Fin.addCases_right, Fin.append_right]
  have hcompg : ∀ v : Fin (k + k) → R, Fin.append w v ∘ σg = Fin.append wv v := by
    intro v
    funext p
    refine Fin.addCases (fun a => ?_) (fun a => ?_) p
    · simp only [hσg, Function.comp_apply, Fin.addCases_left, Fin.append_left, hwv]
    · simp only [hσg, Function.comp_apply, Fin.addCases_right, Fin.append_right]
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨htmem, hval⟩
    -- the chart equality
    rw [chartMap_eq_chartMap_iff] at hval
    obtain ⟨hov, htr⟩ := hval
    refine ⟨φaff t, ?_, ?_⟩
    · rw [hcompφ, append_mem_funGraph]; exact ⟨htmem, rfl⟩
    · rw [hcompg, append_mem_funGraph]
      refine ⟨hbridge_dom.mp hov, ?_⟩
      exact (hbridge_val.mp htr)
  · rintro ⟨v, h1, h2⟩
    rw [hcompφ, append_mem_funGraph] at h1
    rw [hcompg, append_mem_funGraph] at h2
    obtain ⟨htmem, hvφ⟩ := h1
    obtain ⟨hwvDov, hvg⟩ := h2
    refine ⟨htmem, ?_⟩
    rw [chartMap_eq_chartMap_iff]
    refine ⟨hbridge_dom.mpr hwvDov, ?_⟩
    rw [hbridge_val]
    rw [← hvφ, hvg]

/-! ### (B) closure of `IsSemialgebraicSetRP` under union -/

set_option linter.unusedSectionVars false in
/-- `IsSemialgebraicSetRP` is closed under union. -/
theorem IsSemialgebraicSetRP.union {k p : ℕ}
    {S T : Set ((Fin p → R) × complexProjectiveSpace R k)}
    (hS : IsSemialgebraicSetRP S) (hT : IsSemialgebraicSetRP T) :
    IsSemialgebraicSetRP (S ∪ T) := by
  intro i
  have heq : {w : Fin (p + (k + k)) → R |
        (w ∘ Fin.castAdd (k + k), chartMap i (realEquiv.symm (w ∘ Fin.natAdd p))) ∈ S ∪ T}
      = {w : Fin (p + (k + k)) → R |
          (w ∘ Fin.castAdd (k + k), chartMap i (realEquiv.symm (w ∘ Fin.natAdd p))) ∈ S}
        ∪ {w | (w ∘ Fin.castAdd (k + k), chartMap i (realEquiv.symm (w ∘ Fin.natAdd p))) ∈ T} := by
    ext w; simp only [Set.mem_ofPred_eq, Set.mem_union]
  rw [heq]
  exact (hS i).union (hT i)

set_option linter.unusedSectionVars false in
/-- An `IsSemialgebraicSetRP` graph contained in a larger one along an equality of the relation, for
the half-graphs. (Congruence helper.) -/
theorem IsSemialgebraicSetRP.congr {k p : ℕ}
    {S T : Set ((Fin p → R) × complexProjectiveSpace R k)}
    (h : S = T) (hS : IsSemialgebraicSetRP S) : IsSemialgebraicSetRP T := h ▸ hS

/-! ### Affine reparametrization of a semialgebraic path graph -/

open MvPolynomial in
set_option linter.unusedSectionVars false in
/-- **Affine reparametrization.** If `ϕ` has a semialgebraic graph over `S`, and the affine
reparametrization `r u = 2u + e` maps `D` into `S`, then `ϕ ∘ r` has a semialgebraic graph over `D`.
-/
theorem isSemialgebraicSet_funGraph_reparam {ℓ : ℕ} {S D : Set (Fin 1 → R)}
    {ϕ : (Fin 1 → R) → (Fin ℓ → R)} (hϕ : IsSemialgebraicSet (funGraph S ϕ)) (hD : IsSemialgebraicSet D)
    (e : R) (hmaps : ∀ u ∈ D, (fun _ : Fin 1 => 2 * u 0 + e) ∈ S) :
    IsSemialgebraicSet (funGraph D (fun u => ϕ (fun _ : Fin 1 => 2 * u 0 + e))) := by
  -- the linear reparametrization map `M` on `R^{1+ℓ}`
  set M : (Fin (1 + ℓ) → R) → (Fin (1 + ℓ) → R) :=
    fun z => Fin.append (fun _ : Fin 1 => 2 * z (Fin.castAdd ℓ 0) + e) (z ∘ Fin.natAdd 1) with hM
  -- `M` is a polynomial map
  set P : Fin (1 + ℓ) → MvPolynomial (Fin (1 + ℓ)) R :=
    fun j => Fin.addCases
      (fun _ : Fin 1 => 2 * X (Fin.castAdd ℓ 0) + C e)
      (fun b : Fin ℓ => X (Fin.natAdd 1 b)) j with hP
  have hMpoly : M = polynomialMap P := by
    funext z j
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · simp only [hM, hP, polynomialMap, Fin.append_left, Subsingleton.elim a 0, Fin.addCases_left,
        map_add, map_mul, map_ofNat, eval_X, eval_C]
    · simp only [hM, hP, polynomialMap, Fin.append_right, Fin.addCases_right, eval_X,
        Function.comp_apply]
  have hMsemialg : IsSemialgebraicFunction (Set.univ : Set (Fin (1 + ℓ) → R)) M := by
    rw [hMpoly]
    exact isSemialgebraicFunction_polynomialMap isSemialgebraicSet_univ P
  -- preimage of the graph of `ϕ` under `M`
  have hpre : IsSemialgebraicSet (Set.univ ∩ M ⁻¹' funGraph S ϕ) :=
    (proposition_2_83 hMsemialg).2 hϕ
  -- intersect with the `D` constraint on the first coordinate
  have hDcomap : IsSemialgebraicSet {z : Fin (1 + ℓ) → R | z ∘ Fin.castAdd ℓ ∈ D} :=
    IsSemialgebraicSet.comap (Fin.castAdd ℓ) hD
  have hbig : IsSemialgebraicSet ((Set.univ ∩ M ⁻¹' funGraph S ϕ)
      ∩ {z : Fin (1 + ℓ) → R | z ∘ Fin.castAdd ℓ ∈ D}) := hpre.inter hDcomap
  -- identify the reparametrized graph with this intersection
  have heq : funGraph D (fun u => ϕ (fun _ : Fin 1 => 2 * u 0 + e))
      = (Set.univ ∩ M ⁻¹' funGraph S ϕ) ∩ {z : Fin (1 + ℓ) → R | z ∘ Fin.castAdd ℓ ∈ D} := by
    ext z
    simp only [mem_funGraph, Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_preimage,
      Set.mem_ofPred_eq]
    have hcast0 : (z ∘ Fin.castAdd ℓ) 0 = z (Fin.castAdd ℓ 0) := rfl
    have hMcast : M z ∘ Fin.castAdd ℓ = (fun _ : Fin 1 => 2 * z (Fin.castAdd ℓ 0) + e) := by
      funext s; simp only [hM, Function.comp_apply, Fin.append_left]
    have hMnat : M z ∘ Fin.natAdd 1 = z ∘ Fin.natAdd 1 := by
      funext s; simp only [hM, Function.comp_apply, Fin.append_right]
    constructor
    · rintro ⟨hzD, hzval⟩
      refine ⟨⟨?_, ?_⟩, hzD⟩
      · rw [hMcast]
        have := hmaps _ hzD
        rwa [hcast0] at this
      · rw [hMnat, hMcast, hzval, hcast0]
    · rintro ⟨hMz, hzD⟩
      refine ⟨hzD, ?_⟩
      rw [hMnat, hMcast] at hMz
      rw [hMz.2, hcast0]
  rw [heq]; exact hbig

/-! ### Small bridges to the affine interval -/

/-! ### Infinitude and detour points -/

set_option linter.unusedSectionVars false in
/-- `Ri R` is infinite (`R` is infinite, embedded by `AdjoinRoot.of`). -/
instance : Infinite (Ri R) :=
  haveI : Infinite R := Infinite.of_injective (Nat.cast : ℕ → R) Nat.cast_injective
  Infinite.of_injective (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R)) (RingHom.injective _)

set_option linter.unusedSectionVars false in
/-- For distinct charts `i ≠ j`, the pulled-back overlap `φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ)` is infinite. -/
theorem infinite_chartOverlap {k : ℕ} {i j : Fin (k + 1)} (hij : i ≠ j) :
    (chartOverlap i j : Set (Fin k → Ri R)).Infinite := by
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
  rw [chartOverlap_eq]
  have hset : {x : Fin k → Ri R | (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j ≠ 0}
      = {x : Fin k → Ri R | x b ≠ 0} := by
    ext x; simp only [Set.mem_ofPred_eq, ← hb, Fin.insertNth_apply_succAbove]
  rw [hset]
  have halg : Function.Injective (algebraMap R (Ri R)) :=
    FaithfulSMul.algebraMap_injective R (Ri R)
  -- `algebraMap R (Ri R) ∘ ((· : ℕ → R) shifted)` is injective and avoids `0`
  have hcastinj : Function.Injective (fun n : ℕ => algebraMap R (Ri R) ((n : R) + 1)) := by
    intro n₁ n₂ hc
    have := halg hc
    rw [add_left_inj] at this
    exact Nat.cast_injective this
  have hne0 : ∀ n : ℕ, algebraMap R (Ri R) ((n : R) + 1) ≠ 0 := by
    intro n h
    have := halg (by rw [h, map_zero] : algebraMap R (Ri R) ((n : R) + 1) = algebraMap R (Ri R) 0)
    have hpos : (0 : R) < (n : R) + 1 := by positivity
    rw [this] at hpos; exact lt_irrefl _ hpos
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => Function.update (0 : Fin k → Ri R) b (algebraMap R (Ri R) ((n : R) + 1)))
    (hi := ?_) (hf := ?_)
  · intro n₁ n₂ hc
    have := congrFun hc b
    simp only [Function.update_self] at this
    exact hcastinj this
  · intro n
    simp only [Set.mem_ofPred_eq, Function.update_self]
    exact hne0 n

set_option linter.unusedSectionVars false in
/-- For distinct charts `i ≠ j`, the chart overlap `𝒰ᵢ ∩ 𝒰ⱼ` in `ℙ_k(C)` is infinite. -/
theorem infinite_chartSet_inter {k : ℕ} {i j : Fin (k + 1)} (hij : i ≠ j) :
    (chartSet i ∩ chartSet j : Set (complexProjectiveSpace R k)).Infinite := by
  have hsub : chartMap i '' (chartOverlap i j : Set (Fin k → Ri R))
      ⊆ (chartSet i ∩ chartSet j : Set (complexProjectiveSpace R k)) := by
    rintro p ⟨x, hx, rfl⟩
    exact ⟨Set.mem_range_self x, (chartMap_mem_chartSet_iff i j x).mpr hx⟩
  refine Set.Infinite.mono hsub ?_
  exact (infinite_chartOverlap hij).image (fun a _ b _ h => by
    have := congrArg (chartInv i) h
    rwa [chartInv_chartMap, chartInv_chartMap] at this)

set_option linter.unusedSectionVars false in
/-- **Detour point.** For distinct charts `i ≠ j` and finite `Δ`, there is a point in
`𝒰ᵢ ∩ 𝒰ⱼ ∖ Δ`. -/
theorem exists_detour_point_proj {k : ℕ} {i j : Fin (k + 1)} (hij : i ≠ j)
    (Δ : Finset (complexProjectiveSpace R k)) :
    ∃ z : complexProjectiveSpace R k,
      z ∈ (chartSet i : Set (complexProjectiveSpace R k)) ∧
      z ∈ (chartSet j : Set (complexProjectiveSpace R k)) ∧
      z ∉ (↑Δ : Set (complexProjectiveSpace R k)) := by
  have hinf : (chartSet i ∩ chartSet j : Set (complexProjectiveSpace R k)).Infinite :=
    infinite_chartSet_inter hij
  have hne : ((chartSet i ∩ chartSet j) \ (↑Δ : Set (complexProjectiveSpace R k))).Nonempty :=
    (hinf.sdiff Δ.finite_toSet).nonempty
  obtain ⟨z, ⟨⟨hzi, hzj⟩, hzΔ⟩⟩ := hne
  exact ⟨z, hzi, hzj, hzΔ⟩

set_option linter.unusedSectionVars false in
theorem zero_eq_constPt : (0 : Fin 1 → R) = constPt (0 : R) := rfl

set_option linter.unusedSectionVars false in
theorem one_eq_constPt : (1 : Fin 1 → R) = constPt (1 : R) := rfl

set_option linter.unusedSectionVars false in
theorem Icc_zero_one_eq_unitIntervalPt :
    Set.Icc (0 : Fin 1 → R) 1 = (unitIntervalPt : Set (Fin 1 → R)) := rfl

/-! ### (C) Affine chart-path data -/

set_option linter.unusedSectionVars false in
/-- **Affine chart-path.** If `x, y ∈ 𝒰ᵢ ∖ Δ`, there is an affine path `ϕ : R¹ → R^{2k}` with
semialgebraic graph and continuous on `[0,1]`, whose chart-`i` lift `φᵢ ∘ realEquiv⁻¹ ∘ ϕ` joins `x`
to `y` while avoiding `Δ`. (The reusable engine for both the same-chart and cross-chart cases.) -/
theorem chartPath_affine {k : ℕ} (hk : 1 ≤ k) (Δ : Finset (complexProjectiveSpace R k))
    (i : Fin (k + 1)) {x y : complexProjectiveSpace R k}
    (hxi : x ∈ (chartSet i : Set (complexProjectiveSpace R k)))
    (hyi : y ∈ (chartSet i : Set (complexProjectiveSpace R k)))
    (hxΔ : x ∉ (↑Δ : Set (complexProjectiveSpace R k)))
    (hyΔ : y ∉ (↑Δ : Set (complexProjectiveSpace R k))) :
    ∃ ϕ : (Fin 1 → R) → (Fin (k + k) → R),
      IsSemialgebraicSet (funGraph (Set.Icc 0 1) ϕ) ∧
      ContinuousOn ϕ (Set.Icc 0 1) ∧
      ϕ 0 = realEquiv (chartInv i x) ∧
      ϕ 1 = realEquiv (chartInv i y) ∧
      (∀ t ∈ Set.Icc (0 : Fin 1 → R) 1,
        chartMap i (realEquiv.symm (ϕ t)) ∉ (↑Δ : Set (complexProjectiveSpace R k))) := by
  classical
  have hk2 : 2 ≤ k + k := by omega
  set a := realEquiv (chartInv i x) with ha
  set b := realEquiv (chartInv i y) with hb
  set Δ' : Finset (Fin (k + k) → R) :=
    (Δ.filter (fun δ => δ ∈ chartSet i)).image (fun δ => realEquiv (chartInv i δ)) with hΔ'
  have hkey : ∀ p : complexProjectiveSpace R k, p ∈ (chartSet i : Set (complexProjectiveSpace R k)) →
      realEquiv (chartInv i p) ∈ Δ' → p ∈ Δ := by
    intro p hpi hmem
    rw [hΔ', Finset.mem_image] at hmem
    obtain ⟨δ, hδf, hδe⟩ := hmem
    rw [Finset.mem_filter] at hδf
    have hci : chartInv i δ = chartInv i p := realEquiv.injective hδe
    have hδrep : δ.rep i ≠ 0 := by rw [chartSet_eq] at hδf; exact hδf.2
    have hprep : p.rep i ≠ 0 := by rw [chartSet_eq] at hpi; exact hpi
    have : δ = p := by
      have h1 := chartMap_chartInv i δ hδrep
      have h2 := chartMap_chartInv i p hprep
      rw [hci] at h1; rw [← h1, h2]
    rw [← this]; exact hδf.1
  have haΔ : a ∉ Δ' := fun h => hxΔ (by rw [Finset.mem_coe]; exact hkey x hxi h)
  have hbΔ : b ∉ Δ' := fun h => hyΔ (by rw [Finset.mem_coe]; exact hkey y hyi h)
  obtain ⟨ϕ, hϕpath⟩ :=
    Azurite.BPR.isSemialgebraicallyPathConnected_compl_finite hk2 Δ' a
      (by rw [Set.mem_compl_iff, Finset.mem_coe]; exact haΔ) b
      (by rw [Set.mem_compl_iff, Finset.mem_coe]; exact hbΔ)
  refine ⟨ϕ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Icc_zero_one_eq_unitIntervalPt]; exact hϕpath.isSemialgebraicFunction
  · rw [Icc_zero_one_eq_unitIntervalPt]; exact hϕpath.continuousOn
  · rw [zero_eq_constPt, hϕpath.source]
  · rw [one_eq_constPt, hϕpath.target]
  · intro t ht hmem
    have hγti : chartMap i (realEquiv.symm (ϕ t)) ∈ chartSet i := Set.mem_range_self _
    have hci : chartInv i (chartMap i (realEquiv.symm (ϕ t))) = realEquiv.symm (ϕ t) := by
      rw [chartInv_chartMap]
    have hγti' : (chartMap i (realEquiv.symm (ϕ t))).rep i ≠ 0 := by
      rw [chartSet_eq] at hγti; exact hγti
    have hΔ'mem : ϕ t ∈ Δ' := by
      rw [hΔ', Finset.mem_image]
      refine ⟨chartMap i (realEquiv.symm (ϕ t)),
        by rw [Finset.mem_filter]; exact ⟨hmem, by rw [chartSet_eq]; exact hγti'⟩, ?_⟩
      rw [hci, Equiv.apply_symm_apply]
    have hmaps := hϕpath.mapsTo
    have htu : t ∈ (unitIntervalPt : Set (Fin 1 → R)) := by
      rw [← Icc_zero_one_eq_unitIntervalPt]; exact ht
    have := hmaps htu
    rw [Set.mem_compl_iff, Finset.mem_coe] at this
    exact this hΔ'mem

set_option linter.unusedSectionVars false in
/-- **Same-chart connector.** If `x, y ∈ 𝒰ᵢ ∖ Δ`, there is a continuous, semialgebraic-graph path in
`ℙ_k(C) ∖ Δ` from `x` to `y` lying inside the chart `𝒰ᵢ`. -/
theorem sameChart_path {k : ℕ} (hk : 1 ≤ k) (Δ : Finset (complexProjectiveSpace R k))
    (i : Fin (k + 1)) {x y : complexProjectiveSpace R k}
    (hxi : x ∈ (chartSet i : Set (complexProjectiveSpace R k)))
    (hyi : y ∈ (chartSet i : Set (complexProjectiveSpace R k)))
    (hxΔ : x ∉ (↑Δ : Set (complexProjectiveSpace R k)))
    (hyΔ : y ∉ (↑Δ : Set (complexProjectiveSpace R k))) :
    ∃ γ : (Fin 1 → R) → complexProjectiveSpace R k,
      ContinuousOn γ (Set.Icc 0 1) ∧
      Set.MapsTo γ (Set.Icc 0 1) ((↑Δ : Set (complexProjectiveSpace R k))ᶜ) ∧
      γ 0 = x ∧ γ 1 = y ∧
      IsSemialgebraicSetRP
        {tp : (Fin 1 → R) × complexProjectiveSpace R k |
          tp.1 ∈ Set.Icc 0 1 ∧ tp.2 = γ tp.1} := by
  obtain ⟨ϕ, hgraph, hcont, hsrc, htgt, havoid⟩ := chartPath_affine hk Δ i hxi hyi hxΔ hyΔ
  set γ : (Fin 1 → R) → complexProjectiveSpace R k :=
    fun t => chartMap i (realEquiv.symm (ϕ t)) with hγ
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · have hsymm : Continuous (realEquiv.symm : (Fin (k + k) → R) → (Fin k → Ri R)) :=
      realEquivₜ.symm.continuous
    exact (continuous_chartMap i).comp_continuousOn (hsymm.comp_continuousOn hcont)
  · intro t ht; rw [Set.mem_compl_iff]; exact havoid t ht
  · show chartMap i (realEquiv.symm (ϕ (0 : Fin 1 → R))) = x
    rw [hsrc, Equiv.symm_apply_apply]
    exact chartMap_chartInv i x (by rw [chartSet_eq] at hxi; exact hxi)
  · show chartMap i (realEquiv.symm (ϕ (1 : Fin 1 → R))) = y
    rw [htgt, Equiv.symm_apply_apply]
    exact chartMap_chartInv i y (by rw [chartSet_eq] at hyi; exact hyi)
  · exact isSemialgebraicSetRP_chartMap_comp i hgraph

/-! ### Local interval helpers (semialgebraic and closed) -/

omit [Field R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Membership in `[a,b] ⊆ R¹` reduces to the single coordinate. -/
theorem mem_Icc_fin_one_local {a b : R} {y : Fin 1 → R} :
    y ∈ Set.Icc (constPt a) (constPt b) ↔ a ≤ y 0 ∧ y 0 ≤ b := by
  simp only [Set.mem_Icc, constPt, Pi.le_def]
  refine ⟨fun ⟨h1, h2⟩ => ⟨h1 0, h2 0⟩, fun ⟨h1, h2⟩ => ⟨fun i => ?_, fun i => ?_⟩⟩
  · rwa [Subsingleton.elim i 0]
  · rwa [Subsingleton.elim i 0]

open MvPolynomial in
omit [IsRealClosed R] in
/-- The interval `[a,b] ⊆ R¹` is semialgebraic. -/
theorem isSemialgebraicSet_Icc_local (a b : R) :
    IsSemialgebraicSet (Set.Icc (constPt a) (constPt b)) := by
  have heq : Set.Icc (constPt a) (constPt b)
      = {y : Fin 1 → R | eval y (X 0 - C a) ≥ 0} ∩ {y | eval y (X 0 - C b) ≤ 0} := by
    ext y
    rw [mem_Icc_fin_one_local]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, map_sub, eval_X, eval_C, ge_iff_le,
      sub_nonneg, sub_nonpos]
  rw [heq]
  exact (IsSemialgebraicSet.geZero _).inter (IsSemialgebraicSet.leZero _)

set_option linter.unusedSectionVars false in
/-- The interval `[a,b] ⊆ R¹` is closed (euclidean topology). -/
theorem isClosed_Icc_local (a b : R) : IsClosed (Set.Icc (constPt a) (constPt b)) := by
  rw [isClosed_iff, isOpen_iff]
  intro y hy
  rw [Set.mem_compl_iff, mem_Icc_fin_one_local, not_and_or, not_le, not_le] at hy
  have hkey : ∀ s t r : R, 0 < r → (s - t) ^ 2 < r ^ 2 → |s - t| < r := by
    intro s t r hr hsq
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd hsq (not_lt.mpr (by nlinarith [abs_nonneg (s - t), sq_abs (s - t)]))
  have hnormSq : ∀ z : Fin 1 → R, euclideanNormSq (z - y) = (z 0 - y 0) ^ 2 := by
    intro z
    simp only [euclideanNormSq, Finset.univ_unique, Finset.sum_singleton, Pi.sub_apply,
      Fin.default_eq_zero]
  rcases hy with hya | hyb
  · refine ⟨y, a - y 0, by linarith, mem_openBall_self y (by linarith), fun z hz => ?_⟩
    rw [mem_openBall, hnormSq] at hz
    rw [Set.mem_compl_iff, mem_Icc_fin_one_local, not_and_or]
    refine Or.inl (not_le.mpr ?_)
    have := abs_lt.mp (hkey _ _ _ (by linarith) hz)
    linarith [this.1]
  · refine ⟨y, y 0 - b, by linarith, mem_openBall_self y (by linarith), fun z hz => ?_⟩
    rw [mem_openBall, hnormSq] at hz
    rw [Set.mem_compl_iff, mem_Icc_fin_one_local, not_and_or]
    refine Or.inr (not_le.mpr ?_)
    have := abs_lt.mp (hkey _ _ _ (by linarith) hz)
    linarith [this.2]

/-! ### (C) Cross-chart concatenation -/

set_option linter.unusedSectionVars false in
/-- **Cross-chart connector.** Two points `x ∈ 𝒰ᵢ ∖ Δ`, `y ∈ 𝒰ⱼ ∖ Δ` lying in different charts are
joined through a detour point `z ∈ 𝒰ᵢ ∩ 𝒰ⱼ ∖ Δ` by concatenating a chart-`i` path `x → z` and a
chart-`j` path `z → y`. -/
theorem crossChart_path {k : ℕ} (hk : 1 ≤ k) (Δ : Finset (complexProjectiveSpace R k))
    (i j : Fin (k + 1)) {x y z : complexProjectiveSpace R k}
    (hxi : x ∈ (chartSet i : Set (complexProjectiveSpace R k)))
    (hyj : y ∈ (chartSet j : Set (complexProjectiveSpace R k)))
    (hzi : z ∈ (chartSet i : Set (complexProjectiveSpace R k)))
    (hzj : z ∈ (chartSet j : Set (complexProjectiveSpace R k)))
    (hxΔ : x ∉ (↑Δ : Set (complexProjectiveSpace R k)))
    (hyΔ : y ∉ (↑Δ : Set (complexProjectiveSpace R k)))
    (hzΔ : z ∉ (↑Δ : Set (complexProjectiveSpace R k))) :
    ∃ γ : (Fin 1 → R) → complexProjectiveSpace R k,
      ContinuousOn γ (Set.Icc 0 1) ∧
      Set.MapsTo γ (Set.Icc 0 1) ((↑Δ : Set (complexProjectiveSpace R k))ᶜ) ∧
      γ 0 = x ∧ γ 1 = y ∧
      IsSemialgebraicSetRP
        {tp : (Fin 1 → R) × complexProjectiveSpace R k |
          tp.1 ∈ Set.Icc 0 1 ∧ tp.2 = γ tp.1} := by
  classical
  -- affine paths `x → z` in chart `i`, `z → y` in chart `j`
  obtain ⟨ϕ₁, hg₁, hc₁, hs₁, ht₁, hav₁⟩ := chartPath_affine hk Δ i hxi hzi hxΔ hzΔ
  obtain ⟨ϕ₂, hg₂, hc₂, hs₂, ht₂, hav₂⟩ := chartPath_affine hk Δ j hzj hyj hzΔ hyΔ
  -- reparametrized affine paths
  set ψ₁ : (Fin 1 → R) → (Fin (k + k) → R) := fun u => ϕ₁ (fun _ : Fin 1 => 2 * u 0 + 0) with hψ₁
  set ψ₂ : (Fin 1 → R) → (Fin (k + k) → R) := fun u => ϕ₂ (fun _ : Fin 1 => 2 * u 0 + (-1)) with hψ₂
  -- the chart lifts of each half
  set γ₁ : (Fin 1 → R) → complexProjectiveSpace R k :=
    fun u => chartMap i (realEquiv.symm (ψ₁ u)) with hγ₁
  set γ₂ : (Fin 1 → R) → complexProjectiveSpace R k :=
    fun u => chartMap j (realEquiv.symm (ψ₂ u)) with hγ₂
  -- the concatenated path
  set γ : (Fin 1 → R) → complexProjectiveSpace R k :=
    fun u => if u 0 ≤ 1 / 2 then γ₁ u else γ₂ u with hγ
  -- the two closed halves
  set H₁ : Set (Fin 1 → R) := Set.Icc (constPt 0) (constPt (1 / 2)) with hH₁
  set H₂ : Set (Fin 1 → R) := Set.Icc (constPt (1 / 2)) (constPt 1) with hH₂
  have hH₁mem : ∀ u, u ∈ H₁ ↔ 0 ≤ u 0 ∧ u 0 ≤ 1 / 2 := fun u => mem_Icc_fin_one_local
  have hH₂mem : ∀ u, u ∈ H₂ ↔ 1 / 2 ≤ u 0 ∧ u 0 ≤ 1 := fun u => mem_Icc_fin_one_local
  -- `[0,1] = H₁ ∪ H₂`
  have hunion : Set.Icc (0 : Fin 1 → R) 1 = H₁ ∪ H₂ := by
    ext u
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, show (1 : Fin 1 → R) = constPt 1 from rfl,
      mem_Icc_fin_one_local]
    simp only [Set.mem_union, hH₁mem, hH₂mem]
    constructor
    · rintro ⟨h0, h1⟩
      rcases le_or_gt (u 0) (1 / 2) with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h.le, h1⟩
    · rintro (⟨h0, h⟩ | ⟨h, h1⟩)
      · exact ⟨h0, by linarith⟩
      · exact ⟨by linarith, h1⟩
  -- the two reparametrizations land in `[0,1]`
  have hr₁maps : ∀ u ∈ H₁, (fun _ : Fin 1 => 2 * u 0 + 0) ∈ Set.Icc (0 : Fin 1 → R) 1 := by
    intro u hu
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, show (1 : Fin 1 → R) = constPt 1 from rfl,
      mem_Icc_fin_one_local]
    obtain ⟨h0, h2⟩ := (hH₁mem u).mp hu
    constructor <;> simp <;> linarith
  have hr₂maps : ∀ u ∈ H₂,
      (fun _ : Fin 1 => 2 * u 0 + (-1)) ∈ Set.Icc (0 : Fin 1 → R) 1 := by
    intro u hu
    rw [show (0 : Fin 1 → R) = constPt 0 from rfl, show (1 : Fin 1 → R) = constPt 1 from rfl,
      mem_Icc_fin_one_local]
    obtain ⟨h1, h2⟩ := (hH₂mem u).mp hu
    constructor <;> simp <;> linarith
  -- `γ₁` agrees with `z` at `u 0 = 1/2`; `γ₂` too; so `γ` glues.
  have hψ₁half : ∀ u : Fin 1 → R, u 0 = 1 / 2 → ψ₁ u = ϕ₁ 1 := by
    intro u hu
    have : (fun _ : Fin 1 => 2 * u 0 + 0) = (1 : Fin 1 → R) := by
      funext s; simp only [Pi.one_apply]; rw [hu]; norm_num
    rw [hψ₁]; show ϕ₁ (fun _ : Fin 1 => 2 * u 0 + 0) = ϕ₁ 1; rw [this]
  have hψ₂half : ∀ u : Fin 1 → R, u 0 = 1 / 2 → ψ₂ u = ϕ₂ 0 := by
    intro u hu
    have : (fun _ : Fin 1 => 2 * u 0 + (-1)) = (0 : Fin 1 → R) := by
      funext s; simp only [Pi.zero_apply]; rw [hu]; norm_num
    rw [hψ₂]; show ϕ₂ (fun _ : Fin 1 => 2 * u 0 + (-1)) = ϕ₂ 0; rw [this]
  have hγ₁z : ∀ u : Fin 1 → R, u 0 = 1 / 2 → γ₁ u = z := by
    intro u hu
    rw [hγ₁]; show chartMap i (realEquiv.symm (ψ₁ u)) = z
    rw [hψ₁half u hu, ht₁, Equiv.symm_apply_apply]
    exact chartMap_chartInv i z (by rw [chartSet_eq] at hzi; exact hzi)
  have hγ₂z : ∀ u : Fin 1 → R, u 0 = 1 / 2 → γ₂ u = z := by
    intro u hu
    rw [hγ₂]; show chartMap j (realEquiv.symm (ψ₂ u)) = z
    rw [hψ₂half u hu, hs₂, Equiv.symm_apply_apply]
    exact chartMap_chartInv j z (by rw [chartSet_eq] at hzj; exact hzj)
  -- `γ` equals `γ₁` on `H₁` and `γ₂` on `H₂`
  have hγeq₁ : ∀ u ∈ H₁, γ u = γ₁ u := by
    intro u hu
    show (if u 0 ≤ 1 / 2 then γ₁ u else γ₂ u) = γ₁ u
    exact ite_eq_left ((hH₁mem u).mp hu).2
  have hγeq₂ : ∀ u ∈ H₂, γ u = γ₂ u := by
    intro u hu
    show (if u 0 ≤ 1 / 2 then γ₁ u else γ₂ u) = γ₂ u
    rcases le_or_gt (u 0) (1 / 2) with h | h
    · have hhalf : u 0 = 1 / 2 := le_antisymm h ((hH₂mem u).mp hu).1
      rw [ite_eq_left h, hγ₁z u hhalf, ← hγ₂z u hhalf]
    · rw [ite_eq_right (not_le.mpr h)]
  -- continuity of each half
  have hsymm : Continuous (realEquiv.symm : (Fin (k + k) → R) → (Fin k → Ri R)) :=
    realEquivₜ.symm.continuous
  -- the reparametrizations are continuous (polynomial maps in the euclidean topology)
  have hcontr₁ : Continuous (fun u : Fin 1 → R => (fun _ : Fin 1 => 2 * u 0 + 0)) := by
    have heq : (fun u : Fin 1 → R => (fun _ : Fin 1 => 2 * u 0 + 0))
        = polynomialMap (fun _ : Fin 1 => 2 * MvPolynomial.X 0 + MvPolynomial.C 0) := by
      funext u s
      simp only [polynomialMap, map_add, map_mul, map_ofNat, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
    rw [heq]; exact continuous_polynomialMap _
  have hcontr₂ : Continuous (fun u : Fin 1 → R => (fun _ : Fin 1 => 2 * u 0 + (-1))) := by
    have heq : (fun u : Fin 1 → R => (fun _ : Fin 1 => 2 * u 0 + (-1)))
        = polynomialMap (fun _ : Fin 1 => 2 * MvPolynomial.X 0 + MvPolynomial.C (-1)) := by
      funext u s
      simp only [polynomialMap, map_add, map_mul, map_ofNat, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
    rw [heq]; exact continuous_polynomialMap _
  have hcontγ₁ : ContinuousOn γ₁ H₁ := by
    rw [hγ₁]
    refine (continuous_chartMap i).comp_continuousOn (hsymm.comp_continuousOn ?_)
    rw [hψ₁]
    exact hc₁.comp hcontr₁.continuousOn hr₁maps
  have hcontγ₂ : ContinuousOn γ₂ H₂ := by
    rw [hγ₂]
    refine (continuous_chartMap j).comp_continuousOn (hsymm.comp_continuousOn ?_)
    rw [hψ₂]
    exact hc₂.comp hcontr₂.continuousOn hr₂maps
  -- avoid properties for each half
  have hav₁' : ∀ u ∈ H₁, γ₁ u ∉ (↑Δ : Set (complexProjectiveSpace R k)) := by
    intro u hu
    rw [hγ₁]
    exact hav₁ (fun _ : Fin 1 => 2 * u 0 + 0) (hr₁maps u hu)
  have hav₂' : ∀ u ∈ H₂, γ₂ u ∉ (↑Δ : Set (complexProjectiveSpace R k)) := by
    intro u hu
    rw [hγ₂]
    exact hav₂ (fun _ : Fin 1 => 2 * u 0 + (-1)) (hr₂maps u hu)
  -- assemble
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity
    rw [hunion]
    exact ContinuousOn.union_of_isClosed
      (hcontγ₁.congr hγeq₁) (hcontγ₂.congr hγeq₂)
      (isClosed_Icc_local _ _) (isClosed_Icc_local _ _)
  · -- maps into `Δᶜ`
    intro u hu
    rw [hunion] at hu
    rw [Set.mem_compl_iff]
    rcases hu with hu | hu
    · rw [hγeq₁ u hu]; exact hav₁' u hu
    · rw [hγeq₂ u hu]; exact hav₂' u hu
  · -- source: `γ 0 = x`
    have h0 : ((0 : Fin 1 → R)) ∈ H₁ := by rw [hH₁mem]; show 0 ≤ (0:R) ∧ (0:R) ≤ 1/2; norm_num
    rw [hγeq₁ _ h0, hγ₁]
    show chartMap i (realEquiv.symm (ψ₁ 0)) = x
    have hψ0 : ψ₁ (0 : Fin 1 → R) = ϕ₁ 0 := by
      have : (fun _ : Fin 1 => 2 * (0 : Fin 1 → R) 0 + 0) = (0 : Fin 1 → R) := by
        funext s; simp only [Pi.zero_apply]; norm_num
      rw [hψ₁]; show ϕ₁ (fun _ : Fin 1 => 2 * (0 : Fin 1 → R) 0 + 0) = ϕ₁ 0; rw [this]
    rw [hψ0, hs₁, Equiv.symm_apply_apply]
    exact chartMap_chartInv i x (by rw [chartSet_eq] at hxi; exact hxi)
  · -- target: `γ 1 = y`
    have h1 : ((1 : Fin 1 → R)) ∈ H₂ := by rw [hH₂mem]; show 1/2 ≤ (1:R) ∧ (1:R) ≤ 1; norm_num
    rw [hγeq₂ _ h1, hγ₂]
    show chartMap j (realEquiv.symm (ψ₂ 1)) = y
    have hψ1 : ψ₂ (1 : Fin 1 → R) = ϕ₂ 1 := by
      have : (fun _ : Fin 1 => 2 * (1 : Fin 1 → R) 0 + (-1)) = (1 : Fin 1 → R) := by
        funext s; simp only [Pi.one_apply]; norm_num
      rw [hψ₂]; show ϕ₂ (fun _ : Fin 1 => 2 * (1 : Fin 1 → R) 0 + (-1)) = ϕ₂ 1; rw [this]
    rw [hψ1, ht₂, Equiv.symm_apply_apply]
    exact chartMap_chartInv j y (by rw [chartSet_eq] at hyj; exact hyj)
  · -- semialgebraic graph: union of the two reparametrized RP-graphs
    set T : Set ((Fin 1 → R) × complexProjectiveSpace R k) :=
      {tp | tp.1 ∈ Set.Icc 0 1 ∧ tp.2 = γ tp.1} with hT
    set T₁ : Set ((Fin 1 → R) × complexProjectiveSpace R k) :=
      {tp | tp.1 ∈ H₁ ∧ tp.2 = chartMap i (realEquiv.symm (ψ₁ tp.1))} with hT₁
    set T₂ : Set ((Fin 1 → R) × complexProjectiveSpace R k) :=
      {tp | tp.1 ∈ H₂ ∧ tp.2 = chartMap j (realEquiv.symm (ψ₂ tp.1))} with hT₂
    have hTeq : T = T₁ ∪ T₂ := by
      ext ⟨u, p⟩
      simp only [hT, hT₁, hT₂, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨huI, hp⟩
        rw [hunion, Set.mem_union] at huI
        rcases huI with hu | hu
        · exact Or.inl ⟨hu, by rw [hp]; exact hγeq₁ u hu⟩
        · exact Or.inr ⟨hu, by rw [hp]; exact hγeq₂ u hu⟩
      · rintro (⟨hu, hp⟩ | ⟨hu, hp⟩)
        · refine ⟨by rw [hunion]; exact Or.inl hu, ?_⟩
          rw [hp]; exact (hγeq₁ u hu).symm
        · refine ⟨by rw [hunion]; exact Or.inr hu, ?_⟩
          rw [hp]; exact (hγeq₂ u hu).symm
    rw [hTeq]
    refine IsSemialgebraicSetRP.union ?_ ?_
    · have := isSemialgebraicSetRP_chartMap_comp (D := H₁) i
        (isSemialgebraicSet_funGraph_reparam hg₁ (isSemialgebraicSet_Icc_local _ _) 0 hr₁maps)
      exact this
    · have := isSemialgebraicSetRP_chartMap_comp (D := H₂) j
        (isSemialgebraicSet_funGraph_reparam hg₂ (isSemialgebraicSet_Icc_local _ _) (-1) hr₂maps)
      exact this

/-! ### (D) BPR Lemma 4.105 -/

set_option linter.unusedSectionVars false in
/-- **BPR Lemma 4.105.** For a finite subset `Δ ⊆ ℙ₁(C)`, the complement `ℙ₁(C) ∖ Δ` is
semialgebraically path connected. -/
theorem lemma_4_105 (Δ : Finset (complexProjectiveSpace R 1)) :
    IsSemialgebraicallyPathConnected ((↑Δ : Set (complexProjectiveSpace R 1))ᶜ) := by
  classical
  intro x hx y hy
  rw [Set.mem_compl_iff] at hx hy
  -- find a chart containing `x`
  obtain ⟨i, hxi⟩ : ∃ i : Fin 2, x ∈ (chartSet i : Set (complexProjectiveSpace R 1)) := by
    have : x ∈ (⋃ i : Fin 2, chartSet i : Set (complexProjectiveSpace R 1)) := by
      rw [iUnion_chartSet]; exact Set.mem_univ x
    rwa [Set.mem_iUnion] at this
  by_cases hyi : y ∈ (chartSet i : Set (complexProjectiveSpace R 1))
  · -- same chart
    obtain ⟨γ, hcont, hmaps, hs, ht, hrp⟩ := sameChart_path (le_refl 1) Δ i hxi hyi hx hy
    exact ⟨γ, hcont, hmaps, hs, ht, hrp⟩
  · -- `y` is in the other chart
    obtain ⟨j, hyj⟩ : ∃ j : Fin 2, y ∈ (chartSet j : Set (complexProjectiveSpace R 1)) := by
      have : y ∈ (⋃ i : Fin 2, chartSet i : Set (complexProjectiveSpace R 1)) := by
        rw [iUnion_chartSet]; exact Set.mem_univ y
      rwa [Set.mem_iUnion] at this
    have hij : i ≠ j := by rintro rfl; exact hyi hyj
    -- detour point in `𝒰ᵢ ∩ 𝒰ⱼ ∖ Δ`
    obtain ⟨z, hzi, hzj, hzΔ⟩ := exists_detour_point_proj hij Δ
    obtain ⟨γ, hcont, hmaps, hs, ht, hrp⟩ :=
      crossChart_path (le_refl 1) Δ i j hxi hyj hzi hzj hx hy hzΔ
    exact ⟨γ, hcont, hmaps, hs, ht, hrp⟩

end Azurite.BPR.Chapter4
