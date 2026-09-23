import Azurite.BasuPollackRoy.Chapter4.Section4_7.ChartOverlap
import Azurite.BasuPollackRoy.Chapter4.Section4_7.ComplexPolySemialgebraic

/-!
# BPR §4.7: chart transition maps are semialgebraic bijections

The transition map `φⱼ⁻¹ ∘ φᵢ` between the overlaps `φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ)` and `φⱼ⁻¹(𝒰ⱼ ∩ 𝒰ᵢ)` is a
semialgebraic bijection over `C = R[i]`. After inserting a `1` in coordinate `i`, the homogeneous
coordinates of `φᵢ(x)` are complex polynomials in `x`, so the rational transition map clears to a
polynomial relation, hence semialgebraic; and `φⱼ⁻¹ ∘ φᵢ` with inverse `φᵢ⁻¹ ∘ φⱼ` is a bijection.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-- The `j`-th homogeneous coordinate of `φᵢ`, as a complex polynomial in the affine coordinates
(here recorded in the `castAdd` block of the graph variables). -/
noncomputable def hcoord (i j : Fin (k + 1)) : MvPolynomial (Fin (k + k)) (Ri R) :=
  (Fin.insertNth i (C 1) (fun a => X (Fin.castAdd k a)) :
    Fin (k + 1) → MvPolynomial (Fin (k + k)) (Ri R)) j

/-- The transition map `φⱼ⁻¹ ∘ φᵢ`, written without choosing a representative (the rep scalar
cancels): `x ↦ fun b => (insertNth i 1 x)(j.succAbove b) / (insertNth i 1 x)(j)`. -/
noncomputable def transitionMap (i j : Fin (k + 1)) (x : Fin k → Ri R) : Fin k → Ri R :=
  fun b => (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) (j.succAbove b)
            / (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j

set_option linter.unusedSectionVars false in
/-- `aeval` of `hcoord` recovers the homogeneous coordinate. -/
theorem aeval_hcoord (i j : Fin (k + 1)) (p : Fin (k + k) → Ri R) :
    aeval p (hcoord i j : MvPolynomial (Fin (k + k)) (Ri R))
      = (Fin.insertNth i (1 : Ri R) (p ∘ Fin.castAdd k) : Fin (k + 1) → Ri R) j := by
  refine Fin.succAboveCases i ?_ (fun a => ?_) j
  · rw [hcoord, Fin.insertNth_apply_same, Fin.insertNth_apply_same]
    exact map_one _
  · rw [hcoord, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove, aeval_X,
      Function.comp_apply]

/-! ### PART A — the transition map is semialgebraic over `C` -/

/-- The cleared-denominator polynomial `y_b · denom − num_b` for output coordinate `b`. -/
noncomputable def transPoly (i j : Fin (k + 1)) (b : Fin k) :
    MvPolynomial (Fin (k + k)) (Ri R) :=
  X (Fin.natAdd k b) * (hcoord i j : MvPolynomial (Fin (k + k)) (Ri R))
    - (hcoord i (j.succAbove b) : MvPolynomial (Fin (k + k)) (Ri R))

set_option linter.unusedSectionVars false in
/-- **PART A.** The transition map `φⱼ⁻¹ ∘ φᵢ` is semialgebraic over `C` on the overlap. -/
theorem isSemialgebraicFunctionC_transitionMap (i j : Fin (k + 1)) :
    IsSemialgebraicFunctionC (chartOverlap i j : Set (Fin k → Ri R)) (transitionMap i j) := by
  classical
  rw [IsSemialgebraicFunctionC]
  have hgraph : complexFunGraph (chartOverlap i j) (transitionMap i j)
      = {p : Fin (k + k) → Ri R |
            aeval p (hcoord i j : MvPolynomial (Fin (k + k)) (Ri R)) = 0}ᶜ
          ∩ ⋂ b ∈ (Finset.univ : Finset (Fin k)),
              {p : Fin (k + k) → Ri R |
                aeval p (transPoly i j b : MvPolynomial (Fin (k + k)) (Ri R)) = 0} := by
    ext p
    set x := p ∘ Fin.castAdd k with hx
    set y := p ∘ Fin.natAdd k with hy
    -- the denominator value
    have hdenom : aeval p (hcoord i j : MvPolynomial (Fin (k + k)) (Ri R))
        = (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j := aeval_hcoord i j p
    have hoverlap : x ∈ chartOverlap i j
        ↔ aeval p (hcoord i j : MvPolynomial (Fin (k + k)) (Ri R)) ≠ 0 := by
      rw [chartOverlap_eq, Set.mem_ofPred_eq, hdenom]
    -- the cleared-denominator value
    have hE : ∀ b : Fin k, aeval p (transPoly i j b : MvPolynomial (Fin (k + k)) (Ri R))
        = y b * (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j
            - (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) (j.succAbove b) := by
      intro b
      rw [transPoly, map_sub, map_mul, aeval_X, aeval_hcoord, aeval_hcoord]
      rfl
    rw [mem_complexFunGraph, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq,
      Set.mem_iInter₂]
    constructor
    · rintro ⟨hxS, hfun⟩
      have hd : aeval p (hcoord i j) ≠ 0 := hoverlap.mp hxS
      refine ⟨hd, fun b _ => ?_⟩
      rw [Set.mem_ofPred_eq, hE b]
      have hyb : y b = (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) (j.succAbove b)
          / (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j := by
        have := congrFun hfun b
        rwa [transitionMap] at this
      rw [hyb, div_mul_cancel₀, sub_self]
      rw [hdenom] at hd; exact hd
    · rintro ⟨hd, hb⟩
      have hxS : x ∈ chartOverlap i j := hoverlap.mpr hd
      refine ⟨hxS, ?_⟩
      have hdne : (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j ≠ 0 := by
        rw [hdenom] at hd; exact hd
      funext b
      rw [transitionMap]
      have hEb := (hb b (Finset.mem_univ b))
      rw [Set.mem_ofPred_eq, hE b, sub_eq_zero] at hEb
      rw [eq_div_iff hdne]
      exact hEb
  rw [hgraph]
  refine IsSemialgebraicSetC.inter ?_ ?_
  · exact (isSemialgebraicSetC_complexPolyZero (hcoord i j)).compl
  · exact IsSemialgebraicSetC.biInter_finset _
      (fun b _ => isSemialgebraicSetC_complexPolyZero (transPoly i j b))

/-! ### PART B — the transition map is the chart composite `φⱼ⁻¹ ∘ φᵢ`, and a bijection -/

set_option linter.unusedSectionVars false in
/-- The denominator-free transition map equals the chart composite `φⱼ⁻¹ ∘ φᵢ`: the representative
scalar of `mkLine (insertNth i 1 x)` cancels in the ratio. -/
theorem transitionMap_eq_chartInv_chartMap (i j : Fin (k + 1)) (x : Fin k → Ri R) :
    transitionMap i j x = chartInv j (chartMap i x) := by
  obtain ⟨c, hc, hrep⟩ := exists_rep_smul (Fin.insertNth i 1 x) (insertNth_one_ne_zero i x)
  funext b
  rw [transitionMap, chartInv, chartMap, hrep, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, mul_div_mul_left _ _ hc]

set_option linter.unusedSectionVars false in
/-- The `i`-th representative coordinate of `chartMap i x` is the (nonzero) scalar `c`; in particular
`chartMap i x ∈ chartSet i`. -/
theorem chartMap_rep_self_ne_zero (i : Fin (k + 1)) (x : Fin k → Ri R) :
    (chartMap i x).rep i ≠ 0 := by
  obtain ⟨c, hc, hrep⟩ := exists_rep_smul (Fin.insertNth i 1 x) (insertNth_one_ne_zero i x)
  rw [chartMap, hrep, Pi.smul_apply, Fin.insertNth_apply_same, smul_eq_mul, mul_one]
  exact hc

set_option linter.unusedSectionVars false in
/-- On the overlap, the `j`-th representative coordinate of `chartMap i x` is nonzero, so
`chartMap i x ∈ chartSet j`. -/
theorem chartMap_rep_ne_zero_of_mem_overlap (i j : Fin (k + 1)) {x : Fin k → Ri R}
    (hx : x ∈ chartOverlap i j) : (chartMap i x).rep j ≠ 0 := by
  obtain ⟨c, hc, hrep⟩ := exists_rep_smul (Fin.insertNth i 1 x) (insertNth_one_ne_zero i x)
  rw [chartOverlap_eq, Set.mem_ofPred_eq] at hx
  rw [chartMap, hrep, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or]
  exact ⟨hc, hx⟩

set_option linter.unusedSectionVars false in
/-- The transition map sends the overlap `φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ)` into `φⱼ⁻¹(𝒰ⱼ ∩ 𝒰ᵢ)`. -/
theorem transitionMap_mapsTo (i j : Fin (k + 1)) :
    Set.MapsTo (transitionMap i j) (chartOverlap i j : Set (Fin k → Ri R)) (chartOverlap j i) := by
  intro x hx
  rw [transitionMap_eq_chartInv_chartMap]
  have hj : (chartMap i x).rep j ≠ 0 := chartMap_rep_ne_zero_of_mem_overlap i j hx
  have hi : (chartMap i x).rep i ≠ 0 := chartMap_rep_self_ne_zero i x
  -- `chartMap j (chartInv j (chartMap i x)) = chartMap i x`
  have hround : chartMap j (chartInv j (chartMap i x)) = chartMap i x :=
    chartMap_chartInv j (chartMap i x) hj
  -- membership via the preimage definition of `chartOverlap`
  show chartMap j (chartInv j (chartMap i x)) ∈ chartSet j ∩ chartSet i
  rw [hround, Set.mem_inter_iff, chartSet_eq, chartSet_eq, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  exact ⟨hj, hi⟩

set_option linter.unusedSectionVars false in
/-- **BPR §4.7 (Note, part 5 — bijection).** The transition map `φⱼ⁻¹ ∘ φᵢ` is a bijection from
`φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ)` to `φⱼ⁻¹(𝒰ⱼ ∩ 𝒰ᵢ)`, with inverse `φᵢ⁻¹ ∘ φⱼ`. -/
theorem transitionMap_bijOn (i j : Fin (k + 1)) :
    Set.BijOn (transitionMap i j) (chartOverlap i j : Set (Fin k → Ri R)) (chartOverlap j i) := by
  -- round trip: `transitionMap j i (transitionMap i j x) = x` on the overlap
  have hround : ∀ x ∈ (chartOverlap i j : Set (Fin k → Ri R)),
      transitionMap j i (transitionMap i j x) = x := by
    intro x hx
    rw [transitionMap_eq_chartInv_chartMap, transitionMap_eq_chartInv_chartMap]
    have hj : (chartMap i x).rep j ≠ 0 := chartMap_rep_ne_zero_of_mem_overlap i j hx
    rw [chartMap_chartInv j (chartMap i x) hj, chartInv_chartMap]
  -- reverse round trip on `chartOverlap j i`
  have hround' : ∀ x ∈ (chartOverlap j i : Set (Fin k → Ri R)),
      transitionMap i j (transitionMap j i x) = x := by
    intro x hx
    rw [transitionMap_eq_chartInv_chartMap, transitionMap_eq_chartInv_chartMap]
    have hi : (chartMap j x).rep i ≠ 0 := chartMap_rep_ne_zero_of_mem_overlap j i hx
    rw [chartMap_chartInv i (chartMap j x) hi, chartInv_chartMap]
  refine ⟨transitionMap_mapsTo i j, ?_, ?_⟩
  · -- injective on the overlap via the left inverse
    intro a ha b hb hab
    have := congrArg (transitionMap j i) hab
    rwa [hround a ha, hround b hb] at this
  · -- surjective onto the overlap via the right inverse `transitionMap j i`
    intro y hy
    refine ⟨transitionMap j i y, transitionMap_mapsTo j i hy, hround' y hy⟩

/-- **BPR §4.7 (Note, part 5).** `φⱼ⁻¹ ∘ φᵢ` is a semialgebraic bijection from `φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ)` to
`φⱼ⁻¹(𝒰ⱼ ∩ 𝒰ᵢ)`. -/
theorem transitionMap_isSemialgebraicBijection (i j : Fin (k + 1)) :
    IsSemialgebraicFunctionC (chartOverlap i j : Set (Fin k → Ri R)) (transitionMap i j)
      ∧ Set.BijOn (transitionMap i j) (chartOverlap i j : Set (Fin k → Ri R)) (chartOverlap j i) :=
  ⟨isSemialgebraicFunctionC_transitionMap i j, transitionMap_bijOn i j⟩

end Azurite.BPR.Chapter4
