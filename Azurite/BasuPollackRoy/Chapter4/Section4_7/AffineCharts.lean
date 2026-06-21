import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveSpace

/-!
# BPR §4.7: the affine charts of projective space

Let `R` be a real closed field and `C = R[i] = Ri R`. For `i = 0, …, k` the `i`-th *affine chart*
`φᵢ : Cᵏ → ℙ_k(C)` sends `(x₁, …, x_k)` to `(x₁ : ⋯ : x_{i-1} : 1 : x_i : ⋯ : x_k)` — that is, it
inserts a `1` in coordinate `i`. Its image `𝒰ᵢ = φᵢ(Cᵏ)` is the set of points whose `i`-th
homogeneous coordinate is nonzero, and `φᵢ⁻¹` divides through by that coordinate and drops it. The
charts cover projective space: `⋃ᵢ 𝒰ᵢ = ℙ_k(C)`.

(The semialgebraic structure of the overlaps `φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ)` and the transition maps
`φⱼ⁻¹ ∘ φᵢ`, which requires the real identification `C ≅ R²`, is treated separately.)
-/

namespace Azurite.BPR.Chapter4

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

set_option linter.unusedSectionVars false in
/-- Inserting a `1` in coordinate `i` gives a nonzero vector. -/
theorem insertNth_one_ne_zero (i : Fin (k + 1)) (x : Fin k → Ri R) :
    (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) ≠ 0 := by
  intro h
  have := congrFun h i
  rw [Fin.insertNth_apply_same] at this
  simp at this

/-- **BPR §4.7 (affine chart `φᵢ`).** The map `Cᵏ → ℙ_k(C)`, `(x₁, …, x_k) ↦
(x₁ : ⋯ : x_{i-1} : 1 : x_i : ⋯ : x_k)`, inserting a `1` in homogeneous coordinate `i`. -/
noncomputable def chartMap (i : Fin (k + 1)) (x : Fin k → Ri R) : complexProjectiveSpace R k :=
  mkLine (Fin.insertNth i 1 x) (insertNth_one_ne_zero i x)

/-- **BPR §4.7 (chart domain `𝒰ᵢ`).** The image `φᵢ(Cᵏ)` of the `i`-th affine chart. -/
def chartSet (i : Fin (k + 1)) : Set (complexProjectiveSpace R k) :=
  Set.range (chartMap i)

/-- **BPR §4.7 (chart inverse `φᵢ⁻¹`).** On `𝒰ᵢ`, `φᵢ⁻¹(x₀ : ⋯ : x_k) =
(x₀/xᵢ, …, x_{i-1}/xᵢ, x_{i+1}/xᵢ, …, x_k/xᵢ)`: divide every other coordinate by `xᵢ`. -/
noncomputable def chartInv (i : Fin (k + 1)) (p : complexProjectiveSpace R k) : Fin k → Ri R :=
  fun j => p.rep (i.succAbove j) / p.rep i

set_option linter.unusedSectionVars false in
/-- The canonical representative gives back the point. -/
theorem mkLine_rep (p : complexProjectiveSpace R k) :
    mkLine p.rep p.rep_nonzero = p :=
  Projectivization.mk_rep p

set_option linter.unusedSectionVars false in
/-- A representative of `mkLine v` is a nonzero scalar multiple of `v`. -/
theorem exists_rep_smul (v : Fin (k + 1) → Ri R) (hv : v ≠ 0) :
    ∃ c : Ri R, c ≠ 0 ∧ (mkLine v hv).rep = c • v :=
  (mkLine_eq_mkLine_iff _ _ _ _).mp (mkLine_rep (mkLine v hv))

set_option linter.unusedSectionVars false in
/-- `φᵢ` is injective with `φᵢ⁻¹` as a left inverse: `φᵢ⁻¹(φᵢ(x)) = x`. -/
theorem chartInv_chartMap (i : Fin (k + 1)) (x : Fin k → Ri R) :
    chartInv i (chartMap i x) = x := by
  obtain ⟨c, hc, hrep⟩ := exists_rep_smul (Fin.insertNth i 1 x) (insertNth_one_ne_zero i x)
  funext j
  simp only [chartInv, chartMap, hrep, Pi.smul_apply, Fin.insertNth_apply_succAbove,
    Fin.insertNth_apply_same, smul_eq_mul, mul_one]
  rw [mul_comm, mul_div_assoc, div_self hc, mul_one]

set_option linter.unusedSectionVars false in
/-- On `𝒰ᵢ` (where the `i`-th coordinate is nonzero), `φᵢ` recovers the point from `φᵢ⁻¹`:
`φᵢ(φᵢ⁻¹(p)) = p`. -/
theorem chartMap_chartInv (i : Fin (k + 1)) (p : complexProjectiveSpace R k) (h : p.rep i ≠ 0) :
    chartMap i (chartInv i p) = p := by
  have heq : Fin.insertNth i (1 : Ri R) (chartInv i p) = (p.rep i)⁻¹ • p.rep := by
    funext m
    refine Fin.succAboveCases i ?_ (fun j => ?_) m
    · rw [Fin.insertNth_apply_same, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h]
    · rw [Fin.insertNth_apply_succAbove, Pi.smul_apply, smul_eq_mul, chartInv, div_eq_inv_mul]
  rw [chartMap]
  conv_rhs => rw [← mkLine_rep p]
  rw [mkLine_eq_mkLine_iff]
  exact ⟨(p.rep i)⁻¹, inv_ne_zero h, heq⟩

set_option linter.unusedSectionVars false in
/-- **BPR §4.7 (Note).** `𝒰ᵢ = φᵢ(Cᵏ)` is exactly the set of points whose `i`-th homogeneous
coordinate is nonzero. -/
theorem chartSet_eq (i : Fin (k + 1)) :
    chartSet i = {p : complexProjectiveSpace R k | p.rep i ≠ 0} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨c, hc, hrep⟩ := exists_rep_smul (Fin.insertNth i 1 x) (insertNth_one_ne_zero i x)
    rw [Set.mem_setOf_eq, chartMap, hrep, Pi.smul_apply, Fin.insertNth_apply_same, smul_eq_mul,
      mul_one]
    exact hc
  · intro h
    exact ⟨chartInv i p, chartMap_chartInv i p h⟩

set_option linter.unusedSectionVars false in
/-- **BPR §4.7 (Note).** The affine charts cover projective space: `⋃ᵢ 𝒰ᵢ = ℙ_k(C)`. -/
theorem iUnion_chartSet :
    (⋃ i : Fin (k + 1), chartSet i) = (Set.univ : Set (complexProjectiveSpace R k)) := by
  rw [Set.eq_univ_iff_forall]
  intro p
  rw [Set.mem_iUnion]
  obtain ⟨i, hi⟩ : ∃ i, p.rep i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply p.rep_nonzero
    funext i
    exact hcon i
  exact ⟨i, by rw [chartSet_eq]; exact hi⟩

end Azurite.BPR.Chapter4
