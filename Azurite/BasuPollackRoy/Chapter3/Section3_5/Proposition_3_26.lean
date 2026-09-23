import Azurite.BasuPollackRoy.Chapter3.Section3_5.OrthogonalProjection
import Azurite.BasuPollackRoy.Chapter3.Section3_5.SDiffeomorphism
import Azurite.BasuPollackRoy.Chapter3.Section3_5.InverseSmoothness
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # BPR §3.5, Proposition 3.26 — the tangent flat is first-order tangent

**Let `x` be a point of an `𝒮^∞` submanifold `M` of `R^k` of dimension `ℓ`, and let `π`
denote orthogonal projection onto the `ℓ`-flat `T_x(M)`. Then
`lim_{y ∈ M, y → x} ‖y − π(y)‖ / ‖y − x‖ = 0`.**

With a chart `ϕ : U → Ω` at `x` (`ϕ(0) = x`, `ϕ(U ∩ (R^ℓ × {0})) = M ∩ Ω`), the tangent
flat is `T_x(M) = x + dϕ(0)(R^ℓ × {0})`; its direction is the subspace
`W = dϕ(0)(R^ℓ × {0})` and `π(y) = x + orthProj W (y − x)` (`OrthogonalProjection.lean`).
The conclusion is `IsLittleO (fun y => y − π y) M x`, exactly BPR's limit.

The proof rests entirely on the first-order approximation `isLittleO_sub_totalDeriv`
(applied to `ϕ` at `0` and to `ϕ⁻¹` at `x`) and the closest-point property of the
projection:

* `ϕ(u) − x − dϕ(0)(u) = o(‖u‖)` for `u ∈ R^ℓ × {0}` (`ϕ ∈ 𝒮^∞ ⊆ 𝒮¹`);
* `ϕ⁻¹` is locally Lipschitz at `x`: from its own first-order approximation,
  `‖ϕ⁻¹(y)‖ ≤ C‖y − x‖` near `x` (`C = ‖dϕ⁻¹(x)‖ + 1`);
* for `y ∈ M ∩ Ω`, `u = ϕ⁻¹(y) ∈ R^ℓ × {0}` and `x + dϕ(0)(u) ∈ T_x(M)`, so the
  closest-point bound gives `‖y − π(y)‖ ≤ ‖ϕ(u) − x − dϕ(0)(u)‖ = o(‖u‖) = o(‖y − x‖)`. -/

namespace Azurite.BPR

open MvPolynomial

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- The coordinate subspace `R^ℓ × {0}` of `R^k` as a submodule. -/
def coordSubmodule (k ℓ : ℕ) : Submodule R (Fin k → R) where
  carrier := coordSubspace k ℓ
  add_mem' {a b} ha hb := by
    intro i hi; rw [Pi.add_apply, ha i hi, hb i hi, add_zero]
  zero_mem' := by intro i _; rfl
  smul_mem' c a ha := by
    intro i hi; rw [Pi.smul_apply, ha i hi, smul_zero]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem mem_coordSubmodule {v : Fin k → R} :
    v ∈ coordSubmodule (R := R) k ℓ ↔ v ∈ coordSubspace k ℓ := Iff.rfl

/-- **BPR Proposition 3.26.** For a point `x` of an `𝒮^∞` submanifold `M` of dimension `ℓ`,
there is a tangent-space direction `W` (the `ℓ`-flat `T_x(M) = x + W`) such that the
orthogonal projection `π(y) = x + orthProj W (y − x)` onto `T_x(M)` satisfies
`lim_{y ∈ M, y → x} ‖y − π(y)‖ / ‖y − x‖ = 0`, i.e. `y − π(y) = o(‖y − x‖)`. -/
theorem proposition_3_26 {M : Set (Fin k → R)} {x : Fin k → R}
    (hM : IsSInftySubmanifold ℓ M) (hx : x ∈ M) :
    ∃ W : Submodule R (Fin k → R),
      IsLittleO (fun y => y - (x + orthProj W (y - x))) M x := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `k = 0`: `M ⊆ {x}`, the limit is vacuous
    subst hk0
    refine ⟨⊥, isLittleO_of_bound fun r _ => ⟨1, one_pos, fun y _ hyne _ => ?_⟩⟩
    exact absurd (Subsingleton.elim y x) hyne
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  -- extract a chart at `x`
  obtain ⟨U, Ω, ϕ, ϕinv, hchart, h0U, hxΩ, hϕ0, hslice⟩ := hM.2 x hx
  -- partial-derivative data of `ϕ` (from `ϕ ∈ 𝒮^∞ ⊆ 𝒮¹`)
  have hϕ1 : ∀ l, IsSFunction 1 U (fun y => ϕ y l) :=
    fun l => (mem_sClassInfty_iff.mp hchart.mem_sClassInfty 1).2 l
  choose g hg hgS using fun l j => (isSFunction_succ_iff.mp (hϕ1 l)).2 j
  have hSf : ∀ l, IsSemialgebraicFunction U (scalarFun (fun y => ϕ y l)) :=
    fun l => ((isSFunction_succ_iff.mp (hϕ1 l)).1).1
  have hgcont : ∀ l j, ContinuousOn (scalarFun (g l j)) U := fun l j => (hgS l j).2
  -- `ϕ(u) − ϕ(0) − dϕ(0)(u) = o(‖u‖)`
  have hloϕ : IsLittleO
      (fun u => ϕ u - ϕ 0 - (jacobianMatrix g 0).mulVec (u - 0)) U 0 := by
    have h := isLittleO_sub_totalDeriv hchart.isOpen_source hSf hg hgcont h0U
    simpa only [totalDeriv_eq_mulVec] using h
  set A : Matrix (Fin k) (Fin k) R := jacobianMatrix g 0 with hAdef
  -- partial-derivative data of `ϕ⁻¹`
  have hϕinv1 : ∀ l, IsSFunction 1 Ω (fun y => ϕinv y l) :=
    fun l => (mem_sClassInfty_iff.mp hchart.inv_mem_sClassInfty 1).2 l
  choose g' hg' hgS' using fun l j => (isSFunction_succ_iff.mp (hϕinv1 l)).2 j
  have hSf' : ∀ l, IsSemialgebraicFunction Ω (scalarFun (fun y => ϕinv y l)) :=
    fun l => ((isSFunction_succ_iff.mp (hϕinv1 l)).1).1
  have hgcont' : ∀ l j, ContinuousOn (scalarFun (g' l j)) Ω := fun l j => (hgS' l j).2
  have hϕinvx : ϕinv x = 0 := by rw [← hϕ0]; exact hchart.invOn.1 h0U
  have hloϕinv : IsLittleO
      (fun y => ϕinv y - ϕinv x - (jacobianMatrix g' x).mulVec (y - x)) Ω x := by
    have h := isLittleO_sub_totalDeriv hchart.isOpen_target hSf' hg' hgcont' hxΩ
    simpa only [totalDeriv_eq_mulVec] using h
  set A' : Matrix (Fin k) (Fin k) R := jacobianMatrix g' x with hA'def
  -- the tangent-space direction `W = dϕ(0)(R^ℓ × {0})`
  set W : Submodule R (Fin k → R) :=
    Submodule.map (Matrix.mulVecLin A) (coordSubmodule k ℓ) with hWdef
  -- the Lipschitz constant for `ϕ⁻¹`
  set C : R := opNorm A' + 1 with hCdef
  have hC1 : (0 : R) < C + 1 := by have := opNorm_nonneg hk A'; rw [hCdef]; linarith
  refine ⟨W, isLittleO_of_bound fun r hr => ?_⟩
  set ε : R := r / (C + 1) with hεdef
  have hεpos : 0 < ε := div_pos hr hC1
  -- the local Lipschitz bound for `ϕ⁻¹` (from its first-order approximation, `r = 1`)
  obtain ⟨δ₁, hδ₁, hb₁⟩ := IsLittleO.bound hloϕinv one_pos
  have hCbound : ∀ y ∈ Ω, y ≠ x → euclideanNorm (y - x) < δ₁ →
      euclideanNorm (ϕinv y) ≤ C * euclideanNorm (y - x) := by
    intro y hyΩ hyne hyδ
    have h := hb₁ y hyΩ hyne hyδ
    rw [hϕinvx, sub_zero] at h
    -- `‖ϕinv y − A'(y−x)‖ < ‖y−x‖`, so `‖ϕinv y‖ ≤ ‖A'(y−x)‖ + ‖y−x‖ ≤ C‖y−x‖`
    have htri : euclideanNorm (ϕinv y)
        ≤ euclideanNorm (ϕinv y - A'.mulVec (y - x))
          + euclideanNorm (A'.mulVec (y - x)) := by
      have := euclideanNorm_add_le (ϕinv y - A'.mulVec (y - x)) (A'.mulVec (y - x))
      simpa using this
    have hmv : euclideanNorm (A'.mulVec (y - x)) ≤ opNorm A' * euclideanNorm (y - x) :=
      norm_mulVec_le hk A' (y - x)
    rw [hCdef]
    nlinarith [h, htri, hmv, euclideanNorm_nonneg (y - x)]
  -- the first-order bound for `ϕ` at `0` (tolerance `ε`)
  obtain ⟨δ₂, hδ₂, hb₂⟩ := IsLittleO.bound hloϕ hεpos
  -- a ball around `x` inside `Ω`
  obtain ⟨δ₃, hδ₃, hball⟩ := isOpen_iff_ball_self.mp hchart.isOpen_target x hxΩ
  -- the working radius
  refine ⟨min δ₁ (min δ₃ (δ₂ / (C + 1))), ?_, fun y hyM hyne hyδ => ?_⟩
  · exact lt_min hδ₁ (lt_min hδ₃ (by positivity))
  -- `y ∈ Ω`
  have hyΩ : y ∈ Ω :=
    hball ((mem_openBall_iff_norm hδ₃).mpr
      (lt_of_lt_of_le hyδ (le_trans (min_le_right _ _) (min_le_left _ _))))
  -- `u = ϕ⁻¹(y)` lies in `U ∩ (R^ℓ × {0})`, and `ϕ(u) = y`
  have hyMΩ : y ∈ ϕ '' (U ∩ coordSubspace k ℓ) := by rw [hslice]; exact ⟨hyM, hyΩ⟩
  obtain ⟨u, ⟨huU, hucoord⟩, hϕu⟩ := hyMΩ
  have huiv : ϕinv y = u := by rw [← hϕu]; exact hchart.invOn.1 huU
  have hune : u ≠ 0 := fun h => hyne (by rw [← hϕu, h, hϕ0])
  -- `‖u‖ ≤ C‖y − x‖`
  have hu_le : euclideanNorm u ≤ C * euclideanNorm (y - x) := by
    rw [← huiv]
    exact hCbound y hyΩ hyne (lt_of_lt_of_le hyδ (min_le_left _ _))
  -- `‖u‖ < δ₂`
  have hu_lt : euclideanNorm u < δ₂ := by
    have hyx : euclideanNorm (y - x) ≤ δ₂ / (C + 1) :=
      le_of_lt (lt_of_lt_of_le hyδ (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hCnn : (0 : R) ≤ C := by rw [hCdef]; have := opNorm_nonneg hk A'; linarith
    calc euclideanNorm u ≤ C * euclideanNorm (y - x) := hu_le
      _ ≤ C * (δ₂ / (C + 1)) := mul_le_mul_of_nonneg_left hyx hCnn
      _ < δ₂ := by rw [mul_div_assoc', div_lt_iff₀ hC1]; nlinarith [hδ₂, hCnn]
  -- `x + dϕ(0)(u) ∈ T_x(M)`, i.e. `A.mulVec u ∈ W`
  have hwmem : A.mulVec u ∈ W := by
    rw [hWdef]
    exact Submodule.mem_map.mpr ⟨u, mem_coordSubmodule.mpr hucoord,
      by rw [Matrix.mulVecLin_apply]⟩
  -- the closest-point identity `y − (x + A·u) = ϕ(u) − ϕ(0) − A(u − 0)`
  have heqvec : y - (x + A.mulVec u) = ϕ u - ϕ 0 - A.mulVec (u - 0) := by
    rw [sub_zero, hϕ0, hϕu]; abel
  -- assemble: closest point + first-order bound + Lipschitz
  have hϕbound := hb₂ u huU hune (by rw [sub_zero]; exact hu_lt)
  have hεC : ε * C ≤ r := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ hC1]
    have := opNorm_nonneg hk A'
    rw [hCdef]; nlinarith [hr]
  calc euclideanNorm (y - (x + orthProj W (y - x)))
      ≤ euclideanNorm (y - (x + A.mulVec u)) :=
        euclideanNorm_sub_affineProj_le W x y hwmem
    _ = euclideanNorm (ϕ u - ϕ 0 - A.mulVec (u - 0)) := by rw [heqvec]
    _ ≤ ε * euclideanNorm (u - 0) := le_of_lt hϕbound
    _ = ε * euclideanNorm u := by rw [sub_zero]
    _ ≤ ε * (C * euclideanNorm (y - x)) := mul_le_mul_of_nonneg_left hu_le hεpos.le
    _ = ε * C * euclideanNorm (y - x) := by ring
    _ ≤ r * euclideanNorm (y - x) :=
        mul_le_mul_of_nonneg_right hεC (euclideanNorm_nonneg _)

end Azurite.BPR
