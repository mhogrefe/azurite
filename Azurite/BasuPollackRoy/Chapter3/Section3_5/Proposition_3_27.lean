import Azurite.BasuPollackRoy.Chapter3.Section3_5.Proposition_3_26

/-! # BPR §3.5, Proposition 3.27 — curve velocities lie in the tangent space

**Let `x` be a point of the `𝒮^∞` submanifold `M` in `R^k` of dimension `ℓ`, and let
`γ : [−1, 1] → R^k` be an `𝒮^∞` curve contained in `M` with `γ(0) = x`. Then the tangent
vector `x + γ′(0)` is contained in the tangent space `T_x(M)`.**

With a chart `ϕ : U → Ω` at `x` and `T_x(M) = x + d\varphi(0)(R^ℓ × {0})`, the claim is
`γ′(0) ∈ W := dϕ(0)(R^ℓ × {0})`. The curve `c = ϕ⁻¹ ∘ γ` lands in `R^ℓ × {0}` (since
`γ ⊆ M`), so its velocity `c′(0)` lies in `R^ℓ × {0}`; and `γ = ϕ ∘ c`, so by the chain
rule `γ′(0) = dϕ(0)(c′(0)) ∈ dϕ(0)(R^ℓ × {0}) = W`. Both steps are the chain rule
(`hasPartialDerivAtIn_comp`); the curve is modeled as `(Fin 1 → R) → (Fin k → R)` with the
parameter the `0`-th coordinate, and `γ′(0)` is the velocity in that direction. -/

namespace Azurite.BPR

open MvPolynomial

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Partial derivatives only depend on the function's values on the domain: if `c₁ = c₂`
on `U` (with `x ∈ U`), the `i`-th partial of `c₁` at `x` is also that of `c₂`. -/
theorem HasPartialDerivAtIn.congr {c₁ c₂ : (Fin k → R) → R} {U : Set (Fin k → R)}
    {i : Fin k} {x : Fin k → R} {d : R} (hcong : ∀ z ∈ U, c₁ z = c₂ z) (hx : x ∈ U)
    (h : HasPartialDerivAtIn c₁ U i x d) : HasPartialDerivAtIn c₂ U i x d := by
  refine LimitAtInR.congr (fun t ht _ => ?_) h
  show (c₁ (Function.update x i t) - c₁ (Function.update x i (x i))) / (t - x i)
      = (c₂ (Function.update x i t) - c₂ (Function.update x i (x i))) / (t - x i)
  rw [hcong _ ht, hcong (Function.update x i (x i)) (by rw [Function.update_eq_self]; exact hx)]

/-- **BPR Proposition 3.27.** Let `ϕ : U → Ω` be a chart at `x` for the `𝒮^∞` submanifold
`M` of dimension `ℓ` (with `ϕ(0) = x`, `ϕ(U ∩ (R^ℓ × {0})) = M ∩ Ω`), and let `g` be the
partial derivatives of `ϕ`. If `γ : Idom → R^k` (`Idom` a semialgebraic open neighborhood
of `0` in `R^1`) is a curve into `M` with `γ(0) = x` and velocity `γ′` at `0`, then
`γ′ ∈ dϕ(0)(R^ℓ × {0})` — i.e. `x + γ′(0) ∈ T_x(M)`. -/
theorem proposition_3_27 {M U Ω : Set (Fin k → R)}
    {ϕ ϕinv : (Fin k → R) → (Fin k → R)} {x : Fin k → R}
    {g : Fin k → Fin k → (Fin k → R) → R}
    {Idom : Set (Fin 1 → R)} {γ : (Fin 1 → R) → (Fin k → R)} {γ' : Fin k → R}
    (hchart : IsSInftyDiffeomorphism U Ω ϕ ϕinv)
    (h0U : (0 : Fin k → R) ∈ U) (hϕ0 : ϕ 0 = x)
    (hslice : ϕ '' (U ∩ coordSubspace k ℓ) = M ∩ Ω)
    (hg : ∀ l j, ∀ z ∈ U, HasPartialDerivAtIn (fun w => ϕ w l) U j z (g l j z))
    (hgcont : ∀ l j, ContinuousOn (scalarFun (g l j)) U)
    (hIopen : IsOpen Idom) (h0I : (0 : Fin 1 → R) ∈ Idom)
    (hγΩ : Set.MapsTo γ Idom Ω) (hγM : ∀ s ∈ Idom, γ s ∈ M) (hγ0 : γ 0 = x)
    (hγderiv : ∀ m, HasPartialDerivAtIn (fun s => γ s m) Idom 0 (0 : Fin 1 → R) (γ' m)) :
    γ' ∈ Submodule.map (Matrix.mulVecLin (jacobianMatrix g 0)) (coordSubmodule k ℓ) := by
  classical
  set A : Matrix (Fin k) (Fin k) R := jacobianMatrix g 0 with hAdef
  -- `ϕ` is semialgebraic on `U` (from `ϕ ∈ 𝒮^∞`)
  have hSf : ∀ l, IsSemialgebraicFunction U (scalarFun (fun y => ϕ y l)) :=
    fun l => ((isSFunction_succ_iff.mp ((mem_sClassInfty_iff.mp hchart.mem_sClassInfty 1).2 l)).1).1
  -- partial-derivative data of `ϕ⁻¹` (from `ϕ⁻¹ ∈ 𝒮^∞`)
  have hϕinv1 : ∀ l, IsSFunction 1 Ω (fun y => ϕinv y l) :=
    fun l => (mem_sClassInfty_iff.mp hchart.inv_mem_sClassInfty 1).2 l
  choose g' hg' hgS' using fun l j => (isSFunction_succ_iff.mp (hϕinv1 l)).2 j
  have hSf' : ∀ l, IsSemialgebraicFunction Ω (scalarFun (fun y => ϕinv y l)) :=
    fun l => ((isSFunction_succ_iff.mp (hϕinv1 l)).1).1
  have hgcont' : ∀ l j, ContinuousOn (scalarFun (g' l j)) Ω := fun l j => (hgS' l j).2
  have hϕinvx : ϕinv x = 0 := by rw [← hϕ0]; exact hchart.invOn.1 h0U
  -- `ϕ⁻¹` maps `Ω → U`
  have hϕinvMaps : Set.MapsTo ϕinv Ω U := by
    intro y hy
    obtain ⟨u, huU, hϕu⟩ := hchart.bijOn.surjOn hy
    rw [← hϕu, hchart.invOn.1 huU]; exact huU
  -- `ϕ⁻¹` carries `M ∩ Ω` into `R^ℓ × {0}`
  have hcoord : ∀ y, y ∈ M ∩ Ω → ϕinv y ∈ coordSubspace k ℓ := by
    intro y hy
    rw [← hslice] at hy
    obtain ⟨u, ⟨huU, hucoord⟩, hϕu⟩ := hy
    rw [← hϕu, hchart.invOn.1 huU]; exact hucoord
  -- the composite curve `c = ϕ⁻¹ ∘ γ` and its velocity (chain rule)
  set c'val : Fin k → R := fun m => ∑ j, g' m j (γ 0) * γ' j with hc'valdef
  have hc1 : ∀ m, HasPartialDerivAtIn (fun w => ϕinv (γ w) m) Idom 0 (0 : Fin 1 → R)
      (c'val m) := fun m =>
    hasPartialDerivAtIn_comp hchart.isOpen_target hγΩ (hSf' m) (hg' m)
      (fun j => hgcont' m j) h0I hγderiv
  -- `c′(0) ∈ R^ℓ × {0}`: the high components of `c` vanish identically
  have hc'coord : c'val ∈ coordSubmodule k ℓ := by
    intro m hm
    have hconst : HasPartialDerivAtIn (fun w => ϕinv (γ w) m) Idom 0 (0 : Fin 1 → R) 0 := by
      refine hasDerivAtIn_of_constOn (c := 0) (fun t ht => ?_) ?_
      · show ϕinv (γ (Function.update 0 0 t)) m = 0
        exact hcoord _ ⟨hγM _ ht, hγΩ ht⟩ m hm
      · show ϕinv (γ (Function.update 0 0 ((0 : Fin 1 → R) 0))) m = 0
        rw [Function.update_eq_self, hγ0, hϕinvx]; rfl
    exact HasPartialDerivAtIn.unique hIopen h0I (hc1 m) hconst
  -- `γ = ϕ ∘ c` on `Idom`, so the chain rule computes `γ′`
  have hcMaps : Set.MapsTo (fun w => ϕinv (γ w)) Idom U := fun s hs => hϕinvMaps (hγΩ hs)
  have hc2 : ∀ l, HasPartialDerivAtIn (fun w => γ w l) Idom 0 (0 : Fin 1 → R)
      (∑ m, g l m (ϕinv (γ 0)) * c'val m) := by
    intro l
    have hcomp := hasPartialDerivAtIn_comp hchart.isOpen_source hcMaps (hSf l) (hg l)
      (fun m => hgcont l m) h0I hc1
    -- `hcomp : HasPartialDerivAtIn (fun w => ϕ (ϕinv (γ w)) l) Idom 0 0 (∑ m, g l m (ϕinv (γ 0)) * c'val m)`
    refine HasPartialDerivAtIn.congr (fun w hw => ?_) h0I hcomp
    show ϕ (ϕinv (γ w)) l = γ w l
    rw [hchart.invOn.2 (hγΩ hw)]
  -- `γ′ = A · c′(0)`, with `c′(0) ∈ R^ℓ × {0}`, hence `γ′ ∈ W`
  have hγ'eq : γ' = A.mulVec c'val := by
    funext l
    have huniq := HasPartialDerivAtIn.unique hIopen h0I (hγderiv l) (hc2 l)
    rw [huniq, show ϕinv (γ 0) = 0 by rw [hγ0, hϕinvx]]
    show ∑ m, g l m 0 * c'val m = A.mulVec c'val l
    simp only [hAdef, Matrix.mulVec, dotProduct, jacobianMatrix, Matrix.of_apply]
  rw [hγ'eq]
  exact Submodule.mem_map.mpr ⟨c'val, hc'coord, by rw [Matrix.mulVecLin_apply]⟩

end Azurite.BPR
