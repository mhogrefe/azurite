/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_5.Proposition_3_27
import Azurite.BasuPollackRoy.Chapter3.Section3_5.Proposition_3_28
import Azurite.BasuPollackRoy.Chapter3.Section3_5.TangentSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis

/-! # BPR §3.5, Proposition 3.28(b) — a submanifold contained in another has no larger dimension

**Proposition 3.28(b).** If `V'` (dimension `j`) is contained in `V` (dimension `i`), both
`𝒮^∞` submanifolds of `R^k`, then `j ≤ i`.

The proof rests on the dimension theory of the tangent space. First, the chart derivative
`dϕ(0)` is invertible — the chain rule applied to `ϕ⁻¹ ∘ ϕ = id` gives `dϕ⁻¹(x) · dϕ(0) = I`,
so `dϕ(0)` is a unit and `dϕ(0)·` is injective. Hence `T_x(M)` is the injective image of an
`ℓ`-dimensional coordinate subspace and so has dimension `ℓ`. Finally, at a common point
`x ∈ V' ⊆ V`, every tangent vector to `V'` is the velocity of a curve lying in `V' ⊆ V`,
hence (Proposition 3.27) a tangent vector to `V`; so `T_x(V') ⊆ T_x(V)` and
`j = dim T_x(V') ≤ dim T_x(V) = i`. -/

namespace Azurite.BPR

open MvPolynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- **The chart derivative `dϕ(0)` is invertible.** Applying the chain rule to
`ϕ⁻¹ ∘ ϕ = id` (and matching the identity's partials by uniqueness) gives
`dϕ⁻¹(ϕ 0) · dϕ(0) = I`, so the Jacobian `dϕ(0) = jacobianMatrix g 0` is a unit. -/
theorem chart_dϕ0_isUnit [Nonempty (Fin k)] {U Ω : Set (Fin k → R)}
    {ϕ ϕinv : (Fin k → R) → (Fin k → R)} {g : Fin k → Fin k → (Fin k → R) → R}
    (hchart : IsSInftyDiffeomorphism U Ω ϕ ϕinv) (h0U : (0 : Fin k → R) ∈ U)
    (hg : ∀ l j, ∀ z ∈ U, HasPartialDerivAtIn (fun w => ϕ w l) U j z (g l j z)) :
    IsUnit (jacobianMatrix g 0) := by
  classical
  -- partial-derivative data of `ϕ⁻¹`
  have hϕinv1 : ∀ l, IsSFunction 1 Ω (fun y => ϕinv y l) :=
    fun l => (mem_sClassInfty_iff.mp hchart.inv_mem_sClassInfty 1).2 l
  choose g' hg' hg'S using fun l j => (isSFunction_succ_iff.mp (hϕinv1 l)).2 j
  have hSf' : ∀ l, IsSemialgebraicFunction Ω (scalarFun (fun y => ϕinv y l)) :=
    fun l => ((isSFunction_succ_iff.mp (hϕinv1 l)).1).1
  have hg'cont : ∀ l j, ContinuousOn (scalarFun (g' l j)) Ω := fun l j => (hg'S l j).2
  -- `dϕ⁻¹(ϕ 0) · dϕ(0) = I`, entrywise
  have key : ∀ l j : Fin k,
      (∑ m, g' l m (ϕ 0) * g m j 0) = (1 : Matrix (Fin k) (Fin k) R) l j := by
    intro l j
    have hcomp := hasPartialDerivAtIn_comp hchart.isOpen_target hchart.bijOn.mapsTo
      (hSf' l) (hg' l) (fun m => hg'cont l m) h0U (fun m => hg m j 0 h0U)
    -- `ϕ⁻¹_l ∘ ϕ = id_l` on `U`, so it has the identity's partial by congruence + uniqueness
    have hcong : HasPartialDerivAtIn (fun z => z l) U j 0 (∑ m, g' l m (ϕ 0) * g m j 0) := by
      refine HasPartialDerivAtIn.congr (fun z hz => ?_) h0U hcomp
      show ϕinv (ϕ z) l = z l
      rw [hchart.invOn.1 hz]
    have huniq := HasPartialDerivAtIn.unique hchart.isOpen_source h0U hcong
      (hasPartialDerivAtIn_coord U l j 0)
    rw [huniq, Matrix.one_apply]
  have hmul : jacobianMatrix g' (ϕ 0) * jacobianMatrix g 0 = 1 := by
    ext l j
    rw [Matrix.mul_apply]
    exact key l j
  exact ⟨⟨jacobianMatrix g 0, jacobianMatrix g' (ϕ 0),
    mul_eq_one_comm.mp hmul, hmul⟩, rfl⟩

/-- The chart derivative acts injectively. -/
theorem chart_dϕ0_mulVec_injective [Nonempty (Fin k)] {U Ω : Set (Fin k → R)}
    {ϕ ϕinv : (Fin k → R) → (Fin k → R)} {g : Fin k → Fin k → (Fin k → R) → R}
    (hchart : IsSInftyDiffeomorphism U Ω ϕ ϕinv) (h0U : (0 : Fin k → R) ∈ U)
    (hg : ∀ l j, ∀ z ∈ U, HasPartialDerivAtIn (fun w => ϕ w l) U j z (g l j z)) :
    Function.Injective (jacobianMatrix g 0).mulVec :=
  Matrix.mulVec_injective_iff_isUnit.mpr (chart_dϕ0_isUnit hchart h0U hg)

/-! ### Dimension of the tangent space -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The coordinate subspace `R^ℓ × {0}` of `R^k` has dimension `ℓ` (when `ℓ ≤ k`). -/
theorem finrank_coordSubmodule (hℓk : ℓ ≤ k) :
    Module.finrank R (coordSubmodule (R := R) k ℓ) = ℓ := by
  classical
  set b : {j : Fin k // (j : ℕ) < ℓ} → (Fin k → R) := fun jj => Pi.single jj.val 1 with hb_def
  have hb_li : LinearIndependent R b := by
    have hbasis := (Pi.basisFun R (Fin k)).linearIndependent.comp
      (fun jj : {j : Fin k // (j : ℕ) < ℓ} => jj.val) Subtype.val_injective
    have hbeq : b = ⇑(Pi.basisFun R (Fin k)) ∘ (fun jj : {j : Fin k // (j : ℕ) < ℓ} => jj.val) := by
      funext jj
      rw [hb_def, Function.comp_apply, Pi.basisFun_apply]
    rw [hbeq]; exact hbasis
  have hrange : Set.range b = (fun j : Fin k => Pi.single j (1 : R)) '' {j | (j : ℕ) < ℓ} := by
    ext v
    simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq, hb_def]
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩; exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
  rw [coordSubmodule_eq_span, ← hrange, finrank_span_eq_card hb_li]
  have e : {j : Fin k // (j : ℕ) < ℓ} ≃ Fin ℓ :=
    { toFun := fun jj => ⟨jj.val.val, jj.property⟩
      invFun := fun a => ⟨⟨a.val, a.isLt.trans_le hℓk⟩, a.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- **The tangent space has dimension `ℓ`** (for `ℓ ≤ k`): `dϕ(0)` is invertible, so it maps
the `ℓ`-dimensional `R^ℓ × {0}` isomorphically onto `tangentSpaceDir`. -/
theorem finrank_tangentSpaceDir [Nonempty (Fin k)] {U Ω : Set (Fin k → R)}
    {ϕ ϕinv : (Fin k → R) → (Fin k → R)} {g : Fin k → Fin k → (Fin k → R) → R}
    (hchart : IsSInftyDiffeomorphism U Ω ϕ ϕinv) (h0U : (0 : Fin k → R) ∈ U)
    (hg : ∀ l j, ∀ z ∈ U, HasPartialDerivAtIn (fun w => ϕ w l) U j z (g l j z))
    (hℓk : ℓ ≤ k) :
    Module.finrank R (tangentSpaceDir g ℓ) = ℓ := by
  have hinj' : Function.Injective ⇑(Matrix.mulVecLin (jacobianMatrix g 0)) :=
    chart_dϕ0_mulVec_injective hchart h0U hg
  rw [tangentSpaceDir,
    ← LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective _ hinj' (coordSubmodule k ℓ))]
  exact finrank_coordSubmodule hℓk

/-! ### Proposition 3.28(b) -/

/-- **BPR Proposition 3.28(b).** If `V'` (dimension `j`) is contained in `V` (dimension `i`),
both `𝒮^∞` submanifolds of `R^k` (`j, i ≤ k`), and `V'` is nonempty, then `j ≤ i`. The
tangent space `T_x(V')` is a subspace of `T_x(V)` — every tangent vector to `V'` is the
velocity of a curve in `V' ⊆ V`, hence a tangent vector to `V` (Proposition 3.27) — and the
two tangent spaces have dimensions `j` and `i`. -/
theorem proposition_3_28b [Nonempty (Fin k)] {i j : ℕ} {V V' : Set (Fin k → R)}
    (hV : IsSInftySubmanifold i V) (hV' : IsSInftySubmanifold j V') (hV'V : V' ⊆ V)
    (hjk : j ≤ k) (hik : i ≤ k) {x₀ : Fin k → R} (hx₀ : x₀ ∈ V') :
    j ≤ i := by
  classical
  -- charts at `x₀`
  obtain ⟨U, Ω, ϕ, ϕinv, hchart, h0U, hxΩ, hϕ0, hslice⟩ := hV.2 x₀ (hV'V hx₀)
  obtain ⟨U', Ω', ϕ', ϕinv', hchart', h0U', hxΩ', hϕ'0, hslice'⟩ := hV'.2 x₀ hx₀
  -- partial-derivative data of both charts
  have hϕ1 : ∀ l, IsSFunction 1 U (fun z => ϕ z l) :=
    fun l => (mem_sClassInfty_iff.mp hchart.mem_sClassInfty 1).2 l
  choose g hg hgS using fun l j' => (isSFunction_succ_iff.mp (hϕ1 l)).2 j'
  have hgcont : ∀ l j', ContinuousOn (scalarFun (g l j')) U := fun l j' => (hgS l j').2
  have hϕ'1 : ∀ l, IsSFunction 1 U' (fun z => ϕ' z l) :=
    fun l => (mem_sClassInfty_iff.mp hchart'.mem_sClassInfty 1).2 l
  choose g' hg' hg'S using fun l j' => (isSFunction_succ_iff.mp (hϕ'1 l)).2 j'
  have hg'cont : ∀ l j', ContinuousOn (scalarFun (g' l j')) U' := fun l j' => (hg'S l j').2
  have hSf' : ∀ l, IsSemialgebraicFunction U' (scalarFun (fun z => ϕ' z l)) :=
    fun l => ((isSFunction_succ_iff.mp (hϕ'1 l)).1).1
  -- monotonicity of the tangent direction
  have hmono : tangentSpaceDir g' j ≤ tangentSpaceDir g i := by
    intro v hv
    rw [tangentSpaceDir, Submodule.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    -- the curve `γ(s) = ϕ'((s 0) • u)` in `V' ⊆ V`, with velocity `dϕ'(0)(u)`
    set ρ : (Fin 1 → R) → (Fin k → R) := fun s => (s 0) • u with hρdef
    have hρcont : Continuous ρ := by
      have heq : ρ = polynomialMap (fun jj : Fin k => C (u jj) * X 0) := by
        funext s jj
        rw [hρdef]
        simp only [Pi.smul_apply, smul_eq_mul, polynomialMap, map_mul, eval_C, eval_X]
        ring
      rw [heq]; exact continuous_polynomialMap _
    have hρ0 : ρ 0 = 0 := by rw [hρdef]; simp
    have hρcoord : ∀ s, ρ s ∈ coordSubmodule k j := fun s => (coordSubmodule k j).smul_mem (s 0) hu
    set γ : (Fin 1 → R) → (Fin k → R) := fun s => ϕ' (ρ s) with hγdef
    set Idom : Set (Fin 1 → R) := ρ ⁻¹' U' ∩ γ ⁻¹' Ω with hIdef
    have h0I : (0 : Fin 1 → R) ∈ Idom := by
      refine ⟨?_, ?_⟩
      · show ρ 0 ∈ U'; rw [hρ0]; exact h0U'
      · show ϕ' (ρ 0) ∈ Ω; rw [hρ0, hϕ'0]; exact hxΩ
    have hρmaps : Set.MapsTo ρ Idom U' := fun _ hs => hs.1
    have hIopen : IsOpen Idom :=
      ContinuousOn.isOpen_inter_preimage
        ((hchart'.continuousOn_source).comp hρcont.continuousOn (fun _ hs => hs))
        (hchart'.isOpen_source.preimage hρcont) hchart.isOpen_target
    have hρderiv : ∀ l, HasPartialDerivAtIn (fun s => ρ s l) Idom 0 (0 : Fin 1 → R) (u l) := by
      intro l
      have hsl : (fun s : Fin 1 → R => ρ s l) = fun s => u l * s 0 + 0 := by
        funext s; rw [hρdef]
        show ((s 0) • u) l = u l * s 0 + 0
        rw [Pi.smul_apply, smul_eq_mul, mul_comm]; ring
      rw [hsl]
      show HasDerivAtIn
        (fun t : R => u l * (Function.update (0 : Fin 1 → R) (0 : Fin 1) t) (0 : Fin 1) + 0)
        {t : R | Function.update (0 : Fin 1 → R) (0 : Fin 1) t ∈ Idom}
        ((0 : Fin 1 → R) (0 : Fin 1)) (u l)
      have heq : (fun t : R => u l * (Function.update (0 : Fin 1 → R) (0 : Fin 1) t) (0 : Fin 1) + 0)
          = fun t => u l * t + 0 := by
        funext t; rw [Function.update_self]
      rw [heq]
      exact hasDerivAtIn_affine (u l) 0 _ _
    set γ' : Fin k → R := fun m => ∑ l, g' m l (ρ 0) * u l with hγ'def
    have hγderiv : ∀ m, HasPartialDerivAtIn (fun s => γ s m) Idom 0 (0 : Fin 1 → R) (γ' m) :=
      fun m => hasPartialDerivAtIn_comp hchart'.isOpen_source hρmaps (hSf' m) (hg' m)
        (fun l => hg'cont m l) h0I hρderiv
    have hγM : ∀ s ∈ Idom, γ s ∈ V := by
      intro s hs
      have hmem : γ s ∈ V' ∩ Ω' := by
        rw [hγdef, ← hslice']
        exact ⟨ρ s, ⟨hs.1, mem_coordSubmodule.mp (hρcoord s)⟩, rfl⟩
      exact hV'V hmem.1
    have hγ0 : γ 0 = x₀ := by show ϕ' (ρ 0) = x₀; rw [hρ0, hϕ'0]
    have hmem := proposition_3_27 hchart h0U hϕ0 hslice hg hgcont hIopen h0I
      (fun _ hs => hs.2) hγM hγ0 hγderiv
    -- `γ' = dϕ'(0)(u)`, so `dϕ'(0)(u) ∈ tangentSpaceDir g i`
    have hγ'eq : γ' = Matrix.mulVecLin (jacobianMatrix g' 0) u := by
      funext m
      rw [hγ'def, hρ0, Matrix.mulVecLin_apply]
      simp only [Matrix.mulVec, dotProduct, jacobianMatrix, Matrix.of_apply]
    rw [tangentSpaceDir, ← hγ'eq]
    exact hmem
  -- compare dimensions
  calc j = Module.finrank R (tangentSpaceDir g' j) := (finrank_tangentSpaceDir hchart' h0U' hg' hjk).symm
    _ ≤ Module.finrank R (tangentSpaceDir g i) := Submodule.finrank_mono hmono
    _ = i := finrank_tangentSpaceDir hchart h0U hg hik

end Azurite.BPR
