/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_5.SClassClosure

/-! # BPR §3.5 — `𝒮^ℓ`-smoothness of the inverse (Proposition 3.24, closing sentence)

BPR finishes Proposition 3.24 with: *"Moreover, since `f` is of class `𝒮^ℓ`, we easily
get `d(f⁻¹)(x) = (df(f⁻¹(x)))⁻¹` and `f⁻¹ ∈ 𝒮^ℓ(V, U)`."* This file supplies that
"easily".

The argument has two analytic steps and one inductive step.

* **Partials from a first-order approximation** (`hasPartialDerivAtIn_of_isLittleO`): if
  `g(x) − g(x₀) − M(x − x₀) = o(‖x − x₀‖)` for a constant matrix `M`, then every partial
  derivative of `g` at `x₀` exists and equals the corresponding entry of `M` (restrict the
  vector little-o to a coordinate slice).

* **Differentiability of the inverse** (`isLittleO_inverse`, `hasPartialDerivAtIn_inverse`):
  transfer the first-order approximation of `f` at `x₀ = f⁻¹(y₀)` through the local inverse
  using the Lipschitz bound, giving `f⁻¹(y) − f⁻¹(y₀) − A⁻¹(y − y₀) = o(‖y − y₀‖)` with
  `A = df(x₀)`; hence `∂(f⁻¹)/∂y` exists and is the matrix inverse `(df(f⁻¹(y)))⁻¹`.

* **The induction** (`isSFunction_inverse`): the partials of `f⁻¹` are the entries of
  `(jacobianMatrix g ∘ f⁻¹)⁻¹`, which are `𝒮^ℓ` by the closure lemmas
  (`isSFunction_comp` for `g ∘ f⁻¹`, then `isSFunction_matrixInvEntry`), once `f⁻¹` itself
  is known `𝒮^ℓ` — exactly the inductive hypothesis. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### A working form of the little-o predicate -/

/-- Forward form of `o(‖·‖)`: a strict bound `‖f x‖ < r‖x − x₀‖` near `x₀`. -/
theorem IsLittleO.bound {k p : ℕ} {f : (Fin k → R) → (Fin p → R)} {M : Set (Fin k → R)}
    {x₀ : Fin k → R} (h : IsLittleO f M x₀) {r : R} (hr : 0 < r) :
    ∃ δ, 0 < δ ∧ ∀ x ∈ M, x ≠ x₀ → euclideanNorm (x - x₀) < δ →
      euclideanNorm (f x) < r * euclideanNorm (x - x₀) := by
  obtain ⟨δ, hδ, hb⟩ := h r hr
  refine ⟨δ, hδ, fun x hx hxne hxδ => ?_⟩
  have hq := hb x hx hxne hxδ
  rw [sub_zero, euclideanNorm_smul,
    abs_of_nonneg (inv_nonneg.mpr (euclideanNorm_nonneg _))] at hq
  have hpos : 0 < euclideanNorm (x - x₀) := euclideanNorm_pos_of_ne hxne
  rw [inv_mul_lt_iff₀ hpos] at hq
  rwa [mul_comm] at hq

/-- Constructor for `o(‖·‖)` from a `≤` bound `‖f x‖ ≤ r‖x − x₀‖` near `x₀`. -/
theorem isLittleO_of_bound {k p : ℕ} {f : (Fin k → R) → (Fin p → R)} {M : Set (Fin k → R)}
    {x₀ : Fin k → R}
    (h : ∀ r, 0 < r → ∃ δ, 0 < δ ∧ ∀ x ∈ M, x ≠ x₀ → euclideanNorm (x - x₀) < δ →
      euclideanNorm (f x) ≤ r * euclideanNorm (x - x₀)) :
    IsLittleO f M x₀ := by
  intro r hr
  obtain ⟨δ, hδ, hb⟩ := h (r / 2) (by positivity)
  refine ⟨δ, hδ, fun x hx hxne hxδ => ?_⟩
  rw [sub_zero, euclideanNorm_smul,
    abs_of_nonneg (inv_nonneg.mpr (euclideanNorm_nonneg _))]
  have hpos : 0 < euclideanNorm (x - x₀) := euclideanNorm_pos_of_ne hxne
  rw [inv_mul_lt_iff₀ hpos]
  have hq := hb x hx hxne hxδ
  nlinarith [hq, hpos, hr]

/-! ### Partial derivatives from a first-order approximation -/

/-- **Partials from a first-order approximation.** If `g(x) − g(x₀) − M(x − x₀) = o(‖x − x₀‖)`
on an open set `U`, then for all `a, b` the `b`-th partial derivative of the `a`-th
component of `g` at `x₀` exists and equals `M a b`. -/
theorem hasPartialDerivAtIn_of_isLittleO {k p : ℕ} {U : Set (Fin k → R)}
    {g : (Fin k → R) → (Fin p → R)} {M : Matrix (Fin p) (Fin k) R} {x₀ : Fin k → R}
    (hlo : IsLittleO (fun x => g x - g x₀ - M.mulVec (x - x₀)) U x₀)
    (a : Fin p) (b : Fin k) :
    HasPartialDerivAtIn (fun x => g x a) U b x₀ (M a b) := by
  intro r hr
  obtain ⟨δ, hδ, hb⟩ := IsLittleO.bound hlo hr
  refine ⟨δ, hδ, fun t htmem htne htδ => ?_⟩
  set x : Fin k → R := Function.update x₀ b t with hx
  have hxmem : x ∈ U := htmem
  have hxne : x ≠ x₀ := by
    intro h
    apply htne
    have := congrFun h b
    rwa [hx, Function.update_self] at this
  have hnorm : euclideanNorm (x - x₀) = |t - x₀ b| := by
    have h1 : euclideanNorm (x - x₀) ^ 2 = |t - x₀ b| ^ 2 := by
      rw [euclideanNorm_sq, hx, euclideanNormSq_update_sub, sq_abs]
    exact (pow_left_inj₀ (euclideanNorm_nonneg _) (abs_nonneg _) (by norm_num)).mp h1
  have hxδ' : euclideanNorm (x - x₀) < δ := by rw [hnorm]; exact htδ
  have hbb := hb x hxmem hxne hxδ'
  have hmv : M.mulVec (x - x₀) a = M a b * (t - x₀ b) := by
    show ∑ j, M a j * (x - x₀) j = M a b * (t - x₀ b)
    rw [Finset.sum_eq_single b]
    · rw [hx, Pi.sub_apply, Function.update_self]
    · intro j _ hjb
      rw [hx, Pi.sub_apply, Function.update_of_ne hjb, sub_self, mul_zero]
    · intro hb'; exact absurd (Finset.mem_univ b) hb'
  have hcomp_eq : (g x - g x₀ - M.mulVec (x - x₀)) a
      = g x a - g x₀ a - M a b * (t - x₀ b) := by
    simp only [Pi.sub_apply, hmv]
  have hs : t - x₀ b ≠ 0 := sub_ne_zero.mpr htne
  -- reduce the difference quotient to the `a`-component of the little-o numerator
  show |(g (Function.update x₀ b t) a - g (Function.update x₀ b (x₀ b)) a) / (t - x₀ b)
      - M a b| < r
  rw [Function.update_eq_self, ← hx]
  have key : (g x a - g x₀ a) / (t - x₀ b) - M a b
      = (g x - g x₀ - M.mulVec (x - x₀)) a / (t - x₀ b) := by
    rw [hcomp_eq]; field_simp
  rw [key, abs_div, div_lt_iff₀ (abs_pos.mpr hs)]
  calc |(g x - g x₀ - M.mulVec (x - x₀)) a|
      ≤ euclideanNorm (g x - g x₀ - M.mulVec (x - x₀)) := abs_coord_le_norm _ a
    _ < r * euclideanNorm (x - x₀) := hbb
    _ = r * |t - x₀ b| := by rw [hnorm]

/-! ### The little-o transfer for the inverse -/

private theorem euclideanNorm_neg {k : ℕ} (w : Fin k → R) :
    euclideanNorm (-w) = euclideanNorm w := by
  rw [show (-w) = (-1 : R) • w by ext i; simp, euclideanNorm_smul]
  simp

/-- **The little-o transfer for the inverse.** If `f` has a first-order approximation at
`x₀ = finv y₀` with invertible derivative `A`, `finv` is a right inverse mapping into `U`,
and `finv` is Lipschitz, then `finv` has the first-order approximation with derivative `A⁻¹`
at `y₀`. -/
theorem isLittleO_inverse {k : ℕ} [Nonempty (Fin k)]
    {U V : Set (Fin k → R)} {f finv : (Fin k → R) → (Fin k → R)}
    {A : Matrix (Fin k) (Fin k) R} {y₀ : Fin k → R}
    (hA : IsUnit A.det) (hrinv : ∀ y ∈ V, f (finv y) = y)
    (hmaps : Set.MapsTo finv V U) (hy₀ : y₀ ∈ V)
    (hlo : IsLittleO (fun x => f x - f (finv y₀) - A.mulVec (x - finv y₀)) U (finv y₀))
    (C : R) (hC : 0 < C)
    (hLip : ∀ y ∈ V, euclideanNorm (finv y - finv y₀) ≤ C * euclideanNorm (y - y₀)) :
    IsLittleO (fun y => finv y - finv y₀ - A⁻¹.mulVec (y - y₀)) V y₀ := by
  have hk : 0 < k := Fin.pos_iff_nonempty.mpr inferInstance
  set L : R := opNorm A⁻¹ with hLdef
  have hL : 0 ≤ L := opNorm_nonneg hk A⁻¹
  have hfx₀ : f (finv y₀) = y₀ := hrinv y₀ hy₀
  apply isLittleO_of_bound
  intro r hr
  have hLC1 : (0 : R) < L * C + 1 := by have := mul_nonneg hL hC.le; linarith
  set r' : R := r / (L * C + 1) with hr'def
  have hr' : 0 < r' := div_pos hr hLC1
  obtain ⟨δ', hδ', hb⟩ := IsLittleO.bound hlo hr'
  refine ⟨δ' / (C + 1), by positivity, fun y hy hyne hyδ => ?_⟩
  -- the cancellation identity
  have hcancel : A⁻¹.mulVec (A.mulVec (finv y - finv y₀)) = finv y - finv y₀ := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
  have hkeyvec : A⁻¹.mulVec (y - y₀ - A.mulVec (finv y - finv y₀))
      = A⁻¹.mulVec (y - y₀) - (finv y - finv y₀) := by
    rw [Matrix.mulVec_sub, hcancel]
  have hvec : finv y - finv y₀ - A⁻¹.mulVec (y - y₀)
      = -(A⁻¹.mulVec (f (finv y) - f (finv y₀) - A.mulVec (finv y - finv y₀))) := by
    rw [hrinv y hy, hfx₀, hkeyvec]
    abel
  -- the inner point is distinct and close enough
  have hxne : finv y ≠ finv y₀ := by
    intro h
    apply hyne
    rw [← hrinv y hy, ← hfx₀, h]
  have hCδ : C * (δ' / (C + 1)) < δ' := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [hδ']
  have hxlt : euclideanNorm (finv y - finv y₀) < δ' := by
    have h1 := hLip y hy
    have h2 : C * euclideanNorm (y - y₀) < C * (δ' / (C + 1)) :=
      mul_lt_mul_of_pos_left hyδ hC
    linarith
  have hbb := hb (finv y) (hmaps hy) hxne hxlt
  -- combine
  have hfinal : L * r' * C ≤ r := by
    rw [hr'def, show L * (r / (L * C + 1)) * C = L * C * r / (L * C + 1) by ring,
      div_le_iff₀ hLC1]
    nlinarith [hr]
  calc euclideanNorm (finv y - finv y₀ - A⁻¹.mulVec (y - y₀))
      = euclideanNorm (A⁻¹.mulVec
          (f (finv y) - f (finv y₀) - A.mulVec (finv y - finv y₀))) := by
        rw [hvec, euclideanNorm_neg]
    _ ≤ L * euclideanNorm (f (finv y) - f (finv y₀) - A.mulVec (finv y - finv y₀)) :=
        norm_mulVec_le hk _ _
    _ ≤ L * (r' * euclideanNorm (finv y - finv y₀)) :=
        mul_le_mul_of_nonneg_left hbb.le hL
    _ ≤ L * (r' * (C * euclideanNorm (y - y₀))) := by
        refine mul_le_mul_of_nonneg_left ?_ hL
        exact mul_le_mul_of_nonneg_left (hLip y hy) hr'.le
    _ = L * r' * C * euclideanNorm (y - y₀) := by ring
    _ ≤ r * euclideanNorm (y - y₀) :=
        mul_le_mul_of_nonneg_right hfinal (euclideanNorm_nonneg _)

/-! ### Differentiability of the inverse -/

/-- **The inverse is differentiable, with derivative the matrix inverse.** Under the
hypotheses of the Inverse Function Theorem, every partial derivative of `finv` at `y₀ ∈ V`
exists and equals the corresponding entry of `(df(finv y₀))⁻¹ = (jacobianMatrix g
(finv y₀))⁻¹`. -/
theorem hasPartialDerivAtIn_inverse {k : ℕ} [Nonempty (Fin k)]
    {U V : Set (Fin k → R)} {f finv : (Fin k → R) → (Fin k → R)}
    {g : Fin k → Fin k → (Fin k → R) → R}
    (hUopen : IsOpen U)
    (hf : ∀ l, IsSemialgebraicFunction U (scalarFun (fun x => f x l)))
    (hg : ∀ l j, ∀ x ∈ U, HasPartialDerivAtIn (fun w => f w l) U j x (g l j x))
    (hgcont : ∀ l j, ContinuousOn (scalarFun (g l j)) U)
    (hfinvMaps : Set.MapsTo finv V U) (hrinv : ∀ y ∈ V, f (finv y) = y)
    (hdet : ∀ x ∈ U, IsUnit (jacobianMatrix g x).det)
    (C : R) (hC : 0 < C)
    (hLip : ∀ y ∈ V, ∀ y' ∈ V,
      euclideanNorm (finv y - finv y') ≤ C * euclideanNorm (y - y'))
    {y₀ : Fin k → R} (hy₀ : y₀ ∈ V) (a b : Fin k) :
    HasPartialDerivAtIn (fun y => finv y a) V b y₀
      ((jacobianMatrix g (finv y₀))⁻¹ a b) := by
  have hAdet : IsUnit (jacobianMatrix g (finv y₀)).det := hdet (finv y₀) (hfinvMaps hy₀)
  have hlof : IsLittleO (fun x => f x - f (finv y₀)
      - (jacobianMatrix g (finv y₀)).mulVec (x - finv y₀)) U (finv y₀) := by
    have h := isLittleO_sub_totalDeriv hUopen hf hg hgcont (hfinvMaps hy₀)
    simpa only [totalDeriv_eq_mulVec] using h
  have hloinv : IsLittleO (fun y => finv y - finv y₀
      - (jacobianMatrix g (finv y₀))⁻¹.mulVec (y - y₀)) V y₀ :=
    isLittleO_inverse hAdet hrinv hfinvMaps hy₀ hlof C hC (fun y hy => hLip y hy y₀ hy₀)
  exact hasPartialDerivAtIn_of_isLittleO hloinv a b

/-! ### `𝒮^ℓ`-smoothness of the inverse -/

/-- **BPR Proposition 3.24, closing sentence: the inverse is `𝒮^ℓ`.** If `f`'s partial
derivatives `g` are `𝒮^m` (so `f ∈ 𝒮^{m+1}`), the inverse `finv` is `𝒮^0`, maps `V → U`,
is a right inverse, and the Jacobian is everywhere invertible with `finv` Lipschitz, then
every component of `finv` is `𝒮^{m+1}`. (The partials of `finv` are the entries of
`(df(finv ·))⁻¹`, `𝒮^m` by `isSFunction_matrixInvEntry` once `finv` is `𝒮^m` — the
inductive hypothesis.) -/
theorem isSFunction_inverse {k : ℕ} [Nonempty (Fin k)]
    {U V : Set (Fin k → R)} {f finv : (Fin k → R) → (Fin k → R)}
    {g : Fin k → Fin k → (Fin k → R) → R}
    (hUopen : IsOpen U) (hVsa : IsSemialgebraicSet V)
    (hf : ∀ l, IsSemialgContinuousOn U (fun x => f x l))
    (hg : ∀ l j, ∀ x ∈ U, HasPartialDerivAtIn (fun w => f w l) U j x (g l j x))
    (hgSC : ∀ l j, IsSemialgContinuousOn U (g l j))
    (hfinvSC : ∀ a, IsSemialgContinuousOn V (fun y => finv y a))
    (hfinvMaps : Set.MapsTo finv V U) (hrinv : ∀ y ∈ V, f (finv y) = y)
    (hdet : ∀ x ∈ U, IsUnit (jacobianMatrix g x).det)
    (C : R) (hC : 0 < C)
    (hLip : ∀ y ∈ V, ∀ y' ∈ V,
      euclideanNorm (finv y - finv y') ≤ C * euclideanNorm (y - y')) :
    ∀ m : ℕ, (∀ l j, IsSFunction m U (g l j)) →
      ∀ a, IsSFunction (m + 1) V (fun y => finv y a) := by
  -- the partial-value function is `(jacobianMatrix g (finv ·))⁻¹ a b`
  have hpart : ∀ a b, ∀ y ∈ V,
      HasPartialDerivAtIn (fun y => finv y a) V b y
        ((jacobianMatrix g (finv y))⁻¹ a b) := fun a b y hy =>
    hasPartialDerivAtIn_inverse hUopen (fun l => (hf l).1) hg
      (fun l j => (hgSC l j).2) hfinvMaps hrinv hdet C hC hLip hy a b
  have hdet' : ∀ y ∈ V, (Matrix.of fun i j => g i j (finv y)).det ≠ 0 :=
    fun y hy => (hdet (finv y) (hfinvMaps hy)).ne_zero
  intro m
  induction m with
  | zero =>
    intro hgS a
    refine ⟨hfinvSC a, fun b => ⟨fun y => (jacobianMatrix g (finv y))⁻¹ a b,
      fun y hy => hpart a b y hy, ?_⟩⟩
    have hentries : ∀ i j, IsSFunction 0 V (fun y => g i j (finv y)) :=
      fun i j => isSFunction_comp hVsa hUopen hfinvMaps (hgS i j) hfinvSC
    exact isSFunction_matrixInvEntry hVsa hentries hdet' a b
  | succ m ih =>
    intro hgS a
    refine ⟨hfinvSC a, fun b => ⟨fun y => (jacobianMatrix g (finv y))⁻¹ a b,
      fun y hy => hpart a b y hy, ?_⟩⟩
    have hfinvComp : ∀ a', IsSFunction (m + 1) V (fun y => finv y a') :=
      ih (fun l j => (hgS l j).of_succ)
    have hentries : ∀ i j, IsSFunction (m + 1) V (fun y => g i j (finv y)) :=
      fun i j => isSFunction_comp hVsa hUopen hfinvMaps (hgS i j) hfinvComp
    exact isSFunction_matrixInvEntry hVsa hentries hdet' a b

/-! ### Restriction of the `𝒮`-data to a subdomain -/

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- A partial derivative on `U′` restricts to a subdomain `U ⊆ U′` (the slice set shrinks). -/
theorem HasPartialDerivAtIn.mono_set {k : ℕ} {c : (Fin k → R) → R}
    {U U' : Set (Fin k → R)} {j : Fin k} {x : Fin k → R} {d : R} (hUU : U ⊆ U')
    (h : HasPartialDerivAtIn c U' j x d) : HasPartialDerivAtIn c U j x d :=
  HasDerivAtIn.mono (fun _ ht => hUU ht) h

/-- `𝒮^ℓ` membership restricts to a semialgebraic subdomain. -/
theorem IsSFunction.mono_set {k : ℕ} {U U' : Set (Fin k → R)} (hU : IsSemialgebraicSet U)
    (hUU : U ⊆ U') :
    ∀ {m : ℕ} {c : (Fin k → R) → R}, IsSFunction m U' c → IsSFunction m U c := by
  intro m
  induction m with
  | zero => intro c h; exact IsSemialgContinuousOn.mono h hU hUU
  | succ m ih =>
    intro c h
    refine ⟨h.1.mono hU hUU, fun j => ?_⟩
    obtain ⟨gj, hgj, hS⟩ := h.2 j
    exact ⟨gj, fun x hx => (hgj x (hUU hx)).mono_set hUU, ih hS⟩

/-! ### Coordinate functions are `𝒮^ℓ` -/

/-- Coordinate functions are semialgebraic and continuous on any semialgebraic set. -/
theorem isSemialgContinuousOn_coord {k : ℕ} {S : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) (i : Fin k) :
    IsSemialgContinuousOn S (fun z => z i) := by
  constructor
  · have heq : scalarFun (fun z : Fin k → R => z i) = polyFun (X i) := by
      funext z j
      simp [scalarFun, polyFun, constPt]
    rw [heq]
    exact polyFun_isSemialgebraicFunction_on hS _
  · exact continuousOn_scalarFun_of_continuousR (continuousR_coord i)

omit [IsRealClosed R] in
/-- The `j`-th partial derivative of the `i`-th coordinate function is the Kronecker
delta `δᵢⱼ`. -/
theorem hasPartialDerivAtIn_coord {k : ℕ} (U : Set (Fin k → R)) (i j : Fin k)
    (x : Fin k → R) :
    HasPartialDerivAtIn (fun w => w i) U j x (if i = j then 1 else 0) := by
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    show HasDerivAtIn (fun t => Function.update x i t i)
      {t : R | Function.update x i t ∈ U} (x i) 1
    have heq : (fun t : R => Function.update x i t i) = fun t => 1 * t + 0 := by
      funext t
      rw [Function.update_self, one_mul, add_zero]
    rw [heq]
    exact hasDerivAtIn_affine 1 0 _ _
  · rw [ite_eq_right hij]
    show HasDerivAtIn (fun t => Function.update x j t i)
      {t : R | Function.update x j t ∈ U} (x j) 0
    have heq : (fun t : R => Function.update x j t i) = fun _ => x i := by
      funext t
      rw [Function.update_of_ne hij]
    rw [heq]
    exact hasDerivAtIn_const (x i) _ _

/-- A coordinate function is `𝒮^ℓ` for every order (its partials are Kronecker
constants). -/
theorem isSFunction_coord {k : ℕ} {U : Set (Fin k → R)} (hU : IsSemialgebraicSet U)
    (i : Fin k) : ∀ ℓ : ℕ, IsSFunction ℓ U (fun x => x i)
  | 0 => isSemialgContinuousOn_coord hU i
  | ℓ + 1 =>
    ⟨isSemialgContinuousOn_coord hU i, fun j =>
      ⟨fun _ => if i = j then 1 else 0, fun x _ => hasPartialDerivAtIn_coord U i j x,
        isSFunction_const hU _ ℓ⟩⟩

/-! ### Proposition 3.24, closing sentence -/

/-- **BPR Proposition 3.24, closing sentence (`𝒮^ℓ`-smoothness of the inverse).** If, in
addition to the hypotheses of `proposition_3_24`, the partial derivatives `g` of `f` are of
class `𝒮^m` (so `f ∈ 𝒮^{m+1}`), then the local inverse is of class `𝒮^{m+1}`: there are
semialgebraic open neighborhoods `U, V` of `0` with `U ⊆ U′` and `finv` such that `f|_U` is
a semialgebraic homeomorphism onto `V` whose inverse is semialgebraic and `𝒮^{m+1}`. -/
theorem proposition_3_24_sClass {k : ℕ} {U' : Set (Fin k → R)}
    {f : (Fin k → R) → (Fin k → R)} {g : Fin k → Fin k → (Fin k → R) → R}
    (hU'open : IsOpen U') (hU'sa : IsSemialgebraicSet U') (h0U' : (0 : Fin k → R) ∈ U')
    (hf : ∀ l, IsSemialgContinuousOn U' (fun z => f z l))
    (hdiff : ∀ l j, ∀ z ∈ U', HasPartialDerivAtIn (fun w => f w l) U' j z (g l j z))
    (hgsc : ∀ l j, IsSemialgContinuousOn U' (g l j))
    (hf0 : f 0 = 0) (hdet0 : IsUnit (jacobianMatrix g 0).det)
    (m : ℕ) (hgS : ∀ l j, IsSFunction m U' (g l j)) :
    ∃ U V : Set (Fin k → R),
      IsSemialgebraicSet U ∧ IsOpen U ∧ (0 : Fin k → R) ∈ U ∧ U ⊆ U' ∧
      IsSemialgebraicSet V ∧ IsOpen V ∧ (0 : Fin k → R) ∈ V ∧
      ∃ finv : (Fin k → R) → (Fin k → R),
        IsSemialgebraicHomeomorphism U V f finv ∧ IsSemialgebraicFunction V finv ∧
        ∀ a, IsSFunction (m + 1) V (fun y => finv y a) := by
  obtain ⟨U, V, hUsa, hUopen, h0U, hUsub, hVsa, hVopen, h0V, finv,
    hhomeo, hFinvSa, hdetU, C, hC, hLip⟩ :=
    proposition_3_24 hU'open hU'sa h0U' hf hdiff hgsc hf0 hdet0
  refine ⟨U, V, hUsa, hUopen, h0U, hUsub, hVsa, hVopen, h0V, finv,
    hhomeo, hFinvSa, ?_⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0; intro a; exact a.elim0
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  -- the inverse maps `V → U` and is a right inverse
  have hfinvMaps : Set.MapsTo finv V U := by
    intro y hy
    obtain ⟨x, hxU, hfx⟩ := hhomeo.bijOn.surjOn hy
    rw [← hfx, hhomeo.invOn.1 hxU]
    exact hxU
  have hrinv : ∀ y ∈ V, f (finv y) = y := fun y hy => hhomeo.invOn.2 hy
  -- the inverse is `𝒮⁰` componentwise
  have hfinvSC : ∀ a, IsSemialgContinuousOn V (fun y => finv y a) := by
    intro a
    have hcoordSa : IsSemialgebraicFunction U (scalarFun (fun w : Fin k → R => w a)) := by
      have hco : scalarFun (fun w : Fin k → R => w a) = polyFun (X a) := by
        funext u i; simp [scalarFun, polyFun, constPt]
      rw [hco]; exact polyFun_isSemialgebraicFunction_on hUsa (X a)
    have hcoordCont : ContinuousOn (scalarFun (fun w : Fin k → R => w a)) U :=
      continuousOn_scalarFun_of_continuousR (continuousR_coord a)
    exact ⟨proposition_2_84 hFinvSa hcoordSa hfinvMaps,
      hcoordCont.comp hhomeo.continuousOn_inv hfinvMaps⟩
  -- restrict the `f`-data to `U`
  have hfU : ∀ l, IsSemialgContinuousOn U (fun x => f x l) :=
    fun l => (hf l).mono hUsa hUsub
  have hgU : ∀ l j, ∀ x ∈ U, HasPartialDerivAtIn (fun w => f w l) U j x (g l j x) :=
    fun l j x hx => (hdiff l j x (hUsub hx)).mono_set hUsub
  have hgscU : ∀ l j, IsSemialgContinuousOn U (g l j) :=
    fun l j => (hgsc l j).mono hUsa hUsub
  have hgSU : ∀ l j, IsSFunction m U (g l j) :=
    fun l j => (hgS l j).mono_set hUsa hUsub
  exact isSFunction_inverse hUopen hVsa hfU hgU hgscU hfinvSC hfinvMaps hrinv hdetU
    C hC hLip m hgSU

end Azurite.BPR
