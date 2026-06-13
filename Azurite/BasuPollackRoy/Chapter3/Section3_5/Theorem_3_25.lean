import Azurite.BasuPollackRoy.Chapter3.Section3_5.BasePointSmooth

/-! # BPR §3.5, Theorem 3.25 — the Implicit Function Theorem

**Let `(x⁰, y⁰) ∈ R^{k+ℓ}`, and let `f₁, …, f_ℓ` be semialgebraic functions of class
`𝒮^m` on an open neighborhood of `(x⁰, y⁰)` such that `f_j(x⁰, y⁰) = 0` for
`j = 1, …, ℓ` and the Jacobian matrix of `f = (f₁, …, f_ℓ)` at `(x⁰, y⁰)` with respect
to the variables `y₁, …, y_ℓ` is invertible. Then there exists a semialgebraic open
neighborhood `U` (resp. `V`) of `x⁰` (resp. `y⁰`) in `R^k` (resp. `R^ℓ`) and a function
`ϕ ∈ 𝒮^m(U, V)` such that `ϕ(x⁰) = y⁰` and, for every `(x, y) ∈ U × V`,**

  `f₁(x, y) = ⋯ = f_ℓ(x, y) = 0 ⇔ y = ϕ(x).`

**Proof: Apply Proposition 3.24 to the function `(x, y) ↦ (x, f(x, y))`.**

The formalization follows BPR's one-line proof. Points of `R^{k+ℓ}` are split as
`Fin.append x y`; the auxiliary map is `F(z) = Fin.append (z ∘ castAdd ℓ) (f(z))`, whose
Jacobian is block-triangular with blocks `1` and `∂f/∂y` (`det_eq_det_lower_block`), so
`proposition_3_24_at_sClass` (the base-point Inverse Function Theorem with `𝒮^{m+1}`
inverse) applies at `z₀ = (x⁰, y⁰)`. With `Finv` the local inverse, `ϕ(x)` is the
last-`ℓ` block of `Finv(x, 0)`; the neighborhoods are shrunk to a product of balls inside
the injectivity domain, which yields the equivalence. Given `f ∈ 𝒮^{m+1}` (partials `g`
of class `𝒮^m`), `Finv` is `𝒮^{m+1}` and hence so is `ϕ = projSnd ∘ Finv ∘ (·, 0)` by
composition closure — BPR's full statement, `ϕ` of the same class as `f`. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Block-coordinate toolkit -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Subtraction acts blockwise on appended vectors. -/
theorem append_sub_append {k ℓ : ℕ} (a c : Fin k → R) (b d : Fin ℓ → R) :
    Fin.append a b - Fin.append c d = Fin.append (a - c) (b - d) := by
  funext i
  induction i using Fin.addCases with
  | left i' => simp [Fin.append_left]
  | right j' => simp [Fin.append_right]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The squared euclidean norm splits across the two blocks of an appended vector. -/
theorem euclideanNormSq_append {k ℓ : ℕ} (a : Fin k → R) (b : Fin ℓ → R) :
    euclideanNormSq (Fin.append a b) = euclideanNormSq a + euclideanNormSq b := by
  simp only [euclideanNormSq]
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_left]
  · exact Finset.sum_congr rfl fun j _ => by rw [Fin.append_right]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Reassembling a vector of `R^{k+ℓ}` from its two blocks. -/
theorem append_castAdd_natAdd {k ℓ : ℕ} (z : Fin (k + ℓ) → R) :
    Fin.append (z ∘ Fin.castAdd ℓ) (z ∘ Fin.natAdd k) = z := by
  funext i
  induction i using Fin.addCases with
  | left i' => rw [Fin.append_left]; rfl
  | right j' => rw [Fin.append_right]; rfl

/-! ### Coordinate functions: semialgebraic continuity and partial derivatives -/

/-! ### The block embedding `x ↦ (x, 0)` and the block projection `z ↦ z ∘ natAdd` -/

/-- The embedding `x ↦ (x, 0)` of `R^k` into `R^{k+ℓ}` is continuous. -/
theorem continuous_appendZero {k ℓ : ℕ} :
    Continuous (fun x : Fin k → R => Fin.append x (0 : Fin ℓ → R)) := by
  have heq : (fun x : Fin k → R => Fin.append x (0 : Fin ℓ → R))
      = polynomialMap (Fin.addCases
          (motive := fun _ => MvPolynomial (Fin k) R) (fun i => X i) (fun _ => C 0)) := by
    funext x i
    induction i using Fin.addCases with
    | left i' => simp [polynomialMap, Fin.append_left]
    | right j' => simp [polynomialMap, Fin.append_right]
  rw [heq]
  exact continuous_polynomialMap _

omit [IsRealClosed R] in
/-- The embedding `x ↦ (x, 0)` of `R^k` into `R^{k+ℓ}` is a semialgebraic function on
any semialgebraic domain. -/
theorem isSemialgebraicFunction_appendZero {k ℓ : ℕ} [Nonempty (Fin (k + ℓ))]
    {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    IsSemialgebraicFunction S (fun x : Fin k → R => Fin.append x (0 : Fin ℓ → R)) := by
  refine isSemialgebraicFunction_of_coords fun j => ?_
  induction j using Fin.addCases with
  | left i' =>
    have heq : (fun x : Fin k → R => fun _ : Fin 1 =>
        Fin.append x (0 : Fin ℓ → R) (Fin.castAdd ℓ i')) = polyFun (X i') := by
      funext x j
      simp [polyFun, Fin.append_left]
    rw [heq]
    exact polyFun_isSemialgebraicFunction_on hS _
  | right j' =>
    have heq : (fun x : Fin k → R => fun _ : Fin 1 =>
        Fin.append x (0 : Fin ℓ → R) (Fin.natAdd k j')) = polyFun (C 0) := by
      funext x j
      simp [polyFun, Fin.append_right]
    rw [heq]
    exact polyFun_isSemialgebraicFunction_on hS _

/-- The block projection `z ↦ z ∘ natAdd k` from `R^{k+ℓ}` onto `R^ℓ` is continuous. -/
theorem continuous_projSnd {k ℓ : ℕ} :
    Continuous (fun z : Fin (k + ℓ) → R => z ∘ Fin.natAdd k) := by
  have heq : (fun z : Fin (k + ℓ) → R => z ∘ Fin.natAdd k)
      = polynomialMap (fun j : Fin ℓ =>
          (X (Fin.natAdd k j) : MvPolynomial (Fin (k + ℓ)) R)) := by
    funext z j
    simp [polynomialMap]
  rw [heq]
  exact continuous_polynomialMap _

omit [IsRealClosed R] in
/-- The block projection `z ↦ z ∘ natAdd k` is a semialgebraic function on any
semialgebraic domain. -/
theorem isSemialgebraicFunction_projSnd {k ℓ : ℕ} [Nonempty (Fin ℓ)]
    {S : Set (Fin (k + ℓ) → R)} (hS : IsSemialgebraicSet S) :
    IsSemialgebraicFunction S (fun z : Fin (k + ℓ) → R => z ∘ Fin.natAdd k) := by
  refine isSemialgebraicFunction_of_coords fun j => ?_
  have heq : (fun z : Fin (k + ℓ) → R => fun _ : Fin 1 => (z ∘ Fin.natAdd k) j)
      = polyFun (X (Fin.natAdd k j)) := by
    funext z i
    simp [polyFun]
  rw [heq]
  exact polyFun_isSemialgebraicFunction_on hS _

/-! ### A block-triangular determinant -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- If the first `k` rows of `M : Matrix (Fin (k+ℓ)) (Fin (k+ℓ)) R` are the corresponding
rows of the identity, then `det M` is the determinant of the lower-right `ℓ × ℓ` block
(the matrix is block-triangular with an identity block). -/
theorem det_eq_det_lower_block {k ℓ : ℕ} (M : Matrix (Fin (k + ℓ)) (Fin (k + ℓ)) R)
    (htop : ∀ (i' : Fin k) (j : Fin (k + ℓ)),
      M (Fin.castAdd ℓ i') j = if (Fin.castAdd ℓ i' : Fin (k + ℓ)) = j then 1 else 0) :
    M.det = (Matrix.of fun l j' : Fin ℓ =>
      M (Fin.natAdd k l) (Fin.natAdd k j')).det := by
  have hsub : M.submatrix finSumFinEquiv finSumFinEquiv
      = Matrix.fromBlocks 1 0
          (Matrix.of fun (l : Fin ℓ) (j' : Fin k) => M (Fin.natAdd k l) (Fin.castAdd ℓ j'))
          (Matrix.of fun l j' : Fin ℓ => M (Fin.natAdd k l) (Fin.natAdd k j')) := by
    ext i j
    rcases i with i' | l <;> rcases j with j' | j'
    · rw [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_left,
        Matrix.fromBlocks_apply₁₁, htop, Matrix.one_apply]
      by_cases h : i' = j'
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun hc => h (by
          have := congrArg Fin.val hc
          simp only [Fin.val_castAdd] at this
          exact Fin.ext this))]
    · rw [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Matrix.fromBlocks_apply₁₂, htop, Matrix.zero_apply, if_neg]
      intro hc
      have := congrArg Fin.val hc
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rw [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
    · rw [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_right,
        Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, hsub,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

/-! ### Theorem 3.25 -/

/-- **BPR Theorem 3.25 (Implicit Function Theorem).** Let `(x⁰, y⁰) ∈ R^{k+ℓ}` and let
`f₁, …, f_ℓ` be semialgebraic functions of class `𝒮^{m+1}` on a semialgebraic open
neighborhood `W′` of `(x⁰, y⁰)` (coordinatewise data: `f_l` semialgebraic continuous,
partial derivatives `g l j` existing, semialgebraic continuous, and `𝒮^m`), with
`f_j(x⁰, y⁰) = 0` for all `j` and the Jacobian matrix with respect to `y₁, …, y_ℓ`
invertible at `(x⁰, y⁰)`. Then there are semialgebraic open neighborhoods `U ∋ x⁰` in
`R^k` and `V ∋ y⁰` in `R^ℓ` with `U × V ⊆ W′` and a function `ϕ ∈ 𝒮^{m+1}(U, V)` with
`ϕ(x⁰) = y⁰` such that for every `(x, y) ∈ U × V`,

  `f₁(x, y) = ⋯ = f_ℓ(x, y) = 0 ⇔ y = ϕ(x)`.

This is BPR's full statement (`ϕ` of the same class as `f`): the proof applies the
base-point Inverse Function Theorem with `𝒮^{m+1}` inverse
(`proposition_3_24_at_sClass`) to `(x, y) ↦ (x, f(x, y))`. -/
theorem theorem_3_25 {k ℓ : ℕ} {W' : Set (Fin (k + ℓ) → R)}
    {x₀ : Fin k → R} {y₀ : Fin ℓ → R}
    {f : Fin ℓ → (Fin (k + ℓ) → R) → R} {g : Fin ℓ → Fin (k + ℓ) → (Fin (k + ℓ) → R) → R}
    (hW'open : IsOpen W') (hW'sa : IsSemialgebraicSet W')
    (hz₀W : Fin.append x₀ y₀ ∈ W')
    (hf : ∀ l, IsSemialgContinuousOn W' (f l))
    (hdiff : ∀ l j, ∀ z ∈ W', HasPartialDerivAtIn (f l) W' j z (g l j z))
    (hgsc : ∀ l j, IsSemialgContinuousOn W' (g l j))
    (hf0 : ∀ l, f l (Fin.append x₀ y₀) = 0)
    (hdet : IsUnit (Matrix.of fun l j : Fin ℓ =>
      g l (Fin.natAdd k j) (Fin.append x₀ y₀)).det)
    (m : ℕ) (hgS : ∀ l j, IsSFunction m W' (g l j)) :
    ∃ (U : Set (Fin k → R)) (V : Set (Fin ℓ → R)) (ϕ : (Fin k → R) → (Fin ℓ → R)),
      IsSemialgebraicSet U ∧ IsOpen U ∧ x₀ ∈ U ∧
      IsSemialgebraicSet V ∧ IsOpen V ∧ y₀ ∈ V ∧
      IsSemialgebraicFunction U ϕ ∧ ContinuousOn ϕ U ∧
      Set.MapsTo ϕ U V ∧ ϕ x₀ = y₀ ∧
      setProd U V ⊆ W' ∧
      (∀ x ∈ U, ∀ y ∈ V, ((∀ l, f l (Fin.append x y) = 0) ↔ y = ϕ x)) ∧
      ∀ i, IsSFunction (m + 1) U (fun x => ϕ x i) := by
  classical
  rcases Nat.eq_zero_or_pos ℓ with hl0 | hl
  · -- the degenerate case `ℓ = 0`: there are no equations and no `y`-variables
    subst hl0
    set gk : Fin (k + 0) → Fin k := fun i => ⟨i.val, by have := i.isLt; omega⟩ with hgk
    have hcastgk : ∀ i : Fin (k + 0), Fin.castAdd 0 (gk i) = i := fun i => Fin.ext rfl
    have happend : ∀ x : Fin k → R, Fin.append x y₀ = x ∘ gk := by
      intro x
      funext i
      show Fin.append x y₀ i = x (gk i)
      conv_lhs => rw [← hcastgk i]
      rw [Fin.append_left]
    have hcomp : ∀ z : Fin (k + 0) → R, (z ∘ Fin.castAdd 0) ∘ gk = z := by
      intro z
      funext i
      show z (Fin.castAdd 0 (gk i)) = z i
      rw [hcastgk]
    refine ⟨{x | x ∘ gk ∈ W'}, Set.univ, fun _ => y₀,
      IsSemialgebraicSet.comap gk hW'sa, ?_, ?_, isSemialgebraicSet_univ, isOpen_univ,
      Set.mem_univ _, ?_, continuousOn_const, fun x _ => Set.mem_univ _, rfl, ?_, ?_,
      fun i => i.elim0⟩
    · -- openness: the preimage of `W'` under the (polynomial) reindexing map
      have hcont : Continuous (fun x : Fin k → R => x ∘ gk) := by
        have heq : (fun x : Fin k → R => x ∘ gk)
            = polynomialMap (fun i => (X (gk i) : MvPolynomial (Fin k) R)) := by
          funext x i
          simp [polynomialMap]
        rw [heq]
        exact continuous_polynomialMap _
      exact hW'open.preimage hcont
    · show x₀ ∘ gk ∈ W'
      rw [← happend x₀]
      exact hz₀W
    · -- the constant function to `R^0` is semialgebraic: its graph is a cylinder
      show IsSemialgebraicSet (funGraph {x | x ∘ gk ∈ W'} fun _ : Fin k → R => y₀)
      have heq : funGraph {x | x ∘ gk ∈ W'} (fun _ : Fin k → R => y₀)
          = {z : Fin (k + 0) → R | z ∘ Fin.castAdd 0 ∈ {x : Fin k → R | x ∘ gk ∈ W'}} := by
        ext z
        rw [mem_funGraph]
        exact and_iff_left (Subsingleton.elim _ _)
      rw [heq]
      exact IsSemialgebraicSet.comap _ (IsSemialgebraicSet.comap gk hW'sa)
    · -- `setProd U univ ⊆ W'`
      intro z hz
      have h1 : (z ∘ Fin.castAdd 0) ∘ gk ∈ W' := hz.1
      rwa [hcomp z] at h1
    · -- the equivalence is trivially two-sided
      intro x _ y _
      exact iff_of_true (fun l => l.elim0) (Subsingleton.elim _ _)
  -- the main case `ℓ > 0`
  haveI : Nonempty (Fin ℓ) := ⟨⟨0, hl⟩⟩
  haveI : Nonempty (Fin (k + ℓ)) := ⟨⟨0, by omega⟩⟩
  set z₀ : Fin (k + ℓ) → R := Fin.append x₀ y₀ with hz0
  -- the auxiliary map `F(z) = (z ∘ castAdd, f(z))` and its partial-derivative data
  set F : (Fin (k + ℓ) → R) → (Fin (k + ℓ) → R) :=
    fun z => Fin.append (z ∘ Fin.castAdd ℓ) (fun l => f l z) with hFdef
  set Gf : Fin (k + ℓ) → Fin (k + ℓ) → (Fin (k + ℓ) → R) → R :=
    fun i => Fin.addCases
      (motive := fun _ => Fin (k + ℓ) → (Fin (k + ℓ) → R) → R)
      (fun i' j _ => if (Fin.castAdd ℓ i' : Fin (k + ℓ)) = j then (1 : R) else 0)
      (fun l j z => g l j z) i with hGfdef
  have hFcast : ∀ (w : Fin (k + ℓ) → R) (i' : Fin k),
      F w (Fin.castAdd ℓ i') = w (Fin.castAdd ℓ i') := by
    intro w i'
    show Fin.append (w ∘ Fin.castAdd ℓ) (fun l => f l w) (Fin.castAdd ℓ i') = _
    rw [Fin.append_left]
    rfl
  have hFnat : ∀ (w : Fin (k + ℓ) → R) (l : Fin ℓ), F w (Fin.natAdd k l) = f l w := by
    intro w l
    show Fin.append (w ∘ Fin.castAdd ℓ) (fun l => f l w) (Fin.natAdd k l) = _
    rw [Fin.append_right]
  -- the `𝒮¹` data for `F`
  have hFcomp : ∀ i, IsSemialgContinuousOn W' (fun z => F z i) := by
    intro i
    induction i using Fin.addCases with
    | left i' =>
      have heq : (fun z : Fin (k + ℓ) → R => F z (Fin.castAdd ℓ i'))
          = fun z => z (Fin.castAdd ℓ i') := by
        funext z
        rw [hFcast]
      rw [heq]
      exact isSemialgContinuousOn_coord hW'sa _
    | right l =>
      have heq : (fun z : Fin (k + ℓ) → R => F z (Fin.natAdd k l)) = f l := by
        funext z
        rw [hFnat]
      rw [heq]
      exact hf l
  have hdiffF : ∀ i j, ∀ z ∈ W',
      HasPartialDerivAtIn (fun w => F w i) W' j z (Gf i j z) := by
    intro i
    induction i using Fin.addCases with
    | left i' =>
      intro j z hz
      have heq : (fun w : Fin (k + ℓ) → R => F w (Fin.castAdd ℓ i'))
          = fun w => w (Fin.castAdd ℓ i') := by
        funext w
        rw [hFcast]
      have hG : Gf (Fin.castAdd ℓ i') j z
          = if (Fin.castAdd ℓ i' : Fin (k + ℓ)) = j then (1 : R) else 0 := by
        simp [hGfdef, Fin.addCases_left]
      rw [heq, hG]
      exact hasPartialDerivAtIn_coord W' _ j z
    | right l =>
      intro j z hz
      have heq : (fun w : Fin (k + ℓ) → R => F w (Fin.natAdd k l)) = f l := by
        funext w
        rw [hFnat]
      have hG : Gf (Fin.natAdd k l) j z = g l j z := by
        simp [hGfdef, Fin.addCases_right]
      rw [heq, hG]
      exact hdiff l j z hz
  have hgscF : ∀ i j, IsSemialgContinuousOn W' (Gf i j) := by
    intro i
    induction i using Fin.addCases with
    | left i' =>
      intro j
      have heq : Gf (Fin.castAdd ℓ i') j = fun _ : Fin (k + ℓ) → R =>
          if (Fin.castAdd ℓ i' : Fin (k + ℓ)) = j then (1 : R) else 0 := by
        funext z
        simp [hGfdef, Fin.addCases_left]
      rw [heq]
      exact isSemialgContinuousOn_constFun hW'sa _
    | right l =>
      intro j
      have heq : Gf (Fin.natAdd k l) j = g l j := by
        funext z
        simp [hGfdef, Fin.addCases_right]
      rw [heq]
      exact hgsc l j
  -- the Jacobian of `F` at `z₀` is block-triangular with an identity block
  have hdetF : IsUnit (jacobianMatrix Gf z₀).det := by
    have hblock : (jacobianMatrix Gf z₀).det
        = (Matrix.of fun l j' : Fin ℓ =>
            jacobianMatrix Gf z₀ (Fin.natAdd k l) (Fin.natAdd k j')).det := by
      refine det_eq_det_lower_block _ fun i' j => ?_
      show Gf (Fin.castAdd ℓ i') j z₀ = _
      simp [hGfdef, Fin.addCases_left]
    have hlower : (Matrix.of fun l j' : Fin ℓ =>
          jacobianMatrix Gf z₀ (Fin.natAdd k l) (Fin.natAdd k j'))
        = Matrix.of fun l j' : Fin ℓ => g l (Fin.natAdd k j') z₀ := by
      ext l j'
      show Gf (Fin.natAdd k l) (Fin.natAdd k j') z₀ = _
      simp [hGfdef, Fin.addCases_right]
    rw [hblock, hlower]
    exact hdet
  -- `F`'s partials are `𝒮^m` (the identity-block rows are constants, the rest are `g`)
  have hGfS : ∀ i j, IsSFunction m W' (Gf i j) := by
    intro i
    induction i using Fin.addCases with
    | left i' =>
      intro j
      have heq : Gf (Fin.castAdd ℓ i') j
          = fun _ : Fin (k + ℓ) → R =>
              if (Fin.castAdd ℓ i' : Fin (k + ℓ)) = j then (1 : R) else 0 := by
        funext z
        simp [hGfdef, Fin.addCases_left]
      rw [heq]
      exact isSFunction_const hW'sa _ m
    | right l =>
      intro j
      have heq : Gf (Fin.natAdd k l) j = g l j := by
        funext z
        simp [hGfdef, Fin.addCases_right]
      rw [heq]
      exact hgS l j
  -- the Inverse Function Theorem at `z₀`, with `𝒮^{m+1}` inverse
  obtain ⟨U₀, V₀, hU₀sa, hU₀open, hz₀U₀, hU₀sub, hV₀sa, hV₀open, hFz₀V₀, Finv,
    hhomeo, hFinvSa, hFinvS⟩ :=
    proposition_3_24_at_sClass hW'open hW'sa hz₀W hFcomp hdiffF hgscF hdetF m hGfS
  -- the embedding `e`, its preimage domain `D`, and the implicit function `ϕ`
  set e : (Fin k → R) → (Fin (k + ℓ) → R) :=
    fun x => Fin.append x (0 : Fin ℓ → R) with hedef
  set D : Set (Fin k → R) := e ⁻¹' V₀ with hDdef
  set ψ : (Fin k → R) → (Fin (k + ℓ) → R) := fun x => Finv (e x) with hψdef
  set ϕ : (Fin k → R) → (Fin ℓ → R) := fun x => ψ x ∘ Fin.natAdd k with hϕdef
  have hFz0 : F z₀ = e x₀ := by
    funext i
    induction i using Fin.addCases with
    | left i' =>
      rw [hFcast]
      show z₀ (Fin.castAdd ℓ i') = Fin.append x₀ (0 : Fin ℓ → R) (Fin.castAdd ℓ i')
      rw [Fin.append_left]
      show Fin.append x₀ y₀ (Fin.castAdd ℓ i') = x₀ i'
      rw [Fin.append_left]
    | right l =>
      rw [hFnat]
      show f l z₀ = Fin.append x₀ (0 : Fin ℓ → R) (Fin.natAdd k l)
      rw [Fin.append_right]
      exact hf0 l
  -- for `x ∈ D`, `ψ x = (x, ϕ x)` and `f(ψ x) = 0`
  have hψcast : ∀ x ∈ D, ∀ i' : Fin k, ψ x (Fin.castAdd ℓ i') = x i' := by
    intro x hx i'
    have hFψ : F (Finv (e x)) = e x := hhomeo.invOn.2 hx
    have h2 := congrFun hFψ (Fin.castAdd ℓ i')
    rw [hFcast] at h2
    show Finv (e x) (Fin.castAdd ℓ i') = x i'
    rw [h2]
    show Fin.append x (0 : Fin ℓ → R) (Fin.castAdd ℓ i') = x i'
    rw [Fin.append_left]
  have hψzero : ∀ x ∈ D, ∀ l, f l (ψ x) = 0 := by
    intro x hx l
    have hFψ : F (Finv (e x)) = e x := hhomeo.invOn.2 hx
    have h2 := congrFun hFψ (Fin.natAdd k l)
    rw [hFnat] at h2
    show f l (Finv (e x)) = 0
    rw [h2]
    show Fin.append x (0 : Fin ℓ → R) (Fin.natAdd k l) = 0
    rw [Fin.append_right]
    rfl
  have happϕ : ∀ x ∈ D, Fin.append x (ϕ x) = ψ x := by
    intro x hx
    funext i
    induction i using Fin.addCases with
    | left i' =>
      rw [Fin.append_left, hψcast x hx i']
    | right l' =>
      rw [Fin.append_right]
      rfl
  have hfϕ : ∀ x ∈ D, ∀ l, f l (Fin.append x (ϕ x)) = 0 := by
    intro x hx l
    rw [happϕ x hx]
    exact hψzero x hx l
  -- `ϕ(x⁰) = y⁰`
  have hψx0 : ψ x₀ = z₀ := by
    show Finv (e x₀) = z₀
    rw [← hFz0, hhomeo.invOn.1 hz₀U₀]
  have hϕx0 : ϕ x₀ = y₀ := by
    show ψ x₀ ∘ Fin.natAdd k = y₀
    rw [hψx0, hz0]
    exact append_comp_natAdd x₀ y₀
  -- continuity and semialgebraicity of `ϕ` on `D`
  have hecont : Continuous e := continuous_appendZero
  have hDopen : IsOpen D := hV₀open.preimage hecont
  have hemaps : Set.MapsTo e D V₀ := fun x hx => hx
  have hψcont : ContinuousOn ψ D :=
    hhomeo.continuousOn_inv.comp hecont.continuousOn hemaps
  have hϕcont : ContinuousOn ϕ D := by
    have hc : ContinuousOn ((fun w : Fin (k + ℓ) → R => w ∘ Fin.natAdd k) ∘ ψ) D :=
      continuous_projSnd.comp_continuousOn hψcont
    have heq : (fun w : Fin (k + ℓ) → R => w ∘ Fin.natAdd k) ∘ ψ = ϕ := rfl
    rwa [heq] at hc
  have hesa : IsSemialgebraicFunction Set.univ e :=
    isSemialgebraicFunction_appendZero isSemialgebraicSet_univ
  have hDsa : IsSemialgebraicSet D := by
    have h := (proposition_2_83 hesa).2 hV₀sa
    rwa [Set.univ_inter] at h
  have hψsa : IsSemialgebraicFunction D ψ := by
    have h := proposition_2_84 (hesa.mono hDsa (Set.subset_univ D)) hFinvSa hemaps
    have heq : Finv ∘ e = ψ := rfl
    rwa [heq] at h
  have hϕsa : IsSemialgebraicFunction D ϕ := by
    have h := proposition_2_84 hψsa
      (isSemialgebraicFunction_projSnd isSemialgebraicSet_univ) (Set.mapsTo_univ _ _)
    have heq : (fun w : Fin (k + ℓ) → R => w ∘ Fin.natAdd k) ∘ ψ = ϕ := rfl
    rwa [heq] at h
  -- shrink to a product of balls inside the injectivity domain `U₀`
  obtain ⟨ρ, hρ, hball⟩ := isOpen_iff_ball_self.mp hU₀open z₀ hz₀U₀
  have hρ2 : 0 < ρ / 2 := by linarith
  set V : Set (Fin ℓ → R) := openBall y₀ (ρ / 2) with hVdef
  set U : Set (Fin k → R) := (D ∩ ϕ ⁻¹' V) ∩ openBall x₀ (ρ / 2) with hUdef
  have hprodball : ∀ (x : Fin k → R) (y : Fin ℓ → R), x ∈ openBall x₀ (ρ / 2) →
      y ∈ openBall y₀ (ρ / 2) → Fin.append x y ∈ openBall z₀ ρ := by
    intro x y hx hy
    rw [mem_openBall] at hx hy ⊢
    rw [hz0, append_sub_append, euclideanNormSq_append]
    have h4 : (ρ / 2) ^ 2 = ρ ^ 2 / 4 := by ring
    rw [h4] at hx hy
    nlinarith [sq_nonneg ρ]
  have hVsa : IsSemialgebraicSet V := isSemialgebraicSet_openBall y₀ (ρ / 2)
  have hVopen : IsOpen V := isOpen_openBall y₀ hρ2
  have hy0V : y₀ ∈ V := mem_openBall_self y₀ hρ2
  have hx0D : x₀ ∈ D := by
    show e x₀ ∈ V₀
    rw [← hFz0]
    exact hFz₀V₀
  have hx0U : x₀ ∈ U :=
    ⟨⟨hx0D, by show ϕ x₀ ∈ V; rw [hϕx0]; exact hy0V⟩, mem_openBall_self x₀ hρ2⟩
  have hUsub : U ⊆ D := fun x hx => hx.1.1
  have hUsa : IsSemialgebraicSet U :=
    ((proposition_2_83 hϕsa).2 hVsa).inter (isSemialgebraicSet_openBall x₀ (ρ / 2))
  have hUopen : IsOpen U :=
    (hϕcont.isOpen_inter_preimage hDopen hVopen).inter (isOpen_openBall x₀ hρ2)
  -- the equivalence on `U × V`
  have hequiv : ∀ x ∈ U, ∀ y ∈ V, ((∀ l, f l (Fin.append x y) = 0) ↔ y = ϕ x) := by
    intro x hxU y hyV
    constructor
    · intro h0
      have hw1 : Fin.append x y ∈ U₀ := hball (hprodball x y hxU.2 hyV)
      have hw2 : Fin.append x (ϕ x) ∈ U₀ := hball (hprodball x (ϕ x) hxU.2 hxU.1.2)
      have hF1 : F (Fin.append x y) = e x := by
        funext i
        induction i using Fin.addCases with
        | left i' =>
          rw [hFcast]
          show Fin.append x y (Fin.castAdd ℓ i')
            = Fin.append x (0 : Fin ℓ → R) (Fin.castAdd ℓ i')
          rw [Fin.append_left, Fin.append_left]
        | right l =>
          rw [hFnat]
          show f l (Fin.append x y) = Fin.append x (0 : Fin ℓ → R) (Fin.natAdd k l)
          rw [Fin.append_right]
          exact h0 l
      have hF2 : F (Fin.append x (ϕ x)) = e x := by
        funext i
        induction i using Fin.addCases with
        | left i' =>
          rw [hFcast]
          show Fin.append x (ϕ x) (Fin.castAdd ℓ i')
            = Fin.append x (0 : Fin ℓ → R) (Fin.castAdd ℓ i')
          rw [Fin.append_left, Fin.append_left]
        | right l =>
          rw [hFnat]
          show f l (Fin.append x (ϕ x)) = Fin.append x (0 : Fin ℓ → R) (Fin.natAdd k l)
          rw [Fin.append_right]
          exact hfϕ x hxU.1.1 l
      have heqw : Fin.append x y = Fin.append x (ϕ x) :=
        hhomeo.bijOn.injOn hw1 hw2 (by rw [hF1, hF2])
      funext l
      have h2 := congrFun heqw (Fin.natAdd k l)
      rwa [Fin.append_right, Fin.append_right] at h2
    · intro hy
      subst hy
      exact hfϕ x hxU.1.1
  -- the product of the neighborhoods stays inside `W'`
  have hprodsub : setProd U V ⊆ W' := by
    intro z hz
    have h := hprodball (z ∘ Fin.castAdd ℓ) (z ∘ Fin.natAdd k) hz.1.2 hz.2
    rw [append_castAdd_natAdd] at h
    exact hU₀sub (hball h)
  -- the implicit function is `𝒮^{m+1}`: `ϕ_i = (Finv·(natAdd k i)) ∘ (x ↦ (x, 0))`
  have hϕsmooth : ∀ i, IsSFunction (m + 1) U (fun x => ϕ x i) := by
    intro i
    have he_comp : ∀ b : Fin (k + ℓ), IsSFunction (m + 1) D (fun x => e x b) := by
      intro b
      induction b using Fin.addCases with
      | left i'' =>
        have heq : (fun x : Fin k → R => e x (Fin.castAdd ℓ i'')) = fun x => x i'' := by
          funext x
          show Fin.append x (0 : Fin ℓ → R) (Fin.castAdd ℓ i'') = x i''
          rw [Fin.append_left]
        rw [heq]
        exact isSFunction_coord hDsa i'' (m + 1)
      | right j =>
        have heq : (fun x : Fin k → R => e x (Fin.natAdd k j)) = fun _ => (0 : R) := by
          funext x
          show Fin.append x (0 : Fin ℓ → R) (Fin.natAdd k j) = 0
          rw [Fin.append_right]; rfl
        rw [heq]
        exact isSFunction_const hDsa 0 (m + 1)
    have hcomp := isSFunction_comp hDsa hV₀open hemaps (hFinvS (Fin.natAdd k i)) he_comp
    exact (hcomp).mono_set hUsa hUsub
  exact ⟨U, V, ϕ, hUsa, hUopen, hx0U, hVsa, hVopen, hy0V,
    hϕsa.mono hUsa hUsub, hϕcont.mono hUsub, fun x hx => hx.1.2, hϕx0, hprodsub,
    hequiv, hϕsmooth⟩

end Azurite.BPR
