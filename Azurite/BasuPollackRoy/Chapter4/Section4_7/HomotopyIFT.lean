import Azurite.BasuPollackRoy.Chapter4.Section4_7.Theorem_4_104
import Azurite.BasuPollackRoy.Chapter4.Section4_7.JacobianRealify
import Azurite.BasuPollackRoy.Chapter4.Section4_7.HomotopyFamily

/-!
# BPR §4.7: a local implicit function theorem for the homotopy system

This file instantiates the projective implicit function theorem `theorem_4_104` for the homotopy
pencil

`S₍λ:µ₎ = (H₁,λ,µ, …, H_k,λ,µ)`, with `Hᵢ,λ,µ = λ Pᵢ + µ Dᵢ = homotopyPoly P d λ µ i`,

(see `HomotopyFamily.lean`). Near a *non-singular* projective zero `x₀ ∈ ℙ_k(C)` of `S₍p₀₎`
(`p₀ ∈ ℙ_1(C)`), the zeros of `S₍p₎` are locally a single continuous (`𝒮^m`) function of the
parameter `p`, with local uniqueness (`homotopy_local_ift`).

The heavy lifting is supplied by `theorem_4_104`; the work here is the *assembly*: building the
real system `F`/`g` from the complex equations via `realEquiv`, checking the smoothness
hypotheses (each `F l` is a real-polynomial evaluation, hence `𝒮^m`), the determinant hypothesis
(`realifyMatrix` of the complex affine Jacobian, via `isUnit_det_realifyMatrix`), and the
homogeneity-scaling bridge that converts the conclusion's coordinate-form vanishing back to the
`aeval`-on-`rep` form.
-/

namespace Azurite.BPR.Chapter4

open Azurite.BPR (IsSFunction IsSemialgContinuousOn HasPartialDerivAtIn)

open MvPolynomial Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-! ### Partial derivative of a real-polynomial evaluation -/

set_option linter.unusedSectionVars false in
/-- **Partial derivative of `w ↦ eval w Q`.** For a fixed real polynomial `Q`, the `j`-th partial
derivative of its evaluation, within any domain `U`, at any `z`, is `eval z (pderiv j Q)`. (Proved
by `MvPolynomial.induction_on`, using the constant/sum/product derivative rules.) -/
theorem hasPartialDerivAtIn_evalMvPoly {n : ℕ} (Q : MvPolynomial (Fin n) R)
    (U : Set (Fin n → R)) (j : Fin n) (z : Fin n → R) :
    HasPartialDerivAtIn (fun w => eval w Q) U j z (eval z (pderiv j Q)) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact Azurite.BPR.hasPartialDerivAtIn_const a U j z
  | add P P' ihP ihP' =>
    have := ihP.add ihP'
    simpa only [eval_add, map_add] using this
  | mul_X P j' ih =>
    -- write the evaluation as a product of two one-variable functions of the updated coordinate
    have hupd : Function.update z j (z j) = z := Function.update_eq_self j z
    -- second factor: `t ↦ (update z j t) j'`, affine in `t` with slope `if j' = j then 1 else 0`
    have hX : HasPartialDerivAtIn (fun w : Fin n → R => eval w (X j')) U j z
        (eval z (pderiv j (X j'))) := by
      rw [HasPartialDerivAtIn]
      by_cases hjj : j' = j
      · subst hjj
        have heq : (fun t : R => eval (Function.update z j' t) (X j' : MvPolynomial (Fin n) R))
            = fun t => 1 * t + 0 := by
          funext t; rw [eval_X, Function.update_self]; ring
        rw [heq]
        have : eval z (pderiv j' (X j' : MvPolynomial (Fin n) R)) = 1 := by simp
        rw [this]
        exact Azurite.BPR.hasDerivAtIn_affine 1 0 _ _
      · have heq : (fun t : R => eval (Function.update z j t) (X j' : MvPolynomial (Fin n) R))
            = fun _ => z j' := by
          funext t; rw [eval_X, Function.update_of_ne hjj]
        rw [heq]
        have : eval z (pderiv j (X j' : MvPolynomial (Fin n) R)) = 0 := by
          rw [pderiv_X_of_ne hjj, map_zero]
        rw [this]
        exact Azurite.BPR.hasDerivAtIn_const (z j') _ _
    -- product rule for `P * X j'`
    have hmul := ih.mul hX
    -- rewrite the product function and its value to the `pderiv` form
    have hfun : (fun w : Fin n → R => eval w (P * X j'))
        = fun w => (eval w P) * (eval w (X j')) := by
      funext w; rw [eval_mul]
    have hval : (fun w : Fin n → R => eval w P) (Function.update z j (z j))
          * eval z (pderiv j (X j'))
        + (fun w : Fin n → R => eval w (X j')) (Function.update z j (z j))
          * eval z (pderiv j P)
        = eval z (pderiv j (P * X j')) := by
      simp only [hupd]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, eval_add, eval_mul, eval_mul, eval_X]
    rw [hfun]
    rw [HasPartialDerivAtIn] at hmul ⊢
    rw [← hval]
    exact hmul

/-! ### Chart-`j₀` dehomogenization -/

/-- **Dehomogenization in chart `j₀`.** Substitute `1` for the homogeneous coordinate `X_{j₀}` and
keep the other `k` homogeneous coordinates as the affine variables `X₀, …, X_{k-1}` (inserting the
constant `1` at position `j₀`). The result is a polynomial in `k` complex variables. -/
noncomputable def dehomAt (j₀ : Fin (k + 1)) (φ : MvPolynomial (Fin (k + 1)) (Ri R)) :
    MvPolynomial (Fin k) (Ri R) :=
  aeval (Fin.insertNth j₀ (1 : MvPolynomial (Fin k) (Ri R)) X) φ

set_option linter.unusedSectionVars false in
/-- Evaluating `φ` at `insertNth j₀ 1 v` equals evaluating its chart-`j₀` dehomogenization at `v`. -/
theorem aeval_insertNth_one (j₀ : Fin (k + 1)) (φ : MvPolynomial (Fin (k + 1)) (Ri R))
    (v : Fin k → Ri R) :
    aeval (Fin.insertNth j₀ (1 : Ri R) v) φ = aeval v (dehomAt j₀ φ) := by
  rw [dehomAt]
  have h : (aeval v).comp (aeval (Fin.insertNth j₀ (1 : MvPolynomial (Fin k) (Ri R)) X))
      = aeval (Fin.insertNth j₀ (1 : Ri R) v) := by
    rw [comp_aeval]
    congr 1
    funext m
    refine Fin.succAboveCases j₀ ?_ (fun b => ?_) m
    · simp [Fin.insertNth_apply_same]
    · simp [Fin.insertNth_apply_succAbove]
  exact (DFunLike.congr_fun h φ).symm

/-! ### The real coordinate blocks and the complex equations -/

/-- The parameter block `(λ, µ)` reconstructed from a real coordinate vector `z`, in chart `i₀`:
take the first `1 + 1` real entries of `z` (`castAdd` block), read them as one complex number
(`realEquiv.symm`), and insert a `1` at position `i₀`. -/
noncomputable def pcoordsR (i₀ : Fin 2) (z : Fin ((1 + 1) + (k + k)) → R) : Fin 2 → Ri R :=
  Fin.insertNth i₀ (1 : Ri R) (realEquiv.symm (z ∘ Fin.castAdd (k + k)))

/-- The point block `(x₁, …, x_k)` reconstructed from a real coordinate vector `z`, in chart `j₀`:
take the last `k + k` real entries of `z` (`natAdd` block), read them as `k` complex numbers, and
insert a `1` at position `j₀`. -/
noncomputable def xcoordsR (j₀ : Fin (k + 1)) (z : Fin ((1 + 1) + (k + k)) → R) :
    Fin (k + 1) → Ri R :=
  Fin.insertNth j₀ (1 : Ri R) (realEquiv.symm (z ∘ Fin.natAdd (1 + 1)))

/-- The `i`-th complex homotopy equation at the realified coordinates `z`. -/
noncomputable def cEq (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (i : Fin k) (z : Fin ((1 + 1) + (k + k)) → R) : Ri R :=
  aeval (xcoordsR j₀ z) (homotopyPoly P d (pcoordsR i₀ z 0) (pcoordsR i₀ z 1) i)

/-! ### Real/imaginary parts are real polynomials -/

/-- A complex-valued function `f` of a real coordinate vector *has real re/im polynomials* if both
its real and imaginary parts are given by evaluating fixed real polynomials. This predicate is
closed under `+`, `*`, complex constants, and the base maps below; it is the engine that shows each
real homotopy equation `F l` is a real-polynomial evaluation. -/
def HasReImPoly {N : ℕ} (f : (Fin N → R) → Ri R) : Prop :=
  ∃ Qre Qim : MvPolynomial (Fin N) R,
    ∀ z, Ri.reL (f z) = eval z Qre ∧ Ri.imL (f z) = eval z Qim

set_option linter.unusedSectionVars false in
theorem HasReImPoly.add {N : ℕ} {f g : (Fin N → R) → Ri R}
    (hf : HasReImPoly f) (hg : HasReImPoly g) : HasReImPoly (fun z => f z + g z) := by
  obtain ⟨fre, fim, hf⟩ := hf
  obtain ⟨gre, gim, hg⟩ := hg
  refine ⟨fre + gre, fim + gim, fun z => ⟨?_, ?_⟩⟩
  · rw [map_add, eval_add, (hf z).1, (hg z).1]
  · rw [map_add, eval_add, (hf z).2, (hg z).2]

set_option linter.unusedSectionVars false in
theorem HasReImPoly.mul {N : ℕ} {f g : (Fin N → R) → Ri R}
    (hf : HasReImPoly f) (hg : HasReImPoly g) : HasReImPoly (fun z => f z * g z) := by
  obtain ⟨fre, fim, hf⟩ := hf
  obtain ⟨gre, gim, hg⟩ := hg
  refine ⟨fre * gre - fim * gim, fre * gim + fim * gre, fun z => ⟨?_, ?_⟩⟩
  · rw [reL_mul, eval_sub, eval_mul, eval_mul, (hf z).1, (hf z).2, (hg z).1, (hg z).2]
  · rw [imL_mul, eval_add, eval_mul, eval_mul, (hf z).1, (hf z).2, (hg z).1, (hg z).2]

set_option linter.unusedSectionVars false in
/-- A complex constant has real re/im polynomials (the constant polynomials). -/
theorem hasReImPoly_const {N : ℕ} (c : Ri R) : HasReImPoly (fun _ : Fin N → R => c) :=
  ⟨C (Ri.reL c), C (Ri.imL c), fun _ => ⟨by rw [eval_C], by rw [eval_C]⟩⟩

set_option linter.unusedSectionVars false in
/-- For a fixed complex polynomial `φ`, `z ↦ aeval (xcoordsR j₀ z) φ` has real re/im polynomials.
(`xcoordsR j₀ z` reads the point block of `z`; dehomogenize `φ` in chart `j₀` and apply
`exists_reL_imL_aeval` to the resulting `k`-variable complex polynomial, reindexed onto `z`.) -/
theorem hasReImPoly_aeval_xcoordsR (j₀ : Fin (k + 1)) (φ : MvPolynomial (Fin (k + 1)) (Ri R)) :
    HasReImPoly (fun z : Fin ((1 + 1) + (k + k)) → R => aeval (xcoordsR j₀ z) φ) := by
  obtain ⟨Qre, Qim, hQ⟩ := exists_reL_imL_aeval (dehomAt j₀ φ)
  refine ⟨rename (Fin.natAdd (1 + 1)) Qre, rename (Fin.natAdd (1 + 1)) Qim, fun z => ?_⟩
  have hxc : aeval (xcoordsR j₀ z) φ
      = aeval (realEquiv.symm (z ∘ Fin.natAdd (1 + 1))) (dehomAt j₀ φ) := by
    rw [xcoordsR, aeval_insertNth_one]
  show Ri.reL (aeval (xcoordsR j₀ z) φ) = _ ∧ Ri.imL (aeval (xcoordsR j₀ z) φ) = _
  rw [hxc, eval_rename, eval_rename]
  exact hQ (z ∘ Fin.natAdd (1 + 1))

set_option linter.unusedSectionVars false in
/-- Each parameter coordinate `pcoordsR i₀ z a` (for `a : Fin 2`) has real re/im polynomials: it is
either the constant `1` (at `a = i₀`) or one reconstructed complex coordinate of the parameter
block, whose parts are coordinates of `z`. -/
theorem hasReImPoly_pcoordsR (i₀ : Fin 2) (a : Fin 2) :
    HasReImPoly (fun z : Fin ((1 + 1) + (k + k)) → R => pcoordsR i₀ z a) := by
  by_cases ha : a = i₀
  · subst ha
    have hconst : (fun z : Fin ((1 + 1) + (k + k)) → R => pcoordsR a z a)
        = fun _ => (1 : Ri R) := by
      funext z; rw [pcoordsR, Fin.insertNth_apply_same]
    rw [hconst]
    exact hasReImPoly_const 1
  · -- `a = i₀.succAbove b` for the unique `b : Fin 1`
    obtain ⟨b, hb⟩ : ∃ b : Fin 1, i₀.succAbove b = a := Fin.exists_succAbove_eq ha
    refine ⟨X (Fin.castAdd (k + k) (Fin.castAdd 1 b)),
            X (Fin.castAdd (k + k) (Fin.natAdd 1 b)), fun z => ?_⟩
    have hval : pcoordsR i₀ z a = (realEquiv.symm (z ∘ Fin.castAdd (k + k))) b := by
      rw [pcoordsR, ← hb, Fin.insertNth_apply_succAbove]
    simp only [hval]
    constructor
    · rw [reL_symm_apply, eval_X, Function.comp_apply]
    · rw [imL_symm_apply, eval_X, Function.comp_apply]

set_option linter.unusedSectionVars false in
/-- **Each complex homotopy equation has real re/im polynomials.** -/
theorem hasReImPoly_cEq (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (i : Fin k) :
    HasReImPoly (fun z => cEq P d i₀ j₀ i z) := by
  have hsplit : (fun z => cEq P d i₀ j₀ i z)
      = fun z => pcoordsR i₀ z 0 * aeval (xcoordsR j₀ z) (P i)
          + pcoordsR i₀ z 1 * aeval (xcoordsR j₀ z) (diagFactor (R := R) (d i) i) := by
    funext z
    show aeval (xcoordsR j₀ z) (homotopyPoly P d (pcoordsR i₀ z 0) (pcoordsR i₀ z 1) i) = _
    rw [homotopyPoly, map_add, map_mul, map_mul, aeval_C, aeval_C,
      Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply]
  rw [hsplit]
  exact ((hasReImPoly_pcoordsR i₀ 0).mul (hasReImPoly_aeval_xcoordsR j₀ (P i))).add
    ((hasReImPoly_pcoordsR i₀ 1).mul (hasReImPoly_aeval_xcoordsR j₀ (diagFactor (R := R) (d i) i)))

/-! ### The real system `F` and its real-polynomial representatives -/

/-- The real homotopy system: the `(k + k)` real equations obtained by splitting each complex
equation `cEq i` into its real part (the `castAdd` block) and imaginary part (the `natAdd` block). -/
noncomputable def homotopyF (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (l : Fin (k + k)) (z : Fin ((1 + 1) + (k + k)) → R) : R :=
  Fin.addCases (fun l' => Ri.reL (cEq P d i₀ j₀ l' z)) (fun l' => Ri.imL (cEq P d i₀ j₀ l' z)) l

set_option linter.unusedSectionVars false in
/-- **Each real homotopy equation `F l` is a real-polynomial evaluation.** -/
theorem exists_homotopyF_eq_eval (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (l : Fin (k + k)) :
    ∃ Q : MvPolynomial (Fin ((1 + 1) + (k + k))) R,
      ∀ z, homotopyF P d i₀ j₀ l z = eval z Q := by
  refine Fin.addCases (fun l' => ?_) (fun l' => ?_) l
  · obtain ⟨Qre, _, hQ⟩ := hasReImPoly_cEq P d i₀ j₀ l'
    exact ⟨Qre, fun z => by rw [homotopyF, Fin.addCases_left]; exact (hQ z).1⟩
  · obtain ⟨_, Qim, hQ⟩ := hasReImPoly_cEq P d i₀ j₀ l'
    exact ⟨Qim, fun z => by rw [homotopyF, Fin.addCases_right]; exact (hQ z).2⟩

/-! ### Scaling: linearity in `(λ, µ)` -/

set_option linter.unusedSectionVars false in
/-- The homotopy pencil is linear in `(λ, µ)`: scaling both by `s` scales the polynomial by `s`. -/
theorem homotopyPoly_smul (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (s lam mu : Ri R) (i : Fin k) :
    homotopyPoly P d (s * lam) (s * mu) i = C s * homotopyPoly P d lam mu i := by
  rw [homotopyPoly, homotopyPoly, map_mul, map_mul, mul_add]
  ring

set_option linter.unusedSectionVars false in
/-- **The bridge between coordinate-vanishing and `rep`-vanishing.** For `p ∈ 𝒰_{i₀}` and
`x ∈ 𝒰_{j₀}`, all real homotopy equations vanish at the realified chart coordinates of `(p, x)` iff
the (complex) homotopy system vanishes at `x.rep` for the parameter `(p.rep 0, p.rep 1)`. -/
theorem homotopyF_eq_zero_iff (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (p : complexProjectiveSpace R 1)
    (x : complexProjectiveSpace R k) (hp : p ∈ chartSet i₀) (hx : x ∈ chartSet j₀) :
    (∀ l, homotopyF P d i₀ j₀ l
        (Fin.append (realEquiv (chartInv i₀ p)) (realEquiv (chartInv j₀ x))) = 0)
      ↔ (∀ i, aeval x.rep (homotopyPoly P d (p.rep 0) (p.rep 1) i) = 0) := by
  classical
  set z : Fin ((1 + 1) + (k + k)) → R :=
    Fin.append (realEquiv (chartInv i₀ p)) (realEquiv (chartInv j₀ x)) with hz
  -- the point coordinates `xcoordsR j₀ z = insertNth j₀ 1 (chartInv j₀ x)`
  have hzpt : z ∘ Fin.natAdd (1 + 1) = realEquiv (chartInv j₀ x) := by
    funext m; rw [hz, Function.comp_apply, Fin.append_right]
  have hzparam : z ∘ Fin.castAdd (k + k) = realEquiv (chartInv i₀ p) := by
    funext m; rw [hz, Function.comp_apply, Fin.append_left]
  have hxc : xcoordsR j₀ z = Fin.insertNth j₀ (1 : Ri R) (chartInv j₀ x) := by
    rw [xcoordsR, hzpt, Equiv.symm_apply_apply]
  -- the parameter coordinates: `pcoordsR i₀ z = insertNth i₀ 1 (chartInv i₀ p)`
  have hpc : pcoordsR i₀ z = Fin.insertNth i₀ (1 : Ri R) (chartInv i₀ p) := by
    rw [pcoordsR, hzparam, Equiv.symm_apply_apply]
  -- `x.rep = cx • insertNth j₀ 1 (chartInv j₀ x)` with `cx ≠ 0`
  have hxj : x.rep j₀ ≠ 0 := by rw [chartSet_eq] at hx; exact hx
  obtain ⟨cx, hcx, hxrep⟩ :
      ∃ c : Ri R, c ≠ 0 ∧ Fin.insertNth j₀ (1 : Ri R) (chartInv j₀ x) = c • x.rep := by
    have h1 : mkLine (Fin.insertNth j₀ (1 : Ri R) (chartInv j₀ x)) (insertNth_one_ne_zero j₀ _)
        = mkLine x.rep x.rep_nonzero := by
      rw [mkLine_rep]
      conv_rhs => rw [← chartMap_chartInv j₀ x hxj, chartMap]
    exact (mkLine_eq_mkLine_iff _ _ _ _).mp h1
  -- `p.rep = cp • insertNth i₀ 1 (chartInv i₀ p)` with `cp ≠ 0`
  have hpi : p.rep i₀ ≠ 0 := by rw [chartSet_eq] at hp; exact hp
  obtain ⟨cp, hcp, hprep⟩ :
      ∃ c : Ri R, c ≠ 0 ∧ p.rep = c • Fin.insertNth i₀ (1 : Ri R) (chartInv i₀ p) := by
    have h1 : mkLine p.rep p.rep_nonzero
        = mkLine (Fin.insertNth i₀ (1 : Ri R) (chartInv i₀ p)) (insertNth_one_ne_zero i₀ _) := by
      rw [mkLine_rep]
      conv_lhs => rw [← chartMap_chartInv i₀ p hpi]
      rw [chartMap]
    exact (mkLine_eq_mkLine_iff _ _ _ _).mp h1
  -- coordinate-vanishing reduces to vanishing of each `cEq`
  have hcEqzero : (∀ l, homotopyF P d i₀ j₀ l z = 0) ↔ (∀ l', cEq P d i₀ j₀ l' z = 0) := by
    constructor
    · intro h l'
      rw [reL_eq_zero_and_imL_eq_zero_iff]
      constructor
      · have := h (Fin.castAdd k l'); rwa [homotopyF, Fin.addCases_left] at this
      · have := h (Fin.natAdd k l'); rwa [homotopyF, Fin.addCases_right] at this
    · intro h l
      refine Fin.addCases (fun l' => ?_) (fun l' => ?_) l
      · rw [homotopyF, Fin.addCases_left, h l', map_zero]
      · rw [homotopyF, Fin.addCases_right, h l', map_zero]
  rw [hcEqzero]
  -- `cEq l' z = aeval (insertNth j₀ 1 (chartInv j₀ x)) (homotopyPoly ... (pcoords)) `
  refine forall_congr' fun l' => ?_
  rw [cEq, hxc]
  -- relate the chart `(λ,µ)` to `p.rep` (differ by `cp`)
  have hparam0 : pcoordsR i₀ z 0 = cp⁻¹ * p.rep 0 := by
    rw [hpc, hprep, Pi.smul_apply, smul_eq_mul]; field_simp
  have hparam1 : pcoordsR i₀ z 1 = cp⁻¹ * p.rep 1 := by
    rw [hpc, hprep, Pi.smul_apply, smul_eq_mul]; field_simp
  rw [hparam0, hparam1]
  -- scale `(λ,µ)` out: homotopy at `(cp⁻¹ p.rep 0, cp⁻¹ p.rep 1)` is `C cp⁻¹ * homotopy at p.rep`
  rw [homotopyPoly_smul, map_mul, aeval_C, Algebra.algebraMap_self_apply]
  -- scale the point out via homogeneity
  rw [hxrep, aeval_smul_isHomogeneous (homotopyPoly_isHomogeneous P d hP _ _ l')]
  constructor
  · intro h
    have hcxpow : (cx : Ri R) ^ d l' ≠ 0 := pow_ne_zero _ hcx
    have hcpinv : (cp⁻¹ : Ri R) ≠ 0 := inv_ne_zero hcp
    -- `cp⁻¹ * (cx^{d} * aeval x.rep (homotopy at p.rep)) = 0`  ⟹  aeval = 0
    have h2 : cx ^ d l' * aeval x.rep (homotopyPoly P d (p.rep 0) (p.rep 1) l') = 0 :=
      (mul_eq_zero.mp h).resolve_left hcpinv
    exact (mul_eq_zero.mp h2).resolve_left hcxpow
  · intro h
    rw [h, mul_zero, mul_zero]

/-! ### The chosen real-polynomial representatives and the derived data -/

open Classical in
/-- A choice of real polynomial representing the `l`-th real homotopy equation `F l`. -/
noncomputable def homotopyQ (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (l : Fin (k + k)) : MvPolynomial (Fin ((1 + 1) + (k + k))) R :=
  (exists_homotopyF_eq_eval P d i₀ j₀ l).choose

set_option linter.unusedSectionVars false in
theorem homotopyF_eq_eval_homotopyQ (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (l : Fin (k + k)) (z : Fin ((1 + 1) + (k + k)) → R) :
    homotopyF P d i₀ j₀ l z = eval z (homotopyQ P d i₀ j₀ l) :=
  (exists_homotopyF_eq_eval P d i₀ j₀ l).choose_spec z

/-- The `g`-data for the IFT: the partial derivatives of the representing polynomials. -/
noncomputable def homotopyG (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (l : Fin (k + k)) (j : Fin ((1 + 1) + (k + k)))
    (z : Fin ((1 + 1) + (k + k)) → R) : R :=
  eval z (pderiv j (homotopyQ P d i₀ j₀ l))

set_option linter.unusedSectionVars false in
/-- `hF`: each `F l` is semialgebraic and continuous on the full real coordinate space. -/
theorem homotopyF_isSemialgContinuousOn (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (i₀ : Fin 2) (j₀ : Fin (k + 1)) (l : Fin (k + k)) :
    IsSemialgContinuousOn (Set.univ : Set (Fin ((1 + 1) + (k + k)) → R))
      (homotopyF P d i₀ j₀ l) := by
  have heq : homotopyF P d i₀ j₀ l = fun z => eval z (homotopyQ P d i₀ j₀ l) :=
    funext (homotopyF_eq_eval_homotopyQ P d i₀ j₀ l)
  rw [heq]
  exact (isSFunction_evalMvPoly Azurite.BPR.isSemialgebraicSet_univ _ 0)

set_option linter.unusedSectionVars false in
/-- `hgS`: each `g l j` is `𝒮^m` on the full real coordinate space. -/
theorem homotopyG_isSFunction (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (m : ℕ) (l : Fin (k + k)) (j : Fin ((1 + 1) + (k + k))) :
    IsSFunction m (Set.univ : Set (Fin ((1 + 1) + (k + k)) → R)) (homotopyG P d i₀ j₀ l j) :=
  isSFunction_evalMvPoly Azurite.BPR.isSemialgebraicSet_univ _ m

set_option linter.unusedSectionVars false in
/-- `hdiff`: `g l j` is the `j`-th partial derivative of `F l` everywhere. -/
theorem homotopyF_hasPartialDerivAtIn (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (i₀ : Fin 2) (j₀ : Fin (k + 1)) (l : Fin (k + k))
    (j : Fin ((1 + 1) + (k + k))) (z : Fin ((1 + 1) + (k + k)) → R) :
    HasPartialDerivAtIn (homotopyF P d i₀ j₀ l) Set.univ j z (homotopyG P d i₀ j₀ l j z) := by
  have heq : homotopyF P d i₀ j₀ l = fun z => eval z (homotopyQ P d i₀ j₀ l) :=
    funext (homotopyF_eq_eval_homotopyQ P d i₀ j₀ l)
  rw [heq, homotopyG]
  exact hasPartialDerivAtIn_evalMvPoly _ _ j z

/-! ### The local implicit function theorem for the homotopy system -/

/-- **Local implicit function theorem for the homotopy pencil.** Near a non-singular projective zero
`x₀ ∈ ℙ_k(C)` of the system `S₍p₀₎ = (H₁,p₀, …, H_k,p₀)` (`p₀ ∈ ℙ_1(C)`), the zeros of `S₍p₎` are
locally a single `𝒮^m` function `ϕ` of the parameter `p`, with local uniqueness.

This is `theorem_4_104` instantiated for the homotopy family `homotopyPoly P d λ µ`. The conclusion
is in the projective IFT's native realified-coordinate form: for `p ∈ U`, `x ∈ V`, the realified
homotopy system `F` vanishes at the chart-`(i₀,j₀)` coordinates of `(p, x)` iff `x = ϕ p`. The
homogeneity-scaling bridge `homotopyF_eq_zero_iff` rewrites the coordinate-form vanishing
`∀ l, F l (…) = 0` into the intrinsic form `∀ i, aeval x.rep (homotopyPoly P d (p.rep 0) (p.rep 1) i)
= 0` for any `p ∈ 𝒰_{i₀}`, `x ∈ 𝒰_{j₀}`.

All of the projective IFT's smoothness hypotheses are discharged from the real-polynomial structure
of the (realified) homotopy equations; the determinant (transversality) hypothesis `hdet` — the
realification of the complex affine Jacobian being invertible — is taken as an explicit input. (In
`JacobianRealify.lean`, `isUnit_det_realifyMatrix` / `isUnit_det_realifyMatrix_jacobian_dehom`
supply this kind of invertibility from the rank-`k` non-singularity condition.) -/
theorem homotopy_local_ift (m : ℕ) (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    (p₀ : complexProjectiveSpace R 1) (x₀ : complexProjectiveSpace R k)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (hp₀ : p₀ ∈ chartSet i₀) (hx₀ : x₀ ∈ chartSet j₀)
    (hzero : ∀ i, aeval x₀.rep (homotopyPoly P d (p₀.rep 0) (p₀.rep 1) i) = 0)
    (hdet : IsUnit (Matrix.of fun l j : Fin (k + k) =>
      homotopyG P d i₀ j₀ l (Fin.natAdd (1 + 1) j)
        (Fin.append (realEquiv (chartInv i₀ p₀)) (realEquiv (chartInv j₀ x₀)))).det) :
    ∃ (U : Set (complexProjectiveSpace R 1)) (V : Set (complexProjectiveSpace R k))
      (ϕ : complexProjectiveSpace R 1 → complexProjectiveSpace R k),
      IsOpen U ∧ p₀ ∈ U ∧ IsOpen V ∧ x₀ ∈ V ∧ ϕ p₀ = x₀ ∧
      IsSClassMapP m U V ϕ ∧
      (∀ p ∈ U, ∀ x ∈ V,
        ((∀ l, homotopyF P d i₀ j₀ l
            (Fin.append (realEquiv (chartInv i₀ p)) (realEquiv (chartInv j₀ x))) = 0)
          ↔ x = ϕ p)) := by
  classical
  -- the base point in realified coordinates
  set z₀ : Fin ((1 + 1) + (k + k)) → R :=
    Fin.append (realEquiv (chartInv i₀ p₀)) (realEquiv (chartInv j₀ x₀)) with hz₀
  -- `hF0`: the real system vanishes at the base point (from `hzero` via the bridge)
  have hF0 : ∀ l, homotopyF P d i₀ j₀ l z₀ = 0 :=
    (homotopyF_eq_zero_iff P d hP i₀ j₀ p₀ x₀ hp₀ hx₀).mpr hzero
  -- assemble all hypotheses of `theorem_4_104` (with `k_104 := 1`, `ℓ_104 := k`)
  obtain ⟨U, V, ϕ, hUsa, hUopen, hp₀U, hVsa, hVopen, hx₀V, hϕclass, hϕp₀, himpl⟩ :=
    theorem_4_104 (k := 1) (ℓ := k) m p₀ x₀ i₀ j₀ hp₀ hx₀
      (Set.univ : Set (Fin ((1 + 1) + (k + k)) → R)) isOpen_univ
      Azurite.BPR.isSemialgebraicSet_univ
      (homotopyF P d i₀ j₀) (homotopyG P d i₀ j₀)
      (Set.mem_univ _)
      (fun l => homotopyF_isSemialgContinuousOn P d i₀ j₀ l)
      (fun l j z _ => homotopyF_hasPartialDerivAtIn P d i₀ j₀ l j z)
      (fun l j => (homotopyG_isSFunction P d i₀ j₀ 0 l j).isSemialgContinuousOn)
      hF0
      hdet
      (fun l j => homotopyG_isSFunction P d i₀ j₀ m l j)
  exact ⟨U, V, ϕ, hUopen, hp₀U, hVopen, hx₀V, hϕp₀, hϕclass, himpl⟩

end Azurite.BPR.Chapter4
