import Azurite.BasuPollackRoy.Chapter3.Section3_3.BivariateEval
import Azurite.BasuPollackRoy.Chapter3.Section3_2.Proposition_3_9
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Corollary_2_24
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Definition_2_45.Internal
import Azurite.BasuPollackRoy.Chapter2.Section2_3.FiberFormula
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83

/-! # BPR §3.3, Proposition 3.10 — semialgebraic implicit function theorem

Let `P` be a univariate polynomial in `Y` with semialgebraic continuous coefficients on a
semialgebraic set `S ⊆ R^k`. If `y` is a *simple root* of the specialization `P(x, Y)` (so
`P(x, y) = 0` and `∂P/∂Y (x, y) ≠ 0`), then there is a semialgebraic continuous function `f` on a
relatively open neighborhood `U` of `x` in `S` with `f(x) = y` and `f(x')` a simple root of
`P(x', Y)` for every `x' ∈ U`.

The implicit root `f(u)` is the unique zero of `P(u, ·)` in a small interval `(a, b)` around `y`,
located by the intermediate value theorem (`hasIVP_of_isRealClosed`) and pinned down by strict
monotonicity of `P(u, ·)` there (`corollary_2_24_increasing`, valid because `∂P/∂Y > 0` on a box
around `(x, y)`). Semialgebraicity and continuity of `f` come from the bivariate evaluation being a
semialgebraic continuous function (`BivariateEval`). -/

namespace Azurite.BPR

open Polynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### The slice embedding `u ↦ (u, c)` -/

/-- The embedding `R^k → R^{k+1}`, `u ↦ (u, c)` (append the constant `c` as the last coordinate), as
a polynomial map. -/
noncomputable def sliceEmbed (c : R) : (Fin k → R) → (Fin (k + 1) → R) :=
  polynomialMap (Fin.lastCases (MvPolynomial.C c) (fun i => MvPolynomial.X i))

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem sliceEmbed_apply (c : R) (u : Fin k → R) : sliceEmbed c u = Fin.snoc u c := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [sliceEmbed, polynomialMap, Fin.snoc_last]
  · simp [sliceEmbed, polynomialMap, Fin.snoc_castSucc]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem sliceEmbed_proj (c : R) (u : Fin k → R) :
    sliceEmbed c u ∘ Fin.castAdd 1 = u := by
  rw [sliceEmbed_apply]; exact Fin.snoc_comp_castSucc

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem sliceEmbed_last (c : R) (u : Fin k → R) :
    sliceEmbed c u (Fin.natAdd k 0) = c := by
  rw [sliceEmbed_apply]
  have : (Fin.natAdd k 0 : Fin (k + 1)) = Fin.last k := by
    apply Fin.ext; simp
  rw [this, Fin.snoc_last]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The bivariate evaluation along the slice `z = c` is the specialized one-variable evaluation. -/
theorem bivariateEval_sliceEmbed (P : Polynomial ((Fin k → R) → R)) (c : R) (u : Fin k → R) :
    bivariateEval P (sliceEmbed c u) = constPt ((specializeAt P u).eval c) := by
  rw [bivariateEval, sliceEmbed_proj, sliceEmbed_last]

omit [IsRealClosed R] in
theorem isSemialgebraicFunction_sliceEmbed {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    (c : R) : IsSemialgebraicFunction S (sliceEmbed c) :=
  isSemialgebraicFunction_polynomialMap hS _

theorem continuous_sliceEmbed (c : R) : Continuous (sliceEmbed (k := k) c) :=
  continuous_polynomialMap _

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem sliceEmbed_mapsTo {S : Set (Fin k → R)} (c : R) :
    Set.MapsTo (sliceEmbed c) S (setProd S (Set.univ : Set (Fin 1 → R))) := by
  intro u hu
  refine ⟨?_, by trivial⟩
  rw [sliceEmbed_proj]; exact hu

/-! ### The one-variable slice `u ↦ P(u, c)` is semialgebraic and continuous on `S` -/

/-- The slice function `u ↦ P(u, c)`, as a line-valued function on `R^k`. -/
noncomputable def sliceFun (P : Polynomial ((Fin k → R) → R)) (c : R) :
    (Fin k → R) → (Fin 1 → R) :=
  fun u => constPt ((specializeAt P u).eval c)

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem sliceFun_eq (P : Polynomial ((Fin k → R) → R)) (c : R) :
    sliceFun P c = bivariateEval P ∘ sliceEmbed c := by
  funext u; rw [Function.comp_apply, bivariateEval_sliceEmbed]; rfl

theorem isSemialgebraicFunction_sliceFun {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {P : Polynomial ((Fin k → R) → R)} (hP : HasSemialgContinuousCoeffs S P) (c : R) :
    IsSemialgebraicFunction S (sliceFun P c) := by
  rw [sliceFun_eq]
  exact proposition_2_84 (isSemialgebraicFunction_sliceEmbed hS c)
    (isSemialgebraicFunction_bivariateEval hS hP) (sliceEmbed_mapsTo c)

theorem continuousOn_sliceFun {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {P : Polynomial ((Fin k → R) → R)} (hP : HasSemialgContinuousCoeffs S P) (c : R) :
    ContinuousOn (sliceFun P c) S := by
  rw [sliceFun_eq]
  exact (continuousOn_bivariateEval hS hP).comp (continuous_sliceEmbed c).continuousOn
    (sliceEmbed_mapsTo c)

/-! ### The partial derivative `∂P/∂Y` and its coefficients -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Specializing the formal `Y`-derivative is the same as differentiating the specialization. -/
theorem specializeAt_derivative (P : Polynomial ((Fin k → R) → R)) (u : Fin k → R) :
    specializeAt (Polynomial.derivative P) u = (specializeAt P u).derivative := by
  rw [specializeAt, specializeAt, Polynomial.derivative_map]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- `scalarFun` commutes with natural scaling. -/
theorem scalarFun_nsmul (n : ℕ) (c : (Fin k → R) → R) :
    scalarFun (n • c) = n • scalarFun c := by
  funext u j; simp [scalarFun, constPt, Pi.smul_apply]

/-- If every coefficient of `P` is semialgebraic continuous on `S`, then so is every coefficient of
the formal `Y`-derivative `∂P/∂Y` (each is a natural multiple of a coefficient of `P`). -/
theorem HasSemialgContinuousCoeffs.derivative {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {P : Polynomial ((Fin k → R) → R)} (hP : HasSemialgContinuousCoeffs S P) :
    HasSemialgContinuousCoeffs S (Polynomial.derivative P) := by
  intro i
  have hcoeff : (Polynomial.derivative P).coeff i = (i + 1) • P.coeff (i + 1) := by
    rw [Polynomial.coeff_derivative, nsmul_eq_mul, mul_comm]; push_cast; ring
  have hmem : scalarFun (P.coeff (i + 1)) ∈ continuousSemialgebraicFunctions hS := hP (i + 1)
  show scalarFun ((Polynomial.derivative P).coeff i) ∈ continuousSemialgebraicFunctions hS
  rw [hcoeff, scalarFun_nsmul]
  exact nsmul_mem hmem (i + 1)

/-! ### A box around `(x, y)` on which `∂P/∂Y > 0` -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The squared norm splits across the `snoc` (the last coordinate `t` vs the first `k`). -/
theorem euclideanNormSq_snoc_sub (u x : Fin k → R) (t y : R) :
    euclideanNormSq (Fin.snoc u t - Fin.snoc x y : Fin (k + 1) → R)
      = euclideanNormSq (u - x) + (t - y) ^ 2 := by
  simp only [euclideanNormSq, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.sub_apply, Pi.sub_apply, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Pi.sub_apply, Fin.snoc_last, Fin.snoc_last]

/-- **Box of positive `Y`-derivative.** If `∂P/∂Y(x, y) > 0`, there is a radius `ρ > 0` such that
`∂P/∂Y(u, t) > 0` whenever `u ∈ S` is within `ρ` of `x` and `t` is within `ρ/2` of `y`. -/
theorem exists_box_deriv_pos {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {P : Polynomial ((Fin k → R) → R)} (hP : HasSemialgContinuousCoeffs S P) {x : Fin k → R}
    (hx : x ∈ S) {y : R} (hpos : 0 < (specializeAt P x).derivative.eval y) :
    ∃ ρ : R, 0 < ρ ∧ ∀ u ∈ S, euclideanNorm (u - x) < ρ → ∀ t : R, |t - y| ≤ ρ / 2 →
      0 < (specializeAt P u).derivative.eval t := by
  set P' := Polynomial.derivative P with hP'def
  have hP' : HasSemialgContinuousCoeffs S P' := hP.derivative hS
  have hcont : ContinuousOn (bivariateEval P') (setProd S (Set.univ : Set (Fin 1 → R))) :=
    continuousOn_bivariateEval hS hP'
  -- value of `∂P/∂Y` at `(x, y)`
  have hval : bivariateEval P' (sliceEmbed y x) 0 = (specializeAt P x).derivative.eval y := by
    rw [bivariateEval_sliceEmbed, hP'def, specializeAt_derivative]; rfl
  rw [continuousOn_fin_one_iff] at hcont
  obtain ⟨δ, hδ, hδspec⟩ :=
    hcont (sliceEmbed y x) (sliceEmbed_mapsTo y hx) (bivariateEval P' (sliceEmbed y x) 0)
      (by rw [hval]; exact hpos)
  refine ⟨δ / 2, by linarith, fun u hu hunorm t htnorm => ?_⟩
  -- the point `(u, t)` is within `δ` of `(x, y)`
  have hnormlt : euclideanNorm (sliceEmbed t u - sliceEmbed y x) < δ := by
    have hsq : euclideanNormSq (sliceEmbed t u - sliceEmbed y x)
        = euclideanNormSq (u - x) + (t - y) ^ 2 := by
      rw [sliceEmbed_apply, sliceEmbed_apply]; exact euclideanNormSq_snoc_sub u x t y
    have hux : euclideanNormSq (u - x) = euclideanNorm (u - x) ^ 2 := (euclideanNorm_sq _).symm
    have hnnux := euclideanNorm_nonneg (u - x)
    have hnn := euclideanNorm_nonneg (sliceEmbed t u - sliceEmbed y x)
    have hsqnorm := euclideanNorm_sq (sliceEmbed t u - sliceEmbed y x)
    have hlt : euclideanNormSq (sliceEmbed t u - sliceEmbed y x) < δ ^ 2 := by
      nlinarith [hsq, hux, hunorm, hnnux, htnorm, abs_nonneg (t - y), sq_abs (t - y), hδ]
    nlinarith [hsqnorm, hlt, hnn, hδ]
  -- conclude positivity at `(u, t)`
  have hb := hδspec (sliceEmbed t u) (sliceEmbed_mapsTo t hu) hnormlt
  have hgt : bivariateEval P' (sliceEmbed t u) 0 = (specializeAt P u).derivative.eval t := by
    rw [bivariateEval_sliceEmbed, hP'def, specializeAt_derivative]; rfl
  rw [hgt] at hb
  rw [hval] at hb
  -- `|∂P/∂Y(u,t) - ∂P/∂Y(x,y)| < ∂P/∂Y(x,y)` forces `∂P/∂Y(u,t) > 0`
  have := abs_lt.mp hb
  linarith [this.1]

/-! ### Proposition 3.10, positive-derivative case -/

/-- **BPR Proposition 3.10, the case `∂P/∂Y(x, y) > 0`.** -/
theorem proposition_3_10_pos {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {P : Polynomial ((Fin k → R) → R)} (hP : HasSemialgContinuousCoeffs S P) {x : Fin k → R}
    (hx : x ∈ S) {y : R} (hy0 : (specializeAt P x).eval y = 0)
    (hpos : 0 < (specializeAt P x).derivative.eval y) :
    ∃ U : Set (Fin k → R), IsSemialgebraicSet U ∧ IsOpenIn S U ∧ x ∈ U ∧
      ∃ f : (Fin k → R) → R, IsSemialgContinuousOn U f ∧ f x = y ∧
        (∀ x' ∈ U, IsSimpleRoot (specializeAt P x') (f x')) ∧
        ∃ a b, a < y ∧ y < b ∧ ∀ x' ∈ U, f x' ∈ Set.Ioo a b ∧
          ∀ c ∈ Set.Ioo a b, (specializeAt P x').eval c = 0 → c = f x' := by
  classical
  obtain ⟨ρ, hρ, hbox⟩ := exists_box_deriv_pos hS hP hx hpos
  set a := y - ρ / 2 with hadef
  set b := y + ρ / 2 with hbdef
  have ha : a < y := by rw [hadef]; linarith
  have hb : y < b := by rw [hbdef]; linarith
  have hab : a < b := lt_trans ha hb
  -- positivity of `∂P/∂Y` on `[a, b]` for `u` near `x`
  have hderiv : ∀ u ∈ S, euclideanNorm (u - x) < ρ → ∀ t ∈ Set.Icc a b,
      0 < (specializeAt P u).derivative.eval t := by
    intro u hu hun t ht
    refine hbox u hu hun t ?_
    rw [hadef] at ht; rw [hbdef] at ht
    rw [abs_le]; constructor <;> [linarith [ht.1]; linarith [ht.2]]
  -- strict monotonicity of `P(u, ·)` on `[a, b]`
  have hmono : ∀ u ∈ S, euclideanNorm (u - x) < ρ →
      StrictMonoOn (fun t => (specializeAt P u).eval t) (Set.Icc a b) := by
    intro u hu hun
    exact Corollary2_24.corollary_2_24_increasing hasIVP_of_isRealClosed (specializeAt P u) hab
      (fun t ht => hderiv u hu hun t ⟨ht.1.le, ht.2.le⟩)
  -- the neighborhood `U`
  set U : Set (Fin k → R) :=
    {u | u ∈ S ∧ euclideanNorm (u - x) < ρ ∧ (specializeAt P u).eval a < 0 ∧
      0 < (specializeAt P u).eval b} with hUdef
  have hmemU : ∀ u, u ∈ U ↔ u ∈ S ∧ euclideanNorm (u - x) < ρ ∧
      (specializeAt P u).eval a < 0 ∧ 0 < (specializeAt P u).eval b := fun u => Iff.rfl
  have hUS : U ⊆ S := fun u hu => hu.1
  -- `x ∈ U`
  have hxnorm : euclideanNorm (x - x) < ρ :=
    (mem_openBall_iff_norm hρ).mp (mem_openBall_self x hρ)
  have hmonox := hmono x hx hxnorm
  have hxU : x ∈ U := by
    rw [hmemU]
    refine ⟨hx, hxnorm, ?_, ?_⟩
    · have := hmonox ⟨le_refl a, hab.le⟩ ⟨ha.le, hb.le⟩ ha
      simpa [hy0] using this
    · have := hmonox ⟨ha.le, hb.le⟩ ⟨hab.le, le_refl b⟩ hb
      simpa [hy0] using this
  -- existence and uniqueness of the root in `(a, b)`
  have hexU : ∀ u ∈ U, ∃! c : R, c ∈ Set.Ioo a b ∧ (specializeAt P u).eval c = 0 := by
    intro u hu
    rw [hmemU] at hu
    refine VirtualRoots.Internal.exists_unique_root_of_strictMonoOn_Icc hasIVP_of_isRealClosed
      hab (hmono u hu.1 hu.2.1) ?_
    exact mul_neg_of_neg_of_pos hu.2.2.1 hu.2.2.2
  -- the implicit root function
  set f : (Fin k → R) → R := fun u => if h : u ∈ U then ((hexU u h).exists).choose else y
    with hfdef
  have hf_spec : ∀ u (h : u ∈ U),
      f u ∈ Set.Ioo a b ∧ (specializeAt P u).eval (f u) = 0 := by
    intro u h; rw [hfdef]; simp only [dite_eq_left h]; exact ((hexU u h).exists).choose_spec
  have hf_eq : ∀ u (h : u ∈ U) (c : R), c ∈ Set.Ioo a b → (specializeAt P u).eval c = 0 →
      c = f u := fun u h c hc hc0 => (hexU u h).unique ⟨hc, hc0⟩ (hf_spec u h)
  -- `f x = y`
  have hf_x : f x = y := (hf_eq x hxU y (Set.mem_Ioo.mpr ⟨ha, hb⟩) hy0).symm
  -- `f u` is a simple root for `u ∈ U`
  have hsimple : ∀ x' ∈ U, IsSimpleRoot (specializeAt P x') (f x') := by
    intro u hu
    obtain ⟨hfmem, hf0⟩ := hf_spec u hu
    refine ⟨hf0, ne_of_gt ?_⟩
    rw [hmemU] at hu
    exact hderiv u hu.1 hu.2.1 (f u) ⟨hfmem.1.le, hfmem.2.le⟩
  -- `U` is semialgebraic
  have hunivSA : IsSemialgebraicSet (Set.univ : Set (Fin 1 → R)) := by
    have he : (Set.univ : Set (Fin 1 → R))
        = {x | MvPolynomial.eval x (0 : MvPolynomial (Fin 1) R) = 0} := by ext x; simp
    rw [he]; exact IsSemialgebraicSet.eqZero 0
  have hUsa : IsSemialgebraicSet U := by
    have e1 : IsSemialgebraicSet (S ∩ openBall x ρ) := hS.inter (isSemialgebraicSet_openBall x ρ)
    have e2 := (proposition_2_83 (isSemialgebraicFunction_sliceFun hS hP a)).2
      (IsSemialgebraicSet.ltZero (MvPolynomial.X 0))
    have e3 := (proposition_2_83 (isSemialgebraicFunction_sliceFun hS hP b)).2
      (IsSemialgebraicSet.gtZero (MvPolynomial.X 0))
    have hUeq : U = (S ∩ openBall x ρ)
        ∩ (S ∩ sliceFun P a ⁻¹' {v | MvPolynomial.eval v (MvPolynomial.X 0) < 0})
        ∩ (S ∩ sliceFun P b ⁻¹' {v | 0 < MvPolynomial.eval v (MvPolynomial.X 0)}) := by
      ext u
      simp only [hUdef, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
        mem_openBall_iff_norm hρ, sliceFun, constPt, MvPolynomial.eval_X]
      constructor
      · rintro ⟨hS', hn, ha', hb'⟩; exact ⟨⟨⟨hS', hn⟩, hS', ha'⟩, hS', hb'⟩
      · rintro ⟨⟨⟨hS', hn⟩, _, ha'⟩, _, hb'⟩; exact ⟨hS', hn, ha', hb'⟩
    rw [hUeq]; exact (e1.inter e2).inter e3
  -- `U` is open in `S`
  have hUopen : IsOpenIn S U := by
    refine isOpenIn_of_forall_mem hUS (fun u₀ hu₀ => ?_)
    rw [hmemU] at hu₀
    obtain ⟨hu₀S, hu₀n, hu₀a, hu₀b⟩ := hu₀
    have hca := continuousOn_sliceFun hS hP a
    have hcb := continuousOn_sliceFun hS hP b
    rw [continuousOn_fin_one_iff] at hca hcb
    obtain ⟨δ1, hδ1, h1⟩ := hca u₀ hu₀S (-(specializeAt P u₀).eval a) (by linarith)
    obtain ⟨δ2, hδ2, h2⟩ := hcb u₀ hu₀S ((specializeAt P u₀).eval b) (by linarith)
    have hδ3 : 0 < ρ - euclideanNorm (u₀ - x) := by linarith
    have hδpos : 0 < min (ρ - euclideanNorm (u₀ - x)) (min δ1 δ2) := lt_min hδ3 (lt_min hδ1 hδ2)
    refine ⟨openBall u₀ (min (ρ - euclideanNorm (u₀ - x)) (min δ1 δ2)),
      isOpen_openBall u₀ hδpos, mem_openBall_self u₀ hδpos, ?_⟩
    rintro u ⟨huball, huS⟩
    rw [mem_openBall_iff_norm hδpos] at huball
    have hbd1 : euclideanNorm (u - u₀) < δ1 :=
      lt_of_lt_of_le huball (le_trans (min_le_right _ _) (min_le_left _ _))
    have hbd2 : euclideanNorm (u - u₀) < δ2 :=
      lt_of_lt_of_le huball (le_trans (min_le_right _ _) (min_le_right _ _))
    have hbd3 : euclideanNorm (u - u₀) < ρ - euclideanNorm (u₀ - x) :=
      lt_of_lt_of_le huball (min_le_left _ _)
    rw [hmemU]
    refine ⟨huS, ?_, ?_, ?_⟩
    · calc euclideanNorm (u - x) = euclideanNorm ((u - u₀) + (u₀ - x)) := by rw [sub_add_sub_cancel]
        _ ≤ euclideanNorm (u - u₀) + euclideanNorm (u₀ - x) := euclideanNorm_add_le _ _
        _ < ρ := by linarith
    · have hh := h1 u huS hbd1
      simp only [sliceFun, constPt] at hh
      rw [abs_lt] at hh; linarith [hh.2]
    · have hh := h2 u huS hbd2
      simp only [sliceFun, constPt] at hh
      rw [abs_lt] at hh; linarith [hh.1]
  -- `scalarFun f` is semialgebraic on `U`
  have hSAf : IsSemialgebraicFunction U (scalarFun f) := by
    have hbivsa := isSemialgebraicFunction_bivariateEval hS hP
    have hG4 : IsSemialgebraicSet (setProd S (Set.univ : Set (Fin 1 → R)) ∩
        bivariateEval P ⁻¹' {v : Fin 1 → R | MvPolynomial.eval v (MvPolynomial.X 0) = 0}) :=
      (proposition_2_83 hbivsa).2 (IsSemialgebraicSet.eqZero (MvPolynomial.X 0))
    have hGsa : IsSemialgebraicSet (setProd U (Set.univ : Set (Fin 1 → R))
        ∩ {z | 0 < MvPolynomial.eval z (MvPolynomial.X (Fin.natAdd k 0) - MvPolynomial.C a)}
        ∩ {z | MvPolynomial.eval z (MvPolynomial.X (Fin.natAdd k 0) - MvPolynomial.C b) < 0}
        ∩ (setProd S (Set.univ : Set (Fin 1 → R)) ∩
            bivariateEval P ⁻¹' {v : Fin 1 → R | MvPolynomial.eval v (MvPolynomial.X 0) = 0})) :=
      (((hUsa.prod hunivSA).inter (IsSemialgebraicSet.gtZero _)).inter
        (IsSemialgebraicSet.ltZero _)).inter hG4
    rw [IsSemialgebraicFunction]
    convert hGsa using 1
    ext z
    simp only [mem_funGraph, setProd, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_univ, and_true, scalarFun, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
    have hbiv : bivariateEval P z 0
        = (specializeAt P (z ∘ Fin.castAdd 1)).eval (z (Fin.natAdd k 0)) := rfl
    constructor
    · rintro ⟨hzU, hzf⟩
      have hlast : z (Fin.natAdd k 0) = f (z ∘ Fin.castAdd 1) := congrFun hzf 0
      obtain ⟨hfmem, hf0⟩ := hf_spec (z ∘ Fin.castAdd 1) hzU
      refine ⟨⟨⟨hzU, by rw [hlast]; linarith [hfmem.1]⟩, by rw [hlast]; linarith [hfmem.2]⟩,
        hUS hzU, ?_⟩
      rw [hbiv, hlast]; exact hf0
    · rintro ⟨⟨⟨hzU, haz⟩, hbz⟩, _, h0z⟩
      refine ⟨hzU, ?_⟩
      funext j
      rw [Subsingleton.elim j 0]
      have hroot : (specializeAt P (z ∘ Fin.castAdd 1)).eval (z (Fin.natAdd k 0)) = 0 := by
        rw [← hbiv]; exact h0z
      exact hf_eq (z ∘ Fin.castAdd 1) hzU (z (Fin.natAdd k 0))
        (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) hroot
  -- `scalarFun f` is continuous on `U`
  have hContf : ContinuousOn (scalarFun f) U := by
    rw [continuousOn_fin_one_iff]
    intro u₀ hu₀ r hr
    obtain ⟨hz₀mem, hz₀0⟩ := hf_spec u₀ hu₀
    set z₀ := f u₀ with hz₀def
    set ε := min (min ((z₀ - a) / 2) ((b - z₀) / 2)) r with hεdef
    have hz₀a : a < z₀ := hz₀mem.1
    have hz₀b : z₀ < b := hz₀mem.2
    have hε : 0 < ε := lt_min (lt_min (by linarith) (by linarith)) hr
    have hεr : ε ≤ r := min_le_right _ _
    have hεa : a < z₀ - ε := by
      have : ε ≤ (z₀ - a) / 2 := le_trans (min_le_left _ _) (min_le_left _ _); linarith
    have hεb : z₀ + ε < b := by
      have : ε ≤ (b - z₀) / 2 := le_trans (min_le_left _ _) (min_le_right _ _); linarith
    rw [hmemU] at hu₀
    obtain ⟨hu₀S, hu₀n, -, -⟩ := hu₀
    have hmonou₀ := hmono u₀ hu₀S hu₀n
    have hmem_me : z₀ - ε ∈ Set.Icc a b := ⟨hεa.le, by linarith⟩
    have hmem_pe : z₀ + ε ∈ Set.Icc a b := ⟨by linarith, hεb.le⟩
    have hmem_z₀ : z₀ ∈ Set.Icc a b := ⟨hz₀a.le, hz₀b.le⟩
    have hQme : (specializeAt P u₀).eval (z₀ - ε) < 0 := by
      have := hmonou₀ hmem_me hmem_z₀ (by linarith); simpa [hz₀0] using this
    have hQpe : 0 < (specializeAt P u₀).eval (z₀ + ε) := by
      have := hmonou₀ hmem_z₀ hmem_pe (by linarith); simpa [hz₀0] using this
    have hca := continuousOn_sliceFun hS hP (z₀ - ε)
    have hcb := continuousOn_sliceFun hS hP (z₀ + ε)
    rw [continuousOn_fin_one_iff] at hca hcb
    obtain ⟨δ1, hδ1, h1⟩ := hca u₀ hu₀S (-(specializeAt P u₀).eval (z₀ - ε)) (by linarith)
    obtain ⟨δ2, hδ2, h2⟩ := hcb u₀ hu₀S ((specializeAt P u₀).eval (z₀ + ε)) (by linarith)
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun u huU hun => ?_⟩
    simp only [scalarFun, constPt]
    have hunS : u ∈ S := hUS huU
    have hb1 : euclideanNorm (u - u₀) < δ1 := lt_of_lt_of_le hun (min_le_left _ _)
    have hb2 : euclideanNorm (u - u₀) < δ2 := lt_of_lt_of_le hun (min_le_right _ _)
    have hQua : (specializeAt P u).eval (z₀ - ε) < 0 := by
      have := h1 u hunS hb1; simp only [sliceFun, constPt] at this
      rw [abs_lt] at this; linarith [this.2]
    have hQub : 0 < (specializeAt P u).eval (z₀ + ε) := by
      have := h2 u hunS hb2; simp only [sliceFun, constPt] at this
      rw [abs_lt] at this; linarith [this.1]
    obtain ⟨hfumem, hfu0⟩ := hf_spec u huU
    have hmonou := hmono u (hUS huU) (by rw [hmemU] at huU; exact huU.2.1)
    have hfu_Icc : f u ∈ Set.Icc a b := ⟨hfumem.1.le, hfumem.2.le⟩
    have hgt : z₀ - ε < f u := (hmonou.lt_iff_lt hmem_me hfu_Icc).mp (by rw [hfu0]; exact hQua)
    have hlt : f u < z₀ + ε := (hmonou.lt_iff_lt hfu_Icc hmem_pe).mp (by rw [hfu0]; exact hQub)
    rw [abs_lt]
    constructor <;> [linarith [hgt, hεr, hz₀def]; linarith [hlt, hεr, hz₀def]]
  exact ⟨U, hUsa, hUopen, hxU, f, ⟨hSAf, hContf⟩, hf_x, hsimple, a, b, ha, hb,
    fun x' hx' => ⟨(hf_spec x' hx').1, hf_eq x' hx'⟩⟩

/-! ### Reduction of the general case to the positive-derivative case (via `-P`) -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem specializeAt_neg (P : Polynomial ((Fin k → R) → R)) (u : Fin k → R) :
    specializeAt (-P) u = -(specializeAt P u) := by
  rw [specializeAt, specializeAt, Polynomial.map_neg]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem scalarFun_neg (c : (Fin k → R) → R) : scalarFun (-c) = -(scalarFun c) := by
  funext u j; simp [scalarFun, constPt]

/-- If every coefficient of `P` is semialgebraic continuous on `S`, then so is every coefficient of
`-P`. -/
theorem HasSemialgContinuousCoeffs.neg {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {P : Polynomial ((Fin k → R) → R)} (hP : HasSemialgContinuousCoeffs S P) :
    HasSemialgContinuousCoeffs S (-P) := by
  intro i
  have hmem : scalarFun (P.coeff i) ∈ continuousSemialgebraicFunctions hS := hP i
  show scalarFun ((-P).coeff i) ∈ continuousSemialgebraicFunctions hS
  rw [Polynomial.coeff_neg, scalarFun_neg]
  exact neg_mem hmem

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem isSimpleRoot_neg (Q : Polynomial R) (c : R) :
    IsSimpleRoot (-Q) c ↔ IsSimpleRoot Q c := by
  unfold IsSimpleRoot
  rw [Polynomial.eval_neg, neg_eq_zero, Polynomial.derivative_neg, Polynomial.eval_neg, neg_ne_zero]

/-- **BPR Proposition 3.10 (semialgebraic implicit function theorem).** Let `P` be a univariate
polynomial in `Y` with semialgebraic continuous coefficients on a semialgebraic set `S ⊆ R^k`. If `y`
is a simple root of the specialization `P(x, Y)`, then there is a semialgebraic continuous function
`f` on a relatively open neighborhood `U` of `x` in `S` with `f(x) = y` such that `f(x')` is a simple
root of `P(x', Y)` for every `x' ∈ U`. -/
theorem proposition_3_10 {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S)
    {P : Polynomial ((Fin k → R) → R)} (hP : HasSemialgContinuousCoeffs S P) {x : Fin k → R}
    (hx : x ∈ S) {y : R} (hy : IsSimpleRoot (specializeAt P x) y) :
    ∃ U : Set (Fin k → R), IsSemialgebraicSet U ∧ IsOpenIn S U ∧ x ∈ U ∧
      ∃ f : (Fin k → R) → R, IsSemialgContinuousOn U f ∧ f x = y ∧
        (∀ x' ∈ U, IsSimpleRoot (specializeAt P x') (f x')) ∧
        ∃ a b, a < y ∧ y < b ∧ ∀ x' ∈ U, f x' ∈ Set.Ioo a b ∧
          ∀ c ∈ Set.Ioo a b, (specializeAt P x').eval c = 0 → c = f x' := by
  obtain ⟨hy0, hyd⟩ := hy
  rcases lt_or_gt_of_ne hyd with hneg | hpos
  · -- `∂P/∂Y(x, y) < 0`: apply the positive case to `-P`
    have hP' : HasSemialgContinuousCoeffs S (-P) := hP.neg hS
    have hy0' : (specializeAt (-P) x).eval y = 0 := by
      rw [specializeAt_neg, Polynomial.eval_neg, hy0, neg_zero]
    have hpos' : 0 < (specializeAt (-P) x).derivative.eval y := by
      rw [specializeAt_neg, Polynomial.derivative_neg, Polynomial.eval_neg]; linarith
    obtain ⟨U, hUsa, hUopen, hxU, f, hf, hfx, hsimple, a, b, ha, hb, hbranch⟩ :=
      proposition_3_10_pos hS hP' hx hy0' hpos'
    refine ⟨U, hUsa, hUopen, hxU, f, hf, hfx, fun x' hx' => ?_, a, b, ha, hb, fun x' hx' => ?_⟩
    · rw [← isSimpleRoot_neg, ← specializeAt_neg]; exact hsimple x' hx'
    · refine ⟨(hbranch x' hx').1, fun c hc hc0 => (hbranch x' hx').2 c hc ?_⟩
      rw [specializeAt_neg, Polynomial.eval_neg, hc0, neg_zero]
  · -- `∂P/∂Y(x, y) > 0`: direct
    exact proposition_3_10_pos hS hP hx hy0 hpos

end Azurite.BPR
