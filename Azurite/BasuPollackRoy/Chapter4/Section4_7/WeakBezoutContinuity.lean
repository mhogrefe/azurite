import Azurite.BasuPollackRoy.Chapter4.Section4_7.WeakBezoutCount
import Azurite.BasuPollackRoy.Chapter3.Section3_3.Theorem_3_19

/-!
# BPR §4.7, Proposition 4.106: the analytic inputs and final assembly

`WeakBezoutCount.lean` reduces the weak Bézout bound to three analytic facts about the parameter sets
`Pm P d γ m` along the deformation path `γ`:

* `hopen`  — `Pm m` is open in the interval `(0,1]`;
* `hclosed` — `Pm m` is closed in `(0,1]`;
* `hinject` — every finite set of non-singular projective zeros of `P` injects, via finitely many
  local IFT continuations near `(1:0)`, into the common zeros of `S₍γ(w)₎` for a common parameter `w`.

This file supplies these inputs (using the local implicit function theorem `homotopy_local_ift'`,
the curve selection lemma `theorem_3_19`, and projective completeness `projective_curve_limit`) and
assembles `proposition_4_106_of_sa` from the already-proven logical chain in `WeakBezoutCount.lean`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-! ### The `(1:0)` endpoint -/

set_option linter.unusedSectionVars false in
/-- The representative of `(1 : 0)` is a nonzero scalar multiple `c • ![1,0]`. -/
theorem pencilPt10_rep :
    ∃ c : Ri R, c ≠ 0 ∧ (pencilPt10 (R := R)).rep = c • (![1, 0] : Fin 2 → Ri R) := by
  apply (mkLine_eq_mkLine_iff (pencilPt10 (R := R)).rep _ (pencilPt10 (R := R)).rep_nonzero
    (vec1t_ne_zero 0)).mp
  rw [show mkLine (pencilPt10 (R := R)).rep (pencilPt10 (R := R)).rep_nonzero = pencilPt10 from
    Projectivization.mk_rep _]
  rfl

set_option linter.unusedSectionVars false in
/-- The parameter coordinates of `(1 : 0)`: `λ = c ≠ 0`, `µ = 0`. -/
theorem pencilPt10_rep_param :
    ∃ c : Ri R, c ≠ 0 ∧ (pencilPt10 (R := R)).rep 0 = c ∧ (pencilPt10 (R := R)).rep 1 = 0 := by
  obtain ⟨c, hc, hrep⟩ := pencilPt10_rep (R := R)
  exact ⟨c, hc, by rw [hrep]; simp, by rw [hrep]; simp⟩

set_option linter.unusedSectionVars false in
/-- At the parameter `(λ, µ) = (c, 0)` the homotopy pencil is `c · Pᵢ`. -/
theorem homotopyPoly_zero_right (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (c : Ri R) (i : Fin k) :
    homotopyPoly P d c 0 i = C c * P i := by
  rw [homotopyPoly, map_zero, zero_mul, add_zero]

set_option linter.unusedSectionVars false in
/-- A non-singular projective zero of `P` is a non-singular projective zero of the pencil at the
endpoint `(1:0)`. -/
theorem isNonsingular_pencilPt10_of_isNonsingular (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (x : complexProjectiveSpace R k) (hx : IsNonsingularProjectiveZero P x) :
    IsNonsingularProjectiveZero
      (homotopyPoly P d ((pencilPt10 (R := R)).rep 0) ((pencilPt10 (R := R)).rep 1)) x := by
  obtain ⟨c, hc, hlam, hmu⟩ := pencilPt10_rep_param (R := R)
  have hscale : (homotopyPoly P d ((pencilPt10 (R := R)).rep 0) ((pencilPt10 (R := R)).rep 1))
      = fun i => C c * P i := by
    funext i; rw [hlam, hmu, homotopyPoly_zero_right]
  rw [hscale]
  exact isNonsingularProjectiveZero_C_smul hc hx

set_option linter.unusedSectionVars false in
/-- A common projective zero of `P` is a common projective zero of the pencil at the endpoint
`(1:0)`. -/
theorem zero_pencilPt10_of_zero (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (x : complexProjectiveSpace R k) (hx : ∀ i, aeval x.rep (P i) = 0) (i : Fin k) :
    aeval x.rep (homotopyPoly P d ((pencilPt10 (R := R)).rep 0) ((pencilPt10 (R := R)).rep 1) i)
      = 0 := by
  obtain ⟨c, _, hlam, hmu⟩ := pencilPt10_rep_param (R := R)
  rw [hlam, hmu, homotopyPoly_zero_right, map_mul, hx i, mul_zero]

/-! ### Hausdorffness -/

open Azurite.BPR

set_option linter.unusedSectionVars false in
/-- The euclidean space `R^n` is Hausdorff: distinct points are separated by disjoint open balls. -/
instance : T2Space (Fin k → R) := by
  refine ⟨fun x y hxy => ?_⟩
  -- some coordinate differs; the euclidean norm of the difference is positive
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra hcon; push Not at hcon; exact hxy (funext hcon)
  have hpos : 0 < euclideanNorm (x - y) := by
    have hsqpos : 0 < euclideanNormSq (x - y) := by
      have hterm : 0 < (x - y) j ^ 2 := by
        have : (x - y) j ≠ 0 := by rw [Pi.sub_apply]; exact sub_ne_zero.mpr hj
        positivity
      have hle : (x - y) j ^ 2 ≤ euclideanNormSq (x - y) :=
        Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ j)
      linarith
    by_contra hle; push Not at hle
    have := le_antisymm hle (euclideanNorm_nonneg (x - y))
    rw [← euclideanNorm_sq (x - y), this] at hsqpos; simp at hsqpos
  set r := euclideanNorm (x - y) / 2 with hr
  have hrpos : 0 < r := by positivity
  refine ⟨openBall x r, openBall y r, isOpen_openBall x hrpos, isOpen_openBall y hrpos,
    mem_openBall_self x hrpos, mem_openBall_self y hrpos, ?_⟩
  rw [Set.disjoint_iff_inter_eq_empty]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hzx hzy
  rw [mem_openBall_iff_norm hrpos] at hzx hzy
  have htri : euclideanNorm (x - y) ≤ euclideanNorm (z - x) + euclideanNorm (z - y) := by
    have h := euclideanNorm_add_le (x - z) (z - y)
    have heq : (x - z) + (z - y) = x - y := by ring
    rw [heq] at h
    have hsymm : euclideanNorm (x - z) = euclideanNorm (z - x) := by
      have : euclideanNormSq (x - z) = euclideanNormSq (z - x) := by
        rw [euclideanNormSq, euclideanNormSq]; congr 1; funext i
        simp only [Pi.sub_apply]; ring
      rw [euclideanNorm, euclideanNorm, this]
    rw [hsymm] at h; exact h
  rw [hr] at hzx hzy; linarith

set_option linter.unusedSectionVars false in
/-- The moment-map codomain is Hausdorff (induced from `R^N` along an injective reindexing). -/
instance : T2Space (MomentIndex k → R) := by
  apply T2Space.of_injective_continuous
    (f := fun f : MomentIndex k → R => f ∘ (momentReindex k).symm)
  · intro f g hfg
    funext idx
    have := congrFun hfg ((momentReindex k) idx)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using this
  · exact continuous_momentReindex_codomain

set_option linter.unusedSectionVars false in
/-- Complex projective space is Hausdorff: the moment-map embedding is a continuous injection into a
Hausdorff space. -/
instance : T2Space (complexProjectiveSpace R k) :=
  T2Space.of_injective_continuous momentMap_injective continuous_momentMap

/-! ### A chart index for an arbitrary projective point -/

set_option linter.unusedSectionVars false in
/-- Every projective point lies in some affine chart. -/
theorem exists_mem_chartSet {n : ℕ} (p : complexProjectiveSpace R n) :
    ∃ i : Fin (n + 1), p ∈ chartSet i := by
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), p.rep i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact p.rep_nonzero (funext fun i => hcon i)
  exact ⟨i, by rw [chartSet_eq]; exact hi⟩

/-! ### A strengthened Theorem 4.104: the target neighborhood lies in the chart `j₀` -/

set_option linter.unusedSectionVars false in
/-- **Theorem 4.104, strengthened.** Same conclusion as `theorem_4_104`, plus the structural fact that
the produced target neighborhood `V` lies entirely in the chart `𝒰_{j₀}` (`V ⊆ chartSet j₀`). This
extra fact is what makes the lifted map `ϕ` continuous on `U` (the chart coordinate `chartInv j₀ ∘ ϕ`
is then globally defined and continuous on `U`). The proof is the same chart-lifting argument as
`theorem_4_104`, exposing the membership criterion `hmemV`. -/
theorem theorem_4_104_chartV {k ℓ : ℕ} (m : ℕ)
    (x₀ : complexProjectiveSpace R k) (y₀ : complexProjectiveSpace R ℓ)
    (i₀ : Fin (k + 1)) (j₀ : Fin (ℓ + 1))
    (hx₀ : x₀ ∈ chartSet i₀) (hy₀ : y₀ ∈ chartSet j₀)
    (W' : Set (Fin ((k + k) + (ℓ + ℓ)) → R)) (hW'open : IsOpen W') (hW'sa : IsSemialgebraicSet W')
    (F : Fin (ℓ + ℓ) → (Fin ((k + k) + (ℓ + ℓ)) → R) → R)
    (g : Fin (ℓ + ℓ) → Fin ((k + k) + (ℓ + ℓ)) → (Fin ((k + k) + (ℓ + ℓ)) → R) → R)
    (hz₀W : Fin.append (realEquiv (chartInv i₀ x₀)) (realEquiv (chartInv j₀ y₀)) ∈ W')
    (hF : ∀ l, IsSemialgContinuousOn W' (F l))
    (hdiff : ∀ l j, ∀ z ∈ W', HasPartialDerivAtIn (F l) W' j z (g l j z))
    (hgsc : ∀ l j, IsSemialgContinuousOn W' (g l j))
    (hF0 : ∀ l, F l (Fin.append (realEquiv (chartInv i₀ x₀)) (realEquiv (chartInv j₀ y₀))) = 0)
    (hdet : IsUnit (Matrix.of fun l j : Fin (ℓ + ℓ) =>
      g l (Fin.natAdd (k + k) j)
        (Fin.append (realEquiv (chartInv i₀ x₀)) (realEquiv (chartInv j₀ y₀)))).det)
    (hgS : ∀ l j, IsSFunction m W' (g l j)) :
    ∃ (U : Set (complexProjectiveSpace R k)) (V : Set (complexProjectiveSpace R ℓ))
      (ϕ : complexProjectiveSpace R k → complexProjectiveSpace R ℓ),
      IsSemialgebraicSetP U ∧ IsOpen U ∧ x₀ ∈ U ∧
      IsSemialgebraicSetP V ∧ IsOpen V ∧ y₀ ∈ V ∧
      IsSClassMapP m U V ϕ ∧ ϕ x₀ = y₀ ∧
      (∀ x ∈ U, ∀ y ∈ V,
        ((∀ l, F l (Fin.append (realEquiv (chartInv i₀ x)) (realEquiv (chartInv j₀ y))) = 0)
          ↔ y = ϕ x)) ∧
      (∀ q ∈ V, q ∈ chartSet j₀) := by
  classical
  -- abbreviate the realified base point coordinates
  set x₀a : Fin (k + k) → R := realEquiv (chartInv i₀ x₀) with hx₀a
  set y₀a : Fin (ℓ + ℓ) → R := realEquiv (chartInv j₀ y₀) with hy₀a
  -- apply the affine implicit function theorem in the chart `(i₀, j₀)`
  obtain ⟨Ua, Va, ϕa, hUasa, hUaopen, hx₀Ua, hVasa, hVaopen, hy₀Va, hϕasa, hϕacont,
      hϕamaps, hϕax₀, hprodUV, himpl, hϕaS⟩ :=
    Azurite.BPR.theorem_3_25 (k := k + k) (ℓ := ℓ + ℓ) (W' := W') (x₀ := x₀a) (y₀ := y₀a)
      (f := F) (g := g) hW'open hW'sa hz₀W hF hdiff hgsc hF0 hdet m hgS
  -- transport to projective space
  set U₀ : Set (Fin k → Ri R) := realEquiv.symm '' Ua with hU₀
  set V₀ : Set (Fin ℓ → Ri R) := realEquiv.symm '' Va with hV₀
  set ϕ₀ : (Fin k → Ri R) → (Fin ℓ → Ri R) :=
    fun z => realEquiv.symm (ϕa (realEquiv z)) with hϕ₀
  set U : Set (complexProjectiveSpace R k) := chartImageP i₀ U₀ with hUdef
  set V : Set (complexProjectiveSpace R ℓ) := chartImageP j₀ V₀ with hVdef
  set ϕ : complexProjectiveSpace R k → complexProjectiveSpace R ℓ := liftProjMap i₀ j₀ ϕ₀ with hϕdef
  -- realification identities
  have hreUa : realEquiv '' U₀ = Ua := by rw [hU₀, Equiv.image_symm_image]
  have hreVa : realEquiv '' V₀ = Va := by rw [hV₀, Equiv.image_symm_image]
  -- `U₀, V₀` semialgebraic over `C` and open
  have hU₀sa : IsSemialgebraicSetC U₀ := by rw [IsSemialgebraicSetC, hreUa]; exact hUasa
  have hV₀sa : IsSemialgebraicSetC V₀ := by rw [IsSemialgebraicSetC, hreVa]; exact hVasa
  have hU₀open : IsOpen (realEquiv '' U₀) := by rw [hreUa]; exact hUaopen
  have hV₀open : IsOpen (realEquiv '' V₀) := by rw [hreVa]; exact hVaopen
  -- chart-coordinate membership criteria for `U`, `V`
  have hmemU : ∀ p : complexProjectiveSpace R k,
      p ∈ U ↔ p ∈ chartSet i₀ ∧ realEquiv (chartInv i₀ p) ∈ Ua := by
    intro p
    rw [hUdef, chartImageP, Set.mem_ofPred_eq, hU₀]
    refine and_congr_right (fun _ => ?_)
    constructor
    · rintro ⟨w, hwU, hwp⟩; rw [← hwp, Equiv.apply_symm_apply]; exact hwU
    · intro h; exact ⟨realEquiv (chartInv i₀ p), h, by rw [Equiv.symm_apply_apply]⟩
  have hmemV : ∀ q : complexProjectiveSpace R ℓ,
      q ∈ V ↔ q ∈ chartSet j₀ ∧ realEquiv (chartInv j₀ q) ∈ Va := by
    intro q
    rw [hVdef, chartImageP, Set.mem_ofPred_eq, hV₀]
    refine and_congr_right (fun _ => ?_)
    constructor
    · rintro ⟨w, hwV, hwq⟩; rw [← hwq, Equiv.apply_symm_apply]; exact hwV
    · intro h; exact ⟨realEquiv (chartInv j₀ q), h, by rw [Equiv.symm_apply_apply]⟩
  -- `ϕ₀` semialgebraic over `C` on `U₀`
  have hϕ₀sa : IsSemialgebraicFunctionC U₀ ϕ₀ := by
    rw [hϕ₀, hU₀]; exact isSemialgebraicFunctionC_realEquiv_symm hϕasa
  -- `ϕ₀`'s coordinates are `𝒮^m` on `U₀`
  have hϕ₀coords : ∀ b : Fin ℓ, IsSFunctionCC m U₀ (fun z => ϕ₀ z b) := by
    apply isSFunctionCC_of_realComponents
    intro c
    have heq : (fun w => realEquiv (ϕ₀ (realEquiv.symm w)) c)
        = (fun w => ϕa w c) := by
      funext w
      show realEquiv (realEquiv.symm (ϕa (realEquiv (realEquiv.symm w)))) c = ϕa w c
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [heq, hreUa]
    exact (hϕaS c).mono (Nat.le_succ m)
  -- `ϕ` maps `U` into `V`
  have hϕmaps : Set.MapsTo ϕ U V := by
    intro p hp
    rw [hmemU] at hp
    obtain ⟨hpi₀, hpUa⟩ := hp
    have hcoordU : chartInv i₀ p ∈ U₀ := by
      rw [hU₀]; exact ⟨realEquiv (chartInv i₀ p), hpUa, by rw [Equiv.symm_apply_apply]⟩
    have hϕaVa : ϕa (realEquiv (chartInv i₀ p)) ∈ Va :=
      hϕamaps hpUa
    rw [hmemV]
    have hϕp : ϕ p = chartMap j₀ (ϕ₀ (chartInv i₀ p)) := by rw [hϕdef, liftProjMap]
    refine ⟨by rw [hϕp]; exact Set.mem_range_self _, ?_⟩
    have hcij : chartInv j₀ (ϕ p) = ϕ₀ (chartInv i₀ p) := by
      rw [hϕp, chartInv_chartMap]
    rw [hcij, hϕ₀, Equiv.apply_symm_apply]; exact hϕaVa
  -- the per-chart domain is semialgebraic over `C`
  have hDom : ∀ (i : Fin (k + 1)) (j : Fin (ℓ + 1)), IsSemialgebraicSetC
      (chartMap i ⁻¹' (chartImageP i₀ U₀ ∩ chartSet i)
        ∩ (fun z => liftProjMap i₀ j₀ ϕ₀ (chartMap i z)) ⁻¹' chartSet j) := by
    intro i j
    set A : Set (Fin k → Ri R) := {z : Fin k → Ri R |
        z ∈ (chartOverlap i i₀ : Set (Fin k → Ri R)) ∧ transitionMap i i₀ z ∈ U₀} with hA
    have hfac1 : IsSemialgebraicSetC A := by
      have := (isSemialgebraicFunctionC_transitionMap i i₀).preimage hU₀sa
      rw [hA]; convert this using 2
    have hsubA : A ⊆ (chartOverlap i i₀ : Set (Fin k → Ri R)) := fun z hz => hz.1
    have htransA : IsSemialgebraicFunctionC A (transitionMap i i₀) :=
      (isSemialgebraicFunctionC_transitionMap i i₀).mono hfac1 hsubA
    have hmaps1 : Set.MapsTo (transitionMap i i₀) A U₀ := fun z hz => hz.2
    have hψ : IsSemialgebraicFunctionC A (fun z => ϕ₀ (transitionMap i i₀ z)) :=
      IsSemialgebraicFunctionC.comp htransA hϕ₀sa hmaps1
    have hfac2 : IsSemialgebraicSetC {z : Fin k → Ri R |
        z ∈ A ∧ ϕ₀ (transitionMap i i₀ z) ∈ (chartOverlap j₀ j : Set (Fin ℓ → Ri R))} :=
      hψ.preimage (isSemialgebraicSetC_chartOverlap j₀ j)
    have hseteq : (chartMap i ⁻¹' (chartImageP i₀ U₀ ∩ chartSet i)
        ∩ (fun z => liftProjMap i₀ j₀ ϕ₀ (chartMap i z)) ⁻¹' chartSet j)
        = {z : Fin k → Ri R |
            z ∈ A ∧ ϕ₀ (transitionMap i i₀ z) ∈ (chartOverlap j₀ j : Set (Fin ℓ → Ri R))} := by
      rw [chartMap_preimage_chartImageP]
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, hA]
      have hrep : liftProjMap i₀ j₀ ϕ₀ (chartMap i z)
          = chartMap j₀ (ϕ₀ (transitionMap i i₀ z)) := by
        rw [liftProjMap, ← transitionMap_eq_chartInv_chartMap]
      constructor
      · rintro ⟨⟨hov, hU⟩, hj⟩
        rw [hrep, chartMap_mem_chartSet_iff] at hj
        exact ⟨⟨hov, hU⟩, hj⟩
      · rintro ⟨⟨hov, hU⟩, hj⟩
        rw [hrep, chartMap_mem_chartSet_iff]
        exact ⟨⟨hov, hU⟩, hj⟩
    rw [hseteq]; exact hfac2
  have hϕclass : IsSClassMapP m U V ϕ := by
    rw [hUdef, hVdef, hϕdef]
    exact isSClassMapP_liftProjMap i₀ j₀ hU₀open hU₀sa hϕ₀coords
      (by rw [← hUdef, ← hVdef, ← hϕdef]; exact hϕmaps) hDom
  refine ⟨U, V, ϕ, ?_, ?_, ?_, ?_, ?_, ?_, hϕclass, ?_, ?_, ?_⟩
  · rw [hUdef]; exact isSemialgebraicSetP_chartImageP i₀ hU₀sa
  · rw [hUdef]; exact isOpen_chartImageP i₀ (isOpenC_iff_isOpen_realEquiv.mpr hU₀open)
  · rw [hmemU]; exact ⟨hx₀, hx₀Ua⟩
  · rw [hVdef]; exact isSemialgebraicSetP_chartImageP j₀ hV₀sa
  · rw [hVdef]; exact isOpen_chartImageP j₀ (isOpenC_iff_isOpen_realEquiv.mpr hV₀open)
  · rw [hmemV]; exact ⟨hy₀, hy₀Va⟩
  · have hϕx₀ : ϕ x₀ = chartMap j₀ (ϕ₀ (chartInv i₀ x₀)) := by rw [hϕdef, liftProjMap]
    rw [hϕx₀]
    have hcij : ϕ₀ (chartInv i₀ x₀) = realEquiv.symm (ϕa x₀a) := by
      rw [hϕ₀, hx₀a]
    rw [hcij, hϕax₀]
    rw [hy₀a, Equiv.symm_apply_apply]
    have hy₀rep : y₀.rep j₀ ≠ 0 := by rw [chartSet_eq] at hy₀; exact hy₀
    exact chartMap_chartInv j₀ y₀ hy₀rep
  · intro x hx y hy
    rw [hmemU] at hx
    rw [hmemV] at hy
    obtain ⟨hxi₀, hxUa⟩ := hx
    obtain ⟨hyj₀, hyVa⟩ := hy
    set xa : Fin (k + k) → R := realEquiv (chartInv i₀ x) with hxa
    set ya : Fin (ℓ + ℓ) → R := realEquiv (chartInv j₀ y) with hya
    have haff := himpl xa hxUa ya hyVa
    rw [haff]
    constructor
    · intro hya_eq
      have hcoord : chartInv j₀ y = ϕ₀ (chartInv i₀ x) := by
        have h1 : chartInv j₀ y = realEquiv.symm ya := by rw [hya, Equiv.symm_apply_apply]
        rw [h1, hya_eq, hϕ₀, hxa]
      have hyjrep : y.rep j₀ ≠ 0 := by rw [chartSet_eq] at hyj₀; exact hyj₀
      have hyrep : y = chartMap j₀ (chartInv j₀ y) :=
        (chartMap_chartInv j₀ y hyjrep).symm
      have hϕx : ϕ x = chartMap j₀ (ϕ₀ (chartInv i₀ x)) := by rw [hϕdef, liftProjMap]
      rw [hyrep, hcoord, ← hϕx]
    · intro hy_eq
      have hϕx : ϕ x = chartMap j₀ (ϕ₀ (chartInv i₀ x)) := by rw [hϕdef, liftProjMap]
      have hcij : chartInv j₀ y = ϕ₀ (chartInv i₀ x) := by
        rw [hy_eq, hϕx, chartInv_chartMap]
      have : ya = realEquiv (ϕ₀ (chartInv i₀ x)) := by rw [hya, hcij]
      rw [this, hϕ₀, hxa, Equiv.apply_symm_apply]
  · -- the extra fact: `V ⊆ chartSet j₀`
    intro q hq; exact ((hmemV q).mp hq).1

/-! ### Continuity of the chart inverse (via the moment map) -/

open Azurite.BPR

set_option linter.unusedSectionVars false in
/-- **Coordinate-wise `ContinuousWithinAt` into `Rˡ`.** A map `f : X → Rˡ` from any topological space
is `ContinuousWithinAt S x` if each scalar coordinate (packaged as a `Fin 1 → R` map) is. -/
theorem continuousWithinAt_pi_euclidean {X : Type*} [TopologicalSpace X] {ℓ : ℕ}
    {f : X → (Fin ℓ → R)} {S : Set X} {x : X}
    (h : ∀ j, ContinuousWithinAt (fun y => (fun _ : Fin 1 => f y j)) S x) :
    ContinuousWithinAt f S x := by
  unfold ContinuousWithinAt
  rw [(nhds_hasBasis_openBall (f x)).tendsto_right_iff]
  intro r hr
  have hcoord : ∀ j, ∀ᶠ y in nhdsWithin x S,
      |f y j - f x j| < r / ((ℓ : R) + 1) := by
    intro j
    have hrr : 0 < r / ((ℓ : R) + 1) := by positivity
    have hj := h j
    unfold ContinuousWithinAt at hj
    rw [(nhds_hasBasis_openBall ((fun _ : Fin 1 => f x j))).tendsto_right_iff] at hj
    filter_upwards [hj (r / ((ℓ : R) + 1)) hrr] with y hy
    rw [mem_openBall_iff_norm hrr, euclideanNorm_fin_one] at hy
    simpa using hy
  filter_upwards [Filter.eventually_all.mpr hcoord] with y hy
  rw [mem_openBall_iff_norm hr]
  have hball : euclideanNormSq (f y - f x) < r ^ 2 := by
    have hbd : euclideanNormSq (f y - f x) ≤ ∑ _j : Fin ℓ, (r / ((ℓ : R) + 1)) ^ 2 := by
      rw [euclideanNormSq]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have hyj := hy j
      rw [Pi.sub_apply]
      nlinarith [abs_nonneg (f y j - f x j), sq_abs (f y j - f x j), hyj]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbd
    have hlt : (ℓ : R) * (r / ((ℓ : R) + 1)) ^ 2 < r ^ 2 := by
      have h1 : (0 : R) ≤ (ℓ : R) := Nat.cast_nonneg ℓ
      rw [div_pow, mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      have hrpos : (0 : R) < r ^ 2 := by positivity
      have hexp : r ^ 2 * ((ℓ : R) + 1) ^ 2 = r ^ 2 * ((ℓ : R) ^ 2 + 2 * ℓ + 1) := by ring
      rw [hexp]
      nlinarith [hrpos, h1, mul_nonneg (mul_nonneg h1 h1) hrpos.le]
    linarith
  nlinarith [euclideanNorm_sq (f y - f x), hball, euclideanNorm_nonneg (f y - f x), hr]

set_option linter.unusedSectionVars false in
/-- Coordinate-wise `ContinuousOn` into `Rˡ` from any topological space. -/
theorem continuousOn_pi_euclidean {X : Type*} [TopologicalSpace X] {ℓ : ℕ}
    {f : X → (Fin ℓ → R)} {S : Set X}
    (h : ∀ j, ContinuousOn (fun y => (fun _ : Fin 1 => f y j)) S) :
    ContinuousOn f S :=
  fun x hx => continuousWithinAt_pi_euclidean (fun j => h j x hx)

set_option linter.unusedSectionVars false in
/-- A quotient of two scalar (`Fin 1 → R`-packaged) `ContinuousWithinAt` maps with nonvanishing
denominator is `ContinuousWithinAt`. -/
theorem continuousWithinAt_fin1_div {X : Type*} [TopologicalSpace X]
    {num den : X → R} {S : Set X} {x : X}
    (hn : ContinuousWithinAt (fun y => (fun _ : Fin 1 => num y)) S x)
    (hd : ContinuousWithinAt (fun y => (fun _ : Fin 1 => den y)) S x)
    (hdx : den x ≠ 0) :
    ContinuousWithinAt (fun y => (fun _ : Fin 1 => num y / den y)) S x := by
  unfold ContinuousWithinAt at *
  rw [(nhds_hasBasis_openBall _).tendsto_right_iff] at hn hd ⊢
  intro ε hε
  set a := num x with ha
  set b := den x with hb
  have hbpos : (0 : R) < |b| := abs_pos.mpr hdx
  have hn' : ∀ s, 0 < s → ∀ᶠ y in nhdsWithin x S, |num y - a| < s := by
    intro s hs
    filter_upwards [hn s hs] with y hy
    rw [mem_openBall_iff_norm hs, euclideanNorm_fin_one] at hy
    simpa using hy
  have hd' : ∀ s, 0 < s → ∀ᶠ y in nhdsWithin x S, |den y - b| < s := by
    intro s hs
    filter_upwards [hd s hs] with y hy
    rw [mem_openBall_iff_norm hs, euclideanNorm_fin_one] at hy
    simpa using hy
  filter_upwards [hn' (ε * |b| / 4) (by positivity), hd' (|b| / 2) (by positivity),
    hd' (ε * |b| ^ 2 / (4 * (|a| + 1))) (by positivity)] with y hyn hyd hyd2
  rw [mem_openBall_iff_norm hε, euclideanNorm_fin_one, Pi.sub_apply]
  have hdy_lb : |b| / 2 < |den y| := by
    have h := abs_sub_abs_le_abs_sub (den x) (den y)
    rw [abs_sub_comm (den x) (den y), ← hb] at h
    linarith [h, hyd]
  have hdy_pos : (0 : R) < |den y| := by linarith
  have hdyne : den y ≠ 0 := fun hz => by rw [hz, abs_zero] at hdy_pos; exact lt_irrefl _ hdy_pos
  have hkey : num y / den y - a / b
      = (num y - a) / den y + a * (b - den y) / (den y * b) := by
    field_simp; ring
  show |num y / den y - a / b| < ε
  rw [hkey]
  have hbnd1 : |(num y - a) / den y| < ε / 2 := by
    rw [abs_div, div_lt_iff₀ hdy_pos]
    calc |num y - a| < ε * |b| / 4 := hyn
      _ ≤ ε / 2 * |den y| := by nlinarith [hdy_lb, hε.le, hbpos]
  have hbnd2 : |a * (b - den y) / (den y * b)| ≤ ε / 2 := by
    rw [abs_div, abs_mul, abs_mul]
    rw [div_le_iff₀ (by positivity)]
    have hba : |b - den y| = |den y - b| := abs_sub_comm b (den y)
    rw [hba]
    have hden_prod : |b| / 2 * |b| ≤ |den y| * |b| :=
      mul_le_mul_of_nonneg_right hdy_lb.le hbpos.le
    have hstep1 : |a| * |den y - b| ≤ |a| * (ε * |b| ^ 2 / (4 * (|a| + 1))) :=
      mul_le_mul_of_nonneg_left hyd2.le (abs_nonneg a)
    -- `|a| * (ε|b|²/(4(|a|+1))) ≤ ε|b|²/4`
    have hstep2 : |a| * (ε * |b| ^ 2 / (4 * (|a| + 1))) ≤ ε * |b| ^ 2 / 4 := by
      rw [mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hax : |a| ≤ |a| + 1 := by linarith [abs_nonneg a]
      nlinarith [abs_nonneg a, hbpos, hε.le, hax, sq_nonneg (|b|)]
    -- `ε|b|²/4 ≤ ε/2 * (|den y| * |b|)`
    have hstep3 : ε * |b| ^ 2 / 4 ≤ ε / 2 * (|den y| * |b|) := by
      rw [div_le_iff₀ (by positivity)]
      have h4 : ε / 2 * (|den y| * |b|) * 4 = ε * 2 * (|den y| * |b|) := by ring
      rw [h4]
      nlinarith [hden_prod, hε.le, hbpos, sq_nonneg (|b|)]
    linarith [hstep1, hstep2, hstep3]
  calc |(num y - a) / den y + a * (b - den y) / (den y * b)|
      ≤ |(num y - a) / den y| + |a * (b - den y) / (den y * b)| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

set_option linter.unusedSectionVars false in
/-- Evaluating the moment map at a fixed index (packaged as a `Fin 1 → R` map) is continuous. -/
theorem continuous_momentMap_apply (idx : MomentIndex k) :
    Continuous (fun x : complexProjectiveSpace R k => (fun _ : Fin 1 => momentMap x idx)) := by
  -- `momentMap` is continuous into `MomentIndex → R`; postcompose with `Fin 1`-packaged eval
  have hbasis : Continuous
      (fun g : MomentIndex k → R => (fun _ : Fin 1 => g idx)) := by
    -- via the inducing reindexing map and `continuous_iff_components`
    have hcomp : (fun g : MomentIndex k → R => (fun _ : Fin 1 => g idx))
        = (fun h : Fin (Fintype.card (MomentIndex k)) → R =>
            (fun _ : Fin 1 => h (momentReindex k idx)))
          ∘ (fun g : MomentIndex k → R => g ∘ (momentReindex k).symm) := by
      funext g; simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [hcomp]
    refine Continuous.comp ?_ continuous_momentReindex_codomain
    rw [continuous_iff_components]
    intro _; exact continuousR_coord (momentReindex k idx)
  exact hbasis.comp continuous_momentMap

set_option linter.unusedSectionVars false in
/-- The diagonal real projector entry at a nonzero coordinate is positive. -/
theorem projReV_diag_pos {v : Fin (k + 1) → Ri R} {i : Fin (k + 1)} (hi : v i ≠ 0) :
    0 < projReV v i i := by
  rw [projReV]
  have hnum : 0 < Ri.reL (v i) * Ri.reL (v i) + Ri.imL (v i) * Ri.imL (v i) := by
    have := normSqC_pos hi; nlinarith [this]
  have hden : 0 < hermNormSq v := hermNormSq_pos (fun h => hi (by rw [h]; rfl))
  positivity

set_option linter.unusedSectionVars false in
/-- The chart inverse `chartInv i`, viewed through the realification, is continuous on the chart `𝒰ᵢ`.
The chart coordinates are ratios of moment-map entries (`reL_chartInv_eq` / `imL_chartInv_eq`), which
are continuous in the point with positive (hence nonvanishing) denominator. -/
theorem continuousOn_realEquiv_chartInv (i : Fin (k + 1)) :
    ContinuousOn (fun x : complexProjectiveSpace R k => realEquiv (chartInv i x)) (chartSet i) := by
  refine continuousOn_pi_euclidean (fun c => ?_)
  refine Fin.addCases (motive := fun c => ContinuousOn
      (fun x : complexProjectiveSpace R k => (fun _ : Fin 1 => realEquiv (chartInv i x) c))
      (chartSet i)) (fun j => ?_) (fun j => ?_) c
  · -- real-part block: `realEquiv (chartInv i x) (castAdd j) = reL (chartInv i x j)`
    have hden : ∀ x ∈ chartSet i, (momentMap (R := R) (k := k) x) (Sum.inl (i, i)) ≠ 0 := by
      intro x hx; rw [chartSet_eq] at hx
      show (momentMap (R := R) (k := k) x) (Sum.inl (i, i)) ≠ 0
      simp only [momentMap, momentFn_inl]; exact ne_of_gt (projReV_diag_pos hx)
    have hquot : ContinuousOn
        (fun x : complexProjectiveSpace R k =>
          (fun _ : Fin 1 => (momentMap (R := R) (k := k) x) (Sum.inl (i.succAbove j, i)) / (momentMap (R := R) (k := k) x) (Sum.inl (i, i))))
        (chartSet i) := by
      intro x hx
      exact continuousWithinAt_fin1_div
        ((continuous_momentMap_apply _).continuousWithinAt)
        ((continuous_momentMap_apply _).continuousWithinAt) (hden x hx)
    refine hquot.congr (fun x hx => ?_)
    have hx' : x.rep i ≠ 0 := by rw [chartSet_eq] at hx; exact hx
    funext _
    show realEquiv (chartInv i x) (Fin.castAdd k j) = _
    rw [realEquiv_apply_castAdd, reL_chartInv_eq hx' j]
    simp only [momentMap, momentFn_inl]
  · -- imaginary-part block
    have hden : ∀ x ∈ chartSet i, (momentMap (R := R) (k := k) x) (Sum.inl (i, i)) ≠ 0 := by
      intro x hx; rw [chartSet_eq] at hx
      show (momentMap (R := R) (k := k) x) (Sum.inl (i, i)) ≠ 0
      simp only [momentMap, momentFn_inl]; exact ne_of_gt (projReV_diag_pos hx)
    have hquot : ContinuousOn
        (fun x : complexProjectiveSpace R k =>
          (fun _ : Fin 1 => (momentMap (R := R) (k := k) x) (Sum.inr (i.succAbove j, i)) / (momentMap (R := R) (k := k) x) (Sum.inl (i, i))))
        (chartSet i) := by
      intro x hx
      exact continuousWithinAt_fin1_div
        ((continuous_momentMap_apply _).continuousWithinAt)
        ((continuous_momentMap_apply _).continuousWithinAt) (hden x hx)
    refine hquot.congr (fun x hx => ?_)
    have hx' : x.rep i ≠ 0 := by rw [chartSet_eq] at hx; exact hx
    funext _
    show realEquiv (chartInv i x) (Fin.natAdd k j) = _
    rw [realEquiv_apply_natAdd, imL_chartInv_eq hx' j]
    simp only [momentMap, momentFn_inl, momentFn_inr]

set_option linter.unusedSectionVars false in
/-- The chart inverse `chartInv i` is continuous on the chart `𝒰ᵢ`. -/
theorem continuousOn_chartInv (i : Fin (k + 1)) :
    ContinuousOn (chartInv i : complexProjectiveSpace R k → Fin k → Ri R) (chartSet i) := by
  have hsymm : Continuous (realEquivₜ (R := R) (k := k)).symm :=
    (realEquivₜ (R := R) (k := k)).symm.continuous
  have heq : (chartInv i : complexProjectiveSpace R k → Fin k → Ri R)
      = (fun w => (realEquivₜ (R := R) (k := k)).symm w)
        ∘ (fun x => realEquiv (chartInv i x)) := by
    funext x
    show chartInv i x = realEquivₜ.symm (realEquiv (chartInv i x))
    rw [show (realEquivₜ.symm (realEquiv (chartInv i x)) : Fin k → Ri R)
        = realEquiv.symm (realEquiv (chartInv i x)) from rfl, Equiv.symm_apply_apply]
  rw [heq]
  exact hsymm.comp_continuousOn (continuousOn_realEquiv_chartInv i)

/-! ### Continuity of a lifted `𝒮`-map -/

set_option linter.unusedSectionVars false in
/-- An `IsSFunctionC` map is `ContinuousOn` (packaged into the line `Fin 1 → R`). -/
theorem isSFunctionC_continuousOn {n m : ℕ} {W : Set (Fin n → Ri R)} {c : (Fin n → Ri R) → R}
    (h : IsSFunctionC m W c) :
    ContinuousOn (fun z : Fin n → Ri R => (fun _ : Fin 1 => c z)) W := by
  -- `IsSFunctionC` unfolds to `IsSFunction` of the realified map on `realEquiv '' W`
  have hsc : Azurite.BPR.IsSemialgContinuousOn (realEquiv '' W)
      (fun w => c (realEquiv.symm w)) := (Azurite.BPR.IsSFunction.isSemialgContinuousOn h)
  have hcont : ContinuousOn (fun w : Fin (n + n) → R => (fun _ : Fin 1 => c (realEquiv.symm w)))
      (realEquiv '' W) := hsc.2
  -- transport through the homeomorphism `realEquivₜ`
  have hres : (fun z : Fin n → Ri R => (fun _ : Fin 1 => c z))
      = (fun w : Fin (n + n) → R => (fun _ : Fin 1 => c (realEquiv.symm w)))
        ∘ (realEquivₜ (R := R) (k := n)) := by
    funext z; simp only [Function.comp_apply, realEquivₜ_apply, Equiv.symm_apply_apply]
  rw [hres]
  apply hcont.comp (realEquivₜ (R := R) (k := n)).continuous.continuousOn
  intro z hz; exact ⟨z, hz, rfl⟩

set_option linter.unusedSectionVars false in
/-- **Continuity of a lifted `𝒮`-map landing in a single chart.** If `IsSClassMapP m U V ϕ`, `U` is
open, and `V ⊆ chartSet j₀`, then `ϕ` is continuous on `U`. -/
theorem continuousOn_isSClassMapP {ℓ : ℕ} {m : ℕ} {U : Set (complexProjectiveSpace R k)}
    {V : Set (complexProjectiveSpace R ℓ)}
    {ϕ : complexProjectiveSpace R k → complexProjectiveSpace R ℓ} (j₀ : Fin (ℓ + 1))
    (hϕ : IsSClassMapP m U V ϕ) (hUopen : IsOpen U) (hV : ∀ q ∈ V, q ∈ chartSet j₀) :
    ContinuousOn ϕ U := by
  obtain ⟨hmaps, hcc⟩ := hϕ
  -- `ϕ q = chartMap j₀ (chartInv j₀ (ϕ q))` on `U` (since `ϕ q ∈ V ⊆ chartSet j₀`)
  have hϕeq : ∀ q ∈ U, ϕ q = chartMap j₀ (chartInv j₀ (ϕ q)) := by
    intro q hq
    have : ϕ q ∈ chartSet j₀ := hV (ϕ q) (hmaps hq)
    rw [chartSet_eq] at this
    exact (chartMap_chartInv j₀ (ϕ q) this).symm
  -- it suffices that `q ↦ chartInv j₀ (ϕ q)` is continuous on `U`
  have hcoord : ContinuousOn (fun q => chartInv j₀ (ϕ q)) U := by
    -- continuity at each `p ∈ U` within `U`
    intro p hp
    -- pick a chart `i` for `p`
    obtain ⟨i, hpi⟩ := exists_mem_chartSet p
    -- on `U ∩ chartSet i`, write `chartInv j₀ (ϕ q) = (chartInv j₀ ∘ ϕ ∘ chartMap i) (chartInv i q)`
    set A : Set (complexProjectiveSpace R k) := U ∩ chartSet i with hA
    have hAopen : IsOpen A := hUopen.inter (isOpen_chartSet i)
    have hpA : p ∈ A := ⟨hp, hpi⟩
    -- the inner chart-coordinate map `z ↦ realEquiv (chartInv j₀ (ϕ (chartMap i z)))`
    set D : Set (Fin k → Ri R) := chartMap i ⁻¹' (U ∩ chartSet i) with hD
    have hDeq : D = chartMap i ⁻¹' (U ∩ chartSet i) := rfl
    -- on `D`, the second pullback condition `(ϕ∘chartMap i)⁻¹' chartSet j₀` is automatic
    have hdomeq : chartMap i ⁻¹' (U ∩ chartSet i)
        ∩ (fun z => ϕ (chartMap i z)) ⁻¹' chartSet j₀ = D := by
      rw [hD]
      apply Set.inter_eq_left.mpr
      intro z hz
      rw [Set.mem_preimage] at *
      have hmem : chartMap i z ∈ U := hz.1
      exact hV (ϕ (chartMap i z)) (hmaps hmem)
    -- the chart coordinates of `ϕ∘chartMap i` are continuous on `D`
    have hinner : ContinuousOn
        (fun z : Fin k → Ri R => realEquiv (chartInv j₀ (ϕ (chartMap i z)))) D := by
      refine continuousOn_pi_euclidean (fun c => ?_)
      refine Fin.addCases (motive := fun c => ContinuousOn
        (fun z : Fin k → Ri R => (fun _ : Fin 1 =>
          realEquiv (chartInv j₀ (ϕ (chartMap i z))) c)) D) (fun b => ?_) (fun b => ?_) c
      · -- real part
        have hcb := (hcc i j₀ b).1
        rw [hdomeq] at hcb
        refine (isSFunctionC_continuousOn hcb).congr (fun z _ => ?_)
        funext _; rw [realEquiv_apply_castAdd]
      · -- imaginary part
        have hcb := (hcc i j₀ b).2
        rw [hdomeq] at hcb
        refine (isSFunctionC_continuousOn hcb).congr (fun z _ => ?_)
        funext _; rw [realEquiv_apply_natAdd]
    -- transport `hinner` to `chartInv j₀ ∘ ϕ` on `A` via `chartInv i`
    have hinnerC : ContinuousOn
        (fun z : Fin k → Ri R => chartInv j₀ (ϕ (chartMap i z))) D := by
      have hsymm : Continuous (realEquivₜ (R := R) (k := ℓ)).symm :=
        (realEquivₜ (R := R) (k := ℓ)).symm.continuous
      have heq : (fun z : Fin k → Ri R => chartInv j₀ (ϕ (chartMap i z)))
          = (fun w => (realEquivₜ (R := R) (k := ℓ)).symm w)
            ∘ (fun z => realEquiv (chartInv j₀ (ϕ (chartMap i z)))) := by
        funext z
        show chartInv j₀ (ϕ (chartMap i z))
            = realEquivₜ.symm (realEquiv (chartInv j₀ (ϕ (chartMap i z))))
        rw [show (realEquivₜ.symm (realEquiv (chartInv j₀ (ϕ (chartMap i z)))) : Fin ℓ → Ri R)
            = realEquiv.symm (realEquiv (chartInv j₀ (ϕ (chartMap i z)))) from rfl,
          Equiv.symm_apply_apply]
      rw [heq]; exact hsymm.comp_continuousOn hinner
    -- now compose with `chartInv i` continuous on `chartSet i`
    have hcomp : ContinuousOn (fun q => chartInv j₀ (ϕ q)) A := by
      have hmapsto : Set.MapsTo (chartInv i) A D := by
        intro q hq
        have hqi : q.rep i ≠ 0 := by
          have : q ∈ chartSet i := hq.2
          rw [chartSet_eq] at this; exact this
        rw [hD, Set.mem_preimage, chartMap_chartInv i q hqi]
        exact hq
      have hcongr : ∀ q ∈ A, chartInv j₀ (ϕ q)
          = (fun z : Fin k → Ri R => chartInv j₀ (ϕ (chartMap i z))) (chartInv i q) := by
        intro q hq
        have hqi : q.rep i ≠ 0 := by
          have : q ∈ chartSet i := hq.2
          rw [chartSet_eq] at this; exact this
        show chartInv j₀ (ϕ q) = chartInv j₀ (ϕ (chartMap i (chartInv i q)))
        rw [chartMap_chartInv i q hqi]
      refine ContinuousOn.congr ?_ hcongr
      exact hinnerC.comp ((continuousOn_chartInv i).mono Set.inter_subset_right) hmapsto
    -- continuity at `p` within `U` follows since `A = U ∩ chartSet i ∈ 𝓝[U] p`
    have hAmem : A ∈ nhdsWithin p U := by
      rw [hA]
      exact Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds ((isOpen_chartSet i).mem_nhds hpi))
    exact (hcomp.continuousWithinAt hpA).mono_of_mem_nhdsWithin hAmem
  -- assemble: `ϕ = chartMap j₀ ∘ chartInv j₀ ∘ ϕ` continuous on `U`
  refine (ContinuousOn.congr ?_ hϕeq)
  exact (continuous_chartMap j₀).comp_continuousOn hcoord

/-! ### The homotopy local IFT, with the chart fact -/

open Azurite.BPR (HasPartialDerivAtIn IsSemialgContinuousOn IsSFunction)

set_option linter.unusedSectionVars false in
/-- **Homotopy local IFT, with the chart fact.** Same as `homotopy_local_ift'`, additionally
returning `V ⊆ chartSet j₀`. The `hdet` derivation is identical to `homotopy_local_ift'`; the chart
fact is inherited from `theorem_4_104_chartV`. -/
theorem homotopy_local_ift_chartV (m : ℕ) (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (hP : ∀ i, (P i).IsHomogeneous (d i))
    (p₀ : complexProjectiveSpace R 1) (x₀ : complexProjectiveSpace R k)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (hp₀ : p₀ ∈ chartSet i₀) (hx₀ : x₀ ∈ chartSet j₀)
    (hzero : ∀ i, aeval x₀.rep (homotopyPoly P d (p₀.rep 0) (p₀.rep 1) i) = 0)
    (hns : IsNonsingularProjectiveZero (homotopyPoly P d (p₀.rep 0) (p₀.rep 1)) x₀) :
    ∃ (U : Set (complexProjectiveSpace R 1)) (V : Set (complexProjectiveSpace R k))
      (ϕ : complexProjectiveSpace R 1 → complexProjectiveSpace R k),
      IsOpen U ∧ p₀ ∈ U ∧ IsOpen V ∧ x₀ ∈ V ∧ ϕ p₀ = x₀ ∧
      IsSClassMapP m U V ϕ ∧
      (∀ p ∈ U, ∀ x ∈ V,
        ((∀ l, homotopyF P d i₀ j₀ l
            (Fin.append (realEquiv (chartInv i₀ p)) (realEquiv (chartInv j₀ x))) = 0)
          ↔ x = ϕ p)) ∧
      (∀ q ∈ V, q ∈ chartSet j₀) := by
  classical
  set z₀ : Fin ((1 + 1) + (k + k)) → R :=
    Fin.append (realEquiv (chartInv i₀ p₀)) (realEquiv (chartInv j₀ x₀)) with hz₀
  have hpi : p₀.rep i₀ ≠ 0 := by rw [chartSet_eq] at hp₀; exact hp₀
  have hzparam : z₀ ∘ Fin.castAdd (k + k) = realEquiv (chartInv i₀ p₀) := by
    funext mm; rw [hz₀, Function.comp_apply, Fin.append_left]
  have hpc : pcoordsR i₀ z₀ = Fin.insertNth i₀ (1 : Ri R) (chartInv i₀ p₀) := by
    rw [pcoordsR, hzparam, Equiv.symm_apply_apply]
  obtain ⟨cp, hcp, hprep⟩ :
      ∃ c : Ri R, c ≠ 0 ∧ p₀.rep = c • Fin.insertNth i₀ (1 : Ri R) (chartInv i₀ p₀) := by
    have h1 : mkLine p₀.rep p₀.rep_nonzero
        = mkLine (Fin.insertNth i₀ (1 : Ri R) (chartInv i₀ p₀)) (insertNth_one_ne_zero i₀ _) := by
      rw [mkLine_rep]
      conv_lhs => rw [← chartMap_chartInv i₀ p₀ hpi]
      rw [chartMap]
    exact (mkLine_eq_mkLine_iff _ _ _ _).mp h1
  have hparam0 : pcoordsR i₀ z₀ 0 = cp⁻¹ * p₀.rep 0 := by
    rw [hpc, hprep, Pi.smul_apply, smul_eq_mul]; field_simp
  have hparam1 : pcoordsR i₀ z₀ 1 = cp⁻¹ * p₀.rep 1 := by
    rw [hpc, hprep, Pi.smul_apply, smul_eq_mul]; field_simp
  have hsys : ∀ l', homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l'
      = C cp⁻¹ * homotopyPoly P d (p₀.rep 0) (p₀.rep 1) l' := by
    intro l'; rw [hparam0, hparam1, homotopyPoly_smul]
  have hns' : IsNonsingularProjectiveZero
      (fun l' => homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l') x₀ := by
    have hscale : (fun l' => homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l')
        = fun l' => C cp⁻¹ * homotopyPoly P d (p₀.rep 0) (p₀.rep 1) l' := funext hsys
    rw [hscale]
    exact isNonsingularProjectiveZero_C_smul (inv_ne_zero hcp) hns
  have hP' : ∀ l', (homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l').IsHomogeneous (d l') :=
    fun l' => homotopyPoly_isHomogeneous P d hP _ _ l'
  have hJ := isUnit_det_jacobian_dehomAt
    (fun l' => homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l') d hP' j₀ x₀ hx₀ hns'
  have hmatrix := homotopyG_matrix_eq_realifyMatrix P d i₀ j₀ p₀ x₀
  have hJaff : (jacobian (fun l' => dehomAt j₀ (homotopyPoly P d (pcoordsR i₀ z₀ 0)
        (pcoordsR i₀ z₀ 1) l')) (chartInv j₀ x₀))
      = Matrix.of fun l' b : Fin k => aeval (xcoordsR j₀ z₀)
          (pderiv (j₀.succAbove b)
            (homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l')) := by
    ext l' b
    have hxc : aeval (xcoordsR j₀ z₀) (pderiv (j₀.succAbove b)
          (homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l'))
        = aeval (chartInv j₀ x₀) (pderiv b (dehomAt j₀
            (homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l'))) := by
      rw [pderiv_dehomAt]
      have hzpt : z₀ ∘ Fin.natAdd (1 + 1) = realEquiv (chartInv j₀ x₀) := by
        funext mm; rw [hz₀, Function.comp_apply, Fin.append_right]
      rw [xcoordsR, hzpt, Equiv.symm_apply_apply, aeval_insertNth_one, aeval_dehomAt]
    rw [jacobian, Matrix.of_apply, Matrix.of_apply, hxc]
  rw [hJaff] at hJ
  have hdet : IsUnit (Matrix.of fun l j : Fin (k + k) =>
      homotopyG P d i₀ j₀ l (Fin.natAdd (1 + 1) j) z₀).det := by
    rw [hz₀, hmatrix]; exact isUnit_det_realifyMatrix _ hJ
  -- the base point real-system vanishing
  have hF0 : ∀ l, homotopyF P d i₀ j₀ l z₀ = 0 :=
    (homotopyF_eq_zero_iff P d hP i₀ j₀ p₀ x₀ hp₀ hx₀).mpr hzero
  obtain ⟨U, V, ϕ, hUsa, hUopen, hp₀U, hVsa, hVopen, hx₀V, hϕclass, hϕp₀, himpl, hVchart⟩ :=
    theorem_4_104_chartV (k := 1) (ℓ := k) m p₀ x₀ i₀ j₀ hp₀ hx₀
      (Set.univ : Set (Fin ((1 + 1) + (k + k)) → R)) isOpen_univ
      Azurite.BPR.isSemialgebraicSet_univ
      (homotopyF P d i₀ j₀) (homotopyG P d i₀ j₀)
      (Set.mem_univ _)
      (fun l => homotopyF_isSemialgContinuousOn P d i₀ j₀ l)
      (fun l j z _ => homotopyF_hasPartialDerivAtIn P d i₀ j₀ l j z)
      (fun l j => (homotopyG_isSFunction P d i₀ j₀ 0 l j).isSemialgContinuousOn)
      hF0 hdet
      (fun l j => homotopyG_isSFunction P d i₀ j₀ m l j)
  exact ⟨U, V, ϕ, hUopen, hp₀U, hVopen, hx₀V, hϕp₀, hϕclass, himpl, hVchart⟩

end Azurite.BPR.Chapter4
