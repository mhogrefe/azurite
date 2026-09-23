import Azurite.BasuPollackRoy.Chapter4.Section4_7.HomotopyFamily
import Azurite.BasuPollackRoy.Chapter4.Section4_7.AffineCharts
import Mathlib.Algebra.CharP.Algebra

/-!
# BPR §4.7, Proposition 4.106: the diagonal-system count

The diagonal system `S₍₀:₁₎ = (D₁, …, D_k)` with `Dᵢ = ∏_{n=1}^{dᵢ} (X_{i+1} − n X₀)` has exactly
`d₁ ⋯ d_k` non-singular projective zeros, all of which lie in the affine chart `X₀ ≠ 0` and are
exactly the grid `{1, …, d₁} × ⋯ × {1, …, d_k}`. We prove:

* every common projective zero of `S₍₀:₁₎` is non-singular
  (`diagSystem_common_zero_isNonsingular`);
* the count `d₁ ⋯ d_k` (`diagSystem_nonsingularZero_ncard`).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-- The dehomogenized **affine factor** `∏_{n=1}^{d} (Xᵢ − n)` in `C[X₁, …, X_k]`. -/
noncomputable def affineFactor (d : ℕ) (i : Fin k) : MvPolynomial (Fin k) (Ri R) :=
  ∏ n ∈ Finset.Icc 1 d, (X i - C ((n : ℕ) : Ri R))

/-- The dehomogenized **affine system** `(∏ (X₁ − n), …, ∏ (X_k − n))`. -/
noncomputable def affineSystem (d : Fin k → ℕ) (i : Fin k) : MvPolynomial (Fin k) (Ri R) :=
  affineFactor (d i) i

set_option linter.unusedSectionVars false in
/-- **Step 1.** Evaluation of the diagonal factor at a point `v ∈ Cᵏ⁺¹`. -/
theorem aeval_diagFactor (d : ℕ) (i : Fin k) (v : Fin (k + 1) → Ri R) :
    aeval v (diagFactor (R := R) d i)
      = ∏ n ∈ Finset.Icc 1 d, (v i.succ - (n : Ri R) * v 0) := by
  rw [diagFactor, map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [map_sub, aeval_X, map_mul, aeval_C, aeval_X]; rfl

set_option linter.unusedSectionVars false in
/-- **Step 4.** The dehomogenization `Dᵢ(1, X₁, …, X_k)` of the diagonal factor is the affine
factor `∏ (Xᵢ − n)`. -/
theorem aeval_cons_one_diagFactor (d : ℕ) (i : Fin k) :
    aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X) (diagFactor (R := R) d i)
      = affineFactor d i := by
  rw [diagFactor, map_prod, affineFactor]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [map_sub, aeval_X, map_mul, aeval_C, aeval_X, Fin.cons_succ, Fin.cons_zero, mul_one]; rfl

set_option linter.unusedSectionVars false in
/-- Evaluation of the affine factor at `g ∈ Cᵏ`. -/
theorem aeval_affineFactor (d : ℕ) (i : Fin k) (g : Fin k → Ri R) :
    aeval g (affineFactor (R := R) d i) = ∏ n ∈ Finset.Icc 1 d, (g i - (n : Ri R)) := by
  rw [affineFactor, map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [map_sub, aeval_X, aeval_C]; rfl

set_option linter.unusedSectionVars false in
/-- **Step 2 (no zeros at infinity).** A common projective zero of the diagonal system has nonzero
`0`-th homogeneous coordinate. -/
theorem diagSystem_rep_zero_ne_zero (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i)
    (x : complexProjectiveSpace R k)
    (hx : ∀ i, aeval x.rep (diagSystem (R := R) d i) = 0) : x.rep 0 ≠ 0 := by
  intro h0
  apply Projectivization.rep_nonzero x
  funext m
  refine Fin.cases ?_ (fun i => ?_) m
  · exact h0
  · -- `aeval x.rep (diagSystem d i) = (x.rep i.succ)^(d i)` when `x.rep 0 = 0`.
    have hev := hx i
    rw [diagSystem, aeval_diagFactor] at hev
    have hsimp : ∀ n ∈ Finset.Icc 1 (d i),
        (x.rep i.succ - (n : Ri R) * x.rep 0) = x.rep i.succ := by
      intro n _; rw [h0, mul_zero, sub_zero]
    rw [Finset.prod_congr rfl hsimp, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel] at hev
    have : x.rep i.succ = 0 := by
      have hne : d i ≠ 0 := Nat.one_le_iff_ne_zero.mp (hd i)
      exact pow_eq_zero_iff hne |>.mp hev
    simpa using this

set_option linter.unusedSectionVars false in
/-- **Step 5 (zero condition).** `g` is a zero of the `i`-th affine factor iff its `i`-th
coordinate is one of `1, …, d`. -/
theorem aeval_affineFactor_eq_zero_iff (d : ℕ) (i : Fin k) (g : Fin k → Ri R) :
    aeval g (affineFactor (R := R) d i) = 0 ↔ ∃ n ∈ Finset.Icc 1 d, g i = (n : Ri R) := by
  rw [aeval_affineFactor, Finset.prod_eq_zero_iff]
  refine exists_congr fun n => and_congr_right fun _ => ?_
  rw [sub_eq_zero]

set_option linter.unusedSectionVars false in
/-- A derivation `D` killing every factor of a product kills the product. -/
theorem pderiv_prod_eq_zero {ι : Type*} {C : Type*} [CommRing C] {m : ℕ} (j : Fin m)
    (s : Finset ι) (p : ι → MvPolynomial (Fin m) C) (hp : ∀ a ∈ s, pderiv j (p a) = 0) :
    pderiv j (∏ a ∈ s, p a) = 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      hp a (Finset.mem_insert_self a s), ih (fun b hb => hp b (Finset.mem_insert_of_mem hb)),
      mul_zero, mul_zero, add_zero]

set_option linter.unusedSectionVars false in
/-- **Step 5 (off-diagonal).** The affine factor `∏ (Xᵢ − n)` only involves the variable `Xᵢ`:
its partial derivative in any other variable vanishes. -/
theorem pderiv_affineFactor_of_ne (d : ℕ) (i j : Fin k) (hij : j ≠ i) :
    pderiv j (affineFactor (R := R) d i) = 0 := by
  rw [affineFactor]
  refine pderiv_prod_eq_zero j _ _ fun n _ => ?_
  rw [map_sub, pderiv_X, pderiv_C, sub_zero, Pi.single_eq_of_ne' hij]

set_option linter.unusedSectionVars false in
/-- **Step 5 (diagonal entry, nonzero).** At a common zero `g` with `g i = (n₀ : Ri R)`,
`n₀ ∈ Icc 1 d`, the diagonal partial derivative `(∂/∂Xᵢ) ∏ (Xᵢ − n)` evaluates to the nonzero
product `∏_{n ≠ n₀} (n₀ − n)`. -/
theorem aeval_pderiv_affineFactor_ne_zero (d : ℕ) (i : Fin k) (g : Fin k → Ri R)
    {n₀ : ℕ} (hn₀ : n₀ ∈ Finset.Icc 1 d) (hgi : g i = (n₀ : Ri R)) :
    aeval g (pderiv i (affineFactor (R := R) d i)) ≠ 0 := by
  classical
  have : CharZero (Ri R) :=
    charZero_of_injective_algebraMap (algebraMap R (Ri R)).injective
  set rest : MvPolynomial (Fin k) (Ri R) :=
    ∏ n ∈ Finset.Icc 1 d \ {n₀}, (X i - C ((n : ℕ) : Ri R)) with hrest
  -- Factor `affineFactor = rest * (X i - C n₀)`.
  have hfact : affineFactor (R := R) d i = rest * (X i - C ((n₀ : ℕ) : Ri R)) := by
    rw [affineFactor, hrest, Finset.prod_eq_prod_sdiff_singleton_mul hn₀]
  -- Differentiate: the second term vanishes after `aeval` at `g`.
  have hpderiv : pderiv i (affineFactor (R := R) d i)
      = rest + pderiv i rest * (X i - C ((n₀ : ℕ) : Ri R)) := by
    rw [hfact, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      map_sub, pderiv_X, pderiv_C, sub_zero, Pi.single_eq_same, mul_one]
    ring
  rw [hpderiv, map_add, map_mul, map_sub, aeval_X, aeval_C, hgi]
  -- The `(g i - n₀)`-factor is zero; left with `aeval g rest`.
  have hz : ((n₀ : Ri R) - (algebraMap (Ri R) (Ri R)) ((n₀ : ℕ) : Ri R)) = 0 := by
    simp
  rw [hz, mul_zero, add_zero]
  -- `aeval g rest = ∏_{n ≠ n₀} (n₀ - n) ≠ 0`.
  rw [hrest, map_prod, Finset.prod_ne_zero_iff]
  intro n hn
  rw [map_sub, aeval_X, aeval_C, hgi, sub_ne_zero]
  intro hcontra
  -- `(n₀ : Ri R) = (n : Ri R)` would force `n₀ = n`, contradicting `n ∈ Icc \ {n₀}`.
  have hcast : (n₀ : Ri R) = (n : Ri R) := by
    rw [hcontra]; rfl
  have hn0n : n₀ = n := Nat.cast_injective hcast
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hn
  exact hn.2 hn0n.symm

set_option linter.unusedSectionVars false in
/-- **Step 5 (nonsingularity).** Every common affine zero of the affine system is a non-singular
zero: its Jacobian is diagonal with nonzero diagonal entries. -/
theorem isNonsingularZero_affineSystem (d : Fin k → ℕ) (g : Fin k → Ri R)
    (hg : ∀ i, aeval g (affineSystem (R := R) d i) = 0) :
    IsNonsingularZero (affineSystem d) g := by
  classical
  refine ⟨hg, ?_⟩
  -- Each coordinate `g i` is some root `n₀ i ∈ Icc 1 (d i)`.
  have hroot : ∀ i, ∃ n ∈ Finset.Icc 1 (d i), g i = (n : Ri R) := by
    intro i
    have := hg i
    rw [affineSystem, aeval_affineFactor_eq_zero_iff] at this
    exact this
  choose n₀ hn₀mem hn₀eq using hroot
  -- The Jacobian is diagonal.
  have hdiag : jacobian (affineSystem d) g
      = Matrix.diagonal (fun i => aeval g (pderiv i (affineFactor (R := R) (d i) i))) := by
    ext i j
    rw [jacobian, Matrix.of_apply, Matrix.diagonal_apply]
    by_cases hij : j = i
    · subst hij; rw [ite_eq_left rfl]; rfl
    · rw [ite_eq_right (fun h => hij h.symm), affineSystem,
        pderiv_affineFactor_of_ne (d i) i j hij, map_zero]
  rw [hdiag, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
  intro i _
  exact aeval_pderiv_affineFactor_ne_zero (d i) i g (hn₀mem i) (hn₀eq i)

set_option linter.unusedSectionVars false in
/-- Inserting `1` in coordinate `0` is `Fin.cons 1`. -/
theorem insertNth_zero_eq_cons (g : Fin k → Ri R) :
    Fin.insertNth 0 (1 : Ri R) g = (Fin.cons (1 : Ri R) g : Fin (k + 1) → Ri R) := by
  funext m
  refine Fin.cases ?_ (fun j => ?_) m
  · rw [Fin.insertNth_apply_same, Fin.cons_zero]
  · rw [Fin.cons_succ, ← Fin.succAbove_zero, Fin.insertNth_apply_succAbove]

set_option linter.unusedSectionVars false in
/-- A common projective zero in chart `0` gives a common affine zero of the affine system. -/
theorem affineSystem_common_zero_of_projective (d : Fin k → ℕ)
    (x : complexProjectiveSpace R k) (hx0 : x.rep 0 ≠ 0)
    (hx : ∀ i, aeval x.rep (diagSystem (R := R) d i) = 0) :
    ∀ i, aeval (chartInv 0 x) (affineSystem (R := R) d i) = 0 := by
  set g := chartInv 0 x with hg
  -- `x = mkLine (cons 1 g)`, so `x.rep = c • cons 1 g`.
  have hchart : chartMap 0 g = mkLine (Fin.cons (1 : Ri R) g) (cons_one_ne_zero g) := by
    rw [chartMap, mkLine_eq_mkLine_iff]
    exact ⟨1, one_ne_zero, by rw [one_smul, insertNth_zero_eq_cons]⟩
  have hxeq : x = mkLine (Fin.cons (1 : Ri R) g) (cons_one_ne_zero g) := by
    rw [← hchart, hg, chartMap_chartInv 0 x hx0]
  obtain ⟨c, hc, hrep⟩ : ∃ c : Ri R, c ≠ 0 ∧ x.rep = c • (Fin.cons (1 : Ri R) g) := by
    have hmk : mkLine x.rep (Projectivization.rep_nonzero x)
        = mkLine (Fin.cons (1 : Ri R) g) (cons_one_ne_zero g) := by
      rw [mkLine, Projectivization.mk_rep, ← hxeq]
    exact (mkLine_eq_mkLine_iff _ _ _ _).mp hmk
  intro i
  -- From `hx i` and homogeneity, `aeval (cons 1 g) (diagSystem d i) = 0`.
  have hcz : aeval (Fin.cons (1 : Ri R) g) (diagSystem (R := R) d i) = 0 := by
    have hev := hx i
    rw [diagSystem, hrep, aeval_smul_isHomogeneous (diagFactor_isHomogeneous (d i) i)] at hev
    rw [diagSystem]
    exact (mul_eq_zero.mp hev).resolve_left (pow_ne_zero _ hc)
  rw [affineSystem, ← aeval_cons_one_diagFactor, aeval_aeval_cons_one]
  exact hcz

/-- **BPR Proposition 4.106 (non-singularity).** Every common projective zero of the diagonal
system is a non-singular projective zero. -/
theorem diagSystem_common_zero_isNonsingular (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i)
    (x : complexProjectiveSpace R k)
    (hx : ∀ i, MvPolynomial.aeval x.rep (diagSystem (R := R) d i) = 0) :
    IsNonsingularProjectiveZero (diagSystem d) x := by
  -- No zeros at infinity: `x.rep 0 ≠ 0`.
  have hx0 : x.rep 0 ≠ 0 := diagSystem_rep_zero_ne_zero d hd x hx
  set g := chartInv 0 x with hg
  -- `x = mkLine (cons 1 g)`.
  have hchart : chartMap 0 g = mkLine (Fin.cons (1 : Ri R) g) (cons_one_ne_zero g) := by
    rw [chartMap, mkLine_eq_mkLine_iff]
    exact ⟨1, one_ne_zero, by rw [one_smul, insertNth_zero_eq_cons]⟩
  have hxeq : x = mkLine (Fin.cons (1 : Ri R) g) (cons_one_ne_zero g) := by
    rw [← hchart, hg, chartMap_chartInv 0 x hx0]
  -- `g` is a common affine zero, hence a non-singular affine zero.
  have haff : ∀ i, aeval g (affineSystem (R := R) d i) = 0 :=
    affineSystem_common_zero_of_projective d x hx0 hx
  have hns : IsNonsingularZero (affineSystem (R := R) d) g :=
    isNonsingularZero_affineSystem d g haff
  -- Transport along the Note.
  have hiff := isNonsingularZero_dehom_iff_isNonsingularProjectiveZero
    (diagSystem (R := R) d) d (fun i => diagFactor_isHomogeneous (R := R) (d i) i) g
  rw [hxeq, ← hiff]
  -- The Note's dehomogenized system equals the affine system.
  have hdehom : affineSystem (R := R) d
      = (fun i => aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X)
        (diagSystem (R := R) d i)) := by
    funext i; rw [affineSystem, ← aeval_cons_one_diagFactor, diagSystem]
  rw [hdehom] at hns
  exact hns

set_option linter.unusedSectionVars false in
/-- The chart-`0` embedding `g ↦ (1 : g₁ : ⋯ : g_k)` is injective. -/
theorem mkLine_cons_one_injective :
    Function.Injective (fun g : Fin k → Ri R => mkLine (Fin.cons (1 : Ri R) g) (cons_one_ne_zero g))
    := by
  intro g g' hgg
  obtain ⟨c, hc, hceq⟩ := (mkLine_eq_mkLine_iff _ _ _ _).mp hgg
  -- The `0`-th entry forces `c = 1`.
  have hc1 : c = 1 := by
    have := congrFun hceq 0
    simpa [Fin.cons_zero] using this.symm
  funext j
  have := congrFun hceq j.succ
  simpa [Fin.cons_succ, hc1] using this

set_option linter.unusedSectionVars false in
/-- A non-singular projective zero of the affine-system embedding is exactly the image of a common
affine zero. -/
theorem isNonsingularProjectiveZero_diagSystem_iff (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i)
    (x : complexProjectiveSpace R k) :
    IsNonsingularProjectiveZero (diagSystem (R := R) d) x
      ↔ ∃ g : Fin k → Ri R, (∀ i, aeval g (affineSystem (R := R) d i) = 0) ∧
          mkLine (Fin.cons (1 : Ri R) g) (cons_one_ne_zero g) = x := by
  constructor
  · intro hns
    have hx0 : x.rep 0 ≠ 0 := diagSystem_rep_zero_ne_zero d hd x hns.1
    refine ⟨chartInv 0 x, affineSystem_common_zero_of_projective d x hx0 hns.1, ?_⟩
    have hchart : chartMap 0 (chartInv 0 x)
        = mkLine (Fin.cons (1 : Ri R) (chartInv 0 x)) (cons_one_ne_zero (chartInv 0 x)) := by
      rw [chartMap, mkLine_eq_mkLine_iff]
      exact ⟨1, one_ne_zero, by rw [one_smul, insertNth_zero_eq_cons]⟩
    rw [← hchart, chartMap_chartInv 0 x hx0]
  · rintro ⟨g, hg, rfl⟩
    have hns : IsNonsingularZero (affineSystem (R := R) d) g :=
      isNonsingularZero_affineSystem d g hg
    have hiff := isNonsingularZero_dehom_iff_isNonsingularProjectiveZero
      (diagSystem (R := R) d) d (fun i => diagFactor_isHomogeneous (R := R) (d i) i) g
    rw [← hiff]
    have hdehom : affineSystem (R := R) d
        = (fun i => aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X)
          (diagSystem (R := R) d i)) := by
      funext i; rw [affineSystem, ← aeval_cons_one_diagFactor, diagSystem]
    rw [hdehom] at hns
    exact hns

set_option linter.unusedSectionVars false in
/-- The common-zero set of the affine system is the grid `{1,…,d₁} × ⋯ × {1,…,d_k}`. -/
theorem affineSystem_common_zero_eq_piFinset (d : Fin k → ℕ) :
    {g : Fin k → Ri R | ∀ i, aeval g (affineSystem (R := R) d i) = 0}
      = ↑(Fintype.piFinset
          (fun i => (Finset.Icc 1 (d i)).image (fun n : ℕ => (n : Ri R)))) := by
  ext g
  rw [Set.mem_ofPred_eq, Fintype.coe_piFinset, Set.mem_univ_pi]
  refine forall_congr' fun i => ?_
  rw [affineSystem, aeval_affineFactor_eq_zero_iff, Finset.coe_image, Set.mem_image]
  constructor
  · rintro ⟨n, hn, hgi⟩; exact ⟨n, Finset.mem_coe.mpr hn, hgi.symm⟩
  · rintro ⟨n, hn, hgi⟩; exact ⟨n, Finset.mem_coe.mp hn, hgi.symm⟩

set_option linter.unusedSectionVars false in
/-- **BPR Proposition 4.106 (count).** The diagonal system has exactly `d₁·d₂·…·d_k` non-singular
projective zeros. -/
theorem diagSystem_nonsingularZero_ncard (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i) :
    {x : complexProjectiveSpace R k | IsNonsingularProjectiveZero (diagSystem d) x}.ncard
      = ∏ i, d i := by
  classical
  have : CharZero (Ri R) :=
    charZero_of_injective_algebraMap (algebraMap R (Ri R)).injective
  -- The projective nonsingular-zero set is the image of the affine grid.
  set Aff : Set (Fin k → Ri R) :=
    {g | ∀ i, aeval g (affineSystem (R := R) d i) = 0} with hAff
  set f : (Fin k → Ri R) → complexProjectiveSpace R k :=
    fun g => mkLine (Fin.cons (1 : Ri R) g) (cons_one_ne_zero g) with hf
  have himg : {x : complexProjectiveSpace R k | IsNonsingularProjectiveZero (diagSystem d) x}
      = f '' Aff := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_image]
    rw [isNonsingularProjectiveZero_diagSystem_iff d hd]
    exact ⟨fun ⟨g, hg, hx⟩ => ⟨g, hg, hx⟩, fun ⟨g, hg, hx⟩ => ⟨g, hg, hx⟩⟩
  rw [himg, Set.ncard_image_of_injective Aff mkLine_cons_one_injective, hAff,
    affineSystem_common_zero_eq_piFinset, Set.ncard_coe_finset, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc, Nat.add_sub_cancel]

end Azurite.BPR.Chapter4
