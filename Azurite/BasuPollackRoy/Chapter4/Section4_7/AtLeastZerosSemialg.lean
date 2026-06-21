import Azurite.BasuPollackRoy.Chapter4.Section4_7.WeakBezoutCount

/-!
# BPR §4.7, Proposition 4.106: `atLeastZerosRP` is semialgebraic (step 1)

This file discharges step 1 of the fiber-cardinality route: the mixed
real–projective lift of the "at least `m` distinct common projective zeros" condition,
`atLeastZerosRP P d m`, is semialgebraic (`isSemialgebraicSetRP_atLeastZerosRP`).

The proof is a **single realified existential projection** over `m` homogeneous representatives
`r₁, …, r_m ∈ C^{k+1}`. Working chart-by-chart on the `ℙ₁` parameter factor, the condition
`AtLeastZeros P d (chartMap i z) m` is rewritten as the existence of `m` nonzero, pairwise
non-proportional vectors `r a ∈ C^{k+1}` with `aeval (λ, µ, r a) (homotopyJointPoly P d i') = 0` for
all `a, i'`, where `(λ, µ) = insertNth i 1 z` are concrete homogeneous coordinates of the parameter
line (this replacement of `(chartMap i z).rep` by the concrete coordinates is justified by the
linearity of `homotopyPoly` in `(λ, µ)`). Each piece — nonzeroness, non-proportionality (2×2 minor
non-vanishing), and the parameter-coupled joint zero condition (the atom
`isSemialgebraicSetC_jointZeroLocus`) — is semialgebraic over `C`; assembling them and projecting out
the `2m(k+1)` real representative coordinates yields the result.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-! ### Linearity of `homotopyPoly` in the pencil parameters `(λ, µ)` -/

set_option linter.unusedSectionVars false in
/-- Evaluating the pencil splits as `λ · Pᵢ(v) + µ · Dᵢ(v)`: it is linear in `(λ, µ)`. -/
theorem aeval_homotopyPoly_eq (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (lam mu : Ri R) (i : Fin k) (v : Fin (k + 1) → Ri R) :
    aeval v (homotopyPoly P d lam mu i)
      = lam * aeval v (P i) + mu * aeval v (diagFactor (R := R) (d i) i) := by
  rw [homotopyPoly, map_add, map_mul, map_mul, aeval_C, aeval_C,
    Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply]

set_option linter.unusedSectionVars false in
/-- Rescaling the pencil parameters `(λ, µ) ↦ (c λ, c µ)` rescales the value by `c`. Hence the zero
condition `aeval v (homotopyPoly P d λ µ i) = 0` is invariant under nonzero rescaling of `(λ, µ)`. -/
theorem aeval_homotopyPoly_smul (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (c lam mu : Ri R) (i : Fin k) (v : Fin (k + 1) → Ri R) :
    aeval v (homotopyPoly P d (c * lam) (c * mu) i)
      = c * aeval v (homotopyPoly P d lam mu i) := by
  rw [aeval_homotopyPoly_eq, aeval_homotopyPoly_eq]; ring

/-! ### Proportionality via vanishing of all `2×2` minors -/

set_option linter.unusedSectionVars false in
/-- **Two nonzero vectors span the same line iff all their `2×2` minors vanish.**
`mkLine u = mkLine v` (for nonzero `u, v`) iff `uⱼ vₗ = uₗ vⱼ` for all `j, l`. -/
theorem mkLine_eq_iff_minors_vanish (u v : Fin (k + 1) → Ri R) (hu : u ≠ 0) (hv : v ≠ 0) :
    mkLine u hu = mkLine v hv ↔ ∀ j l : Fin (k + 1), u j * v l = u l * v j := by
  rw [mkLine_eq_mkLine_iff]
  constructor
  · rintro ⟨c, _, rfl⟩ j l
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · intro hminor
    -- pick a coordinate `l₀` where `v` is nonzero
    obtain ⟨l₀, hl₀⟩ : ∃ l₀, v l₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv (funext hcon)
    refine ⟨u l₀ / v l₀, ?_, ?_⟩
    · -- the scalar is nonzero since `u ≠ 0`
      rw [ne_eq, div_eq_zero_iff, not_or]
      refine ⟨?_, hl₀⟩
      intro hul₀
      apply hu
      funext j
      have := hminor j l₀
      rw [hul₀, zero_mul] at this
      simp only [Pi.zero_apply]
      exact (mul_eq_zero.mp this).resolve_right hl₀
    · funext j
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff hl₀]
      linear_combination hminor j l₀

/-! ### Replacing the canonical chart representative by concrete homogeneous coordinates -/

set_option linter.unusedSectionVars false in
/-- The zero condition for the pencil at the line `chartMap i z` is invariant under replacing the
canonical representative `(chartMap i z).rep` of the parameter line by the concrete homogeneous
coordinates `insertNth i 1 z`. This uses the linearity of `homotopyPoly` in `(λ, µ)`. -/
theorem aeval_homotopyPoly_chartMap_iff (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i : Fin 2) (z : Fin 1 → Ri R) (r : Fin (k + 1) → Ri R) (i' : Fin k) :
    aeval r (homotopyPoly P d ((chartMap i z).rep 0) ((chartMap i z).rep 1) i') = 0
      ↔ aeval r (homotopyPoly P d ((Fin.insertNth i 1 z : Fin 2 → Ri R) 0)
          ((Fin.insertNth i 1 z : Fin 2 → Ri R) 1) i') = 0 := by
  obtain ⟨c, hc, hrep⟩ := exists_rep_smul (Fin.insertNth i 1 z) (insertNth_one_ne_zero i z)
  have hcm : (chartMap i z).rep = c • (Fin.insertNth i 1 z : Fin 2 → Ri R) := hrep
  have h0 : (chartMap i z).rep 0 = c * (Fin.insertNth i 1 z : Fin 2 → Ri R) 0 := by
    rw [hcm]; simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : (chartMap i z).rep 1 = c * (Fin.insertNth i 1 z : Fin 2 → Ri R) 1 := by
    rw [hcm]; simp only [Pi.smul_apply, smul_eq_mul]
  rw [h0, h1, aeval_homotopyPoly_smul, mul_eq_zero, or_iff_right hc]

/-! ### The representative form of `AtLeastZeros` on a chart -/

set_option linter.unusedSectionVars false in
/-- **Representative form of `AtLeastZeros` on chart `i`.** The pencil at the parameter line
`chartMap i z` has at least `m` distinct common projective zeros iff there exist `m` nonzero,
pairwise non-proportional homogeneous representatives `r : Fin m → C^{k+1}` (non-proportionality
encoded as non-vanishing of some `2×2` minor) with `aeval (r a) (homotopyPoly P d (λ) (µ) i') = 0`
for all `a, i'`, where `(λ, µ) = insertNth i 1 z` are concrete homogeneous coordinates of the line. -/
theorem atLeastZeros_chartMap_iff_exists_rep
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    (i : Fin 2) (z : Fin 1 → Ri R) (m : ℕ) :
    AtLeastZeros P d (chartMap i z) m
      ↔ ∃ r : Fin m → Fin (k + 1) → Ri R,
          (∀ a, r a ≠ 0) ∧
          (∀ a b, a ≠ b → ∃ j l : Fin (k + 1), r a j * r b l ≠ r a l * r b j) ∧
          (∀ a (i' : Fin k), aeval (r a)
            (homotopyPoly P d ((Fin.insertNth i 1 z : Fin 2 → Ri R) 0)
              ((Fin.insertNth i 1 z : Fin 2 → Ri R) 1) i') = 0) := by
  constructor
  · rintro ⟨ys, hinj, hzero⟩
    refine ⟨fun a => (ys a).rep, fun a => (ys a).rep_nonzero, ?_, ?_⟩
    · intro a b hab
      -- the lines differ, so not all minors vanish
      by_contra hcon
      push Not at hcon
      apply hab
      apply hinj
      rw [← mkLine_rep (ys a), ← mkLine_rep (ys b)]
      exact (mkLine_eq_iff_minors_vanish _ _ _ _).mpr hcon
    · intro a i'
      rw [← aeval_homotopyPoly_chartMap_iff]
      exact hzero a i'
  · rintro ⟨r, hne, hminor, hzero⟩
    refine ⟨fun a => mkLine (r a) (hne a), ?_, ?_⟩
    · intro a b hab
      by_contra hne'
      obtain ⟨j, l, hjl⟩ := hminor a b hne'
      exact hjl ((mkLine_eq_iff_minors_vanish _ _ _ _).mp hab j l)
    · intro a i'
      rw [aeval_homotopyPoly_chartMap_iff]
      -- `(mkLine (r a)).rep = c • r a`; use homogeneity to relate the two evaluations
      obtain ⟨c, hc, hrep⟩ := exists_rep_smul (r a) (hne a)
      have hcm : (mkLine (r a) (hne a)).rep = c • r a := hrep
      rw [hcm,
        aeval_smul_isHomogeneous
          (homotopyPoly_isHomogeneous P d hP _ _ i') c (r a),
        mul_eq_zero, or_iff_right (pow_ne_zero _ hc)]
      exact hzero a i'

/-! ### The semialgebraic-over-`C` predicate on the combined complex tuple

We pack the parameter coordinate `z` and the `m` representatives `r₁, …, r_m ∈ C^{k+1}` into a single
complex tuple `u : Fin (1 + m*(k+1)) → C`: coordinate `0` is `z`, and the representatives are flattened
into the remaining `m*(k+1)` coordinates via `finProdFinEquiv`. -/

variable (m : ℕ)

/-- The parameter coordinate `z = u 0` of the combined complex tuple. -/
def packZ (u : Fin (1 + m * (k + 1)) → Ri R) : Ri R := u 0

/-- The `a`-th representative `r a ∈ C^{k+1}` read off from the combined complex tuple `u`. -/
noncomputable def packR (u : Fin (1 + m * (k + 1)) → Ri R) (a : Fin m) : Fin (k + 1) → Ri R :=
  fun j => u (Fin.natAdd 1 (finProdFinEquiv (a, j)))

/-- The concrete `2 + (k+1)` joint-coordinate vector: the homogeneous parameter coordinates
`insertNth i 1 ![z]` followed by the representative `r a`. -/
noncomputable def packLamMuR (i : Fin 2) (u : Fin (1 + m * (k + 1)) → Ri R) (a : Fin m) :
    Fin (2 + (k + 1)) → Ri R :=
  Fin.append (Fin.insertNth i (1 : Ri R) (fun _ : Fin 1 => packZ m u)) (packR m u a)

/-- The substitution sending the `2 + (k+1)` variables of `homotopyJointPoly` to expressions in the
`1 + m*(k+1)` packed complex variables: the two pencil-parameter slots become the concrete
homogeneous coordinates `insertNth i (1) (z)` (constant `1` at slot `i`, the variable `z = X 0`
elsewhere), and the `k+1` homogeneous-coordinate slots become the variables of the `a`-th
representative. -/
noncomputable def jointSubstMap (i : Fin 2) (a : Fin m) :
    Fin (2 + (k + 1)) → MvPolynomial (Fin (1 + m * (k + 1))) (Ri R) :=
  Fin.append
    (Fin.insertNth i (C 1 : MvPolynomial (Fin (1 + m * (k + 1))) (Ri R))
      (fun _ : Fin 1 => X 0))
    (fun j : Fin (k + 1) => X (Fin.natAdd 1 (finProdFinEquiv (a, j))))

set_option linter.unusedSectionVars false in
/-- Evaluating `homotopyJointPoly P d i'` at the combined complex tuple `u`, after the substitution
`jointSubstMap`, equals the parameter-coupled pencil evaluation at the `a`-th representative with the
concrete homogeneous coordinates `insertNth i 1 ![u 0]`. -/
theorem aeval_jointSubst (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i : Fin 2) (a : Fin m) (i' : Fin k) (u : Fin (1 + m * (k + 1)) → Ri R) :
    aeval u (bind₁ (jointSubstMap m i a) (homotopyJointPoly P d i'))
      = aeval (packR m u a)
          (homotopyPoly P d
            ((Fin.insertNth i 1 (fun _ : Fin 1 => packZ m u) : Fin 2 → Ri R) 0)
            ((Fin.insertNth i 1 (fun _ : Fin 1 => packZ m u) : Fin 2 → Ri R) 1) i') := by
  rw [aeval_bind₁]
  -- the evaluated substitution is exactly `packLamMuR i u a`
  have hsubst : (fun b : Fin (2 + (k + 1)) =>
        (MvPolynomial.aeval u : MvPolynomial (Fin (1 + m * (k + 1))) (Ri R) →ₐ[Ri R] Ri R)
          (jointSubstMap m i a b))
      = packLamMuR m i u a := by
    funext b
    rw [packLamMuR]
    refine Fin.addCases (fun t => ?_) (fun j => ?_) b
    · rw [jointSubstMap, Fin.append_left, Fin.append_left]
      refine Fin.succAboveCases i ?_ (fun s => ?_) t
      · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same, aeval_C,
          Algebra.algebraMap_self_apply]
      · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove, aeval_X]
        rfl
    · rw [jointSubstMap, Fin.append_right, Fin.append_right, aeval_X, packR]
  rw [hsubst]
  have hpair : (Fin.insertNth i (1 : Ri R) (fun _ : Fin 1 => packZ m u) : Fin 2 → Ri R)
      = ![(Fin.insertNth i 1 (fun _ : Fin 1 => packZ m u) : Fin 2 → Ri R) 0,
          (Fin.insertNth i 1 (fun _ : Fin 1 => packZ m u) : Fin 2 → Ri R) 1] := by
    funext s
    fin_cases s <;> rfl
  rw [show packLamMuR m i u a
      = Fin.append (Fin.insertNth i (1 : Ri R) (fun _ : Fin 1 => packZ m u)) (packR m u a) from rfl,
    hpair, aeval_homotopyJointPoly]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ### Each conjunct of the predicate is semialgebraic over `C` -/

set_option linter.unusedSectionVars false in
/-- The locus where representative `a` is nonzero is semialgebraic over `C`. -/
theorem isSemialgebraicSetC_packR_ne_zero (a : Fin m) :
    IsSemialgebraicSetC {u : Fin (1 + m * (k + 1)) → Ri R | packR m u a ≠ 0} := by
  classical
  have heq : {u : Fin (1 + m * (k + 1)) → Ri R | packR m u a ≠ 0}
      = (⋂ j ∈ (Finset.univ : Finset (Fin (k + 1))),
          {u : Fin (1 + m * (k + 1)) → Ri R |
            aeval u (X (Fin.natAdd 1 (finProdFinEquiv (a, j)))
              : MvPolynomial (Fin (1 + m * (k + 1))) (Ri R)) = 0})ᶜ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iInter, Finset.mem_univ,
      forall_true_left, aeval_X, ne_eq, not_forall]
    constructor
    · intro hne
      by_contra hcon
      push Not at hcon
      exact hne (funext fun j => hcon j)
    · rintro ⟨j, hj⟩ hzero
      exact hj (congrFun hzero j)
  rw [heq]
  exact (IsSemialgebraicSetC.biInter_finset _
    (fun j _ => isSemialgebraicSetC_complexPolyZero _)).compl

set_option linter.unusedSectionVars false in
/-- The locus where representatives `a` and `b` are non-proportional (some `2×2` minor is nonzero)
is semialgebraic over `C`. -/
theorem isSemialgebraicSetC_minor_ne (a b : Fin m) :
    IsSemialgebraicSetC {u : Fin (1 + m * (k + 1)) → Ri R |
      ∃ j l : Fin (k + 1), packR m u a j * packR m u b l ≠ packR m u a l * packR m u b j} := by
  classical
  have heq : {u : Fin (1 + m * (k + 1)) → Ri R |
        ∃ j l : Fin (k + 1), packR m u a j * packR m u b l ≠ packR m u a l * packR m u b j}
      = (⋂ jl ∈ (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))),
          {u : Fin (1 + m * (k + 1)) → Ri R |
            aeval u (X (Fin.natAdd 1 (finProdFinEquiv (a, jl.1)))
                  * X (Fin.natAdd 1 (finProdFinEquiv (b, jl.2)))
                - X (Fin.natAdd 1 (finProdFinEquiv (a, jl.2)))
                  * X (Fin.natAdd 1 (finProdFinEquiv (b, jl.1)))
              : MvPolynomial (Fin (1 + m * (k + 1))) (Ri R)) = 0})ᶜ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iInter, Finset.mem_univ,
      forall_true_left, map_sub, map_mul, aeval_X, Prod.forall, not_forall]
    constructor
    · rintro ⟨j, l, hjl⟩
      refine ⟨j, l, ?_⟩
      rw [sub_eq_zero]
      intro hcon
      exact hjl hcon
    · rintro ⟨j, l, hjl⟩
      refine ⟨j, l, ?_⟩
      rw [sub_eq_zero] at hjl
      exact hjl
  rw [heq]
  exact (IsSemialgebraicSetC.biInter_finset _
    (fun jl _ => isSemialgebraicSetC_complexPolyZero _)).compl

set_option linter.unusedSectionVars false in
/-- The parameter-coupled joint zero locus for representative `a` is semialgebraic over `C`. -/
theorem isSemialgebraicSetC_jointZero (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (i : Fin 2) (a : Fin m) :
    IsSemialgebraicSetC {u : Fin (1 + m * (k + 1)) → Ri R |
      ∀ i' : Fin k, aeval u (bind₁ (jointSubstMap m i a) (homotopyJointPoly P d i')) = 0} := by
  classical
  have heq : {u : Fin (1 + m * (k + 1)) → Ri R |
        ∀ i' : Fin k, aeval u (bind₁ (jointSubstMap m i a) (homotopyJointPoly P d i')) = 0}
      = ⋂ i' ∈ (Finset.univ : Finset (Fin k)),
          {u : Fin (1 + m * (k + 1)) → Ri R |
            aeval u (bind₁ (jointSubstMap m i a) (homotopyJointPoly P d i')) = 0} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_univ, forall_true_left]
  rw [heq]
  exact IsSemialgebraicSetC.biInter_finset _
    (fun i' _ => isSemialgebraicSetC_complexPolyZero _)

/-! ### The realification reindex bridging `[z-reals, r-reals]` and the `realEquiv` layout -/

/-- The real coordinate reindex carrying the `realEquiv` layout of `C^{1 + m(k+1)}`
(re-block then im-block) to the `[z.re, z.im, r-reals]` layout `Fin (2 + (M+M))` used by the
existential projection. -/
def packReindex :
    Fin ((1 + m * (k + 1)) + (1 + m * (k + 1))) → Fin (2 + (m * (k + 1) + m * (k + 1))) :=
  Fin.addCases
    -- re-block: coordinate `t : Fin (1 + M)`
    (fun t => Fin.addCases
      (fun _ : Fin 1 => (0 : Fin (2 + (m * (k + 1) + m * (k + 1)))))
      (fun t' : Fin (m * (k + 1)) => Fin.natAdd 2 (Fin.castAdd (m * (k + 1)) t')) t)
    -- im-block: coordinate `t : Fin (1 + M)`
    (fun t => Fin.addCases
      (fun _ : Fin 1 => (1 : Fin (2 + (m * (k + 1) + m * (k + 1)))))
      (fun t' : Fin (m * (k + 1)) => Fin.natAdd 2 (Fin.natAdd (m * (k + 1)) t')) t)

set_option linter.unusedSectionVars false in
/-- The composed reindex realifies the appended complex tuple `[realEquiv.symm ζ, realEquiv.symm y]`
back to the `[ζ, y]` real layout. -/
theorem append_comp_packReindex (ζ : Fin 2 → R) (y : Fin (m * (k + 1) + m * (k + 1)) → R) :
    Fin.append ζ y ∘ packReindex m
      = realEquiv (Fin.append (realEquiv.symm ζ) (realEquiv.symm y)) := by
  funext s
  refine Fin.addCases (fun t => ?_) (fun t => ?_) s
  · -- re-block: realEquiv re of coordinate `t`
    rw [realEquiv_apply_castAdd]
    refine Fin.addCases (fun w => ?_) (fun t' => ?_) t
    · -- coordinate `0` = parameter
      have hw : w = 0 := Subsingleton.elim _ _
      subst hw
      rw [Function.comp_apply, packReindex, Fin.addCases_left, Fin.addCases_left,
        Fin.append_left, reL_symm_apply]
      show Fin.append ζ y 0 = ζ (Fin.castAdd 1 (0 : Fin 1))
      rw [show (0 : Fin (2 + (m * (k + 1) + m * (k + 1))))
            = Fin.castAdd (m * (k + 1) + m * (k + 1)) (0 : Fin 2) by
          apply Fin.ext; simp, Fin.append_left]
      rfl
    · -- coordinate `natAdd 1 t'` = representative
      rw [Function.comp_apply, packReindex, Fin.addCases_left, Fin.addCases_right,
        Fin.append_right, Fin.append_right, reL_symm_apply]
  · -- im-block: realEquiv im of coordinate `t`
    rw [realEquiv_apply_natAdd]
    refine Fin.addCases (fun w => ?_) (fun t' => ?_) t
    · have hw : w = 0 := Subsingleton.elim _ _
      subst hw
      rw [Function.comp_apply, packReindex, Fin.addCases_right, Fin.addCases_left,
        Fin.append_left, imL_symm_apply]
      show Fin.append ζ y 1 = ζ (Fin.natAdd 1 (0 : Fin 1))
      rw [show (1 : Fin (2 + (m * (k + 1) + m * (k + 1))))
            = Fin.castAdd (m * (k + 1) + m * (k + 1)) (1 : Fin 2) by
          apply Fin.ext
          show (1 : ℕ) % (2 + (m * (k + 1) + m * (k + 1))) = (1 : Fin 2).val
          rw [Fin.val_one, Nat.mod_eq_of_lt (by omega)], Fin.append_left]
      rfl
    · rw [Function.comp_apply, packReindex, Fin.addCases_right, Fin.addCases_right,
        Fin.append_right, Fin.append_right, imL_symm_apply]

/-! ### The chart-`i` realified set is semialgebraic -/

set_option linter.unusedSectionVars false in
/-- The combined semialgebraic-over-`C` predicate set: representatives are nonzero, pairwise
non-proportional, and satisfy the parameter-coupled joint zero condition. -/
theorem isSemialgebraicSetC_predC (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i : Fin 2) :
    IsSemialgebraicSetC {u : Fin (1 + m * (k + 1)) → Ri R |
      (∀ a, packR m u a ≠ 0) ∧
      (∀ a b, a ≠ b →
        ∃ j l : Fin (k + 1), packR m u a j * packR m u b l ≠ packR m u a l * packR m u b j) ∧
      (∀ a (i' : Fin k), aeval u (bind₁ (jointSubstMap m i a) (homotopyJointPoly P d i')) = 0)} := by
  classical
  have heq : {u : Fin (1 + m * (k + 1)) → Ri R |
        (∀ a, packR m u a ≠ 0) ∧
        (∀ a b, a ≠ b →
          ∃ j l : Fin (k + 1), packR m u a j * packR m u b l ≠ packR m u a l * packR m u b j) ∧
        (∀ a (i' : Fin k), aeval u (bind₁ (jointSubstMap m i a) (homotopyJointPoly P d i')) = 0)}
      = (⋂ a ∈ (Finset.univ : Finset (Fin m)),
            {u | packR m u a ≠ 0})
        ∩ (⋂ ab ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun ab => ab.1 ≠ ab.2),
            {u | ∃ j l : Fin (k + 1),
              packR m u ab.1 j * packR m u ab.2 l ≠ packR m u ab.1 l * packR m u ab.2 j})
        ∩ (⋂ a ∈ (Finset.univ : Finset (Fin m)),
            {u | ∀ i' : Fin k, aeval u (bind₁ (jointSubstMap m i a) (homotopyJointPoly P d i')) = 0}) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_univ,
      forall_true_left, Finset.mem_filter, Prod.forall, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun a => h1 a, fun a b hab => h2 a b hab⟩, fun a => h3 a⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun a => h1 a, fun a b hab => h2 a b hab, fun a => h3 a⟩
  rw [heq]
  refine IsSemialgebraicSetC.inter (IsSemialgebraicSetC.inter ?_ ?_) ?_
  · exact IsSemialgebraicSetC.biInter_finset _
      (fun a _ => isSemialgebraicSetC_packR_ne_zero m a)
  · exact IsSemialgebraicSetC.biInter_finset _
      (fun ab _ => isSemialgebraicSetC_minor_ne m ab.1 ab.2)
  · exact IsSemialgebraicSetC.biInter_finset _
      (fun a _ => isSemialgebraicSetC_jointZero m P d i a)

set_option linter.unusedSectionVars false in
/-- **The chart-`i` realified parameter set is semialgebraic.** -/
theorem isSemialgebraicSet_chartT (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) (i : Fin 2) :
    IsSemialgebraicSet
      {ζ : Fin 2 → R | AtLeastZeros P d (chartMap i (realEquiv.symm ζ)) m} := by
  classical
  -- Step 1–2: realify the predicate and reindex into the `[z-reals, r-reals]` layout.
  have hC := isSemialgebraicSetC_predC m P d i
  rw [IsSemialgebraicSetC] at hC
  have hcomap := IsSemialgebraicSet.comap (packReindex m) hC
  -- Step 3: project out the representative real coordinates.
  have hproj := IsSemialgebraicSet.exists_append_right (k := 2) (ℓ := m * (k + 1) + m * (k + 1))
    hcomap
  -- Step 4: identify the projection with `T_i`.
  convert hproj using 1
  ext ζ
  simp only [Set.mem_setOf_eq]
  rw [atLeastZeros_chartMap_iff_exists_rep P d hP i (realEquiv.symm ζ) m]
  constructor
  · rintro ⟨r, hne, hminor, hzero⟩
    -- choose `y` realifying the representatives `r`
    refine ⟨realEquiv (fun idx : Fin (m * (k + 1)) =>
      r (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2), ?_⟩
    show Fin.append ζ (realEquiv fun idx : Fin (m * (k + 1)) =>
      r (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2) ∘ packReindex m
        ∈ realEquiv '' _
    rw [append_comp_packReindex, Equiv.symm_apply_apply, realEquiv.injective.mem_set_image]
    set rr : Fin (m * (k + 1)) → Ri R := fun idx =>
      r (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2 with hrr
    set u : Fin (1 + m * (k + 1)) → Ri R :=
      Fin.append (realEquiv.symm ζ) rr with hu
    have hpackR : ∀ a, packR m u a = r a := by
      intro a
      funext j
      rw [packR, hu, Fin.append_right, hrr]
      show r (finProdFinEquiv.symm (finProdFinEquiv (a, j))).1
        (finProdFinEquiv.symm (finProdFinEquiv (a, j))).2 = r a j
      rw [Equiv.symm_apply_apply]
    refine ⟨fun a => ?_, fun a b hab => ?_, fun a i' => ?_⟩
    · rw [hpackR]; exact hne a
    · rw [hpackR, hpackR]; exact hminor a b hab
    · rw [aeval_jointSubst, hpackR]
      have hz : packZ m u = (realEquiv.symm ζ : Fin 1 → Ri R) 0 := by
        rw [packZ, hu]
        show Fin.append (realEquiv.symm ζ : Fin 1 → Ri R) rr 0
          = (realEquiv.symm ζ : Fin 1 → Ri R) 0
        rw [show (0 : Fin (1 + m * (k + 1)))
              = Fin.castAdd (m * (k + 1)) (0 : Fin 1) by
            apply Fin.ext; simp only [Fin.val_zero, Fin.val_castAdd], Fin.append_left]
      have hzf : (fun _ : Fin 1 => packZ m u) = (realEquiv.symm ζ : Fin 1 → Ri R) := by
        funext s
        have hs : s = 0 := Subsingleton.elim _ _
        subst hs; exact hz
      rw [hzf]; exact hzero a i'
  · rintro ⟨y, hy⟩
    have hy' : Fin.append ζ y ∘ packReindex m ∈ realEquiv '' _ := hy
    rw [append_comp_packReindex, realEquiv.injective.mem_set_image] at hy'
    obtain ⟨h1, h2, h3⟩ := hy'
    set u : Fin (1 + m * (k + 1)) → Ri R :=
      Fin.append (realEquiv.symm ζ) (realEquiv.symm y) with hu
    refine ⟨fun a => packR m u a, fun a => h1 a, fun a b hab => h2 a b hab, fun a i' => ?_⟩
    have hthis := h3 a i'
    rw [aeval_jointSubst] at hthis
    have hzf : (fun _ : Fin 1 => packZ m u) = (realEquiv.symm ζ : Fin 1 → Ri R) := by
      funext s
      have hs : s = 0 := Subsingleton.elim _ _
      subst hs
      rw [packZ, hu]
      show Fin.append (realEquiv.symm ζ : Fin 1 → Ri R) (realEquiv.symm y) 0
        = (realEquiv.symm ζ : Fin 1 → Ri R) 0
      rw [show (0 : Fin (1 + m * (k + 1)))
            = Fin.castAdd (m * (k + 1)) (0 : Fin 1) by
          apply Fin.ext; simp only [Fin.val_zero, Fin.val_castAdd], Fin.append_left]
    rw [hzf] at hthis
    exact hthis

set_option linter.unusedSectionVars false in
/-- **BPR §4.7 (step 1 of Proposition 4.106).** The mixed real–projective lift of the "at least `m`
distinct common projective zeros" condition is semialgebraic. -/
theorem isSemialgebraicSetRP_atLeastZerosRP
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) (m : ℕ) :
    IsSemialgebraicSetRP (atLeastZerosRP P d m) := by
  intro i
  -- The RP pullback set is a cylinder over the chart-`i` realified parameter set `T_i`.
  have heq : {w : Fin (1 + (1 + 1)) → R |
        (w ∘ Fin.castAdd (1 + 1), chartMap i (realEquiv.symm (w ∘ Fin.natAdd 1)))
          ∈ atLeastZerosRP P d m}
      = {w : Fin (1 + (1 + 1)) → R |
          (w ∘ Fin.natAdd 1) ∈
            {ζ : Fin 2 → R | AtLeastZeros P d (chartMap i (realEquiv.symm ζ)) m}} := by
    ext w
    simp only [Set.mem_setOf_eq, atLeastZerosRP]
  rw [heq]
  exact IsSemialgebraicSet.comap (Fin.natAdd 1) (isSemialgebraicSet_chartT m P d hP i)

end Azurite.BPR.Chapter4
