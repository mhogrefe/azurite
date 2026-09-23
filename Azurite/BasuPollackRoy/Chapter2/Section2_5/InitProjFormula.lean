import Azurite.BasuPollackRoy.Chapter2.Section2_4.ParametrizedTarskiQuery
import Azurite.BasuPollackRoy.Chapter2.Section2_4.BasicCellStratumA
import Azurite.BasuPollackRoy.Chapter2.Section2_4.BasicCellProjection
import Azurite.BasuPollackRoy.Chapter2.Section2_4.StratumB

/-! # Formula-level `Fin.init` projection (towards `huinitproj` / Theorem 2.76)

This file builds the explicit, **field-uniform** quantifier-free formula for the
`Fin.init` projection of a quantifier-free formula — the single remaining ingredient
`huinitproj` of BPR Theorem 2.80 (`Section2_5/Theorem_2_80.lean`). The strategy mirrors
the set-level Theorem 2.76 but stays at the `Formula` level, reusing the already
field-parametric building blocks (`tarskiFormula`, `fiberFormula_high`, `degFormula`,
the sign/atom formulas, `disjListO`): DNF into basic cells, project each cell
(Stratum A/B as formulas), and take the disjunction.

So far: the `conjListO` helper (conjunction of a list of formulas), used to assemble the
matrix/sign conditions at the formula level.
-/

namespace Azurite.BPR
namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]

/-- Conjunction of a list of ordered-field formulas (empty list = the true atom `1 > 0`). -/
noncomputable def conjListO (l : List (Formula σ (OrderedFieldAtom σ D))) :
    Formula σ (OrderedFieldAtom σ D) :=
  l.foldr Formula.and (gtZeroO 1)

theorem conjListO_isQF (l : List (Formula σ (OrderedFieldAtom σ D)))
    (h : ∀ Φ ∈ l, Φ.IsQuantifierFree) : (conjListO l).IsQuantifierFree := by
  induction l with
  | nil => exact trivial
  | cons a t ih =>
    exact ⟨h a List.mem_cons_self, ih (fun Φ hΦ => h Φ (List.mem_cons_of_mem _ hΦ))⟩

variable [DecidableEq σ] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Algebra D R]

@[simp] theorem realization_conjListO (l : List (Formula σ (OrderedFieldAtom σ D))) :
    (conjListO l).realization (C := R) = {y | ∀ Φ ∈ l, y ∈ Φ.realization (C := R)} := by
  induction l with
  | nil => ext y; simp [conjListO, realization_gtZeroO]
  | cons a t ih =>
    ext y
    simp only [conjListO, List.foldr_cons, Formula.realization, Set.mem_inter_iff,
      Set.mem_ofPred_eq, List.forall_mem_cons]
    rw [show (List.foldr Formula.and (gtZeroO 1) t) = conjListO t from rfl, ih]
    simp [Set.mem_ofPred_eq]

end Formula

open _root_.Polynomial
open scoped Matrix

variable {k s : ℕ} {D : Type*} [CommRing D] [IsDomain D]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Algebra D R] [IsRealClosed R]

/-! ## Stratum A: the matrix-condition formula

`matrixFormula` is the explicit quantifier-free formula whose realization is the
`{y | P_y ≢ 0 ∧ 0 < (M ·ᵥ TarskiQueryVec) j₀}` locus — the formula-level counterpart of
`matrixLocus_isSemialgebraicSetOver` (`Section2_4/BasicCellStratumA.lean`). It is
field-uniform: the same formula works over every real closed field. -/

/-- The Stratum A (matrix-condition) locus as an explicit quantifier-free formula. -/
noncomputable def matrixFormula (P_split : Polynomial (MvPolynomial (Fin k) D))
    (𝒬 : Fin s → Polynomial (MvPolynomial (Fin k) D))
    (M : Matrix (Fin (3 ^ s)) (Fin (3 ^ s)) ℚ) (j₀ : Fin (3 ^ s)) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  Formula.disjListO
    (((Fintype.piFinset (fun _ : Fin (3 ^ s) =>
        Finset.Icc (-(P_split.natDegree : ℤ)) (P_split.natDegree : ℤ))).filter
        (fun c => 0 < (M *ᵥ (fun i => (c i : ℚ))) j₀)).toList.map
      (fun c => Formula.conjListO ((List.finRange (3 ^ s)).map
        (fun i => tarskiFormula P_split 𝒬 (expFn s i) (c i)))))

theorem matrixFormula_isQF (P_split : Polynomial (MvPolynomial (Fin k) D))
    (𝒬 : Fin s → Polynomial (MvPolynomial (Fin k) D))
    (M : Matrix (Fin (3 ^ s)) (Fin (3 ^ s)) ℚ) (j₀ : Fin (3 ^ s)) :
    (matrixFormula P_split 𝒬 M j₀).IsQuantifierFree := by
  apply Formula.disjListO_isQF
  intro Φ hΦ
  simp only [List.mem_map] at hΦ
  obtain ⟨c, _, rfl⟩ := hΦ
  apply Formula.conjListO_isQF
  intro Ψ hΨ
  simp only [List.mem_map] at hΨ
  obtain ⟨i, _, rfl⟩ := hΨ
  exact tarskiFormula_isQF P_split 𝒬 (expFn s i) (c i)

theorem matrixFormula_realization (P_split : Polynomial (MvPolynomial (Fin k) D))
    (𝒬 : Fin s → Polynomial (MvPolynomial (Fin k) D))
    (M : Matrix (Fin (3 ^ s)) (Fin (3 ^ s)) ℚ) (j₀ : Fin (3 ^ s))
    (hinj : Function.Injective (algebraMap D R)) :
    (matrixFormula P_split 𝒬 M j₀).realization (C := R) =
      {y : Fin k → R | P_split.map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
        0 < (M *ᵥ (fun i => (tarskiQuery
              (familyPow (fun j => (𝒬 j).map (MvPolynomial.aeval y).toRingHom) (expFn s i))
              (P_split.map (MvPolynomial.aeval y).toRingHom) : ℚ))) j₀} := by
  classical
  rw [matrixFormula, Formula.realization_disjListO]
  ext y
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨Φ, hΦmem, hyΦ⟩
    rw [List.mem_map] at hΦmem
    obtain ⟨c, hcmem, rfl⟩ := hΦmem
    rw [Finset.mem_toList, Finset.mem_filter] at hcmem
    rw [Formula.realization_conjListO, Set.mem_ofPred_eq] at hyΦ
    have hAi : ∀ i, y ∈ (tarskiFormula P_split 𝒬 (expFn s i) (c i)).realization (C := R) :=
      fun i => hyΦ _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    simp only [tarskiFormula_realization P_split 𝒬 _ _ hinj, Set.mem_ofPred_eq] at hAi
    refine ⟨(hAi j₀).1, ?_⟩
    have hvc : (fun i => ((tarskiQuery
        (familyPow (fun j => (𝒬 j).map (MvPolynomial.aeval y).toRingHom) (expFn s i))
        (P_split.map (MvPolynomial.aeval y).toRingHom)) : ℚ)) = (fun i => (c i : ℚ)) :=
      funext (fun i => by rw [(hAi i).2])
    rw [hvc]; exact hcmem.2
  · rintro ⟨hPy, hpos⟩
    refine ⟨_, List.mem_map.mpr ⟨fun i => tarskiQuery
        (familyPow (fun j => (𝒬 j).map (MvPolynomial.aeval y).toRingHom) (expFn s i))
        (P_split.map (MvPolynomial.aeval y).toRingHom), ?_, rfl⟩, ?_⟩
    · rw [Finset.mem_toList, Finset.mem_filter]
      refine ⟨?_, hpos⟩
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      have hb : |tarskiQuery
          (familyPow (fun j => (𝒬 j).map (MvPolynomial.aeval y).toRingHom) (expFn s i))
          (P_split.map (MvPolynomial.aeval y).toRingHom)| ≤ (P_split.natDegree : ℤ) :=
        le_trans (abs_tarskiQuery_le_natDegree _ _) (by exact_mod_cast Polynomial.natDegree_map_le)
      exact ⟨(abs_le.mp hb).1, (abs_le.mp hb).2⟩
    · rw [Formula.realization_conjListO, Set.mem_ofPred_eq]
      intro Ψ hΨ
      rw [List.mem_map] at hΨ
      obtain ⟨i, _, rfl⟩ := hΨ
      rw [tarskiFormula_realization P_split 𝒬 _ _ hinj, Set.mem_ofPred_eq]
      exact ⟨hPy, rfl⟩

/-- The **Stratum A formula** for a basic cell `(P, Q)`: `matrixFormula` specialized via
Lemma 2.74 (`stratumA_eq_matrix`). Its realization over any real closed field is the
`P_y ≢ 0` stratum of the basic-cell projection. -/
noncomputable def stratumAFormula (P : MvPolynomial (Fin (k + 1)) D)
    (Q : Finset (MvPolynomial (Fin (k + 1)) D)) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  matrixFormula (splitLast P) (fun j => splitLast (Q.toList.get j))
    ((signMatrixQ Q.toList.length)⁻¹)
    ((signEquiv Q.toList.length).symm (fun _ => SignType.pos))

theorem stratumAFormula_isQF (P : MvPolynomial (Fin (k + 1)) D)
    (Q : Finset (MvPolynomial (Fin (k + 1)) D)) :
    (stratumAFormula P Q).IsQuantifierFree :=
  matrixFormula_isQF _ _ _ _

theorem stratumAFormula_realization (hinj : Function.Injective (algebraMap D R))
    (P : MvPolynomial (Fin (k + 1)) D) (Q : Finset (MvPolynomial (Fin (k + 1)) D)) :
    (stratumAFormula P Q).realization (C := R) =
      {y : Fin k → R | (splitLast P).map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
        ∃ x, ((splitLast P).map (MvPolynomial.aeval y).toRingHom).IsRoot x ∧
          ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x} := by
  rw [stratumAFormula, matrixFormula_realization _ _ _ _ hinj, ← stratumA_eq_matrix]

/-! ## Stratum B: degree, sign-at-`±∞`, and realizability formulas

These mirror the foundational loci of `BasicCellStratumB`/`StratumB` at the `Formula`
level. They are field-uniform. -/

/-- `deg P_y = d` as a quantifier-free formula (the `degFormula` cast into `OrderedFieldAtom`). -/
noncomputable def degFormulaO (P : Polynomial (MvPolynomial (Fin k) D)) (d : WithBot ℕ) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  (degFormula P d).mapAtom FieldAtom.toOrderedFieldAtom

omit [IsDomain D] [IsRealClosed R] in
theorem degFormulaO_isQF (P : Polynomial (MvPolynomial (Fin k) D)) (d : WithBot ℕ) :
    (degFormulaO P d).IsQuantifierFree := by
  rw [degFormulaO, Formula.mapAtom_isQF]; exact degFormula_isQF P d

omit [IsDomain D] [IsRealClosed R] in
theorem degFormulaO_realization (P : Polynomial (MvPolynomial (Fin k) D)) (d : WithBot ℕ) :
    (degFormulaO P d).realization (C := R) =
      {y : Fin k → R | (P.map (MvPolynomial.aeval y).toRingHom).degree = d} := by
  rw [degFormulaO, Formula.realization_mapAtom_toOrderedFieldAtom, realization_degFormula]

/-- `P_y ≠ 0` as a quantifier-free formula (`deg P_y ≠ ⊥`). -/
noncomputable def neZeroPolyFormula (P : Polynomial (MvPolynomial (Fin k) D)) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  .not (degFormulaO P ⊥)

omit [IsDomain D] [IsRealClosed R] in
theorem neZeroPolyFormula_isQF (P : Polynomial (MvPolynomial (Fin k) D)) :
    (neZeroPolyFormula P).IsQuantifierFree := degFormulaO_isQF P ⊥

omit [IsDomain D] [IsRealClosed R] in
theorem neZeroPolyFormula_realization (P : Polynomial (MvPolynomial (Fin k) D)) :
    (neZeroPolyFormula P).realization (C := R) =
      {y : Fin k → R | P.map (MvPolynomial.aeval y).toRingHom ≠ 0} := by
  rw [neZeroPolyFormula, Formula.realization, degFormulaO_realization]
  ext y; simp [Polynomial.degree_eq_bot]

/-- `signAtPosInfty(P_y) = +` as a formula: union over the degree `n` of
`deg P_y = n ∧ 0 < P.coeff n` (the leading coefficient is positive). -/
noncomputable def signPosInftyFormula (P : Polynomial (MvPolynomial (Fin k) D)) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  Formula.disjListO ((List.range (P.natDegree + 1)).map
    (fun n => (degFormulaO P (n : ℕ)).and (Formula.gtZeroO (P.coeff n))))

omit [IsDomain D] [IsRealClosed R] in
theorem signPosInftyFormula_isQF (P : Polynomial (MvPolynomial (Fin k) D)) :
    (signPosInftyFormula P).IsQuantifierFree := by
  apply Formula.disjListO_isQF
  intro Φ hΦ; simp only [List.mem_map, List.mem_range] at hΦ
  obtain ⟨n, _, rfl⟩ := hΦ
  exact ⟨degFormulaO_isQF P _, trivial⟩

omit [IsDomain D] [IsRealClosed R] in
theorem signPosInftyFormula_realization (P : Polynomial (MvPolynomial (Fin k) D)) :
    (signPosInftyFormula P).realization (C := R) =
      {y : Fin k → R | signAtPosInfty (P.map (MvPolynomial.aeval y).toRingHom) = SignType.pos} := by
  classical
  rw [signPosInftyFormula, Formula.realization_disjListO]
  ext y
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, signAtPosInfty_eq_sign_leadingCoeff]
  constructor
  · rintro ⟨Φ, hmem, hyΦ⟩
    rw [List.mem_map] at hmem
    obtain ⟨n, _, rfl⟩ := hmem
    rw [Formula.realization_and, Set.mem_inter_iff, degFormulaO_realization, Set.mem_ofPred_eq,
      Formula.realization_gtZeroO, Set.mem_ofPred_eq] at hyΦ
    obtain ⟨hdeg, hcpos⟩ := hyΦ
    have hnd : (P.map (MvPolynomial.aeval y).toRingHom).natDegree = n := by
      rw [Polynomial.natDegree, hdeg]; rfl
    have hlc : (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff
        = MvPolynomial.aeval y (P.coeff n) := by
      rw [Polynomial.leadingCoeff, hnd, Polynomial.coeff_map]; rfl
    rw [hlc]; exact sign_eq_one_iff.mpr hcpos
  · intro hsign
    have hpos : 0 < (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff := sign_eq_one_iff.mp hsign
    have hne : P.map (MvPolynomial.aeval y).toRingHom ≠ 0 := by
      rintro h; rw [h] at hpos; simp at hpos
    set m := (P.map (MvPolynomial.aeval y).toRingHom).natDegree with hm
    have hlc : (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff
        = MvPolynomial.aeval y (P.coeff m) := by
      rw [Polynomial.leadingCoeff, ← hm, Polynomial.coeff_map]; rfl
    refine ⟨_, List.mem_map.mpr ⟨m, List.mem_range.mpr ?_, rfl⟩, ?_⟩
    · have := Polynomial.natDegree_map_le (f := (MvPolynomial.aeval y).toRingHom) (p := P); omega
    · rw [Formula.realization_and, Set.mem_inter_iff, degFormulaO_realization, Set.mem_ofPred_eq,
        Formula.realization_gtZeroO, Set.mem_ofPred_eq]
      exact ⟨Polynomial.degree_eq_natDegree hne, by rw [← hlc]; exact hpos⟩

/-- `signAtNegInfty(P_y) = +` as a formula: union over `n` of `deg P_y = n ∧ 0 < (-1)^n · P.coeff n`. -/
noncomputable def signNegInftyFormula (P : Polynomial (MvPolynomial (Fin k) D)) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  Formula.disjListO ((List.range (P.natDegree + 1)).map
    (fun n => (degFormulaO P (n : ℕ)).and (Formula.gtZeroO ((-1) ^ n * P.coeff n))))

omit [IsDomain D] [IsRealClosed R] in
theorem signNegInftyFormula_isQF (P : Polynomial (MvPolynomial (Fin k) D)) :
    (signNegInftyFormula P).IsQuantifierFree := by
  apply Formula.disjListO_isQF
  intro Φ hΦ; simp only [List.mem_map, List.mem_range] at hΦ
  obtain ⟨n, _, rfl⟩ := hΦ
  exact ⟨degFormulaO_isQF P _, trivial⟩

omit [IsDomain D] [IsRealClosed R] in
theorem signNegInftyFormula_realization (P : Polynomial (MvPolynomial (Fin k) D)) :
    (signNegInftyFormula P).realization (C := R) =
      {y : Fin k → R | signAtNegInfty (P.map (MvPolynomial.aeval y).toRingHom) = SignType.pos} := by
  classical
  have key : ∀ (z : R) (m : ℕ),
      ((-1 : SignType) ^ m * SignType.sign z = SignType.pos) ↔ (0 < (-1 : R) ^ m * z) := by
    intro z m; rw [← sign_eq_one_iff, sign_mul, sign_pow, sign_neg neg_one_lt_zero]; rfl
  have haeval : ∀ (y : Fin k → R) (j : ℕ), MvPolynomial.aeval y ((-1) ^ j * P.coeff j)
      = (-1 : R) ^ j * MvPolynomial.aeval y (P.coeff j) := fun y j => by
    rw [map_mul, map_pow, map_neg, map_one]
  rw [signNegInftyFormula, Formula.realization_disjListO]
  ext y
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨Φ, hmem, hyΦ⟩
    rw [List.mem_map] at hmem
    obtain ⟨n, _, rfl⟩ := hmem
    rw [Formula.realization_and, Set.mem_inter_iff, degFormulaO_realization, Set.mem_ofPred_eq,
      Formula.realization_gtZeroO, Set.mem_ofPred_eq] at hyΦ
    obtain ⟨hdeg, hcpos⟩ := hyΦ
    have hnd : (P.map (MvPolynomial.aeval y).toRingHom).natDegree = n := by
      rw [Polynomial.natDegree, hdeg]; rfl
    have hlc : (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff
        = MvPolynomial.aeval y (P.coeff n) := by
      rw [Polynomial.leadingCoeff, hnd, Polynomial.coeff_map]; rfl
    rw [signAtNegInfty_eq_sign_leadingCoeff, hnd, hlc]
    rw [haeval] at hcpos
    exact (key _ n).mpr hcpos
  · intro hsign
    rw [signAtNegInfty_eq_sign_leadingCoeff] at hsign
    have hne : P.map (MvPolynomial.aeval y).toRingHom ≠ 0 := by
      rintro h; rw [h] at hsign; simp at hsign
    set m := (P.map (MvPolynomial.aeval y).toRingHom).natDegree with hm
    have hlc : (P.map (MvPolynomial.aeval y).toRingHom).leadingCoeff
        = MvPolynomial.aeval y (P.coeff m) := by
      rw [Polynomial.leadingCoeff, ← hm, Polynomial.coeff_map]; rfl
    refine ⟨_, List.mem_map.mpr ⟨m, List.mem_range.mpr ?_, rfl⟩, ?_⟩
    · have := Polynomial.natDegree_map_le (f := (MvPolynomial.aeval y).toRingHom) (p := P); omega
    · rw [Formula.realization_and, Set.mem_inter_iff, degFormulaO_realization, Set.mem_ofPred_eq,
        Formula.realization_gtZeroO, Set.mem_ofPred_eq]
      refine ⟨Polynomial.degree_eq_natDegree hne, ?_⟩
      rw [haeval]; rw [hlc] at hsign; exact (key _ m).mp hsign

/-! ## Stratum B: realizability and the Stratum B formula -/

open scoped Matrix in
/-- The **realizability formula** for a family `𝒬`: the all-positive sign condition for
`𝒬_y` is realized over `R` iff all `𝒬_i ≠ 0` and (all `+` at `−∞`, or all `+` at `+∞`,
or the `C' = (∏𝒬)'` matrix condition). Mirror of `realizabilityLocus_isSemialgebraicSetOver`. -/
noncomputable def realizabilityFormula (𝒬 : Fin s → Polynomial (MvPolynomial (Fin k) D)) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  (Formula.conjListO ((List.finRange s).map (fun i => neZeroPolyFormula (𝒬 i)))).and
    (((Formula.conjListO ((List.finRange s).map (fun i => signNegInftyFormula (𝒬 i)))).or
      (Formula.conjListO ((List.finRange s).map (fun i => signPosInftyFormula (𝒬 i))))).or
      (matrixFormula (∏ i, 𝒬 i).derivative 𝒬 ((signMatrixQ s)⁻¹)
        ((signEquiv s).symm (fun _ => SignType.pos))))

theorem realizabilityFormula_isQF (𝒬 : Fin s → Polynomial (MvPolynomial (Fin k) D)) :
    (realizabilityFormula 𝒬).IsQuantifierFree := by
  refine ⟨Formula.conjListO_isQF _ (fun Φ hΦ => ?_),
    ⟨Formula.conjListO_isQF _ (fun Φ hΦ => ?_), Formula.conjListO_isQF _ (fun Φ hΦ => ?_)⟩,
    matrixFormula_isQF _ _ _ _⟩ <;>
  · simp only [List.mem_map, List.mem_finRange, true_and] at hΦ
    obtain ⟨i, rfl⟩ := hΦ
    first
      | exact neZeroPolyFormula_isQF (𝒬 i)
      | exact signNegInftyFormula_isQF (𝒬 i)
      | exact signPosInftyFormula_isQF (𝒬 i)

open scoped Matrix in
theorem realizabilityFormula_realization (𝒬 : Fin s → Polynomial (MvPolynomial (Fin k) D))
    (hinj : Function.Injective (algebraMap D R)) :
    (realizabilityFormula 𝒬).realization (C := R) =
      {y : Fin k → R | ∃ x : R, ∀ i,
        0 < ((𝒬 i).map (MvPolynomial.aeval y).toRingHom).eval x} := by
  classical
  have hCeq : ∀ (y : Fin k → R),
      (∏ i, (𝒬 i).map (MvPolynomial.aeval y).toRingHom).derivative
        = ((∏ i, 𝒬 i).derivative).map (MvPolynomial.aeval y).toRingHom := fun y => by
    rw [← Polynomial.map_prod, Polynomial.derivative_map]
  rw [realizabilityFormula, Formula.realization_and, Formula.realization_or, Formula.realization_or,
    Formula.realization_conjListO, Formula.realization_conjListO, Formula.realization_conjListO,
    matrixFormula_realization _ _ _ _ hinj]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq, List.forall_mem_map,
    List.mem_finRange, neZeroPolyFormula_realization, signNegInftyFormula_realization,
    signPosInftyFormula_realization]
  rw [realizable_iff_disjuncts hasIVP_of_isRealClosed
    (fun i => (𝒬 i).map (MvPolynomial.aeval y).toRingHom), hCeq y]
  tauto

/-- Rewrite a `Finset`-membership universal as a `Fin`-indexed one over the `toList`
enumeration (local copy of `StratumB`'s private helper). -/
private theorem forall_mem_iff_forall_get {α : Type*} (Q : Finset α) (Φ : α → Prop) :
    (∀ q ∈ Q, Φ q) ↔ ∀ i : Fin Q.toList.length, Φ (Q.toList.get i) := by
  constructor
  · intro h i; exact h _ (Finset.mem_toList.mp (Q.toList.get_mem i))
  · intro h q hq
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hq)
    exact h i

/-- The **Stratum B formula** for a basic cell `(P, Q)`: `deg(splitLast P) = ⊥` (i.e.
`P_y ≡ 0`) conjoined with the realizability of the specialised family. Its realization
over any real closed field is the `P_y ≡ 0` stratum of the basic-cell projection. -/
noncomputable def stratumBFormula (P : MvPolynomial (Fin (k + 1)) D)
    (Q : Finset (MvPolynomial (Fin (k + 1)) D)) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  (degFormulaO (splitLast P) ⊥).and
    (realizabilityFormula (fun i => splitLast (Q.toList.get i)))

theorem stratumBFormula_isQF (P : MvPolynomial (Fin (k + 1)) D)
    (Q : Finset (MvPolynomial (Fin (k + 1)) D)) :
    (stratumBFormula P Q).IsQuantifierFree :=
  ⟨degFormulaO_isQF _ _, realizabilityFormula_isQF _⟩

theorem stratumBFormula_realization (hinj : Function.Injective (algebraMap D R))
    (P : MvPolynomial (Fin (k + 1)) D) (Q : Finset (MvPolynomial (Fin (k + 1)) D)) :
    (stratumBFormula P Q).realization (C := R) =
      {y : Fin k → R | (splitLast P).map (MvPolynomial.aeval y).toRingHom = 0 ∧
        ∃ x, ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x} := by
  rw [stratumBFormula, Formula.realization_and, degFormulaO_realization,
    realizabilityFormula_realization _ hinj]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  refine and_congr Polynomial.degree_eq_bot (exists_congr (fun x => ?_))
  exact (forall_mem_iff_forall_get Q
    (fun q => 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x)).symm

/-! ## The basic-cell projection formula -/

/-- The **basic-cell projection formula**: `stratumAFormula ∨ stratumBFormula`. Its
realization over any real closed field is `Fin.init '' basicCell(P, Q)` — the
formula-level counterpart of `basicCellProjection_of_strata`. -/
noncomputable def basicCellProjFormula (P : MvPolynomial (Fin (k + 1)) D)
    (Q : Finset (MvPolynomial (Fin (k + 1)) D)) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  (stratumAFormula P Q).or (stratumBFormula P Q)

theorem basicCellProjFormula_isQF (P : MvPolynomial (Fin (k + 1)) D)
    (Q : Finset (MvPolynomial (Fin (k + 1)) D)) :
    (basicCellProjFormula P Q).IsQuantifierFree :=
  ⟨stratumAFormula_isQF P Q, stratumBFormula_isQF P Q⟩

theorem basicCellProjFormula_realization (hinj : Function.Injective (algebraMap D R))
    (P : MvPolynomial (Fin (k + 1)) D) (Q : Finset (MvPolynomial (Fin (k + 1)) D)) :
    (basicCellProjFormula P Q).realization (C := R) =
      Fin.init '' {x : Fin (k + 1) → R |
        MvPolynomial.aeval x P = 0 ∧ ∀ q ∈ Q, MvPolynomial.aeval x q > 0} := by
  rw [basicCellProjFormula, Formula.realization_or, stratumAFormula_realization hinj,
    stratumBFormula_realization hinj, ← cellProjSplit_strata, cellProjection_eq_split]

/-! ## Field-uniform disjunctive normal form

Given a quantifier-free formula `Ψ` over coefficient field `F`, we extract a list of
basic cells `(P, Q)` (data, independent of the realization field) whose union, realized
over any ordered `F`-algebra `E`, is `Ψ`'s realization. Because the cells are syntactic,
the *same* list works over `F` and over any extension — exactly the uniformity
`huinitproj` needs. The construction is a signed recursion (`cellsOfSigned b` returns the
DNF of `Ψ` if `b = false`, of `¬Ψ` if `b = true`), with the sum-of-squares cell merge of
`IsBasicSemialgebraicSetOver.inter` packaged as `cellMerge`. -/

section DNF

variable {n : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {E : Type*} [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra F E]

open MvPolynomial

/-- A basic cell `(P, Q)` over coefficient field `F`, realized over an `F`-algebra `E`. -/
def cellSet (c : MvPolynomial (Fin n) F × Finset (MvPolynomial (Fin n) F)) : Set (Fin n → E) :=
  {z | aeval z c.1 = 0 ∧ ∀ q ∈ c.2, aeval z q > 0}

/-- Union of a list of basic cells, realized over `E`. -/
def cellsUnion (cells : List (MvPolynomial (Fin n) F × Finset (MvPolynomial (Fin n) F))) :
    Set (Fin n → E) :=
  {z | ∃ c ∈ cells, z ∈ (cellSet c : Set (Fin n → E))}

omit [IsStrictOrderedRing F] in
/-- Intersecting two basic cells: combine the equalities by sum of squares
(`P₁² + P₂² = 0 ↔ P₁ = 0 ∧ P₂ = 0` over an ordered field) and union the positivity sets. -/
theorem cellMerge (P₁ : MvPolynomial (Fin n) F) (Q₁ : Finset (MvPolynomial (Fin n) F))
    (P₂ : MvPolynomial (Fin n) F) (Q₂ : Finset (MvPolynomial (Fin n) F)) :
    (cellSet (P₁ ^ 2 + P₂ ^ 2, Q₁ ∪ Q₂) : Set (Fin n → E)) =
      cellSet (P₁, Q₁) ∩ cellSet (P₂, Q₂) := by
  classical
  ext z
  simp only [cellSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_union, map_add, map_pow]
  constructor
  · rintro ⟨hsum, hQ⟩
    have hP₁ : (aeval z P₁ : E) ^ 2 = 0 := by
      nlinarith [sq_nonneg (aeval z P₁ : E), sq_nonneg (aeval z P₂ : E)]
    have hP₂ : (aeval z P₂ : E) ^ 2 = 0 := by
      nlinarith [sq_nonneg (aeval z P₁ : E), sq_nonneg (aeval z P₂ : E)]
    exact ⟨⟨sq_eq_zero_iff.mp hP₁, fun q hq => hQ q (Or.inl hq)⟩,
           sq_eq_zero_iff.mp hP₂, fun q hq => hQ q (Or.inr hq)⟩
  · rintro ⟨⟨hp₁, hQ₁⟩, hp₂, hQ₂⟩
    refine ⟨by rw [hp₁, hp₂]; ring, ?_⟩
    rintro q (hq | hq); exacts [hQ₁ q hq, hQ₂ q hq]

omit [LinearOrder F] [IsStrictOrderedRing F] [IsStrictOrderedRing E] in
theorem cellsUnion_append (l₁ l₂ : List (MvPolynomial (Fin n) F × Finset (MvPolynomial (Fin n) F))) :
    (cellsUnion (l₁ ++ l₂) : Set (Fin n → E)) = cellsUnion l₁ ∪ cellsUnion l₂ := by
  ext z
  simp only [cellsUnion, Set.mem_ofPred_eq, Set.mem_union, List.mem_append, or_and_right, exists_or]

/-- Merge two cell-lists (cartesian product, intersecting each pair via sum of squares). -/
noncomputable def mergeCells
    (l₁ l₂ : List (MvPolynomial (Fin n) F × Finset (MvPolynomial (Fin n) F))) :
    List (MvPolynomial (Fin n) F × Finset (MvPolynomial (Fin n) F)) :=
  l₁.flatMap (fun c₁ => l₂.map (fun c₂ => (c₁.1 ^ 2 + c₂.1 ^ 2, c₁.2 ∪ c₂.2)))

omit [IsStrictOrderedRing F] in
theorem cellsUnion_merge
    (l₁ l₂ : List (MvPolynomial (Fin n) F × Finset (MvPolynomial (Fin n) F))) :
    (cellsUnion (mergeCells l₁ l₂) : Set (Fin n → E)) = cellsUnion l₁ ∩ cellsUnion l₂ := by
  ext z
  simp only [cellsUnion, mergeCells, Set.mem_ofPred_eq, Set.mem_inter_iff, List.mem_flatMap,
    List.mem_map]
  constructor
  · rintro ⟨c, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, hz⟩
    rw [cellMerge] at hz
    exact ⟨⟨c₁, hc₁, hz.1⟩, ⟨c₂, hc₂, hz.2⟩⟩
  · rintro ⟨⟨c₁, hc₁, hz₁⟩, ⟨c₂, hc₂, hz₂⟩⟩
    exact ⟨_, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, by rw [cellMerge]; exact ⟨hz₁, hz₂⟩⟩

/-- Negate a comparison relation: `¬(P R 0)` is `P (negRel R) 0`. -/
def negRel : OrderRel → OrderRel
  | .eq => .ne | .ne => .eq | .lt => .ge | .ge => .lt | .gt => .le | .le => .gt

/-- Basic cells whose union is `{z | P(z) R 0}` (one cell, except `≥`/`≤` split in two). -/
noncomputable def atomCells (P : MvPolynomial (Fin n) F) :
    OrderRel → List (MvPolynomial (Fin n) F × Finset (MvPolynomial (Fin n) F))
  | .eq => [(P, ∅)]
  | .gt => [(0, {P})]
  | .lt => [(0, {-P})]
  | .ne => [(0, {P ^ 2})]
  | .ge => [(P, ∅), (0, {P})]
  | .le => [(P, ∅), (0, {-P})]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem atomCells_realization (P : MvPolynomial (Fin n) F) (rel : OrderRel) :
    (cellsUnion (atomCells P rel) : Set (Fin n → E)) =
      (Formula.atom (⟨P, rel⟩ : OrderedFieldAtom (Fin n) F)).realization (C := E) := by
  cases rel <;> ext z <;>
    simp only [atomCells, cellsUnion, cellSet, Formula.realization, AtomRealization.interpret,
      List.mem_cons, List.not_mem_nil, Finset.mem_singleton, Finset.notMem_empty, Set.mem_ofPred_eq,
      map_zero, map_neg, map_pow, forall_eq, or_false, IsEmpty.forall_iff, implies_true,
      true_and, and_true, exists_eq_left, exists_eq_or_imp, neg_pos, sq_pos_iff, gt_iff_lt]
  · constructor
    · rintro (h | h); exacts [le_of_eq h, le_of_lt h]
    · intro h; exact (lt_or_eq_of_le h).symm
  · constructor
    · rintro (h | h); exacts [le_of_eq h.symm, le_of_lt h]
    · intro h; rcases lt_or_eq_of_le h with h | h; exacts [Or.inr h, Or.inl h.symm]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem atom_negRel_realization (P : MvPolynomial (Fin n) F) (rel : OrderRel) :
    (Formula.atom (⟨P, negRel rel⟩ : OrderedFieldAtom (Fin n) F)).realization (C := E) =
      ((Formula.atom (⟨P, rel⟩ : OrderedFieldAtom (Fin n) F)).realization (C := E))ᶜ := by
  cases rel <;> ext z <;>
    simp [negRel, Formula.realization, AtomRealization.interpret, Set.mem_compl_iff, not_lt, not_le]

/-- Signed DNF: `cellsOfSigned false Ψ` is the basic-cell decomposition of `Ψ`,
`cellsOfSigned true Ψ` that of `¬Ψ`. Negation flips the sign bit; `∧`/`∨` distribute
according to the bit (merge vs append). -/
noncomputable def cellsOfSigned :
    Bool → Formula (Fin n) (OrderedFieldAtom (Fin n) F) →
      List (MvPolynomial (Fin n) F × Finset (MvPolynomial (Fin n) F))
  | b, .atom a => atomCells a.poly (if b then negRel a.rel else a.rel)
  | b, .not Ψ => cellsOfSigned (!b) Ψ
  | b, .and Ψ₁ Ψ₂ =>
      if b then cellsOfSigned b Ψ₁ ++ cellsOfSigned b Ψ₂
      else mergeCells (cellsOfSigned b Ψ₁) (cellsOfSigned b Ψ₂)
  | b, .or Ψ₁ Ψ₂ =>
      if b then mergeCells (cellsOfSigned b Ψ₁) (cellsOfSigned b Ψ₂)
      else cellsOfSigned b Ψ₁ ++ cellsOfSigned b Ψ₂
  | b, .implies Ψ₁ Ψ₂ =>
      if b then mergeCells (cellsOfSigned false Ψ₁) (cellsOfSigned true Ψ₂)
      else cellsOfSigned true Ψ₁ ++ cellsOfSigned false Ψ₂
  | _, .exists_ _ _ => []
  | _, .forall_ _ _ => []

omit [IsStrictOrderedRing F] in
theorem cellsOfSigned_realization (Ψ : Formula (Fin n) (OrderedFieldAtom (Fin n) F)) :
    ∀ (b : Bool), Ψ.IsQuantifierFree →
      (cellsUnion (cellsOfSigned b Ψ) : Set (Fin n → E)) =
        cond b ((Ψ.realization (C := E))ᶜ) (Ψ.realization (C := E)) := by
  induction Ψ with
  | atom a =>
    intro b _; cases b
    · show (cellsUnion (atomCells a.poly a.rel) : Set _) = (Formula.atom a).realization (C := E)
      rw [atomCells_realization]
    · show (cellsUnion (atomCells a.poly (negRel a.rel)) : Set _)
        = ((Formula.atom a).realization (C := E))ᶜ
      rw [atomCells_realization, atom_negRel_realization]
  | not Ψ ih =>
    intro b hqf; rw [cellsOfSigned, ih (!b) hqf]
    cases b <;> simp [Formula.realization, compl_compl]
  | and Ψ₁ Ψ₂ ih₁ ih₂ =>
    intro b hqf; obtain ⟨h₁, h₂⟩ := hqf
    cases b <;>
      simp [cellsOfSigned, cellsUnion_append, cellsUnion_merge, ih₁ _ h₁, ih₂ _ h₂,
        Formula.realization, Set.compl_inter]
  | or Ψ₁ Ψ₂ ih₁ ih₂ =>
    intro b hqf; obtain ⟨h₁, h₂⟩ := hqf
    cases b <;>
      simp [cellsOfSigned, cellsUnion_append, cellsUnion_merge, ih₁ _ h₁, ih₂ _ h₂,
        Formula.realization, Set.compl_union]
  | implies Ψ₁ Ψ₂ ih₁ ih₂ =>
    intro b hqf; obtain ⟨h₁, h₂⟩ := hqf
    cases b <;>
      simp [cellsOfSigned, cellsUnion_append, cellsUnion_merge, ih₁ _ h₁, ih₂ _ h₂,
        Formula.realization, Set.compl_union, compl_compl]
  | exists_ x Ψ ih => intro b hqf; exact absurd hqf id
  | forall_ x Ψ ih => intro b hqf; exact absurd hqf id

omit [IsStrictOrderedRing F] in
/-- **Field-uniform DNF.** A quantifier-free formula's realization, over any ordered
`F`-algebra `E`, is the union of its basic cells `cellsOfSigned false Ψ` — a list of
cells fixed independently of `E`. -/
theorem dnf_realization (Ψ : Formula (Fin n) (OrderedFieldAtom (Fin n) F))
    (hqf : Ψ.IsQuantifierFree) :
    Ψ.realization (C := E) = cellsUnion (cellsOfSigned false Ψ) :=
  (cellsOfSigned_realization Ψ false hqf).symm

end DNF

/-! ## Assembly: the formula-level `Fin.init` projection (`huinitproj`)

Putting the pieces together: the `Fin.init` projection of a quantifier-free formula's
realization is, uniformly over the base field and any real closed extension, the
realization of the explicit quantifier-free `disjListO` of basic-cell projection formulas
over the DNF cells. This is `huinitproj` — the single remaining hypothesis of BPR
Theorem 2.80 (`Section2_5/Theorem_2_80.lean`). -/

section Assembly

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable {E : Type*} [Field E] [LinearOrder E] [IsStrictOrderedRing E] [IsRealClosed E] [Algebra R E]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The `Fin.init` image of a union of basic cells (over `E`) is the realization of the
`disjListO` of the per-cell basic-cell projection formulas. -/
theorem initImage_cellsUnion {m : ℕ} (hinj : Function.Injective (algebraMap R E))
    (cells : List (MvPolynomial (Fin (m + 1)) R × Finset (MvPolynomial (Fin (m + 1)) R))) :
    Fin.init '' (cellsUnion cells : Set (Fin (m + 1) → E)) =
      (Formula.disjListO (cells.map (fun c => basicCellProjFormula c.1 c.2))).realization
        (C := E) := by
  rw [Formula.realization_disjListO]
  ext y
  simp only [Set.mem_image, cellsUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨c, hc, hzc⟩, rfl⟩
    exact ⟨basicCellProjFormula c.1 c.2, List.mem_map.mpr ⟨c, hc, rfl⟩,
      by rw [basicCellProjFormula_realization hinj]; exact ⟨z, hzc, rfl⟩⟩
  · rintro ⟨Φ, hΦ, hyΦ⟩
    rw [List.mem_map] at hΦ
    obtain ⟨c, hc, rfl⟩ := hΦ
    rw [basicCellProjFormula_realization hinj] at hyΦ
    obtain ⟨z, hzc, rfl⟩ := hyΦ
    exact ⟨z, ⟨c, hc, hzc⟩, rfl⟩

variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
  [Algebra R R']

/-- **`huinitproj`: the formula-level `Fin.init` projection (BPR Theorem 2.76, uniform).**
For a quantifier-free formula `Ψ` over `Fin (m+1)`, the explicit quantifier-free formula
`Ψ'` (the `disjListO` of basic-cell projection formulas over `Ψ`'s DNF cells) realizes the
`Fin.init` projection of `Ψ` — *simultaneously* over the base real closed field `R` and
over every real closed extension `R'`. This is the single remaining ingredient of
`theorem_2_80_of_initProj`, completing the Tarski–Seidenberg transfer principle. -/
theorem initProjFormula_spec (m : ℕ)
    (Ψ : Formula (Fin (m + 1)) (OrderedFieldAtom (Fin (m + 1)) R)) (hqf : Ψ.IsQuantifierFree) :
    ∃ Ψ' : Formula (Fin m) (OrderedFieldAtom (Fin m) R), Ψ'.IsQuantifierFree ∧
      Fin.init '' Ψ.realization (C := R) = Ψ'.realization (C := R) ∧
      Fin.init '' Ψ.realization (C := R') = Ψ'.realization (C := R') := by
  refine ⟨Formula.disjListO ((cellsOfSigned false Ψ).map (fun c => basicCellProjFormula c.1 c.2)),
    ?_, ?_, ?_⟩
  · apply Formula.disjListO_isQF
    intro Φ hΦ; rw [List.mem_map] at hΦ; obtain ⟨c, _, rfl⟩ := hΦ
    exact basicCellProjFormula_isQF _ _
  · rw [dnf_realization Ψ hqf (E := R), initImage_cellsUnion (algebraMap R R).injective]
  · rw [dnf_realization Ψ hqf (E := R'), initImage_cellsUnion (algebraMap R R').injective]

end Assembly

end Azurite.BPR
