import Azurite.BasuPollackRoy.Chapter2.Section2_3.FiberFormula
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_61
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_56
import Azurite.BasuPollackRoy.Chapter2.Section2_4.RealizationOverZeroSet

/-! # Parametrized Tarski queries (Theorem 2.76 kernel)

The Sturm–Tarski engine for the basic-cell projection of BPR Theorem 2.76. The
generalized bridge `sturmCount_eq_actual_varAt_diff_gen` (Theorem 2.62 machinery
with an *arbitrary* second Sturm argument `S` in place of `Ptil.derivative`)
computes, for each parameter `y`, the sign-change difference of `SRemS(P_y, S_y)`
combinatorially from a leaf path of `TRems Ptil S`.

Here we tie that to the **Tarski query**: when the specialised second argument
factors as `S_y = P_y' · Q` (the Sturm–Tarski shape of Theorem 2.61), the abstract
`sturmCount sigPat` equals the actual `TaQ(Q, P_y)`. Taking
`S = Ptil.derivative * 𝒬^α` (`familyPowMv`) for the constraint family `𝒬` makes
`Q = 𝒬_y^α`, yielding the parametrized Tarski queries `TaQ(𝒬_y^α, P_y)` that drive
Lemma 2.74's matrix condition (`stratumA_eq_matrix`).
-/

open _root_.Polynomial

namespace Azurite.BPR

/-! ### The multivariate family power `𝒬^α` -/

variable {k s : ℕ} {D : Type*} [CommRing D]

/-- Multivariate `𝒬^α = ∏ᵢ 𝒬ᵢ^{αᵢ}` over `D[Y][X]` (the coefficient-ring analogue
of `familyPow`). -/
noncomputable def familyPowMv (Q : Fin s → Polynomial (MvPolynomial (Fin k) D))
    (α : Fin s → ℕ) : Polynomial (MvPolynomial (Fin k) D) :=
  ∏ i, Q i ^ α i

section Map

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Algebra D R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Specialising `𝒬^α` at `y` commutes with `familyPow`. -/
theorem familyPowMv_map (Q : Fin s → Polynomial (MvPolynomial (Fin k) D))
    (α : Fin s → ℕ) (y : Fin k → R) :
    (familyPowMv Q α).map (MvPolynomial.aeval y).toRingHom
      = familyPow (fun i => (Q i).map (MvPolynomial.aeval y).toRingHom) α := by
  simp [familyPowMv, familyPow, Polynomial.map_prod, Polynomial.map_pow]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The Sturm–Tarski factorization `S_y = P_y' · 𝒬_y^α` for the second argument
`S = Ptil.derivative * 𝒬^α`. -/
theorem map_deriv_mul_familyPowMv (Ptil : Polynomial (MvPolynomial (Fin k) D))
    (Q : Fin s → Polynomial (MvPolynomial (Fin k) D)) (α : Fin s → ℕ) (y : Fin k → R) :
    (Ptil.derivative * familyPowMv Q α).map (MvPolynomial.aeval y).toRingHom
      = (Ptil.map (MvPolynomial.aeval y).toRingHom).derivative
        * familyPow (fun i => (Q i).map (MvPolynomial.aeval y).toRingHom) α := by
  rw [Polynomial.map_mul, Polynomial.derivative_map, familyPowMv_map]

end Map

/-! ### The parametrized Tarski-query bridge -/

variable [IsDomain D]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Algebra D R] [IsRealClosed R]

/-- **Parametrized Tarski-query bridge.** For a leaf path of `TRems Ptil S` at a
parameter `y` whose specialised second argument factors as
`S_y = P_y' · Qpoly` (the Sturm–Tarski shape), the abstract Sturm count
`sturmCount sigPat ((Ptil :: path).map natDegree)` equals the actual Tarski query
`TaQ(Qpoly, P_y)`, where `P_y = Ptil.map (aeval y)`.

Combining the generalized combinatorial bridge
`sturmCount_eq_actual_varAt_diff_gen` (count = `varAt(SRemS(P_y, S_y))` difference)
with BPR Theorem 2.61 (`varAt(SRemS(P, P'·Q))` difference = `TaQ(Q, P)`). The
boundary non-vanishing hypotheses of Theorem 2.61 hold because `P_y ≠ 0` (its
leading coefficient survives specialisation, by `hlc`). -/
theorem sturmCount_eq_tarskiQuery
    (Ptil S : Polynomial (MvPolynomial (Fin k) D))
    (path : List (Polynomial (MvPolynomial (Fin k) D)))
    (sigPat : List SignType)
    (h_path : path ∈ (TRems Ptil S).leafPaths)
    (h_sigPat : sigPat ∈ allSignPatterns (Ptil :: path).length)
    (y : Fin k → R)
    (h_leaf : y ∈ (leafFormula Ptil S path).realization (C := R))
    (h_sign : y ∈ (Formula.sturmLeafSignFormula (Ptil :: path) sigPat).realization (C := R))
    (hlc : MvPolynomial.aeval y Ptil.leadingCoeff ≠ 0)
    (Qpoly : R[X])
    (hSy : S.map (MvPolynomial.aeval y).toRingHom
      = (Ptil.map (MvPolynomial.aeval y).toRingHom).derivative * Qpoly) :
    (sturmCount sigPat ((Ptil :: path).map Polynomial.natDegree) : ℤ)
      = tarskiQuery Qpoly (Ptil.map (MvPolynomial.aeval y).toRingHom) := by
  have hPy : Ptil.map (MvPolynomial.aeval y).toRingHom ≠ 0 := by
    intro h
    apply hlc
    have hc := congrArg (fun p => Polynomial.coeff p Ptil.natDegree) h
    simpa [Polynomial.coeff_map] using hc
  have hgen := sturmCount_eq_actual_varAt_diff_gen Ptil S path sigPat h_path h_sigPat
    y h_leaf h_sign hlc
  simp only [hSy] at hgen
  rw [hgen, tarskiQuery_eq_tarskiQueryOn_negInf_posInf,
    ← theorem_2_61 hasIVP_of_isRealClosed (Ptil.map (MvPolynomial.aeval y).toRingHom) Qpoly hPy
      .negInf .posInf (by trivial)
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hPy))
      (leadingCoeff_ne_zero.mpr hPy)]

/-- **Family parametrized Tarski-query bridge.** Specialisation of
`sturmCount_eq_tarskiQuery` to `S = Ptil.derivative * 𝒬^α`: a leaf path of
`TRems Ptil (Ptil.derivative * 𝒬^α)` computes the parametrized Tarski query
`TaQ(𝒬_y^α, P_y)` of the constraint family `𝒬`. This is the per-leaf value
feeding Lemma 2.74's matrix `Mₛ⁻¹ · TaQ`. -/
theorem sturmCount_eq_tarskiQuery_family
    (Ptil : Polynomial (MvPolynomial (Fin k) D))
    (Q : Fin s → Polynomial (MvPolynomial (Fin k) D)) (α : Fin s → ℕ)
    (path : List (Polynomial (MvPolynomial (Fin k) D)))
    (sigPat : List SignType)
    (h_path : path ∈ (TRems Ptil (Ptil.derivative * familyPowMv Q α)).leafPaths)
    (h_sigPat : sigPat ∈ allSignPatterns (Ptil :: path).length)
    (y : Fin k → R)
    (h_leaf : y ∈ (leafFormula Ptil (Ptil.derivative * familyPowMv Q α) path).realization
                    (C := R))
    (h_sign : y ∈ (Formula.sturmLeafSignFormula (Ptil :: path) sigPat).realization (C := R))
    (hlc : MvPolynomial.aeval y Ptil.leadingCoeff ≠ 0) :
    (sturmCount sigPat ((Ptil :: path).map Polynomial.natDegree) : ℤ)
      = tarskiQuery (familyPow (fun i => (Q i).map (MvPolynomial.aeval y).toRingHom) α)
          (Ptil.map (MvPolynomial.aeval y).toRingHom) :=
  sturmCount_eq_tarskiQuery Ptil (Ptil.derivative * familyPowMv Q α) path sigPat
    h_path h_sigPat y h_leaf h_sign hlc _ (map_deriv_mul_familyPowMv Ptil Q α y)

/-! ### The parametrized-Tarski-query QF formula

For a fixed family `𝒬`, exponent `α`, and target value `c`, the formula
`tarskiFormula P_split 𝒬 α c` is the disjunction, over the leaf patterns whose
abstract Sturm count equals `c`, of the per-leaf degree/leaf/sign conditions. Its
realization is the locus `{y | P_y ≠ 0 ∧ TaQ(𝒬_y^α, P_y) = c}`. This is the
parametrized analogue of `fiberFormula_high`, with the `goodSignPattern` criterion
(`0 < sturmCount`) replaced by the equation `sturmCount = c`. -/

/-- Helper: `(l.map f).zip (l.map g) = l.map (fun a => (f a, g a))`. -/
private theorem zip_map_map_diag {α β γ : Type*}
    (l : List α) (f : α → β) (g : α → γ) :
    (l.map f).zip (l.map g) = l.map (fun a => (f a, g a)) := by
  induction l with
  | nil => rfl
  | cons head tail ih => simp [List.zip_cons_cons, ih]

/-- Leaf patterns whose abstract Sturm count hits a target value `c` — the
parametrized-Tarski-query analogue of `goodRootLeafPatterns` (filtered by
`sturmCount = c` instead of `0 < sturmCount`, and using the Sturm–Tarski second
argument `Ptil.derivative * 𝒬^α` instead of `Ptil.derivative`). -/
noncomputable def tarskiLeafPatterns
    (P_split : Polynomial (MvPolynomial (Fin k) D))
    (Q : Fin s → Polynomial (MvPolynomial (Fin k) D)) (α : Fin s → ℕ) (c : ℤ) :
    List (Polynomial (MvPolynomial (Fin k) D) ×
          List (Polynomial (MvPolynomial (Fin k) D)) × List SignType) :=
  (Tru_finite P_split).toFinset.toList.flatMap fun Ptil =>
    (TRems Ptil (Ptil.derivative * familyPowMv Q α)).leafPaths.flatMap fun path =>
      let degrees := (Ptil :: path).map Polynomial.natDegree
      ((allSignPatterns (Ptil :: path).length).filter
        (fun pat => decide (sturmCount pat degrees = c))).map
        (fun pat => (Ptil, path, pat))

theorem mem_tarskiLeafPatterns_iff
    {P_split : Polynomial (MvPolynomial (Fin k) D)}
    {Q : Fin s → Polynomial (MvPolynomial (Fin k) D)} {α : Fin s → ℕ} {c : ℤ}
    {Ptil : Polynomial (MvPolynomial (Fin k) D)}
    {path : List (Polynomial (MvPolynomial (Fin k) D))}
    {pat : List SignType} :
    (Ptil, path, pat) ∈ tarskiLeafPatterns P_split Q α c ↔
      Ptil ∈ Tru P_split ∧
      path ∈ (TRems Ptil (Ptil.derivative * familyPowMv Q α)).leafPaths ∧
      pat ∈ allSignPatterns (Ptil :: path).length ∧
      sturmCount pat ((Ptil :: path).map Polynomial.natDegree) = c := by
  simp only [tarskiLeafPatterns, List.mem_flatMap, List.mem_map,
    List.mem_filter, decide_eq_true_eq, Prod.mk.injEq,
    Finset.mem_toList, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨Ptil', hPtil'_mem, path', hpath'_mem, pat',
        ⟨hpat'_mem, hpat'_good⟩, hPtil_eq, hpath_eq, hpat_eq⟩
    subst hPtil_eq; subst hpath_eq; subst hpat_eq
    exact ⟨hPtil'_mem, hpath'_mem, hpat'_mem, hpat'_good⟩
  · rintro ⟨hPtil_mem, hpath_mem, hpat_mem, hpat_good⟩
    exact ⟨Ptil, hPtil_mem, path, hpath_mem, pat,
      ⟨hpat_mem, hpat_good⟩, rfl, rfl, rfl⟩

/-- The QF formula whose realization is the parametrized locus
`{y | P_y ≠ 0 ∧ TaQ(𝒬_y^α, P_y) = c}`: a disjunction over the leaf patterns whose
abstract Sturm count equals `c`. -/
noncomputable def tarskiFormula
    (P_split : Polynomial (MvPolynomial (Fin k) D))
    (Q : Fin s → Polynomial (MvPolynomial (Fin k) D)) (α : Fin s → ℕ) (c : ℤ) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  Formula.disjListO (
    (tarskiLeafPatterns P_split Q α c).map fun t =>
      (((degFormula P_split (↑t.1.natDegree)).and
          (leafFormula t.1 (t.1.derivative * familyPowMv Q α) t.2.1)).mapAtom
            FieldAtom.toOrderedFieldAtom).and
        (Formula.sturmLeafSignFormula (t.1 :: t.2.1) t.2.2)
  )

theorem tarskiFormula_isQF
    (P_split : Polynomial (MvPolynomial (Fin k) D))
    (Q : Fin s → Polynomial (MvPolynomial (Fin k) D)) (α : Fin s → ℕ) (c : ℤ) :
    (tarskiFormula P_split Q α c).IsQuantifierFree := by
  apply Formula.disjListO_isQF
  intro Φ hΦ
  simp only [List.mem_map] at hΦ
  obtain ⟨⟨Ptil, path, sigPat⟩, _, rfl⟩ := hΦ
  refine ⟨?_, Formula.sturmLeafSignFormula_isQF _ _⟩
  rw [Formula.mapAtom_isQF]
  exact ⟨degFormula_isQF _ _, leafFormula_isQF _ _ _⟩

/-! ### Correctness of `tarskiFormula` -/

section Realization

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Algebra D R] [IsRealClosed R]

/-- **Per-`y` characterization.** `P_y ≠ 0` with Tarski query `TaQ(𝒬_y^α, P_y) = c`
iff some leaf pattern of count `c` covers `y` (degree, leaf, and sign conditions).
The parametrized analogue of `fiber_nonempty_iff_some_good_disjunct`, with
`sturmCount_eq_tarskiQuery_family` supplying the Sturm–Tarski content. -/
theorem tarski_eq_iff_some_disjunct
    (P_split : Polynomial (MvPolynomial (Fin k) D))
    (Q : Fin s → Polynomial (MvPolynomial (Fin k) D)) (α : Fin s → ℕ) (c : ℤ)
    (hinj : Function.Injective (algebraMap D R))
    (y : Fin k → R) :
    (P_split.map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
      tarskiQuery (familyPow (fun i => (Q i).map (MvPolynomial.aeval y).toRingHom) α)
        (P_split.map (MvPolynomial.aeval y).toRingHom) = c) ↔
    ∃ (Ptil : Polynomial (MvPolynomial (Fin k) D))
      (path : List (Polynomial (MvPolynomial (Fin k) D)))
      (sigPat : List SignType),
      (Ptil, path, sigPat) ∈ tarskiLeafPatterns P_split Q α c ∧
      y ∈ (degFormula P_split (↑Ptil.natDegree)).realization (C := R) ∧
      y ∈ (leafFormula Ptil (Ptil.derivative * familyPowMv Q α) path).realization (C := R) ∧
      y ∈ (Formula.sturmLeafSignFormula (Ptil :: path) sigPat).realization (C := R) := by
  constructor
  · rintro ⟨hP_y_ne, hTaQ⟩
    have hsplit_ne : P_split ≠ 0 := fun h => hP_y_ne (by rw [h, Polynomial.map_zero])
    obtain ⟨Ptil, hPtil_mem, hPtil_deg⟩ :=
      Tru_covers_degrees hinj P_split hsplit_ne y hP_y_ne
    have h_deg : y ∈ (degFormula P_split (↑Ptil.natDegree)).realization (C := R) := by
      rw [realization_degFormula, Set.mem_ofPred_eq]; exact hPtil_deg
    have hPtil_ne : Ptil ≠ 0 := fun h => zero_not_mem_Tru _ hsplit_ne (h ▸ hPtil_mem)
    obtain ⟨hP_y_eq, hlc⟩ := degFormula_Tru_spec P_split Ptil hPtil_mem hPtil_ne y h_deg
    obtain ⟨path, h_path, h_leaf⟩ :=
      leafFormula_covering hinj Ptil (Ptil.derivative * familyPowMv Q α) y
    set sigPat : List SignType :=
      (Ptil :: path).map (fun p => SignType.sign (MvPolynomial.aeval y p.leadingCoeff))
      with sigPat_def
    have h_sigPat : sigPat ∈ allSignPatterns (Ptil :: path).length := by
      rw [mem_allSignPatterns_iff, sigPat_def, List.length_map]
    have h_sign : y ∈ (Formula.sturmLeafSignFormula (Ptil :: path) sigPat).realization (C := R) := by
      rw [Formula.realization_sturmLeafSignFormula]
      simp only [Set.mem_ofPred_eq]
      intro ps hps
      rw [sigPat_def, zip_map_map_diag, List.mem_map] at hps
      obtain ⟨p, _, rfl⟩ := hps
      rfl
    have h_count : sturmCount sigPat ((Ptil :: path).map Polynomial.natDegree) = c := by
      rw [sturmCount_eq_tarskiQuery_family Ptil Q α path sigPat h_path h_sigPat y h_leaf h_sign hlc,
          ← hP_y_eq]
      exact hTaQ
    exact ⟨Ptil, path, sigPat,
      mem_tarskiLeafPatterns_iff.mpr ⟨hPtil_mem, h_path, h_sigPat, h_count⟩,
      h_deg, h_leaf, h_sign⟩
  · rintro ⟨Ptil, path, sigPat, h_mem, h_deg, h_leaf, h_sign⟩
    obtain ⟨hPtil_mem, h_path, h_sigPat, h_count⟩ := mem_tarskiLeafPatterns_iff.mp h_mem
    have hsplit_ne : P_split ≠ 0 := by
      intro h; rw [h, Tru_empty_of_eq_zero] at hPtil_mem; exact hPtil_mem
    have hPtil_ne : Ptil ≠ 0 := fun h => zero_not_mem_Tru _ hsplit_ne (h ▸ hPtil_mem)
    obtain ⟨hP_y_eq, hlc⟩ := degFormula_Tru_spec P_split Ptil hPtil_mem hPtil_ne y h_deg
    have hPtily_ne : Ptil.map (MvPolynomial.aeval y).toRingHom ≠ 0 := by
      intro h; apply hlc
      have hc := congrArg (fun p => Polynomial.coeff p Ptil.natDegree) h
      simpa [Polynomial.coeff_map] using hc
    refine ⟨by rw [hP_y_eq]; exact hPtily_ne, ?_⟩
    rw [hP_y_eq,
        ← sturmCount_eq_tarskiQuery_family Ptil Q α path sigPat h_path h_sigPat y h_leaf h_sign hlc]
    exact h_count

/-- **Realization of `tarskiFormula`.** The QF formula `tarskiFormula P_split 𝒬 α c`
realizes to the parametrized locus `{y | P_y ≠ 0 ∧ TaQ(𝒬_y^α, P_y) = c}`. -/
theorem tarskiFormula_realization
    (P_split : Polynomial (MvPolynomial (Fin k) D))
    (Q : Fin s → Polynomial (MvPolynomial (Fin k) D)) (α : Fin s → ℕ) (c : ℤ)
    (hinj : Function.Injective (algebraMap D R)) :
    (tarskiFormula P_split Q α c).realization (C := R) =
      {y : Fin k → R | P_split.map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
        tarskiQuery (familyPow (fun i => (Q i).map (MvPolynomial.aeval y).toRingHom) α)
          (P_split.map (MvPolynomial.aeval y).toRingHom) = c} := by
  ext y
  rw [Set.mem_ofPred_eq, tarski_eq_iff_some_disjunct P_split Q α c hinj y]
  unfold tarskiFormula
  rw [Formula.realization_disjListO, Set.mem_ofPred_eq]
  simp only [List.mem_map]
  constructor
  · rintro ⟨Φ, ⟨⟨Ptil, path, sigPat⟩, h_mem, rfl⟩, hy_in⟩
    simp only [Formula.realization_and, Set.mem_inter_iff,
      Formula.realization_mapAtom_toOrderedFieldAtom] at hy_in
    obtain ⟨⟨h_deg, h_leaf⟩, h_sign⟩ := hy_in
    exact ⟨Ptil, path, sigPat, h_mem, h_deg, h_leaf, h_sign⟩
  · rintro ⟨Ptil, path, sigPat, h_mem, h_deg, h_leaf, h_sign⟩
    refine ⟨_, ⟨(Ptil, path, sigPat), h_mem, rfl⟩, ?_⟩
    simp only [Formula.realization_and, Set.mem_inter_iff,
      Formula.realization_mapAtom_toOrderedFieldAtom]
    exact ⟨⟨h_deg, h_leaf⟩, h_sign⟩

/-- **The parametrized Tarski locus is semialgebraic over `D`.** For a fixed family
`𝒬`, exponent `α`, and target value `c`, the set
`{y | P_y ≠ 0 ∧ TaQ(𝒬_y^α, P_y) = c}` is semialgebraic over `D` — it is the
realization of the quantifier-free `tarskiFormula`. This is the deep content of
Theorem 2.76's Stratum A: the Tarski queries vary semialgebraically with `y`. -/
theorem tarskiLocus_isSemialgebraicSetOver
    (P_split : Polynomial (MvPolynomial (Fin k) D))
    (Q : Fin s → Polynomial (MvPolynomial (Fin k) D)) (α : Fin s → ℕ) (c : ℤ)
    (hinj : Function.Injective (algebraMap D R)) :
    IsSemialgebraicSetOver D
      {y : Fin k → R | P_split.map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
        tarskiQuery (familyPow (fun i => (Q i).map (MvPolynomial.aeval y).toRingHom) α)
          (P_split.map (MvPolynomial.aeval y).toRingHom) = c} := by
  rw [← tarskiFormula_realization P_split Q α c hinj]
  exact qfRealizable_isSemialgebraicSetOver (tarskiFormula_isQF P_split Q α c)

end Realization

end Azurite.BPR
