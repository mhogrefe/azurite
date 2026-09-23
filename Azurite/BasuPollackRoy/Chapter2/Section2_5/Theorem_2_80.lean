import Azurite.BasuPollackRoy.Chapter2.Section2_5.Theorem_2_77
import Azurite.BasuPollackRoy.Chapter2.Section2_5.InitProjFormula
import Azurite.BasuPollackRoy.Chapter2.Section2_3.OrderedSentences

/-! # BPR Theorem 2.80: Tarski–Seidenberg transfer principle

**Theorem 2.80.** If `R ⊆ R'` are real closed fields and `Φ` is a sentence in the
language of ordered fields with coefficients in `R`, then `Φ` is true in `R` iff it
is true in `R'`.

## Structure of the formalization

BPR's proof has two ingredients:

1. (Theorem 2.77) a quantifier-free `Ψ` equivalent to `Φ` over `R`, **and** — "it
   follows from the proof of Theorem 2.76" — over `R'` as well (the *same* `Ψ`). This
   is **uniform quantifier elimination**: one QF formula equivalent to `Φ` over every
   real closed extension of `R`.
2. (the elementary step) a QF formula's truth transfers along `R ↪ R'`, because its
   atoms `c = 0`, `c > 0`, `c < 0`, … with `c ∈ R` have the same truth value after the
   order-preserving embedding.

This file proves ingredient (2) — `qf_realization_transfer`, the reusable core — and
the reduction `tarski_seidenberg_of_uniformQE`: given uniform QE (a single QF `Ψ`
equivalent to `Φ` over both `R` and `R'`) and that `Φ` is a sentence (its realization
is `∅` or `univ`), the transfer holds.

Ingredient (1) — *uniform* QE — is **not** yet available: the project's `theorem_2_77`
extracts a *field-specific* `Ψ` (via the existential `semialgebraic_isQFRealizableOver`)
and gives no proof that the same `Ψ` works over `R'`. Making it uniform requires the
projection theorem (2.76) to output a single field-uniform QF formula. So `Ψ` and the
two equivalences are taken as hypotheses here.
-/

open _root_.Polynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
variable [Algebra R R']

/-- A ring map between real closed fields is strictly monotone: `b - a ≥ 0` is a square,
hence stays a square — and so stays nonnegative — after the map. -/
theorem strictMono_algebraMap_RR' : StrictMono (algebraMap R R') := by
  have hinj : Function.Injective (algebraMap R R') := FaithfulSMul.algebraMap_injective R R'
  refine fun a b hab => lt_of_le_of_ne ?_ (fun h => (ne_of_lt hab) (hinj h))
  rw [← sub_nonneg, ← map_sub]
  obtain ⟨w, hw⟩ := IsRealClosed.nonneg_iff_isSquare.mp (sub_nonneg.mpr hab.le)
  rw [hw, map_mul]
  exact IsRealClosed.nonneg_iff_isSquare.mpr ⟨_, rfl⟩

/-- **Transfer of quantifier-free realizations.** For a quantifier-free formula `Ψ`
with coefficients in `R`, a point `y ∈ Rᵏ` realizes `Ψ` over `R` iff its image
`algebraMap R R' ∘ y` realizes `Ψ` over `R'`. The order-preserving embedding
`R ↪ R'` (`strictMono_algebraMap_RR'`) preserves the truth of every atom
`aeval y P {=,≠,<,>,≤,≥} 0`. -/
theorem qf_realization_transfer {k : ℕ}
    (Ψ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) (hqf : Ψ.IsQuantifierFree)
    (y : Fin k → R) :
    y ∈ Ψ.realization (C := R) ↔ (algebraMap R R' ∘ y) ∈ Ψ.realization (C := R') := by
  have hmono := strictMono_algebraMap_RR' (R := R) (R' := R')
  have hinj : Function.Injective (algebraMap R R') := hmono.injective
  have hz : (0 : R') = algebraMap R R' 0 := (map_zero _).symm
  have haeval : ∀ (P : MvPolynomial (Fin k) R),
      algebraMap R R' (MvPolynomial.aeval y P)
        = MvPolynomial.aeval (algebraMap R R' ∘ y) P := by
    intro P
    have key : (Algebra.ofId R R').comp (MvPolynomial.aeval y)
        = MvPolynomial.aeval (algebraMap R R' ∘ y) := by
      apply MvPolynomial.algHom_ext; intro i; simp [Algebra.ofId_apply]
    exact congrFun (congrArg (DFunLike.coe) key) P
  induction Ψ with
  | atom a =>
    obtain ⟨P, rel⟩ := a
    cases rel <;>
      simp only [Formula.realization, AtomRealization.interpret, Set.mem_ofPred_eq, ← haeval]
    · exact (map_eq_zero_iff _ hinj).symm
    · exact (map_eq_zero_iff _ hinj).not.symm
    · rw [hz]; exact hmono.lt_iff_lt.symm
    · rw [hz]; exact hmono.lt_iff_lt.symm
    · rw [hz]; exact hmono.le_iff_le.symm
    · rw [hz]; exact hmono.le_iff_le.symm
  | not Ψ ih => simp only [Formula.realization, Set.mem_compl_iff, ih hqf]
  | and Ψ₁ Ψ₂ ih₁ ih₂ =>
    simp only [Formula.realization, Set.mem_inter_iff, ih₁ hqf.1, ih₂ hqf.2]
  | or Ψ₁ Ψ₂ ih₁ ih₂ =>
    simp only [Formula.realization, Set.mem_union, ih₁ hqf.1, ih₂ hqf.2]
  | implies Ψ₁ Ψ₂ ih₁ ih₂ =>
    simp only [Formula.realization, Set.mem_union, Set.mem_compl_iff, ih₁ hqf.1, ih₂ hqf.2]
  | exists_ x Ψ ih => exact absurd hqf (by simp [Formula.IsQuantifierFree])
  | forall_ x Ψ ih => exact absurd hqf (by simp [Formula.IsQuantifierFree])

/-- **Tarski–Seidenberg, modulo uniform quantifier elimination.** Let `Φ` be a sentence
(its realization is `∅` or `univ` over each field — point-independent because all
variables are bound), and let `Ψ` be a quantifier-free formula equivalent to `Φ` over
both `R` and `R'` (*uniform* QE). Then `Φ` is true in `R` iff it is true in `R'`, where
"true" means the realization is nonempty.

The forward direction is immediate from `qf_realization_transfer`. The backward direction
also uses that a true sentence over `R'` has realization `univ`, so it contains the image
of any `R`-point, which transfers back. -/
theorem tarski_seidenberg_of_uniformQE {k : ℕ}
    (Φ Ψ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) (hqf : Ψ.IsQuantifierFree)
    (hR : Φ.realization (C := R) = Ψ.realization (C := R))
    (hR' : Φ.realization (C := R') = Ψ.realization (C := R'))
    (hsentR' : Φ.realization (C := R') = ∅ ∨ Φ.realization (C := R') = Set.univ) :
    (Φ.realization (C := R)).Nonempty ↔ (Φ.realization (C := R')).Nonempty := by
  constructor
  · rintro ⟨y, hy⟩
    rw [hR] at hy
    rw [hR']
    exact ⟨_, (qf_realization_transfer Ψ hqf y).mp hy⟩
  · rintro ⟨y', hy'⟩
    have hu : Φ.realization (C := R') = Set.univ :=
      hsentR'.resolve_left (fun h => by rw [h] at hy'; exact hy'.elim)
    have hmem : (algebraMap R R' ∘ (0 : Fin k → R)) ∈ Ψ.realization (C := R') := by
      rw [← hR', hu]; trivial
    exact ⟨0, hR ▸ (qf_realization_transfer Ψ hqf 0).mpr hmem⟩

/-! ### Uniform quantifier elimination, modulo a uniform projection formula

The remaining content of Theorem 2.80 is **uniform QE**: one quantifier-free `Ψ`
equivalent to `Φ` over both `R` and `R'`. By induction on `Φ` this reduces to a single
deep ingredient — a **uniform projection formula**: for a quantifier-free `Ψ` and a
coordinate `x`, a quantifier-free `Ψ'` whose realization is the projection
`{y | ∃ c, update y x c ∈ Ψ.realization}` over *both* `R` and `R'`. (This is the
formula-level form of `IsSemialgebraicSetOver.exists_update` / Theorem 2.76, with the
field-uniform realization that the underlying building-block formulas — `tarskiFormula`,
`fiberFormula_high`, `degFormula`, … — already enjoy.)
-/

omit [IsRealClosed R] [IsRealClosed R'] in
/-- **Uniform QE, modulo uniform projection.** Given a uniform projection formula
(`huproj`), every formula `Φ` (coefficients in `R`) has a quantifier-free `Ψ` equivalent
to it over both `R` and `R'`. Structural induction: atoms and the boolean connectives are
field-uniform automatically; `exists_` is the projection; `forall_` is `¬ ∃ ¬`. -/
theorem uniform_qe_of_proj {k : ℕ}
    (huproj : ∀ (Ψ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) (x : Fin k),
        Ψ.IsQuantifierFree →
        ∃ Ψ' : Formula (Fin k) (OrderedFieldAtom (Fin k) R), Ψ'.IsQuantifierFree ∧
          {y : Fin k → R | ∃ c, Function.update y x c ∈ Ψ.realization (C := R)}
            = Ψ'.realization (C := R) ∧
          {y : Fin k → R' | ∃ c, Function.update y x c ∈ Ψ.realization (C := R')}
            = Ψ'.realization (C := R'))
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) :
    ∃ Ψ : Formula (Fin k) (OrderedFieldAtom (Fin k) R), Ψ.IsQuantifierFree ∧
      Φ.realization (C := R) = Ψ.realization (C := R) ∧
      Φ.realization (C := R') = Ψ.realization (C := R') := by
  induction Φ with
  | atom a => exact ⟨.atom a, trivial, rfl, rfl⟩
  | not Φ ih =>
    obtain ⟨Ψ, hqf, hR, hR'⟩ := ih
    exact ⟨.not Ψ, hqf, by simp only [Formula.realization, hR],
      by simp only [Formula.realization, hR']⟩
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hq₁, hR₁, hR'₁⟩ := ih₁; obtain ⟨Ψ₂, hq₂, hR₂, hR'₂⟩ := ih₂
    exact ⟨.and Ψ₁ Ψ₂, ⟨hq₁, hq₂⟩, by simp only [Formula.realization, hR₁, hR₂],
      by simp only [Formula.realization, hR'₁, hR'₂]⟩
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hq₁, hR₁, hR'₁⟩ := ih₁; obtain ⟨Ψ₂, hq₂, hR₂, hR'₂⟩ := ih₂
    exact ⟨.or Ψ₁ Ψ₂, ⟨hq₁, hq₂⟩, by simp only [Formula.realization, hR₁, hR₂],
      by simp only [Formula.realization, hR'₁, hR'₂]⟩
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hq₁, hR₁, hR'₁⟩ := ih₁; obtain ⟨Ψ₂, hq₂, hR₂, hR'₂⟩ := ih₂
    exact ⟨.implies Ψ₁ Ψ₂, ⟨hq₁, hq₂⟩, by simp only [Formula.realization, hR₁, hR₂],
      by simp only [Formula.realization, hR'₁, hR'₂]⟩
  | exists_ x Φ ih =>
    obtain ⟨Ψ, hqf, hR, hR'⟩ := ih
    obtain ⟨Ψ', hqf', hpR, hpR'⟩ := huproj Ψ x hqf
    refine ⟨Ψ', hqf', ?_, ?_⟩
    · rw [← hpR]; ext y; simp only [Formula.realization, Set.mem_ofPred_eq, hR]
    · rw [← hpR']; ext y; simp only [Formula.realization, Set.mem_ofPred_eq, hR']
  | forall_ x Φ ih =>
    obtain ⟨Ψ, hqf, hR, hR'⟩ := ih
    obtain ⟨Ψ', hqf', hpR, hpR'⟩ := huproj (.not Ψ) x (by simp [Formula.IsQuantifierFree, hqf])
    refine ⟨.not Ψ', hqf', ?_, ?_⟩
    · rw [Formula.realization, ← hpR]; ext y
      simp only [Formula.realization, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, hR, not_not]
    · rw [Formula.realization, ← hpR']; ext y
      simp only [Formula.realization, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, hR', not_not]

/-- **BPR Theorem 2.80 (Tarski–Seidenberg), modulo the uniform projection formula.**
Given the uniform projection formula (`huproj`), a sentence `Φ` (coefficients in `R`,
realization `∅`/`univ` over `R'`) is true in `R` iff it is true in `R'`. -/
theorem theorem_2_80_of_proj {k : ℕ}
    (huproj : ∀ (Ψ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) (x : Fin k),
        Ψ.IsQuantifierFree →
        ∃ Ψ' : Formula (Fin k) (OrderedFieldAtom (Fin k) R), Ψ'.IsQuantifierFree ∧
          {y : Fin k → R | ∃ c, Function.update y x c ∈ Ψ.realization (C := R)}
            = Ψ'.realization (C := R) ∧
          {y : Fin k → R' | ∃ c, Function.update y x c ∈ Ψ.realization (C := R')}
            = Ψ'.realization (C := R'))
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R))
    (hsentR' : Φ.realization (C := R') = ∅ ∨ Φ.realization (C := R') = Set.univ) :
    (Φ.realization (C := R)).Nonempty ↔ (Φ.realization (C := R')).Nonempty := by
  obtain ⟨Ψ, hqf, hR, hR'⟩ := uniform_qe_of_proj huproj Φ
  exact tarski_seidenberg_of_uniformQE Φ Ψ hqf hR hR' hsentR'

/-! ### Reducing the projection formula to the `Fin.init` (basic-cell) projection

The cylindrical projection formula `projFormula Ψ x` (whose realization is
`{y | ∃ c, update y x c ∈ Ψ}`) is assembled from the `Fin.init`-projection formula
(`initProjFormula`, the formula-level Theorem 2.76) by the same swap/cylinder structure
as `IsSemialgebraicSetOver.exists_update`, using `Formula.rename` as the formula-level
`comap`. -/

section Rename

variable {σ τ : Type*} {D : Type*} [CommRing D]
variable {C : Type*} [Field C] [LinearOrder C] [IsStrictOrderedRing C] [Algebra D C]

/-- Realization of a renamed ordered-field formula is the preimage along `· ∘ f` (the
formula-level `comap`). Same statement as `Formula.rename_realization` but for the
`OrderedFieldAtom` atoms. -/
theorem Formula.rename_realization_ordered [DecidableEq σ] [DecidableEq τ]
    (f : σ → τ) (hf : Function.Injective f)
    (Φ : Formula σ (OrderedFieldAtom σ D)) :
    (Φ.rename f (OrderedFieldAtom.renameVars f)).realization (C := C) =
      (· ∘ f) ⁻¹' Φ.realization (C := C) := by
  induction Φ with
  | atom a =>
    ext y; obtain ⟨P, rel⟩ := a
    cases rel <;>
      simp [Formula.rename, OrderedFieldAtom.renameVars, Formula.realization,
        AtomRealization.interpret, MvPolynomial.aeval_rename, Function.comp_def]
  | not _ ih => simp [Formula.rename, Formula.realization, ih, Set.preimage_compl]
  | and _ _ ih₁ ih₂ => simp [Formula.rename, Formula.realization, ih₁, ih₂, Set.preimage_inter]
  | or _ _ ih₁ ih₂ => simp [Formula.rename, Formula.realization, ih₁, ih₂, Set.preimage_union]
  | implies _ _ ih₁ ih₂ =>
    simp [Formula.rename, Formula.realization, ih₁, ih₂, Set.preimage_union, Set.preimage_compl]
  | exists_ x _ ih =>
    ext y
    simp only [Formula.rename, Formula.realization, Set.mem_ofPred_eq, Set.mem_preimage, ih]
    constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, ?_⟩ <;>
    · convert hc using 1; ext i; simp [Function.update, hf.eq_iff]
  | forall_ x _ ih =>
    ext y
    simp only [Formula.rename, Formula.realization, Set.mem_ofPred_eq, Set.mem_preimage, ih]
    constructor <;> intro hc <;> intro c <;>
    · have := hc c; convert this using 1; ext i; simp [Function.update, hf.eq_iff]

end Rename

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] in
/-- The cylindrical projection `{y | ∃ c, update y x c ∈ V}` as two swaps and a
`Fin.init` image — the set identity behind `exists_update`, field-generic. -/
theorem exists_update_eq {k : ℕ} (x : Fin (k + 1)) (V : Set (Fin (k + 1) → R)) :
    {y : Fin (k + 1) → R | ∃ c, Function.update y x c ∈ V} =
    (fun g : Fin (k + 1) → R => g ∘ (Equiv.swap x (Fin.last k))) ⁻¹'
      ((fun g : Fin (k + 1) → R => g ∘ Fin.castSucc) ⁻¹'
        (Fin.init '' ((fun g : Fin (k + 1) → R => g ∘ (Equiv.swap x (Fin.last k))) ⁻¹' V))) := by
  set e : Fin (k + 1) ≃ Fin (k + 1) := Equiv.swap x (Fin.last k) with he
  have hupd : ∀ (w : Fin (k + 1) → R) (d : R),
      Function.update w (Fin.last k) d = Fin.snoc (Fin.init w) d := by
    intro w d; funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Function.update_self, Fin.snoc_last]
    · rw [Function.update_of_ne (Fin.castSucc_ne_last j), Fin.snoc_castSucc]; rfl
  have key : ∀ (y : Fin (k + 1) → R) (c : R),
      (Fin.snoc ((y ∘ ⇑e) ∘ Fin.castSucc) c) ∘ ⇑e = Function.update y x c := by
    intro y c
    have h1 : (y ∘ ⇑e) ∘ Fin.castSucc = Fin.init (y ∘ ⇑e) := rfl
    rw [h1, ← hupd (y ∘ ⇑e) c, Function.update_comp_equiv]
    have h2 : (y ∘ ⇑e) ∘ ⇑e = y := by funext i; simp [he, Equiv.swap_apply_self]
    have h3 : e.symm (Fin.last k) = x := by simp [he, Equiv.symm_swap, Equiv.swap_apply_right]
    rw [h2, h3]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Fin.init_image_eq_setOf_exists_snoc]
  exact exists_congr (fun c => by rw [key y c])

section TransferReduction

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
variable [Algebra R R']

omit [IsRealClosed R] [IsRealClosed R'] in
/-- **Uniform projection from the `Fin.init` projection.** Given `initProjFormula`
(`huinitproj`) — for a quantifier-free `Ψ` over `Fin (m+1)`, a quantifier-free `Ψ'` over
`Fin m` realizing `Fin.init '' Ψ` over both fields — one obtains the cylindrical
projection formula for any coordinate `x` (swap `x` to the last position with
`Formula.rename`, project, cylinder back). -/
theorem uniform_projection_of_init
    (huinitproj : ∀ (m : ℕ) (Ψ : Formula (Fin (m + 1)) (OrderedFieldAtom (Fin (m + 1)) R)),
        Ψ.IsQuantifierFree →
        ∃ Ψ' : Formula (Fin m) (OrderedFieldAtom (Fin m) R), Ψ'.IsQuantifierFree ∧
          Fin.init '' Ψ.realization (C := R) = Ψ'.realization (C := R) ∧
          Fin.init '' Ψ.realization (C := R') = Ψ'.realization (C := R')) :
    ∀ {k : ℕ} (Ψ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) (x : Fin k),
      Ψ.IsQuantifierFree →
      ∃ Ψ' : Formula (Fin k) (OrderedFieldAtom (Fin k) R), Ψ'.IsQuantifierFree ∧
        {y : Fin k → R | ∃ c, Function.update y x c ∈ Ψ.realization (C := R)}
          = Ψ'.realization (C := R) ∧
        {y : Fin k → R' | ∃ c, Function.update y x c ∈ Ψ.realization (C := R')}
          = Ψ'.realization (C := R') := by
  intro k
  cases k with
  | zero => exact fun Ψ x => x.elim0
  | succ m =>
    intro Ψ x hqf
    set e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap x (Fin.last m)
    obtain ⟨Ψ', hqf', hpR, hpR'⟩ :=
      huinitproj m (Ψ.rename e (OrderedFieldAtom.renameVars e)) (Formula.rename_isQF _ _ _ hqf)
    refine ⟨(Ψ'.rename Fin.castSucc (OrderedFieldAtom.renameVars Fin.castSucc)).rename e
        (OrderedFieldAtom.renameVars e),
      Formula.rename_isQF _ _ _ (Formula.rename_isQF _ _ _ hqf'), ?_, ?_⟩
    · rw [Formula.rename_realization_ordered e e.injective,
          Formula.rename_realization_ordered Fin.castSucc (Fin.castSucc_injective m),
          ← hpR, Formula.rename_realization_ordered e e.injective]
      exact exists_update_eq x (Ψ.realization (C := R))
    · rw [Formula.rename_realization_ordered e e.injective,
          Formula.rename_realization_ordered Fin.castSucc (Fin.castSucc_injective m),
          ← hpR', Formula.rename_realization_ordered e e.injective]
      exact exists_update_eq x (Ψ.realization (C := R'))

/-- **BPR Theorem 2.80, modulo the formula-level `Fin.init` projection (Theorem 2.76).**
Given `huinitproj` — the quantifier-free `Fin.init`-projection formula, field-uniform over
`R` and `R'` — a sentence `Φ` (coefficients in `R`) is true in `R` iff in `R'`. This
isolates the *entire* remaining content of Tarski–Seidenberg into a single ingredient:
the formula-level projection theorem. -/
theorem theorem_2_80_of_initProj {k : ℕ}
    (huinitproj : ∀ (m : ℕ) (Ψ : Formula (Fin (m + 1)) (OrderedFieldAtom (Fin (m + 1)) R)),
        Ψ.IsQuantifierFree →
        ∃ Ψ' : Formula (Fin m) (OrderedFieldAtom (Fin m) R), Ψ'.IsQuantifierFree ∧
          Fin.init '' Ψ.realization (C := R) = Ψ'.realization (C := R) ∧
          Fin.init '' Ψ.realization (C := R') = Ψ'.realization (C := R'))
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R))
    (hsentR' : Φ.realization (C := R') = ∅ ∨ Φ.realization (C := R') = Set.univ) :
    (Φ.realization (C := R)).Nonempty ↔ (Φ.realization (C := R')).Nonempty :=
  theorem_2_80_of_proj (fun Ψ x hqf => uniform_projection_of_init huinitproj Ψ x hqf) Φ hsentR'

/-- **BPR Theorem 2.80 (Tarski–Seidenberg transfer principle).** Let `R ⊆ R'` be real
closed fields and let `Φ` be a *sentence* in the language of ordered fields with
coefficients in `R` — a formula with no free variables (`isSentence Φ`). Then `Φ` is true
in `R` if and only if it is true in `R'`.

Truth is `Formula.IsTrue` (the realization is all of the space); for a sentence this is its
genuine truth value, since a sentence's realization is `∅` (false) or everything (true).
The formula-level `Fin.init` projection `initProjFormula_spec` (BPR Theorem 2.76,
field-uniform) discharges the last hypothesis of `theorem_2_80_of_initProj`, so the
principle is unconditional. -/
theorem theorem_2_80 {k : ℕ}
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) R)) (hΦ : Formula.isSentence Φ) :
    Φ.IsTrue (C := R) ↔ Φ.IsTrue (C := R') := by
  rw [Formula.isTrue_iff_nonempty_of_isSentence Φ hΦ,
    Formula.isTrue_iff_nonempty_of_isSentence Φ hΦ]
  exact theorem_2_80_of_initProj (fun m Ψ hqf => initProjFormula_spec m Ψ hqf) Φ
    (Formula.sentence_trivial_realization_ordered Φ hΦ)

end TransferReduction

end Azurite.BPR
