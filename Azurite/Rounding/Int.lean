import Azurite.Rounding.Symmetric
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring

/-!
# `RoundingTarget` instance for the integers

The subset `intSet ⊆ EReal` consisting of (the images of) the integers is a
`RoundingTarget`: every real number rounds down to `⌊x⌋` and rounds up to `⌈x⌉`.

The tiebreaker prefers the even candidate when the two candidates have different
parities; when both are even or both are odd the choice is arbitrary (we return
the first).

Since `intSet` contains `0`, is closed under negation, and `intTiebreak` commutes
with negation on adjacent integers (which always have different parity), the
integers form a `SymmetricRoundingTarget`.
-/

namespace Azurite
namespace RoundingTarget

/-- The image of `ℤ` in `EReal` (via `ℤ → ℝ → EReal`). -/
def intSet : Set EReal := {e | ∃ z : ℤ, ((z : ℝ) : EReal) = e}

/-- Given `a : ↥intSet`, recover the underlying integer. Noncomputable. -/
noncomputable def toInt (a : ↥intSet) : ℤ := Classical.choose a.property

/-- Tiebreaker for the integer rounding target. The semantically relevant case is when
the two candidates have different parities: then the even one is returned. When both
have the same parity (the spec-irrelevant case for `(F, C) = (⌊x⌋, ⌈x⌉)`, since adjacent
integers have different parity), we fall back to choosing by absolute value, breaking
ties by returning the first argument. The latter rule is symmetric under joint negation
(modulo the involution fixed point `(z, -z)`, which is excluded by the `tiebreak_neg`
side condition `a.val ≠ -b.val`). -/
noncomputable def intTiebreak (a b : ↥intSet) : ↥intSet :=
  if Even (toInt a) ∧ ¬ Even (toInt b) then a
  else if Even (toInt b) ∧ ¬ Even (toInt a) then b
  else if (toInt a).natAbs < (toInt b).natAbs then a
  else if (toInt b).natAbs < (toInt a).natAbs then b
  else a

noncomputable instance intRoundingTarget : RoundingTarget intSet where
  existsLeastGE x := by
    refine ⟨((⌈x⌉ : ℝ) : EReal), ⟨⟨⌈x⌉, rfl⟩, ?_⟩, ?_⟩
    · exact_mod_cast Int.le_ceil x
    · rintro s ⟨⟨z, rfl⟩, hz⟩
      have : x ≤ (z : ℝ) := by exact_mod_cast hz
      exact_mod_cast Int.ceil_le.mpr this
  existsGreatestLE x := by
    refine ⟨((⌊x⌋ : ℝ) : EReal), ⟨⟨⌊x⌋, rfl⟩, ?_⟩, ?_⟩
    · exact_mod_cast Int.floor_le x
    · rintro s ⟨⟨z, rfl⟩, hz⟩
      have : (z : ℝ) ≤ x := by exact_mod_cast hz
      exact_mod_cast Int.le_floor.mpr this
  tiebreak := intTiebreak
  tiebreak_mem a b := by
    unfold intTiebreak
    split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The defining spec of `toInt`: its real-cast equals the underlying value. -/
lemma toInt_spec (a : ↥intSet) : ((toInt a : ℝ) : EReal) = a.val := by
  unfold toInt
  exact Classical.choose_spec a.property

/-- If `a : ↥intSet` has value `((z : ℝ) : EReal)`, then `toInt a = z`. -/
lemma toInt_eq_of_val {a : ↥intSet} {z : ℤ} (h : ((z : ℝ) : EReal) = a.val) :
    toInt a = z := by
  have hsp := toInt_spec a
  have heq : ((toInt a : ℝ) : EReal) = ((z : ℝ) : EReal) := hsp.trans h.symm
  exact_mod_cast heq

/-- The floor of `x : ℝ` in `intSet` is `⌊x⌋`. -/
lemma val_roundFloor_intSet (x : ℝ) :
    (roundFloor intSet x).val = ((⌊x⌋ : ℝ) : EReal) := by
  apply (isGreatest_roundFloor intSet x).unique
  refine ⟨⟨⟨⌊x⌋, rfl⟩, ?_⟩, ?_⟩
  · exact_mod_cast Int.floor_le x
  · rintro s ⟨⟨z, rfl⟩, hz⟩
    have : (z : ℝ) ≤ x := by exact_mod_cast hz
    exact_mod_cast Int.le_floor.mpr this

/-- The ceiling of `x : ℝ` in `intSet` is `⌈x⌉`. -/
lemma val_roundCeiling_intSet (x : ℝ) :
    (roundCeiling intSet x).val = ((⌈x⌉ : ℝ) : EReal) := by
  apply (isLeast_roundCeiling intSet x).unique
  refine ⟨⟨⟨⌈x⌉, rfl⟩, ?_⟩, ?_⟩
  · exact_mod_cast Int.le_ceil x
  · rintro s ⟨⟨z, rfl⟩, hz⟩
    have : x ≤ (z : ℝ) := by exact_mod_cast hz
    exact_mod_cast Int.ceil_le.mpr this

private lemma toInt_roundFloor (x : ℝ) : toInt (roundFloor intSet x) = ⌊x⌋ :=
  toInt_eq_of_val (val_roundFloor_intSet x).symm

private lemma toInt_roundCeiling (x : ℝ) : toInt (roundCeiling intSet x) = ⌈x⌉ :=
  toInt_eq_of_val (val_roundCeiling_intSet x).symm

private lemma intSet_neg_mem {s : EReal} (h : s ∈ intSet) : -s ∈ intSet := by
  obtain ⟨z, hz⟩ := h
  exact ⟨-z, by rw [Int.cast_neg, EReal.coe_neg, hz]⟩

/-- For `a : ↥intSet`, the underlying integer of the negated subtype. -/
private lemma toInt_neg (a : ↥intSet) :
    toInt ⟨-a.val, intSet_neg_mem a.property⟩ = -toInt a := by
  apply toInt_eq_of_val
  rw [Int.cast_neg, EReal.coe_neg, toInt_spec a]

private lemma val_eq_coe_toInt (a : ↥intSet) : a.val = ((toInt a : ℝ) : EReal) :=
  (toInt_spec a).symm

noncomputable instance intSymmetricRoundingTarget : SymmetricRoundingTarget intSet where
  zero_mem := ⟨0, by push_cast; rfl⟩
  neg_mem := intSet_neg_mem
  tiebreak_neg a b hne := by
    set za := toInt a with hza_def
    set zb := toInt b with hzb_def
    have hzne : za ≠ -zb := by
      intro h
      apply hne
      rw [val_eq_coe_toInt a, val_eq_coe_toInt b, ← hza_def, ← hzb_def, h,
          Int.cast_neg, EReal.coe_neg]
    show (intTiebreak ⟨-a.val, intSet_neg_mem a.property⟩
            ⟨-b.val, intSet_neg_mem b.property⟩).val =
        -(intTiebreak b a).val
    unfold intTiebreak
    rw [toInt_neg a, toInt_neg b, ← hza_def, ← hzb_def]
    simp only [even_neg, Int.natAbs_neg]
    -- Case split on the parity branches directly, then natAbs branches.
    by_cases h1 : Even za ∧ ¬ Even zb
    · -- LHS branch 1 fires (picks -a.val); RHS branch 2 fires (picks a, negated).
      have h2 : ¬ (Even zb ∧ ¬ Even za) := fun h => h.2 h1.1
      simp only [if_pos h1, if_neg h2]
    · by_cases h3 : Even zb ∧ ¬ Even za
      · -- LHS branch 2 fires (picks -b.val); RHS branch 1 fires (picks b, negated).
        simp only [if_neg h1, if_pos h3]
      · -- Same parity: fall through to natAbs comparison on both sides.
        simp only [if_neg h1, if_neg h3]
        by_cases h_lt : za.natAbs < zb.natAbs
        · have h_gt : ¬ zb.natAbs < za.natAbs :=
            fun h => absurd (h.trans h_lt) (lt_irrefl _)
          simp only [if_pos h_lt, if_neg h_gt]
        · by_cases h_gt : zb.natAbs < za.natAbs
          · simp only [if_neg h_lt, if_pos h_gt]
          · -- Equal natAbs: za = zb (since za = -zb is excluded by hzne).
            have h_abs_eq : za.natAbs = zb.natAbs := by omega
            have h_za_eq : za = zb := by
              rcases Int.natAbs_eq_natAbs_iff.mp h_abs_eq with heq | heq
              · exact heq
              · exact absurd heq hzne
            simp only [if_neg h_lt, if_neg h_gt]
            show (-a.val : EReal) = -b.val
            rw [val_eq_coe_toInt a, val_eq_coe_toInt b, ← hza_def, ← hzb_def, h_za_eq]

end RoundingTarget
end Azurite
