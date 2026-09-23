import Azurite.Rounding.Symmetric

/-!
# `RoundingTarget` and `SymmetricRoundingTarget` instances for `ℝ`

The image of `ℝ` in `EReal` is itself a `RoundingTarget`: every real `x` rounds to
itself in both directions. The tiebreaker is spec-irrelevant (since the floor and
ceiling coincide at every real `x`); we choose one that satisfies the
negation-symmetry condition `tiebreak_neg`, so `realSet` is also a
`SymmetricRoundingTarget`.
-/

namespace Azurite
namespace RoundingTarget

/-- The image of `ℝ` in `EReal`. -/
def realSet : Set EReal := {e | ∃ x : ℝ, (x : EReal) = e}

/-- Given `a : ↥realSet`, recover the underlying real. Noncomputable. -/
noncomputable def toReal (a : ↥realSet) : ℝ := Classical.choose a.property

/-- The defining spec of `toReal`: its real-cast equals the underlying value. -/
lemma toReal_spec (a : ↥realSet) : ((toReal a : ℝ) : EReal) = a.val :=
  Classical.choose_spec a.property

/-- If `a : ↥realSet` has value `((x : ℝ) : EReal)`, then `toReal a = x`. -/
lemma toReal_eq_of_val {a : ↥realSet} {x : ℝ} (h : ((x : ℝ) : EReal) = a.val) :
    toReal a = x := by
  have hsp := toReal_spec a
  have heq : ((toReal a : ℝ) : EReal) = ((x : ℝ) : EReal) := hsp.trans h.symm
  exact_mod_cast heq

private lemma realSet_neg_mem {s : EReal} (h : s ∈ realSet) : -s ∈ realSet := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨-x, by push_cast; rfl⟩

private lemma toReal_neg (a : ↥realSet) :
    toReal ⟨-a.val, realSet_neg_mem a.property⟩ = -toReal a := by
  apply toReal_eq_of_val
  rw [EReal.coe_neg, toReal_spec a]

/-- Tiebreaker for the real rounding target. Spec-irrelevant since the floor and
ceiling coincide at every real `x`; chosen so that `tiebreak_neg` holds (the
sum of the candidates' real values is preserved by joint negation up to a
sign), making `realSet` a `SymmetricRoundingTarget`. -/
noncomputable def realTiebreak (a b : ↥realSet) : ↥realSet :=
  if 0 ≤ toReal a + toReal b then a else b

noncomputable instance realRoundingTarget : RoundingTarget realSet where
  existsLeastGE x :=
    ⟨(x : EReal), ⟨⟨x, rfl⟩, le_refl _⟩, fun _ ⟨_, hs⟩ => hs⟩
  existsGreatestLE x :=
    ⟨(x : EReal), ⟨⟨x, rfl⟩, le_refl _⟩, fun _ ⟨_, hs⟩ => hs⟩
  tiebreak := realTiebreak
  tiebreak_mem a b := by
    unfold realTiebreak
    by_cases h : 0 ≤ toReal a + toReal b
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (ite_eq_right h)

noncomputable instance realSymmetricRoundingTarget : SymmetricRoundingTarget realSet where
  zero_mem := ⟨0, by push_cast; rfl⟩
  neg_mem := realSet_neg_mem
  tiebreak_neg a b hne := by
    show (realTiebreak ⟨-a.val, realSet_neg_mem a.property⟩
            ⟨-b.val, realSet_neg_mem b.property⟩).val =
        -(realTiebreak b a).val
    unfold realTiebreak
    rw [toReal_neg a, toReal_neg b]
    have hne' : toReal a ≠ -toReal b := by
      intro h
      apply hne
      rw [← toReal_spec a, ← toReal_spec b, h, EReal.coe_neg]
    rcases lt_trichotomy (toReal a + toReal b) 0 with hlt | heq | hgt
    · have hL : 0 ≤ -toReal a + -toReal b := by linarith
      have hR : ¬ 0 ≤ toReal b + toReal a := by linarith
      rw [ite_eq_left hL, ite_eq_right hR]
    · exfalso; apply hne'; linarith
    · have hL : ¬ 0 ≤ -toReal a + -toReal b := by linarith
      have hR : 0 ≤ toReal b + toReal a := by linarith
      rw [ite_eq_right hL, ite_eq_left hR]

end RoundingTarget
end Azurite
