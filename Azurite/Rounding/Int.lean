import Azurite.Rounding.Basic
import Mathlib.Algebra.Order.Floor.Defs

/-!
# `RoundingTarget` instance for the integers

The subset `intSet ⊆ EReal` consisting of (the images of) the integers is a
`RoundingTarget`: every real number rounds down to `⌊x⌋` and rounds up to `⌈x⌉`.

The tiebreaker prefers the even candidate when the two candidates have different
parities; when both are even or both are odd the choice is arbitrary (we return
the first).
-/

namespace Azurite
namespace RoundingTarget

/-- The image of `ℤ` in `EReal` (via `ℤ → ℝ → EReal`). -/
def intSet : Set EReal := {e | ∃ z : ℤ, ((z : ℝ) : EReal) = e}

/-- Given `a : ↥intSet`, recover the underlying integer. Noncomputable. -/
noncomputable def toInt (a : ↥intSet) : ℤ := Classical.choose a.property

/-- Tiebreaker for the integer rounding target: if exactly one of the two candidates
is even, return the even one; otherwise return the first. -/
noncomputable def intTiebreak (a b : ↥intSet) : ↥intSet :=
  if Even (toInt a) then a else if Even (toInt b) then b else a

noncomputable instance : RoundingTarget intSet where
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
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

end RoundingTarget
end Azurite
