import Azurite.Rounding.Basic

/-!
# Trivial `RoundingTarget` instance for `ℝ`

The image of `ℝ` in `EReal` is itself a `RoundingTarget`: every real `x` rounds to
itself in both directions. The tiebreaker is irrelevant; we return the first argument.
-/

namespace Azurite
namespace RoundingTarget

/-- The image of `ℝ` in `EReal`. -/
def realSet : Set EReal := {e | ∃ x : ℝ, (x : EReal) = e}

noncomputable instance : RoundingTarget realSet where
  existsLeastGE x :=
    ⟨(x : EReal), ⟨⟨x, rfl⟩, le_refl _⟩, fun _ ⟨_, hs⟩ => hs⟩
  existsGreatestLE x :=
    ⟨(x : EReal), ⟨⟨x, rfl⟩, le_refl _⟩, fun _ ⟨_, hs⟩ => hs⟩
  tiebreak a _ := a
  tiebreak_mem _ _ := Or.inl rfl

end RoundingTarget
end Azurite
