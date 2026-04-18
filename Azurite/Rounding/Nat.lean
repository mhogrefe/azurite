import Azurite.Rounding.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# `ℕ` and `ℕ ∪ {-∞}` as rounding targets

The subset `natSet ⊆ EReal` consisting of (the images of) the naturals is *not* a
`RoundingTarget`: for any negative real `x`, no element of `natSet` is `≤ x`, so
the `existsGreatestLE` condition fails.

Adjoining `⊥ = -∞` restores that condition: `natBotSet = natSet ∪ {⊥}` is a
`RoundingTarget`. The tiebreaker prefers the even nat, analogous to the `ℤ` instance;
when one argument is `⊥` the choice is not spec-relevant.
-/

namespace Azurite
namespace RoundingTarget

/-- The image of `ℕ` in `EReal` (via `ℕ → ℝ → EReal`). -/
def natSet : Set EReal := {e | ∃ n : ℕ, ((n : ℝ) : EReal) = e}

/-- No element of `natSet` is `≤ -1`, so `{s ∈ natSet | s ≤ -1}` has no maximum. -/
theorem not_existsGreatestLE_natSet :
    ¬ ∃ M, IsGreatest {s | s ∈ natSet ∧ s ≤ ((-1 : ℝ) : EReal)} M := by
  rintro ⟨M, ⟨⟨n, hn⟩, hM_le⟩, _⟩
  have h1 : ((n : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) := hn ▸ hM_le
  have h2 : (n : ℝ) ≤ -1 := by exact_mod_cast h1
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- `natSet` cannot be equipped with a `RoundingTarget` structure: the
`existsGreatestLE` field has no witness at `x = -1`. -/
theorem not_nonempty_roundingTarget_natSet :
    ¬ Nonempty (RoundingTarget natSet) := by
  rintro ⟨inst⟩
  exact not_existsGreatestLE_natSet (inst.existsGreatestLE (-1))

/-- `natSet` together with `⊥ = -∞`: adjoining `⊥` restores `existsGreatestLE` for
negative reals. -/
def natBotSet : Set EReal := {e | e = ⊥ ∨ ∃ n : ℕ, ((n : ℝ) : EReal) = e}

open Classical in
/-- Recover the underlying nat, returning `0` on `⊥` (so the tiebreaker treats `⊥` as
even, which is acceptable since the spec is indifferent in that case). -/
noncomputable def natBotToNat (a : ↥natBotSet) : ℕ :=
  if h : ∃ n : ℕ, ((n : ℝ) : EReal) = a.val then h.choose else 0

/-- Parity-based tiebreaker for `natBotSet`: prefers the even nat. When either input
is `⊥` (where `natBotToNat` returns `0`) the choice is not spec-relevant. -/
noncomputable def natBotTiebreak (a b : ↥natBotSet) : ↥natBotSet :=
  if Even (natBotToNat a) then a else if Even (natBotToNat b) then b else a

noncomputable instance : RoundingTarget natBotSet where
  existsLeastGE x := by
    refine ⟨((⌈x⌉₊ : ℝ) : EReal), ⟨Or.inr ⟨⌈x⌉₊, rfl⟩, ?_⟩, ?_⟩
    · exact_mod_cast Nat.le_ceil x
    · rintro s ⟨hmem, hge⟩
      rcases hmem with rfl | ⟨n, rfl⟩
      · exact absurd hge (not_le_of_gt (EReal.bot_lt_coe x))
      · have : x ≤ (n : ℝ) := by exact_mod_cast hge
        exact_mod_cast Nat.ceil_le.mpr this
  existsGreatestLE x := by
    by_cases hx : 0 ≤ x
    · refine ⟨((⌊x⌋₊ : ℝ) : EReal), ⟨Or.inr ⟨⌊x⌋₊, rfl⟩, ?_⟩, ?_⟩
      · exact_mod_cast Nat.floor_le hx
      · rintro s ⟨hmem, hle⟩
        rcases hmem with rfl | ⟨n, rfl⟩
        · exact bot_le
        · have : (n : ℝ) ≤ x := by exact_mod_cast hle
          exact_mod_cast Nat.le_floor this
    · have hx : x < 0 := lt_of_not_ge hx
      refine ⟨⊥, ⟨Or.inl rfl, bot_le⟩, ?_⟩
      rintro s ⟨hmem, hle⟩
      rcases hmem with rfl | ⟨n, rfl⟩
      · exact le_refl ⊥
      · exfalso
        have h1 : (n : ℝ) ≤ x := by exact_mod_cast hle
        linarith [Nat.cast_nonneg (α := ℝ) n]
  tiebreak := natBotTiebreak
  tiebreak_mem a b := by
    unfold natBotTiebreak
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

end RoundingTarget
end Azurite
