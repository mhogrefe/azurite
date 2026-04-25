import Azurite.AzInt.ShiftRightRound
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Equiv.Add
import Azurite.AzNat.Equiv.ShiftRightRound
import Azurite.Rounding.NatBotInt

namespace Azurite
open RoundingTarget AzInt

/-- Helper: AzNat shiftRightRound correctness lifted to `intSet` via the bridge. -/
private lemma azInt_aux_round_intSet (z : AzInt) (m : RoundingMode) (sh : Nat) :
    (((z.abs.shiftRightRound m sh).1.toNat : ℝ) : EReal) =
      (round intSet m ((z.abs.toNat : ℝ) / ((2 : ℝ) ^ sh))).val := by
  set y : ℝ := (z.abs.toNat : ℝ) / ((2 : ℝ) ^ sh)
  have hy_nonneg : 0 ≤ y := nat_div_pow_nonneg z.abs.toNat sh
  have h1 : (((z.abs.shiftRightRound m sh).1.toNat : ℕ) : EReal) =
      (round natBotSet m y).val := AzNat.toNat_shiftRightRound z.abs m sh
  have hcast : (((z.abs.shiftRightRound m sh).1.toNat : ℕ) : EReal) =
      (((z.abs.shiftRightRound m sh).1.toNat : ℝ) : EReal) := by push_cast; rfl
  rw [← hcast, h1]
  exact val_round_natBotSet_eq_intSet m y hy_nonneg

private lemma mkNorm_false_toInt_real (a : AzNat) :
    (((mkNorm false a).toInt : ℝ) : EReal) = -((a.toNat : ℝ) : EReal) := by
  by_cases ha : a = 0
  · subst ha
    have h1 : (mkNorm false (0 : AzNat)).toInt = 0 := by
      unfold mkNorm
      simp only [↓reduceDIte]
      rfl
    rw [h1]
    show ((0 : Int) : ℝ) = -(((0 : AzNat).toNat : ℝ) : EReal)
    push_cast; simp
  · rw [AzInt.toInt_mkNorm_false a ha]
    push_cast; rfl

private lemma mkNorm_true_toInt_real (a : AzNat) :
    (((mkNorm true a).toInt : ℝ) : EReal) = ((a.toNat : ℝ) : EReal) := by
  rw [AzInt.toInt_mkNorm_true]
  push_cast; rfl

/-- **Correctness of `AzInt.shiftRightRound`.**

For any rounding mode and shift amount, the limb-level `shiftRightRound` on `AzInt`
agrees with the abstract `round` of `z.toInt / 2^sh` against the rounding target
`intSet ⊆ EReal`. -/
theorem AzInt.toInt_shiftRightRound (z : AzInt) (mode : RoundingMode) (sh : Nat) :
    ((((z.shiftRightRound mode sh).1).toInt : ℝ) : EReal) =
      (round intSet mode ((z.toInt : ℝ) / ((2 : ℝ) ^ sh))).val := by
  unfold AzInt.shiftRightRound
  set y : ℝ := (z.abs.toNat : ℝ) / ((2 : ℝ) ^ sh) with hy_def
  by_cases hs : z.sign = true
  · -- z.sign = true: x = y, mode' = mode.
    have hxy : ((z.toInt : ℝ) / ((2 : ℝ) ^ sh)) = y := by
      rw [hy_def]; congr 1
      unfold AzInt.toInt; rw [if_pos hs]; push_cast; rfl
    rw [hxy, hs]
    show (((mkNorm true (z.abs.shiftRightRound mode sh).1).toInt : ℝ) : EReal) =
         (round intSet mode y).val
    rw [mkNorm_true_toInt_real]
    rw [hy_def]
    exact azInt_aux_round_intSet z mode sh
  · -- z.sign = false: x = -y, mode' = -mode.
    have hs_false : z.sign = false := by cases h : z.sign <;> simp_all
    have hxy : ((z.toInt : ℝ) / ((2 : ℝ) ^ sh)) = -y := by
      rw [hy_def]
      have hzi : (z.toInt : ℝ) = -(z.abs.toNat : ℝ) := by
        unfold AzInt.toInt; rw [if_neg hs]; push_cast; rfl
      rw [hzi, neg_div]
    rw [hxy, hs_false]
    show (((mkNorm false (z.abs.shiftRightRound (-mode) sh).1).toInt : ℝ) : EReal) =
         (round intSet mode (-y)).val
    rw [round_neg intSet mode y]
    rw [mkNorm_false_toInt_real]
    rw [hy_def]
    rw [show -mode = (-mode : RoundingMode) from rfl]
    rw [← azInt_aux_round_intSet z (-mode) sh]

/-- `ofInt`-version of `AzInt.toInt_shiftRightRound`. -/
theorem AzInt.ofInt_toInt_shiftRightRound (i : Int) (mode : RoundingMode) (sh : Nat) :
    ((((((AzInt.ofInt i).shiftRightRound mode sh).1).toInt : ℝ) : EReal)) =
      (round intSet mode ((i : ℝ) / ((2 : ℝ) ^ sh))).val := by
  have h := AzInt.toInt_shiftRightRound (AzInt.ofInt i) mode sh
  rwa [AzInt.toInt_ofInt] at h

end Azurite
