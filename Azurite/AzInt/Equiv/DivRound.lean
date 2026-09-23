import Azurite.AzInt.DivRound
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Equiv.Add
import Azurite.AzNat.Equiv.DivRound
import Azurite.Rounding.NatBotInt

namespace Azurite
open RoundingTarget AzInt

/-- Helper: AzNat divRound correctness lifted to `intSet` via the bridge. -/
private lemma azInt_aux_divRound_intSet (a b : AzNat) (m : RoundingMode) (hb : 0 < b.toNat) :
    (((a.divRound b m).1.toNat : ℝ) : EReal) =
      (round intSet m ((a.toNat : ℝ) / (b.toNat : ℝ))).val := by
  set y : ℝ := (a.toNat : ℝ) / (b.toNat : ℝ)
  have hb_real : (0 : ℝ) < (b.toNat : ℝ) := by exact_mod_cast hb
  have hy_nonneg : 0 ≤ y :=
    div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hb_real)
  have h1 : (((a.divRound b m).1.toNat : ℕ) : EReal) =
      (round natBotSet m y).val := AzNat.toNat_divRound a b m hb
  have hcast : (((a.divRound b m).1.toNat : ℕ) : EReal) =
      (((a.divRound b m).1.toNat : ℝ) : EReal) := by push_cast; rfl
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

/-- Real-cast of `a.toInt` in terms of sign and absolute value. -/
private lemma toInt_real_eq (a : AzInt) :
    ((a.toInt : ℝ) = if a.sign then (a.abs.toNat : ℝ) else -(a.abs.toNat : ℝ)) := by
  unfold AzInt.toInt
  split_ifs <;> push_cast <;> rfl

/-- **Correctness of `AzInt.divRound`.**

For any rounding mode and nonzero divisor, the limb-level `divRound` on `AzInt`
agrees with the abstract `round` of `a.toInt / b.toInt` against the rounding target
`intSet ⊆ EReal`. -/
theorem AzInt.toInt_divRound (a b : AzInt) (mode : RoundingMode) (hb : 0 < b.abs.toNat) :
    ((((a.divRound b mode).1).toInt : ℝ) : EReal) =
      (round intSet mode ((a.toInt : ℝ) / (b.toInt : ℝ))).val := by
  unfold AzInt.divRound
  set y : ℝ := (a.abs.toNat : ℝ) / (b.abs.toNat : ℝ) with hy_def
  have hb_real : (0 : ℝ) < (b.abs.toNat : ℝ) := by exact_mod_cast hb
  have hb_ne : (b.abs.toNat : ℝ) ≠ 0 := ne_of_gt hb_real
  have h_aR := toInt_real_eq a
  have h_bR := toInt_real_eq b
  by_cases hsa : a.sign = true
  · by_cases hsb : b.sign = true
    · -- (T, T): same sign, mode unchanged
      have hsame : (a.sign == b.sign) = true := by rw [hsa, hsb]; rfl
      rw [hsame]
      show (((mkNorm true (a.abs.divRound b.abs mode).1).toInt : ℝ) : EReal) =
          (round intSet mode ((a.toInt : ℝ) / (b.toInt : ℝ))).val
      have hxy : ((a.toInt : ℝ) / (b.toInt : ℝ)) = y := by
        rw [h_aR, h_bR, hsa, hsb, hy_def]
        simp
      rw [hxy, mkNorm_true_toInt_real, hy_def]
      exact azInt_aux_divRound_intSet a.abs b.abs mode hb
    · -- (T, F): different sign, mode flipped
      have hsb_f : b.sign = false := by cases h : b.sign <;> simp_all
      have hsame_f : (a.sign == b.sign) = false := by rw [hsa, hsb_f]; rfl
      rw [hsame_f]
      show (((mkNorm false (a.abs.divRound b.abs (-mode)).1).toInt : ℝ) : EReal) =
          (round intSet mode ((a.toInt : ℝ) / (b.toInt : ℝ))).val
      have hxy : ((a.toInt : ℝ) / (b.toInt : ℝ)) = -y := by
        rw [h_aR, h_bR, hsa, hsb_f, hy_def]
        simp [div_neg]
      rw [hxy, round_neg intSet mode y, mkNorm_false_toInt_real, hy_def]
      have h := azInt_aux_divRound_intSet a.abs b.abs (-mode) hb
      rw [← h]
  · have hsa_f : a.sign = false := by cases h : a.sign <;> simp_all
    by_cases hsb : b.sign = true
    · -- (F, T): different sign, mode flipped
      have hsame_f : (a.sign == b.sign) = false := by rw [hsa_f, hsb]; rfl
      rw [hsame_f]
      show (((mkNorm false (a.abs.divRound b.abs (-mode)).1).toInt : ℝ) : EReal) =
          (round intSet mode ((a.toInt : ℝ) / (b.toInt : ℝ))).val
      have hxy : ((a.toInt : ℝ) / (b.toInt : ℝ)) = -y := by
        rw [h_aR, h_bR, hsa_f, hsb, hy_def]
        simp [neg_div]
      rw [hxy, round_neg intSet mode y, mkNorm_false_toInt_real, hy_def]
      have h := azInt_aux_divRound_intSet a.abs b.abs (-mode) hb
      rw [← h]
    · -- (F, F): same sign, mode unchanged
      have hsb_f : b.sign = false := by cases h : b.sign <;> simp_all
      have hsame : (a.sign == b.sign) = true := by rw [hsa_f, hsb_f]; rfl
      rw [hsame]
      show (((mkNorm true (a.abs.divRound b.abs mode).1).toInt : ℝ) : EReal) =
          (round intSet mode ((a.toInt : ℝ) / (b.toInt : ℝ))).val
      have hxy : ((a.toInt : ℝ) / (b.toInt : ℝ)) = y := by
        rw [h_aR, h_bR, hsa_f, hsb_f, hy_def]
        simp [neg_div_neg_eq]
      rw [hxy, mkNorm_true_toInt_real, hy_def]
      exact azInt_aux_divRound_intSet a.abs b.abs mode hb

/-- `ofInt`-version of `AzInt.toInt_divRound`. -/
theorem AzInt.ofInt_toInt_divRound (i j : Int) (mode : RoundingMode)
    (hj : 0 < (AzInt.ofInt j).abs.toNat) :
    ((((((AzInt.ofInt i).divRound (AzInt.ofInt j) mode).1).toInt : ℝ) : EReal)) =
      (round intSet mode ((i : ℝ) / (j : ℝ))).val := by
  have h := AzInt.toInt_divRound (AzInt.ofInt i) (AzInt.ofInt j) mode hj
  rwa [AzInt.toInt_ofInt, AzInt.toInt_ofInt] at h

/-! ### Ordering tag correctness -/

/-- Negation flips ordering: `compare (-x) (-y)` is `(compare x y).swap`. -/
private lemma compare_neg_neg_real (x y : ℝ) :
    compare (-x) (-y) = (compare x y).swap := by
  rcases lt_trichotomy x y with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr (neg_lt_neg h)]; rfl
  · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr (by rw [h])]; rfl
  · rw [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr (neg_lt_neg h)]; rfl

/-- **Ordering tag correctness for `AzInt.divRound`.**

The ordering in `(a.divRound b mode).2` records the relation between the rounded
value and the true real value `a.toInt / b.toInt`. -/
theorem AzInt.snd_divRound (a b : AzInt) (mode : RoundingMode) (hb : 0 < b.abs.toNat) :
    (a.divRound b mode).2 =
      compare (((a.divRound b mode).1.toInt : ℤ) : ℝ)
        ((a.toInt : ℝ) / (b.toInt : ℝ)) := by
  unfold AzInt.divRound
  simp only []
  have h_aR := toInt_real_eq a
  have h_bR := toInt_real_eq b
  by_cases hsa : a.sign = true
  · by_cases hsb : b.sign = true
    · -- (T, T): same sign, mode unchanged, ord unchanged
      have hsame : (a.sign == b.sign) = true := by rw [hsa, hsb]; rfl
      rw [hsame]
      simp only [ite_true]
      have h_az := AzNat.snd_divRound a.abs b.abs mode hb
      rw [h_az]
      have h_int : (((mkNorm true (a.abs.divRound b.abs mode).1).toInt : ℤ) : ℝ) =
          (((a.abs.divRound b.abs mode).1.toNat : ℕ) : ℝ) := by
        rw [AzInt.toInt_mkNorm_true]; push_cast; rfl
      have h_ratio : ((a.toInt : ℝ) / (b.toInt : ℝ)) =
          ((a.abs.toNat : ℝ) / (b.abs.toNat : ℝ)) := by
        rw [h_aR, h_bR, hsa, hsb]; simp
      rw [h_int, h_ratio]
    · -- (T, F): different sign, mode flipped, ord swapped
      have hsb_f : b.sign = false := by cases h : b.sign <;> simp_all
      have hsame_f : (a.sign == b.sign) = false := by rw [hsa, hsb_f]; rfl
      rw [hsame_f]
      simp only [Bool.false_eq_true, ite_false]
      have h_az := AzNat.snd_divRound a.abs b.abs (-mode) hb
      rw [h_az]
      have h_int : (((mkNorm false (a.abs.divRound b.abs (-mode)).1).toInt : ℤ) : ℝ) =
          -(((a.abs.divRound b.abs (-mode)).1.toNat : ℕ) : ℝ) := by
        by_cases hq : (a.abs.divRound b.abs (-mode)).1 = 0
        · rw [hq]
          have h0 : (mkNorm false (0 : AzNat)).toInt = 0 := by
            unfold mkNorm; simp only [↓reduceDIte]; rfl
          rw [h0]; push_cast; simp
        · rw [AzInt.toInt_mkNorm_false _ hq]; push_cast; rfl
      have h_ratio : ((a.toInt : ℝ) / (b.toInt : ℝ)) =
          -((a.abs.toNat : ℝ) / (b.abs.toNat : ℝ)) := by
        rw [h_aR, h_bR, hsa, hsb_f]; simp [div_neg]
      rw [h_int, h_ratio, compare_neg_neg_real]
  · have hsa_f : a.sign = false := by cases h : a.sign <;> simp_all
    by_cases hsb : b.sign = true
    · -- (F, T): different sign, mode flipped, ord swapped
      have hsame_f : (a.sign == b.sign) = false := by rw [hsa_f, hsb]; rfl
      rw [hsame_f]
      simp only [Bool.false_eq_true, ite_false]
      have h_az := AzNat.snd_divRound a.abs b.abs (-mode) hb
      rw [h_az]
      have h_int : (((mkNorm false (a.abs.divRound b.abs (-mode)).1).toInt : ℤ) : ℝ) =
          -(((a.abs.divRound b.abs (-mode)).1.toNat : ℕ) : ℝ) := by
        by_cases hq : (a.abs.divRound b.abs (-mode)).1 = 0
        · rw [hq]
          have h0 : (mkNorm false (0 : AzNat)).toInt = 0 := by
            unfold mkNorm; simp only [↓reduceDIte]; rfl
          rw [h0]; push_cast; simp
        · rw [AzInt.toInt_mkNorm_false _ hq]; push_cast; rfl
      have h_ratio : ((a.toInt : ℝ) / (b.toInt : ℝ)) =
          -((a.abs.toNat : ℝ) / (b.abs.toNat : ℝ)) := by
        rw [h_aR, h_bR, hsa_f, hsb]; simp [neg_div]
      rw [h_int, h_ratio, compare_neg_neg_real]
    · -- (F, F): same sign, mode unchanged, ord unchanged
      have hsb_f : b.sign = false := by cases h : b.sign <;> simp_all
      have hsame : (a.sign == b.sign) = true := by rw [hsa_f, hsb_f]; rfl
      rw [hsame]
      simp only [ite_true]
      have h_az := AzNat.snd_divRound a.abs b.abs mode hb
      rw [h_az]
      have h_int : (((mkNorm true (a.abs.divRound b.abs mode).1).toInt : ℤ) : ℝ) =
          (((a.abs.divRound b.abs mode).1.toNat : ℕ) : ℝ) := by
        rw [AzInt.toInt_mkNorm_true]; push_cast; rfl
      have h_ratio : ((a.toInt : ℝ) / (b.toInt : ℝ)) =
          ((a.abs.toNat : ℝ) / (b.abs.toNat : ℝ)) := by
        rw [h_aR, h_bR, hsa_f, hsb_f]; simp [neg_div_neg_eq]
      rw [h_int, h_ratio]

end Azurite
