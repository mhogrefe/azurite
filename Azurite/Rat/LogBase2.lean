import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Azurite.Nat.Compare

open Real

namespace Azurite.Rat

/-- Returns the floor of the base-2 logarithm of the absolute value of a rational number.
 -/
def floorLogBase2Abs (q : ℚ) : ℤ :=
  let exponent : ℤ := (Nat.log2 q.num.natAbs : ℤ) - (Nat.log2 q.den : ℤ)
  if Azurite.Nat.normalizedCompare q.num.natAbs q.den == Ordering.lt then
    exponent - 1
  else
    exponent

#guard floorLogBase2Abs (1/4294967297) == -33
#guard floorLogBase2Abs (1/2) == -1
#guard floorLogBase2Abs (1/3) == -2
#guard floorLogBase2Abs (1/4) == -2
#guard floorLogBase2Abs (1/5) == -3
#guard floorLogBase2Abs (1/6) == -3
#guard floorLogBase2Abs (1/7) == -3
#guard floorLogBase2Abs (1/8) == -3
#guard floorLogBase2Abs (1/9) == -4

#guard floorLogBase2Abs (-1) == 0
#guard floorLogBase2Abs (-100) == 6
#guard floorLogBase2Abs (-1000000000000) == 39
#guard floorLogBase2Abs (-4294967295) == 31
#guard floorLogBase2Abs (-4294967296) == 32
#guard floorLogBase2Abs (-4294967297) == 32
#guard floorLogBase2Abs (-22/7) == 1
#guard floorLogBase2Abs (-936851431250/1397) == 29
#guard floorLogBase2Abs (-1/1000000000000) == -40
#guard floorLogBase2Abs (-1/4294967295) == -32
#guard floorLogBase2Abs (-1/4294967296) == -32
#guard floorLogBase2Abs (-1/4294967297) == -33
#guard floorLogBase2Abs (-1/2) == -1
#guard floorLogBase2Abs (-1/3) == -2
#guard floorLogBase2Abs (-1/4) == -2
#guard floorLogBase2Abs (-1/5) == -3
#guard floorLogBase2Abs (-1/6) == -3
#guard floorLogBase2Abs (-1/7) == -3
#guard floorLogBase2Abs (-1/8) == -3
#guard floorLogBase2Abs (-1/9) == -4

/-- Returns the ceiling of the base-2 logarithm of the absolute value of a rational number.
 -/
def ceilingLogBase2Abs (q : ℚ) : ℤ :=
  let exponent : ℤ := (Nat.log2 q.num.natAbs : ℤ) - (Nat.log2 q.den : ℤ)
  if Azurite.Nat.normalizedCompare q.num.natAbs q.den == Ordering.gt then
    exponent + 1
  else
    exponent

#guard ceilingLogBase2Abs 1 == 0
#guard ceilingLogBase2Abs 100 == 7
#guard ceilingLogBase2Abs 1000000000000 == 40
#guard ceilingLogBase2Abs 4294967295 == 32
#guard ceilingLogBase2Abs 4294967296 == 32
#guard ceilingLogBase2Abs 4294967297 == 33
#guard ceilingLogBase2Abs (22/7) == 2
#guard ceilingLogBase2Abs (936851431250/1397) == 30
#guard ceilingLogBase2Abs (1/1000000000000) == -39
#guard ceilingLogBase2Abs (1/4294967295) == -31
#guard ceilingLogBase2Abs (1/4294967296) == -32
#guard ceilingLogBase2Abs (1/4294967297) == -32
#guard ceilingLogBase2Abs (1/2) == -1
#guard ceilingLogBase2Abs (1/3) == -1
#guard ceilingLogBase2Abs (1/4) == -2
#guard ceilingLogBase2Abs (1/5) == -2
#guard ceilingLogBase2Abs (1/6) == -2
#guard ceilingLogBase2Abs (1/7) == -2
#guard ceilingLogBase2Abs (1/8) == -3
#guard ceilingLogBase2Abs (1/9) == -3

#guard ceilingLogBase2Abs (-1) == 0
#guard ceilingLogBase2Abs (-100) == 7
#guard ceilingLogBase2Abs (-1000000000000) == 40
#guard ceilingLogBase2Abs (-4294967295) == 32
#guard ceilingLogBase2Abs (-4294967296) == 32
#guard ceilingLogBase2Abs (-4294967297) == 33
#guard ceilingLogBase2Abs (-22/7) == 2
#guard ceilingLogBase2Abs (-936851431250/1397) == 30
#guard ceilingLogBase2Abs (-1/1000000000000) == -39
#guard ceilingLogBase2Abs (-1/4294967295) == -31
#guard ceilingLogBase2Abs (-1/4294967296) == -32
#guard ceilingLogBase2Abs (-1/4294967297) == -32
#guard ceilingLogBase2Abs (-1/2) == -1
#guard ceilingLogBase2Abs (-1/3) == -1
#guard ceilingLogBase2Abs (-1/4) == -2
#guard ceilingLogBase2Abs (-1/5) == -2
#guard ceilingLogBase2Abs (-1/6) == -2
#guard ceilingLogBase2Abs (-1/7) == -2
#guard ceilingLogBase2Abs (-1/8) == -3
#guard ceilingLogBase2Abs (-1/9) == -3

lemma size_bounds (N : ℕ) (hN : N > 0) :
  ((Nat.size N - 1 : ℕ) : ℝ) ≤ logb 2 (N : ℝ) ∧ logb 2 (N : ℝ) < (Nat.size N : ℝ) := by
  have hl1 : 2 ^ (Nat.size N - 1) ≤ N := Nat.lt_size.mp (Nat.pred_lt (Nat.size_pos.mpr hN).ne')
  have hl2 : N < 2 ^ Nat.size N := Nat.size_le.mp (le_refl _)
  have h_base : (1 : ℝ) < 2 := by norm_num
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  constructor
  · have hcast1 : (2 : ℝ) ^ (Nat.size N - 1) ≤ (N : ℝ) := by exact_mod_cast hl1
    have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (Nat.size N - 1) := by positivity
    have hlog1_iff : logb 2 ((2 : ℝ) ^ (Nat.size N - 1)) ≤ logb 2 (N : ℝ) ↔ (2 : ℝ) ^ (Nat.size N - 1) ≤ (N : ℝ) :=
      logb_le_logb h_base h_pow_pos hN_pos
    have hlog1 : logb 2 ((2 : ℝ) ^ (Nat.size N - 1)) ≤ logb 2 (N : ℝ) := hlog1_iff.mpr hcast1
    have h_simp : logb 2 ((2 : ℝ) ^ (Nat.size N - 1)) = ((Nat.size N - 1 : ℕ) : ℝ) := by
      rw [logb_pow, logb_self_eq_one h_base, mul_one]
    rw [h_simp] at hlog1
    exact hlog1
  · have hcast2 : (N : ℝ) < (2 : ℝ) ^ Nat.size N := by exact_mod_cast hl2
    have hN_pow_pos : (0 : ℝ) < (2 : ℝ) ^ Nat.size N := by positivity
    have hlog2_iff : logb 2 (N : ℝ) < logb 2 ((2 : ℝ) ^ Nat.size N) ↔ (N : ℝ) < (2 : ℝ) ^ Nat.size N :=
      logb_lt_logb_iff h_base hN_pos hN_pow_pos
    have hlog2 : logb 2 (N : ℝ) < logb 2 ((2 : ℝ) ^ Nat.size N) := hlog2_iff.mpr hcast2
    have h_simp : logb 2 ((2 : ℝ) ^ Nat.size N) = (Nat.size N : ℝ) := by
      rw [logb_pow, logb_self_eq_one h_base, mul_one]
    rw [h_simp] at hlog2
    exact hlog2

lemma compare_rat_cast (a b : ℚ) : @compare ℚ Rat.linearOrder.toOrd a b = compare (a : ℝ) (b : ℝ) := by
  have hl : a < b ↔ (a : ℝ) < (b : ℝ) := by exact_mod_cast Iff.rfl
  have he : a = b ↔ (a : ℝ) = (b : ℝ) := by exact_mod_cast Iff.rfl
  have hg : b < a ↔ (b : ℝ) < (a : ℝ) := by exact_mod_cast Iff.rfl
  rcases lt_trichotomy a b with h1 | h2 | h3
  · have h1' : (a : ℝ) < (b : ℝ) := hl.mp h1
    have c1 : @compare _ Rat.linearOrder.toOrd a b = Ordering.lt := compare_lt_iff_lt.mpr h1
    have c2 : compare (a : ℝ) (b : ℝ) = Ordering.lt := compare_lt_iff_lt.mpr h1'
    rw [c1, c2]
  · have h2' : (a : ℝ) = (b : ℝ) := he.mp h2
    have c1 : @compare _ Rat.linearOrder.toOrd a b = Ordering.eq := compare_eq_iff_eq.mpr h2
    have c2 : compare (a : ℝ) (b : ℝ) = Ordering.eq := compare_eq_iff_eq.mpr h2'
    rw [c1, c2]
  · have h3' : (b : ℝ) < (a : ℝ) := hg.mp h3
    have c1 : @compare _ Rat.linearOrder.toOrd a b = Ordering.gt := compare_gt_iff_gt.mpr h3
    have c2 : compare (a : ℝ) (b : ℝ) = Ordering.gt := compare_gt_iff_gt.mpr h3'
    rw [c1, c2]

lemma normalizedCompare_eq_real (x y : ℕ) (hx : x > 0) (hy : y > 0) :
  Azurite.Nat.normalizedCompare x y = compare ((x : ℝ) / (2 ^ Nat.size x : ℝ)) ((y : ℝ) / (2 ^ Nat.size y : ℝ)) := by
  rw [Azurite.Nat.normalizedCompare_eq_rat x y hx hy]
  have h_compare := compare_rat_cast ((x : ℚ) / (2 ^ Nat.size x : ℚ)) ((y : ℚ) / (2 ^ Nat.size y : ℚ))
  rw [h_compare]
  push_cast
  rfl

lemma compare_to_logb_bounds_lt (N D : ℕ) (hN : N > 0) (hD : D > 0) (h_lt : Azurite.Nat.normalizedCompare N D == Ordering.lt) :
    logb 2 (N : ℝ) - logb 2 (D : ℝ) < (Nat.size N : ℝ) - (Nat.size D : ℝ) := by
  have h_comp := normalizedCompare_eq_real N D hN hD
  have h_base : (1 : ℝ) < 2 := by norm_num
  have h_pos_N : (0 : ℝ) < (N : ℝ) / 2 ^ Nat.size N := div_pos (Nat.cast_pos.mpr hN) (by positivity)
  have h_pos_D : (0 : ℝ) < (D : ℝ) / 2 ^ Nat.size D := div_pos (Nat.cast_pos.mpr hD) (by positivity)
  have h_log_N : logb 2 ((N : ℝ) / 2 ^ Nat.size N) = logb 2 (N : ℝ) - (Nat.size N : ℝ) := by
    rw [logb_div (Nat.cast_pos.mpr hN).ne' (by positivity), logb_pow, logb_self_eq_one h_base, mul_one]
  have h_log_D : logb 2 ((D : ℝ) / 2 ^ Nat.size D) = logb 2 (D : ℝ) - (Nat.size D : ℝ) := by
    rw [logb_div (Nat.cast_pos.mpr hD).ne' (by positivity), logb_pow, logb_self_eq_one h_base, mul_one]
  rw [beq_iff_eq] at h_lt
  have h1 : compare ((N : ℝ) / (2 ^ Nat.size N : ℝ)) ((D : ℝ) / (2 ^ Nat.size D : ℝ)) = Ordering.lt := by
    rw [← h_comp, h_lt]
  have h2 : (N : ℝ) / 2 ^ Nat.size N < (D : ℝ) / 2 ^ Nat.size D := compare_lt_iff_lt.mp h1
  have h3 : logb 2 ((N : ℝ) / 2 ^ Nat.size N) < logb 2 ((D : ℝ) / 2 ^ Nat.size D) := (logb_lt_logb_iff h_base h_pos_N h_pos_D).mpr h2
  rw [h_log_N, h_log_D] at h3
  linarith

lemma compare_to_logb_bounds_ge (N D : ℕ) (hN : N > 0) (hD : D > 0) (h_lt : ¬(Azurite.Nat.normalizedCompare N D == Ordering.lt)) :
    (Nat.size N : ℝ) - (Nat.size D : ℝ) ≤ logb 2 (N : ℝ) - logb 2 (D : ℝ) := by
  have h_comp := normalizedCompare_eq_real N D hN hD
  have h_base : (1 : ℝ) < 2 := by norm_num
  have h_pos_N : (0 : ℝ) < (N : ℝ) / 2 ^ Nat.size N := div_pos (Nat.cast_pos.mpr hN) (by positivity)
  have h_pos_D : (0 : ℝ) < (D : ℝ) / 2 ^ Nat.size D := div_pos (Nat.cast_pos.mpr hD) (by positivity)
  have h_log_N : logb 2 ((N : ℝ) / 2 ^ Nat.size N) = logb 2 (N : ℝ) - (Nat.size N : ℝ) := by
    rw [logb_div (Nat.cast_pos.mpr hN).ne' (by positivity), logb_pow, logb_self_eq_one h_base, mul_one]
  have h_log_D : logb 2 ((D : ℝ) / 2 ^ Nat.size D) = logb 2 (D : ℝ) - (Nat.size D : ℝ) := by
    rw [logb_div (Nat.cast_pos.mpr hD).ne' (by positivity), logb_pow, logb_self_eq_one h_base, mul_one]
  have h_lt_ne : Azurite.Nat.normalizedCompare N D ≠ Ordering.lt := by
    intro hc; apply h_lt; rw [hc]; rfl
  have h1 : compare ((N : ℝ) / (2 ^ Nat.size N : ℝ)) ((D : ℝ) / (2 ^ Nat.size D : ℝ)) ≠ Ordering.lt := by
    rw [← h_comp]; exact h_lt_ne
  have h2 : ¬((N : ℝ) / 2 ^ Nat.size N < (D : ℝ) / 2 ^ Nat.size D) := by
    intro hc; exact h1 (compare_lt_iff_lt.mpr hc)
  have h3 : (D : ℝ) / 2 ^ Nat.size D ≤ (N : ℝ) / 2 ^ Nat.size N := not_lt.mp h2
  have h4 : logb 2 ((D : ℝ) / 2 ^ Nat.size D) ≤ logb 2 ((N : ℝ) / 2 ^ Nat.size N) := (logb_le_logb h_base h_pos_D h_pos_N).mpr h3
  rw [h_log_N, h_log_D] at h4
  linarith

lemma floorLogBase2Abs_eq (q : ℚ) (hq : q ≠ 0) :
  floorLogBase2Abs q = ⌊logb 2 |(q : ℝ)|⌋ := by
  have hN : q.num.natAbs > 0 := by
    apply Int.natAbs_pos.mpr
    intro h_num
    have h_zero : q = 0 := by
      rw [← Rat.num_div_den q, h_num, Int.cast_zero, zero_div]
    exact hq h_zero
  have hD : q.den > 0 := q.den_pos
  
  have h_abs_q : |(q : ℝ)| = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
    have h1 : |(q.num : ℝ)| = (q.num.natAbs : ℝ) := by simp
    have h2 : |(q.den : ℝ)| = (q.den : ℝ) := by simp
    rw [Rat.cast_def, abs_div, h1, h2]
  
  have hN_pos : (q.num.natAbs : ℝ) > 0 := by exact_mod_cast hN
  have hD_pos : (q.den : ℝ) > 0 := by exact_mod_cast hD
  
  have h_log_div : logb 2 |(q : ℝ)| = logb 2 (q.num.natAbs : ℝ) - logb 2 (q.den : ℝ) := by
    rw [h_abs_q, logb_div hN_pos.ne' hD_pos.ne']
  
  have h_exponent : (floorLogBase2Abs q : ℝ) =
    if Azurite.Nat.normalizedCompare q.num.natAbs q.den == Ordering.lt then
      (Nat.size q.num.natAbs : ℝ) - (Nat.size q.den : ℝ) - 1
    else
      (Nat.size q.num.natAbs : ℝ) - (Nat.size q.den : ℝ) := by
    have hsr_num : (Nat.size q.num.natAbs : ℝ) = (Nat.log2 q.num.natAbs : ℝ) + 1 := by
      exact_mod_cast Azurite.Nat.size_eq_log2_succ q.num.natAbs hN
    have hsr_den : (Nat.size q.den : ℝ) = (Nat.log2 q.den : ℝ) + 1 := by
      exact_mod_cast Azurite.Nat.size_eq_log2_succ q.den hD
    unfold floorLogBase2Abs
    split_ifs <;> push_cast <;> linarith
  
  have h_floor_iff : ⌊logb 2 |(q : ℝ)|⌋ = floorLogBase2Abs q ↔
    (floorLogBase2Abs q : ℝ) ≤ logb 2 |(q : ℝ)| ∧ logb 2 |(q : ℝ)| < (floorLogBase2Abs q : ℝ) + 1 := by
    exact Int.floor_eq_iff (z := floorLogBase2Abs q) (a := logb 2 |(q : ℝ)|)
  
  rw [eq_comm, h_floor_iff, h_exponent, h_log_div]
  
  have h_sizeN := size_bounds q.num.natAbs hN
  have h_sizeD := size_bounds q.den hD
  
  have h_sizeN_cast : ((q.num.natAbs.size - 1 : ℕ) : ℝ) = (q.num.natAbs.size : ℝ) - 1 := by
    have hl : 1 ≤ q.num.natAbs.size := Nat.size_pos.mpr hN
    rw [Nat.cast_sub hl, Nat.cast_one]
  have h_sizeD_cast : ((q.den.size - 1 : ℕ) : ℝ) = (q.den.size : ℝ) - 1 := by
    have hl : 1 ≤ q.den.size := Nat.size_pos.mpr hD
    rw [Nat.cast_sub hl, Nat.cast_one]
  
  rw [h_sizeN_cast] at h_sizeN
  rw [h_sizeD_cast] at h_sizeD
  
  split_ifs with h_lt
  · have h_cmp := compare_to_logb_bounds_lt q.num.natAbs q.den hN hD h_lt
    constructor
    · linarith [h_sizeN.1, h_sizeD.2]
    · linarith [h_cmp]
  · have h_cmp := compare_to_logb_bounds_ge q.num.natAbs q.den hN hD h_lt
    constructor
    · linarith [h_cmp]
    · linarith [h_sizeN.2, h_sizeD.1]

lemma compare_to_logb_bounds_ceiling_gt (N D : ℕ) (hN : N > 0) (hD : D > 0) (h_gt : Azurite.Nat.normalizedCompare N D == Ordering.gt) :
    (Nat.size N : ℝ) - (Nat.size D : ℝ) < logb 2 (N : ℝ) - logb 2 (D : ℝ) := by
  have h_comp := normalizedCompare_eq_real N D hN hD
  have h_base : (1 : ℝ) < 2 := by norm_num
  have h_pos_N : (0 : ℝ) < (N : ℝ) / 2 ^ Nat.size N := div_pos (Nat.cast_pos.mpr hN) (by positivity)
  have h_pos_D : (0 : ℝ) < (D : ℝ) / 2 ^ Nat.size D := div_pos (Nat.cast_pos.mpr hD) (by positivity)
  have h_log_N : logb 2 ((N : ℝ) / 2 ^ Nat.size N) = logb 2 (N : ℝ) - (Nat.size N : ℝ) := by
    rw [logb_div (Nat.cast_pos.mpr hN).ne' (by positivity), logb_pow, logb_self_eq_one h_base, mul_one]
  have h_log_D : logb 2 ((D : ℝ) / 2 ^ Nat.size D) = logb 2 (D : ℝ) - (Nat.size D : ℝ) := by
    rw [logb_div (Nat.cast_pos.mpr hD).ne' (by positivity), logb_pow, logb_self_eq_one h_base, mul_one]
  rw [beq_iff_eq] at h_gt
  have h1 : compare ((N : ℝ) / (2 ^ Nat.size N : ℝ)) ((D : ℝ) / (2 ^ Nat.size D : ℝ)) = Ordering.gt := by
    rw [← h_comp, h_gt]
  have h2 : (D : ℝ) / 2 ^ Nat.size D < (N : ℝ) / 2 ^ Nat.size N := compare_gt_iff_gt.mp h1
  have h3 : logb 2 ((D : ℝ) / 2 ^ Nat.size D) < logb 2 ((N : ℝ) / 2 ^ Nat.size N) := (logb_lt_logb_iff h_base h_pos_D h_pos_N).mpr h2
  rw [h_log_N, h_log_D] at h3
  linarith

lemma compare_to_logb_bounds_ceiling_le (N D : ℕ) (hN : N > 0) (hD : D > 0) (h_gt : ¬(Azurite.Nat.normalizedCompare N D == Ordering.gt)) :
    logb 2 (N : ℝ) - logb 2 (D : ℝ) ≤ (Nat.size N : ℝ) - (Nat.size D : ℝ) := by
  have h_comp := normalizedCompare_eq_real N D hN hD
  have h_base : (1 : ℝ) < 2 := by norm_num
  have h_pos_N : (0 : ℝ) < (N : ℝ) / 2 ^ Nat.size N := div_pos (Nat.cast_pos.mpr hN) (by positivity)
  have h_pos_D : (0 : ℝ) < (D : ℝ) / 2 ^ Nat.size D := div_pos (Nat.cast_pos.mpr hD) (by positivity)
  have h_log_N : logb 2 ((N : ℝ) / 2 ^ Nat.size N) = logb 2 (N : ℝ) - (Nat.size N : ℝ) := by
    rw [logb_div (Nat.cast_pos.mpr hN).ne' (by positivity), logb_pow, logb_self_eq_one h_base, mul_one]
  have h_log_D : logb 2 ((D : ℝ) / 2 ^ Nat.size D) = logb 2 (D : ℝ) - (Nat.size D : ℝ) := by
    rw [logb_div (Nat.cast_pos.mpr hD).ne' (by positivity), logb_pow, logb_self_eq_one h_base, mul_one]
  have h_gt_ne : Azurite.Nat.normalizedCompare N D ≠ Ordering.gt := by
    intro hc; apply h_gt; rw [hc]; rfl
  have h1 : compare ((N : ℝ) / (2 ^ Nat.size N : ℝ)) ((D : ℝ) / (2 ^ Nat.size D : ℝ)) ≠ Ordering.gt := by
    rw [← h_comp]; exact h_gt_ne
  have h2 : ¬((D : ℝ) / 2 ^ Nat.size D < (N : ℝ) / 2 ^ Nat.size N) := by
    intro hc; exact h1 (compare_gt_iff_gt.mpr hc)
  have h3 : (N : ℝ) / 2 ^ Nat.size N ≤ (D : ℝ) / 2 ^ Nat.size D := not_lt.mp h2
  have h4 : logb 2 ((N : ℝ) / 2 ^ Nat.size N) ≤ logb 2 ((D : ℝ) / 2 ^ Nat.size D) := (logb_le_logb h_base h_pos_N h_pos_D).mpr h3
  rw [h_log_N, h_log_D] at h4
  linarith

lemma ceilingLogBase2Abs_eq (q : ℚ) (hq : q ≠ 0) :
  ceilingLogBase2Abs q = ⌈logb 2 |(q : ℝ)|⌉ := by
  have hN : q.num.natAbs > 0 := by
    apply Int.natAbs_pos.mpr
    intro h_num
    have h_zero : q = 0 := by
      rw [← Rat.num_div_den q, h_num, Int.cast_zero, zero_div]
    exact hq h_zero
  have hD : q.den > 0 := q.den_pos
  
  have h_abs_q : |(q : ℝ)| = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
    have h1 : |(q.num : ℝ)| = (q.num.natAbs : ℝ) := by simp
    have h2 : |(q.den : ℝ)| = (q.den : ℝ) := by simp
    rw [Rat.cast_def, abs_div, h1, h2]
  
  have hN_pos : (q.num.natAbs : ℝ) > 0 := by exact_mod_cast hN
  have hD_pos : (q.den : ℝ) > 0 := by exact_mod_cast hD
  
  have h_log_div : logb 2 |(q : ℝ)| = logb 2 (q.num.natAbs : ℝ) - logb 2 (q.den : ℝ) := by
    rw [h_abs_q, logb_div hN_pos.ne' hD_pos.ne']
  
  have h_exponent : (ceilingLogBase2Abs q : ℝ) =
    if Azurite.Nat.normalizedCompare q.num.natAbs q.den == Ordering.gt then
      (Nat.size q.num.natAbs : ℝ) - (Nat.size q.den : ℝ) + 1
    else
      (Nat.size q.num.natAbs : ℝ) - (Nat.size q.den : ℝ) := by
    have hsr_num : (Nat.size q.num.natAbs : ℝ) = (Nat.log2 q.num.natAbs : ℝ) + 1 := by
      exact_mod_cast Azurite.Nat.size_eq_log2_succ q.num.natAbs hN
    have hsr_den : (Nat.size q.den : ℝ) = (Nat.log2 q.den : ℝ) + 1 := by
      exact_mod_cast Azurite.Nat.size_eq_log2_succ q.den hD
    unfold ceilingLogBase2Abs
    split_ifs <;> push_cast <;> linarith
  
  have h_ceil_iff : ⌈logb 2 |(q : ℝ)|⌉ = ceilingLogBase2Abs q ↔
    (ceilingLogBase2Abs q : ℝ) - 1 < logb 2 |(q : ℝ)| ∧ logb 2 |(q : ℝ)| ≤ (ceilingLogBase2Abs q : ℝ) := by
    exact Int.ceil_eq_iff (z := ceilingLogBase2Abs q) (a := logb 2 |(q : ℝ)|)
  
  rw [eq_comm, h_ceil_iff, h_exponent, h_log_div]
  
  have h_sizeN := size_bounds q.num.natAbs hN
  have h_sizeD := size_bounds q.den hD
  
  have h_sizeN_cast : ((q.num.natAbs.size - 1 : ℕ) : ℝ) = (q.num.natAbs.size : ℝ) - 1 := by
    have hl : 1 ≤ q.num.natAbs.size := Nat.size_pos.mpr hN
    rw [Nat.cast_sub hl, Nat.cast_one]
  have h_sizeD_cast : ((q.den.size - 1 : ℕ) : ℝ) = (q.den.size : ℝ) - 1 := by
    have hl : 1 ≤ q.den.size := Nat.size_pos.mpr hD
    rw [Nat.cast_sub hl, Nat.cast_one]
  
  rw [h_sizeN_cast] at h_sizeN
  rw [h_sizeD_cast] at h_sizeD
  
  split_ifs with h_gt
  · have h_cmp := compare_to_logb_bounds_ceiling_gt q.num.natAbs q.den hN hD h_gt
    constructor
    · linarith [h_cmp]
    · linarith [h_sizeN.2, h_sizeD.1]
  · have h_cmp := compare_to_logb_bounds_ceiling_le q.num.natAbs q.den hN hD h_gt
    constructor
    · linarith [h_sizeN.1, h_sizeD.2]
    · linarith [h_cmp]

lemma floorLogBase2Abs_lt_imp_abs_lt (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h_log_lt : floorLogBase2Abs x < floorLogBase2Abs y) : |x| < |y| := by
  have h_floor_x := floorLogBase2Abs_eq x hx
  have h_floor_y := floorLogBase2Abs_eq y hy
  
  have h_base : (1 : ℝ) < 2 := by norm_num
  have h_abs_x_pos : 0 < |(x : ℝ)| := abs_pos.mpr (by exact_mod_cast hx)
  have h_abs_y_pos : 0 < |(y : ℝ)| := abs_pos.mpr (by exact_mod_cast hy)
  
  have h_floor_bound_x : logb 2 |(x : ℝ)| < (floorLogBase2Abs x : ℝ) + 1 := by
    have h1 := Int.lt_floor_add_one (logb 2 |(x : ℝ)|)
    rw [← h_floor_x] at h1
    exact h1
  
  have h_floor_bound_y : (floorLogBase2Abs y : ℝ) ≤ logb 2 |(y : ℝ)| := by
    have h1 := Int.floor_le (logb 2 |(y : ℝ)|)
    rw [← h_floor_y] at h1
    exact h1
  
  have h_cast_lt : (floorLogBase2Abs x : ℝ) + 1 ≤ (floorLogBase2Abs y : ℝ) := by
    exact_mod_cast h_log_lt
  
  have h_log_trans : logb 2 |(x : ℝ)| < logb 2 |(y : ℝ)| := by calc
    logb 2 |(x : ℝ)| < (floorLogBase2Abs x : ℝ) + 1 := h_floor_bound_x
    _ ≤ (floorLogBase2Abs y : ℝ) := h_cast_lt
    _ ≤ logb 2 |(y : ℝ)| := h_floor_bound_y
  
  have h_abs_lt : |(x : ℝ)| < |(y : ℝ)| := (logb_lt_logb_iff h_base h_abs_x_pos h_abs_y_pos).mp h_log_trans
  
  exact_mod_cast h_abs_lt

end Azurite.Rat
