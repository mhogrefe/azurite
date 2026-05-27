import Azurite.AzNat.Gcd
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.TrailingZeros
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Azurite.AzNat

/-!
## Correctness of binary GCD

We prove `toNat_gcd : (gcd a b).toNat = Nat.gcd a.toNat b.toNat`.
-/

/-! ### Nat-level lemmas for binary GCD -/

private theorem odd_div_two_pow_padicVal (n : Nat) (hn : n ≠ 0) :
    Odd (n / 2 ^ padicValNat 2 n) := by
  obtain ⟨k, m, hm_odd, h_eq⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm_pos : m ≠ 0 := Odd.pos hm_odd |>.ne'
  have hk_eq : k = padicValNat 2 n := by
    rw [h_eq, padicValNat.mul (by positivity) hm_pos, padicValNat.prime_pow]
    have : padicValNat 2 m = 0 := by
      rw [padicValNat.eq_zero_of_not_dvd]
      intro h; have := hm_odd; rw [Nat.odd_iff] at this; omega
    omega
  rw [← hk_eq, h_eq, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm_odd

/-- When `b` is odd and `b < a`, `gcd(a,b) = gcd((a-b)/2^v, b)`. -/
private theorem binary_gcd_step (a b : Nat) (hb : Odd b)
    (hab : b < a) :
    Nat.gcd a b = Nat.gcd ((a - b) / 2 ^ padicValNat 2 (a - b)) b := by
  have h1 : Nat.gcd a b = Nat.gcd (a - b) b := by
    rw [Nat.gcd_comm a b, Nat.gcd_sub_self_left (by omega), Nat.gcd_comm]
  set v := padicValNat 2 (a - b)
  have h_dvd : 2 ^ v ∣ (a - b) := pow_padicValNat_dvd
  have h_coprime : Nat.Coprime (2 ^ v) b :=
    Nat.Coprime.pow_left v (Odd.coprime_two_left hb)
  rw [h1]
  conv_lhs => rw [show a - b = 2 ^ v * ((a - b) / 2 ^ v) from
    (Nat.mul_div_cancel' h_dvd).symm]
  exact h_coprime.gcd_mul_left_cancel _

/-- `Nat.gcd (2^k * a) (2^k * b) = 2^k * Nat.gcd a b` -/
private theorem gcd_mul_pow2_left (a b k : Nat) :
    Nat.gcd (2 ^ k * a) (2 ^ k * b) = 2 ^ k * Nat.gcd a b :=
  Nat.gcd_mul_left (2 ^ k) a b

/-! ### Bridge lemmas: limb operations to Nat operations -/

/-- `shrLimbs a sh` computes `toNatLimbsList a.toList / 2 ^ sh`. -/
private theorem toNatLimbsList_shrLimbs (a : Array UInt64) (sh : Nat) :
    toNatLimbsList (shrLimbs a sh).toList = toNatLimbsList a.toList / 2 ^ sh := by
  unfold shrLimbs
  dsimp only
  by_cases h_big : sh / 64 ≥ a.size
  · rw [if_pos h_big]
    show 0 = _
    symm; apply Nat.div_eq_of_lt
    calc toNatLimbsList a.toList
        < 2 ^ (64 * a.size) := by
          rw [show a.size = a.toList.length from rfl]
          exact toNatLimbsList_lt_pow a.toList
      _ ≤ 2 ^ sh := by
          apply Nat.pow_le_pow_right (by omega)
          have h1 : sh = 64 * (sh / 64) + sh % 64 := (Nat.div_add_mod sh 64).symm
          have h2 : 64 * a.size ≤ 64 * (sh / 64) := Nat.mul_le_mul_left 64 h_big
          omega
  · push Not at h_big
    rw [if_neg (by omega : ¬(sh / 64 ≥ a.size))]
    by_cases h_ss0 : sh % 64 = 0
    · rw [dif_pos h_ss0, toNatLimbsList_extract_size]
      congr 1; congr 1
      have := (Nat.div_add_mod sh 64).symm; omega
    · rw [dif_neg h_ss0]
      have h_ss_lb : 1 ≤ sh % 64 := by omega
      have h_ss_ub : sh % 64 ≤ 63 := by
        have : sh % 64 < 64 := Nat.mod_lt _ (by omega); omega
      set dropped := a.extract (sh / 64) a.size with hdropped
      have h_dropped_val : toNatLimbsList dropped.toList =
          toNatLimbsList a.toList / 2 ^ (64 * (sh / 64)) :=
        toNatLimbsList_extract_size a (sh / 64)
      have h_shift := shiftLimbsRight_toNat dropped 0 dropped.size (sh % 64)
        (Nat.zero_le _) (Nat.le_refl _) h_ss_lb h_ss_ub
      simp only [List.drop_zero, Nat.sub_zero] at h_shift
      have h_sr_size := shiftLimbsRight_size dropped 0 dropped.size (sh % 64)
        (Nat.zero_le _) (Nat.le_refl _) h_ss_lb h_ss_ub
      have h_take_d : dropped.toList.take dropped.size = dropped.toList :=
        List.take_of_length_le (by rfl)
      have h_take_sr : (shiftLimbsRight dropped 0 dropped.size (sh % 64)
        (Nat.zero_le _) (Nat.le_refl _) h_ss_lb h_ss_ub).1.toList.take dropped.size =
        (shiftLimbsRight dropped 0 dropped.size (sh % 64)
        (Nat.zero_le _) (Nat.le_refl _) h_ss_lb h_ss_ub).1.toList :=
        List.take_of_length_le (by rw [Array.length_toList, h_sr_size])
      rw [h_take_d, h_take_sr] at h_shift
      have h_carry_lt := UInt64.toNat_lt (shiftLimbsRight dropped 0 dropped.size (sh % 64)
        (Nat.zero_le _) (Nat.le_refl _) h_ss_lb h_ss_ub).2
      conv_rhs =>
        rw [show sh = 64 * (sh / 64) + sh % 64 from (Nat.div_add_mod sh 64).symm,
            Nat.pow_add, ← Nat.div_div_eq_div_mul]
      rw [← h_dropped_val]
      have h_pow_split : (2 : Nat) ^ 64 = 2 ^ (sh % 64) * 2 ^ (64 - sh % 64) := by
        rw [← Nat.pow_add]; congr 1; omega
      set V := toNatLimbsList (shiftLimbsRight dropped 0 dropped.size (sh % 64)
          (Nat.zero_le _) (Nat.le_refl _) h_ss_lb h_ss_ub).1.toList with hV
      set C := (shiftLimbsRight dropped 0 dropped.size (sh % 64)
          (Nat.zero_le _) (Nat.le_refl _) h_ss_lb h_ss_ub).2.toNat with hC
      have h_V_eq : V = (V * 2 ^ 64 + C) / 2 ^ 64 := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
            Nat.div_eq_of_lt h_carry_lt, Nat.zero_add]
      rw [h_V_eq, h_shift, h_pow_split,
          Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)]

/-- `trailingZerosLimbs` on a non-empty AzNat gives `padicValNat 2`. -/
private theorem trailingZerosLimbs_eq (a : AzNat) (ha : a.limbs.size ≠ 0) :
    trailingZerosLimbs a.limbs = padicValNat 2 a.toNat := by
  have h_ne : a ≠ 0 := by
    intro h
    exact ha (by show a.limbs.size = 0; have := congr_arg AzNat.limbs h; rw [this]; rfl)
  have h := trailingZeros_eq_padicValNat a h_ne
  unfold trailingZeros at h
  rw [if_neg ha] at h
  exact Option.some.inj h

set_option maxHeartbeats 400000 in
/-- `trailingZerosLimbsAux` gives the same result after popping a trailing zero limb. -/
private theorem trailingZerosLimbsAux_pop (a : Array UInt64) (i : Nat)
    (hi : i < a.size) (hi' : i < a.pop.size) (hlast : a[a.size - 1] = 0) :
    trailingZerosLimbsAux a i hi = trailingZerosLimbsAux a.pop i hi' := by
  have hpop_size : a.pop.size = a.size - 1 := Array.size_pop
  have hget : a.pop[i]'hi' = a[i]'hi := by simp [Array.getElem_pop]
  rw [trailingZerosLimbsAux, trailingZerosLimbsAux]
  simp only [hget]
  split
  case isTrue h =>
    by_cases h2 : i + 1 < a.pop.size
    · have h3 : i + 1 < a.size := by omega
      simp only [h3, h2, ↓reduceDIte]
      exact trailingZerosLimbsAux_pop a (i + 1) h3 h2 hlast
    · have h3 : i + 1 < a.size := by omega
      simp only [h3, h2, ↓reduceDIte]
      have heq : i + 1 = a.size - 1 := by omega
      rw [trailingZerosLimbsAux]
      have h4 : a[i + 1]'h3 = 0 := by simp only [heq, hlast]
      simp only [h4, show ¬(i + 1 + 1 < a.size) from by omega, ↓reduceDIte]
  case isFalse h =>
    rfl
  termination_by a.size - i

/-- `trailingZerosLimbs` is unchanged by popping a trailing zero limb. -/
private theorem trailingZerosLimbs_pop (a : Array UInt64)
    (h_size : 0 < a.size) (hlast : a[a.size - 1] = 0) :
    trailingZerosLimbs a = trailingZerosLimbs a.pop := by
  unfold trailingZerosLimbs
  by_cases h_one : a.size = 1
  · have h_pop_empty : a.pop.size = 0 := by simp [Array.size_pop]; omega
    rw [dif_pos h_size, dif_neg (by omega : ¬(0 < a.pop.size))]
    conv_lhs => unfold trailingZerosLimbsAux
    have h0 : a[(0 : Nat)]'h_size = 0 := by
      have : 0 = a.size - 1 := by omega
      simp only [this, hlast]
    split
    · simp [show ¬(0 + 1 < a.size) from by omega]
    · rename_i hne; exact absurd h0 hne
  · have h_pop_pos : 0 < a.pop.size := by simp [Array.size_pop]; omega
    rw [dif_pos h_size, dif_pos h_pop_pos]
    exact trailingZerosLimbsAux_pop a 0 h_size h_pop_pos hlast

/-- `trailingZerosLimbs` is invariant under `trimTrailingZeros`. -/
private theorem trailingZerosLimbs_trimTrailingZeros_eq (a : Array UInt64) :
    trailingZerosLimbs a = trailingZerosLimbs (trimTrailingZeros a) := by
  rw [trimTrailingZeros]
  by_cases h : a.size = 0
  · simp only [h, ↓reduceDIte]
  · simp only [h, ↓reduceDIte]
    have h_idx : a.size - 1 < a.size := Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one
    by_cases h_last : a[a.size - 1] = 0
    · rw [if_pos h_last, trailingZerosLimbs_pop a (by omega) h_last]
      exact trailingZerosLimbs_trimTrailingZeros_eq a.pop
    · rw [if_neg h_last]
  termination_by a.size
  decreasing_by simp [Array.size_pop]; omega

/-- `trailingZerosLimbs` on a raw array with nonzero value gives `padicValNat 2`.

    The proof constructs the trimmed `AzNat` via `ofLimbs` and uses the existing
    `trailingZerosLimbs_eq`.  The bridge is that `trailingZerosLimbs` only examines
    limbs from index 0 upward and terminates at the first nonzero limb, so removing
    trailing zero limbs (which `trimTrailingZeros` does) cannot change the result. -/
private theorem trailingZerosLimbs_raw_eq (a : Array UInt64)
    (ha : toNatLimbsList a.toList ≠ 0) :
    trailingZerosLimbs a = padicValNat 2 (toNatLimbsList a.toList) := by
  rw [trailingZerosLimbs_trimTrailingZeros_eq]
  have h_toNat : (ofLimbs a).toNat = toNatLimbsList a.toList := toNat_ofLimbs a
  have h_ne : (ofLimbs a).toNat ≠ 0 := h_toNat ▸ ha
  have h_size : (ofLimbs a).limbs.size ≠ 0 :=
    fun h => h_ne ((toNat_eq_zero_iff (ofLimbs a)).mpr h)
  rw [show trimTrailingZeros a = (ofLimbs a).limbs from rfl,
      trailingZerosLimbs_eq (ofLimbs a) h_size, h_toNat]

/-- `makeOddLimbs` computes division by the 2-part. -/
private theorem toNatLimbsList_makeOddLimbs (a : Array UInt64)
    (ha : toNatLimbsList a.toList ≠ 0) :
    toNatLimbsList (makeOddLimbs a).toList =
      toNatLimbsList a.toList / 2 ^ padicValNat 2 (toNatLimbsList a.toList) := by
  unfold makeOddLimbs
  rw [toNatLimbsList_trimTrailingZeros, toNatLimbsList_shrLimbs,
      trailingZerosLimbs_raw_eq a ha]

/-- `makeOddLimbs` produces a nonempty array when the input is nonzero. -/
private theorem makeOddLimbs_size_pos (a : Array UInt64)
    (ha : toNatLimbsList a.toList ≠ 0) :
    0 < (makeOddLimbs a).size := by
  by_contra h
  push Not at h
  have h_empty : (makeOddLimbs a).toList = [] :=
    List.length_eq_zero_iff.mp (by rw [Array.length_toList]; omega)
  have h_val : toNatLimbsList (makeOddLimbs a).toList = 0 := by rw [h_empty]; rfl
  rw [toNatLimbsList_makeOddLimbs a ha] at h_val
  have h_pos : 0 < toNatLimbsList a.toList / 2 ^ padicValNat 2 (toNatLimbsList a.toList) :=
    Odd.pos (odd_div_two_pow_padicVal _ ha)
  omega

/-- `makeOddLimbs` produces a trimmed array. -/
private theorem back?_makeOddLimbs (a : Array UInt64) :
    (makeOddLimbs a).back? ≠ some 0 := by
  unfold makeOddLimbs; exact back?_trimTrailingZeros _

/-- A trimmed nonempty array has value ≥ 2^(64*(size-1)). -/
private theorem toNatLimbsList_ge_of_trimmed (a : Array UInt64)
    (ha : 0 < a.size) (h_trim : a.back? ≠ some 0) :
    2 ^ (64 * (a.size - 1)) ≤ toNatLimbsList a.toList := by
  have h_ne : a.toList ≠ [] := by
    intro h; have : a.size = 0 := by rw [show a.size = a.toList.length from rfl, h]; rfl
    omega
  have h_last_ne : a.toList.getLast h_ne ≠ 0 := by
    intro h_eq
    have h1 : a.back? = some (a.toList.getLast h_ne) := by
      rw [← Array.getLast?_toList]; exact List.getLast?_eq_some_getLast h_ne
    rw [h_eq] at h1; exact h_trim h1
  have h_len : a.toList.length = a.size := rfl
  have h_td := toNatLimbsList_take_drop a.toList (a.size - 1) (by rw [h_len]; omega)
  rw [show a.toList.drop (a.size - 1) = [a.toList.getLast h_ne] from by
    rw [← h_len]; exact List.drop_length_sub_one h_ne] at h_td
  rw [h_td]
  have h_singleton : toNatLimbsList [a.toList.getLast h_ne] =
      (a.toList.getLast h_ne).toNat := by
    show 0 * 2 ^ 64 + (a.toList.getLast h_ne).toNat = _; omega
  have h_last_pos : 0 < (a.toList.getLast h_ne).toNat := by
    rw [Nat.pos_iff_ne_zero]; intro h
    apply h_last_ne; exact UInt64.toNat.inj h
  calc 2 ^ (64 * (a.size - 1))
      = 1 * 2 ^ (64 * (a.size - 1)) := by ring
    _ ≤ (a.toList.getLast h_ne).toNat * 2 ^ (64 * (a.size - 1)) :=
        Nat.mul_le_mul_right _ h_last_pos
    _ = toNatLimbsList [a.toList.getLast h_ne] * 2 ^ (64 * (a.size - 1)) := by
        rw [h_singleton]
    _ ≤ toNatLimbsList [a.toList.getLast h_ne] * 2 ^ (64 * (a.size - 1)) +
        toNatLimbsList (a.toList.take (a.size - 1)) := Nat.le_add_right _ _

/-! ### Loop invariant for gcdOddLimbs -/

/-- Correctness of the binary GCD inner loop.

    The fuel parameter bounds the number of iterations; `64 * (a.size + b.size)`
    is a safe upper bound since each step strictly reduces the bit length of
    one operand. The proof would proceed by well-founded induction on the
    pair `(toNatLimbsList a.toList + toNatLimbsList b.toList, fuel)`, using
    `binary_gcd_step` for the GCD invariant and showing that `makeOddLimbs` of
    the difference strictly reduces the sum of values.

    The detailed proof requires connecting:
    - `compareLimbs_eq_compare_slice` (comparison)
    - `subSameLengthLimbs_toNat` / `subGeqLimbs_toNat` (subtraction)
    - `toNatLimbsList_makeOddLimbs` (odd part extraction)
    to show each recursive call preserves `Nat.gcd` and decreases the measure. -/
private theorem gcdOddLimbs_correct (a b : Array UInt64) (fuel : Nat)
    (ha : 0 < a.size) (hb : 0 < b.size)
    (ha_odd : Odd (toNatLimbsList a.toList))
    (hb_odd : Odd (toNatLimbsList b.toList))
    (hfuel : toNatLimbsList a.toList + toNatLimbsList b.toList ≤ 2 ^ fuel)
    (ha_trim : a.back? ≠ some 0)
    (hb_trim : b.back? ≠ some 0) :
    toNatLimbsList (gcdOddLimbs a b fuel ha hb).toList =
      Nat.gcd (toNatLimbsList a.toList) (toNatLimbsList b.toList) := by
  have ha_pos : 0 < toNatLimbsList a.toList := Odd.pos ha_odd
  have hb_pos : 0 < toNatLimbsList b.toList := Odd.pos hb_odd
  induction fuel generalizing a b with
  | zero => exfalso; omega
  | succ fuel' ih =>
    unfold gcdOddLimbs
    have h_a_slice : (a.toList.drop 0).take a.size = a.toList := by
      simp [List.drop_zero]
    have h_b_slice : (b.toList.drop 0).take b.size = b.toList := by
      simp [List.drop_zero]
    split
    case _ h_eqsz =>
      have h_cmp := compareLimbs_eq_compare_slice a b 0 0 a.size (by omega) (by rw [h_eqsz]; omega)
      have h_b_slice' : (b.toList.drop 0).take a.size = b.toList := by
        rw [h_eqsz]; exact h_b_slice
      rw [h_a_slice, h_b_slice'] at h_cmp
      split
      case h_1 h_eq =>
        rw [h_cmp] at h_eq
        have := (Nat.compare_eq_eq (a := toNatLimbsList a.toList) (b := toNatLimbsList b.toList)).mp h_eq
        simp only [this, Nat.gcd_self]
      case h_2 h_gt =>
        rw [h_cmp] at h_gt
        have h_a_gt_b := Nat.compare_eq_gt.mp h_gt
        dsimp only
        -- Abbreviations for the sub result
        have hA : 0 + a.size ≤ a.size := by omega
        have hB : 0 + a.size ≤ b.size := by rw [h_eqsz]; omega
        -- Subtraction value equals a_val - b_val
        have h_sub_eq : toNatLimbsList (subSameLengthLimbs a b 0 0 a.size hA hB).1.toList =
            toNatLimbsList a.toList - toNatLimbsList b.toList := by
          have h := subSameLengthLimbs_toNat a b 0 0 a.size hA hB
          have h_sz := subSameLengthLimbs_size a b 0 0 a.size hA hB
          -- Eliminate match
          set s := subSameLengthLimbs a b 0 0 a.size hA hB with hs_def
          obtain ⟨sa, sc⟩ := s
          simp only at h h_sz ⊢
          rw [h_a_slice, h_b_slice'] at h
          rw [List.drop_zero, List.take_of_length_le
            (by rw [Array.length_toList, h_sz])] at h
          have h_sa_lt : toNatLimbsList sa.toList < 2 ^ (64 * a.size) := by
            conv_rhs => rw [show a.size = sa.toList.length from by rw [Array.length_toList, h_sz]]
            exact toNatLimbsList_lt_pow sa.toList
          have h_a_lt : toNatLimbsList a.toList < 2 ^ (64 * a.size) := by
            conv_rhs => rw [show a.size = a.toList.length from rfl]
            exact toNatLimbsList_lt_pow a.toList
          cases sc with
          | false => simp at h; omega
          | true => simp at h; omega
        have h_sub_ne : toNatLimbsList (subSameLengthLimbs a b 0 0 a.size hA hB).1.toList ≠ 0 := by
          rw [h_sub_eq]; omega
        -- diff = makeOddLimbs (sub result)
        set diff := makeOddLimbs (subSameLengthLimbs a b 0 0 a.size hA hB).1 with hdiff
        have h_diff_val : toNatLimbsList diff.toList =
            (toNatLimbsList a.toList - toNatLimbsList b.toList) /
              2 ^ padicValNat 2 (toNatLimbsList a.toList - toNatLimbsList b.toList) := by
          rw [hdiff, toNatLimbsList_makeOddLimbs _ h_sub_ne, h_sub_eq]
        have h_diff_odd : Odd (toNatLimbsList diff.toList) := by
          rw [h_diff_val]; exact odd_div_two_pow_padicVal _ (by omega)
        have h_diff_pos : 0 < diff.size := makeOddLimbs_size_pos _ h_sub_ne
        rw [dif_pos h_diff_pos]
        rw [binary_gcd_step _ _ hb_odd h_a_gt_b, ← h_diff_val]
        refine ih diff b h_diff_pos hb h_diff_odd hb_odd ?_
          (back?_makeOddLimbs _) hb_trim h_diff_odd.pos hb_pos
        -- Fuel sufficiency: diff_val + b_val ≤ 2^fuel'
        have h_padic_ge : 1 ≤ padicValNat 2 (toNatLimbsList a.toList - toNatLimbsList b.toList) := by
          rw [Nat.one_le_iff_ne_zero]
          intro h0
          have := padicValNat.eq_zero_iff.mp h0
          have h_even := (Nat.Odd.sub_odd ha_odd hb_odd).two_dvd
          omega
        have h_diff_le : toNatLimbsList diff.toList ≤
            (toNatLimbsList a.toList - toNatLimbsList b.toList) / 2 := by
          rw [h_diff_val]
          have : 2 ≤ 2 ^ padicValNat 2 (toNatLimbsList a.toList - toNatLimbsList b.toList) := by
            calc (2 : Nat) = 2 ^ 1 := by ring
              _ ≤ 2 ^ padicValNat 2 (toNatLimbsList a.toList - toNatLimbsList b.toList) :=
                Nat.pow_le_pow_right (by omega) h_padic_ge
          exact Nat.div_le_div_left this (by positivity)
        calc toNatLimbsList diff.toList + toNatLimbsList b.toList
            ≤ (toNatLimbsList a.toList - toNatLimbsList b.toList) / 2 + toNatLimbsList b.toList := by omega
          _ ≤ (toNatLimbsList a.toList + toNatLimbsList b.toList) / 2 := by omega
          _ ≤ 2 ^ (fuel' + 1) / 2 := Nat.div_le_div_right hfuel
          _ = 2 ^ fuel' := by
              rw [show 2 ^ (fuel' + 1) = 2 ^ fuel' * 2 from by ring]; omega
      case h_3 h_lt =>
        rw [h_cmp] at h_lt
        have h_b_gt_a := Nat.compare_eq_lt.mp h_lt
        dsimp only
        have hA' : 0 + b.size ≤ b.size := by omega
        have hB' : 0 + b.size ≤ a.size := by rw [← h_eqsz]; omega
        have h_sub_eq : toNatLimbsList (subSameLengthLimbs b a 0 0 b.size hA' hB').1.toList =
            toNatLimbsList b.toList - toNatLimbsList a.toList := by
          have h := subSameLengthLimbs_toNat b a 0 0 b.size hA' hB'
          have h_sz := subSameLengthLimbs_size b a 0 0 b.size hA' hB'
          set s := subSameLengthLimbs b a 0 0 b.size hA' hB'
          obtain ⟨sa, sc⟩ := s
          simp only at h h_sz ⊢
          rw [h_b_slice] at h
          have h_a_slice_b : (a.toList.drop 0).take b.size = a.toList := by
            rw [← h_eqsz]; exact h_a_slice
          rw [h_a_slice_b] at h
          rw [List.drop_zero, List.take_of_length_le
            (by rw [Array.length_toList, h_sz])] at h
          have h_sa_lt : toNatLimbsList sa.toList < 2 ^ (64 * b.size) := by
            conv_rhs => rw [show b.size = sa.toList.length from by rw [Array.length_toList, h_sz]]
            exact toNatLimbsList_lt_pow sa.toList
          have h_b_lt : toNatLimbsList b.toList < 2 ^ (64 * b.size) := by
            conv_rhs => rw [show b.size = b.toList.length from rfl]
            exact toNatLimbsList_lt_pow b.toList
          cases sc with
          | false => simp at h; omega
          | true => simp at h; omega
        have h_sub_ne : toNatLimbsList (subSameLengthLimbs b a 0 0 b.size hA' hB').1.toList ≠ 0 := by
          rw [h_sub_eq]; omega
        set diff := makeOddLimbs (subSameLengthLimbs b a 0 0 b.size hA' hB').1 with hdiff
        have h_diff_val : toNatLimbsList diff.toList =
            (toNatLimbsList b.toList - toNatLimbsList a.toList) /
              2 ^ padicValNat 2 (toNatLimbsList b.toList - toNatLimbsList a.toList) := by
          rw [hdiff, toNatLimbsList_makeOddLimbs _ h_sub_ne, h_sub_eq]
        have h_diff_odd : Odd (toNatLimbsList diff.toList) := by
          rw [h_diff_val]; exact odd_div_two_pow_padicVal _ (by omega)
        have h_diff_pos : 0 < diff.size := makeOddLimbs_size_pos _ h_sub_ne
        rw [dif_pos h_diff_pos]
        rw [Nat.gcd_comm, binary_gcd_step _ _ ha_odd h_b_gt_a, ← h_diff_val, Nat.gcd_comm]
        refine ih a diff ha h_diff_pos ha_odd h_diff_odd ?_
          ha_trim (back?_makeOddLimbs _) ha_pos h_diff_odd.pos
        -- Fuel sufficiency
        have h_padic_ge : 1 ≤ padicValNat 2 (toNatLimbsList b.toList - toNatLimbsList a.toList) := by
          rw [Nat.one_le_iff_ne_zero]
          intro h0
          have := padicValNat.eq_zero_iff.mp h0
          have h_even := (Nat.Odd.sub_odd hb_odd ha_odd).two_dvd
          omega
        have h_diff_le : toNatLimbsList diff.toList ≤
            (toNatLimbsList b.toList - toNatLimbsList a.toList) / 2 := by
          rw [h_diff_val]
          have : 2 ≤ 2 ^ padicValNat 2 (toNatLimbsList b.toList - toNatLimbsList a.toList) := by
            calc (2 : Nat) = 2 ^ 1 := by ring
              _ ≤ 2 ^ padicValNat 2 (toNatLimbsList b.toList - toNatLimbsList a.toList) :=
                Nat.pow_le_pow_right (by omega) h_padic_ge
          exact Nat.div_le_div_left this (by positivity)
        calc toNatLimbsList a.toList + toNatLimbsList diff.toList
            ≤ toNatLimbsList a.toList + (toNatLimbsList b.toList - toNatLimbsList a.toList) / 2 := by omega
          _ ≤ (toNatLimbsList a.toList + toNatLimbsList b.toList) / 2 := by omega
          _ ≤ 2 ^ (fuel' + 1) / 2 := Nat.div_le_div_right hfuel
          _ = 2 ^ fuel' := by rw [show 2 ^ (fuel' + 1) = 2 ^ fuel' * 2 from by ring]; omega
    case _ h_neqsz =>
      split
      case _ h_gt =>
        dsimp only
        have h_a_gt_b : toNatLimbsList b.toList < toNatLimbsList a.toList := by
          have h_a_ge := toNatLimbsList_ge_of_trimmed a ha ha_trim
          have h_b_lt : toNatLimbsList b.toList < 2 ^ (64 * b.size) := by
            conv_rhs => rw [show b.size = b.toList.length from rfl]
            exact toNatLimbsList_lt_pow b.toList
          calc toNatLimbsList b.toList
              < 2 ^ (64 * b.size) := h_b_lt
            _ ≤ 2 ^ (64 * (a.size - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
            _ ≤ toNatLimbsList a.toList := h_a_ge
        -- Subtraction
        have hA : 0 + a.size ≤ a.size := by omega
        have hB : 0 + b.size ≤ b.size := by omega
        have h_ge : b.size ≤ a.size := by omega
        -- subGeqLimbs correctness
        have h_sub_eq : toNatLimbsList (subGeqLimbs a b 0 a.size 0 b.size hA hB h_ge ha hb).1.toList =
            toNatLimbsList a.toList - toNatLimbsList b.toList := by
          have h := subGeqLimbs_toNat a b 0 a.size 0 b.size hA hB h_ge ha hb
          have h_sz := subGeqLimbs_size a b 0 a.size 0 b.size hA hB h_ge ha hb
          set s := subGeqLimbs a b 0 a.size 0 b.size hA hB h_ge ha hb
          obtain ⟨sa, sc⟩ := s
          simp only at h h_sz ⊢
          rw [h_a_slice, h_b_slice] at h
          rw [List.drop_zero, List.take_of_length_le
            (by rw [Array.length_toList, h_sz])] at h
          have h_sa_lt : toNatLimbsList sa.toList < 2 ^ (64 * a.size) := by
            conv_rhs => rw [show a.size = sa.toList.length from by rw [Array.length_toList, h_sz]]
            exact toNatLimbsList_lt_pow sa.toList
          have h_a_lt : toNatLimbsList a.toList < 2 ^ (64 * a.size) := by
            conv_rhs => rw [show a.size = a.toList.length from rfl]
            exact toNatLimbsList_lt_pow a.toList
          cases sc with
          | false => simp at h; omega
          | true => simp at h; omega
        -- trimTrailingZeros preserves value
        have h_trim_eq : toNatLimbsList (trimTrailingZeros (subGeqLimbs a b 0 a.size 0 b.size hA hB h_ge ha hb).1).toList =
            toNatLimbsList a.toList - toNatLimbsList b.toList := by
          rw [toNatLimbsList_trimTrailingZeros, h_sub_eq]
        have h_trim_ne : toNatLimbsList (trimTrailingZeros (subGeqLimbs a b 0 a.size 0 b.size hA hB h_ge ha hb).1).toList ≠ 0 := by
          rw [h_trim_eq]; omega
        set diff := makeOddLimbs (trimTrailingZeros (subGeqLimbs a b 0 a.size 0 b.size hA hB h_ge ha hb).1) with hdiff
        have h_diff_val : toNatLimbsList diff.toList =
            (toNatLimbsList a.toList - toNatLimbsList b.toList) /
              2 ^ padicValNat 2 (toNatLimbsList a.toList - toNatLimbsList b.toList) := by
          rw [hdiff, toNatLimbsList_makeOddLimbs _ h_trim_ne, h_trim_eq]
        have h_diff_odd : Odd (toNatLimbsList diff.toList) := by
          rw [h_diff_val]; exact odd_div_two_pow_padicVal _ (by omega)
        have h_diff_pos : 0 < diff.size := makeOddLimbs_size_pos _ h_trim_ne
        rw [dif_pos h_diff_pos]
        rw [binary_gcd_step _ _ hb_odd h_a_gt_b, ← h_diff_val]
        refine ih diff b h_diff_pos hb h_diff_odd hb_odd ?_
          (back?_makeOddLimbs _) hb_trim h_diff_odd.pos hb_pos
        -- Fuel sufficiency
        have h_padic_ge : 1 ≤ padicValNat 2 (toNatLimbsList a.toList - toNatLimbsList b.toList) := by
          rw [Nat.one_le_iff_ne_zero]; intro h0
          have := padicValNat.eq_zero_iff.mp h0
          have h_even := (Nat.Odd.sub_odd ha_odd hb_odd).two_dvd
          omega
        have h_diff_le : toNatLimbsList diff.toList ≤
            (toNatLimbsList a.toList - toNatLimbsList b.toList) / 2 := by
          rw [h_diff_val]
          have : 2 ≤ 2 ^ padicValNat 2 (toNatLimbsList a.toList - toNatLimbsList b.toList) := by
            calc (2 : Nat) = 2 ^ 1 := by ring
              _ ≤ 2 ^ padicValNat 2 (toNatLimbsList a.toList - toNatLimbsList b.toList) :=
                Nat.pow_le_pow_right (by omega) h_padic_ge
          exact Nat.div_le_div_left this (by positivity)
        calc toNatLimbsList diff.toList + toNatLimbsList b.toList
            ≤ (toNatLimbsList a.toList - toNatLimbsList b.toList) / 2 + toNatLimbsList b.toList := by omega
          _ ≤ (toNatLimbsList a.toList + toNatLimbsList b.toList) / 2 := by omega
          _ ≤ 2 ^ (fuel' + 1) / 2 := Nat.div_le_div_right hfuel
          _ = 2 ^ fuel' := by rw [show 2 ^ (fuel' + 1) = 2 ^ fuel' * 2 from by ring]; omega
      case _ h_ngt =>
        have h_lt : b.size > a.size := by omega
        dsimp only
        have h_b_gt_a : toNatLimbsList a.toList < toNatLimbsList b.toList := by
          have h_b_ge := toNatLimbsList_ge_of_trimmed b hb hb_trim
          have h_a_lt : toNatLimbsList a.toList < 2 ^ (64 * a.size) := by
            conv_rhs => rw [show a.size = a.toList.length from rfl]
            exact toNatLimbsList_lt_pow a.toList
          calc toNatLimbsList a.toList
              < 2 ^ (64 * a.size) := h_a_lt
            _ ≤ 2 ^ (64 * (b.size - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
            _ ≤ toNatLimbsList b.toList := h_b_ge
        have hA : 0 + b.size ≤ b.size := by omega
        have hB : 0 + a.size ≤ a.size := by omega
        have h_ge : a.size ≤ b.size := by omega
        have h_sub_eq : toNatLimbsList (subGeqLimbs b a 0 b.size 0 a.size hA hB h_ge hb ha).1.toList =
            toNatLimbsList b.toList - toNatLimbsList a.toList := by
          have h := subGeqLimbs_toNat b a 0 b.size 0 a.size hA hB h_ge hb ha
          have h_sz := subGeqLimbs_size b a 0 b.size 0 a.size hA hB h_ge hb ha
          set s := subGeqLimbs b a 0 b.size 0 a.size hA hB h_ge hb ha
          obtain ⟨sa, sc⟩ := s
          simp only at h h_sz ⊢
          rw [h_b_slice, h_a_slice] at h
          rw [List.drop_zero, List.take_of_length_le
            (by rw [Array.length_toList, h_sz])] at h
          have h_sa_lt : toNatLimbsList sa.toList < 2 ^ (64 * b.size) := by
            conv_rhs => rw [show b.size = sa.toList.length from by rw [Array.length_toList, h_sz]]
            exact toNatLimbsList_lt_pow sa.toList
          have h_b_lt : toNatLimbsList b.toList < 2 ^ (64 * b.size) := by
            conv_rhs => rw [show b.size = b.toList.length from rfl]
            exact toNatLimbsList_lt_pow b.toList
          cases sc with
          | false => simp at h; omega
          | true => simp at h; omega
        have h_trim_eq : toNatLimbsList (trimTrailingZeros (subGeqLimbs b a 0 b.size 0 a.size hA hB h_ge hb ha).1).toList =
            toNatLimbsList b.toList - toNatLimbsList a.toList := by
          rw [toNatLimbsList_trimTrailingZeros, h_sub_eq]
        have h_trim_ne : toNatLimbsList (trimTrailingZeros (subGeqLimbs b a 0 b.size 0 a.size hA hB h_ge hb ha).1).toList ≠ 0 := by
          rw [h_trim_eq]; omega
        set diff := makeOddLimbs (trimTrailingZeros (subGeqLimbs b a 0 b.size 0 a.size hA hB h_ge hb ha).1) with hdiff
        have h_diff_val : toNatLimbsList diff.toList =
            (toNatLimbsList b.toList - toNatLimbsList a.toList) /
              2 ^ padicValNat 2 (toNatLimbsList b.toList - toNatLimbsList a.toList) := by
          rw [hdiff, toNatLimbsList_makeOddLimbs _ h_trim_ne, h_trim_eq]
        have h_diff_odd : Odd (toNatLimbsList diff.toList) := by
          rw [h_diff_val]; exact odd_div_two_pow_padicVal _ (by omega)
        have h_diff_pos : 0 < diff.size := makeOddLimbs_size_pos _ h_trim_ne
        rw [dif_pos h_diff_pos]
        rw [Nat.gcd_comm, binary_gcd_step _ _ ha_odd h_b_gt_a, ← h_diff_val, Nat.gcd_comm]
        refine ih a diff ha h_diff_pos ha_odd h_diff_odd ?_
          ha_trim (back?_makeOddLimbs _) ha_pos h_diff_odd.pos
        -- Fuel sufficiency
        have h_padic_ge : 1 ≤ padicValNat 2 (toNatLimbsList b.toList - toNatLimbsList a.toList) := by
          rw [Nat.one_le_iff_ne_zero]; intro h0
          have := padicValNat.eq_zero_iff.mp h0
          have h_even := (Nat.Odd.sub_odd hb_odd ha_odd).two_dvd
          omega
        have h_diff_le : toNatLimbsList diff.toList ≤
            (toNatLimbsList b.toList - toNatLimbsList a.toList) / 2 := by
          rw [h_diff_val]
          have : 2 ≤ 2 ^ padicValNat 2 (toNatLimbsList b.toList - toNatLimbsList a.toList) := by
            calc (2 : Nat) = 2 ^ 1 := by ring
              _ ≤ 2 ^ padicValNat 2 (toNatLimbsList b.toList - toNatLimbsList a.toList) :=
                Nat.pow_le_pow_right (by omega) h_padic_ge
          exact Nat.div_le_div_left this (by positivity)
        calc toNatLimbsList a.toList + toNatLimbsList diff.toList
            ≤ toNatLimbsList a.toList + (toNatLimbsList b.toList - toNatLimbsList a.toList) / 2 := by omega
          _ ≤ (toNatLimbsList a.toList + toNatLimbsList b.toList) / 2 := by omega
          _ ≤ 2 ^ (fuel' + 1) / 2 := Nat.div_le_div_right hfuel
          _ = 2 ^ fuel' := by rw [show 2 ^ (fuel' + 1) = 2 ^ fuel' * 2 from by ring]; omega

/-! ### Main theorem -/

/-- Helper: `padicValNat 2 (n / 2^k)` when `2^k | n` and `n ≠ 0`. -/
private theorem padicValNat_div_pow (n k : Nat) (hn : n ≠ 0) (hk : k ≤ padicValNat 2 n) :
    padicValNat 2 (n / 2 ^ k) = padicValNat 2 n - k := by
  have h_dvd : 2 ^ k ∣ n := Nat.dvd_trans (Nat.pow_dvd_pow 2 hk) pow_padicValNat_dvd
  have h_ne : n / 2 ^ k ≠ 0 := by
    intro h
    have h1 : 2 ^ k ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h_dvd
    have h2 : n / 2 ^ k > 0 := Nat.div_pos h1 (Nat.two_pow_pos _)
    omega
  have h_factor : n = 2 ^ k * (n / 2 ^ k) := (Nat.mul_div_cancel' h_dvd).symm
  calc padicValNat 2 (n / 2 ^ k)
      = k + padicValNat 2 (n / 2 ^ k) - k := by omega
    _ = padicValNat 2 (2 ^ k * (n / 2 ^ k)) - k := by
        rw [padicValNat.mul (by positivity) h_ne, padicValNat.prime_pow]
    _ = padicValNat 2 n - k := by rw [← h_factor]

/-- Correctness of `gcd`: the binary GCD computes `Nat.gcd`. -/
theorem toNat_gcd (a b : AzNat) : (gcd a b).toNat = Nat.gcd a.toNat b.toNat := by
  unfold gcd
  by_cases ha0 : a.limbs.size = 0
  · simp only [ha0, ↓reduceIte]
    rw [(toNat_eq_zero_iff a).mpr ha0, Nat.gcd_zero_left]
  · simp only [ha0, ↓reduceIte]
    by_cases hb0 : b.limbs.size = 0
    · simp only [hb0, ↓reduceIte]
      rw [(toNat_eq_zero_iff b).mpr hb0, Nat.gcd_zero_right]
    · simp only [hb0, ↓reduceIte]
      -- Both nonzero
      set tzA := trailingZerosLimbs a.limbs
      set tzB := trailingZerosLimbs b.limbs
      set commonTz := min tzA tzB
      set aOdd := makeOddLimbs (shrLimbs a.limbs commonTz)
      set bOdd := makeOddLimbs (shrLimbs b.limbs commonTz)
      set fuel := 64 * (a.limbs.size + b.limbs.size)
      -- Key facts
      have h_a_ne : a.toNat ≠ 0 := fun h => ha0 ((toNat_eq_zero_iff a).mp h)
      have h_b_ne : b.toNat ≠ 0 := fun h => hb0 ((toNat_eq_zero_iff b).mp h)
      have h_a_pos : 0 < a.toNat := Nat.pos_of_ne_zero h_a_ne
      have h_b_pos : 0 < b.toNat := Nat.pos_of_ne_zero h_b_ne
      -- trailingZerosLimbs gives padicValNat
      have h_tzA_eq : tzA = padicValNat 2 a.toNat := trailingZerosLimbs_eq a ha0
      have h_tzB_eq : tzB = padicValNat 2 b.toNat := trailingZerosLimbs_eq b hb0
      -- commonTz = min va vb
      have h_ctz_le_va : commonTz ≤ padicValNat 2 a.toNat := by
        show min tzA tzB ≤ _; rw [h_tzA_eq]; exact Nat.min_le_left _ _
      have h_ctz_le_vb : commonTz ≤ padicValNat 2 b.toNat := by
        show min tzA tzB ≤ _; rw [h_tzB_eq]; exact Nat.min_le_right _ _
      have h_ctz_eq : commonTz = min (padicValNat 2 a.toNat) (padicValNat 2 b.toNat) := by
        show min tzA tzB = _; rw [h_tzA_eq, h_tzB_eq]
      -- shrLimbs values
      have h_shr_a : toNatLimbsList (shrLimbs a.limbs commonTz).toList =
          a.toNat / 2 ^ commonTz := by
        rw [toNatLimbsList_shrLimbs]; rfl
      have h_shr_b : toNatLimbsList (shrLimbs b.limbs commonTz).toList =
          b.toNat / 2 ^ commonTz := by
        rw [toNatLimbsList_shrLimbs]; rfl
      -- These are nonzero (since commonTz ≤ padicVal, division is exact and > 0)
      have h_dvd_a : 2 ^ commonTz ∣ a.toNat :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 h_ctz_le_va) pow_padicValNat_dvd
      have h_dvd_b : 2 ^ commonTz ∣ b.toNat :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 h_ctz_le_vb) pow_padicValNat_dvd
      have h_shr_a_ne : toNatLimbsList (shrLimbs a.limbs commonTz).toList ≠ 0 := by
        rw [h_shr_a]; intro h
        have := Nat.div_pos (Nat.le_of_dvd h_a_pos h_dvd_a) (Nat.two_pow_pos _)
        omega
      have h_shr_b_ne : toNatLimbsList (shrLimbs b.limbs commonTz).toList ≠ 0 := by
        rw [h_shr_b]; intro h
        have := Nat.div_pos (Nat.le_of_dvd h_b_pos h_dvd_b) (Nat.two_pow_pos _)
        omega
      -- makeOddLimbs gives the odd part
      have h_aOdd_val : toNatLimbsList aOdd.toList =
          a.toNat / 2 ^ padicValNat 2 a.toNat := by
        show toNatLimbsList (makeOddLimbs (shrLimbs a.limbs commonTz)).toList = _
        rw [toNatLimbsList_makeOddLimbs _ h_shr_a_ne, h_shr_a,
            padicValNat_div_pow _ _ h_a_ne h_ctz_le_va,
            Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have : commonTz + (padicValNat 2 a.toNat - commonTz) = padicValNat 2 a.toNat := by omega
        rw [this]
      have h_bOdd_val : toNatLimbsList bOdd.toList =
          b.toNat / 2 ^ padicValNat 2 b.toNat := by
        show toNatLimbsList (makeOddLimbs (shrLimbs b.limbs commonTz)).toList = _
        rw [toNatLimbsList_makeOddLimbs _ h_shr_b_ne, h_shr_b,
            padicValNat_div_pow _ _ h_b_ne h_ctz_le_vb,
            Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have : commonTz + (padicValNat 2 b.toNat - commonTz) = padicValNat 2 b.toNat := by omega
        rw [this]
      -- aOdd and bOdd are odd
      have h_aOdd_odd : Odd (toNatLimbsList aOdd.toList) := by
        rw [h_aOdd_val]; exact odd_div_two_pow_padicVal _ h_a_ne
      have h_bOdd_odd : Odd (toNatLimbsList bOdd.toList) := by
        rw [h_bOdd_val]; exact odd_div_two_pow_padicVal _ h_b_ne
      -- aOdd and bOdd are nonempty
      have haO : 0 < aOdd.size :=
        makeOddLimbs_size_pos _ h_shr_a_ne
      have hbO : 0 < bOdd.size :=
        makeOddLimbs_size_pos _ h_shr_b_ne
      simp only [haO, ↓reduceDIte, hbO]
      -- Main computation
      show (shiftLeft (ofLimbs (gcdOddLimbs aOdd bOdd fuel haO hbO)) commonTz).toNat =
        Nat.gcd a.toNat b.toNat
      rw [toNat_shiftLeft, toNat_ofLimbs]
      -- Use the loop invariant
      have h_aOdd_lt : toNatLimbsList aOdd.toList < 2 ^ (64 * a.limbs.size) := by
        rw [h_aOdd_val]
        calc a.toNat / 2 ^ padicValNat 2 a.toNat
            ≤ a.toNat := Nat.div_le_self _ _
          _ < 2 ^ (64 * a.limbs.size) := by
              rw [show a.toNat = toNatLimbsList a.limbs.toList from rfl]
              exact toNatLimbsList_lt_pow _
      have h_bOdd_lt : toNatLimbsList bOdd.toList < 2 ^ (64 * b.limbs.size) := by
        rw [h_bOdd_val]
        calc b.toNat / 2 ^ padicValNat 2 b.toNat
            ≤ b.toNat := Nat.div_le_self _ _
          _ < 2 ^ (64 * b.limbs.size) := by
              rw [show b.toNat = toNatLimbsList b.limbs.toList from rfl]
              exact toNatLimbsList_lt_pow _
      have h_fuel_suff : toNatLimbsList aOdd.toList + toNatLimbsList bOdd.toList ≤ 2 ^ fuel := by
        have h_sa : 0 < a.limbs.size := Nat.pos_of_ne_zero ha0
        have h_sb : 0 < b.limbs.size := Nat.pos_of_ne_zero hb0
        have h1 : 2 ^ (64 * a.limbs.size) ≤ 2 ^ (64 * (a.limbs.size + b.limbs.size) - 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have h2 : 2 ^ (64 * b.limbs.size) ≤ 2 ^ (64 * (a.limbs.size + b.limbs.size) - 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have h3 : 2 ^ (64 * (a.limbs.size + b.limbs.size)) =
            2 ^ (64 * (a.limbs.size + b.limbs.size) - 1 + 1) := by
          congr 1; omega
        rw [h3, Nat.pow_succ]
        omega
      have h_result_val := gcdOddLimbs_correct aOdd bOdd fuel haO hbO
        h_aOdd_odd h_bOdd_odd h_fuel_suff (back?_makeOddLimbs _) (back?_makeOddLimbs _)
      rw [h_result_val, h_aOdd_val, h_bOdd_val]
      -- Goal: gcd(a/2^va, b/2^vb) * 2^commonTz = gcd(a, b)
      rw [h_ctz_eq]
      -- Decompose: a = 2^va * a', b = 2^vb * b'
      set va := padicValNat 2 a.toNat
      set vb := padicValNat 2 b.toNat
      set a' := a.toNat / 2 ^ va
      set b' := b.toNat / 2 ^ vb
      have h_a_decomp : a.toNat = 2 ^ va * a' :=
        (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
      have h_b_decomp : b.toNat = 2 ^ vb * b' :=
        (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
      have h_a_odd : Odd a' := odd_div_two_pow_padicVal _ h_a_ne
      have h_b_odd : Odd b' := odd_div_two_pow_padicVal _ h_b_ne
      -- gcd(a, b) = 2^min(va,vb) * gcd(a', b')
      suffices h : Nat.gcd a.toNat b.toNat = 2 ^ min va vb * Nat.gcd a' b' by
        rw [h, Nat.mul_comm]
      conv_lhs => rw [h_a_decomp, h_b_decomp]
      -- Factor out 2^min from both
      rw [show 2 ^ va = 2 ^ min va vb * 2 ^ (va - min va vb) from by
            rw [← Nat.pow_add]; congr 1; omega,
          show 2 ^ vb = 2 ^ min va vb * 2 ^ (vb - min va vb) from by
            rw [← Nat.pow_add]; congr 1; omega,
          show 2 ^ min va vb * 2 ^ (va - min va vb) * a' =
            2 ^ min va vb * (2 ^ (va - min va vb) * a') from by ring,
          show 2 ^ min va vb * 2 ^ (vb - min va vb) * b' =
            2 ^ min va vb * (2 ^ (vb - min va vb) * b') from by ring,
          gcd_mul_pow2_left]
      congr 1
      -- One of the exponents is 0
      by_cases h_le : va ≤ vb
      · rw [Nat.min_eq_left h_le, show va - va = 0 from by omega,
            Nat.pow_zero, Nat.one_mul]
        -- Goal: a'.gcd (2^(vb-va) * b') = a'.gcd b'
        exact (Nat.Coprime.pow_left _ (Odd.coprime_two_left h_a_odd)).gcd_mul_left_cancel_right b'
      · push Not at h_le
        rw [Nat.min_eq_right (by omega), show vb - vb = 0 from by omega,
            Nat.pow_zero, Nat.one_mul]
        -- Goal: (2^(va-vb) * a').gcd b' = a'.gcd b'
        exact (Nat.Coprime.pow_left _ (Odd.coprime_two_left h_b_odd)).gcd_mul_left_cancel a'

end Azurite.AzNat
