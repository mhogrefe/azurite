import Azurite.AzNat.ModPow2
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.ShiftRight

namespace Azurite.AzNat

/-- `toNatLimbsList (l.take k)` is the low-`64k`-bit chunk of `toNatLimbsList l`. -/
private lemma toNatLimbsList_take (l : List UInt64) (k : Nat) :
    toNatLimbsList (l.take k) = toNatLimbsList l % 2 ^ (64 * k) := by
  by_cases hk : k ≤ l.length
  · have h_app := toNatLimbsList_append (l.take k) (l.drop k)
    rw [List.take_append_drop] at h_app
    have h_take_len : (l.take k).length = k := by rw [List.length_take]; omega
    rw [h_take_len] at h_app
    have hlt : toNatLimbsList (l.take k) < 2 ^ (64 * k) := by
      have := toNatLimbsList_lt_pow (l.take k)
      rw [h_take_len] at this; exact this
    have hkey : (toNatLimbsList (l.take k) + toNatLimbsList (l.drop k) * 2 ^ (64 * k))
        % 2 ^ (64 * k) = toNatLimbsList (l.take k) := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    rw [h_app, Nat.add_comm, hkey]
  · push Not at hk
    rw [List.take_of_length_le (Nat.le_of_lt hk)]
    have hlt : toNatLimbsList l < 2 ^ (64 * k) := by
      have h1 := toNatLimbsList_lt_pow l
      have h2 : 2 ^ (64 * l.length) ≤ 2 ^ (64 * k) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    exact (Nat.mod_eq_of_lt hlt).symm

/-- `(a.extract 0 q).toNat` is the low-`64q`-bit chunk of `a.toNat`. -/
private lemma toNatLimbsList_extract_zero (a : Array UInt64) (q : Nat) :
    toNatLimbsList (a.extract 0 q).toList = toNatLimbsList a.toList % 2 ^ (64 * q) := by
  rw [Array.toList_extract, List.extract_eq_take_drop]
  simp only [Nat.sub_zero, List.drop_zero]
  exact toNatLimbsList_take a.toList q

/-- The numeric value of the low-`r`-bit mask `(1 <<< r) - 1` in UInt64 is `2 ^ r - 1`. -/
private lemma uint64_lowMask_toNat (r : Nat) (hr : r < 64) :
    (((1 : UInt64) <<< UInt64.ofNat r) - 1).toNat = 2 ^ r - 1 := by
  have h1 : ((1 : UInt64) <<< UInt64.ofNat r).toNat = 2 ^ r := by
    rw [UInt64.toNat_shiftLeft, show ((1 : UInt64).toNat = 1) from rfl]
    have hofNat : (UInt64.ofNat r).toNat = r := Nat.mod_eq_of_lt (by omega)
    rw [hofNat, Nat.one_shiftLeft, Nat.mod_eq_of_lt hr]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hr)
  rw [UInt64.toNat_sub, h1]
  change (2 ^ 64 - 1 + 2 ^ r) % 2 ^ 64 = 2 ^ r - 1
  have h2pow : 2 ^ r < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hr
  have h2pos : 0 < 2 ^ r := Nat.two_pow_pos _
  rw [show 2 ^ 64 - 1 + 2 ^ r = 2 ^ 64 + (2 ^ r - 1) from by omega]
  omega

/-- Arithmetic split: when `b < 2 ^ q`,
    `(a * 2 ^ q + b) % 2 ^ (q + r) = (a % 2 ^ r) * 2 ^ q + b`. -/
private lemma mul_pow_add_mod (a b q r : Nat) (hb : b < 2 ^ q) :
    (a * 2 ^ q + b) % 2 ^ (q + r) = (a % 2 ^ r) * 2 ^ q + b := by
  rw [show (2 : Nat) ^ (q + r) = 2 ^ q * 2 ^ r from Nat.pow_add 2 q r]
  have hpow_q_pos : 0 < 2 ^ q := Nat.two_pow_pos q
  have hpow_r_pos : 0 < 2 ^ r := Nat.two_pow_pos r
  have h_b_lt : b < 2 ^ q * 2 ^ r := lt_of_lt_of_le hb (Nat.le_mul_of_pos_right _ hpow_r_pos)
  have h_amul : (2 ^ q * a) % (2 ^ q * 2 ^ r) = 2 ^ q * (a % 2 ^ r) :=
    Nat.mul_mod_mul_left (2 ^ q) a (2 ^ r)
  rw [show a * 2 ^ q + b = 2 ^ q * a + b from by ring]
  rw [Nat.add_mod, h_amul, Nat.mod_eq_of_lt h_b_lt]
  have h_amod : a % 2 ^ r < 2 ^ r := Nat.mod_lt _ hpow_r_pos
  have h_result_lt : 2 ^ q * (a % 2 ^ r) + b < 2 ^ q * 2 ^ r := by
    have h1 : 2 ^ q * (a % 2 ^ r) ≤ 2 ^ q * (2 ^ r - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : 2 ^ q * (2 ^ r - 1) = 2 ^ q * 2 ^ r - 2 ^ q := by rw [Nat.mul_sub_one]
    have h3 : 2 ^ q ≤ 2 ^ q * 2 ^ r := Nat.le_mul_of_pos_right _ hpow_r_pos
    omega
  rw [Nat.mod_eq_of_lt h_result_lt]
  ring

/-- **Correctness of `modPow2`.** The lowest `k` bits of `n` agree with `n mod 2 ^ k`. -/
theorem toNat_modPow2 (n : AzNat) (k : Nat) :
    (n.modPow2 k).toNat = n.toNat % 2 ^ k := by
  have hr_lt : k % 64 < 64 := Nat.mod_lt _ (by omega)
  have hk_decomp : k = 64 * (k / 64) + k % 64 := by omega
  by_cases hq : k / 64 ≥ n.limbs.size
  · -- Case A: `k / 64 ≥ n.limbs.size`. `n.toNat < 2^k`, so `n.toNat % 2^k = n.toNat`.
    have h_eq : n.modPow2 k = n := by unfold modPow2; simp [hq]
    rw [h_eq]
    have h1 : n.toNat < 2 ^ (64 * n.limbs.size) :=
      toNatLimbsList_lt_pow n.limbs.toList
    have h_mul : 64 * n.limbs.size ≤ 64 * (k / 64) := Nat.mul_le_mul_left 64 hq
    have h2 : (2 : Nat) ^ (64 * n.limbs.size) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact (Nat.mod_eq_of_lt (lt_of_lt_of_le h1 h2)).symm
  · push Not at hq
    have hq_lt : k / 64 < n.limbs.size := hq
    have h_lowLimbs_toNat : toNatLimbsList (n.limbs.extract 0 (k / 64)).toList =
        n.toNat % 2 ^ (64 * (k / 64)) := toNatLimbsList_extract_zero n.limbs (k / 64)
    have h_lowLimbs_len : (n.limbs.extract 0 (k / 64)).toList.length = k / 64 := by
      rw [Array.toList_extract, List.extract_eq_take_drop]
      simp only [Nat.sub_zero, List.drop_zero, List.length_take, Array.length_toList]
      omega
    by_cases hr_zero : k % 64 = 0
    · -- Case B: `r = 0`, so `k = 64 * q`. Take the low `q` limbs.
      have h_eq : n.modPow2 k = ofLimbs (n.limbs.extract 0 (k / 64)) := by
        unfold modPow2; simp [hr_zero, Nat.not_le_of_lt hq_lt]
      have hk_eq : 64 * (k / 64) = k := by omega
      rw [h_eq, toNat_ofLimbs, h_lowLimbs_toNat, hk_eq]
    · -- Case C: `r > 0`. Low `q` limbs plus a masked `q`-th limb.
      have h_eq : n.modPow2 k =
          ofLimbs ((n.limbs.extract 0 (k / 64)).push
            (n.limbs[k / 64] &&& (((1 : UInt64) <<< UInt64.ofNat (k % 64)) - 1))) := by
        unfold modPow2; simp [hr_zero, Nat.not_le_of_lt hq_lt]
      rw [h_eq, toNat_ofLimbs, Array.toList_push, toNatLimbsList_append,
          h_lowLimbs_len, toNatLimbsList_cons,
          show toNatLimbsList ([] : List UInt64) = 0 from rfl,
          Nat.zero_mul, Nat.zero_add, h_lowLimbs_toNat]
      have hmask : (n.limbs[k / 64] &&&
          (((1 : UInt64) <<< UInt64.ofNat (k % 64)) - 1)).toNat =
            n.limbs[k / 64].toNat % 2 ^ (k % 64) := by
        rw [UInt64.toNat_and, uint64_lowMask_toNat (k % 64) hr_lt,
            Nat.and_two_pow_sub_one_eq_mod]
      rw [hmask]
      -- Decompose `n.toNat` at position `q = k / 64`.
      have h_drop_q_split : n.limbs.toList.drop (k / 64) =
          n.limbs[k / 64] :: n.limbs.toList.drop ((k / 64) + 1) := by
        have h_lt : k / 64 < n.limbs.toList.length := by rw [Array.length_toList]; omega
        rw [List.drop_eq_getElem_cons h_lt]
        congr 1
      have h_take_toNat : toNatLimbsList (n.limbs.toList.take (k / 64)) =
          n.toNat % 2 ^ (64 * (k / 64)) := toNatLimbsList_take n.limbs.toList (k / 64)
      have h_take_len : (n.limbs.toList.take (k / 64)).length = k / 64 := by
        rw [List.length_take, Array.length_toList]; omega
      have h_n_toNat_decomp : n.toNat =
          (toNatLimbsList (n.limbs.toList.drop ((k / 64) + 1)) * 2 ^ 64 +
            n.limbs[k / 64].toNat) * 2 ^ (64 * (k / 64)) +
              n.toNat % 2 ^ (64 * (k / 64)) := by
        conv_lhs => rw [show n.toNat = toNatLimbsList n.limbs.toList from rfl,
                        show n.limbs.toList = n.limbs.toList.take (k / 64) ++
                          n.limbs.toList.drop (k / 64)
                          from (List.take_append_drop _ _).symm]
        rw [toNatLimbsList_append, h_take_len, h_drop_q_split, toNatLimbsList_cons,
            h_take_toNat]
      have hC_lt : n.toNat % 2 ^ (64 * (k / 64)) < 2 ^ (64 * (k / 64)) :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      -- `((high * 2^64 + limbs[q].toNat) % 2^r) = limbs[q].toNat % 2^r` since `2^r | 2^64`.
      have h_high_mod :
          (toNatLimbsList (n.limbs.toList.drop ((k / 64) + 1)) * 2 ^ 64 +
            n.limbs[k / 64].toNat) % 2 ^ (k % 64) =
              n.limbs[k / 64].toNat % 2 ^ (k % 64) := by
        have h_64_eq : 2 ^ 64 = 2 ^ (64 - k % 64) * 2 ^ (k % 64) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [h_64_eq, ← Nat.mul_assoc, Nat.add_comm,
            Nat.add_mul_mod_self_right]
      -- Rewrite RHS: `n.toNat % 2^k = (high % 2^r) * 2^(64*q) + (n.toNat % 2^(64*q))`.
      have h_pow_eq : (2 : Nat) ^ k = 2 ^ (64 * (k / 64) + k % 64) := by
        rw [show 64 * (k / 64) + k % 64 = k from by omega]
      conv_rhs => rw [h_pow_eq, h_n_toNat_decomp]
      rw [mul_pow_add_mod _ _ (64 * (k / 64)) (k % 64) hC_lt, h_high_mod]

end Azurite.AzNat
