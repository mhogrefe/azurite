import Azurite.UInt64.Digits
import Azurite.UInt64.Equiv.Pow2
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.MaxPowDiv

namespace UInt64

/-! ### UInt64-level shift/mask helpers -/

private lemma toNat_low_mask (k : Nat) (hk : k < 64) :
    (((1 : UInt64) <<< UInt64.ofNat k) - 1).toNat = 2 ^ k - 1 := by
  have h1 : ((1 : UInt64) <<< UInt64.ofNat k).toNat = 2 ^ k := by
    rw [UInt64.toNat_shiftLeft, show ((1 : UInt64).toNat = 1) from rfl]
    have : (UInt64.ofNat k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.one_shiftLeft, Nat.mod_eq_of_lt hk]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hk)
  rw [UInt64.toNat_sub, h1]
  change (2 ^ 64 - 1 + 2 ^ k) % 2 ^ 64 = 2 ^ k - 1
  have h2pow : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hk
  have h2pos : 0 < 2 ^ k := Nat.two_pow_pos _
  rw [show 2 ^ 64 - 1 + 2 ^ k = 2 ^ 64 + (2 ^ k - 1) from by omega]
  omega

private lemma toNat_shiftRight_ofNat (u : UInt64) (k : Nat) (hk : k < 64) :
    (u >>> UInt64.ofNat k).toNat = u.toNat / 2 ^ k := by
  rw [UInt64.toNat_shiftRight]
  have h1 : (UInt64.ofNat k).toNat = k := Nat.mod_eq_of_lt (by omega)
  rw [show (UInt64.ofNat k).toNat % 64 = k from by rw [h1, Nat.mod_eq_of_lt hk],
      Nat.shiftRight_eq_div_pow]

private lemma toNat_and_low_mask (u : UInt64) (k : Nat) (hk : k < 64) :
    (u &&& (((1 : UInt64) <<< UInt64.ofNat k) - 1)).toNat = u.toNat % 2 ^ k := by
  rw [UInt64.toNat_and, toNat_low_mask k hk, Nat.and_two_pow_sub_one_eq_mod]

/-! ### `ctz` agrees with `padicValNat 2` -/

private lemma dvd_of_testBit_false (n k : Nat) (h : ∀ i < k, n.testBit i = false) :
    2 ^ k ∣ n := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih (fun i hi => h i (by omega))
    have hk := h k (by omega)
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hm,
          Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)] at hk
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero (by omega)
    rw [hm, hq]; exact ⟨q, by rw [Nat.pow_succ, Nat.mul_assoc]⟩

private lemma not_dvd_of_testBit_true (n k : Nat) (h : n.testBit k = true) :
    ¬ 2 ^ (k + 1) ∣ n := by
  intro ⟨m, hm⟩
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hm, Nat.pow_succ, Nat.mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)] at h

private lemma ctz_eq_padicValNat (x : UInt64) (hx : x ≠ 0) :
    x.toBitVec.ctz.toNat = padicValNat 2 x.toNat := by
  have hbv : x.toBitVec ≠ 0#64 := by
    intro h; apply hx; exact UInt64.eq_of_toBitVec_eq h
  have hnat : x.toNat ≠ 0 := by
    intro h; apply hx; ext; exact h
  apply le_antisymm
  · rw [← Nat.pow_dvd_iff_le_padicValNat (by omega) hnat]
    exact dvd_of_testBit_false _ _ (fun i hi => BitVec.getLsbD_false_of_lt_ctz hi)
  · by_contra hc
    push Not at hc
    have h_dvd : 2 ^ (x.toBitVec.ctz.toNat + 1) ∣ x.toNat := by
      rw [Nat.pow_dvd_iff_le_padicValNat (by omega) hnat]; omega
    exact not_dvd_of_testBit_true _ _ (BitVec.getLsbD_true_ctz_of_ne_zero hbv) h_dvd

/-- For a power-of-two `UInt64` `u`, `u.toNat = 2 ^ ctz`. -/
private lemma toNat_eq_two_pow_ctz (u : UInt64) (hu : u.isPowerOfTwo = true) :
    u.toNat = 2 ^ u.toBitVec.ctz.toNat := by
  have hu_ne : u ≠ 0 := by
    intro he
    unfold UInt64.isPowerOfTwo at hu
    rw [he] at hu; simp at hu
  rw [UInt64.isPowerOfTwo_iff] at hu
  obtain ⟨k, hk⟩ := hu
  have h_ctz : u.toBitVec.ctz.toNat = k := by
    rw [ctz_eq_padicValNat u hu_ne, hk, padicValNat_base_pow (by omega) k]
  rw [h_ctz, hk]

/-- A `UInt64` that is a power of two and at least `2` has `ctz ≥ 1`. -/
private lemma ctz_pos_of_isPowerOfTwo_ge_two (u : UInt64) (hu : u.isPowerOfTwo = true)
    (h2 : 2 ≤ u.toNat) : 1 ≤ u.toBitVec.ctz.toNat := by
  by_contra h
  push Not at h
  have h_ctz_zero : u.toBitVec.ctz.toNat = 0 := by omega
  have h_eq : u.toNat = 2 ^ u.toBitVec.ctz.toNat := toNat_eq_two_pow_ctz u hu
  rw [h_ctz_zero] at h_eq; simp at h_eq; omega

/-! ### `digitsPow2Aux` correctness (via WF `induct` lemma) -/

private theorem digitsPow2Aux_eq (k : Nat) (hk_pos : 1 ≤ k) (hk_lt : k < 64)
    (hs : 1 ≤ (UInt64.ofNat k).toNat ∧ (UInt64.ofNat k).toNat < 64)
    (u : UInt64) (acc : Array UInt64) :
    (digitsPow2Aux (((1 : UInt64) <<< UInt64.ofNat k) - 1) (UInt64.ofNat k) hs u acc).toList.map
        UInt64.toNat = acc.toList.map UInt64.toNat ++ Nat.digits (2 ^ k) u.toNat := by
  induction u, acc using
    digitsPow2Aux.induct (((1 : UInt64) <<< UInt64.ofNat k) - 1) (UInt64.ofNat k) hs with
  | case1 acc =>
    rw [digitsPow2Aux]
    simp [Nat.digits_zero]
  | case2 u acc hu ih =>
    rw [digitsPow2Aux]
    rw [dif_neg hu, ih, Array.toList_push, List.map_append]
    simp only [List.map_cons, List.map_nil]
    have h_u_toNat_ne : u.toNat ≠ 0 := fun h =>
      hu (UInt64.toNat.inj (h.trans UInt64.toNat_zero.symm))
    rw [toNat_and_low_mask u k hk_lt, toNat_shiftRight_ofNat u k hk_lt]
    have hb_gt_one : 1 < 2 ^ k := by
      have : (2 : Nat) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk_pos
      omega
    rw [Nat.digits_def' hb_gt_one (Nat.pos_of_ne_zero h_u_toNat_ne)]
    simp [List.append_assoc]

/-! ### `digitsGenericAux` correctness (via WF `induct` lemma) -/

private theorem digitsGenericAux_eq (b : UInt64) (hb : 2 ≤ b.toNat) (u : UInt64) (acc : Array UInt64) :
    (digitsGenericAux b hb u acc).toList.map UInt64.toNat
      = acc.toList.map UInt64.toNat ++ Nat.digits b.toNat u.toNat := by
  induction u, acc using digitsGenericAux.induct b hb with
  | case1 acc =>
    rw [digitsGenericAux]
    simp [Nat.digits_zero]
  | case2 u acc hu ih =>
    rw [digitsGenericAux]
    rw [dif_neg hu, ih, Array.toList_push, List.map_append]
    simp only [List.map_cons, List.map_nil]
    have h_u_toNat_ne : u.toNat ≠ 0 := fun h =>
      hu (UInt64.toNat.inj (h.trans UInt64.toNat_zero.symm))
    rw [UInt64.toNat_mod, UInt64.toNat_div]
    rw [Nat.digits_def' (by omega : 1 < b.toNat) (Nat.pos_of_ne_zero h_u_toNat_ne)]
    simp [List.append_assoc]

/-! ### Main correctness theorems -/

/-- **Correctness of `digitsPow2`.** For `1 ≤ k`, the function's output matches
    `Nat.digits (2^k) u.toNat`. -/
theorem digitsPow2_eq (k : Nat) (hk : 1 ≤ k) (u : UInt64) :
    (UInt64.digitsPow2 k u).toList.map UInt64.toNat = Nat.digits (2 ^ k) u.toNat := by
  unfold digitsPow2
  have hk0 : ¬ k = 0 := by omega
  rw [dif_neg hk0]
  by_cases hk64 : 64 ≤ k
  · rw [dif_pos hk64]
    by_cases hu : u = 0
    · simp [hu, Nat.digits_zero]
    · have h_u_ne : u.toNat ≠ 0 := fun h =>
        hu (UInt64.toNat.inj (h.trans UInt64.toNat_zero.symm))
      have h_u_lt : u.toNat < 2 ^ k := by
        have h64 : u.toNat < 2 ^ 64 := UInt64.toNat_lt u
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) hk64)
      simp [hu, Nat.digits_of_lt _ _ h_u_ne h_u_lt]
  · rw [dif_neg hk64]
    have hs : 1 ≤ (UInt64.ofNat k).toNat ∧ (UInt64.ofNat k).toNat < 64 := by
      have : (UInt64.ofNat k).toNat = k := Nat.mod_eq_of_lt (by omega)
      omega
    have h_lt : k < 64 := by omega
    have := digitsPow2Aux_eq k hk h_lt hs u #[]
    simpa using this

/-- **Correctness of `digits`.** For `b ≥ 2`, the function's output matches
    `Nat.digits b.toNat u.toNat`. -/
theorem digits_eq (b u : UInt64) (hb : 2 ≤ b.toNat) :
    (UInt64.digits b u).toList.map UInt64.toNat = Nat.digits b.toNat u.toNat := by
  unfold digits
  have hb_uint : ¬ b < 2 := by
    intro h
    rw [UInt64.lt_iff_toNat_lt] at h
    have h2 : ((2 : UInt64).toNat = 2) := rfl
    rw [h2] at h; omega
  rw [dif_neg hb_uint]
  by_cases hpow : b.isPowerOfTwo
  · rw [if_pos hpow]
    have h_eq : b.toNat = 2 ^ b.toBitVec.ctz.toNat := toNat_eq_two_pow_ctz b hpow
    have h_ctz_pos : 1 ≤ b.toBitVec.ctz.toNat := ctz_pos_of_isPowerOfTwo_ge_two b hpow hb
    rw [digitsPow2_eq _ h_ctz_pos u, h_eq]
  · rw [if_neg hpow]
    have := digitsGenericAux_eq b hb u #[]
    simpa using this

end UInt64
