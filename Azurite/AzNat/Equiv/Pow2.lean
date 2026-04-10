import Azurite.AzNat.Pow2
import Azurite.AzNat.Equiv.Basic

namespace Azurite.AzNat

private lemma toNatLimbsList_replicate_zero (n : Nat) :
    toNatLimbsList (List.replicate n (0 : UInt64)) = 0 := by
  induction n with
  | zero => simp [toNatLimbsList]
  | succ n ih => rw [List.replicate_succ, toNatLimbsList_cons]; simp [ih]

private lemma shiftLeft_one_toNat (k : Nat) :
    ((1 : UInt64) <<< (UInt64.ofNat (k % 64))).toNat = 2 ^ (k % 64) := by
  simp only [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat,
             show 1 % 2 ^ 64 = 1 from by omega, Nat.one_shiftLeft]
  have h1 : k % 64 < 64 := Nat.mod_lt _ (by omega)
  have h2 : (k % 64) % UInt64.size = k % 64 := by
    apply Nat.mod_eq_of_lt; change k % 64 < 2 ^ 64; omega
  rw [show UInt64.size = 2 ^ 64 from rfl] at h2
  have h3 : (UInt64.ofNat (k % 64)).toNat = k % 64 := by
    show (k % 64) % 2 ^ 64 = k % 64
    exact Nat.mod_eq_of_lt (by omega)
  rw [h3]
  have h4 : k % 64 % 64 = k % 64 := Nat.mod_eq_of_lt h1
  rw [h4]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) h1)

theorem toNat_pow2 (k : Nat) : (AzNat.pow2 k).toNat = 2 ^ k := by
  unfold AzNat.pow2 toNat
  simp only [Array.toList_push, Array.toList_replicate]
  rw [toNatLimbsList_append, List.length_replicate]
  simp only [toNatLimbsList_replicate_zero]
  rw [toNatLimbsList_cons]
  simp only [toNatLimbsList, List.foldr, Nat.zero_mul, Nat.zero_add]
  rw [shiftLeft_one_toNat, Nat.add_zero, ← Nat.pow_add]
  congr 1; omega

theorem pow2_eq_ofNat (k : Nat) : AzNat.pow2 k = ofNat (2 ^ k) := by
  apply toNat_injective
  rw [toNat_pow2, toNat_ofNat]

private lemma toNatLimbsList_eq_zero_iff_all_zero (l : List UInt64) :
    toNatLimbsList l = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp [toNatLimbsList]
  | cons x xs ih =>
    rw [toNatLimbsList_cons]
    have hxlt : x.toNat < 2 ^ 64 := UInt64.toNat_lt _
    constructor
    · intro h
      have hx_zero : x.toNat = 0 := by
        have : 0 ≤ toNatLimbsList xs := Nat.zero_le _
        omega
      have hxs_zero : toNatLimbsList xs = 0 := by omega
      have hx_eq : x = 0 := UInt64.eq_of_toNat_eq hx_zero
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx_eq
      · exact (ih.mp hxs_zero) y hy
    · intro hall
      have hx_eq : x = 0 := hall x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y = 0 := fun y hy => hall y (List.mem_cons_of_mem _ hy)
      have hxs_zero : toNatLimbsList xs = 0 := ih.mpr hxs
      rw [hx_eq, hxs_zero]; decide

private lemma allZeroLoop_eq_true_iff (a : Array UInt64) (k : Nat) (h : k ≤ a.size) :
    AzNat.allZeroLoop a k h = true ↔ ∀ i (_hi : i < k), a[i]'(by omega) = 0 := by
  induction k with
  | zero => simp [AzNat.allZeroLoop]
  | succ k ih =>
    unfold AzNat.allZeroLoop
    simp only [Bool.and_eq_true, beq_iff_eq]
    rw [ih (by omega)]
    constructor
    · rintro ⟨hk, hall⟩ i hi
      by_cases hieq : i = k
      · subst hieq; exact hk
      · exact hall i (by omega)
    · intro hall
      exact ⟨hall k (Nat.lt_succ_self _), fun i hi => hall i (by omega)⟩

private lemma uint64_and_sub_one_eq_zero_iff (u : UInt64) (hu : u ≠ 0) :
    u &&& (u - 1) = 0 ↔ u.toNat.isPowerOfTwo := by
  have hu_nat : u.toNat ≠ 0 := by
    intro h
    apply hu
    apply UInt64.eq_of_toNat_eq
    rw [h]; rfl
  rw [← Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hu_nat]
  have huint_iff : u &&& (u - 1) = 0 ↔ (u &&& (u - 1)).toNat = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; apply UInt64.eq_of_toNat_eq; exact h
  rw [huint_iff, UInt64.toNat_and, UInt64.toNat_sub,
      show (UInt64.toNat 1) = 1 from rfl]
  have hu_lt : u.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hu_ge : 1 ≤ u.toNat := Nat.one_le_iff_ne_zero.mpr hu_nat
  have heq : (2 ^ 64 - 1 + u.toNat) % 2 ^ 64 = u.toNat - 1 := by omega
  rw [heq]

/-- Decompose `a.toNat` as `last_limb * 2^(64*n) + (lower_limbs as toNatLimbsList)`. -/
private lemma toNat_decomp (a : AzNat) (n : Nat) (hsize : a.limbs.size = n + 1) :
    a.toNat = (a.limbs[n]'(by omega)).toNat * 2 ^ (64 * n) +
              toNatLimbsList (a.limbs.toList.take n) := by
  unfold toNat
  have hlen : a.limbs.toList.length = n + 1 := by
    rw [Array.length_toList]; exact hsize
  have hlen_take : (a.limbs.toList.take n).length = n := by
    rw [List.length_take, hlen]; omega
  have hi_list : n < a.limbs.toList.length := by rw [hlen]; omega
  have h_get : a.limbs.toList[n]'hi_list = a.limbs[n]'(by omega) :=
    (Array.getElem_toList (by omega)).symm
  have hsplit : a.limbs.toList = a.limbs.toList.take n ++ [a.limbs[n]'(by omega)] := by
    have h1 := List.take_concat_get (l := a.limbs.toList) hi_list
    rw [List.concat_eq_append, h_get] at h1
    have h2 : a.limbs.toList.take (n + 1) = a.limbs.toList :=
      List.take_of_length_le (by omega)
    rw [h2] at h1
    exact h1.symm
  conv_lhs => rw [hsplit]
  rw [toNatLimbsList_append, hlen_take]
  rw [show toNatLimbsList [a.limbs[n]'(by omega)] = (a.limbs[n]'(by omega)).toNat from by
    simp [toNatLimbsList]]

theorem isPowerOfTwo_iff (a : AzNat) : a.isPowerOfTwo = true ↔ a.toNat.isPowerOfTwo := by
  unfold AzNat.isPowerOfTwo
  split
  · -- size = 0
    rename_i hsize
    simp only [Bool.false_eq_true, false_iff]
    have h_empty : a.limbs.toList = [] := by
      have hlen : a.limbs.toList.length = 0 := hsize
      exact List.length_eq_zero_iff.mp hlen
    have h_toNat : a.toNat = 0 := by unfold toNat; rw [h_empty]; rfl
    rintro ⟨k, hk⟩
    rw [h_toNat] at hk
    have := Nat.two_pow_pos k
    omega
  · -- size = n + 1
    rename_i n hsize
    simp only [Bool.and_eq_true, beq_iff_eq]
    rw [allZeroLoop_eq_true_iff]
    have hlen : a.limbs.toList.length = n + 1 := by
      rw [Array.length_toList]; exact hsize
    -- Top limb is non-zero by invariant
    have hi : n < a.limbs.size := by omega
    have hlast_ne : a.limbs[n]'hi ≠ 0 := by
      intro hzero
      apply a.last_ne_zero
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
      have : a.limbs[a.limbs.size - 1]'(by omega) = a.limbs[n]'hi := by
        congr 1; omega
      rw [this, hzero]
    rw [uint64_and_sub_one_eq_zero_iff _ hlast_ne]
    rw [toNat_decomp a n hsize]
    constructor
    · rintro ⟨⟨j, hj⟩, hlow⟩
      -- All lower limbs zero ⇒ toNatLimbsList of take n is 0
      have hlow_zero : toNatLimbsList (a.limbs.toList.take n) = 0 := by
        rw [toNatLimbsList_eq_zero_iff_all_zero]
        intro x hx
        rcases List.mem_iff_getElem.mp hx with ⟨i, hi_lt, hgi⟩
        have hlen_take : (a.limbs.toList.take n).length = n := by
          rw [List.length_take, hlen]; omega
        have hin : i < n := by rw [hlen_take] at hi_lt; exact hi_lt
        have h_get_take : (a.limbs.toList.take n)[i]'hi_lt = a.limbs[i]'(by omega) := by
          rw [List.getElem_take]
          exact (Array.getElem_toList (by omega)).symm
        rw [h_get_take] at hgi
        rw [← hgi]
        exact hlow i hin
      rw [hlow_zero, Nat.add_zero, hj]
      exact ⟨j + 64 * n, by rw [Nat.pow_add]⟩
    · rintro ⟨k, hk⟩
      -- Need to recover both: last limb is power of 2, and lower limbs are 0.
      have hlast_lt : (a.limbs[n]'hi).toNat < 2 ^ 64 := UInt64.toNat_lt _
      have hlast_ge : 1 ≤ (a.limbs[n]'hi).toNat := by
        rcases Nat.eq_zero_or_pos (a.limbs[n]'hi).toNat with h0 | hpos
        · exfalso
          apply hlast_ne
          exact UInt64.eq_of_toNat_eq (by rw [h0]; rfl)
        · exact hpos
      have hlen_take : (a.limbs.toList.take n).length = n := by
        rw [List.length_take, hlen]; omega
      have hlow_lt : toNatLimbsList (a.limbs.toList.take n) < 2 ^ (64 * n) := by
        have h := toNatLimbsList_lt_pow (a.limbs.toList.take n)
        rw [hlen_take] at h
        exact h
      -- From hk: last * 2^(64n) + lower = 2^k
      -- last ≥ 1, lower < 2^(64n), so 2^k ≥ 2^(64n), so k ≥ 64n.
      have hk_ge : k ≥ 64 * n := by
        by_contra hlt
        have hlt : k < 64 * n := Nat.lt_of_not_le hlt
        have h1 : (2 : Nat) ^ k < 2 ^ (64 * n) := Nat.pow_lt_pow_right (by omega) hlt
        have h2 : (a.limbs[n]'hi).toNat * 2 ^ (64 * n) ≥ 2 ^ (64 * n) := by
          calc (a.limbs[n]'hi).toNat * 2 ^ (64 * n)
              ≥ 1 * 2 ^ (64 * n) := Nat.mul_le_mul_right _ hlast_ge
            _ = 2 ^ (64 * n) := Nat.one_mul _
        omega
      -- Let j = k - 64n. Then 2^k = 2^j * 2^(64n).
      set j := k - 64 * n with hj_def
      have hk_eq : k = j + 64 * n := by omega
      have hpow_eq : (2 : Nat) ^ k = 2 ^ j * 2 ^ (64 * n) := by
        rw [hk_eq, Nat.pow_add]
      rw [hpow_eq] at hk
      -- last * 2^(64n) + lower = 2^j * 2^(64n)
      -- lower < 2^(64n), so last * 2^(64n) ≤ 2^j * 2^(64n) and last * 2^(64n) > (2^j - 1) * 2^(64n)
      have hpow_n_pos : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
      have hlast_eq : (a.limbs[n]'hi).toNat = 2 ^ j := by
        -- From last * P + lower = 2^j * P with lower < P
        -- → last * P ≤ 2^j * P, so last ≤ 2^j
        -- → last * P > 2^j * P - P = (2^j - 1) * P, so last ≥ 2^j (when 2^j ≥ 1)
        have h_le : (a.limbs[n]'hi).toNat * 2 ^ (64 * n) ≤ 2 ^ j * 2 ^ (64 * n) := by omega
        have h_lt : 2 ^ j * 2 ^ (64 * n) < ((a.limbs[n]'hi).toNat + 1) * 2 ^ (64 * n) := by
          rw [Nat.add_mul, Nat.one_mul]; omega
        have hle1 : (a.limbs[n]'hi).toNat ≤ 2 ^ j :=
          Nat.le_of_mul_le_mul_right h_le hpow_n_pos
        have hlt1 : 2 ^ j < (a.limbs[n]'hi).toNat + 1 :=
          Nat.lt_of_mul_lt_mul_right h_lt
        omega
      have hlow_eq : toNatLimbsList (a.limbs.toList.take n) = 0 := by
        rw [hlast_eq] at hk; omega
      refine ⟨⟨j, hlast_eq⟩, ?_⟩
      intro i hin
      have hi_take : i < (a.limbs.toList.take n).length := by rw [hlen_take]; exact hin
      have h_get_take : (a.limbs.toList.take n)[i]'hi_take = a.limbs[i]'(by omega) := by
        rw [List.getElem_take]
        exact (Array.getElem_toList (by omega)).symm
      rw [← h_get_take]
      have hall := (toNatLimbsList_eq_zero_iff_all_zero _).mp hlow_eq
      apply hall
      apply List.getElem_mem

theorem isPowerOfTwo_ofNat (n : Nat) :
    (ofNat n).isPowerOfTwo = true ↔ n.isPowerOfTwo := by
  rw [isPowerOfTwo_iff, toNat_ofNat]

end Azurite.AzNat
