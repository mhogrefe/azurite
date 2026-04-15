import Azurite.AzNat.Compare
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Conversion

namespace Azurite.AzNat

lemma drop_eq_cons_of_lt {α} (l : List α) (i : Nat) (hi : i < l.length) :
  l.drop i = l.get ⟨i, hi⟩ :: l.drop (i + 1) := by
  exact List.drop_eq_getElem_cons hi

lemma toNatLimbsList_take_drop (l : List UInt64) (i : Nat) (h : i ≤ l.length) :
  toNatLimbsList l = toNatLimbsList (l.drop i) * 2 ^ (64 * i) + toNatLimbsList (l.take i) := by
  have ht : l = l.take i ++ l.drop i := (List.take_append_drop i l).symm
  nth_rw 1 [ht]
  rw [toNatLimbsList_append]
  have hz : (l.take i).length = i := List.length_take_of_le h
  rw [hz]

lemma toNatLimbsList_eq_drop_take (l : List UInt64) (i : Nat) (h : i < l.length) :
  toNatLimbsList l = toNatLimbsList (l.drop (i + 1)) * 2 ^ (64 * (i + 1)) + (l.get ⟨i, h⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (l.take i) := by
  have h1 : i ≤ l.length := by omega
  have h_td := toNatLimbsList_take_drop l i h1
  rw [h_td]
  have h_drop := drop_eq_cons_of_lt l i h
  rw [h_drop]
  have hz1 : toNatLimbsList (l.get ⟨i, h⟩ :: l.drop (i + 1)) = toNatLimbsList (l.drop (i + 1)) * 2^64 + (l.get ⟨i, h⟩).toNat := rfl
  rw [hz1]
  have hz : 64 * (i + 1) = 64 * i + 64 := by omega
  rw [hz, Nat.pow_add]
  have h_dist : (toNatLimbsList (List.drop (i + 1) l) * 2 ^ 64 + (l.get ⟨i, h⟩).toNat) * 2 ^ (64 * i) =
    toNatLimbsList (List.drop (i + 1) l) * 2 ^ 64 * 2 ^ (64 * i) + (l.get ⟨i, h⟩).toNat * 2 ^ (64 * i) := Nat.add_mul _ _ _
  rw [h_dist]
  have h_assoc : toNatLimbsList (List.drop (i + 1) l) * 2 ^ 64 * 2 ^ (64 * i) =
    toNatLimbsList (List.drop (i + 1) l) * (2 ^ 64 * 2 ^ (64 * i)) := Nat.mul_assoc _ _ _
  rw [h_assoc, Nat.mul_comm (2 ^ 64) _]

lemma compare_mul_add_lt (a b pow rem1 rem2 : Nat) (hab : a < b) (hrem1 : rem1 < pow) : a * pow + rem1 < b * pow + rem2 := by
  calc
    a * pow + rem1 < a * pow + pow := Nat.add_lt_add_left hrem1 _
    _ = (a + 1) * pow := by
      have hz : a * pow + pow = a * pow + 1 * pow := by rw [Nat.one_mul]
      rw [hz, ← Nat.add_mul]
    _ ≤ b * pow := Nat.mul_le_mul_right pow (by omega)
    _ ≤ b * pow + rem2 := Nat.le_add_right _ _

lemma compare_add_eq (a b c : Nat) : Ord.compare (a + b) (a + c) = Ord.compare b c := by
  change (if a + b < a + c then Ordering.lt else if a + b = a + c then Ordering.eq else Ordering.gt) =
         (if b < c then Ordering.lt else if b = c then Ordering.eq else Ordering.gt)
  split_ifs with h1 h2 h3 h4 h5 h6
  · rfl
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · rfl
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · rfl

lemma compare_eq_of_drop_eq (l1 l2 : List UInt64) (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length)
  (h_drop : l1.drop (i + 1) = l2.drop (i + 1)) :
  Ord.compare (toNatLimbsList l1) (toNatLimbsList l2) =
    if (l1.get ⟨i, h1⟩).toNat < (l2.get ⟨i, h2⟩).toNat then Ordering.lt
    else if (l1.get ⟨i, h1⟩).toNat > (l2.get ⟨i, h2⟩).toNat then Ordering.gt
    else Ord.compare (toNatLimbsList (l1.take i)) (toNatLimbsList (l2.take i)) := by
  have hd1 := toNatLimbsList_eq_drop_take l1 i h1
  have hd2 := toNatLimbsList_eq_drop_take l2 i h2
  rw [h_drop] at hd1
  rw [hd1, hd2]
  split_ifs with h_lt h_gt
  · have hb1 := toNatLimbsList_lt_pow (l1.take i)
    have hl1 : (l1.take i).length = i := List.length_take_of_le (by omega)
    rw [hl1] at hb1
    have h_sub := compare_mul_add_lt ((l1.get ⟨i, h1⟩).toNat) ((l2.get ⟨i, h2⟩).toNat) (2 ^ (64 * i)) (toNatLimbsList (List.take i l1)) (toNatLimbsList (List.take i l2)) h_lt hb1
    have h_add_C : toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l1.get ⟨i, h1⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l1) < toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l2.get ⟨i, h2⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l2) := by
      have hz1 : toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l1.get ⟨i, h1⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l1) = toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + ((l1.get ⟨i, h1⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l1)) := Nat.add_assoc _ _ _
      have hz2 : toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l2.get ⟨i, h2⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l2) = toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + ((l2.get ⟨i, h2⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l2)) := Nat.add_assoc _ _ _
      rw [hz1, hz2]
      exact Nat.add_lt_add_left h_sub _
    change (if _ then Ordering.lt else if _ then Ordering.eq else Ordering.gt) = Ordering.lt
    rw [if_pos h_add_C]
  · have hb2 := toNatLimbsList_lt_pow (l2.take i)
    have hl2 : (l2.take i).length = i := List.length_take_of_le (by omega)
    rw [hl2] at hb2
    have h_sub := compare_mul_add_lt ((l2.get ⟨i, h2⟩).toNat) ((l1.get ⟨i, h1⟩).toNat) (2 ^ (64 * i)) (toNatLimbsList (List.take i l2)) (toNatLimbsList (List.take i l1)) h_gt hb2
    have h_add_C : toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l2.get ⟨i, h2⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l2) < toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l1.get ⟨i, h1⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l1) := by
      have hz1 : toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l1.get ⟨i, h1⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l1) = toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + ((l1.get ⟨i, h1⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l1)) := Nat.add_assoc _ _ _
      have hz2 : toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l2.get ⟨i, h2⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l2) = toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + ((l2.get ⟨i, h2⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l2)) := Nat.add_assoc _ _ _
      rw [hz1, hz2]
      exact Nat.add_lt_add_left h_sub _
    change (if _ then Ordering.lt else if _ then Ordering.eq else Ordering.gt) = Ordering.gt
    have ht : ¬ (toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l1.get ⟨i, h1⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l1) < toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l2.get ⟨i, h2⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l2)) := by omega
    have ht2 : toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l1.get ⟨i, h1⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l1) ≠ toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l2.get ⟨i, h2⟩).toNat * 2 ^ (64 * i) + toNatLimbsList (List.take i l2) := by omega
    rw [if_neg ht, if_neg ht2]
  · have heq : (l1.get ⟨i, h1⟩).toNat = (l2.get ⟨i, h2⟩).toNat := by omega
    rw [heq]
    exact compare_add_eq (toNatLimbsList (List.drop (i + 1) l2) * 2 ^ (64 * (i + 1)) + (l2.get ⟨i, h2⟩).toNat * 2 ^ (64 * i)) (toNatLimbsList (List.take i l1)) (toNatLimbsList (List.take i l2))

lemma compare_UInt64_eq_compare_toNat (a b : UInt64) :
  Ord.compare a b = Ord.compare a.toNat b.toNat := by
  have hm1 : Ord.compare a b = if a.toNat < b.toNat then Ordering.lt else if a = b then Ordering.eq else Ordering.gt := rfl
  have hm2 : Ord.compare a.toNat b.toNat = if a.toNat < b.toNat then Ordering.lt else if a.toNat = b.toNat then Ordering.eq else Ordering.gt := rfl
  rw [hm1, hm2]
  split_ifs with h1 h2 h3 h4
  · rfl
  · rfl
  · have hc : a.toNat = b.toNat := by rw [h2]
    contradiction
  · have h_eq : a = b := UInt64.eq_of_toNat_eq h4
    contradiction
  · rfl

lemma compare_UInt64_eq_of_lt (a b : UInt64) (h : a < b) : Ord.compare a b = Ordering.lt := by
  have ht : a.toNat < b.toNat := h
  rw [compare_UInt64_eq_compare_toNat]
  have hc : Ord.compare a.toNat b.toNat = if a.toNat < b.toNat then Ordering.lt else if a.toNat = b.toNat then Ordering.eq else Ordering.gt := rfl
  rw [hc, if_pos ht]

lemma compare_UInt64_eq_of_gt (a b : UInt64) (h : a > b) : Ord.compare a b = Ordering.gt := by
  have ht : a.toNat > b.toNat := h
  have ht2 : ¬ (a.toNat < b.toNat) := by omega
  have ht3 : a.toNat ≠ b.toNat := by omega
  rw [compare_UInt64_eq_compare_toNat]
  have hc : Ord.compare a.toNat b.toNat = if a.toNat < b.toNat then Ordering.lt else if a.toNat = b.toNat then Ordering.eq else Ordering.gt := rfl
  rw [hc, if_neg ht2, if_neg ht3]

lemma compare_UInt64_eq_of_eq (a b : UInt64) (h : a = b) : Ord.compare a b = Ordering.eq := by
  rw [compare_UInt64_eq_compare_toNat, h]
  have hz : Ord.compare b.toNat b.toNat = if b.toNat < b.toNat then Ordering.lt else if b.toNat = b.toNat then Ordering.eq else Ordering.gt := rfl
  rw [hz]
  split_ifs
  · omega
  · rfl
  · omega

lemma list_get_take_eq {α} (l : List α) (i : Nat) (hi : i < l.length) :
  (l.take (i + 1)).get ⟨i, by rw [List.length_take_of_le (by omega)]; omega⟩ = l.get ⟨i, hi⟩ := by simp

lemma last_ne_zero_to_list {a : AzNat} (h : a.limbs.size > 0) :
  a.limbs.toList ≠ [] := by
  have hz : a.limbs.toList.length = a.limbs.size := rfl
  intro hc; rw [hc] at hz
  have hz2 : 0 = a.limbs.size := hz
  omega

lemma back_eq_getLast {a : AzNat} :
  a.limbs.back? = a.limbs.toList.getLast? := by
  have h1 := @List.back?_toArray UInt64 a.limbs.toList
  have h2 : a.limbs.toList.toArray = a.limbs := Array.toArray_toList
  rw [h2] at h1
  exact h1

lemma drop_length_sub_one {α} (l : List α) (h : l ≠ []) : l.drop (l.length - 1) = [l.getLast h] := by
  revert h
  induction l with
  | nil => intro hc; contradiction
  | cons head tail ih =>
    intro _h
    cases tail with
    | nil => rfl
    | cons h2 t2 =>
      have ht2 : head :: h2 :: t2 ≠ [] := by simp
      have hl : (head :: h2 :: t2).length - 1 = (h2 :: t2).length := rfl
      rw [hl]
      have hdrop : (head :: h2 :: t2).drop (h2 :: t2).length = (h2 :: t2).drop ((h2 :: t2).length - 1) := by
        have h_len : (h2 :: t2).length = (h2 :: t2).length - 1 + 1 := rfl
        rw [h_len]
        rfl
      rw [hdrop]
      have hlast : (head :: h2 :: t2).getLast ht2 = (h2 :: t2).getLast (by simp) := rfl
      rw [hlast]
      exact ih (by simp)

lemma pow_le_toNatLimbsList (l : List UInt64) (h_not_empty : l ≠ []) (hl : l.getLast? ≠ some 0) :
  2 ^ (64 * (l.length - 1)) ≤ toNatLimbsList l := by
  have htd := toNatLimbsList_take_drop l (l.length - 1) (by omega)
  rw [htd]
  have h_drop : l.drop (l.length - 1) = [l.getLast h_not_empty] := drop_length_sub_one l h_not_empty
  rw [h_drop]
  have hz2 : toNatLimbsList [l.getLast h_not_empty] = (l.getLast h_not_empty).toNat := by
    change 0 * 2^64 + (l.getLast h_not_empty).toNat = (l.getLast h_not_empty).toNat
    simp
  have ht_last : l.getLast? = some (l.getLast h_not_empty) := List.getLast?_eq_some_getLast h_not_empty
  rw [ht_last] at hl
  have h_ne_0 : (l.getLast h_not_empty).toNat ≠ 0 := by
    intro hc
    have h_eq_0 : l.getLast h_not_empty = 0 := UInt64.eq_of_toNat_eq hc
    rw [h_eq_0] at hl
    contradiction
  have h_ge_1 : (l.getLast h_not_empty).toNat ≥ 1 := by omega
  have hz3 : toNatLimbsList [l.getLast h_not_empty] * 2 ^ (64 * (l.length - 1)) = (l.getLast h_not_empty).toNat * 2 ^ (64 * (l.length - 1)) := by rw [hz2]
  rw [hz3]
  have mul_bound : 1 * 2 ^ (64 * (l.length - 1)) ≤ (l.getLast h_not_empty).toNat * 2 ^ (64 * (l.length - 1)) := Nat.mul_le_mul_right _ h_ge_1
  rw [Nat.one_mul] at mul_bound
  exact Nat.le_trans mul_bound (Nat.le_add_right _ _)

lemma compare_Nat_eq_of_lt (a b : Nat) (h : a < b) : Ord.compare a b = Ordering.lt := by
  change (if a < b then Ordering.lt else if a = b then Ordering.eq else Ordering.gt) = Ordering.lt
  rw [if_pos h]

lemma compare_Nat_eq_of_gt (a b : Nat) (h : a > b) : Ord.compare a b = Ordering.gt := by
  change (if a < b then Ordering.lt else if a = b then Ordering.eq else Ordering.gt) = Ordering.gt
  have ht : ¬ (a < b) := by omega
  have ht2 : a ≠ b := by omega
  rw [if_neg ht, if_neg ht2]

lemma toNatLimbsList_take_one (l : List UInt64) (h : 0 < l.length) :
  toNatLimbsList (l.take 1) = (l.get ⟨0, h⟩).toNat := by
  cases l
  · contradiction
  · rename_i head tail
    have h1 : (head :: tail).take 1 = [head] := rfl
    have h2 : (head :: tail).get ⟨0, h⟩ = head := rfl
    rw [h1, h2]
    unfold toNatLimbsList
    dsimp only [List.foldr]
    omega

lemma match_compare_eq (a b : UInt64) :
  (match Ord.compare a b with | Ordering.eq => Ordering.eq | ord => ord) = Ord.compare a b := by
  cases Ord.compare a b <;> rfl


/-- `compareLimbs` compares two length-`k` subarrays lexicographically from the high limb down,
which is equivalent to comparing them as multi-limb naturals (little-endian). -/
theorem compareLimbs_eq_compare_slice (a b : Array UInt64) (aLo bLo k : Nat)
    (ha : aLo + k ≤ a.size) (hb : bLo + k ≤ b.size) :
    compareLimbs a b aLo bLo k ha hb =
      Ord.compare
        (toNatLimbsList ((a.toList.drop aLo).take k))
        (toNatLimbsList ((b.toList.drop bLo).take k)) := by
  induction k with
  | zero =>
    simp [compareLimbs, toNatLimbsList]
  | succ k ih =>
    unfold compareLimbs
    dsimp only
    have hA' : aLo + k < a.size := by omega
    have hB' : bLo + k < b.size := by omega
    have h_lenA : a.toList.length = a.size := rfl
    have h_lenB : b.toList.length = b.size := rfl
    have hla_len : k < ((a.toList.drop aLo).take (k + 1)).length := by
      rw [List.length_take, List.length_drop]; omega
    have hlb_len : k < ((b.toList.drop bLo).take (k + 1)).length := by
      rw [List.length_take, List.length_drop]; omega
    have h_drop_empty : ((a.toList.drop aLo).take (k + 1)).drop (k + 1)
        = ((b.toList.drop bLo).take (k + 1)).drop (k + 1) := by simp
    have h_cmp := compare_eq_of_drop_eq
      ((a.toList.drop aLo).take (k + 1))
      ((b.toList.drop bLo).take (k + 1))
      k hla_len hlb_len h_drop_empty
    have hga : ((a.toList.drop aLo).take (k + 1)).get ⟨k, hla_len⟩ = a[aLo + k] := by
      show _ = _; simp
    have hgb : ((b.toList.drop bLo).take (k + 1)).get ⟨k, hlb_len⟩ = b[bLo + k] := by
      show _ = _; simp
    rw [hga, hgb] at h_cmp
    have hta : ((a.toList.drop aLo).take (k + 1)).take k = (a.toList.drop aLo).take k := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    have htb : ((b.toList.drop bLo).take (k + 1)).take k = (b.toList.drop bLo).take k := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [hta, htb] at h_cmp
    rw [h_cmp]
    split_ifs with h_lt h_gt
    · rw [compare_UInt64_eq_of_lt _ _ h_lt]
    · rw [compare_UInt64_eq_of_gt _ _ h_gt]
    · have h_eq_b : a[aLo + k].toNat = b[bLo + k].toNat := by omega
      have h_eq_u : a[aLo + k] = b[bLo + k] := UInt64.eq_of_toNat_eq h_eq_b
      rw [compare_UInt64_eq_of_eq _ _ h_eq_u]
      exact ih (by omega) (by omega)

theorem compare_eq_compare_toNat (a b : AzNat) : compare a b = Ord.compare a.toNat b.toNat := by
  unfold compare toNat
  have h_sizeA : a.limbs.toList.length = a.limbs.size := rfl
  have h_sizeB : b.limbs.toList.length = b.limbs.size := rfl
  split
  · -- eq case: Ord.compare a.limbs.size b.limbs.size = .eq
    rename_i h_cmp
    have hb_eq : a.limbs.size = b.limbs.size := Nat.compare_eq_eq.mp h_cmp
    rw [compareLimbs_eq_compare_slice a.limbs b.limbs 0 0 a.limbs.size]
    simp [List.take_of_length_le h_sizeA.le,
          List.take_of_length_le (h_sizeB.trans hb_eq.symm).le]
  · -- non-eq case (lt or gt)
    rename_i h_ne
    cases h_cmp : Ord.compare a.limbs.size b.limbs.size
    · -- lt
      have ha : a.limbs.size < b.limbs.size := compare_lt_iff_lt.mp h_cmp
      have h_b_ne : b.limbs.size > 0 := by omega
      have h_a_val_lt : toNatLimbsList a.limbs.toList < 2 ^ (64 * a.limbs.size) := by
        have ht := toNatLimbsList_lt_pow a.limbs.toList
        rw [h_sizeA] at ht
        exact ht
      have hlB : b.limbs.toList.getLast? ≠ some 0 := by
        have ht : b.limbs.back? ≠ some 0 := b.last_ne_zero
        rw [← back_eq_getLast]
        exact ht
      have h_b_val_le : 2 ^ (64 * (b.limbs.size - 1)) ≤ toNatLimbsList b.limbs.toList := by
        have hp := pow_le_toNatLimbsList b.limbs.toList (last_ne_zero_to_list h_b_ne) hlB
        rw [h_sizeB] at hp
        exact hp
      have h_a_lt_b : toNatLimbsList a.limbs.toList < toNatLimbsList b.limbs.toList := by
        have hc : a.limbs.size ≤ b.limbs.size - 1 := by omega
        have hc2 : 2 ^ (64 * a.limbs.size) ≤ 2 ^ (64 * (b.limbs.size - 1)) := by
          apply Nat.pow_le_pow_right (by omega) (by omega)
        omega
      exact (compare_Nat_eq_of_lt _ _ h_a_lt_b).symm
    · -- eq (contradiction)
      exact absurd h_cmp h_ne
    · -- gt
      have ha : a.limbs.size > b.limbs.size := compare_gt_iff_gt.mp h_cmp
      have h_a_ne : a.limbs.size > 0 := by omega
      have hlA : a.limbs.toList.getLast? ≠ some 0 := by
        have ht : a.limbs.back? ≠ some 0 := a.last_ne_zero
        rw [← back_eq_getLast]
        exact ht
      have h_a_val_le : 2 ^ (64 * (a.limbs.size - 1)) ≤ toNatLimbsList a.limbs.toList := by
        have hp := pow_le_toNatLimbsList a.limbs.toList (last_ne_zero_to_list h_a_ne) hlA
        rw [h_sizeA] at hp
        exact hp
      have h_b_val_lt : toNatLimbsList b.limbs.toList < 2 ^ (64 * b.limbs.size) := by
        have ht := toNatLimbsList_lt_pow b.limbs.toList
        rw [h_sizeB] at ht
        exact ht
      have h_a_gt_b : toNatLimbsList a.limbs.toList > toNatLimbsList b.limbs.toList := by
        have hc : b.limbs.size ≤ a.limbs.size - 1 := by omega
        have hc2 : 2 ^ (64 * b.limbs.size) ≤ 2 ^ (64 * (a.limbs.size - 1)) := by
          apply Nat.pow_le_pow_right (by omega) (by omega)
        omega
      exact (compare_Nat_eq_of_gt _ _ h_a_gt_b).symm

theorem compare_ofNat_eq_compare (a b : Nat) : compare (ofNat a) (ofNat b) = Ord.compare a b := by
  rw [compare_eq_compare_toNat]
  rw [toNat_ofNat, toNat_ofNat]

lemma le_iff_toNat_le (a b : AzNat) : a ≤ b ↔ a.toNat ≤ b.toNat := by
  change compare a b ≠ Ordering.gt ↔ a.toNat ≤ b.toNat
  rw [compare_eq_compare_toNat]
  exact compare_le_iff_le

lemma lt_iff_toNat_lt (a b : AzNat) : a < b ↔ a.toNat < b.toNat := by
  change compare a b = Ordering.lt ↔ a.toNat < b.toNat
  rw [compare_eq_compare_toNat]
  exact compare_lt_iff_lt

lemma le_refl (a : AzNat) : a ≤ a := by
  rw [le_iff_toNat_le]

lemma le_trans (a b c : AzNat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rw [le_iff_toNat_le] at *
  exact Nat.le_trans h1 h2

lemma le_antisymm (a b : AzNat) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  rw [le_iff_toNat_le] at *
  exact toNat_injective (Nat.le_antisymm h1 h2)

lemma le_total (a b : AzNat) : a ≤ b ∨ b ≤ a := by
  rw [le_iff_toNat_le, le_iff_toNat_le]
  exact Nat.le_total _ _

lemma lt_iff_le_not_ge (a b : AzNat) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  rw [lt_iff_toNat_lt, le_iff_toNat_le, le_iff_toNat_le]
  have hz : a.toNat < b.toNat ↔ a.toNat ≤ b.toNat ∧ ¬b.toNat ≤ a.toNat := by omega
  exact hz

lemma compare_eq_compareOfLessAndEq (a b : AzNat) : compare a b = compareOfLessAndEq a b := by
  dsimp [compareOfLessAndEq]
  have hl1 : a < b ↔ compare a b = Ordering.lt := Iff.rfl
  have h_eq : a = b ↔ compare a b = Ordering.eq := by
    rw [compare_eq_compare_toNat]
    have hc : a.toNat = b.toNat ↔ Ord.compare a.toNat b.toNat = Ordering.eq := Iff.symm compare_eq_iff_eq
    rw [←hc]
    exact ⟨fun h => by rw [h], toNat_injective⟩
  rcases hc : compare a b with _ | _ | _
  · have h_lt : a < b := by rw [hl1]; exact hc
    have h1 : (if a < b then Ordering.lt else if a = b then Ordering.eq else Ordering.gt) = Ordering.lt := by
      rw [if_pos h_lt]
    exact h1.symm
  · have h_eq_b : a = b := by rw [h_eq]; exact hc
    have hn_lt : ¬ (a < b) := by rw [h_eq_b, lt_iff_toNat_lt]; exact Nat.lt_irrefl _
    have h1 : (if a < b then Ordering.lt else if a = b then Ordering.eq else Ordering.gt) = Ordering.eq := by
      rw [if_neg hn_lt, if_pos h_eq_b]
    exact h1.symm
  · have h_not_lt : ¬ (a < b) := by rw [hl1]; intro h; rw [h] at hc; contradiction
    have h_not_eq : ¬ (a = b) := by rw [h_eq]; intro h; rw [h] at hc; contradiction
    have h1 : (if a < b then Ordering.lt else if a = b then Ordering.eq else Ordering.gt) = Ordering.gt := by
      rw [if_neg h_not_lt, if_neg h_not_eq]
    exact h1.symm

instance : LinearOrder AzNat where
  le_refl := le_refl
  le_trans a b c := le_trans a b c
  lt_iff_le_not_ge := lt_iff_le_not_ge
  le_antisymm a b := le_antisymm a b
  le_total := le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  min_def := fun _ _ => rfl
  max_def := fun _ _ => rfl
  compare := compare
  compare_eq_compareOfLessAndEq := compare_eq_compareOfLessAndEq

theorem compareUInt64_eq (a : AzNat) (u : UInt64) :
    a.compareUInt64 u = Ord.compare a.toNat u.toNat := by
  unfold compareUInt64 toNat
  split
  · -- size = 0
    rename_i h
    have h_empty : a.limbs.toList = [] :=
      List.length_eq_zero_iff.mp (by simp [h])
    rw [h_empty]
    simp only [toNatLimbsList, List.foldr]
    split_ifs with hu
    · have hu0 : u = 0 := of_decide_eq_true hu
      rw [hu0]; rfl
    · have hu_ne : u ≠ 0 := of_decide_eq_false (Bool.eq_false_of_not_eq_true hu)
      have hu_pos : 0 < u.toNat := by
        have : u.toNat ≠ 0 := fun h => hu_ne (UInt64.eq_of_toNat_eq (h.trans rfl))
        omega
      exact (compare_Nat_eq_of_lt 0 u.toNat hu_pos).symm
  · -- size = 1
    rename_i h
    have h0 : 0 < a.limbs.toList.length := by simp [h]
    have h_val : toNatLimbsList a.limbs.toList = a.limbs[0].toNat := by
      have hl : a.limbs.toList.length = 1 := by simp [h]
      have h_eq : a.limbs.toList = a.limbs.toList.take 1 := by
        conv_lhs => rw [show a.limbs.toList = a.limbs.toList.take a.limbs.toList.length from List.take_length.symm]; rw [hl]
      conv_lhs => rw [h_eq]
      rw [toNatLimbsList_take_one a.limbs.toList h0]
      simp
    rw [compare_UInt64_eq_compare_toNat, h_val]
  · -- size ≥ 2
    rename_i n h
    have h_size : a.limbs.size ≥ 2 := by omega
    have h_ne : a.limbs.toList ≠ [] := last_ne_zero_to_list (by omega)
    have hlast : a.limbs.toList.getLast? ≠ some 0 := by
      rw [← back_eq_getLast]; exact a.last_ne_zero
    have h_lb : 2 ^ (64 * (a.limbs.size - 1)) ≤ toNatLimbsList a.limbs.toList := by
      exact pow_le_toNatLimbsList a.limbs.toList h_ne hlast
    have h_ub : u.toNat < 2 ^ 64 := u.toBitVec.isLt
    have h_pow : 2 ^ 64 ≤ 2 ^ (64 * (a.limbs.size - 1)) := by
      apply Nat.pow_le_pow_right (by omega)
      omega
    have h_gt : toNatLimbsList a.limbs.toList > u.toNat := by omega
    exact (compare_Nat_eq_of_gt _ _ h_gt).symm

lemma compare_nat_cast_int (a b : Nat) : Ord.compare a b = Ord.compare (a : Int) (b : Int) := by
  change (if a < b then Ordering.lt else if a = b then Ordering.eq else Ordering.gt) =
         (if (a : Int) < (b : Int) then Ordering.lt else if (a : Int) = (b : Int) then Ordering.eq else Ordering.gt)
  split_ifs with h1 h2 h3 h4 h5 h6
  · rfl
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · rfl
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · rfl

theorem compareInt64_eq (a : AzNat) (i : Int64) :
    a.compareInt64 i = Ord.compare (a.toNat : Int) i.toInt := by
  unfold compareInt64
  split_ifs with hi
  · -- i < 0
    have h_neg : i.toInt < 0 := by rwa [Int64.lt_iff_toInt_lt] at hi
    have h_pos : (a.toNat : Int) ≥ 0 := Int.natCast_nonneg _
    symm; exact compare_gt_iff_gt.mpr (by omega)
  · -- i ≥ 0
    rw [compareUInt64_eq]
    have h_eq : (i.toUInt64.toNat : Int) = i.toInt := by
      have h_nn : ¬i.toInt < 0 := by rwa [Int64.lt_iff_toInt_lt] at hi
      have h1 : i.toUInt64.toNat = i.toBitVec.toNat := rfl
      have h2 : i.toInt = i.toBitVec.toInt := rfl
      rw [h1, h2]
      rw [h2] at h_nn
      have h_lt : i.toBitVec.toNat < 2^64 := i.toBitVec.isLt
      unfold BitVec.toInt at h_nn ⊢
      split_ifs with h
      · rfl
      · exfalso
        simp only [not_lt] at h
        split_ifs at h_nn with h2
        · omega
        · omega
    rw [compare_nat_cast_int, h_eq]

instance : WellFoundedLT AzNat where
  wf := by
    have h : WellFounded (InvImage (· < ·) toNat) := InvImage.wf toNat wellFounded_lt
    exact Subrelation.wf (fun {a b : AzNat} (hlt : a < b) => (lt_iff_toNat_lt a b).mp hlt) h

end Azurite.AzNat
