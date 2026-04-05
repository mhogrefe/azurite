import Azurite.AzNat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Basic

namespace Azurite.AzNat

def toNatLimbsList (l : List UInt64) : Nat :=
  l.foldr (fun limb acc => acc * (2 ^ 64) + limb.toNat) 0

lemma toNatLimbsList_cons (x : UInt64) (xs : List UInt64) :
  toNatLimbsList (x :: xs) = toNatLimbsList xs * 2^64 + x.toNat := rfl

lemma toNatLimbsList_append (l1 l2 : List UInt64) :
  toNatLimbsList (l1 ++ l2) = toNatLimbsList l2 * 2^(64 * l1.length) + toNatLimbsList l1 := by
  induction l1 with
  | nil =>
    simp [toNatLimbsList]
  | cons x xs ih =>
    rw [List.cons_append, toNatLimbsList_cons, ih, toNatLimbsList_cons, List.length_cons]
    have h : (toNatLimbsList l2 * 2 ^ (64 * xs.length) + toNatLimbsList xs) * 2 ^ 64 + x.toNat =
      toNatLimbsList l2 * 2 ^ (64 * xs.length) * 2 ^ 64 + toNatLimbsList xs * 2 ^ 64 + x.toNat := by ring
    rw [h]
    have hp : 64 * (xs.length + 1) = 64 * xs.length + 64 := by ring
    rw [hp, Nat.pow_add, Nat.mul_assoc]
    omega

lemma toNatLimbsList_lt_pow (l : List UInt64) : toNatLimbsList l < 2 ^ (64 * l.length) := by
  induction l with
  | nil => decide
  | cons x xs ih =>
    rw [toNatLimbsList_cons, List.length_cons]
    have h1 : 64 * (xs.length + 1) = 64 * xs.length + 64 := by omega
    rw [h1, Nat.pow_add]
    have h2 : toNatLimbsList xs * 2^64 + x.toNat < 2^(64 * xs.length) * 2^64 := by
      have h3 : x.toNat < 2^64 := UInt64.toNat_lt _
      have hc1 : toNatLimbsList xs + 1 ≤ 2 ^ (64 * xs.length) := ih
      have hc2 : (toNatLimbsList xs + 1) * 2 ^ 64 ≤ 2 ^ (64 * xs.length) * 2 ^ 64 := Nat.mul_le_mul_right (2 ^ 64) hc1
      have hc3 : toNatLimbsList xs * 2 ^ 64 + x.toNat < toNatLimbsList xs * 2 ^ 64 + 2 ^ 64 := Nat.add_lt_add_left h3 _
      have hc4 : toNatLimbsList xs * 2 ^ 64 + 2 ^ 64 = (toNatLimbsList xs + 1) * 2 ^ 64 := by ring
      rw [hc4] at hc3
      exact Nat.lt_of_lt_of_le hc3 hc2
    exact h2

def ofNatAux (n : Nat) (acc : Array UInt64) : Array UInt64 :=
  if _h : n = 0 then acc
  else
    ofNatAux (n / (2 ^ 64)) (acc.push (UInt64.ofNat n))
decreasing_by
  apply Nat.div_lt_self
  · omega
  · decide

private lemma toNatLimbs_ofNatAux (n : Nat) (acc : Array UInt64) :
  toNatLimbsList (ofNatAux n acc).toList = n * 2^(64 * acc.size) + toNatLimbsList acc.toList := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    unfold ofNatAux
    split
    · rename_i h_zero
      rw [h_zero]
      simp
    · rename_i h_nzero
      have h_lt : n / 2^64 < n := by apply Nat.div_lt_self; omega; decide
      have ih_call := ih (n / 2^64) h_lt (acc.push (UInt64.ofNat n))
      rw [ih_call]
      rw [Array.toList_push]
      rw [toNatLimbsList_append]
      change _ + (toNatLimbsList [UInt64.ofNat n] * 2 ^ (64 * acc.toList.length) + toNatLimbsList acc.toList) = _
      have hl2 : toNatLimbsList [UInt64.ofNat n] = n % 2^64 := by
        unfold toNatLimbsList; simp
      rw [hl2]
      have h_size : (acc.push (UInt64.ofNat n)).size = acc.size + 1 := by simp
      rw [h_size]
      have h_len : acc.toList.length = acc.size := rfl
      rw [h_len]
      have h_pow : 2 ^ (64 * (acc.size + 1)) = 2 ^ 64 * 2 ^ (64 * acc.size) := by
        have : 64 * (acc.size + 1) = 64 * acc.size + 64 := by ring
        rw [this, Nat.pow_add, Nat.mul_comm]
      rw [h_pow]
      have eqN : n / 2^64 * 2^64 + n % 2^64 = n := by omega
      have eqT : n / 2 ^ 64 * (2 ^ 64 * 2 ^ (64 * acc.size)) + (n % 2 ^ 64 * 2 ^ (64 * acc.size) + toNatLimbsList acc.toList) =
        (n / 2^64 * 2^64 + n % 2^64) * 2 ^ (64 * acc.size) + toNatLimbsList acc.toList := by ring
      rw [eqT, eqN]

theorem ofNatAux_back_ne_zero_of_pos (n : Nat) (hn : 0 < n) (acc : Array UInt64) :
  (ofNatAux n acc).back? ≠ some 0 := by
  unfold ofNatAux
  split
  · rename_i h; omega
  · by_cases hn_div : n / 2^64 = 0
    · have h1 : ofNatAux (n / 2^64) (acc.push (UInt64.ofNat n)) = acc.push (UInt64.ofNat n) := by
        rw [hn_div]
        unfold ofNatAux
        split <;> trivial
      rw [h1]
      rw [Array.back?_push]
      intro hc
      injection hc with hc'
      have ht : (UInt64.ofNat n).toNat = (0 : UInt64).toNat := by rw [hc']
      have hUInt64_size : UInt64.size = 2^64 := rfl
      change n % UInt64.size = 0 at ht
      rw [hUInt64_size] at ht
      have h_lt : n < 2^64 := by omega
      have h_mod : n % 2^64 = n := Nat.mod_eq_of_lt h_lt
      rw [h_mod] at ht
      omega
    · apply ofNatAux_back_ne_zero_of_pos
      · exact Nat.pos_of_ne_zero hn_div
decreasing_by
  apply Nat.div_lt_self
  · omega
  · decide

def ofNat (n : Nat) : AzNat :=
  let arr := ofNatAux n #[]
  ⟨arr, by
    change (ofNatAux n #[]).back? ≠ some 0
    by_cases hn : n = 0
    · rw [hn]
      unfold ofNatAux
      simp
    · apply ofNatAux_back_ne_zero_of_pos n
      omega
  ⟩

def toNat (n : AzNat) : Nat :=
  toNatLimbsList n.limbs.toList

theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  unfold toNat ofNat
  change toNatLimbsList (ofNatAux n #[]).toList = n
  have ht := toNatLimbs_ofNatAux n #[]
  rw [ht]
  simp [toNatLimbsList]

private lemma base_2_64_unique (A B x y : Nat) (hx : x < 2^64) (hy : y < 2^64)
  (h : A * 2^64 + x = B * 2^64 + y) : x = y ∧ A = B := by
  omega

private lemma uint64_val_eq (x y : UInt64) (h : x.toNat = y.toNat) : x = y := by
  have h2 : x.toBitVec = y.toBitVec := BitVec.eq_of_toNat_eq h
  cases x; cases y; simp at h2; subst h2; rfl

private lemma toNatLimbsList_eq_zero_of_getLast_ne_zero (l : List UInt64) (hl : l.getLast? ≠ some 0) (h : toNatLimbsList l = 0) : l = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_cons : toNatLimbsList (x :: xs) = toNatLimbsList xs * 2^64 + x.toNat := rfl
    rw [h_cons] at h
    have hz : 0 * 2^64 + 0 = toNatLimbsList xs * 2^64 + x.toNat := by
      rw [h]; simp
    have hunq := base_2_64_unique 0 (toNatLimbsList xs) 0 x.toNat (by decide) (UInt64.toNat_lt _) hz
    rcases hunq with ⟨hx0, hxs0⟩
    have hx_eq_0 : x = 0 := uint64_val_eq x 0 hx0.symm
    subst hx_eq_0
    have hl_xs : xs.getLast? ≠ some 0 := by
      cases xs
      · contradiction
      · rename_i y ys
        have hh : (0 :: y :: ys ++ []).getLast? = (y :: ys).getLast? := by simp
        exact hl
    have ih_zero := ih hl_xs hxs0.symm
    subst ih_zero
    have hhx : ([0] : List UInt64).getLast? = some 0 := rfl
    contradiction

private lemma toNatLimbsList_inj (l1 l2 : List UInt64)
  (hl1 : l1.getLast? ≠ some 0) (hl2 : l2.getLast? ≠ some 0)
  (h : toNatLimbsList l1 = toNatLimbsList l2) : l1 = l2 := by
  revert l2
  induction l1 with
  | nil =>
    intro l2 hl2 h
    symm
    apply toNatLimbsList_eq_zero_of_getLast_ne_zero l2 hl2 h.symm
  | cons x xs ih =>
    intro l2 hl2 h
    cases l2 with
    | nil =>
      have hz := toNatLimbsList_eq_zero_of_getLast_ne_zero (x :: xs) hl1 h
      contradiction
    | cons y ys =>
      have hc1 : toNatLimbsList (x :: xs) = toNatLimbsList xs * 2^64 + x.toNat := rfl
      have hc2 : toNatLimbsList (y :: ys) = toNatLimbsList ys * 2^64 + y.toNat := rfl
      rw [hc1, hc2] at h
      have hunq := base_2_64_unique (toNatLimbsList xs) (toNatLimbsList ys) x.toNat y.toNat (UInt64.toNat_lt _) (UInt64.toNat_lt _) h
      rcases hunq with ⟨hx, hxs⟩
      have eq_x : x = y := uint64_val_eq x y hx
      subst eq_x
      have hl1_xs : xs.getLast? ≠ some 0 := by
        cases xs
        · intro hc; contradiction
        · rename_i a as
          have hh : (x :: a :: as).getLast? = (a :: as).getLast? := by simp
          rw [← hh]; exact hl1
      have hl2_ys : ys.getLast? ≠ some 0 := by
        cases ys
        · intro hc; contradiction
        · rename_i a as
          have hh : (x :: a :: as).getLast? = (a :: as).getLast? := by simp
          rw [← hh]; exact hl2
      have eq_xs := ih hl1_xs ys hl2_ys hxs
      subst eq_xs
      rfl

theorem toNat_injective {a b : AzNat} (h : toNat a = toNat b) : a = b := by
  have ha : a.limbs.toList.getLast? ≠ some 0 := by
    have h1 := a.last_ne_zero
    have h2 : a.limbs.back? = a.limbs.toList.getLast? := by cases a.limbs; simp
    rw [← h2]
    exact h1
  have hb : b.limbs.toList.getLast? ≠ some 0 := by
    have h1 := b.last_ne_zero
    have h2 : b.limbs.back? = b.limbs.toList.getLast? := by cases b.limbs; simp
    rw [← h2]
    exact h1
  have h_list := toNatLimbsList_inj a.limbs.toList b.limbs.toList ha hb h
  have h_arr : a.limbs = b.limbs := by apply Array.ext'; exact h_list
  cases a
  cases b
  simp at h_arr
  subst h_arr
  rfl

theorem ofNat_toNat (n : AzNat) : ofNat (toNat n) = n := by
  apply toNat_injective
  rw [toNat_ofNat]

def equivNat : AzNat ≃ Nat where
  toFun := toNat
  invFun := ofNat
  left_inv := ofNat_toNat
  right_inv := toNat_ofNat

@[simp] lemma toNat_zero : toNat (0 : AzNat) = 0 := rfl

@[simp] lemma ofNat_zero : ofNat (0 : Nat) = 0 := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_zero]

@[simp] lemma toNat_one : toNat (1 : AzNat) = 1 := rfl

@[simp] lemma ofNat_one : ofNat (1 : Nat) = 1 := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_one]

@[simp] lemma beqUInt64_eq (a : AzNat) (u : UInt64) :
  a.beqUInt64 u = true ↔ a.toNat = u.toNat := by
  rcases a with ⟨⟨l⟩, hl⟩
  have h_size : ({ toList := l } : Array UInt64).size = l.length := rfl
  unfold beqUInt64 toNat
  rw [h_size]
  cases l
  · unfold toNatLimbsList
    simp
    constructor
    · intro h; rw [h]; rfl
    · intro h; have h2 : u.toBitVec = (0 : UInt64).toBitVec := BitVec.eq_of_toNat_eq h.symm
      cases u; simp at h2; subst h2; rfl
  · rename_i x ys
    cases ys
    · have h_back : ({ toList := [x] } : Array UInt64).back? = some x := rfl
      rw [h_back]
      unfold toNatLimbsList
      simp
      constructor
      · intro h; rw [h]
      · intro h; have h2 : x.toBitVec = u.toBitVec := BitVec.eq_of_toNat_eq h
        cases x; cases u; simp at h2; subst h2; rfl
    · rename_i y ys
      have hl_y : (y :: ys).getLast? ≠ some 0 := by
        have hh : ({ toList := x :: y :: ys } : Array UInt64).back? = (x :: y :: ys).getLast? :=
          List.back?_toArray (x :: y :: ys)
        rw [hh] at hl
        have hh2 : (x :: y :: ys).getLast? = (y :: ys).getLast? := rfl
        rw [← hh2]
        exact hl
      simp
      intro hc
      have h_u : u.toNat < 2^64 := UInt64.toNat_lt u
      have h_toNat_y_ys : toNatLimbsList (y :: ys) ≠ 0 := by
        intro h_zero
        have h_nil := toNatLimbsList_eq_zero_of_getLast_ne_zero (y :: ys) hl_y h_zero
        contradiction
      have h_toNat_y_ys_pos : toNatLimbsList (y :: ys) > 0 := Nat.pos_of_ne_zero h_toNat_y_ys
      change toNatLimbsList (y :: ys) * 2^64 + x.toNat = u.toNat at hc
      have h_x_nonneg : x.toNat ≥ 0 := Nat.zero_le _
      omega

@[simp] lemma beqInt64_eq (a : AzNat) (i : Int64) :
  a.beqInt64 i = true ↔ (a.toNat : Int) = i.toInt := by
  unfold beqInt64
  simp only [Bool.and_eq_true, beqUInt64_eq]
  constructor
  · rintro ⟨h1, h2⟩
    change decide (decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = true) = true at h1
    have h1_cast : decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = true := of_decide_eq_true h1
    have h0 : (0 : Int64).toBitVec.toInt = 0 := rfl
    rw [h0] at h1_cast
    have hh_nonneg : 0 ≤ i.toBitVec.toInt := of_decide_eq_true h1_cast
    have h_toInt : i.toInt = i.toBitVec.toInt := rfl
    have h_toNat : (i.toUInt64.toNat : Int) = i.toBitVec.toNat := rfl
    unfold Int64.toInt BitVec.toInt at *
    split_ifs at hh_nonneg
    · omega
    · omega
  · intro h_eq
    have h_toInt : i.toInt = i.toBitVec.toInt := rfl
    have h_toNat : (i.toUInt64.toNat : Int) = i.toBitVec.toNat := rfl
    have hh_nonneg : 0 ≤ i.toBitVec.toInt := by
      rw [← h_toInt, ← h_eq]
      exact Int.natCast_nonneg a.toNat
    have h1_cast : decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = true := by
      have h0 : (0 : Int64).toBitVec.toInt = 0 := rfl
      rw [h0]
      exact decide_eq_true hh_nonneg
    have h1_final : decide (decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = true) = true :=
      decide_eq_true h1_cast
    have h1 : decide (i ≥ 0) = true := by
      change decide (decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = true) = true
      exact h1_final
    refine ⟨h1, ?_⟩
    unfold Int64.toInt BitVec.toInt at *
    split_ifs at hh_nonneg
    · omega
    · omega

end Azurite.AzNat
