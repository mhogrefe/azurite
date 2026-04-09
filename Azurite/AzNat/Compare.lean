import Azurite.AzNat.Basic

namespace Azurite.AzNat

def compareLimbsLoop (a b : Array UInt64) (lo k : Nat)
    (ha : lo + k ≤ a.size) (hb : lo + k ≤ b.size) : Ordering :=
  match k with
  | 0 => Ordering.eq
  | k + 1 =>
    have hai : lo + k < a.size := by omega
    have hbi : lo + k < b.size := by omega
    match Ord.compare a[lo + k] b[lo + k] with
    | Ordering.eq => compareLimbsLoop a b lo k (by omega) (by omega)
    | ord => ord

def compareLimbs (a b : Array UInt64) (lo hi : Nat)
    (hlo : lo ≤ hi) (ha : hi ≤ a.size) (hb : hi ≤ b.size) : Ordering :=
  compareLimbsLoop a b lo (hi - lo) (by omega) (by omega)

def compareLoop (a b : AzNat) (i : Nat) (hi : i < a.limbs.size)
    (hs : a.limbs.size = b.limbs.size) : Ordering :=
  have hib : i < b.limbs.size := hs ▸ hi
  match Ord.compare a.limbs[i] b.limbs[i] with
  | Ordering.eq => match i with
    | 0 => Ordering.eq
    | i + 1 => compareLoop a b i (by omega) hs
  | ord => ord

@[simp] theorem compareLimbsLoop_zero (a b : Array UInt64) (lo : Nat)
    (ha : lo ≤ a.size) (hb : lo ≤ b.size) :
    compareLimbsLoop a b lo 0 ha hb = Ordering.eq := by
  unfold compareLimbsLoop; rfl

theorem compareLoop_eq_compareLimbsLoop (a b : AzNat) (i : Nat)
    (hi : i < a.limbs.size) (hs : a.limbs.size = b.limbs.size) :
    compareLoop a b i hi hs =
      compareLimbsLoop a.limbs b.limbs 0 (i + 1) (by omega) (by omega) := by
  induction i with
  | zero =>
    unfold compareLoop compareLimbsLoop
    simp [compareLimbsLoop]
  | succ i ih =>
    unfold compareLoop compareLimbsLoop
    simp
    split
    · rename_i heq; simp [heq]; exact ih (by omega)
    · simp

def compare (a b : AzNat) : Ordering :=
  match h : Ord.compare a.limbs.size b.limbs.size with
  | Ordering.eq =>
    have hs : a.limbs.size = b.limbs.size := Nat.compare_eq_eq.mp h
    compareLimbs a.limbs b.limbs 0 a.limbs.size (by omega) (by omega) (by omega)
  | ord => ord

theorem compare_eq_old (a b : AzNat) :
    compare a b =
      match h : Ord.compare a.limbs.size b.limbs.size with
      | Ordering.eq =>
        have hs : a.limbs.size = b.limbs.size := Nat.compare_eq_eq.mp h
        match h2 : a.limbs.size with
        | 0 => Ordering.eq
        | x + 1 => compareLoop a b x (by omega) hs
      | ord => ord := by
  unfold compare compareLimbs
  split
  · rename_i h_cmp
    have hs : a.limbs.size = b.limbs.size := Nat.compare_eq_eq.mp h_cmp
    split
    · rename_i h_sz
      simp [h_sz]
    · rename_i x h_sz
      simp only [Nat.sub_zero, h_sz]
      rw [← compareLoop_eq_compareLimbsLoop]
  · rfl

instance instOrdAzNat : Ord AzNat where
  compare := compare

instance : LE AzNat where le a b := compare a b ≠ Ordering.gt
instance : LT AzNat where lt a b := compare a b = Ordering.lt

instance : DecidableRel (α := AzNat) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (compare a b ≠ Ordering.gt))

instance : DecidableRel (α := AzNat) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (compare a b = Ordering.lt))

instance : Max AzNat where max a b := if a ≤ b then b else a
instance : Min AzNat where min a b := if a ≤ b then a else b

end Azurite.AzNat
