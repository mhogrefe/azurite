import Azurite.AzNat.Size
import Azurite.AzNat.Equiv.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

namespace Azurite.AzNat



lemma size_mul_add (a k b : Nat) (ha : 0 < a) (hb : b < 2^k) : (a * 2^k + b).size = a.size + k := by
  apply le_antisymm
  · rw [Nat.size_le, Nat.pow_add]
    have h1 : a < 2^a.size := by rw [← Nat.size_le]
    have h2 : a * 2^k + b < a * 2^k + 2^k := Nat.add_lt_add_left hb _
    have h3 : a * 2^k + 2^k = (a + 1) * 2^k := by ring
    rw [h3] at h2
    have h4 : (a + 1) * 2^k ≤ 2^a.size * 2^k := Nat.mul_le_mul_right _ h1
    exact Nat.lt_of_lt_of_le h2 h4
  · have hk : a.size + k - 1 = a.size - 1 + k := by
      have hs : a.size > 0 := by
        by_contra hc
        have hc1 : a.size = 0 := by omega
        have hc2 : a.size ≤ 0 := by omega
        have hc3 : a < 2^0 := Nat.size_le.mp hc2
        have hc4 : a < 1 := hc3
        omega
      omega
    have ha1 : 2^(a.size - 1) ≤ a := by
      by_contra hc
      have hc1 : a < 2^(a.size - 1) := by omega
      have hc2 : a.size ≤ a.size - 1 := (Nat.size_le).mpr hc1
      have hs : a.size > 0 := by
        by_contra hcc
        have hc1' : a.size = 0 := by omega
        have hc2' : a.size ≤ 0 := by omega
        have hc3' : a < 2^0 := Nat.size_le.mp hc2'
        have hc4' : a < 1 := hc3'
        omega
      omega
    have step2 : 2^(a.size - 1) * 2^k ≤ a * 2^k := Nat.mul_le_mul_right _ ha1
    have step3 : a * 2^k ≤ a * 2^k + b := Nat.le_add_right _ _
    have step4 : 2^(a.size - 1) * 2^k ≤ a * 2^k + b := le_trans step2 step3
    by_contra hc
    have hlt : (a * 2^k + b).size < a.size + k := by omega
    have hle : (a * 2^k + b).size ≤ a.size + k - 1 := by omega
    have hlt2 : a * 2^k + b < 2^(a.size + k - 1) := Nat.size_le.mp hle
    rw [hk, Nat.pow_add] at hlt2
    omega

lemma toNatLimbsList_append_singleton (l : List UInt64) (x : UInt64) :
  toNatLimbsList (l ++ [x]) = x.toNat * 2 ^ (64 * l.length) + toNatLimbsList l := by
  have hl1 := toNatLimbsList_append l [x]
  have hl2 : toNatLimbsList [x] = x.toNat := by
    unfold toNatLimbsList
    simp
  rw [hl2] at hl1
  exact hl1

lemma uint64_size_eq_log2_add_one (x : UInt64) (hx : x.toNat ≠ 0) :
  x.toNat.size = x.log2.toNat + 1 := by
  have hl : x.log2.toNat = Nat.log2 x.toNat := rfl
  rw [hl, Nat.log2_eq_log_two]
  have h1 : 2 ^ (Nat.log 2 x.toNat) ≤ x.toNat := Nat.pow_log_le_self 2 hx
  have h2 : x.toNat < 2 ^ (Nat.log 2 x.toNat + 1) := Nat.lt_pow_succ_log_self (by decide) x.toNat
  have hs1 : x.toNat.size ≤ Nat.log 2 x.toNat + 1 := Nat.size_le.mpr h2
  have hs2 : Nat.log 2 x.toNat < x.toNat.size := Nat.lt_size.mpr h1
  omega

lemma size_toNatLimbsList (l : List UInt64) (hl : l ≠ []) (hx : (l.getLast hl).toNat ≠ 0) :
  (toNatLimbsList l).size = (l.length - 1) * 64 + (l.getLast hl).toNat.size := by
  have heq : l = l.dropLast ++ [l.getLast hl] := (List.dropLast_append_getLast hl).symm
  have hlen1 : l.length = l.dropLast.length + 1 := by
    have hl_len := congr_arg List.length heq
    rw [List.length_append, List.length_singleton] at hl_len
    exact hl_len
  have hlen2 : l.dropLast.length = l.length - 1 := by omega
  have htoNat : toNatLimbsList l = (l.getLast hl).toNat * 2 ^ (64 * l.dropLast.length) + toNatLimbsList l.dropLast := by
    nth_rw 1 [heq]
    apply toNatLimbsList_append_singleton
  rw [htoNat]
  have ha : 0 < (l.getLast hl).toNat := by omega
  have hb : toNatLimbsList l.dropLast < 2 ^ (64 * l.dropLast.length) := toNatLimbsList_lt_pow l.dropLast
  have h_size := size_mul_add ((l.getLast hl).toNat) (64 * l.dropLast.length) (toNatLimbsList l.dropLast) ha hb
  rw [h_size, hlen2]
  omega

lemma size_toNat (n : AzNat) : n.toNat.size = n.size := by
  have hsz : n.limbs.size > 0 ∨ n.limbs.size = 0 := by omega
  rcases hsz with hsz_pos | hsz_zero
  · let s := n.limbs.size - 1
    unfold toNat
    have hl : n.limbs.toList ≠ [] := by
      intro hc
      have hlen : n.limbs.toList.length = 0 := by rw [hc]; rfl
      have hl2 : n.limbs.size = 0 := by rw [←Array.length_toList]; exact hlen
      omega
    have h_last : n.limbs.toList.getLast hl = n.limbs[s] := by
      have hlen : n.limbs.toList.length = n.limbs.size := Array.length_toList
      have hel : n.limbs.toList.getLast hl = n.limbs.toList.get ⟨s, by omega⟩ := by
        rw [List.getLast_eq_getElem hl]
        congr 1
      rw [hel]
      exact Array.getElem_toList (by omega)
    have hx2 : n.limbs[s].toNat ≠ 0 := by
      have h_last_nz : n.limbs.back? ≠ some 0 := n.last_ne_zero
      have h_back : n.limbs.back? = some n.limbs[s] := by
        change n.limbs[n.limbs.size - 1]? = some n.limbs[s]
        change n.limbs[s]? = some n.limbs[s]
        exact Array.getElem?_eq_getElem (by omega)
      rw [h_back] at h_last_nz
      intro h_err
      have h_zero : n.limbs[s] = 0 := by
        ext
        exact h_err
      have hc : some n.limbs[s] = some 0 := congrArg Option.some h_zero
      exact h_last_nz hc
    have hx : (n.limbs.toList.getLast hl).toNat ≠ 0 := by rw [h_last]; exact hx2
    have hl_len : n.limbs.toList.length = n.limbs.size := Array.length_toList
    have h_size := size_toNatLimbsList n.limbs.toList hl hx
    rw [h_last, hl_len] at h_size
    have h_log2 := uint64_size_eq_log2_add_one (n.limbs[s]) hx2
    
    unfold AzNat.size
    dsimp only
    rw [dif_pos hsz_pos]
    rw [h_size, h_log2]
    rfl
  · unfold toNat
    have hl : n.limbs.toList = [] := by
      have h1 : n.limbs.toList.length = n.limbs.size := Array.length_toList
      rw [hsz_zero] at h1
      exact List.length_eq_zero_iff.mp h1
    rw [hl]
    unfold AzNat.size
    dsimp only
    rw [dif_neg (by omega)]
    rfl

lemma size_ofNat (n : Nat) : (ofNat n).size = n.size := by
  have h := size_toNat (ofNat n)
  have ht := toNat_ofNat n
  rw [ht] at h
  exact h.symm

end Azurite.AzNat
