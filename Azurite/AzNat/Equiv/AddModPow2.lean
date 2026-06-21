import Azurite.AzNat.AddModPow2
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.UInt64.Equiv.AddWithCarry
import Mathlib.Tactic.LinearCombination

/-!
## Correctness of `AzNat.addModPow2`

`(addModPow2 a b k).toNat = (a.toNat + b.toNat) % 2 ^ k`.
-/

namespace Azurite.AzNat

/-- Padded chunk: the value of limbs `[i, L)` of `arr`, reading `0` past the end. -/
private def chunkP (arr : Array UInt64) (i L : Nat) : Nat :=
  if i < L then (arr[i]?.getD 0).toNat + chunkP arr (i + 1) L * 2 ^ 64 else 0
termination_by L - i

/-- `chunkP` reads the low `[i, L)` limbs, i.e. it is the value of the
    corresponding `take`/`drop` slice. -/
private lemma chunkP_eq_slice (arr : Array UInt64) (i L : Nat) :
    chunkP arr i L = toNatLimbsList ((arr.toList.drop i).take (L - i)) := by
  induction h_sub : L - i generalizing i with
  | zero =>
    have h_ge : L ≤ i := by omega
    rw [chunkP]; simp only [Nat.not_lt.mpr h_ge, ↓reduceIte]
    simp [List.take_zero, toNatLimbsList]
  | succ n ih =>
    have h_lt : i < L := by omega
    rw [chunkP]; simp only [h_lt, ↓reduceIte]
    rw [ih (i + 1) (by omega)]
    by_cases hi : i < arr.size
    · have hlt : i < arr.toList.length := by rwa [Array.length_toList]
      rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons, toNatLimbsList_cons]
      rw [Array.getElem?_eq_getElem hi]
      rw [show arr.toList[i] = arr[i] from (Array.getElem_toList hi).symm]
      simp only [Option.getD_some]
      ring
    · -- past the end: read is 0 and the drop is empty.
      rw [Array.getElem?_eq_none (by omega)]
      have hd : arr.toList.drop i = [] := by
        rw [List.drop_eq_nil_iff]; rw [Array.length_toList]; omega
      have hd1 : arr.toList.drop (i + 1) = [] := by
        rw [List.drop_eq_nil_iff]; rw [Array.length_toList]; omega
      simp [hd, hd1, toNatLimbsList]

/-- `chunkP arr 0 L` truncates `arr` to its low `L` limbs, i.e. `arr.toNat`
    reduced mod `2 ^ (64 * L)`. -/
private lemma chunkP_zero (arr : Array UInt64) (L : Nat) :
    chunkP arr 0 L = toNatLimbsList arr.toList % 2 ^ (64 * L) := by
  rw [chunkP_eq_slice, Nat.sub_zero, List.drop_zero]
  by_cases hL : L ≤ arr.toList.length
  · have h_td := toNatLimbsList_take_drop arr.toList L hL
    have h_lt : toNatLimbsList (arr.toList.take L) < 2 ^ (64 * L) := by
      have := toNatLimbsList_lt_pow (arr.toList.take L)
      rwa [List.length_take, Nat.min_eq_left hL] at this
    rw [h_td, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_lt]
  · rw [List.take_of_length_le (by omega)]
    rw [Nat.mod_eq_of_lt]
    have := toNatLimbsList_lt_pow arr.toList
    calc toNatLimbsList arr.toList < 2 ^ (64 * arr.toList.length) := this
      _ ≤ 2 ^ (64 * L) := Nat.pow_le_pow_right (by decide) (by omega)

/-- The number of limbs produced by `lowSumLimbs`: one per iteration. -/
private lemma lowSumLimbs_size (a b : Array UInt64) (L i : Nat) (carry : Bool)
    (acc : Array UInt64) :
    (lowSumLimbs a b L i carry acc).size = acc.size + (L - i) := by
  induction h_sub : L - i generalizing i carry acc with
  | zero =>
    have h_ge : L ≤ i := by omega
    rw [lowSumLimbs]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < L := by omega
    rw [lowSumLimbs]
    simp only [h_lt, ↓reduceIte]
    rw [ih (i + 1) _ _ (by omega)]
    rw [Array.size_push]
    omega

/-- The go-loop invariant for `lowSumLimbs`.  `acc` already holds the low limbs;
    the remaining limbs `[i, L)` of `a` and `b` plus the incoming carry produce
    the rest, with the final carry-out dropped (hence the `% 2 ^ (64 * size)`). -/
private lemma lowSumLimbs_correct (a b : Array UInt64) (L i : Nat) (carry : Bool)
    (acc : Array UInt64) :
    toNatLimbsList (lowSumLimbs a b L i carry acc).toList
      = (toNatLimbsList acc.toList
          + (carry.toNat + chunkP a i L + chunkP b i L) * 2 ^ (64 * acc.size))
        % 2 ^ (64 * (acc.size + (L - i))) := by
  induction h_sub : L - i generalizing i carry acc with
  | zero =>
    have h_ge : L ≤ i := by omega
    rw [lowSumLimbs]; simp only [Nat.not_lt.mpr h_ge, ↓reduceIte]
    have hCA : chunkP a i L = 0 := by rw [chunkP]; simp [Nat.not_lt.mpr h_ge]
    have hCB : chunkP b i L = 0 := by rw [chunkP]; simp [Nat.not_lt.mpr h_ge]
    rw [hCA, hCB]
    have h_lt : toNatLimbsList acc.toList < 2 ^ (64 * acc.size) := by
      have := toNatLimbsList_lt_pow acc.toList
      rwa [Array.length_toList] at this
    simp only [Nat.add_zero]
    -- carry contributes carry.toNat * 2^(64*acc.size), which mod 2^(64*acc.size) is 0.
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_lt]
  | succ n ih =>
    have h_lt : i < L := by omega
    rw [lowSumLimbs]
    simp only [h_lt, ↓reduceIte]
    set awc := UInt64.addWithCarry (a[i]?.getD 0) (b[i]?.getD 0) carry with hawc
    have h_rec : L - (i + 1) = n := by omega
    rw [ih (i + 1) awc.2 (acc.push awc.1) h_rec]
    -- The per-limb add equation.
    have h_awc := UInt64.addWithCarry_eq (a[i]?.getD 0) (b[i]?.getD 0) carry
    rw [← hawc] at h_awc
    -- Expand chunkP at i.
    have hCA : chunkP a i L = (a[i]?.getD 0).toNat + chunkP a (i + 1) L * 2 ^ 64 := by
      rw [chunkP]; simp only [h_lt, ↓reduceIte]
    have hCB : chunkP b i L = (b[i]?.getD 0).toNat + chunkP b (i + 1) L * 2 ^ 64 := by
      rw [chunkP]; simp only [h_lt, ↓reduceIte]
    rw [hCA, hCB]
    -- acc.push: toNatLimbsList and size.
    rw [show (acc.push awc.1).toList = acc.toList ++ [awc.1] from Array.toList_push]
    rw [toNatLimbsList_append_singleton, Array.length_toList, Array.size_push]
    -- Moduli agree.
    rw [show acc.size + 1 + n = acc.size + (n + 1) from by omega]
    -- Set up powers.
    have h_pow : (2 : Nat) ^ (64 * (acc.size + 1)) = 2 ^ (64 * acc.size) * 2 ^ 64 := by
      rw [show 64 * (acc.size + 1) = 64 * acc.size + 64 from by ring, Nat.pow_add]
    set M := (2 : Nat) ^ (64 * (acc.size + (n + 1))) with hM
    set P := (2 : Nat) ^ (64 * acc.size) with hP
    set aR := (a[i]?.getD 0).toNat with haR
    set bR := (b[i]?.getD 0).toNat with hbR
    set CA := chunkP a (i + 1) L with hCAd
    set CB := chunkP b (i + 1) L with hCBd
    have h_cT : (if carry then 1 else 0) = carry.toNat := by cases carry <;> simp
    have h_cN : (if awc.2 then 1 else 0) = awc.2.toNat := by cases awc.2 <;> simp
    rw [h_cT, h_cN] at h_awc
    have key : aR + bR + carry.toNat = awc.2.toNat * 2 ^ 64 + awc.1.toNat := h_awc
    -- Numerators agree as Nats, so the two mods are equal.
    have h_num :
        awc.1.toNat * P + toNatLimbsList acc.toList
            + (awc.2.toNat + CA + CB) * (2 : Nat) ^ (64 * (acc.size + 1))
          = toNatLimbsList acc.toList
            + (carry.toNat + (aR + CA * 2 ^ 64) + (bR + CB * 2 ^ 64)) * P := by
      rw [h_pow]; linear_combination (P : ℕ) * key.symm
    rw [h_num]

/-- **Correctness of `addModPow2`.** The fused add-and-mask equals
    `(a.toNat + b.toNat) % 2 ^ k`. -/
theorem toNat_addModPow2 (a b : AzNat) (k : Nat) :
    (addModPow2 a b k).toNat = (a.toNat + b.toNat) % 2 ^ k := by
  set L := (k + 63) / 64 with hL
  -- `s` = the low-`L`-limb sum array.
  set s := lowSumLimbs a.limbs b.limbs L 0 false #[] with hs
  -- Invariant at i = 0, acc = #[], carry = false.
  have h_inv := lowSumLimbs_correct a.limbs b.limbs L 0 false #[]
  rw [← hs] at h_inv
  have h_empty : toNatLimbsList (#[] : Array UInt64).toList = 0 := by
    simp [toNatLimbsList]
  rw [h_empty, Array.size_empty, Nat.sub_zero, Nat.zero_add] at h_inv
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at h_inv
  rw [show (false : Bool).toNat = 0 from rfl, Nat.zero_add] at h_inv
  rw [show (0 + L) = L from Nat.zero_add L] at h_inv
  -- chunkP at 0 = truncations.
  rw [chunkP_zero a.limbs L, chunkP_zero b.limbs L] at h_inv
  -- `addModPow2 = modPow2 (ofLimbs s) k`.
  show (modPow2 (ofLimbs s) k).toNat = (a.toNat + b.toNat) % 2 ^ k
  rw [toNat_modPow2, toNat_ofLimbs]
  rw [h_inv]
  -- Now reduce the nested mods.  `2 ^ k ∣ 2 ^ (64 * L)`.
  have hkL : k ≤ 64 * L := by rw [hL]; omega
  have hdvd : (2 : Nat) ^ k ∣ 2 ^ (64 * L) := Nat.pow_dvd_pow 2 hkL
  set A := toNatLimbsList a.limbs.toList with hA
  set B := toNatLimbsList b.limbs.toList with hB
  have hAtoNat : A = a.toNat := rfl
  have hBtoNat : B = b.toNat := rfl
  rw [hAtoNat, hBtoNat]
  -- `((A % M + B % M) % M) % 2^k = (A + B) % 2^k`, with `2^k ∣ M`.
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod (a.toNat % _) (b.toNat % _),
    Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd, ← Nat.add_mod]

end Azurite.AzNat
