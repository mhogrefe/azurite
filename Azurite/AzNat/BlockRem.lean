/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div.Schoolbook
import Azurite.AzNat.Div.Classic
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.Equiv.Div.DivModLimb
import Azurite.AzNat.Equiv.ShiftRight

/-!
# The blocks of a number modulo a one-limb modulus

`blockRemsLimb d hd mk w off n a` is the array of the remainders modulo the limb `d` of the
`n` blocks of `w` limbs of `a` that start at limb `off` (block `k` is the limbs
`off + k w, …, off + k w + w − 1`; limbs past the end count as zero), each wrapped by `mk`
together with the proof that it is below `d`.  Each block is reduced where it lies by the
loop of the one-limb division `divModLimb` without its quotient (`modLimbPre`, equal to the
remainder of `divModLimb` by `modLimbPre_eq`): no block is copied, nothing is written.

Used to read the coefficients of a Kronecker product modulo a one-limb modulus
(`AzPolynomial/Kronecker.lean`).  The values are in `Equiv/BlockRem.lean`.
-/

namespace Azurite.AzNat

theorem divModLimb_snd_lt (a : Array UInt64) (lo hi : Nat) (d : UInt64) (hd : d ≠ 0)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    (divModLimb a lo hi d hd hlo hhi).2.toNat < d.toNat :=
  (divModLimb_toNat a lo hi d hd hlo hhi).2

/-- The loop of `divModLimb.go` without the quotient: the running remainder only, the
array is not written. -/
def modLimbLoop (d' inv : UInt64) (k : Nat) (a : Array UInt64) (lo j : Nat) (r : UInt64)
    (hbnd : lo + j ≤ a.size) : UInt64 :=
  match j with
  | 0 => r
  | j + 1 =>
    have h_idx : lo + j < a.size := by omega
    let u_j := a[lo + j]
    let u_carry : UInt64 :=
      if k = 0 then 0
      else if hj0 : j = 0 then 0
      else
        have hjp : lo + j - 1 < a.size := by omega
        a[lo + j - 1]'hjp >>> UInt64.ofNat (64 - k)
    let u_j_shifted := (u_j <<< UInt64.ofNat k) ||| u_carry
    modLimbLoop d' inv k a lo j (UInt64.div2By1 r u_j_shifted d' inv).2 (by omega)

/-- The remainder of the slice `a[lo:hi)` modulo a limb `d`, from the precomputed shift
`k = leadingZeros d`, normalized divisor `d' = d <<< k` and reciprocal `inv` of `d'`: the
second component of `divModLimb` (`modLimbPre_eq`), without writing the quotient. -/
def modLimbPre (a : Array UInt64) (lo hi : Nat) (d' inv : UInt64) (k : Nat)
    (_hlo : lo ≤ hi) (hhi : hi ≤ a.size) : UInt64 :=
  let len := hi - lo
  let r0 : UInt64 :=
    if k = 0 then 0
    else if hlen0 : len = 0 then 0
    else
      have h_top : hi - 1 < a.size := by omega
      a[hi - 1]'h_top >>> UInt64.ofNat (64 - k)
  modLimbLoop d' inv k a lo len r0 (by omega) >>> UInt64.ofNat k

theorem modLimbLoop_eq (d' inv : UInt64) (k : Nat) (hk : k ≤ 63) (a : Array UInt64)
    (lo j : Nat) :
    ∀ (a' : Array UInt64) (r : UInt64) (hbnd : lo + j ≤ a.size) (hbnd' : lo + j ≤ a'.size),
      (∀ i (h : i < lo + j), a'[i]'(by omega) = a[i]'(by omega)) →
      modLimbLoop d' inv k a lo j r hbnd = (divModLimb.go d' inv k hk a' lo j r hbnd').2 := by
  induction j with
  | zero =>
    intro a' r hbnd hbnd' _
    rw [modLimbLoop, divModLimb.go]
  | succ j ih =>
    intro a' r hbnd hbnd' hag
    rw [modLimbLoop, divModLimb.go]
    dsimp only
    have h1 : a'[lo + j]'(by omega) = a[lo + j]'(by omega) := hag _ (by omega)
    have h2 : (if k = 0 then (0 : UInt64) else if hj0 : j = 0 then 0
        else a'[lo + j - 1]'(by omega) >>> UInt64.ofNat (64 - k)) =
        (if k = 0 then (0 : UInt64) else if hj0 : j = 0 then 0
        else a[lo + j - 1]'(by omega) >>> UInt64.ofNat (64 - k)) := by
      split
      · rfl
      · split
        · rfl
        · rw [hag _ (by omega)]
    simp only [h1, h2]
    apply ih
    intro i h
    rw [Array.getElem_set_ne (h := by omega)]
    exact hag i (by omega)

/-- `modLimbPre` with the data of `d` is the remainder of `divModLimb`. -/
theorem modLimbPre_eq (a : Array UInt64) (lo hi : Nat) (d : UInt64) (hd : d ≠ 0)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    modLimbPre a lo hi (d <<< UInt64.ofNat (UInt64.leadingZeros d))
      (UInt64.reciprocal (d <<< UInt64.ofNat (UInt64.leadingZeros d))
        (UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros d hd))
      (UInt64.leadingZeros d) hlo hhi = (divModLimb a lo hi d hd hlo hhi).2 := by
  unfold modLimbPre divModLimb
  dsimp only
  rw [modLimbLoop_eq _ _ _ (UInt64.leadingZeros_le d hd) a lo (hi - lo) a _ _ _ (fun _ _ => rfl)]

theorem modLimbPre_lt (a : Array UInt64) (lo hi : Nat) (d : UInt64) (hd : d ≠ 0)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    (modLimbPre a lo hi (d <<< UInt64.ofNat (UInt64.leadingZeros d))
      (UInt64.reciprocal (d <<< UInt64.ofNat (UInt64.leadingZeros d))
        (UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros d hd))
      (UInt64.leadingZeros d) hlo hhi).toNat < d.toNat := by
  rw [modLimbPre_eq]
  exact divModLimb_snd_lt a lo hi d hd hlo hhi

/-- The loop of `blockRemsLimb`: blocks `k, …, n − 1`, with the shift `s`, the normalized
divisor `d'` and its reciprocal `inv` computed once. -/
def blockRemsLimb.go {α : Type} (d : UInt64) (hd : d ≠ 0)
    (mk : (r : UInt64) → r.toNat < d.toNat → α) (w off n : Nat) (a : Array UInt64)
    (s : Nat) (d' inv : UInt64) (hs : s = UInt64.leadingZeros d)
    (hd' : d' = d <<< UInt64.ofNat (UInt64.leadingZeros d))
    (hinv : inv = UInt64.reciprocal (d <<< UInt64.ofNat (UInt64.leadingZeros d))
      (UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros d hd)) (k : Nat)
    (out : Array α) : Array α :=
  if k < n then
    let lo := min (off + k * w) a.size
    let hi := min (off + k * w + w) a.size
    have hlo : lo ≤ hi := by omega
    have hhi : hi ≤ a.size := by omega
    blockRemsLimb.go d hd mk w off n a s d' inv hs hd' hinv (k + 1)
      (out.push (mk (modLimbPre a lo hi d' inv s hlo hhi)
        (by subst hs hd' hinv; exact modLimbPre_lt a lo hi d hd hlo hhi)))
  else out
  termination_by n - k

/-- **The remainders modulo `d` of `n` blocks of `w` limbs** of `a`, from limb `off` on. -/
def blockRemsLimb {α : Type} (d : UInt64) (hd : d ≠ 0)
    (mk : (r : UInt64) → r.toNat < d.toNat → α) (w off n : Nat) (a : Array UInt64) : Array α :=
  blockRemsLimb.go d hd mk w off n a (UInt64.leadingZeros d)
    (d <<< UInt64.ofNat (UInt64.leadingZeros d))
    (UInt64.reciprocal (d <<< UInt64.ofNat (UInt64.leadingZeros d))
      (UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros d hd)) rfl rfl rfl 0 (Array.mkEmpty n)

/-- The limb of a one-limb number is not zero. -/
theorem limb_ne_zero_of_size_eq_one (m : AzNat) (h1 : m.limbs.size = 1) :
    m.limbs[0]'(by omega) ≠ 0 := by
  intro h
  apply m.last_ne_zero
  rw [Array.back?_eq_getElem?, show m.limbs.size - 1 = 0 from by omega,
    Array.getElem?_eq_getElem (by omega)]
  exact congrArg some h

/-- The value of a one-limb number. -/
theorem toNat_of_size_eq_one (m : AzNat) (h1 : m.limbs.size = 1) :
    m.toNat = (m.limbs[0]'(by omega)).toNat := by
  have hl : m.limbs.toList = [m.limbs[0]'(by omega)] := by
    apply List.ext_getElem
    · simp [h1]
    · intro i h1' h2'
      have : i = 0 := by simp at h2'; omega
      subst this
      simp
  show toNatLimbsList m.limbs.toList = _
  rw [hl]
  simp [toNatLimbsList]

/-- **The blocks of `a` modulo a one-limb `m`**, as numbers below `m`. -/
def blockRemsMod {α : Type} (m : AzNat) (h1 : m.limbs.size = 1)
    (mk : (c : AzNat) → c.toNat < m.toNat → α) (w off n : Nat) (a : Array UInt64) : Array α :=
  blockRemsLimb (m.limbs[0]'(by omega)) (limb_ne_zero_of_size_eq_one m h1)
    (fun r hr => mk (ofLimbs #[r]) (by
      rw [toNat_ofLimbs, toNat_of_size_eq_one m h1]
      simpa [toNatLimbsList] using hr)) w off n a

#guard blockRemsLimb 7 (by decide) (fun r _ => r) 1 0 3 #[10, 20, 30] == #[3, 6, 2]
#guard blockRemsLimb 7 (by decide) (fun r _ => r) 1 1 3 #[10, 20, 30] == #[6, 2, 0]
#guard blockRemsLimb 1000003 (by decide) (fun r _ => r.toNat) 2 0 3
    (ofNat (123456789 + 2 ^ 128 * (2 ^ 100 + 17) + 2 ^ 256 * 999)).limbs
  == #[123456789 % 1000003, (2 ^ 100 + 17) % 1000003, 999]
#guard blockRemsLimb 1000003 (by decide) (fun r _ => r.toNat) 2 1 2
    (ofNat (123456789 + 2 ^ 64 * (2 ^ 100 + 17) + 2 ^ 192 * 999)).limbs
  == #[(2 ^ 100 + 17) % 1000003, 999]
#guard blockRemsLimb 5 (by decide) (fun r _ => r) 3 0 0 #[10, 20, 30] == #[]

end Azurite.AzNat
