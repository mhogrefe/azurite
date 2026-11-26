/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.BlockRem
import Azurite.AzNat.Equiv.Div.Classic
import Azurite.AzNat.Equiv.DivRecursiveLimbs
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ModPow2

/-!
# The blocks of a number modulo a one-limb modulus: the values

`blockRemsLimb_spec`, `blockRemsMod_spec`: the `j`-th entry is `mk` of the remainder of the
`j`-th block (`blockValue`), and there are `n` entries.
-/

namespace Azurite.AzNat

/-- The value of the block of `w` limbs that starts at limb `off + k w`. -/
def blockValue (L : List UInt64) (w off k : ℕ) : ℕ :=
  toNatLimbsList ((L.drop (off + k * w)).take w)

/-- The clamped slice is the block. -/
theorem drop_take_clamp (L : List UInt64) (p w : ℕ) :
    (L.drop (min p L.length)).take (min (p + w) L.length - min p L.length) =
      (L.drop p).take w := by
  by_cases hp : p ≤ L.length
  · rw [Nat.min_eq_left hp]
    by_cases hw : p + w ≤ L.length
    · rw [Nat.min_eq_left hw, Nat.add_sub_cancel_left]
    · rw [Nat.min_eq_right (by omega), List.take_of_length_le (by simp),
        List.take_of_length_le (by simp; omega)]
  · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega), List.drop_of_length_le (by omega),
      List.drop_of_length_le (by omega)]
    simp

/-- One block: the remainder. -/
theorem blockRems_step (d : UInt64) (hd : d ≠ 0) (w off : Nat) (a : Array UInt64) (k : ℕ)
    (hlohi : min (off + k * w) a.size ≤ min (off + k * w + w) a.size)
    (hhia : min (off + k * w + w) a.size ≤ a.size) :
    (modLimbPre a (min (off + k * w) a.size) (min (off + k * w + w) a.size)
      (d <<< UInt64.ofNat (UInt64.leadingZeros d))
      (UInt64.reciprocal (d <<< UInt64.ofNat (UInt64.leadingZeros d))
        (UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros d hd))
      (UInt64.leadingZeros d) hlohi hhia).toNat = blockValue a.toList w off k % d.toNat := by
  rw [modLimbPre_eq]
  have hdiv : toNatLimbsList ((a.toList.drop (min (off + k * w) a.size)).take
        (min (off + k * w + w) a.size - min (off + k * w) a.size)) =
      toNatLimbsList (((divModLimb a _ _ d hd hlohi hhia).1.toList.drop
        (min (off + k * w) a.size)).take
          (min (off + k * w + w) a.size - min (off + k * w) a.size)) *
        d.toNat + (divModLimb a _ _ d hd hlohi hhia).2.toNat ∧
      (divModLimb a _ _ d hd hlohi hhia).2.toNat < d.toNat :=
    divModLimb_toNat a _ _ d hd hlohi hhia
  have hslice : toNatLimbsList ((a.toList.drop (min (off + k * w) a.size)).take
      (min (off + k * w + w) a.size - min (off + k * w) a.size)) = blockValue a.toList w off k := by
    unfold blockValue
    rw [← Array.length_toList, drop_take_clamp]
  obtain ⟨h1, h2⟩ := hdiv
  rw [← hslice, h1, Nat.mul_add_mod_of_lt h2]

theorem blockRemsLimb.go_spec {α : Type} (d : UInt64) (hd : d ≠ 0)
    (mk : (r : UInt64) → r.toNat < d.toNat → α) (w off n : Nat) (a : Array UInt64)
    (s : Nat) (d' inv : UInt64) (hs : s = UInt64.leadingZeros d)
    (hd' : d' = d <<< UInt64.ofNat (UInt64.leadingZeros d))
    (hinv : inv = UInt64.reciprocal (d <<< UInt64.ofNat (UInt64.leadingZeros d))
      (UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros d hd)) :
    ∀ (t : ℕ) (k : ℕ) (out : Array α), n - k = t →
      (blockRemsLimb.go d hd mk w off n a s d' inv hs hd' hinv k out).size =
        out.size + (n - k) ∧
      (∀ i, i < out.size →
        (blockRemsLimb.go d hd mk w off n a s d' inv hs hd' hinv k out)[i]? = out[i]?) ∧
      ∀ j, k ≤ j → j < n → ∃ r hr,
        (blockRemsLimb.go d hd mk w off n a s d' inv hs hd' hinv k out)[out.size + (j - k)]? =
            some (mk r hr) ∧
          r.toNat = blockValue a.toList w off j % d.toNat := by
  subst hs hd' hinv
  intro t
  induction t with
  | zero =>
    intro k out ht
    have hk : ¬ k < n := by omega
    rw [blockRemsLimb.go]
    simp only [hk, ↓reduceIte]
    exact ⟨by omega, by simp, fun j h1 h2 => by omega⟩
  | succ t ih =>
    intro k out ht
    have hk : k < n := by omega
    rw [blockRemsLimb.go]
    simp only [hk, ↓reduceIte]
    have hs3 := blockRems_step d hd w off a k (by omega) (by omega)
    obtain ⟨ih1, ih2, ih3⟩ := ih (k + 1) (out.push (mk _
      (modLimbPre_lt a (min (off + k * w) a.size)
        (min (off + k * w + w) a.size) d hd (by omega) (by omega)))) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [ih1, Array.size_push]
      omega
    · intro i hi'
      rw [ih2 i (by rw [Array.size_push]; omega), Array.getElem?_push_lt hi',
        Array.getElem?_eq_getElem hi']
    · intro j hkj hjn
      by_cases hjk : j = k
      · subst hjk
        refine ⟨_, modLimbPre_lt a (min (off + j * w) a.size)
          (min (off + j * w + w) a.size) d hd (by omega) (by omega), ?_, hs3⟩
        rw [Nat.sub_self, Nat.add_zero, ih2 _ (by rw [Array.size_push]; omega)]
        simp
      · obtain ⟨r, hr, h1, h2⟩ := ih3 j (by omega) hjn
        refine ⟨r, hr, ?_, h2⟩
        rw [← h1, Array.size_push]
        congr 1
        omega

/-- **The remainders of the blocks.** -/
theorem blockRemsLimb_spec {α : Type} (d : UInt64) (hd : d ≠ 0)
    (mk : (r : UInt64) → r.toNat < d.toNat → α) (w off n : Nat) (a : Array UInt64) :
    (blockRemsLimb d hd mk w off n a).size = n ∧
      ∀ j, j < n → ∃ r hr, (blockRemsLimb d hd mk w off n a)[j]? = some (mk r hr) ∧
        r.toNat = blockValue a.toList w off j % d.toNat := by
  unfold blockRemsLimb
  obtain ⟨h1, -, h3⟩ := blockRemsLimb.go_spec d hd mk w off n a _ _ _ rfl rfl rfl n 0
    (Array.mkEmpty n) rfl
  refine ⟨by simpa using h1, fun j hj => ?_⟩
  obtain ⟨r, hr, h4, h5⟩ := h3 j (Nat.zero_le _) hj
  exact ⟨r, hr, by simpa using h4, h5⟩

/-- **The blocks modulo a one-limb `m`.** -/
theorem blockRemsMod_spec {α : Type} (m : AzNat) (h1 : m.limbs.size = 1)
    (mk : (c : AzNat) → c.toNat < m.toNat → α) (w off n : Nat) (a : Array UInt64) :
    (blockRemsMod m h1 mk w off n a).size = n ∧
      ∀ j, j < n → ∃ c hc, (blockRemsMod m h1 mk w off n a)[j]? = some (mk c hc) ∧
        c.toNat = blockValue a.toList w off j % m.toNat := by
  unfold blockRemsMod
  obtain ⟨hs, h⟩ := blockRemsLimb_spec (m.limbs[0]'(by omega))
    (limb_ne_zero_of_size_eq_one m h1)
    (fun r hr => mk (ofLimbs #[r]) (by
      rw [toNat_ofLimbs, toNat_of_size_eq_one m h1]
      simpa [toNatLimbsList] using hr)) w off n a
  refine ⟨hs, fun j hj => ?_⟩
  obtain ⟨r, hr, h1', h2'⟩ := h j hj
  refine ⟨ofLimbs #[r], _, h1', ?_⟩
  rw [toNat_ofLimbs, toNat_of_size_eq_one m h1, ← h2']
  simp [toNatLimbsList]

end Azurite.AzNat
