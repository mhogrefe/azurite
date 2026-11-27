/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.IsPrimeLucas
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.IsPrimeWord
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.Sub
import Mathlib.NumberTheory.LucasPrimality

/-!
# Soundness of the primality certificates by the factorization of `n − 1`

**`lucasCertified_prime`**: `lucasCertified fuel n = true → Nat.Prime n.toNat`, by Lucas's
test (`lucas_primality` of Mathlib).  The proposal of `lucasHint` is not part of the
argument: `lucasCheck` computes the product of the proposed factors and the powers in
`AzZMod n`, and the factors are certified in turn.
-/

namespace Azurite.AzNat

private theorem toNat_one₃ : (1 : AzNat).toNat = 1 := by decide

theorem toNat_listProd (l : List AzNat) : (listProd l).toNat = (l.map toNat).prod := by
  have key : ∀ (l : List AzNat) (a : AzNat),
      (l.foldl (· * ·) a).toNat = a.toNat * (l.map toNat).prod := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons b l ih =>
      intro a
      rw [List.foldl_cons, ih, toNat_mul, List.map_cons, List.prod_cons, mul_assoc]
  rw [listProd, key, toNat_one₃, one_mul]

/-- The one-word test on an `AzNat` of at most 32 bits. -/
theorem isPrimeWord_toUInt64 {n : AzNat} (h32 : n.size ≤ 32) {b : Bool}
    (hw : isPrimeWord n.toUInt64 = some b) : b = true ↔ Nat.Prime n.toNat := by
  have hlt : n.toNat < 2 ^ 32 := by
    rw [← size_toNat] at h32
    exact lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) h32)
  have hto : n.toUInt64.toNat = n.toNat := by
    rw [toUInt64_toNat]
    show n.toNat % 2 ^ 64 = n.toNat
    exact Nat.mod_eq_of_lt (by omega)
  have := isPrimeWord_eq_some hw
  rwa [hto] at this

/-- **Lucas's test, checked**: if `lucasCheck n a l` holds and every element of `l` is prime,
then `n` is prime. -/
theorem lucasCheck_prime {n : AzNat} [NeZero n.toNat] {a : AzNat} {l : List AzNat}
    (h : lucasCheck n a l = true) (hl : ∀ q ∈ l, q.toNat.Prime) : Nat.Prime n.toNat := by
  unfold lucasCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hprod, hpow⟩, hq⟩ := h
  have hprod' : (l.map toNat).prod = n.toNat - 1 := by
    rw [← toNat_listProd, hprod, toNat_sub, toNat_one₃]
  apply lucas_primality n.toNat (AzZMod.toZMod (AzZMod.ofAzNat n a))
  · have := congrArg AzZMod.toZMod hpow
    rwa [AzZMod.toZMod_powAzNat, AzZMod.toZMod_one, toNat_sub, toNat_one₃] at this
  · intro q hqp hqd
    rw [← hprod'] at hqd
    obtain ⟨r, hr, hqr⟩ := (Prime.dvd_prod_iff hqp.prime).1 hqd
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hr
    have heq : q = q'.toNat := (Nat.prime_dvd_prime_iff_eq hqp (hl q' hq')).1 hqr
    have hne := hq q' (List.mem_dedup.2 hq')
    intro hone
    apply hne
    apply AzZMod.toZMod_injective
    rw [AzZMod.toZMod_powAzNat, AzZMod.toZMod_one, toNat_div, toNat_sub, toNat_one₃, ← heq]
    exact hone

/-- **A certificate proves primality.** -/
theorem lucasCertified_prime : ∀ (fuel : ℕ) (n : AzNat), lucasCertified fuel n = true →
    Nat.Prime n.toNat := by
  intro fuel
  induction fuel with
  | zero => intro n h; simp [lucasCertified] at h
  | succ fuel ih =>
    intro n h
    rw [lucasCertified] at h
    split_ifs at h with h32 h63 h0
    · rw [beq_iff_eq] at h
      exact (isPrimeWord_toUInt64 h32 h).1 rfl
    · have : NeZero n.toNat := ⟨h0⟩
      rcases hh : lucasHint n.toUInt64 with _ | ⟨a, l⟩
      · rw [hh] at h
        cases h
      · rw [hh] at h
        simp only [Bool.and_eq_true, List.all_eq_true] at h
        refine lucasCheck_prime h.1 (fun q hq => ih q (h.2 q (List.mem_dedup.2 hq)))

end Azurite.AzNat
