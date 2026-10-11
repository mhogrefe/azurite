/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Primorial
import Azurite.AzNat.Equiv.SumProduct
import Azurite.Algorithm.Equiv.PrimeSieve
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting

/-!
## Correctness of `AzNat.primorial`, `firstPrimes` and `productOfFirstNPrimes`

`toNat_primorial : (primorial n).toNat = n#` (Mathlib's `primorial`),
`firstPrimes_spec : (firstPrimes n).size = n ∧ (firstPrimes n)[i] = Nat.nth Nat.Prime i`, and
`toNat_productOfFirstNPrimes : (productOfFirstNPrimes n).toNat = ∏ i < n, Nat.nth Nat.Prime i`.
The sieve's sorted list of primes enumerates `Nat.nth Nat.Prime` (`getElem_primesUpTo_eq_nth`,
through `Nat.nth_count`: the primes below the `i`-th entry are exactly the `i` earlier entries),
and the doubling loop ends with enough primes by Bertrand's postulate
(`le_card_primes_two_pow`).
-/

namespace Azurite.AzNat

open Finset

/-! ### The sorted list of primes -/

theorem toFinset_primesUpTo (B : ℕ) :
    (primesUpTo B).toList.toFinset = (range (B + 1)).filter Nat.Prime := by
  ext p
  rw [List.mem_toFinset, Array.mem_toList_iff, mem_primesUpTo, mem_filter, mem_range]
  exact ⟨fun ⟨hp, hle⟩ => ⟨by omega, hp⟩, fun ⟨hlt, hp⟩ => ⟨hp, by omega⟩⟩

theorem nodup_primesUpTo (B : ℕ) : (primesUpTo B).toList.Nodup :=
  (primesUpTo_sorted B).imp ne_of_lt

theorem size_primesUpTo (B : ℕ) :
    (primesUpTo B).size = #((range (B + 1)).filter Nat.Prime) := by
  rw [← toFinset_primesUpTo, List.toFinset_card_of_nodup (nodup_primesUpTo B),
    Array.length_toList]

theorem getElem_primesUpTo_lt (B : ℕ) {i j : ℕ} (hi : i < (primesUpTo B).toList.length)
    (hj : j < (primesUpTo B).toList.length) (hij : i < j) :
    (primesUpTo B).toList[i] < (primesUpTo B).toList[j] :=
  List.pairwise_iff_getElem.mp (primesUpTo_sorted B) i j hi hj hij

theorem lt_of_getElem_primesUpTo_lt (B : ℕ) {i j : ℕ} (hi : i < (primesUpTo B).toList.length)
    (hj : j < (primesUpTo B).toList.length)
    (h : (primesUpTo B).toList[i] < (primesUpTo B).toList[j]) : i < j := by
  by_contra hle
  rcases Nat.lt_or_eq_of_le (not_lt.mp hle) with hlt | heq
  · exact absurd (getElem_primesUpTo_lt B hj hi hlt) (not_lt.mpr h.le)
  · subst heq; exact lt_irrefl _ h

theorem prime_getElem_primesUpTo (B : ℕ) {i : ℕ} (hi : i < (primesUpTo B).toList.length) :
    Nat.Prime (primesUpTo B).toList[i] ∧ (primesUpTo B).toList[i] ≤ B :=
  mem_primesUpTo.mp (Array.mem_toList_iff.mp (List.getElem_mem hi))

/-- The primes below the `i`-th entry are exactly the `i` earlier entries. -/
theorem count_getElem_primesUpTo (B : ℕ) {i : ℕ} (hi : i < (primesUpTo B).toList.length) :
    Nat.count Nat.Prime (primesUpTo B).toList[i] = i := by
  have h : #(range i) = #((range (primesUpTo B).toList[i]).filter Nat.Prime) := by
    apply card_bij (fun j hj => (primesUpTo B).toList[j]'(by rw [mem_range] at hj; omega))
    · intro j hj
      rw [mem_range] at hj
      rw [mem_filter, mem_range]
      exact ⟨getElem_primesUpTo_lt B (by omega) hi hj, (prime_getElem_primesUpTo B (by omega)).1⟩
    · intro j₁ hj₁ j₂ hj₂ heq
      exact ((nodup_primesUpTo B).getElem_inj_iff).mp heq
    · intro x hx
      rw [mem_filter, mem_range] at hx
      have hxmem : x ∈ (primesUpTo B).toList := Array.mem_toList_iff.mpr
        (mem_primesUpTo.mpr ⟨hx.2, by have := (prime_getElem_primesUpTo B hi).2; omega⟩)
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hxmem
      exact ⟨j, mem_range.mpr (lt_of_getElem_primesUpTo_lt B hj hi hx.1), rfl⟩
  rw [Nat.count_eq_card_filter_range, ← h, card_range]

/-- **The sieve enumerates the primes in order**: entry `i` is `Nat.nth Nat.Prime i`. -/
theorem getElem_primesUpTo_eq_nth (B : ℕ) {i : ℕ} (hi : i < (primesUpTo B).toList.length) :
    (primesUpTo B).toList[i] = Nat.nth Nat.Prime i := by
  have := Nat.nth_count (p := Nat.Prime) (prime_getElem_primesUpTo B hi).1
  rw [count_getElem_primesUpTo B hi] at this
  exact this.symm

/-! ### Enough primes below `2^(n+1)` (Bertrand) -/

theorem le_card_primes_two_pow : ∀ k : ℕ, k + 1 ≤ #((range (2 ^ (k + 1) + 1)).filter Nat.Prime)
  | 0 => card_pos.mpr ⟨2, by simp [Nat.prime_two]⟩
  | k + 1 => by
    obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ (k + 1)) (by positivity)
    have ih := le_card_primes_two_pow k
    have h2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    have hnot : p ∉ (range (2 ^ (k + 1) + 1)).filter Nat.Prime := by
      rw [mem_filter, mem_range]; omega
    have hsub : insert p ((range (2 ^ (k + 1) + 1)).filter Nat.Prime)
        ⊆ (range (2 ^ (k + 1 + 1) + 1)).filter Nat.Prime := by
      intro x hx
      rw [mem_insert, mem_filter, mem_range] at hx
      rw [mem_filter, mem_range]
      rcases hx with rfl | ⟨h1, h2'⟩
      · exact ⟨by omega, hp⟩
      · exact ⟨by omega, h2'⟩
    calc k + 1 + 1 ≤ #((range (2 ^ (k + 1) + 1)).filter Nat.Prime) + 1 := by omega
      _ = #(insert p ((range (2 ^ (k + 1) + 1)).filter Nat.Prime)) :=
          (card_insert_of_notMem hnot).symm
      _ ≤ _ := card_le_card hsub

theorem size_primesUpTo_mono {a b : ℕ} (h : a ≤ b) : (primesUpTo a).size ≤ (primesUpTo b).size := by
  rw [size_primesUpTo, size_primesUpTo]
  apply card_le_card
  intro x hx
  rw [mem_filter, mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

/-- The doubling loop returns a sieve with at least `n` primes. -/
theorem firstPrimes.go_spec (n : ℕ) : ∀ (fuel B : ℕ), 2 ^ (n + 1 - fuel) ≤ B →
    ∃ B', firstPrimes.go n fuel B = primesUpTo B' ∧ n ≤ (primesUpTo B').size
  | 0, B, hB => by
    refine ⟨B, rfl, ?_⟩
    have h1 := le_card_primes_two_pow n
    have h2 := size_primesUpTo_mono (a := 2 ^ (n + 1)) (b := B) (by simpa using hB)
    rw [size_primesUpTo] at h2
    omega
  | fuel + 1, B, hB => by
    unfold firstPrimes.go
    dsimp only
    split_ifs with h
    · exact ⟨B, rfl, h⟩
    · apply firstPrimes.go_spec n fuel (2 * B)
      by_cases hf : fuel ≤ n
      · have : n + 1 - fuel = (n + 1 - (fuel + 1)) + 1 := by omega
        rw [this, pow_succ]
        omega
      · have : n + 1 - fuel = 0 := by omega
        rw [this, pow_zero]
        have : 0 < B := lt_of_lt_of_le (pow_pos two_pos _) hB
        omega

/-- **`firstPrimes n` is the array of the first `n` primes.** -/
theorem firstPrimes_spec (n : ℕ) :
    (firstPrimes n).size = n ∧
      ∀ i (hi : i < (firstPrimes n).size), (firstPrimes n)[i] = Nat.nth Nat.Prime i := by
  obtain ⟨B', hgo, hsize⟩ := firstPrimes.go_spec n (n + 1) (max 2 (n * (Nat.log 2 n + 2)))
    (by rw [Nat.sub_self, pow_zero]; omega)
  unfold firstPrimes
  rw [hgo]
  have hs : ((primesUpTo B').extract 0 n).size = n := by
    rw [Array.size_extract]; omega
  refine ⟨hs, ?_⟩
  intro i hi
  have := getElem_primesUpTo_eq_nth B' (i := i) (by rw [Array.length_toList]; omega)
  rw [Array.getElem_toList] at this
  simp only [Array.getElem_extract, Nat.zero_add]
  exact this

theorem size_firstPrimes (n : ℕ) : (firstPrimes n).size = n := (firstPrimes_spec n).1

/-! ### The products -/

theorem prod_map_range_eq_prod_range {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∀ n : ℕ, ((List.range n).map f).prod = ∏ i ∈ range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, prod_map_range_eq_prod_range f n, prod_range_succ]

theorem toNat_comp_ofNat : toNat ∘ ofNat = id := funext toNat_ofNat

/-- **Correctness of `primorial`**: `n#`. -/
theorem toNat_primorial (n : ℕ) : (primorial n).toNat = _root_.primorial n := by
  unfold Azurite.AzNat.primorial
  rw [toNat_product, List.map_map, toNat_comp_ofNat, List.map_id, _root_.primorial,
    ← toFinset_primesUpTo, List.prod_toFinset _ (nodup_primesUpTo n), List.map_id']

/-- **Correctness of `productOfFirstNPrimes`**: `∏_{i < n} pᵢ` with `pᵢ = Nat.nth Nat.Prime i`. -/
theorem toNat_productOfFirstNPrimes (n : ℕ) :
    (productOfFirstNPrimes n).toNat = ∏ i ∈ range n, Nat.nth Nat.Prime i := by
  unfold productOfFirstNPrimes
  rw [toNat_product, List.map_map, toNat_comp_ofNat, List.map_id]
  have hl : (firstPrimes n).toList = (List.range n).map (Nat.nth Nat.Prime) := by
    apply List.ext_getElem
    · rw [Array.length_toList, size_firstPrimes, List.length_map, List.length_range]
    · intro i h1 h2
      rw [Array.getElem_toList, (firstPrimes_spec n).2, List.getElem_map, List.getElem_range]
  rw [hl, prod_map_range_eq_prod_range]

end Azurite.AzNat
