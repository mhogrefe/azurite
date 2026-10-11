/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzVector.DotSignInt
import Azurite.AzVector.Equiv.DotSign
import Azurite.AzInt.Equiv.CompareProducts
import Azurite.AzInt.Equiv.Mul
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.RingEquiv
import Azurite.AzNat.Equiv.Sub

/-!
## Correctness of `AzInt.dotSign`

`dotSign_eq : dotSign v w = compare (∑ i, vᵢ wᵢ) 0` over the integer values, and
`dotSign_eq_compare_dot : dotSign v w = compare (v.dot w).toInt 0`.  The dot product is `P − N`
for the sums `P`, `N` of the positive and negative magnitudes (`sum_terms_eq`), `extractMax`
only reorders a list (`sum_extractMax`), and `compareSums` compares `P` with `N`
(`compareSums_eq`), the set-aside term being decided through `AzNat.compareProduct`.
-/

namespace Azurite.AzInt

open Azurite (AzVector)
open Azurite.AzNat (compare_Nat_lt_iff compare_Nat_eq_iff compare_Nat_gt_iff)

variable {n : Nat}

/-- The magnitude of a term. -/
def mag (p : AzNat × AzNat) : ℕ := p.1.toNat * p.2.toNat

theorem toNat_sumProducts (l : List (AzNat × AzNat)) :
    (sumProducts l).toNat = (l.map mag).sum := by
  unfold sumProducts
  suffices h : ∀ acc : AzNat, (l.foldl (fun acc p => acc + p.1 * p.2) acc).toNat
      = acc.toNat + (l.map mag).sum by
    simpa [AzNat.toNat_zero] using h 0
  induction l with
  | nil => intro acc; simp
  | cons p ps ih =>
    intro acc
    rw [List.foldl_cons, ih, AzNat.toNat_add, AzNat.toNat_mul, List.map_cons, List.sum_cons]
    unfold mag
    ring

theorem extractMax_eq_none_iff (l : List (AzNat × AzNat)) : extractMax l = none ↔ l = [] := by
  cases l with
  | nil => simp [extractMax]
  | cons p ps =>
    simp only [extractMax, List.cons_ne_nil, iff_false]
    split
    · simp
    · split_ifs <;> simp

/-- `extractMax` only reorders: the removed pair is a member and, with the rest, sums to the
whole. -/
theorem sum_extractMax : ∀ (l : List (AzNat × AzNat)) (p : AzNat × AzNat)
    (rest : List (AzNat × AzNat)), extractMax l = some (p, rest) →
    p ∈ l ∧ (l.map mag).sum = mag p + (rest.map mag).sum
  | [], p, rest, h => by simp [extractMax] at h
  | q :: qs, p, rest, h => by
    simp only [extractMax] at h
    split at h
    · rename_i hnone
      rw [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := (extractMax_eq_none_iff qs).mp hnone
      subst this
      simp
    · rename_i r rest' hsome
      split_ifs at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hmem, ih⟩ := sum_extractMax qs r rest' hsome
        refine ⟨List.mem_cons_of_mem _ hmem, ?_⟩
        simp only [List.map_cons, List.sum_cons]
        omega

private theorem compare_add_sub {a b c : ℕ} (h : b < c) :
    Ord.compare a (c - b) = Ord.compare (a + b) c := by
  rcases lt_trichotomy (a + b) c with h' | h' | h'
  · rw [(compare_Nat_lt_iff _ _).mpr h', (compare_Nat_lt_iff _ _).mpr (by omega)]
  · rw [(compare_Nat_eq_iff _ _).mpr h', (compare_Nat_eq_iff _ _).mpr (by omega)]
  · rw [(compare_Nat_gt_iff _ _).mpr h', (compare_Nat_gt_iff _ _).mpr (by omega)]

private theorem compare_swap (a b : ℕ) : (Ord.compare a b).swap = Ord.compare b a := by
  rcases lt_trichotomy a b with h | h | h
  · rw [(compare_Nat_lt_iff _ _).mpr h, (compare_Nat_gt_iff _ _).mpr h]; rfl
  · rw [(compare_Nat_eq_iff _ _).mpr h, (compare_Nat_eq_iff _ _).mpr h.symm]; rfl
  · rw [(compare_Nat_gt_iff _ _).mpr h, (compare_Nat_lt_iff _ _).mpr h]; rfl

/-! ### The interval screen -/

theorem le_maxSize {l : List (AzNat × AzNat)} {p : AzNat × AzNat} (hp : p ∈ l) :
    p.1.size + p.2.size ≤ maxSize l := by
  unfold maxSize
  suffices h : ∀ m : ℕ, p.1.size + p.2.size ≤ l.foldl (fun m p => max m (p.1.size + p.2.size)) m
    from h 0
  induction l with
  | nil => simp at hp
  | cons q qs ih =>
    intro m
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · have hmono : ∀ (l : List (AzNat × AzNat)) (a b : ℕ), a ≤ b →
          l.foldl (fun m p => max m (p.1.size + p.2.size)) a
            ≤ l.foldl (fun m p => max m (p.1.size + p.2.size)) b := by
        intro l
        induction l with
        | nil => intro a b h; exact h
        | cons r rs ih' => intro a b h; exact ih' _ _ (max_le_max_right _ h)
      have hbase : ∀ (l : List (AzNat × AzNat)) (a : ℕ),
          a ≤ l.foldl (fun m p => max m (p.1.size + p.2.size)) a := by
        intro l
        induction l with
        | nil => intro a; exact le_rfl
        | cons r rs ih' => intro a; exact (le_max_left _ _).trans (ih' _)
      exact (le_max_right m _).trans (hbase qs _)
    · exact ih hp' _

private theorem foldl_max_eq_or_mem : ∀ (l : List (AzNat × AzNat)) (m : ℕ),
    l.foldl (fun m p => max m (p.1.size + p.2.size)) m = m ∨
      ∃ p ∈ l, p.1.size + p.2.size = l.foldl (fun m p => max m (p.1.size + p.2.size)) m
  | [], m => Or.inl rfl
  | q :: qs, m => by
    rw [List.foldl_cons]
    rcases foldl_max_eq_or_mem qs (max m (q.1.size + q.2.size)) with h | ⟨p, hp, hpe⟩
    · rw [h]
      rcases Nat.le_total m (q.1.size + q.2.size) with hle | hle
      · exact Or.inr ⟨q, List.mem_cons_self .., (Nat.max_eq_right hle).symm⟩
      · exact Or.inl (Nat.max_eq_left hle)
    · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hpe⟩

theorem exists_eq_maxSize {l : List (AzNat × AzNat)} (hl : l ≠ []) :
    ∃ p ∈ l, p.1.size + p.2.size = maxSize l := by
  rcases foldl_max_eq_or_mem l 0 with h | h
  · cases l with
    | nil => exact absurd rfl hl
    | cons q qs =>
      refine ⟨q, List.mem_cons_self .., ?_⟩
      have := le_maxSize (l := q :: qs) (p := q) (List.mem_cons_self ..)
      unfold maxSize at this ⊢
      omega
  · exact h

/-- A side's sum is below `2^(K + size m)`. -/
theorem sum_mag_lt (l : List (AzNat × AzNat)) :
    (l.map mag).sum < 2 ^ (maxSize l + Nat.size l.length) := by
  have hterm : ∀ p ∈ l, mag p < 2 ^ maxSize l := by
    intro p hp
    unfold mag
    calc p.1.toNat * p.2.toNat < 2 ^ p.1.toNat.size * 2 ^ p.2.toNat.size :=
          Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self _) (Nat.lt_size_self _).le
            (Nat.two_pow_pos _)
      _ = 2 ^ (p.1.size + p.2.size) := by rw [← pow_add, AzNat.size_toNat, AzNat.size_toNat]
      _ ≤ 2 ^ maxSize l := Nat.pow_le_pow_right (by norm_num) (le_maxSize hp)
  calc (l.map mag).sum ≤ l.length * 2 ^ maxSize l := by
        have := List.sum_le_length_nsmul (l.map mag) (2 ^ maxSize l)
          (fun x hx => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
            exact (hterm p hp).le)
        simpa using this
    _ < 2 ^ Nat.size l.length * 2 ^ maxSize l :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (Nat.two_pow_pos _)
    _ = 2 ^ (maxSize l + Nat.size l.length) := by rw [← pow_add, add_comm]

/-- A nonempty side's sum is at least `2^(K − 2)`, from its largest term alone. -/
theorem two_pow_le_sum_mag {l : List (AzNat × AzNat)} (hl : l ≠ [])
    (hpos : ∀ p ∈ l, 0 < p.1.toNat ∧ 0 < p.2.toNat) :
    2 ^ (maxSize l - 2) ≤ (l.map mag).sum := by
  obtain ⟨p, hp, hpe⟩ := exists_eq_maxSize hl
  have hx := (hpos p hp).1
  have hy := (hpos p hp).2
  have hsx := Nat.size_pos.mpr hx
  have hsy := Nat.size_pos.mpr hy
  calc 2 ^ (maxSize l - 2) = 2 ^ (p.1.toNat.size - 1) * 2 ^ (p.2.toNat.size - 1) := by
        rw [← pow_add, ← hpe, AzNat.size_toNat, AzNat.size_toNat]
        congr 1
        rw [AzNat.size_toNat] at hsx hsy
        omega
    _ ≤ p.1.toNat * p.2.toNat :=
        Nat.mul_le_mul (AzNat.two_pow_size_sub_one_le hx) (AzNat.two_pow_size_sub_one_le hy)
    _ ≤ (l.map mag).sum := List.le_sum_of_mem (List.mem_map_of_mem hp)

/-- The general case compares the two sums. -/
theorem compareSumsGeneral_eq (pos neg : List (AzNat × AzNat))
    (hpos : ∀ p ∈ pos, 0 < p.1.toNat ∧ 0 < p.2.toNat)
    (hneg : ∀ p ∈ neg, 0 < p.1.toNat ∧ 0 < p.2.toNat) (hp : pos ≠ []) (hq : neg ≠ []) :
    compareSumsGeneral pos neg = Ord.compare (pos.map mag).sum (neg.map mag).sum := by
  unfold compareSumsGeneral
  split_ifs with hscr₁ hscr₂
  · symm; rw [compare_Nat_lt_iff]
    calc (pos.map mag).sum < 2 ^ (maxSize pos + Nat.size pos.length) := sum_mag_lt pos
      _ ≤ 2 ^ (maxSize neg - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (neg.map mag).sum := two_pow_le_sum_mag hq hneg
  · symm; rw [compare_Nat_gt_iff]
    calc (neg.map mag).sum < 2 ^ (maxSize neg + Nat.size neg.length) := sum_mag_lt neg
      _ ≤ 2 ^ (maxSize pos - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (pos.map mag).sum := two_pow_le_sum_mag hp hpos
  rcases h1 : extractMax pos with _ | ⟨p, pos'⟩
  · exact absurd ((extractMax_eq_none_iff pos).mp h1) hp
  rcases h2 : extractMax neg with _ | ⟨q, neg'⟩
  · exact absurd ((extractMax_eq_none_iff neg).mp h2) hq
  obtain ⟨hpmem, hP⟩ := sum_extractMax pos p pos' h1
  obtain ⟨hqmem, hQ⟩ := sum_extractMax neg q neg' h2
  have hTp : 0 < mag p := Nat.mul_pos (hpos p hpmem).1 (hpos p hpmem).2
  have hTq : 0 < mag q := Nat.mul_pos (hneg q hqmem).1 (hneg q hqmem).2
  dsimp only
  split_ifs with hsize hle₁ hle₂
  · -- the largest term is positive
    rw [AzNat.le_iff_toNat_le, toNat_sumProducts, toNat_sumProducts] at hle₁
    symm; rw [compare_Nat_gt_iff]; omega
  · rw [AzNat.le_iff_toNat_le, toNat_sumProducts, toNat_sumProducts] at hle₁
    rw [AzNat.compareProduct_eq, AzNat.toNat_sub, toNat_sumProducts, toNat_sumProducts]
    show Ord.compare (mag p) _ = _
    rw [compare_add_sub (by omega), hP]
  · -- the largest term is negative
    rw [AzNat.le_iff_toNat_le, toNat_sumProducts, toNat_sumProducts] at hle₂
    symm; rw [compare_Nat_lt_iff]; omega
  · rw [AzNat.le_iff_toNat_le, toNat_sumProducts, toNat_sumProducts] at hle₂
    rw [AzNat.compareProduct_eq, AzNat.toNat_sub, toNat_sumProducts, toNat_sumProducts]
    show (Ord.compare (mag q) _).swap = _
    rw [compare_add_sub (by omega), compare_swap, hQ]

/-- **`compareSums` compares the two sums**, for lists of pairs of positive numbers. -/
theorem compareSums_eq (pos neg : List (AzNat × AzNat))
    (hpos : ∀ p ∈ pos, 0 < p.1.toNat ∧ 0 < p.2.toNat)
    (hneg : ∀ p ∈ neg, 0 < p.1.toNat ∧ 0 < p.2.toNat) :
    compareSums pos neg = Ord.compare (pos.map mag).sum (neg.map mag).sum := by
  have hsum_pos : ∀ (l : List (AzNat × AzNat)), (∀ p ∈ l, 0 < p.1.toNat ∧ 0 < p.2.toNat) →
      l ≠ [] → 0 < (l.map mag).sum := by
    intro l hl hne
    cases l with
    | nil => exact absurd rfl hne
    | cons p ps =>
      rw [List.map_cons, List.sum_cons]
      exact Nat.lt_of_lt_of_le (Nat.mul_pos (hl p (List.mem_cons_self ..)).1
        (hl p (List.mem_cons_self ..)).2) (Nat.le_add_right _ _)
  rcases pos with _ | ⟨p, ps⟩ <;> rcases neg with _ | ⟨q, qs⟩
  · rfl
  · show Ordering.lt = _
    symm; rw [compare_Nat_lt_iff]
    simpa using hsum_pos (q :: qs) hneg (List.cons_ne_nil q qs)
  · show Ordering.gt = _
    symm; rw [compare_Nat_gt_iff]
    simpa using hsum_pos (p :: ps) hpos (List.cons_ne_nil p ps)
  · rcases ps with _ | ⟨p₂, ps₂⟩ <;> rcases qs with _ | ⟨q₂, qs₂⟩
    · show AzNat.compareProducts p.1 p.2 q.1 q.2 = _
      rw [AzNat.compareProducts_eq]
      simp [mag]
    all_goals
      show compareSumsGeneral _ _ = _
      exact compareSumsGeneral_eq _ _ hpos hneg (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)

/-- The value of a term, and the split: `Σ terms = P − N` with all pairs positive. -/
theorem splitTerms_spec : ∀ l : List (AzInt × AzInt),
    (l.map fun p => p.1.toInt * p.2.toInt).sum
        = (((splitTerms l).1.map mag).sum : ℤ) - (((splitTerms l).2.map mag).sum : ℤ) ∧
      (∀ p ∈ (splitTerms l).1, 0 < p.1.toNat ∧ 0 < p.2.toNat) ∧
      (∀ p ∈ (splitTerms l).2, 0 < p.1.toNat ∧ 0 < p.2.toNat)
  | [] => by simp [splitTerms]
  | (a, b) :: rest => by
    obtain ⟨hsum, hpos, hneg⟩ := splitTerms_spec rest
    simp only [splitTerms, List.map_cons, List.sum_cons]
    have hterm : a.toInt * b.toInt
        = if (a.sign == b.sign) then ((a.abs.toNat * b.abs.toNat : ℕ) : ℤ)
          else -((a.abs.toNat * b.abs.toNat : ℕ) : ℤ) := by
      unfold toInt; exact toInt_mul_signed a.sign b.sign a.abs b.abs
    split_ifs with hz hs
    · -- a zero term
      have h0 : a.abs.toNat * b.abs.toNat = 0 := by
        rcases hz with h | h <;> simp [(AzNat.eq_zero_iff_toNat _).mp h]
      refine ⟨?_, hpos, hneg⟩
      rw [hterm, h0, hsum]
      split_ifs <;> simp
    · rw [not_or, AzNat.eq_zero_iff_toNat, AzNat.eq_zero_iff_toNat] at hz
      refine ⟨?_, ?_, hneg⟩
      · rw [hterm, hsum, ite_eq_left hs]
        simp only [List.map_cons, List.sum_cons, mag]
        push_cast
        ring
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨Nat.pos_of_ne_zero hz.1, Nat.pos_of_ne_zero hz.2⟩
        · exact hpos p hp
    · rw [not_or, AzNat.eq_zero_iff_toNat, AzNat.eq_zero_iff_toNat] at hz
      refine ⟨?_, hpos, ?_⟩
      · rw [hterm, hsum, ite_eq_right hs]
        simp only [List.map_cons, List.sum_cons, mag]
        push_cast
        ring
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨Nat.pos_of_ne_zero hz.1, Nat.pos_of_ne_zero hz.2⟩
        · exact hneg p hp

private theorem compare_sub_zero (P N : ℕ) :
    Ord.compare ((P : ℤ) - (N : ℤ)) 0 = Ord.compare P N := by
  rcases lt_trichotomy P N with h | h | h
  · rw [(compare_Nat_lt_iff _ _).mpr h, compare_lt_iff_lt]; omega
  · rw [(compare_Nat_eq_iff _ _).mpr h, compare_eq_iff_eq]; omega
  · rw [(compare_Nat_gt_iff _ _).mpr h, compare_gt_iff_gt]; omega

/-- **Correctness of `dotSign`**: the ordering of `∑ i, vᵢ wᵢ` against `0`. -/
theorem dotSign_eq (v w : AzVector AzInt n) :
    dotSign v w = Ord.compare (∑ i, (v.toFn i).toInt * (w.toFn i).toInt) 0 := by
  unfold dotSign dotTerms
  obtain ⟨hsum, hpos, hneg⟩ :=
    splitTerms_spec ((List.finRange n).map fun i => (v.toFn i, w.toFn i))
  rw [compareSums_eq _ _ hpos hneg, ← compare_sub_zero, ← hsum, List.map_map,
    ← List.ofFn_eq_map, List.sum_ofFn]
  rfl

/-- **`dotSign` is the sign of the dot product.** -/
theorem dotSign_eq_compare_dot (v w : AzVector AzInt n) :
    dotSign v w = Ord.compare (v.dot w).toInt 0 := by
  rw [dotSign_eq, AzVector.dot_eq_dotProduct, dotProduct, ← toIntRingHom_apply, map_sum]
  congr 2
  funext i
  rw [map_mul, toIntRingHom_apply, toIntRingHom_apply]

end Azurite.AzInt
