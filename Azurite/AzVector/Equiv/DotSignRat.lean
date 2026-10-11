/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzVector.DotSignRat
import Azurite.AzVector.Equiv.DotSignInt
import Azurite.AzRat.Equiv.CompareProducts
import Azurite.AzRat.Equiv.RingEquiv
import Azurite.AzNat.Equiv.Landau

/-!
## Correctness of `AzRat.dotSign`

`dotSign_eq : dotSign v w = compare (∑ i, vᵢ wᵢ) 0` over the rational values, and
`dotSign_eq_compare_dot : dotSign v w = compare (toRat (v.dot w)) 0`.  Unreduced fractions form
an additive monoid whose value map is additive when the denominators are nonzero
(`Frac.val_sum`), so the balanced sum of a side is its sum of values; the interval screen is the
bound `2^(e−2) ≤ value < 2^(e+2)` on each term; and the two sides are compared through their
cross products (`compare_div_nat`).
-/

namespace Azurite

/-! ### Unreduced fractions -/

instance : AddMonoid Frac where
  add_assoc p q r := by
    ext
    · apply AzNat.toNat_injective
      simp only [Frac.add_def, AzNat.toNat_add, AzNat.toNat_mul]
      ring
    · apply AzNat.toNat_injective
      simp only [Frac.add_def, AzNat.toNat_mul]
      ring
  zero_add p := by
    ext
    · apply AzNat.toNat_injective
      simp only [Frac.add_def, Frac.zero_def, AzNat.toNat_add, AzNat.toNat_mul, AzNat.toNat_zero,
        AzNat.toNat_one]
      ring
    · apply AzNat.toNat_injective
      simp only [Frac.add_def, Frac.zero_def, AzNat.toNat_mul, AzNat.toNat_one]
      ring
  add_zero p := by
    ext
    · apply AzNat.toNat_injective
      simp only [Frac.add_def, Frac.zero_def, AzNat.toNat_add, AzNat.toNat_mul, AzNat.toNat_zero,
        AzNat.toNat_one]
      ring
    · apply AzNat.toNat_injective
      simp only [Frac.add_def, Frac.zero_def, AzNat.toNat_mul, AzNat.toNat_one]
      ring
  nsmul := nsmulRec

/-- The value of an unreduced fraction. -/
noncomputable def Frac.val (p : Frac) : ℚ := (p.num.toNat : ℚ) / (p.den.toNat : ℚ)

theorem Frac.val_add {p q : Frac} (hp : p.den.toNat ≠ 0) (hq : q.den.toNat ≠ 0) :
    (p + q).val = p.val + q.val := by
  unfold Frac.val
  rw [Frac.add_def]
  simp only [AzNat.toNat_add, AzNat.toNat_mul]
  push_cast
  rw [div_add_div _ _ (by exact_mod_cast hp) (by exact_mod_cast hq)]
  congr 1
  ring

theorem Frac.den_sum (l : List Frac) : (l.sum).den.toNat = (l.map fun p => p.den.toNat).prod := by
  induction l with
  | nil => simp [Frac.zero_def, AzNat.toNat_one]
  | cons p ps ih =>
    rw [List.sum_cons, List.map_cons, List.prod_cons, ← ih]
    show (p.den * ps.sum.den).toNat = _
    exact AzNat.toNat_mul _ _

theorem Frac.den_sum_ne_zero {l : List Frac} (h : ∀ p ∈ l, p.den.toNat ≠ 0) :
    (l.sum).den.toNat ≠ 0 := by
  rw [Frac.den_sum]
  exact (List.prod_pos (fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact Nat.pos_of_ne_zero (h p hp))).ne'

/-- **The value of the sum is the sum of the values**, when the denominators are nonzero. -/
theorem Frac.val_sum {l : List Frac} (h : ∀ p ∈ l, p.den.toNat ≠ 0) :
    (l.sum).val = (l.map Frac.val).sum := by
  induction l with
  | nil => simp [Frac.val, Frac.zero_def, AzNat.toNat_zero]
  | cons p ps ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons,
      Frac.val_add (h p (List.mem_cons_self ..))
        (Frac.den_sum_ne_zero fun q hq => h q (List.mem_cons_of_mem _ hq)),
      ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem Frac.sum_eq (l : List Frac) : Frac.sum l = l.sum := Azurite.balancedSum_eq_sum l

namespace AzRat

open Azurite (AzVector)
open Azurite.AzNat (compare_Nat_lt_iff compare_Nat_eq_iff compare_Nat_gt_iff
  two_pow_size_sub_one_le le_foldl_max le_foldl_max_of_mem foldl_max_eq_or_mem)

variable {n : Nat}

/-! ### Terms -/

/-- The value of a term. -/
noncomputable def Term.val (t : Term) : ℚ := t.toFrac.val

/-- All four factors of a term are positive. -/
def Term.Pos (t : Term) : Prop :=
  0 < t.nx.toNat ∧ 0 < t.ny.toNat ∧ 0 < t.dx.toNat ∧ 0 < t.dy.toNat

theorem Term.val_eq (t : Term) :
    t.val = ((t.nx.toNat * t.ny.toNat : ℕ) : ℚ) / ((t.dx.toNat * t.dy.toNat : ℕ) : ℚ) := by
  unfold Term.val Frac.val Term.toFrac
  rw [AzNat.toNat_mul, AzNat.toNat_mul]

theorem Term.val_pos {t : Term} (h : t.Pos) : 0 < t.val := by
  rw [Term.val_eq]
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact div_pos (by exact_mod_cast Nat.mul_pos h1 h2) (by exact_mod_cast Nat.mul_pos h3 h4)

theorem Term.toFrac_den_ne_zero {t : Term} (h : t.Pos) : t.toFrac.den.toNat ≠ 0 := by
  unfold Term.toFrac
  rw [AzNat.toNat_mul]
  exact (Nat.mul_pos h.2.2.1 h.2.2.2).ne'

/-! ### The interval bounds on a term -/

private theorem two_zpow_nat (a : ℕ) : (2 : ℚ) ^ (a : ℤ) = ((2 ^ a : ℕ) : ℚ) := by
  rw [zpow_natCast]; push_cast; rfl

/-- `value < 2^(e + 2)`. -/
theorem Term.val_lt {t : Term} (h : t.Pos) : t.val < (2 : ℚ) ^ (t.exp + 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs3 := Nat.size_pos.mpr h3
  have hs4 := Nat.size_pos.mpr h4
  rw [Term.val_eq, div_lt_iff₀ (by exact_mod_cast Nat.mul_pos h3 h4)]
  have hnum : t.nx.toNat * t.ny.toNat < 2 ^ (t.nx.size + t.ny.size) := by
    rw [pow_add, ← AzNat.size_toNat, ← AzNat.size_toNat]
    exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self _) (Nat.lt_size_self _).le
      (Nat.two_pow_pos _)
  have h2 : 2 ≤ t.dx.size + t.dy.size := by rw [← AzNat.size_toNat, ← AzNat.size_toNat]; omega
  have hden : 2 ^ (t.dx.size + t.dy.size - 2) ≤ t.dx.toNat * t.dy.toNat := by
    rw [← AzNat.size_toNat, ← AzNat.size_toNat]
    rw [show t.dx.toNat.size + t.dy.toNat.size - 2 = (t.dx.toNat.size - 1) + (t.dy.toNat.size - 1)
      by omega, pow_add]
    exact Nat.mul_le_mul (two_pow_size_sub_one_le h3) (two_pow_size_sub_one_le h4)
  have hexp : (2 : ℚ) ^ (t.exp + 2) * ((2 ^ (t.dx.size + t.dy.size - 2) : ℕ) : ℚ)
      = ((2 ^ (t.nx.size + t.ny.size) : ℕ) : ℚ) := by
    rw [← two_zpow_nat, ← two_zpow_nat, ← zpow_add₀ (by norm_num)]
    congr 1
    unfold Term.exp
    push_cast [Nat.cast_sub h2]
    ring
  calc ((t.nx.toNat * t.ny.toNat : ℕ) : ℚ) < ((2 ^ (t.nx.size + t.ny.size) : ℕ) : ℚ) := by
        exact_mod_cast hnum
    _ = (2 : ℚ) ^ (t.exp + 2) * ((2 ^ (t.dx.size + t.dy.size - 2) : ℕ) : ℚ) := hexp.symm
    _ ≤ (2 : ℚ) ^ (t.exp + 2) * ((t.dx.toNat * t.dy.toNat : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hden) (zpow_nonneg (by norm_num) _)

/-- `2^(e − 2) ≤ value`. -/
theorem Term.two_zpow_le_val {t : Term} (h : t.Pos) : (2 : ℚ) ^ (t.exp - 2) ≤ t.val := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs1 := Nat.size_pos.mpr h1
  have hs2 := Nat.size_pos.mpr h2
  rw [Term.val_eq, le_div_iff₀ (by exact_mod_cast Nat.mul_pos h3 h4)]
  have h2' : 2 ≤ t.nx.size + t.ny.size := by rw [← AzNat.size_toNat, ← AzNat.size_toNat]; omega
  have hnum : 2 ^ (t.nx.size + t.ny.size - 2) ≤ t.nx.toNat * t.ny.toNat := by
    rw [← AzNat.size_toNat, ← AzNat.size_toNat]
    rw [show t.nx.toNat.size + t.ny.toNat.size - 2 = (t.nx.toNat.size - 1) + (t.ny.toNat.size - 1)
      by omega, pow_add]
    exact Nat.mul_le_mul (two_pow_size_sub_one_le h1) (two_pow_size_sub_one_le h2)
  have hden : t.dx.toNat * t.dy.toNat < 2 ^ (t.dx.size + t.dy.size) := by
    rw [pow_add, ← AzNat.size_toNat, ← AzNat.size_toNat]
    exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self _) (Nat.lt_size_self _).le
      (Nat.two_pow_pos _)
  have hexp : (2 : ℚ) ^ (t.exp - 2) * ((2 ^ (t.dx.size + t.dy.size) : ℕ) : ℚ)
      = ((2 ^ (t.nx.size + t.ny.size - 2) : ℕ) : ℚ) := by
    rw [← two_zpow_nat, ← two_zpow_nat, ← zpow_add₀ (by norm_num)]
    congr 1
    unfold Term.exp
    push_cast [Nat.cast_sub h2']
    ring
  calc (2 : ℚ) ^ (t.exp - 2) * ((t.dx.toNat * t.dy.toNat : ℕ) : ℚ)
      ≤ (2 : ℚ) ^ (t.exp - 2) * ((2 ^ (t.dx.size + t.dy.size) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hden.le) (zpow_nonneg (by norm_num) _)
    _ = ((2 ^ (t.nx.size + t.ny.size - 2) : ℕ) : ℚ) := hexp
    _ ≤ ((t.nx.toNat * t.ny.toNat : ℕ) : ℚ) := by exact_mod_cast hnum

/-! ### The maximal exponent -/

theorem maxExp_cons (t : Term) (ts : List Term) :
    maxExp (t :: ts) = (ts.map Term.exp).foldl max t.exp := by
  simp [maxExp, List.foldl_map]

theorem le_maxExp {l : List Term} {t : Term} (ht : t ∈ l) : t.exp ≤ maxExp l := by
  cases l with
  | nil => simp at ht
  | cons s ss =>
    rw [maxExp_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact le_foldl_max _ _
    · exact le_foldl_max_of_mem _ _ (List.mem_map_of_mem ht)

theorem exists_eq_maxExp {l : List Term} (hl : l ≠ []) : ∃ t ∈ l, t.exp = maxExp l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons s ss =>
    rw [maxExp_cons]
    rcases foldl_max_eq_or_mem (ss.map Term.exp) s.exp with h | h
    · exact ⟨s, List.mem_cons_self .., h.symm⟩
    · obtain ⟨t, ht, hte⟩ := List.mem_map.mp h
      exact ⟨t, List.mem_cons_of_mem _ ht, hte⟩

/-- A side's sum is below `2^(E + size m + 2)`. -/
theorem sum_val_lt (l : List Term) (h : ∀ t ∈ l, t.Pos) :
    (l.map Term.val).sum < (2 : ℚ) ^ (maxExp l + (Nat.size l.length : ℤ) + 2) := by
  have hterm : ∀ t ∈ l, t.val ≤ (2 : ℚ) ^ (maxExp l + 2) := fun t ht =>
    (Term.val_lt (h t ht)).le.trans
      (zpow_le_zpow_right₀ (by norm_num) (by have := le_maxExp ht; omega))
  calc (l.map Term.val).sum ≤ (l.map Term.val).length • (2 : ℚ) ^ (maxExp l + 2) :=
        List.sum_le_length_nsmul _ _ (fun x hx => by
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
          exact hterm t ht)
    _ = (l.length : ℚ) * (2 : ℚ) ^ (maxExp l + 2) := by rw [List.length_map, nsmul_eq_mul]
    _ < (2 : ℚ) ^ (Nat.size l.length : ℤ) * (2 : ℚ) ^ (maxExp l + 2) := by
        apply mul_lt_mul_of_pos_right _ (zpow_pos (by norm_num) _)
        rw [two_zpow_nat]
        exact_mod_cast Nat.lt_size_self _
    _ = (2 : ℚ) ^ (maxExp l + (Nat.size l.length : ℤ) + 2) := by
        rw [← zpow_add₀ (by norm_num)]; congr 1; ring

/-- A nonempty side's sum is at least `2^(E − 2)`, from its largest term alone. -/
theorem two_zpow_le_sum_val {l : List Term} (hl : l ≠ []) (h : ∀ t ∈ l, t.Pos) :
    (2 : ℚ) ^ (maxExp l - 2) ≤ (l.map Term.val).sum := by
  obtain ⟨t, ht, hte⟩ := exists_eq_maxExp hl
  calc (2 : ℚ) ^ (maxExp l - 2) = (2 : ℚ) ^ (t.exp - 2) := by rw [hte]
    _ ≤ t.val := Term.two_zpow_le_val (h t ht)
    _ ≤ (l.map Term.val).sum :=
        List.single_le_sum (fun x hx => by
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
          exact (Term.val_pos (h s hs)).le) _ (List.mem_map_of_mem ht)

/-! ### Comparing fractions -/

theorem compare_div_nat (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    Ord.compare ((a : ℚ) / (b : ℚ)) ((c : ℚ) / (d : ℚ)) = Ord.compare (a * d) (c * b) := by
  have := compare_div (a : ℤ) (c : ℤ) (b : ℤ) (d : ℤ) (by exact_mod_cast hb) (by exact_mod_cast hd)
  push_cast at this
  rw [this]
  rcases lt_trichotomy (a * d) (c * b) with h | h | h
  · rw [(compare_Nat_lt_iff _ _).mpr h, compare_lt_iff_lt]; exact_mod_cast h
  · rw [(compare_Nat_eq_iff _ _).mpr h, compare_eq_iff_eq]; exact_mod_cast h
  · rw [(compare_Nat_gt_iff _ _).mpr h, compare_gt_iff_gt]; exact_mod_cast h

/-! ### The sums -/

theorem compareSumsGeneral_eq (pos neg : List Term) (hpos : ∀ t ∈ pos, t.Pos)
    (hneg : ∀ t ∈ neg, t.Pos) (hp : pos ≠ []) (hq : neg ≠ []) :
    compareSumsGeneral pos neg = Ord.compare (pos.map Term.val).sum (neg.map Term.val).sum := by
  unfold compareSumsGeneral
  split_ifs with h1 h2
  · symm; rw [compare_lt_iff_lt]
    calc (pos.map Term.val).sum < (2 : ℚ) ^ (maxExp pos + (Nat.size pos.length : ℤ) + 2) :=
          sum_val_lt pos hpos
      _ ≤ (2 : ℚ) ^ (maxExp neg - 2) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ ≤ (neg.map Term.val).sum := two_zpow_le_sum_val hq hneg
  · symm; rw [compare_gt_iff_gt]
    calc (neg.map Term.val).sum < (2 : ℚ) ^ (maxExp neg + (Nat.size neg.length : ℤ) + 2) :=
          sum_val_lt neg hneg
      _ ≤ (2 : ℚ) ^ (maxExp pos - 2) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ ≤ (pos.map Term.val).sum := two_zpow_le_sum_val hp hpos
  · have hPd := Frac.den_sum_ne_zero (l := pos.map Term.toFrac) fun f hf => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
      exact Term.toFrac_den_ne_zero (hpos t ht)
    have hNd := Frac.den_sum_ne_zero (l := neg.map Term.toFrac) fun f hf => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
      exact Term.toFrac_den_ne_zero (hneg t ht)
    have hP : ((pos.map Term.toFrac).sum).val = (pos.map Term.val).sum := by
      rw [Frac.val_sum (fun f hf => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
        exact Term.toFrac_den_ne_zero (hpos t ht)), List.map_map]
      rfl
    have hN : ((neg.map Term.toFrac).sum).val = (neg.map Term.val).sum := by
      rw [Frac.val_sum (fun f hf => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
        exact Term.toFrac_den_ne_zero (hneg t ht)), List.map_map]
      rfl
    rw [AzNat.compareProducts_eq, Frac.sum_eq, Frac.sum_eq, ← hP, ← hN]
    unfold Frac.val
    rw [compare_div_nat _ _ _ _ (Nat.pos_of_ne_zero hPd) (Nat.pos_of_ne_zero hNd)]

theorem compareSums_eq (pos neg : List Term) (hpos : ∀ t ∈ pos, t.Pos)
    (hneg : ∀ t ∈ neg, t.Pos) :
    compareSums pos neg = Ord.compare (pos.map Term.val).sum (neg.map Term.val).sum := by
  have hsum_pos : ∀ (l : List Term), (∀ t ∈ l, t.Pos) → l ≠ [] → 0 < (l.map Term.val).sum := by
    intro l hl hne
    cases l with
    | nil => exact absurd rfl hne
    | cons t ts =>
      rw [List.map_cons, List.sum_cons]
      have := Term.val_pos (hl t (List.mem_cons_self ..))
      have : 0 ≤ (ts.map Term.val).sum := List.sum_nonneg (fun x hx => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
        exact (Term.val_pos (hl s (List.mem_cons_of_mem _ hs))).le)
      linarith
  rcases pos with _ | ⟨p, ps⟩ <;> rcases neg with _ | ⟨q, qs⟩
  · rfl
  · show Ordering.lt = _
    symm; rw [compare_lt_iff_lt]
    simpa using hsum_pos (q :: qs) hneg (List.cons_ne_nil q qs)
  · show Ordering.gt = _
    symm; rw [compare_gt_iff_gt]
    simpa using hsum_pos (p :: ps) hpos (List.cons_ne_nil p ps)
  · rcases ps with _ | ⟨p₂, ps₂⟩ <;> rcases qs with _ | ⟨q₂, qs₂⟩
    · show compareProductsMag p.nx p.dx p.ny p.dy q.nx q.dx q.ny q.dy = _
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hpos p (List.mem_cons_self ..)
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hneg q (List.mem_cons_self ..)
      rw [compareProductsMag_eq _ _ _ _ _ _ _ _ hp1 hp3 hp2 hp4 hq1 hq3 hq2 hq4]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Term.val_eq]
      rw [compare_div_nat _ _ _ _ (Nat.mul_pos hp3 hp4) (Nat.mul_pos hq3 hq4)]
    all_goals
      show compareSumsGeneral _ _ = _
      exact compareSumsGeneral_eq _ _ hpos hneg (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)

/-! ### The split -/

theorem splitTerms_spec : ∀ l : List (AzRat × AzRat),
    (l.map fun p => toRat p.1 * toRat p.2).sum
        = ((splitTerms l).1.map Term.val).sum - ((splitTerms l).2.map Term.val).sum ∧
      (∀ t ∈ (splitTerms l).1, t.Pos) ∧ (∀ t ∈ (splitTerms l).2, t.Pos)
  | [] => by simp [splitTerms]
  | (x, y) :: rest => by
    obtain ⟨hsum, hpos, hneg⟩ := splitTerms_spec rest
    simp only [splitTerms, List.map_cons, List.sum_cons]
    have hdx : 0 < x.den.toNat :=
      Nat.pos_of_ne_zero fun h => x.den_nz ((AzNat.eq_zero_iff_toNat _).mpr h)
    have hdy : 0 < y.den.toNat :=
      Nat.pos_of_ne_zero fun h => y.den_nz ((AzNat.eq_zero_iff_toNat _).mpr h)
    have hterm : toRat x * toRat y
        = (if (x.sign == y.sign) then ((x.num.toNat * y.num.toNat : ℕ) : ℚ)
            else -((x.num.toNat * y.num.toNat : ℕ) : ℚ))
          / ((x.den.toNat * y.den.toNat : ℕ) : ℚ) := by
      rw [toRat_eq_divInt, toRat_eq_divInt, Rat.divInt_mul_divInt, Rat.divInt_eq_div,
        AzInt.toInt_mul_signed]
      split_ifs <;> push_cast <;> ring
    split_ifs with hz hs
    · -- a zero term
      have h0 : x.num.toNat * y.num.toNat = 0 := by
        rcases hz with h | h <;> simp [(AzNat.eq_zero_iff_toNat _).mp h]
      refine ⟨?_, hpos, hneg⟩
      rw [hterm, h0, hsum]
      split_ifs <;> simp
    · rw [not_or, AzNat.eq_zero_iff_toNat, AzNat.eq_zero_iff_toNat] at hz
      refine ⟨?_, ?_, hneg⟩
      · rw [hterm, hsum, ite_eq_left hs]
        simp only [List.map_cons, List.sum_cons, Term.val_eq]
        ring
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨Nat.pos_of_ne_zero hz.1, Nat.pos_of_ne_zero hz.2, hdx, hdy⟩
        · exact hpos t ht
    · rw [not_or, AzNat.eq_zero_iff_toNat, AzNat.eq_zero_iff_toNat] at hz
      refine ⟨?_, hpos, ?_⟩
      · rw [hterm, hsum, ite_eq_right hs]
        simp only [List.map_cons, List.sum_cons, Term.val_eq]
        ring
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨Nat.pos_of_ne_zero hz.1, Nat.pos_of_ne_zero hz.2, hdx, hdy⟩
        · exact hneg t ht

private theorem compare_sub_zero (P N : ℚ) : Ord.compare (P - N) 0 = Ord.compare P N := by
  rcases lt_trichotomy P N with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt]; linarith
  · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq]; linarith
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt]; linarith

/-- **Correctness of `dotSign`**: the ordering of `∑ i, vᵢ wᵢ` against `0`. -/
theorem dotSign_eq (v w : AzVector AzRat n) :
    dotSign v w = Ord.compare (∑ i, toRat (v.toFn i) * toRat (w.toFn i)) 0 := by
  unfold dotSign
  obtain ⟨hsum, hpos, hneg⟩ :=
    splitTerms_spec ((List.finRange n).map fun i => (v.toFn i, w.toFn i))
  rw [compareSums_eq _ _ hpos hneg, ← compare_sub_zero, ← hsum, List.map_map,
    ← List.ofFn_eq_map, List.sum_ofFn]
  rfl

/-- **`dotSign` is the sign of the dot product.** -/
theorem dotSign_eq_compare_dot (v w : AzVector AzRat n) :
    dotSign v w = Ord.compare (toRat (v.dot w)) 0 := by
  rw [dotSign_eq, AzVector.dot_eq_dotProduct, dotProduct, ← toRatRingHom_apply, map_sum]
  congr 2
  funext i
  rw [map_mul, toRatRingHom_apply, toRatRingHom_apply]

end AzRat

end Azurite
