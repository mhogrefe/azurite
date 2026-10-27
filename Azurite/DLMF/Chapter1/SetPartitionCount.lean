/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Tactic.Ring

/-!
# Counting ordered set partitions by block sizes

Mathlib's `Multiset.bell s` is the closed-form number `(s.sum)! / (∏ⱼ (j!)^{mⱼ} mⱼ!)` of set
partitions whose block sizes form the multiset `s` (`mⱼ = count j s`); Mathlib leaves the fact
that it counts partitions as a TODO.  This file proves it for Mathlib's `OrderedFinpartition n`
(set partitions of `Fin n`, which Faà di Bruno's formula is stated over):

* `sizes c`: the multiset of block sizes of `c : OrderedFinpartition n`;
* `cnt n s`: the number of `c` with `sizes c = s`;
* `cnt_eq_bell`: `cnt n s = s.bell` for `s` a multiset of positive integers with sum `n`,
  by induction on `n` through `OrderedFinpartition.extendEquiv` (a partition of `Fin (n + 1)`
  is a partition of `Fin n` with a new singleton block, or with one block grown by one element:
  `cnt_succ`), with the weight `wt M s = ∏_{j < M} (j!)^{mⱼ} mⱼ!` tracking the recursion
  (`cnt_mul_wt : cnt n s * wt (n + 2) s = n!`, `bell_mul_wt`);
* `iteratedDeriv_comp_eq_sum_partition`: Faà di Bruno's formula regrouped as a sum over the
  partitions of `n` (`Nat.Partition n`), each weighted by `Multiset.bell`;
* `bell_cast_eq`: `Multiset.bell` of a partition of `n` as `n! / (∏ (j!)^{mⱼ} ∏ mⱼ!)` in `ℝ`.
-/

namespace Azurite.DLMF
open Finset OrderedFinpartition

variable {n : ℕ}

/-- The multiset of block sizes of an ordered finpartition. -/
def sizes (c : OrderedFinpartition n) : Multiset ℕ := univ.val.map c.partSize

theorem sizes_card (c : OrderedFinpartition n) : Multiset.card (sizes c) = c.length := by
  simp [sizes]

theorem sum_partSize (c : OrderedFinpartition n) : ∑ i, c.partSize i = n := by
  have := Fintype.card_congr c.equivSigma
  simpa only [Fintype.card_sigma, Fintype.card_fin] using this

theorem sizes_sum (c : OrderedFinpartition n) : (sizes c).sum = n := by
  rw [sizes, ← Finset.sum_eq_multiset_sum]
  exact sum_partSize c

theorem zero_notMem_sizes (c : OrderedFinpartition n) : 0 ∉ sizes c := by
  simp only [sizes, Multiset.mem_map, mem_univ_val, true_and, not_exists]
  intro i h
  exact (c.partSize_pos i).ne' h

theorem count_sizes (c : OrderedFinpartition n) (j : ℕ) :
    (sizes c).count j = (univ.filter fun i => c.partSize i = j).card := by
  rw [sizes, Multiset.count_map, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun i _ => eq_comm

theorem sizes_extendLeft (c : OrderedFinpartition n) :
    sizes c.extendLeft = 1 ::ₘ sizes c := by
  change Multiset.map (Fin.cons 1 c.partSize : Fin (c.length + 1) → ℕ) univ.val = _
  rw [Fin.univ_succ, Finset.cons_val, Multiset.map_cons, Fin.cons_zero, Finset.map_val,
    Multiset.map_map]
  rfl

theorem map_univ_update (p : Fin n → ℕ) (k : Fin n) (v : ℕ) :
    univ.val.map (Function.update p k v) = v ::ₘ (univ.erase k).val.map p := by
  conv_lhs => rw [← Finset.insert_erase (mem_univ k)]
  rw [Finset.insert_val_of_notMem (Finset.notMem_erase k _), Multiset.map_cons,
    Function.update_self]
  congr 1
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_def.mpr hi))]

theorem sizes_extendMiddle (c : OrderedFinpartition n) (k : Fin c.length) :
    sizes (c.extendMiddle k) = (c.partSize k + 1) ::ₘ (sizes c).erase (c.partSize k) := by
  have h : sizes c = c.partSize k ::ₘ (univ.erase k).val.map c.partSize := by
    rw [sizes]
    conv_lhs => rw [← Finset.insert_erase (mem_univ k)]
    rw [Finset.insert_val_of_notMem (Finset.notMem_erase k _), Multiset.map_cons]
  rw [h, Multiset.erase_cons_head, sizes, extendMiddle_partSize]
  change Multiset.map (Function.update c.partSize k (c.partSize k + 1) : Fin c.length → ℕ)
    univ.val = _
  rw [map_univ_update]

/-- The only ordered finpartition of `Fin 0` is the empty one. -/
theorem sizes_eq_zero (c : OrderedFinpartition 0) : sizes c = 0 := by
  rw [← Multiset.card_eq_zero, sizes_card]
  by_contra h
  have hpos : 0 < c.length := Nat.pos_of_ne_zero h
  exact (c.emb ⟨0, hpos⟩ ⟨0, c.partSize_pos _⟩).elim0

/-- The weight `∏_{j < M} (j!)^{mⱼ} mⱼ!` of a multiset of block sizes with multiplicities
`mⱼ = count j s`; `s.bell * wt M s = (s.sum)!` for `M` beyond the largest size. -/
def wt (M : ℕ) (s : Multiset ℕ) : ℕ :=
  ∏ j ∈ range M, (j.factorial ^ s.count j * (s.count j).factorial)

theorem wt_pos (M : ℕ) (s : Multiset ℕ) : 0 < wt M s :=
  prod_pos fun j _ => Nat.mul_pos (pow_pos (Nat.factorial_pos j) _) (Nat.factorial_pos _)

theorem wt_eq_of_lt {M M' : ℕ} {s : Multiset ℕ} (hM : ∀ j ∈ s, j < M) (hMM' : M ≤ M') :
    wt M s = wt M' s := by
  unfold wt
  refine prod_subset (Finset.range_mono hMM') fun j _ hj => ?_
  have : s.count j = 0 := Multiset.count_eq_zero.mpr fun h => hj (Finset.mem_range.mpr (hM j h))
  simp [this]

/-- `Multiset.bell_mul_eq` in terms of `wt`. -/
theorem bell_mul_wt {M : ℕ} {s : Multiset ℕ} (hM : ∀ j ∈ s, j < M) (h0 : 0 ∉ s) :
    s.bell * wt M s = s.sum.factorial := by
  rw [← Multiset.bell_mul_eq s, mul_assoc]
  congr 1
  rw [wt, Finset.prod_multiset_map_count, Finset.prod_mul_distrib]
  have hsub : s.toFinset ⊆ range M := fun j hj =>
    Finset.mem_range.mpr (hM j (Multiset.mem_toFinset.mp hj))
  have hsub' : s.toFinset.erase 0 = s.toFinset := Finset.erase_eq_of_notMem (by simpa using h0)
  rw [hsub']
  congr 1
  · exact (prod_subset hsub fun j _ hj => by
      simp [Multiset.count_eq_zero.mpr (fun h => hj (Multiset.mem_toFinset.mpr h))]).symm
  · exact (prod_subset hsub fun j _ hj => by
      simp [Multiset.count_eq_zero.mpr (fun h => hj (Multiset.mem_toFinset.mpr h))]).symm

theorem prod_range_split1 {M j : ℕ} (hj : j < M) (f : ℕ → ℕ) :
    ∏ i ∈ range M, f i = f j * ∏ i ∈ (range M).erase j, f i :=
  (Finset.mul_prod_erase (range M) f (Finset.mem_range.mpr hj)).symm

theorem prod_range_split2 {M j : ℕ} (hj : j + 1 < M) (f : ℕ → ℕ) :
    ∏ i ∈ range M, f i = f j * (f (j + 1) * ∏ i ∈ ((range M).erase j).erase (j + 1), f i) := by
  rw [Finset.mul_prod_erase ((range M).erase j) f
    (Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hj⟩),
    Finset.mul_prod_erase (range M) f (Finset.mem_range.mpr (by omega))]

/-- Removing one block of size `1`: `wt s = (count 1 s) * wt (s.erase 1)`. -/
theorem wt_erase_one {M : ℕ} (hM : 1 < M) {s : Multiset ℕ} (h1 : 1 ∈ s) :
    wt M s = s.count 1 * wt M (s.erase 1) := by
  unfold wt
  rw [prod_range_split1 hM, prod_range_split1 hM (fun i => i.factorial ^ (s.erase 1).count i *
    ((s.erase 1).count i).factorial), ← mul_assoc]
  congr 1
  · rw [Multiset.count_erase_self, Nat.factorial_one, one_pow, one_pow, one_mul, one_mul,
      ← Nat.succ_pred_eq_of_pos (Multiset.count_pos.mpr h1), Nat.factorial_succ]
    simp
  · refine prod_congr rfl fun j hj => ?_
    rw [Multiset.count_erase_of_ne (Finset.ne_of_mem_erase hj)]

/-- Growing one block from size `j` to `j + 1`: for `t = j ::ₘ s'.erase (j + 1)`,
`wt t * (j + 1) * count (j + 1) s' = wt s' * (count j s' + 1)`. -/
theorem wt_grow {M j : ℕ} (hj : j + 1 < M) {s' : Multiset ℕ} (hmem : j + 1 ∈ s') :
    wt M (j ::ₘ s'.erase (j + 1)) * (j + 1) * s'.count (j + 1) = wt M s' * (s'.count j + 1) := by
  set t := j ::ₘ s'.erase (j + 1) with ht
  have hne : j ≠ j + 1 := by omega
  have hcj : t.count j = s'.count j + 1 := by
    rw [ht, Multiset.count_cons_self, Multiset.count_erase_of_ne hne]
  have hcj1 : t.count (j + 1) = s'.count (j + 1) - 1 := by
    rw [ht, Multiset.count_cons_of_ne hne.symm, Multiset.count_erase_self]
  have hother : ∀ i, i ≠ j → i ≠ j + 1 → t.count i = s'.count i := fun i hi hi' => by
    rw [ht, Multiset.count_cons_of_ne hi, Multiset.count_erase_of_ne hi']
  have hpos : 0 < s'.count (j + 1) := Multiset.count_pos.mpr hmem
  unfold wt
  rw [prod_range_split2 hj (fun i => i.factorial ^ t.count i * (t.count i).factorial),
    prod_range_split2 hj (fun i => i.factorial ^ s'.count i * (s'.count i).factorial)]
  have hrest : ∏ i ∈ ((range M).erase j).erase (j + 1),
      (i.factorial ^ t.count i * (t.count i).factorial) =
      ∏ i ∈ ((range M).erase j).erase (j + 1),
        (i.factorial ^ s'.count i * (s'.count i).factorial) := by
    refine prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_erase.mp hi
    have hi'' := Finset.mem_erase.mp hi'.2
    rw [hother i hi''.1 hi'.1]
  rw [hrest, hcj, hcj1]
  obtain ⟨m, hm⟩ : ∃ m, s'.count (j + 1) = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm, Nat.add_sub_cancel, Nat.factorial_succ (s'.count j), Nat.factorial_succ m,
    Nat.factorial_succ j, pow_succ, pow_succ]
  ring

/-- The number of ordered finpartitions of `Fin n` with block-size multiset `s`. -/
noncomputable def cnt (n : ℕ) (s : Multiset ℕ) : ℕ :=
  (univ.filter fun c : OrderedFinpartition n => sizes c = s).card

theorem cnt_eq_zero_of_zero_mem {s : Multiset ℕ} (h : 0 ∈ s) : cnt n s = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c _ hc
  exact zero_notMem_sizes c (hc ▸ h)

theorem eq_atomic_zero (c : OrderedFinpartition 0) : c = atomic 0 := by
  have hl : c.length = 0 := by rw [← sizes_card, sizes_eq_zero, Multiset.card_zero]
  obtain ⟨l, p, hp, e, h1, h2, h3, h4⟩ := c
  simp only at hl
  subst hl
  have hp' : p = fun _ => 1 := funext fun i => i.elim0
  subst hp'
  have he : e = fun m _ => m := funext fun i => i.elim0
  subst he
  rfl

theorem cnt_zero (s : Multiset ℕ) : cnt 0 s = if s = 0 then 1 else 0 := by
  unfold cnt
  have hu : (univ : Finset (OrderedFinpartition 0)) = {atomic 0} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_univ _, fun c _ => eq_atomic_zero c⟩
  rw [hu, Finset.filter_singleton, sizes_eq_zero]
  by_cases h : s = 0
  · simp [h]
  · simp [h, Ne.symm h]

/-- The recursion for `cnt`, from `OrderedFinpartition.extendEquiv`: a partition of `Fin (n + 1)`
is a partition of `Fin n` with a new singleton block, or with one block grown by one element. -/
theorem cnt_succ (n : ℕ) (s' : Multiset ℕ) :
    cnt (n + 1) s' = (if 1 ∈ s' then cnt n (s'.erase 1) else 0) +
      ∑ j ∈ range (n + 1), if j + 1 ∈ s' then (s'.count j + 1) * cnt n (j ::ₘ s'.erase (j + 1))
        else 0 := by
  classical
  have h1 : cnt (n + 1) s' = ∑ c : OrderedFinpartition n, ∑ o : Option (Fin c.length),
      if sizes (c.extend o) = s' then 1 else 0 := by
    unfold cnt
    rw [Finset.card_filter, ← (extendEquiv n).sum_comp, Fintype.sum_sigma]
    simp only [extendEquiv_apply]
  simp only [Fintype.sum_option, extend_none, extend_some, sizes_extendLeft, sizes_extendMiddle,
    Finset.sum_add_distrib] at h1
  rw [h1]
  congr 1
  · -- the new singleton block
    by_cases hmem : 1 ∈ s'
    · rw [ite_eq_left hmem]
      unfold cnt
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      congr 1
      apply propext
      constructor
      · intro h
        rw [← h, Multiset.erase_cons_head]
      · intro h
        rw [h, Multiset.cons_erase hmem]
    · rw [ite_eq_right hmem]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [ite_eq_right]
      intro h
      exact hmem (h ▸ Multiset.mem_cons_self 1 _)
  · -- growing a block
    have hfib : ∀ c : OrderedFinpartition n, (∑ k : Fin c.length,
        if (c.partSize k + 1) ::ₘ (sizes c).erase (c.partSize k) = s' then 1 else 0) =
        ∑ j ∈ range (n + 1), (sizes c).count j *
          if (j + 1) ::ₘ (sizes c).erase j = s' then 1 else 0 := by
      intro c
      rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range (n + 1)) (g := c.partSize)
        (fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (c.partSize_le k)))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [count_sizes, Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [(Finset.mem_filter.mp hk).2]
    simp_rw [hfib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hmem : j + 1 ∈ s'
    · rw [ite_eq_left hmem]
      unfold cnt
      rw [Finset.card_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : sizes c = j ::ₘ s'.erase (j + 1)
      · rw [ite_eq_left hc, hc, Multiset.erase_cons_head, Multiset.cons_erase hmem, ite_eq_left rfl,
          Multiset.count_cons_self, Multiset.count_erase_of_ne (by omega)]
      · rw [ite_eq_right hc, mul_zero]
        by_cases hj : j ∈ sizes c
        · rw [ite_eq_right, mul_zero]
          intro h
          apply hc
          rw [← h, Multiset.erase_cons_head, Multiset.cons_erase hj]
        · rw [Multiset.count_eq_zero.mpr hj, zero_mul]
    · rw [ite_eq_right hmem]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [ite_eq_right, mul_zero]
      intro h
      exact hmem (h ▸ Multiset.mem_cons_self _ _)

theorem sum_erase_of_mem {s : Multiset ℕ} {a : ℕ} (h : a ∈ s) : (s.erase a).sum + a = s.sum := by
  conv_rhs => rw [← Multiset.cons_erase h]
  rw [Multiset.sum_cons, add_comm]

/-- `s.sum = ∑_{i < M} i * count i s` for `M` beyond the largest element. -/
theorem sum_eq_sum_range_count {M : ℕ} {s : Multiset ℕ} (hM : ∀ j ∈ s, j < M) :
    s.sum = ∑ i ∈ range M, i * s.count i := by
  have h : s.sum = ∑ m ∈ s.toFinset, m * s.count m := by
    have h0 := Finset.sum_multiset_count s
    simpa only [smul_eq_mul, mul_comm] using h0
  rw [h]
  refine Finset.sum_subset (f := fun i => i * s.count i)
    (fun j hj => Finset.mem_range.mpr (hM j (Multiset.mem_toFinset.mp hj))) fun j _ hj => ?_
  rw [Multiset.count_eq_zero.mpr fun h => hj (Multiset.mem_toFinset.mpr h), mul_zero]

/-- The count times the weight is `n!`: by induction on `n` through `cnt_succ`, `wt_erase_one`
and `wt_grow`. -/
theorem cnt_mul_wt : ∀ (n : ℕ) (s : Multiset ℕ), s.sum = n → 0 ∉ s →
    cnt n s * wt (n + 2) s = n.factorial := by
  intro n
  induction n with
  | zero =>
    intro s hs h0
    have : s = 0 := Multiset.eq_zero_of_forall_notMem fun x hx =>
      h0 ((Multiset.sum_eq_zero_iff.mp hs x hx) ▸ hx)
    subst this
    simp [cnt_zero, wt]
  | succ n ih =>
    intro s' hs h0
    have hlt : ∀ j ∈ s', j < n + 2 := fun j hj =>
      Nat.lt_succ_of_le (hs ▸ Multiset.le_sum_of_mem hj)
    have hlt' : ∀ j ∈ s', j < n + 3 := fun j hj => Nat.lt_succ_of_lt (hlt j hj)
    rw [cnt_succ, add_mul, Finset.sum_mul]
    -- the singleton term
    have hA : (if 1 ∈ s' then cnt n (s'.erase 1) else 0) * wt (n + 1 + 2) s' =
        s'.count 1 * n.factorial := by
      by_cases h1 : 1 ∈ s'
      · rw [ite_eq_left h1, wt_erase_one (by omega) h1,
          ← wt_eq_of_lt (M := n + 2) (fun j hj => hlt j (Multiset.mem_of_mem_erase hj)) (by omega),
          ← ih (s'.erase 1) (by have := sum_erase_of_mem h1; omega)
            (fun h => h0 (Multiset.mem_of_mem_erase h))]
        ring
      · rw [ite_eq_right h1, zero_mul, Multiset.count_eq_zero.mpr h1, zero_mul]
    -- the growing terms
    have hB : ∀ j ∈ range (n + 1), (if j + 1 ∈ s' then (s'.count j + 1) *
        cnt n (j ::ₘ s'.erase (j + 1)) else 0) * wt (n + 1 + 2) s' =
        if j = 0 then 0 else (j + 1) * s'.count (j + 1) * n.factorial := by
      intro j hj
      by_cases hmem : j + 1 ∈ s'
      · rw [ite_eq_left hmem]
        by_cases hj0 : j = 0
        · subst hj0
          rw [cnt_eq_zero_of_zero_mem (Multiset.mem_cons_self 0 _), mul_zero, zero_mul,
            ite_eq_left rfl]
        · rw [ite_eq_right hj0]
          have hjlt : j + 1 < n + 3 := by
            have := Finset.mem_range.mp hj
            omega
          have hw := wt_grow hjlt hmem
          have hsum : (j ::ₘ s'.erase (j + 1)).sum = n := by
            rw [Multiset.sum_cons]
            have := sum_erase_of_mem hmem
            omega
          have h0' : 0 ∉ j ::ₘ s'.erase (j + 1) := by
            rw [Multiset.mem_cons]
            rintro (h | h)
            · exact hj0 h.symm
            · exact h0 (Multiset.mem_of_mem_erase h)
          have hih := ih _ hsum h0'
          rw [wt_eq_of_lt (M := n + 2) (M' := n + 3)
            (fun i hi => by
              rw [Multiset.mem_cons] at hi
              rcases hi with rfl | hi
              · omega
              · exact hlt i (Multiset.mem_of_mem_erase hi)) (by omega)] at hih
          calc (s'.count j + 1) * cnt n (j ::ₘ s'.erase (j + 1)) * wt (n + 1 + 2) s'
              = cnt n (j ::ₘ s'.erase (j + 1)) * (wt (n + 3) s' * (s'.count j + 1)) := by ring
            _ = cnt n (j ::ₘ s'.erase (j + 1)) *
                (wt (n + 3) (j ::ₘ s'.erase (j + 1)) * (j + 1) * s'.count (j + 1)) := by rw [hw]
            _ = (j + 1) * s'.count (j + 1) * n.factorial := by rw [← hih]; ring
      · rw [ite_eq_right hmem, zero_mul, Multiset.count_eq_zero.mpr hmem]
        split_ifs <;> ring
    rw [hA, Finset.sum_congr rfl hB, Finset.sum_range_succ', ite_eq_left rfl, add_zero]
    simp only [Nat.succ_ne_zero, ite_eq_right, not_false_eq_true]
    -- ∑_{j < n} (j + 2) m_{j+2} + m₁ = (n + 1)
    have hsum := sum_eq_sum_range_count hlt
    rw [hs, Finset.sum_range_succ', Finset.sum_range_succ'] at hsum
    simp only [zero_mul, add_zero, zero_add, one_mul] at hsum
    rw [Nat.factorial_succ, hsum, add_mul, Finset.sum_mul, add_comm]

/-- **The number of ordered finpartitions of `Fin n` with block sizes `s` is `s.bell`** (this is
the counting interpretation of `Multiset.bell` left as a TODO in Mathlib). -/
theorem cnt_eq_bell {n : ℕ} {s : Multiset ℕ} (hs : s.sum = n) (h0 : 0 ∉ s) : cnt n s = s.bell := by
  have hlt : ∀ j ∈ s, j < n + 2 := fun j hj => by
    have := Multiset.le_sum_of_mem hj
    omega
  have h1 := cnt_mul_wt n s hs h0
  have h2 := bell_mul_wt hlt h0
  rw [hs] at h2
  exact Nat.eq_of_mul_eq_mul_right (wt_pos _ _) (h1.trans h2.symm)

/-- The Faà di Bruno summand depends on the ordered finpartition only through its block sizes. -/
noncomputable def fdbTerm (f g : ℝ → ℝ) (x : ℝ) (s : Multiset ℕ) : ℝ :=
  iteratedDeriv (Multiset.card s) f (g x) * (s.map fun j => iteratedDeriv j g x).prod

theorem fdbTerm_sizes (f g : ℝ → ℝ) (x : ℝ) (c : OrderedFinpartition n) :
    fdbTerm f g x (sizes c) =
      iteratedDeriv c.length f (g x) * ∏ j, iteratedDeriv (c.partSize j) g x := by
  rw [fdbTerm, sizes_card, sizes, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

/-- Faà di Bruno's formula as a sum over the partitions of `n` (block-size multisets), with the
multiplicities `Multiset.bell`. -/
theorem iteratedDeriv_comp_eq_sum_partition {f g : ℝ → ℝ} {x : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n f (g x)) (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n (f ∘ g) x =
      ∑ p : Nat.Partition n, (p.parts.bell : ℝ) * fdbTerm f g x p.parts := by
  classical
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hf hg le_rfl]
  simp_rw [← fdbTerm_sizes f g x]
  rw [Finset.sum_comp (fdbTerm f g x) sizes]
  have hinj : Function.Injective fun p : Nat.Partition n => p.parts := fun p q h =>
    Nat.Partition.ext h
  rw [← Finset.sum_image (f := fun s => (s.bell : ℝ) * fdbTerm f g x s) (s := univ)
    (g := fun p : Nat.Partition n => p.parts) fun p _ q _ h => hinj h]
  have hsub : (univ : Finset (OrderedFinpartition n)).image sizes ⊆
      (univ : Finset (Nat.Partition n)).image fun p => p.parts := by
    intro s hs
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨⟨sizes c, fun hi => Nat.pos_of_ne_zero fun h =>
      zero_notMem_sizes c (h ▸ hi), sizes_sum c⟩, mem_univ _, rfl⟩
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hs
    rw [← cnt_eq_bell p.parts_sum (fun h => (p.parts_pos h).ne rfl), cnt, nsmul_eq_mul]
  · intro s _ hs
    have : (univ.filter fun c : OrderedFinpartition n => sizes c = s) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro c _ hc
      exact hs (Finset.mem_image.mpr ⟨c, mem_univ _, hc⟩)
    rw [this, Finset.card_empty, zero_smul]

/-- The block sizes of a partition of `n` lie in `[1, n]`. -/
theorem partition_toFinset_subset_Icc {n : ℕ} (p : Nat.Partition n) :
    p.parts.toFinset ⊆ Finset.Icc 1 n := fun j hj => by
  rw [Multiset.mem_toFinset] at hj
  exact Finset.mem_Icc.mpr ⟨p.parts_pos hj, p.parts_sum ▸ Multiset.le_sum_of_mem hj⟩

/-- `Multiset.bell` of a partition of `n` in closed form, cast to `ℝ`:
`n! / (∏ⱼ (j!)^{mⱼ} ∏ⱼ mⱼ!)` with `mⱼ = count j`. -/
theorem bell_cast_eq {n : ℕ} (p : Nat.Partition n) :
    (p.parts.bell : ℝ) = n.factorial /
      ((∏ j ∈ p.parts.toFinset, (j.factorial : ℝ) ^ p.parts.count j) *
        ∏ j ∈ p.parts.toFinset, ((p.parts.count j).factorial : ℝ)) := by
  have h0 : p.parts.toFinset.erase 0 = p.parts.toFinset :=
    Finset.erase_eq_of_notMem fun h => (p.parts_pos (Multiset.mem_toFinset.mp h)).ne rfl
  have hbell := Multiset.bell_mul_eq p.parts
  rw [h0, p.parts_sum, Finset.prod_multiset_map_count] at hbell
  rw [eq_div_iff (by positivity), ← mul_assoc]
  exact_mod_cast hbell

end Azurite.DLMF
