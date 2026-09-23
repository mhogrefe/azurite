/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Data.List.Rotate

/-!
# `FoerSequence`: Finite-Or-Eventually-Repeating sequences

A `FoerSequence T` denotes the infinite-or-finite sequence
`nonRepeating ++ (repeating cycled forever)`. An empty `repeating` makes the sequence finite
(just `nonRepeating`). The representation is a *unique canonical form*: the pair
`(nonRepeating, repeating)` is stored in *reduced* form, meaning

1. `repeating` is at its minimal period, and
2. no trailing element of `nonRepeating` can be absorbed into the cycle.

This is a Lean port of Malachite's `RationalSequence`.

This file contains the core list algorithms (`minRepeatingLen`, `trailingCount`, `foerIsReduced`,
`reduce`), the proof that `reduce` produces a reduced pair (`reduce_isReduced`), the bundled type
`FoerSequence`, its smart constructors, accessors, `get`/`set`/`mutate`, and a `ToString` instance.
-/

namespace Azurite

variable {T : Type _} [DecidableEq T]

namespace FoerSequence

/-! ## Core list algorithms -/

/-- `periodicB xs d` checks the *adjacent* period-`d` condition: for every valid `i`,
`xs[i + d] = xs[i]`. Together with `d ∣ xs.length` this says that `xs` equals `xs.take d`
cycled to length `xs.length`. This is the (provably equivalent) internal form of Malachite's
`min_repeating_len` cycle check. -/
def periodicB (xs : List T) (d : Nat) : Bool :=
  (List.range (xs.length - d)).all (fun i => decide (xs[i + d]? = xs[i]?))

/-- `isRepLen xs d` holds when `d` divides `xs.length` and `xs` has period `d`. -/
def isRepLen (xs : List T) (d : Nat) : Bool :=
  (xs.length % d == 0) && periodicB xs d

/-- The smallest `d` with `1 ≤ d ≤ xs.length / 2`, `d ∣ xs.length`, and `xs` equal to `xs.take d`
cycled to `xs.length`; if no such `d` exists, `xs.length`. (For `xs = []` this returns `0`;
callers guard against the empty case.) -/
def minRepeatingLen (xs : List T) : Nat :=
  ((List.range' 1 (xs.length / 2)).find? (fun d => isRepLen xs d)).getD xs.length

/-- `trailingCount a P j` counts the leading run of `a` that matches the pattern `P` read cyclically
starting at index `j`. Used with `a = nonRepeating.reverse`, `P = repeating.reverse` to count how
many trailing elements of `nonRepeating` continue the reverse-cycled `repeating` pattern. -/
def trailingCount (a P : List T) (j : Nat) : Nat :=
  match a with
  | [] => 0
  | x :: a' =>
    match P[j % P.length]? with
    | none => 0
    | some y => if x = y then 1 + trailingCount a' P (j + 1) else 0

/-- Number of trailing elements of `nonRepeating` that match the reverse-cycled `repeating`
(Malachite: `nonRepeating.iter().rev().zip(repeating.iter().rev().cycle()).take_while(==).count()`).
-/
def trailingMatch (nonRepeating repeating : List T) : Nat :=
  trailingCount nonRepeating.reverse repeating.reverse 0

/-- Rotate `ys` to the right by `k` (Malachite `rotate_right`). Since `List.rotate` is a left
rotation, right-rotation by `k` is left-rotation by `ys.length - k`. -/
def rotateRight (ys : List T) (k : Nat) : List T := ys.rotate (ys.length - k)

/-- The checkable reduced invariant. `repeating = []` ⇒ reduced; if `repeating` is not at its
minimal period ⇒ not reduced; `nonRepeating = []` ⇒ reduced; otherwise reduced iff no trailing
`nonRepeating` element can be absorbed into the cycle. -/
def foerIsReduced (nonRepeating repeating : List T) : Bool :=
  if repeating = [] then true
  else if minRepeatingLen repeating ≠ repeating.length then false
  else if nonRepeating = [] then true
  else trailingMatch nonRepeating repeating == 0

/-- Canonicalize a `(nonRepeating, repeating)` pair. Truncate `repeating` to its minimal period,
then absorb any trailing `nonRepeating` elements that continue the cycle (rotating `repeating`
accordingly). -/
def reduce (nonRepeating repeating : List T) : List T × List T :=
  if repeating = [] then (nonRepeating, repeating)
  else
    let rp := repeating.take (minRepeatingLen repeating)
    if nonRepeating = [] then (nonRepeating, rp)
    else
      let extra := trailingMatch nonRepeating rp
      if extra = 0 then (nonRepeating, rp)
      else
        (nonRepeating.take (nonRepeating.length - extra),
          rotateRight rp (extra % rp.length))

/-! ### Periodicity characterization -/

/-- `HasPeriod xs d`: every in-bounds index of `xs` agrees with its residue mod `d`. For `d > 0` and
`d ∣ xs.length` this is exactly "`xs` is `xs.take d` cycled". -/
def HasPeriod (xs : List T) (d : Nat) : Prop :=
  ∀ i, i < xs.length → xs[i]? = xs[i % d]?

theorem periodicB_iff (xs : List T) (d : Nat) :
    periodicB xs d = true ↔ ∀ i, i + d < xs.length → xs[i + d]? = xs[i]? := by
  unfold periodicB
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    have hmem : i ∈ List.range (xs.length - d) := by rw [List.mem_range]; omega
    simpa using h i hmem
  · intro h i hi
    rw [List.mem_range] at hi
    simpa using h i (by omega)

theorem hasPeriod_of_periodicB (xs : List T) (d : Nat) (hd : 0 < d)
    (h : periodicB xs d = true) : HasPeriod xs d := by
  rw [periodicB_iff] at h
  unfold HasPeriod
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases lt_or_ge i d with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
    · have key : xs[i]? = xs[i - d]? := by
        have := h (i - d) (by omega)
        rwa [Nat.sub_add_cancel hge] at this
      rw [key, ih (i - d) (by omega) (by omega), Nat.mod_eq_sub_mod hge]

theorem periodicB_of_hasPeriod (xs : List T) (d : Nat) (h : HasPeriod xs d) :
    periodicB xs d = true := by
  unfold HasPeriod at h
  rw [periodicB_iff]
  intro i hi
  have h1 : xs[i + d]? = xs[(i + d) % d]? := h (i + d) hi
  have h2 : xs[i]? = xs[i % d]? := h i (by omega)
  rw [h1, h2, Nat.add_mod_right]

/-! ### `minRepeatingLen` specification -/

theorem minRepeatingLen_le (xs : List T) : minRepeatingLen xs ≤ xs.length := by
  unfold minRepeatingLen
  cases hf : (List.range' 1 (xs.length / 2)).find? (fun d => isRepLen xs d) with
  | none => simp
  | some b =>
    simp only [Option.getD_some]
    have := List.mem_of_find?_eq_some hf
    rw [List.mem_range'_1] at this
    omega

theorem one_le_minRepeatingLen (xs : List T) (hne : xs ≠ []) : 1 ≤ minRepeatingLen xs := by
  unfold minRepeatingLen
  cases hf : (List.range' 1 (xs.length / 2)).find? (fun d => isRepLen xs d) with
  | none =>
    simp only [Option.getD_none]
    exact Nat.one_le_iff_ne_zero.2 (by simpa [List.length_eq_zero_iff] using hne)
  | some b =>
    simp only [Option.getD_some]
    have := List.mem_of_find?_eq_some hf
    rw [List.mem_range'_1] at this
    omega

theorem isRepLen_minRepeatingLen (xs : List T) (h : minRepeatingLen xs ≠ xs.length) :
    isRepLen xs (minRepeatingLen xs) = true := by
  unfold minRepeatingLen at h ⊢
  cases hf : (List.range' 1 (xs.length / 2)).find? (fun d => isRepLen xs d) with
  | none => rw [hf] at h; simp at h
  | some b =>
    simp only [Option.getD_some]
    simpa using List.find?_some hf

theorem minRepeatingLen_min (xs : List T) (d : Nat)
    (h1 : 1 ≤ d) (h2 : d ≤ xs.length / 2) (h3 : isRepLen xs d = true) :
    minRepeatingLen xs ≤ d := by
  unfold minRepeatingLen
  have hmem : d ∈ List.range' 1 (xs.length / 2) := by rw [List.mem_range'_1]; omega
  cases hf : (List.range' 1 (xs.length / 2)).find? (fun e => isRepLen xs e) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd h3 (by simpa using hf d hmem)
  | some b =>
    simp only [Option.getD_some]
    rw [List.find?_eq_some_iff_getElem] at hf
    obtain ⟨_, i, hi, hbi, hmin⟩ := hf
    -- `d` sits at index `d - 1`
    have hk : d - 1 < (List.range' 1 (xs.length / 2)).length := by
      rw [List.length_range']; omega
    have hLd : (List.range' 1 (xs.length / 2))[d - 1] = d := by
      rw [List.getElem_range']; omega
    have hik : i ≤ d - 1 := by
      by_contra hlt
      push Not at hlt
      have := hmin (d - 1) hlt
      rw [hLd] at this
      simp only [Bool.not_eq_true'] at this
      rw [h3] at this
      exact absurd this (by decide)
    have hLi : (List.range' 1 (xs.length / 2))[i] = 1 + i := by
      rw [List.getElem_range']; omega
    rw [← hbi, hLi]
    omega

theorem minRepeatingLen_eq_length (xs : List T)
    (h : ∀ d, 1 ≤ d → d ≤ xs.length / 2 → isRepLen xs d = false) :
    minRepeatingLen xs = xs.length := by
  unfold minRepeatingLen
  have hnone : (List.range' 1 (xs.length / 2)).find? (fun d => isRepLen xs d) = none := by
    rw [List.find?_eq_none]
    intro x hx
    rw [List.mem_range'_1] at hx
    simp only [Bool.not_eq_true]
    exact h x hx.1 (by omega)
  rw [hnone]; rfl

/-! ### Period composition and rotation invariance -/

omit [DecidableEq T] in
/-- If `rp` has period `m` and its prefix `rp.take m` has period `d ∣ m`, then `rp` has period `d`.
-/
theorem hasPeriod_take_compose (rp : List T) (m d : Nat) (hm : 0 < m) (hd : 0 < d)
    (hml : m ≤ rp.length) (hdm : d ∣ m)
    (hperM : HasPeriod rp m) (hperD : HasPeriod (rp.take m) d) : HasPeriod rp d := by
  unfold HasPeriod at *
  intro i hi
  have him : i % m < m := Nat.mod_lt _ hm
  have hidm : i % d < m := lt_of_lt_of_le (Nat.mod_lt _ hd) (Nat.le_of_dvd hm hdm)
  rw [hperM i hi, ← List.getElem?_take_of_lt him,
    hperD (i % m) (by rw [List.length_take]; omega), Nat.mod_mod_of_dvd i hdm,
    List.getElem?_take_of_lt hidm]

omit [DecidableEq T] in
/-- Period `d` (when `d ∣ length`) is invariant under left rotation. -/
theorem hasPeriod_rotate (L : List T) (d k : Nat) (hd : 0 < d) (hdvd : d ∣ L.length)
    (h : HasPeriod L d) : HasPeriod (L.rotate k) d := by
  unfold HasPeriod at *
  intro i hi
  rw [List.length_rotate] at hi
  have hlen : 0 < L.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have rot : ∀ j, j < L.length → (L.rotate k)[j]? = L[(j + k) % L.length]? := by
    intro j hj
    rw [List.getElem?_eq_getElem (show j < (L.rotate k).length by rw [List.length_rotate]; exact hj),
      List.getElem_rotate, List.getElem?_eq_getElem (Nat.mod_lt _ hlen)]
  have him : i % d < L.length := lt_of_lt_of_le (Nat.mod_lt _ hd) (Nat.le_of_dvd hlen hdvd)
  rw [rot i hi, rot (i % d) him, h _ (Nat.mod_lt _ hlen), h _ (Nat.mod_lt _ hlen),
    Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd]
  have hidx : (i + k) % d = (i % d + k) % d := by
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
  rw [hidx]

/-- Rotating a list at its minimal period keeps it at its minimal period. -/
theorem minRepeatingLen_rotate (L : List T) (k : Nat)
    (hL : minRepeatingLen L = L.length) :
    minRepeatingLen (L.rotate k) = (L.rotate k).length := by
  apply minRepeatingLen_eq_length
  intro d hd1 hd2
  rw [List.length_rotate] at hd2
  by_contra hc
  rw [Bool.not_eq_false] at hc
  unfold isRepLen at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hmod, hper⟩ := hc
  rw [List.length_rotate] at hmod
  have hddvd : d ∣ L.length := Nat.dvd_of_mod_eq_zero (by simpa using hmod)
  have hperRot : HasPeriod (L.rotate k) d := hasPeriod_of_periodicB _ _ hd1 hper
  have hlen : 0 < L.length := by omega
  have hperL : HasPeriod L d := by
    have hback := hasPeriod_rotate (L.rotate k) d (L.length - k % L.length) hd1
      (by rw [List.length_rotate]; exact hddvd) hperRot
    have heq : (L.rotate k).rotate (L.length - k % L.length) = L := by
      rw [List.rotate_rotate]
      have hdm := Nat.div_add_mod k L.length
      have hmk : k % L.length < L.length := Nat.mod_lt _ hlen
      rw [show k + (L.length - k % L.length) = L.length * (k / L.length + 1) by
        rw [Nat.mul_succ]; omega, List.rotate_length_mul]
    rwa [heq] at hback
  have hrep : isRepLen L d = true := by
    unfold isRepLen
    rw [Bool.and_eq_true]
    exact ⟨by simp [Nat.mod_eq_zero_of_dvd hddvd], periodicB_of_hasPeriod _ _ hperL⟩
  have := minRepeatingLen_min L d hd1 (by omega) hrep
  omega

/-- `minRepeatingLen rp` is a genuine period of `rp` that divides its length. -/
theorem minRepeatingLen_hasPeriod (rp : List T) (hne : rp ≠ []) :
    HasPeriod rp (minRepeatingLen rp) ∧ (minRepeatingLen rp ∣ rp.length) := by
  by_cases hcase : minRepeatingLen rp = rp.length
  · refine ⟨?_, ?_⟩
    · unfold HasPeriod
      intro i hi
      rw [hcase, Nat.mod_eq_of_lt hi]
    · rw [hcase]; exact Nat.dvd_refl _
  · have hrep : isRepLen rp (minRepeatingLen rp) = true := isRepLen_minRepeatingLen rp hcase
    unfold isRepLen at hrep
    rw [Bool.and_eq_true] at hrep
    obtain ⟨hmod, hper⟩ := hrep
    exact ⟨hasPeriod_of_periodicB _ _ (one_le_minRepeatingLen rp hne) hper,
      Nat.dvd_of_mod_eq_zero (by simpa using hmod)⟩

/-- Truncating `rp` to its minimal period yields a list already at its minimal period (lemma A). -/
theorem minRepeatingLen_take (rp : List T) (hne : rp ≠ []) :
    minRepeatingLen (rp.take (minRepeatingLen rp)) = (rp.take (minRepeatingLen rp)).length := by
  set m := minRepeatingLen rp with hmdef
  have hmlen : m ≤ rp.length := minRepeatingLen_le rp
  have hm1 : 1 ≤ m := one_le_minRepeatingLen rp hne
  have hrp'len : (rp.take m).length = m := by rw [List.length_take]; omega
  apply minRepeatingLen_eq_length
  intro d hd1 hd2
  rw [hrp'len] at hd2
  by_contra hc
  rw [Bool.not_eq_false] at hc
  unfold isRepLen at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hmod, hper⟩ := hc
  rw [hrp'len] at hmod
  have hddvd : d ∣ m := Nat.dvd_of_mod_eq_zero (by simpa using hmod)
  have hperD : HasPeriod (rp.take m) d := hasPeriod_of_periodicB _ _ hd1 hper
  obtain ⟨hperM, hmdvd⟩ := minRepeatingLen_hasPeriod rp hne
  rw [← hmdef] at hperM hmdvd
  have hperRpd : HasPeriod rp d :=
    hasPeriod_take_compose rp m d (by omega) hd1 hmlen hddvd hperM hperD
  have hrep : isRepLen rp d = true := by
    unfold isRepLen
    rw [Bool.and_eq_true]
    refine ⟨?_, periodicB_of_hasPeriod _ _ hperRpd⟩
    have h0 : rp.length % d = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hddvd hmdvd)
    simp [h0]
  have hle := minRepeatingLen_min rp d hd1 (by omega) hrep
  rw [← hmdef] at hle
  omega

/-! ### `trailingCount` -/

theorem trailingCount_cons (x : T) (a' Q : List T) (j : Nat) (hjlt : j % Q.length < Q.length) :
    trailingCount (x :: a') Q j =
      if x = Q[j % Q.length]'hjlt then 1 + trailingCount a' Q (j + 1) else 0 := by
  rw [trailingCount, List.getElem?_eq_getElem hjlt]

/-- When `trailingCount` stops before exhausting `a`, the element at the stopping index disagrees
with the pattern element it was compared against. -/
theorem trailingCount_stop (a Q : List T) (j : Nat) (hQ : Q ≠ [])
    (h : trailingCount a Q j < a.length) :
    a[trailingCount a Q j]? ≠ Q[(j + trailingCount a Q j) % Q.length]? := by
  induction a generalizing j with
  | nil => simp at h
  | cons x a' ih =>
    have hjlt : j % Q.length < Q.length := Nat.mod_lt _ (List.length_pos_of_ne_nil hQ)
    rw [trailingCount_cons x a' Q j hjlt] at h ⊢
    by_cases hxy : x = Q[j % Q.length]'hjlt
    · rw [ite_eq_left hxy] at h ⊢
      have hc' : trailingCount a' Q (j + 1) < a'.length := by
        rw [List.length_cons] at h; omega
      have hih := ih (j + 1) hc'
      rw [show (1 : Nat) + trailingCount a' Q (j + 1) = trailingCount a' Q (j + 1) + 1 from by omega,
        List.getElem?_cons_succ,
        show j + (trailingCount a' Q (j + 1) + 1) = (j + 1) + trailingCount a' Q (j + 1) from by omega]
      exact hih
    · rw [ite_eq_right hxy, Nat.add_zero, List.getElem?_cons_zero, List.getElem?_eq_getElem hjlt]
      simpa using hxy

/-- If the first element of `a` already disagrees with the pattern, `trailingCount` is `0`. -/
theorem trailingCount_head_ne (a Q : List T) (j : Nat) (hQ : Q ≠ []) (ha : a ≠ [])
    (hne : a[0]? ≠ Q[j % Q.length]?) : trailingCount a Q j = 0 := by
  obtain ⟨x, a', rfl⟩ := List.exists_cons_of_ne_nil ha
  have hjlt : j % Q.length < Q.length := Nat.mod_lt _ (List.length_pos_of_ne_nil hQ)
  rw [trailingCount_cons x a' Q j hjlt, ite_eq_right]
  intro heq
  exact hne (by rw [List.getElem?_cons_zero, List.getElem?_eq_getElem hjlt, heq])

/-- Lemma C: after absorbing `e = trailingCount …` trailing elements and rotating the cycle, no
trailing element of the shortened `nonRepeating` matches the rotated cycle. -/
theorem trailingMatch_reduce (nr rp' : List T) (hrp' : rp' ≠ [])
    (he_lt : trailingCount nr.reverse rp'.reverse 0 < nr.length) :
    trailingCount
      (nr.take (nr.length - trailingCount nr.reverse rp'.reverse 0)).reverse
      (rotateRight rp' (trailingCount nr.reverse rp'.reverse 0 % rp'.length)).reverse 0 = 0 := by
  set e := trailingCount nr.reverse rp'.reverse 0 with hedef
  set m := rp'.length with hmdef
  have hm1 : 0 < m := List.length_pos_of_ne_nil hrp'
  have hem : e % m < m := Nat.mod_lt _ hm1
  have hnrl : (nr.take (nr.length - e)).length = nr.length - e := by rw [List.length_take]; omega
  -- the stopping element from the original count
  have hstop := trailingCount_stop nr.reverse rp'.reverse 0
    (by rw [ne_eq, List.reverse_eq_nil_iff]; exact hrp')
    (by rw [List.length_reverse]; exact he_lt)
  rw [← hedef, Nat.zero_add, List.length_reverse, List.getElem?_reverse he_lt,
    List.getElem?_reverse (show e % rp'.length < rp'.length from hmdef ▸ hem), ← hmdef] at hstop
  -- left element of the reduced comparison
  have hLeft : (nr.take (nr.length - e)).reverse[0]? = nr[nr.length - 1 - e]? := by
    rw [List.getElem?_reverse (by rw [hnrl]; omega), hnrl,
      List.getElem?_take_of_lt (by omega)]
    congr 1
    omega
  -- right element of the reduced comparison
  have hRight : (rotateRight rp' (e % m)).reverse[0 % (rotateRight rp' (e % m)).reverse.length]?
              = rp'[m - 1 - e % m]? := by
    unfold rotateRight
    rw [List.length_reverse, List.length_rotate, ← hmdef, Nat.zero_mod,
      List.getElem?_reverse (by rw [List.length_rotate, ← hmdef]; omega),
      List.length_rotate, ← hmdef, List.getElem?_rotate (by rw [← hmdef]; omega)]
    congr 1
    rw [← hmdef]
    rw [show m - 1 - 0 + (m - e % m) = (m - 1 - e % m) + 1 * m from by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  refine trailingCount_head_ne _ _ 0 ?_ ?_ ?_
  · rw [ne_eq, List.reverse_eq_nil_iff]; unfold rotateRight; rw [List.rotate_eq_nil_iff]; exact hrp'
  · have hpos : 0 < (nr.take (nr.length - e)).length := by rw [hnrl]; omega
    rw [ne_eq, List.reverse_eq_nil_iff]
    exact List.ne_nil_of_length_pos hpos
  · rw [hLeft, hRight]; exact hstop

/-! ### `reduce` produces a reduced pair -/

theorem foerIsReduced_nil_left (rp' : List T) (h : minRepeatingLen rp' = rp'.length) :
    foerIsReduced [] rp' = true := by
  unfold foerIsReduced
  by_cases hrp' : rp' = []
  · rw [ite_eq_left hrp']
  · rw [ite_eq_right hrp', ite_eq_right (not_not_intro h), ite_eq_left rfl]

/-- Canonicalization produces a canonical (reduced) form. -/
theorem reduce_isReduced (nr rp : List T) :
    foerIsReduced (reduce nr rp).1 (reduce nr rp).2 = true := by
  by_cases hrp : rp = []
  · subst hrp; simp [reduce, foerIsReduced]
  · have hm1 : 1 ≤ minRepeatingLen rp := one_le_minRepeatingLen rp hrp
    have hmlen : minRepeatingLen rp ≤ rp.length := minRepeatingLen_le rp
    have hrp'len : (rp.take (minRepeatingLen rp)).length = minRepeatingLen rp := by
      rw [List.length_take]; omega
    have hrp'ne : rp.take (minRepeatingLen rp) ≠ [] :=
      List.ne_nil_of_length_pos (by rw [hrp'len]; omega)
    have hAred : minRepeatingLen (rp.take (minRepeatingLen rp))
        = (rp.take (minRepeatingLen rp)).length := minRepeatingLen_take rp hrp
    by_cases hnr : nr = []
    · rw [show reduce nr rp = (nr, rp.take (minRepeatingLen rp)) from by
        unfold reduce; rw [ite_eq_right hrp, ite_eq_left hnr]]
      subst hnr
      exact foerIsReduced_nil_left _ hAred
    · by_cases hextra : trailingMatch nr (rp.take (minRepeatingLen rp)) = 0
      · rw [show reduce nr rp = (nr, rp.take (minRepeatingLen rp)) from by
          unfold reduce; rw [ite_eq_right hrp, ite_eq_right hnr, ite_eq_left hextra]]
        show foerIsReduced nr (rp.take (minRepeatingLen rp)) = true
        unfold foerIsReduced
        rw [ite_eq_right hrp'ne, ite_eq_right (not_not_intro hAred), ite_eq_right hnr]
        simp [hextra]
      · rw [show reduce nr rp
              = (nr.take (nr.length - trailingMatch nr (rp.take (minRepeatingLen rp))),
                  rotateRight (rp.take (minRepeatingLen rp))
                    (trailingMatch nr (rp.take (minRepeatingLen rp))
                      % (rp.take (minRepeatingLen rp)).length)) from by
          unfold reduce; rw [ite_eq_right hrp, ite_eq_right hnr, ite_eq_right hextra]]
        show foerIsReduced (nr.take (nr.length - trailingMatch nr (rp.take (minRepeatingLen rp))))
            (rotateRight (rp.take (minRepeatingLen rp))
              (trailingMatch nr (rp.take (minRepeatingLen rp))
                % (rp.take (minRepeatingLen rp)).length)) = true
        set rp' := rp.take (minRepeatingLen rp) with hrp'def
        set e := trailingMatch nr rp' with hedef
        set rp'' := rotateRight rp' (e % rp'.length) with hrp''def
        set nr'' := nr.take (nr.length - e) with hnr''def
        have hrp''ne : rp'' ≠ [] := by
          rw [hrp''def]; unfold rotateRight; rw [ne_eq, List.rotate_eq_nil_iff]; exact hrp'ne
        have hB : minRepeatingLen rp'' = rp''.length := by
          rw [hrp''def]; unfold rotateRight; exact minRepeatingLen_rotate _ _ hAred
        unfold foerIsReduced
        rw [ite_eq_right hrp''ne, ite_eq_right (not_not_intro hB)]
        by_cases hnr'' : nr'' = []
        · rw [ite_eq_left hnr'']
        · rw [ite_eq_right hnr'']
          have he_lt : e < nr.length := by
            have hpos : 0 < nr''.length := List.length_pos_of_ne_nil hnr''
            rw [hnr''def, List.length_take] at hpos
            omega
          have hkey : trailingMatch nr'' rp'' = 0 := by
            rw [hnr''def, hrp''def, hedef]
            unfold trailingMatch
            exact trailingMatch_reduce nr rp' hrp'ne
              (by rw [hedef] at he_lt; unfold trailingMatch at he_lt; exact he_lt)
          simp [hkey]

/-! ### Computational sanity checks (translation validation) -/

-- `min_repeating_len` doctests
#guard minRepeatingLen ([1, 2, 1, 2, 1, 2] : List Nat) == 2
#guard minRepeatingLen ([1, 2, 1, 2, 1, 3] : List Nat) == 6
#guard minRepeatingLen ([5, 5, 5] : List Nat) == 1

-- `reduce` doctests (raw pair form)
#guard reduce ([] : List Nat) [] == ([], [])
#guard reduce ([] : List Nat) [1, 2] == ([], [1, 2])
#guard reduce ([1, 2] : List Nat) [] == ([1, 2], [])
#guard reduce ([1, 2] : List Nat) [3, 4] == ([1, 2], [3, 4])
#guard reduce ([1, 2, 3] : List Nat) [4, 3] == ([1, 2], [3, 4])
#guard reduce ([] : List Nat) [3, 4, 3, 4] == ([], [3, 4])

end FoerSequence

/-! ## The bundled `FoerSequence` type -/

/-- A canonical Finite-Or-Eventually-Repeating sequence: it denotes
`nonRepeating ++ (repeating cycled forever)`, stored in reduced (unique canonical) form. -/
structure FoerSequence (T : Type _) [DecidableEq T] where
  /-- The non-repeating prefix. -/
  nonRepeating : List T
  /-- The repeating cycle (empty ⇒ the sequence is finite). -/
  repeating : List T
  /-- The stored pair is reduced (minimal period, no absorbable trailing prefix element). -/
  reduced : FoerSequence.foerIsReduced nonRepeating repeating = true

namespace FoerSequence

variable {T : Type _} [DecidableEq T]

/-- Two sequences are equal when their two component lists agree (`reduced` is a proposition). -/
@[ext] theorem ext {s t : FoerSequence T} (hn : s.nonRepeating = t.nonRepeating)
    (hr : s.repeating = t.repeating) : s = t := by
  cases s; cases t; cases hn; cases hr; rfl

instance : DecidableEq (FoerSequence T) := fun s t =>
  decidable_of_iff (s.nonRepeating = t.nonRepeating ∧ s.repeating = t.repeating)
    ⟨fun ⟨hn, hr⟩ => ext hn hr, fun h => h ▸ ⟨rfl, rfl⟩⟩

/-! ### Smart constructors and conversions -/

/-- Build a `FoerSequence` from a non-repeating and a repeating list, canonicalizing. -/
def ofLists (nr rp : List T) : FoerSequence T :=
  ⟨(reduce nr rp).1, (reduce nr rp).2, reduce_isReduced nr rp⟩

/-- Build a finite `FoerSequence` from a single list. -/
def ofList (nr : List T) : FoerSequence T := ofLists nr []

instance : Inhabited (FoerSequence T) := ⟨ofList []⟩

/-- The non-repeating and repeating component lists. -/
def toLists (s : FoerSequence T) : List T × List T := (s.nonRepeating, s.repeating)

/-- References to the non-repeating and repeating component lists. -/
def slicesRef (s : FoerSequence T) : List T × List T := (s.nonRepeating, s.repeating)

/-! ### Accessors -/

/-- Whether the sequence is empty. -/
def isEmpty (s : FoerSequence T) : Bool := s.nonRepeating.isEmpty && s.repeating.isEmpty

/-- Whether the sequence is finite (has no repeating part). -/
def isFinite (s : FoerSequence T) : Bool := s.repeating.isEmpty

/-- The length of the sequence, or `none` if it is infinite. -/
def len (s : FoerSequence T) : Option Nat :=
  if s.repeating = [] then some s.nonRepeating.length else none

/-- The sum of the lengths of the two component lists. -/
def componentLen (s : FoerSequence T) : Nat := s.nonRepeating.length + s.repeating.length

/-! ### Get and set -/

/-- The element at index `i`, or `none` if `i` is past the end of a finite sequence. -/
def get (s : FoerSequence T) (i : Nat) : Option T :=
  if i < s.nonRepeating.length then s.nonRepeating[i]?
  else if s.repeating = [] then none
  else s.repeating[(i - s.nonRepeating.length) % s.repeating.length]?

/-- Apply `f` to the element at index `i`, returning the updated (re-canonicalized) sequence, or
`none` if `i` is out of bounds (past the end of a finite sequence). -/
def mutate (s : FoerSequence T) (i : Nat) (f : T → T) : Option (FoerSequence T) :=
  let nr := s.nonRepeating
  let rp := s.repeating
  if h : i < nr.length then
    some (ofLists (nr.set i (f (nr[i]'h))) rp)
  else if rp = [] then none
  else
    let extra := i - nr.length + 1
    let cyc := (List.replicate (extra / rp.length + 1) rp).flatten.take extra
    let nr2 := nr ++ cyc
    let rp2 := rp.rotate (extra % rp.length)
    if h2 : i < nr2.length then
      some (ofLists (nr2.set i (f (nr2[i]'h2))) rp2)
    else none

/-- Set the element at index `i` to `x`, returning the updated sequence, or `none` if out of
bounds. -/
def set (s : FoerSequence T) (i : Nat) (x : T) : Option (FoerSequence T) :=
  s.mutate i (fun _ => x)

/-! ### `ToString` -/

instance [ToString T] : ToString (FoerSequence T) where
  toString s :=
    let render (l : List T) : String := String.intercalate ", " (l.map toString)
    "[" ++ render s.nonRepeating ++
      (if s.repeating = [] then ""
        else (if s.nonRepeating = [] then "" else ", ") ++ "[" ++ render s.repeating ++ "]") ++ "]"

/-! ### Guards: Malachite doctests -/

-- `Display` / `from_slices` doctests
#guard toString (ofLists ([] : List Nat) []) == "[]"
#guard toString (ofLists ([] : List Nat) [1, 2]) == "[[1, 2]]"
#guard toString (ofLists ([1, 2] : List Nat) []) == "[1, 2]"
#guard toString (ofLists ([1, 2] : List Nat) [3, 4]) == "[1, 2, [3, 4]]"
-- the absorb + rotate canonicalization
#guard toString (ofLists ([1, 2, 3] : List Nat) [4, 3]) == "[1, 2, [3, 4]]"
-- minimal period
#guard toString (ofLists ([] : List Nat) [3, 4, 3, 4]) == "[[3, 4]]"

-- `get`
#guard (ofLists ([1, 2] : List Nat) [3, 4]).get 1 == some 2
#guard (ofLists ([1, 2] : List Nat) [3, 4]).get 10 == some 3

-- `mutate`
#guard (ofLists ([1, 2] : List Nat) [3, 4]).mutate 1 (fun _ => 100)
  == some (ofLists [1, 100] [3, 4])
#guard (ofLists ([1, 2] : List Nat) [3, 4]).mutate 6 (fun _ => 100)
  == some (ofLists [1, 2, 3, 4, 3, 4, 100] [4, 3])

-- `isEmpty`
#guard (ofList ([] : List Nat)).isEmpty == true
#guard (ofList ([1, 2, 3] : List Nat)).isEmpty == false
#guard (ofLists ([] : List Nat) [3, 4]).isEmpty == false
#guard (ofLists ([1, 2] : List Nat) [3, 4]).isEmpty == false

-- `isFinite`
#guard (ofList ([] : List Nat)).isFinite == true
#guard (ofList ([1, 2, 3] : List Nat)).isFinite == true
#guard (ofLists ([] : List Nat) [3, 4]).isFinite == false
#guard (ofLists ([1, 2] : List Nat) [3, 4]).isFinite == false

-- `len`
#guard (ofList ([] : List Nat)).len == some 0
#guard (ofList ([1, 2, 3] : List Nat)).len == some 3
#guard (ofLists ([] : List Nat) [3, 4]).len == none
#guard (ofLists ([1, 2] : List Nat) [3, 4]).len == none

-- `componentLen`
#guard (ofList ([] : List Nat)).componentLen == 0
#guard (ofList ([1, 2, 3] : List Nat)).componentLen == 3
#guard (ofLists ([] : List Nat) [3, 4]).componentLen == 2
#guard (ofLists ([1, 2] : List Nat) [3, 4]).componentLen == 4

end FoerSequence

end Azurite
