/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.CoeffChars
import Mathlib.Data.String.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

namespace Azurite.AzPolynomial

/-!
# Char-level String Lemmas for coefficient conversions

This file contains pure character-list lemmas about the primitive coefficient
conversions (`natToChars`, `intToChars`, `ratToChars`, `zmodToChars`) and their
parsers. These lemmas are consumed by `AzMvPolynomial.ParsableCoeff` to build
the `ParsableCoeff` instances for `ℕ`, `ℤ`, `ℚ`, and `ZMod n`.

The old display-layer / `AzPolynomial R` lemmas live in their own modules now
that `AzPolynomial/ToString.lean` and `AzPolynomial/Parse.lean` are thin facades
over `AzMvPolynomial`.
-/

/-! ### Char and digit helpers -/

lemma char_ofNat_ne_dash (n : ℕ) : Char.ofNat ('0'.toNat + n % 10) ≠ '-' := by
  have h_mod : n % 10 < 10 := Nat.mod_lt _ (by decide)
  generalize h : n % 10 = k
  rw [h] at h_mod
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals { first | decide | contradiction}

lemma not_mem_natToCharsAux (f n : ℕ) (acc : List Char) (h : '-' ∉ acc) :
  '-' ∉ natToCharsAux f n acc := by
  induction f generalizing n acc with
  | zero => exact h
  | succ f ih =>
    dsimp [natToCharsAux]
    split
    · exact h
    · apply ih
      intro hc
      rw [List.mem_cons] at hc
      rcases hc with h_head | h_tail
      · exact char_ofNat_ne_dash n h_head.symm
      · exact h h_tail

lemma not_mem_natToChars (n : ℕ) : '-' ∉ natToChars n := by
  dsimp [natToChars]
  split
  · intro hc; nomatch hc
  · apply not_mem_natToCharsAux
    intro hc; nomatch hc

lemma not_mem_tail_intToChars (z : ℤ) : '-' ∉ (intToChars z).drop 1 := by
  dsimp [intToChars]
  split
  · split
    · decide
    · dsimp [List.drop]
      apply not_mem_natToCharsAux
      intro hc; nomatch hc
  · split
    · decide
    · intro hc
      exact not_mem_natToCharsAux _ _ _ (by intro hc2; nomatch hc2) (List.mem_of_mem_drop hc)

lemma natToCharsAux_ne_nil_of_acc_ne_nil (f n : ℕ) (acc : List Char) (h : acc ≠ []) :
    natToCharsAux f n acc ≠ [] := by
  induction f generalizing n acc with
  | zero => exact h
  | succ f ih =>
    dsimp [natToCharsAux]
    split
    · exact h
    · apply ih
      intro hc
      contradiction

lemma natToCharsAux_ne_nil_of_ne_zero (f n : ℕ) (h : n ≠ 0) :
    natToCharsAux (f + 1) n [] ≠ [] := by
  dsimp [natToCharsAux]
  split
  · contradiction
  · apply natToCharsAux_ne_nil_of_acc_ne_nil
    intro hc; contradiction

lemma natToChars_ne_nil (n : ℕ) : natToChars n ≠ [] := by
  dsimp [natToChars]
  split_ifs with hn
  · intro hc; contradiction
  · cases n
    · contradiction
    · rename_i k
      exact natToCharsAux_ne_nil_of_ne_zero k (k+1) (by simp)

lemma zmodToChars_ne_nil {n : ℕ} [NeZero n] (c : ZMod n) : zmodToChars c ≠ [] := by
  dsimp [zmodToChars]
  exact natToChars_ne_nil c.val

lemma intToChars_ne_nil (z : ℤ) : intToChars z ≠ [] := by
  dsimp [intToChars]
  split
  · split
    · intro hc; contradiction
    · intro hc; contradiction
  · split
    · intro hc; contradiction
    · cases hz : z.natAbs
      · contradiction
      · rename_i k
        apply natToCharsAux_ne_nil_of_ne_zero k (k+1)
        intro hc; contradiction

lemma ratToChars_ne_nil (q : ℚ) : ratToChars q ≠ [] := by
  dsimp [ratToChars]
  split
  · exact intToChars_ne_nil _
  · have h_int := intToChars_ne_nil q.num
    cases h : intToChars q.num
    · contradiction
    · intro hc
      contradiction

lemma not_mem_tail_ratToChars (q : ℚ) : '-' ∉ (ratToChars q).drop 1 := by
  dsimp [ratToChars]
  split
  · exact not_mem_tail_intToChars _
  · have h_int := intToChars_ne_nil q.num
    cases h : intToChars q.num
    · contradiction
    · rename_i head tail
      dsimp [List.drop]
      intro hc
      rw [List.mem_append] at hc
      cases hc with
      | inl h_tail =>
        have h_int_tail : '-' ∉ tail := by
          have ht := not_mem_tail_intToChars q.num
          rw [h] at ht
          exact ht
        rw [List.mem_append] at h_tail
        cases h_tail with
        | inl ht' => exact h_int_tail ht'
        | inr hdiv => nomatch hdiv
      | inr h_rest =>
        exact not_mem_natToChars _ h_rest

lemma natToChars_not_dash (n : ℕ) (cs : List Char) : natToChars n = '-' :: cs → False := by
  intro h
  have h_parse := parseNatChars_natToChars n
  rw [h] at h_parse
  have h_none : parseNatChars ('-' :: cs) = none := rfl
  rw [h_none] at h_parse
  contradiction

lemma intToChars_natAbs (z : ℤ) :
    intToChars z = if z < 0 then '-' :: natToChars z.natAbs else natToChars z.natAbs := by
  unfold intToChars natToChars
  dsimp only
  split_ifs
  any_goals rfl
  any_goals omega

lemma parseIntChars_intToChars (z : ℤ) : parseIntChars (intToChars z) = some z := by
  rw [intToChars_natAbs]
  split_ifs with hz
  · change (parseNatChars (natToChars z.natAbs)).map (fun n => - (n : ℤ)) = some z
    have h_parse := parseNatChars_natToChars z.natAbs
    rw [h_parse]
    dsimp
    congr 1
    omega
  · have hz_nonneg : 0 ≤ z := by omega
    cases h_chars : natToChars z.natAbs with
    | nil =>
      have h_parse := parseNatChars_natToChars z.natAbs
      rw [h_chars] at h_parse
      contradiction
    | cons c cs =>
      by_cases h_c : c = '-'
      · subst h_c
        exfalso
        exact natToChars_not_dash z.natAbs cs h_chars
      · have h_parse_int : parseIntChars (c :: cs) =
            (parseNatChars (c :: cs)).map (fun n => (n : ℤ)) := by
          unfold parseIntChars
          split
          · contradiction
          · rename_i rest h_eq
            injection h_eq with h_c_eq
            contradiction
          · rfl
        rw [h_parse_int]
        have h_parse := parseNatChars_natToChars z.natAbs
        rw [h_chars] at h_parse
        rw [h_parse]
        dsimp
        congr 1
        omega

lemma not_mem_natToCharsAux_of_not_digit (c : Char) (hc : c.toNat < 48 ∨ 57 < c.toNat)
    (fuel n : ℕ) (acc : List Char) (h : c ∉ acc) :
    c ∉ natToCharsAux fuel n acc := by
  induction fuel generalizing n acc with
  | zero => exact h
  | succ f ih =>
    dsimp [natToCharsAux]
    split_ifs with hn
    · exact h
    · apply ih
      simp only [List.mem_cons, not_or]
      constructor
      · intro hc_eq
        have hd : (Char.ofNat (48 + n % 10)).toNat - 48 = n % 10 := toNat_digit n
        rw [← hc_eq] at hd
        have h_lt : n % 10 < 10 := Nat.mod_lt _ (by decide)
        rw [← hd] at h_lt
        cases hc with
        | inl h1 =>
          have h_sub : c.toNat - 48 = 0 := by omega
          have h_mod : n % 10 = 0 := by omega
          have h_c_0 : c = '0' := by
            rw [h_mod] at hc_eq
            exact hc_eq
          have ht : '0'.toNat = 48 := rfl
          rw [h_c_0, ht] at h1
          omega
        | inr h2 =>
          omega
      · exact h

lemma not_mem_natToChars_of_not_digit (c : Char) (hc : c.toNat < 48 ∨ 57 < c.toNat) (n : ℕ) :
    c ∉ natToChars n := by
  unfold natToChars
  split_ifs with hn
  · intro hc_eq; simp at hc_eq
    have ht : '0'.toNat = 48 := rfl
    have hc_toNat : c.toNat = 48 := by
      rw [hc_eq, ht]
    rw [hc_toNat] at hc
    omega
  · exact not_mem_natToCharsAux_of_not_digit c hc _ _ _ (by simp)

lemma mem_natToChars_only_digits (n : ℕ) (c : Char) (h : c ∈ natToChars n) :
    '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat := by
  by_contra hc
  rw [not_and_or, not_le, not_le] at hc
  have h_not_mem := not_mem_natToChars_of_not_digit c hc n
  contradiction

lemma mem_intToChars_only_digits_or_dash (z : ℤ) (c : Char) (h : c ∈ intToChars z) :
    c = '-' ∨ ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat) := by
  rw [intToChars_natAbs] at h
  split_ifs at h with hz
  · rcases (List.mem_cons.mp h) with rfl | h_nat
    · exact Or.inl rfl
    · exact Or.inr (mem_natToChars_only_digits _ _ h_nat)
  · exact Or.inr (mem_natToChars_only_digits _ _ h)

lemma mem_ratToChars_only_digits_or_dash_or_slash (q : ℚ) (c : Char) (h : c ∈ ratToChars q) :
    c = '/' ∨ c = '-' ∨ ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat) := by
  dsimp [ratToChars] at h
  split_ifs at h with hd
  · rcases (mem_intToChars_only_digits_or_dash _ _ h) with rfl | h_dig
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr h_dig)
  · have h_assoc : intToChars q.num ++ ['/'] ++ natToChars q.den
        = (intToChars q.num ++ ['/']) ++ natToChars q.den := rfl
    rw [h_assoc] at h
    rcases (List.mem_append.mp h) with h_int_slash | h_nat
    · rcases (List.mem_append.mp h_int_slash) with h_int | h_slash
      · rcases (mem_intToChars_only_digits_or_dash _ _ h_int) with rfl | h_dig
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr h_dig)
      · rcases (List.mem_cons.mp h_slash) with rfl | hk
        · exact Or.inl rfl
        · contradiction
    · exact Or.inr (Or.inr (mem_natToChars_only_digits _ _ h_nat))

/-! ### `'/'` not in `natToChars` / `intToChars`, used by `parseRatChars_ratToChars`. -/

lemma not_mem_natToCharsAux_div (fuel n : ℕ) (acc : List Char) (h : '/' ∉ acc) :
    '/' ∉ natToCharsAux fuel n acc := by
  induction fuel generalizing n acc with
  | zero => exact h
  | succ f ih =>
    dsimp [natToCharsAux]
    split_ifs with hn
    · exact h
    · apply ih
      simp only [List.mem_cons, not_or]
      constructor
      · intro hc
        have hd : (Char.ofNat (48 + n % 10)).toNat - 48 = n % 10 := toNat_digit n
        rw [← hc] at hd
        have h47 : '/'.toNat = 47 := rfl
        rw [h47] at hd
        have h_sub : 47 - 48 = 0 := rfl
        rw [h_sub] at hd
        have h_mod_0 : n % 10 = 0 := hd.symm
        rw [h_mod_0] at hc
        revert hc
        decide
      · exact h

lemma not_mem_natToChars_div (n : ℕ) : '/' ∉ natToChars n := by
  unfold natToChars
  split_ifs with hn
  · intro hc; simp at hc
  · exact not_mem_natToCharsAux_div _ _ _ (by simp)

lemma not_mem_intToChars (z : ℤ) : '/' ∉ intToChars z := by
  rw [intToChars_natAbs]
  split_ifs with hz
  · intro hc
    simp only [List.mem_cons] at hc
    cases hc with
    | inl hl =>
       have h_val := congrArg Char.toNat hl
       have h47 : '/'.toNat = 47 := rfl
       have h45 : '-'.toNat = 45 := rfl
       rw [h47, h45] at h_val
       contradiction
    | inr hr => exact not_mem_natToChars_div _ hr
  · exact not_mem_natToChars_div _

/-! ### Generic `splitOn` infrastructure

These lemmas handle splitting on any character separator. They are used to
implement `parseRatChars_ratToChars`.
-/

/-- Step past a non-separator character in `splitOnPPrepend`. -/
private lemma splitOnP_go_cons_false (sep x : Char) (xs acc : List Char)
    (h : (x == sep) = false) :
    List.splitOnPPrepend (· == sep) (x :: xs) acc =
    List.splitOnPPrepend (· == sep) xs (x :: acc) := by
  exact List.splitOnPPrepend_cons_neg h

/-- Step past the separator character, resetting the accumulator. -/
private lemma splitOnP_go_cons_true (sep : Char) (xs acc : List Char) :
    List.splitOnPPrepend (· == sep) (sep :: xs) acc =
    acc.reverse :: List.splitOnPPrepend (· == sep) xs [] := by
  exact List.splitOnPPrepend_cons_pos (beq_self_eq_true sep)

/-- If `sep ∉ l`, the go passes through, producing `[acc.reverse ++ l]`. -/
private lemma splitOnP_go_not_mem (sep : Char) (l acc : List Char) (h : sep ∉ l) :
    List.splitOnPPrepend (· == sep) l acc = [acc.reverse ++ l] := by
  induction l generalizing acc with
  | nil => simp [List.splitOnPPrepend]
  | cons x xs ih =>
    have hxq : (x == sep) = false := by
      simp only [beq_eq_false_iff_ne]; intro hx; subst hx; exact h (List.Mem.head _)
    simp only [splitOnP_go_cons_false sep x xs acc hxq]
    rw [ih (x :: acc) (fun hc => h (List.Mem.tail _ hc))]
    simp [List.reverse_cons, List.append_assoc]

/-- Move a `sep`-free prefix over `splitOnPPrepend`. -/
private lemma splitOnP_go_append_not_mem (sep : Char) (l1 l2 acc : List Char) (h : sep ∉ l1) :
    List.splitOnPPrepend (· == sep) (l1 ++ l2) acc =
    List.splitOnPPrepend (· == sep) l2 (l1.reverse ++ acc) := by
  induction l1 generalizing acc with
  | nil => simp
  | cons x xs ih =>
    have hxq : (x == sep) = false := by
      simp only [beq_eq_false_iff_ne]; intro hx; subst hx; exact h (List.Mem.head _)
    rw [List.cons_append, splitOnP_go_cons_false sep x (xs ++ l2) acc hxq]
    rw [ih (x :: acc) (fun hc => h (List.Mem.tail _ hc))]
    simp [List.reverse_cons, List.append_assoc]

/-- Splitting a list with no separator gives a single part. -/
lemma splitOn_not_mem (sep : Char) (l : List Char) (h : sep ∉ l) : l.splitOn sep = [l] := by
  simp [List.splitOn, List.splitOnP, splitOnP_go_not_mem sep l [] h]

lemma splitOn_append_singleton_append_not_mem (sep : Char) (l1 l2 : List Char)
    (h1 : sep ∉ l1) (h2 : sep ∉ l2) :
    (l1 ++ [sep] ++ l2).splitOn sep = [l1, l2] := by
  simp only [List.splitOn, List.splitOnP, List.append_assoc, List.singleton_append]
  rw [splitOnP_go_append_not_mem sep l1 (sep :: l2) [] h1]
  simp only [List.append_nil]
  rw [splitOnP_go_cons_true sep l2 l1.reverse]
  rw [show List.splitOnPPrepend (· == sep) l2 [] = [l2] by
    simpa using splitOnP_go_not_mem sep l2 [] h2]
  simp

/-! ### Derived `'/'` splitting lemmas used by `parseRatChars_ratToChars`. -/

/-- `splitOn '/'` over a prefix with no `'/'`s. -/
lemma splitOn_not_mem_slash (l : List Char) (h : '/' ∉ l) : l.splitOn '/' = [l] :=
  splitOn_not_mem '/' l h

/-- `splitOn '/'` splits at exactly one `/` surrounded by `/`-free strings. -/
lemma splitOn_append_singleton_append_not_mem_slash (l1 l2 : List Char)
    (h1 : '/' ∉ l1) (h2 : '/' ∉ l2) :
    (l1 ++ ['/'] ++ l2).splitOn '/' = [l1, l2] :=
  splitOn_append_singleton_append_not_mem '/' l1 l2 h1 h2

lemma rat_ext_eq (q : ℚ) : q = (q.num : ℚ) / (q.den : ℚ) := by
  exact (Rat.num_div_den q).symm

lemma parseRatChars_ratToChars (q : ℚ) : parseRatChars (ratToChars q) = some q := by
  unfold ratToChars
  split_ifs with hd
  · unfold parseRatChars
    rw [splitOn_not_mem_slash (intToChars q.num) (not_mem_intToChars q.num)]
    change (parseIntChars (intToChars q.num)).map (fun n => (n : ℚ)) = some q
    have hz_parse := parseIntChars_intToChars q.num
    rw [hz_parse]
    dsimp
    have h_eq_q : some ((q.num : ℚ)) = some q := by
      congr 1
      have h_q := rat_ext_eq q
      rw [h_q, hd]
      simp
    rw [h_eq_q]
  · unfold parseRatChars
    have h1 := not_mem_intToChars q.num
    have h2 := not_mem_natToChars_div q.den
    rw [splitOn_append_singleton_append_not_mem_slash
      (intToChars q.num) (natToChars q.den) h1 h2]
    change (match parseIntChars (intToChars q.num), parseNatChars (natToChars q.den) with
            | some num, some den => if den = 0 then none else some ((num : ℚ) / (den : ℚ))
            | _, _ => none) = some q
    rw [parseIntChars_intToChars q.num, parseNatChars_natToChars q.den]
    dsimp
    have hn0 : q.den ≠ 0 := by
      have hpos := q.den_pos
      omega
    rw [ite_eq_right hn0]
    have h_eq_q : some ((q.num : ℚ) / (q.den : ℚ)) = some q := by
      congr 1
      exact (rat_ext_eq q).symm
    rw [h_eq_q]

end Azurite.AzPolynomial
