import Azurite.DensePoly.ToString
import Azurite.DensePoly.Parse
import Mathlib.Data.String.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

namespace Azurite.DensePoly

/-!
# String Lemmas for `DensePoly`

This file proves key lemmas about the string (character-list) representation of
dense polynomials:

- Properties of the primitive `natToChars`, `intToChars`, `ratToChars`, and
  `zmodToChars` functions (non-empty, no leading zeros or minus signs).
- Round-trip lemmas: `parseXChars (xToChars v) = some v`.
- Generic `splitOn` infrastructure (see `splitOn_append_singleton_append_not_mem`).
- A `DensePolyToCharsValid` typeclass capturing the invariants, and generic
  `monomialToChars_ne_nil` / `monomialToChars_not_start_zero` proofs derived from it.
- High-level `toChars`/`parseChars` round-trip lemmas for each ring type.
-/

/-! ### Char and digit helpers -/

lemma char_ofNat_ne_dash (n : ℕ) : Char.ofNat ('0'.toNat + n % 10) ≠ '-' := by
  have h_mod : n % 10 < 10 := Nat.mod_lt _ (by decide)
  generalize h : n % 10 = k
  rw [h] at h_mod
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals { first | decide | contradiction }

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

lemma natToCharsAux_ne_nil_of_acc_ne_nil (f n : ℕ) (acc : List Char) (h : acc ≠ []) : natToCharsAux f n acc ≠ [] := by
  induction f generalizing n acc with
  | zero => exact h
  | succ f ih =>
    dsimp [natToCharsAux]
    split
    · exact h
    · apply ih
      intro hc
      contradiction

lemma natToCharsAux_ne_nil_of_ne_zero (f n : ℕ) (h : n ≠ 0) : natToCharsAux (f + 1) n [] ≠ [] := by
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

lemma drop_one_append_of_ne_nil {α : Type _} (l1 l2 : List α) (h : l1 ≠ []) :
  (l1 ++ l2).drop 1 = l1.drop 1 ++ l2 := by
  cases l1
  · contradiction
  · rfl

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

class NoDashInTail (R : Type _) [DensePolyToChars R] : Prop where
  no_dash_in_tail : ∀ (r : R), '-' ∉ (DensePolyToChars.toChars r).drop 1

instance : NoDashInTail ℕ where
  no_dash_in_tail := fun n hc => not_mem_natToChars n (List.mem_of_mem_drop hc)

instance : NoDashInTail ℤ where
  no_dash_in_tail := not_mem_tail_intToChars

instance : NoDashInTail ℚ where
  no_dash_in_tail := not_mem_tail_ratToChars

lemma drop_one_append {α : Type _} (l1 l2 : List α) :
  (l1 ++ l2).drop 1 = if l1 = [] then l2.drop 1 else l1.drop 1 ++ l2 := by
  cases l1
  · rfl
  · rfl

lemma not_mem_tail_monomialToChars {R : Type _} [DecidableEq R] [Zero R] [dpc : DensePolyToChars R] [ndit : NoDashInTail R] (d : ℕ) (c : R) :
  '-' ∉ (monomialToChars d c).drop 1 := by
  dsimp [monomialToChars]
  split
  · decide
  · split
    · exact ndit.no_dash_in_tail c
    · let sfx := if d = 1 then ['x'] else ['x', '^'] ++ natToChars d
      have hsfx : '-' ∉ sfx := by
        dsimp [sfx]
        split
        · decide
        · intro hc
          simp only [List.mem_cons] at hc
          rcases hc with h1 | h2 | h3
          · contradiction
          · contradiction
          · exact not_mem_natToChars d h3
      have hsfx_drop : '-' ∉ sfx.drop 1 := by
        intro hc; exact hsfx (List.mem_of_mem_drop hc)

      let s := DensePolyToChars.toChars c
      have hs : '-' ∉ s.drop 1 := ndit.no_dash_in_tail c

      split
      · -- s == ['1']
        exact hsfx_drop
      · split
        · -- s == ['-', '1']
          exact hsfx
        · -- s ++ ['*']
          rw [List.append_assoc]
          rw [drop_one_append]
          split
          · exact hsfx
          · intro hc
            simp only [List.mem_append, List.mem_cons] at hc
            rcases hc with h_s_drop | h_star | h_sfx_mem
            · exact hs h_s_drop
            · contradiction
            · exact hsfx h_sfx_mem

lemma aux_0 (n : ℕ) (h : n < 10^0) : n = 0 := by
  omega

lemma length_natToCharsAux (fuel n : ℕ) (acc : List Char) :
  (natToCharsAux fuel n acc).length = (natToCharsAux fuel n []).length + acc.length := by
  induction fuel generalizing n acc with
  | zero => simp [natToCharsAux]
  | succ f ih =>
    dsimp [natToCharsAux]
    split_ifs with hn
    · simp
    · let digit := Char.ofNat ('0'.toNat + (n % 10))
      have ih1 := ih (n / 10) (digit :: acc)
      have ih2 := ih (n / 10) [digit]
      show (natToCharsAux f (n / 10) (Char.ofNat (48 + n % 10) :: acc)).length = _
      change (natToCharsAux f (n / 10) (digit :: acc)).length = (natToCharsAux f (n / 10) [digit]).length + acc.length
      rw [ih1, ih2]
      simp [add_assoc]
      omega

lemma hf_ineq (f n : ℕ) (h : n < 10^(f+1)) : n / 10 < 10^f := by
  omega

lemma isDigit_digit_mod (m : ℕ) (h : m < 10) : (Char.ofNat (48 + m)).isDigit = true := by
  match m with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide
  | m + 10 => omega

lemma isDigit_digit (n : ℕ) : (Char.ofNat (48 + n % 10)).isDigit = true := by
  apply isDigit_digit_mod
  exact Nat.mod_lt _ (by decide)

lemma toNat_digit_mod (m : ℕ) (h : m < 10) : (Char.ofNat (48 + m)).toNat - 48 = m := by
  match m with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide
  | m + 10 => omega

lemma toNat_digit (n : ℕ) : (Char.ofNat (48 + n % 10)).toNat - 48 = n % 10 := by
  apply toNat_digit_mod
  exact Nat.mod_lt _ (by decide)

lemma parseNatCharsAux_natToCharsAux (fuel n acc : ℕ) (h_fuel : n < 10^fuel) (cs : List Char) :
  parseNatCharsAux (natToCharsAux fuel n cs) acc = parseNatCharsAux cs (acc * 10^(natToCharsAux fuel n []).length + n) := by
  induction fuel generalizing n acc cs with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    dsimp [natToCharsAux]
    simp
  | succ f ih =>
    dsimp [natToCharsAux]
    split_ifs with hn
    · subst hn
      simp
    · let digit := Char.ofNat (48 + (n % 10))
      show parseNatCharsAux (natToCharsAux f (n / 10) (digit :: cs)) acc = _
      have hf : n / 10 < 10^f := by omega
      have ih2 := ih (n / 10) acc hf (digit :: cs)
      rw [ih2]
      show parseNatCharsAux (digit :: cs) _ = _
      dsimp [parseNatCharsAux]
      have h_dig : digit.isDigit = true := isDigit_digit n
      have h_val : digit.toNat - 48 = n % 10 := toNat_digit n
      show (if digit.isDigit then _ else _) = _
      rw [h_dig, if_pos rfl]
      rw [h_val]
      congr 1
      have hl := length_natToCharsAux f (n / 10) [digit]
      show _ * 10 + n % 10 = acc * 10 ^ (natToCharsAux f (n / 10) [digit]).length + n
      rw [hl]
      dsimp
      set L := (natToCharsAux f (n / 10) []).length
      have h_pow : 10 ^ (L + 1) = 10 ^ L * 10 := rfl
      rw [h_pow]
      have h_div_mod : (n / 10) * 10 + n % 10 = n := by omega
      calc (acc * 10 ^ L + n / 10) * 10 + n % 10
        _ = acc * (10 ^ L * 10) + ((n / 10) * 10 + n % 10) := by ring
        _ = acc * (10 ^ L * 10) + n := by rw [h_div_mod]

lemma parseNatChars_eq (cs : List Char) (h : cs ≠ []) : parseNatChars cs = parseNatCharsAux cs 0 := by
  cases cs
  · contradiction
  · rfl

lemma natToCharsAux_ne_nil (n : ℕ) (hn : n ≠ 0) : natToCharsAux n n [] ≠ [] := by
  cases n with
  | zero => contradiction
  | succ n' =>
    dsimp [natToCharsAux]
    let digit := Char.ofNat (48 + (n' + 1) % 10)
    have hl := length_natToCharsAux n' ((n' + 1) / 10) [digit]
    have h_len : [digit].length = 1 := rfl
    intro contra
    rw [contra] at hl
    change 0 = _ at hl
    omega

lemma lt_pow_self (n : ℕ) : n < 10 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : 10 ^ n * 1 ≤ 10 ^ n * 10 := Nat.mul_le_mul_left _ (by decide)
    omega



/-! ### Parse round-trip lemmas -/

lemma parseNatChars_natToChars (n : ℕ) : parseNatChars (natToChars n) = some n := by
  unfold natToChars
  split_ifs with hn
  · subst hn
    rfl
  · have h_neq := natToCharsAux_ne_nil n hn
    rw [parseNatChars_eq _ h_neq]
    have h_fuel := lt_pow_self n
    have h_aux := parseNatCharsAux_natToCharsAux n n 0 h_fuel []
    rw [h_aux]
    simp [parseNatCharsAux]

lemma natToChars_not_dash (n : ℕ) (cs : List Char) : natToChars n = '-' :: cs → False := by
  intro h
  have h_parse := parseNatChars_natToChars n
  rw [h] at h_parse
  have h_none : parseNatChars ('-' :: cs) = none := rfl
  rw [h_none] at h_parse
  contradiction

lemma natToCharsAux_eval_zero (f : ℕ) (acc : List Char) :
  natToCharsAux f 0 acc = acc := by
  cases f <;> rfl

lemma natToCharsAux_not_start_zero (f n : ℕ) (hf : n < 10^f) (hn : n ≠ 0) (acc : List Char) :
  ∀ cs, natToCharsAux f n acc ≠ '0' :: cs := by
  induction f generalizing n acc with
  | zero =>
    have : n = 0 := by omega
    contradiction
  | succ f ih =>
    intro cs h
    dsimp [natToCharsAux] at h
    split_ifs at h with hn_zero
    · contradiction
    · let digit := Char.ofNat (48 + n % 10)
      by_cases h_div : n / 10 = 0
      · have h_eval : natToCharsAux f (n / 10) (digit :: acc) = digit :: acc := by
          rw [h_div]
          exact natToCharsAux_eval_zero f (digit :: acc)
        rw [h_eval] at h
        have h_digit : digit = '0' := by
          injection h
        have h_mod : n % 10 ≠ 0 := by
          intro h_mod_zero
          have h_eq : n = (n / 10) * 10 + n % 10 := by omega
          rw [h_div, h_mod_zero] at h_eq
          omega
        have h_digit_toNat : digit.toNat - 48 = n % 10 := toNat_digit n
        rw [h_digit] at h_digit_toNat
        have h0 : '0'.toNat = 48 := rfl
        rw [h0] at h_digit_toNat
        omega
      · have hf' : n / 10 < 10^f := by omega
        exact ih (n / 10) hf' h_div (digit :: acc) cs h

lemma natToChars_not_start_zero (n : ℕ) (cs : List Char) (hn : n ≠ 0) : natToChars n ≠ '0' :: cs := by
  dsimp [natToChars]
  rw [if_neg hn]
  have h_fuel := lt_pow_self n
  exact natToCharsAux_not_start_zero n n h_fuel hn [] cs

lemma intToChars_natAbs (z : ℤ) : intToChars z = if z < 0 then '-' :: natToChars z.natAbs else natToChars z.natAbs := by
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
      · have h_parse_int : parseIntChars (c :: cs) = (parseNatChars (c :: cs)).map (fun n => (n : ℤ)) := by
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

lemma intToChars_not_start_zero (z : ℤ) (cs : List Char) (hz : z ≠ 0) : intToChars z ≠ '0' :: cs := by
  dsimp [intToChars]
  split
  · split
    · intro h; omega
    · intro h; injection h; contradiction
  · split
    · intro h; omega
    · have h_abs : z.natAbs ≠ 0 := by omega
      have h_fuel := lt_pow_self z.natAbs
      exact natToCharsAux_not_start_zero z.natAbs z.natAbs h_fuel h_abs [] cs

lemma not_mem_natToCharsAux_of_not_digit (c : Char) (hc : c.toNat < 48 ∨ 57 < c.toNat) (fuel n : ℕ) (acc : List Char) (h : c ∉ acc) :
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

lemma not_mem_natToChars_of_not_digit (c : Char) (hc : c.toNat < 48 ∨ 57 < c.toNat) (n : ℕ) : c ∉ natToChars n := by
  unfold natToChars
  split_ifs with hn
  · intro hc_eq; simp at hc_eq
    have ht : '0'.toNat = 48 := rfl
    have hc_toNat : c.toNat = 48 := by
      rw [hc_eq, ht]
    rw [hc_toNat] at hc
    omega
  · exact not_mem_natToCharsAux_of_not_digit c hc _ _ _ (by simp)

lemma not_mem_natToChars_x (n : ℕ) : 'x' ∉ natToChars n := by
  apply not_mem_natToChars_of_not_digit
  have hx : 'x'.toNat = 120 := rfl
  rw [hx]
  exact Or.inr (by decide)

lemma mem_natToChars_only_digits (n : ℕ) (c : Char) (h : c ∈ natToChars n) : '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat := by
  by_contra hc
  rw [not_and_or, not_le, not_le] at hc
  have h_not_mem := not_mem_natToChars_of_not_digit c hc n
  contradiction

lemma mem_monomialToChars_nat_only_valid (d : ℕ) (c : ℕ) (ch : Char) (h : ch ∈ monomialToChars d c) :
  ch = 'x' ∨ ch = '*' ∨ ch = '^' ∨ ('0'.toNat ≤ ch.toNat ∧ ch.toNat ≤ '9'.toNat) := by
  have h_toChars : DensePolyToChars.toChars c = natToChars c := rfl
  dsimp [monomialToChars] at h
  rw [h_toChars] at h
  split_ifs at h with hc hd hc1 hc2 hd1
  · simp only [List.mem_singleton] at h
    subst h
    exact Or.inr (Or.inr (Or.inr (by decide)))
  · exact Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h)))
  · simp only [List.nil_append, List.mem_singleton] at h
    subst h
    exact Or.inl rfl
  · simp only [List.nil_append] at h
    rcases (List.mem_cons.mp h) with rfl | hk
    · exact Or.inl rfl
    · rcases (List.mem_cons.mp hk) with rfl | hh
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ hh)))
  · have h_eq := eq_of_beq hd1
    have h_dash_not_in : '-' ∉ natToChars c := by
      intro h_in
      have h_dig := mem_natToChars_only_digits c '-' h_in
      have ht : '-'.toNat = 45 := rfl
      have hz : '0'.toNat = 48 := rfl
      rw [ht, hz] at h_dig
      omega
    rw [h_eq] at h_dash_not_in
    have h_mem : '-' ∈ ['-', '1'] := by decide
    contradiction
  · have h_eq := eq_of_beq hd1
    have h_dash_not_in : '-' ∉ natToChars c := by
      intro h_in
      have h_dig := mem_natToChars_only_digits c '-' h_in
      have ht : '-'.toNat = 45 := rfl
      have hz : '0'.toNat = 48 := rfl
      rw [ht, hz] at h_dig
      omega
    rw [h_eq] at h_dash_not_in
    have h_mem : '-' ∈ ['-', '1'] := by decide
    contradiction
  · have h_assoc : natToChars c ++ ['*'] ++ ['x'] = natToChars c ++ ['*', 'x'] := by simp
    rw [h_assoc] at h
    rcases (List.mem_append.mp h) with h_nat | h_rest
    · exact Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h_nat)))
    · rcases (List.mem_cons.mp h_rest) with rfl | h_rest2
      · exact Or.inr (Or.inl rfl)
      · have h_eq_x : ch = 'x' := List.mem_singleton.mp h_rest2
        exact Or.inl h_eq_x
  · have h_assoc : natToChars c ++ ['*'] ++ 'x' :: '^' :: natToChars d = natToChars c ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc] at h
    rcases (List.mem_append.mp h) with h_nat | h_rest
    · exact Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h_nat)))
    · rcases (List.mem_cons.mp h_rest) with rfl | h_rest2
      · exact Or.inr (Or.inl rfl)
      · rcases (List.mem_cons.mp h_rest2) with rfl | h_rest3
        · exact Or.inl rfl
        · rcases (List.mem_cons.mp h_rest3) with rfl | h_rest4
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h_rest4)))


lemma not_mem_intToChars_x (z : ℤ) : 'x' ∉ intToChars z := by
  rw [intToChars_natAbs]
  split_ifs with hz
  · intro hc
    simp only [List.mem_cons] at hc
    cases hc with
    | inl hl =>
       have h_val := congrArg Char.toNat hl
       have h_x : 'x'.toNat = 120 := rfl
       have h_sub : '-'.toNat = 45 := rfl
       rw [h_x, h_sub] at h_val
       contradiction
    | inr hr => exact not_mem_natToChars_x _ hr
  · exact not_mem_natToChars_x _

lemma mem_intToChars_only_digits_or_dash (z : ℤ) (c : Char) (h : c ∈ intToChars z) :
  c = '-' ∨ ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat) := by
  rw [intToChars_natAbs] at h
  split_ifs at h with hz
  · rcases (List.mem_cons.mp h) with rfl | h_nat
    · exact Or.inl rfl
    · exact Or.inr (mem_natToChars_only_digits _ _ h_nat)
  · exact Or.inr (mem_natToChars_only_digits _ _ h)

lemma mem_monomialToChars_int_only_valid (d : ℕ) (c : ℤ) (ch : Char) (h : ch ∈ monomialToChars d c) :
  ch = 'x' ∨ ch = '*' ∨ ch = '^' ∨ ch = '-' ∨ ('0'.toNat ≤ ch.toNat ∧ ch.toNat ≤ '9'.toNat) := by
  have h_toChars : DensePolyToChars.toChars c = intToChars c := rfl
  dsimp [monomialToChars] at h
  rw [h_toChars] at h
  split_ifs at h with hc hd hc1 hd1 hd1_ignore
  · simp only [List.mem_singleton] at h
    subst h
    exact Or.inr (Or.inr (Or.inr ( Or.inr (by decide) )))
  · rcases mem_intToChars_only_digits_or_dash _ _ h with rfl | h_dig
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h_dig)))
  · simp only [List.nil_append, List.mem_singleton] at h
    subst h
    exact Or.inl rfl
  · simp only [List.nil_append] at h
    rcases (List.mem_cons.mp h) with rfl | hk
    · exact Or.inl rfl
    · rcases (List.mem_cons.mp hk) with rfl | hh
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ hh))))
  · have h_assoc : ['-'] ++ ['x'] = ['-', 'x'] := rfl
    rw [h_assoc] at h
    rcases (List.mem_cons.mp h) with rfl | hk
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · have h_eq_x : ch = 'x' := List.mem_singleton.mp hk
      exact Or.inl h_eq_x
  · have h_assoc : ['-'] ++ 'x' :: '^' :: natToChars d = '-' :: 'x' :: '^' :: natToChars d := rfl
    rw [h_assoc] at h
    rcases (List.mem_cons.mp h) with rfl | hk
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rcases (List.mem_cons.mp hk) with rfl | hh
      · exact Or.inl rfl
      · rcases (List.mem_cons.mp hh) with rfl | h3
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h3))))
  · have h_assoc : intToChars c ++ ['*'] ++ ['x'] = intToChars c ++ ['*', 'x'] := by simp
    rw [h_assoc] at h
    rcases (List.mem_append.mp h) with h_int | h_rest
    · rcases mem_intToChars_only_digits_or_dash _ _ h_int with rfl | h_dig
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h_dig)))
    · rcases (List.mem_cons.mp h_rest) with rfl | h_rest2
      · exact Or.inr (Or.inl rfl)
      · have h_eq_x : ch = 'x' := List.mem_singleton.mp h_rest2
        exact Or.inl h_eq_x
  · have h_assoc : intToChars c ++ ['*'] ++ 'x' :: '^' :: natToChars d = intToChars c ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc] at h
    rcases (List.mem_append.mp h) with h_int | h_rest
    · rcases mem_intToChars_only_digits_or_dash _ _ h_int with rfl | h_dig
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h_dig)))
    · rcases (List.mem_cons.mp h_rest) with rfl | h_rest2
      · exact Or.inr (Or.inl rfl)
      · rcases (List.mem_cons.mp h_rest2) with rfl | h_rest3
        · exact Or.inl rfl
        · rcases (List.mem_cons.mp h_rest3) with rfl | h_rest4
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h_rest4))))

lemma mem_ratToChars_only_digits_or_dash_or_slash (q : ℚ) (c : Char) (h : c ∈ ratToChars q) :
  c = '/' ∨ c = '-' ∨ ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat) := by
  dsimp [ratToChars] at h
  split_ifs at h with hd
  · rcases (mem_intToChars_only_digits_or_dash _ _ h) with rfl | h_dig
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr h_dig)
  · have h_assoc : intToChars q.num ++ ['/'] ++ natToChars q.den = (intToChars q.num ++ ['/']) ++ natToChars q.den := rfl
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

lemma mem_monomialToChars_rat_only_valid (d : ℕ) (c : ℚ) (ch : Char) (h : ch ∈ monomialToChars d c) :
  ch = 'x' ∨ ch = '*' ∨ ch = '^' ∨ ch = '/' ∨ ch = '-' ∨ ('0'.toNat ≤ ch.toNat ∧ ch.toNat ≤ '9'.toNat) := by
  have h_toChars : DensePolyToChars.toChars c = ratToChars c := rfl
  dsimp [monomialToChars] at h
  rw [h_toChars] at h
  split_ifs at h with hc hd hc1 hd1 hd1_ignore
  · simp only [List.mem_singleton] at h
    subst h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))
  · rcases mem_ratToChars_only_digits_or_dash_or_slash _ _ h with rfl | rfl | h_dig
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_dig))))
  · simp only [List.nil_append, List.mem_singleton] at h
    subst h
    exact Or.inl rfl
  · simp only [List.nil_append] at h
    rcases (List.mem_cons.mp h) with rfl | hk
    · exact Or.inl rfl
    · rcases (List.mem_cons.mp hk) with rfl | hh
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ hh)))))
  · have h_assoc : ['-'] ++ ['x'] = ['-', 'x'] := rfl
    rw [h_assoc] at h
    rcases (List.mem_cons.mp h) with rfl | hk
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · have h_eq_x : ch = 'x' := List.mem_singleton.mp hk
      exact Or.inl h_eq_x
  · have h_assoc : ['-'] ++ 'x' :: '^' :: natToChars d = '-' :: 'x' :: '^' :: natToChars d := rfl
    rw [h_assoc] at h
    rcases (List.mem_cons.mp h) with rfl | hk
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · rcases (List.mem_cons.mp hk) with rfl | hh
      · exact Or.inl rfl
      · rcases (List.mem_cons.mp hh) with rfl | h3
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h3)))))
  · have h_assoc : ratToChars c ++ ['*'] ++ ['x'] = ratToChars c ++ ['*', 'x'] := by simp
    rw [h_assoc] at h
    rcases (List.mem_append.mp h) with h_rat | h_rest
    · rcases mem_ratToChars_only_digits_or_dash_or_slash _ _ h_rat with rfl | rfl | h_dig
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_dig))))
    · rcases (List.mem_cons.mp h_rest) with rfl | h_rest2
      · exact Or.inr (Or.inl rfl)
      · have h_eq_x : ch = 'x' := List.mem_singleton.mp h_rest2
        exact Or.inl h_eq_x
  · have h_assoc : ratToChars c ++ ['*'] ++ 'x' :: '^' :: natToChars d = ratToChars c ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc] at h
    rcases (List.mem_append.mp h) with h_rat | h_rest
    · rcases mem_ratToChars_only_digits_or_dash_or_slash _ _ h_rat with rfl | rfl | h_dig
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_dig))))
    · rcases (List.mem_cons.mp h_rest) with rfl | h_rest2
      · exact Or.inr (Or.inl rfl)
      · rcases (List.mem_cons.mp h_rest2) with rfl | h_rest3
        · exact Or.inl rfl
        · rcases (List.mem_cons.mp h_rest3) with rfl | h_rest4
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h_rest4)))))

lemma mem_monomialToChars_zmod_only_valid {n : ℕ} [NeZero n] (d : ℕ) (c : ZMod n) (ch : Char) (h : ch ∈ monomialToChars d c) :
  ch = 'x' ∨ ch = '*' ∨ ch = '^' ∨ ('0'.toNat ≤ ch.toNat ∧ ch.toNat ≤ '9'.toNat) := by
  have h_toChars : DensePolyToChars.toChars c = natToChars c.val := rfl
  dsimp [monomialToChars] at h
  rw [h_toChars] at h
  split_ifs at h with hc hd hc1 hd1 hd1_ignore
  · simp only [List.mem_singleton] at h
    subst h
    exact Or.inr (Or.inr (Or.inr (by decide)))
  · exact Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h)))
  · simp only [List.nil_append, List.mem_singleton] at h
    subst h
    exact Or.inl rfl
  · simp only [List.nil_append] at h
    rcases (List.mem_cons.mp h) with rfl | hk
    · exact Or.inl rfl
    · rcases (List.mem_cons.mp hk) with rfl | hh
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ hh)))
  · have h_eq := eq_of_beq hd1_ignore
    have h_dash_not_in : '-' ∉ natToChars c.val := by
      intro h_in
      have h_dig := mem_natToChars_only_digits c.val '-' h_in
      have ht : '-'.toNat = 45 := rfl
      have hz : '0'.toNat = 48 := rfl
      rw [ht, hz] at h_dig
      omega
    rw [h_eq] at h_dash_not_in
    have h_mem : '-' ∈ ['-', '1'] := by decide
    contradiction
  · have h_eq := eq_of_beq hd1_ignore
    have h_dash_not_in : '-' ∉ natToChars c.val := by
      intro h_in
      have h_dig := mem_natToChars_only_digits c.val '-' h_in
      have ht : '-'.toNat = 45 := rfl
      have hz : '0'.toNat = 48 := rfl
      rw [ht, hz] at h_dig
      omega
    rw [h_eq] at h_dash_not_in
    have h_mem : '-' ∈ ['-', '1'] := by decide
    contradiction
  · have h_assoc : natToChars c.val ++ ['*'] ++ ['x'] = natToChars c.val ++ ['*', 'x'] := by simp
    rw [h_assoc] at h
    rcases (List.mem_append.mp h) with h_nat | h_rest
    · exact Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h_nat)))
    · rcases (List.mem_cons.mp h_rest) with rfl | h_rest2
      · exact Or.inr (Or.inl rfl)
      · have h_eq_x : ch = 'x' := List.mem_singleton.mp h_rest2
        exact Or.inl h_eq_x
  · have h_assoc : natToChars c.val ++ ['*'] ++ 'x' :: '^' :: natToChars d = natToChars c.val ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc] at h
    rcases (List.mem_append.mp h) with h_nat | h_rest
    · exact Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h_nat)))
    · rcases (List.mem_cons.mp h_rest) with rfl | h_rest2
      · exact Or.inr (Or.inl rfl)
      · rcases (List.mem_cons.mp h_rest2) with rfl | h_rest3
        · exact Or.inl rfl
        · rcases (List.mem_cons.mp h_rest3) with rfl | h_rest4
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (mem_natToChars_only_digits _ _ h_rest4)))

lemma not_mem_ratToChars_x (q : ℚ) : 'x' ∉ ratToChars q := by
  unfold ratToChars
  split_ifs
  · exact not_mem_intToChars_x q.num
  · intro hc
    have hc1 : 'x' ∈ intToChars q.num ++ ['/'] ∨ 'x' ∈ natToChars q.den := List.mem_append.mp hc
    cases hc1 with
    | inl h1 =>
      have hc2 : 'x' ∈ intToChars q.num ∨ 'x' ∈ ['/'] := List.mem_append.mp h1
      cases hc2 with
      | inl h_int => exact not_mem_intToChars_x q.num h_int
      | inr h_div =>
        have h_eq : 'x' = '/' := by
          simp only [List.mem_singleton] at h_div
          exact h_div
        have h_x : 'x'.toNat = 120 := rfl
        have h_div_char : '/'.toNat = 47 := rfl
        have h_eq2 : 'x'.toNat = '/'.toNat := congrArg Char.toNat h_eq
        rw [h_x, h_div_char] at h_eq2
        contradiction
    | inr h_nat => exact not_mem_natToChars_x q.den h_nat

lemma not_mem_natToChars_mul (n : ℕ) : '*' ∉ natToChars n := by
  apply not_mem_natToChars_of_not_digit
  have hmul : '*'.toNat = 42 := rfl
  rw [hmul]
  exact Or.inl (by decide)

lemma not_mem_intToChars_mul (z : ℤ) : '*' ∉ intToChars z := by
  rw [intToChars_natAbs]
  split_ifs with hz
  · intro hc
    simp only [List.mem_cons] at hc
    cases hc with
    | inl hl =>
       have h_val := congrArg Char.toNat hl
       have h_mul : '*'.toNat = 42 := rfl
       have h_sub : '-'.toNat = 45 := rfl
       rw [h_mul, h_sub] at h_val
       contradiction
    | inr hr => exact not_mem_natToChars_mul _ hr
  · exact not_mem_natToChars_mul _

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

These lemmas handle splitting on any character separator.
The `'/'` and `'x'` splitting uses these uniformly.
-/

/-- Step past a non-separator character in `splitOnP.go`. -/
private lemma splitOnP_go_cons_false (sep x : Char) (xs acc : List Char)
    (h : (x == sep) = false) :
    List.splitOnP.go (· == sep) (x :: xs) acc =
    List.splitOnP.go (· == sep) xs (x :: acc) := by
  simp [List.splitOnP.go, h]

/-- Step past the separator character, resetting the accumulator. -/
private lemma splitOnP_go_cons_true (sep : Char) (xs acc : List Char) :
    List.splitOnP.go (· == sep) (sep :: xs) acc =
    acc.reverse :: List.splitOnP.go (· == sep) xs [] := by
  simp [List.splitOnP.go]

/-- If `sep ∉ l`, the go passes through, producing `[acc.reverse ++ l]`. -/
private lemma splitOnP_go_not_mem (sep : Char) (l acc : List Char) (h : sep ∉ l) :
    List.splitOnP.go (· == sep) l acc = [acc.reverse ++ l] := by
  induction l generalizing acc with
  | nil => simp [List.splitOnP.go]
  | cons x xs ih =>
    have hxq : (x == sep) = false := by
      simp only [beq_eq_false_iff_ne]; intro hx; subst hx; exact h (List.Mem.head _)
    simp only [splitOnP_go_cons_false sep x xs acc hxq]
    rw [ih (x :: acc) (fun hc => h (List.Mem.tail _ hc))]
    simp [List.reverse_cons, List.append_assoc]

/-- Move a `sep`-free prefix over `splitOnP.go`. -/
private lemma splitOnP_go_append_not_mem (sep : Char) (l1 l2 acc : List Char) (h : sep ∉ l1) :
    List.splitOnP.go (· == sep) (l1 ++ l2) acc =
    List.splitOnP.go (· == sep) l2 (l1.reverse ++ acc) := by
  induction l1 generalizing acc with
  | nil => simp
  | cons x xs ih =>
    have hxq : (x == sep) = false := by
      simp only [beq_eq_false_iff_ne]; intro hx; subst hx; exact h (List.Mem.head _)
    rw [List.cons_append, splitOnP_go_cons_false sep x (xs ++ l2) acc hxq]
    rw [ih (x :: acc) (fun hc => h (List.Mem.tail _ hc))]
    simp [List.reverse_cons, List.append_assoc]

/-- Splitting a list with exactly one separator gives two parts. -/
lemma splitOn_not_mem (sep : Char) (l : List Char) (h : sep ∉ l) : l.splitOn sep = [l] := by
  simp [List.splitOn, List.splitOnP, splitOnP_go_not_mem sep l [] h]

lemma splitOn_append_singleton_append_not_mem (sep : Char) (l1 l2 : List Char)
    (h1 : sep ∉ l1) (h2 : sep ∉ l2) :
    (l1 ++ [sep] ++ l2).splitOn sep = [l1, l2] := by
  simp only [List.splitOn, List.splitOnP, List.append_assoc, List.singleton_append]
  rw [splitOnP_go_append_not_mem sep l1 (sep :: l2) [] h1]
  simp only [List.append_nil]
  rw [splitOnP_go_cons_true sep l2 l1.reverse]
  rw [show List.splitOnP.go (· == sep) l2 [] = [l2] by
    simpa using splitOnP_go_not_mem sep l2 [] h2]
  simp

/-! ### Derived `'/'` and `'x'` splitting lemmas -/

/-- `splitOn '/'` over a prefix with no `'/'`s. -/
lemma splitOn_not_mem_slash (l : List Char) (h : '/' ∉ l) : l.splitOn '/' = [l] :=
  splitOn_not_mem '/' l h

/-- `splitOn 'x'` over a prefix with no `'x'`es. -/
lemma splitOn_not_mem_x (l : List Char) (h : 'x' ∉ l) : l.splitOn 'x' = [l] :=
  splitOn_not_mem 'x' l h

/-- `splitOn '/'` splits at exactly one `/` surrounded by `/`-free strings. -/
lemma splitOn_append_singleton_append_not_mem_slash (l1 l2 : List Char)
    (h1 : '/' ∉ l1) (h2 : '/' ∉ l2) :
    (l1 ++ ['/'] ++ l2).splitOn '/' = [l1, l2] :=
  splitOn_append_singleton_append_not_mem '/' l1 l2 h1 h2

/-- `splitOn 'x'` splits at exactly one `x` surrounded by `x`-free strings. -/
lemma splitOn_append_singleton_append_not_mem_x (l1 l2 : List Char)
    (h1 : 'x' ∉ l1) (h2 : 'x' ∉ l2) :
    (l1 ++ ['x'] ++ l2).splitOn 'x' = [l1, l2] :=
  splitOn_append_singleton_append_not_mem 'x' l1 l2 h1 h2

/-- `(l ++ ['*', 'x']).splitOn 'x' = [l ++ ['*'], []]` when `'x' ∉ l`. -/
lemma splitOn_append_mul_x (l : List Char) (h : 'x' ∉ l) :
    (l ++ ['*', 'x']).splitOn 'x' = [l ++ ['*'], []] := by
  have : l ++ ['*', 'x'] = (l ++ ['*']) ++ ['x'] ++ [] := by simp
  rw [this]
  apply splitOn_append_singleton_append_not_mem_x
  · intro h_in
    simp only [List.mem_append, List.mem_singleton] at h_in
    rcases h_in with h_l | h_mul
    · exact h h_l
    · exact (by decide : 'x' ≠ '*') h_mul
  · simp

/-- `(l ++ '*' :: 'x' :: '^' :: d).splitOn 'x' = [l ++ ['*'], '^' :: d]`
    when `'x' ∉ l` and `'x' ∉ d`. -/
lemma splitOn_append_mul_x_pow (l d : List Char) (h : 'x' ∉ l) (hd : 'x' ∉ d) :
    (l ++ '*' :: 'x' :: '^' :: d).splitOn 'x' = [l ++ ['*'], '^' :: d] := by
  have : l ++ '*' :: 'x' :: '^' :: d = (l ++ ['*']) ++ ['x'] ++ ('^' :: d) := by simp
  rw [this]
  apply splitOn_append_singleton_append_not_mem_x
  · intro h_in
    simp only [List.mem_append, List.mem_singleton] at h_in
    rcases h_in with h_l | h_mul
    · exact h h_l
    · exact (by decide : 'x' ≠ '*') h_mul
  · intro h_in
    simp only [List.mem_cons] at h_in
    rcases h_in with h_pow | h_d
    · exact (by decide : 'x' ≠ '^') h_pow
    · exact hd h_d


/-! ### Accumulator generalization for `'x'`-splitting

These helpers allow rewriting `splitOnP.go · == 'x'` with a non-empty accumulator
in terms of the zero-accumulator variant.
-/

private lemma splitOnP_go_accum_gen (cs acc : List Char) :
    List.splitOnP.go (· == 'x') cs acc =
    match List.splitOnP.go (· == 'x') cs [] with
    | [] => []
    | hd :: tail => (acc.reverse ++ hd) :: tail := by
  revert acc
  induction cs with
  | nil => intro acc; simp [List.splitOnP.go]
  | cons x xs ih =>
    intro acc
    simp only [List.splitOnP.go]
    split
    · simp
    · rename_i h_neq
      rw [ih (x :: acc), ih [x]]
      generalize List.splitOnP.go (· == 'x') xs [] = res
      cases res with
      | nil => rfl
      | cons hd tail => simp [List.append_assoc]

private lemma splitOnP_go_accum (c : Char) (cs hd : List Char) (tail : List (List Char))
    (h : List.splitOnP.go (· == 'x') cs [] = hd :: tail) :
    List.splitOnP.go (· == 'x') cs [c] = (c :: hd) :: tail := by
  have h_gen := splitOnP_go_accum_gen cs [c]
  rw [h] at h_gen
  exact h_gen


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
    rw [splitOn_append_singleton_append_not_mem_slash (intToChars q.num) (natToChars q.den) h1 h2]
    change (match parseIntChars (intToChars q.num), parseNatChars (natToChars q.den) with
            | some num, some den => if den = 0 then none else some ((num : ℚ) / (den : ℚ))
            | _, _ => none) = some q
    rw [parseIntChars_intToChars q.num, parseNatChars_natToChars q.den]
    dsimp
    have hn0 : q.den ≠ 0 := by
      have hpos := q.den_pos
      omega
    rw [if_neg hn0]
    have h_eq_q : some ((q.num : ℚ) / (q.den : ℚ)) = some q := by
      congr 1
      exact (rat_ext_eq q).symm
    rw [h_eq_q]

lemma ratToChars_not_start_zero (q : ℚ) (cs : List Char) (hq : q ≠ 0) : ratToChars q ≠ '0' :: cs := by
  dsimp [ratToChars]
  have h_num : q.num ≠ 0 := by
    intro h_0
    have hq_eq : q = (q.num : ℚ) / (q.den : ℚ) := rat_ext_eq q
    rw [h_0] at hq_eq
    simp at hq_eq
    exact hq hq_eq
  split
  · exact intToChars_not_start_zero q.num cs h_num
  · intro h
    have h_int := intToChars_not_start_zero q.num
    cases h_chars : intToChars q.num
    · have h_ne_nil := intToChars_ne_nil q.num
      contradiction
    · rename_i c rest
      have h_append : intToChars q.num ++ ['/'] ++ natToChars q.den = (c :: rest) ++ ['/'] ++ natToChars q.den := by rw [h_chars]
      rw [h_append] at h
      have h_c : c = '0' := by injection h
      subst h_c
      exact h_int rest h_num h_chars

lemma append_star_dropLast (l : List Char) : (l ++ ['*']).dropLast = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp [List.dropLast, ih]

lemma append_star_getLast? (l : List Char) : (l ++ ['*']).getLast? = some '*' := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp [List.getLast?]

/-- Helper for parseMonomial to extract the coefficient string prefix -/

@[simp] lemma parse_monomialToChars_zero {R : Type _} [DensePolyParsable R] [DecidableEq R] [Zero R] [DensePolyToChars R] (d : ℕ)
  (hparse : DensePolyParsable.parse ['0'] = some (0 : R)) :
  parseMonomial (R := R) (monomialToChars d (0 : R)) = some (0, 0) := by
  dsimp [monomialToChars]
  have h0 : (0 : R) = 0 := rfl
  rw [if_pos h0]
  dsimp [parseMonomial]
  have h_split : ['0'].splitOn 'x' = [['0']] := rfl
  rw [h_split]
  dsimp
  rw [hparse]
  rfl

lemma splitOn_x_pow (d : List Char) (h : 'x' ∉ d) :
  ('x' :: '^' :: d).splitOn 'x' = [[], '^' :: d] := by
  have h_eq : 'x' :: '^' :: d = [] ++ ['x'] ++ ('^' :: d) := rfl
  rw [h_eq]
  apply splitOn_append_singleton_append_not_mem_x
  · intro h_nil
    contradiction
  · intro h2
    simp only [List.mem_cons] at h2
    cases h2 with
    | inl h_pow =>
      have hx : 'x'.toNat = 120 := rfl
      have hm : '^'.toNat = 94 := rfl
      have h_eq : 'x'.toNat = '^'.toNat := congrArg Char.toNat h_pow
      rw [hx, hm] at h_eq
      contradiction
    | inr hd => exact h hd

lemma splitOn_neg_x_pow (d : List Char) (h : 'x' ∉ d) :
  ('-' :: 'x' :: '^' :: d).splitOn 'x' = [['-'], '^' :: d] := by
  have h_eq : '-' :: 'x' :: '^' :: d = ['-'] ++ ['x'] ++ ('^' :: d) := rfl
  rw [h_eq]
  apply splitOn_append_singleton_append_not_mem_x
  · intro h_mem
    cases h_mem; contradiction
  · intro h2
    simp only [List.mem_cons] at h2
    cases h2 with
    | inl h_pow =>
      have hx : 'x'.toNat = 120 := rfl
      have hm : '^'.toNat = 94 := rfl
      have h_eq : 'x'.toNat = '^'.toNat := congrArg Char.toNat h_pow
      rw [hx, hm] at h_eq
      contradiction
    | inr hd => exact h hd

@[simp] lemma parse_monomialToChars_ne_zero_nat (d : ℕ) (c : ℕ) (hc : c ≠ 0) :
  parseMonomial (R := ℕ) (monomialToChars d c) = some (d, c) := by
  dsimp [monomialToChars]
  rw [if_neg hc]
  have h_toChars : DensePolyToChars.toChars c = natToChars c := rfl
  have hc_chars : natToChars c ≠ ['0'] := by
    intro contra
    have hparse := parseNatChars_natToChars c
    rw [contra] at hparse
    have h0 : parseNatChars ['0'] = some 0 := rfl
    rw [h0] at hparse
    injection hparse with heq
    have eq0 : c = 0 := heq.symm
    contradiction
  have hx_not_mem : 'x' ∉ natToChars c := not_mem_natToChars_x c
  by_cases hd : d = 0
  · -- d = 0
    rw [if_pos hd]
    dsimp [parseMonomial]
    rw [h_toChars]
    have h_split : (natToChars c).splitOn 'x' = [natToChars c] := splitOn_not_mem_x _ hx_not_mem
    rw [h_split]
    dsimp [DensePolyParsable.parse]
    rw [parseNatChars_natToChars c]
    subst hd
    rfl
  · -- d ≠ 0
    rw [if_neg hd]
    by_cases hc1 : natToChars c = ['1']
    · by_cases hd1 : d = 1
      · -- 1x
        have hc1_decide : (DensePolyToChars.toChars c == ['1']) = true := by
          rw [h_toChars, hc1]
          rfl
        simp [hc1_decide, hd1]
        dsimp [parseMonomial]
        have h_split : List.splitOn 'x' ['x'] = [[], []] := rfl
        rw [h_split]
        simp [DensePolyParsable.parse]
        unfold parseMonomial_c_opt_prefix
        rw [← hc1]
        rw [parseNatChars_natToChars c]
        rfl
      · -- 1x^d
        have hc1_decide : (DensePolyToChars.toChars c == ['1']) = true := by
          rw [h_toChars, hc1]
          rfl
        simp_rw [hc1_decide]
        simp [hd1]
        dsimp [parseMonomial]
        have h_split : List.splitOn 'x' ('x' :: '^' :: natToChars d) = [[], '^' :: natToChars d] := splitOn_x_pow _ (not_mem_natToChars_x d)
        rw [h_split]
        simp [DensePolyParsable.parse]
        have h_d := parseNatChars_natToChars d
        unfold parseMonomial_c_opt_prefix
        simp_rw [h_d, ← hc1, parseNatChars_natToChars c]
        rfl
    · by_cases hd1 : d = 1
      · -- cx
        have hc1_decide : (DensePolyToChars.toChars c == ['1']) = false := by
          cases h : (DensePolyToChars.toChars c == ['1'])
          · rfl
          · exfalso
            have h_eq : DensePolyToChars.toChars c = ['1'] := eq_of_beq h
            rw [h_toChars] at h_eq
            exact hc1 h_eq
        have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = false := by
          cases h : (DensePolyToChars.toChars c == ['-', '1'])
          · rfl
          · exfalso
            have h_eq : DensePolyToChars.toChars c = ['-', '1'] := eq_of_beq h
            rw [h_toChars] at h_eq
            exact natToChars_not_dash c ['1'] h_eq
        simp [hc1_decide, hc2_decide, hd1]
        dsimp [parseMonomial]
        rw [h_toChars]
        have h_split : (natToChars c ++ ['*', 'x']).splitOn 'x' = [natToChars c ++ ['*'], []] := splitOn_append_mul_x _ hx_not_mem
        rw [h_split]
        dsimp [DensePolyParsable.parse]
        unfold parseMonomial_c_opt_prefix
        split
        · next h =>
          have h_len : (natToChars c ++ ['*']).length = 0 := by rw [h]; rfl
          simp at h_len
        · next h =>
          have h_last : (natToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
          have hm : (['-'] : List Char).getLast? = some '-' := rfl
          rw [h, hm] at h_last
          injection h_last with heq
          contradiction
        · have h_get : (natToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
          have h_drop : (natToChars c ++ ['*']).dropLast = natToChars c := append_star_dropLast _
          simp_rw [if_pos h_get, h_drop]
          simp_rw [parseNatChars_natToChars c]
          rfl
      · -- cx^d
        have hc1_decide : (DensePolyToChars.toChars c == ['1']) = false := by
          cases h : (DensePolyToChars.toChars c == ['1'])
          · rfl
          · exfalso
            have h_eq : DensePolyToChars.toChars c = ['1'] := eq_of_beq h
            rw [h_toChars] at h_eq
            exact hc1 h_eq
        have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = false := by
          cases h : (DensePolyToChars.toChars c == ['-', '1'])
          · rfl
          · exfalso
            have h_eq : DensePolyToChars.toChars c = ['-', '1'] := eq_of_beq h
            rw [h_toChars] at h_eq
            exact natToChars_not_dash c ['1'] h_eq
        simp [hc1_decide, hc2_decide, hd1]
        dsimp [parseMonomial]
        rw [h_toChars]
        have h_split : (natToChars c ++ '*' :: 'x' :: '^' :: natToChars d).splitOn 'x' = [natToChars c ++ ['*'], '^' :: natToChars d] := splitOn_append_mul_x_pow _ _ hx_not_mem (not_mem_natToChars_x d)
        rw [h_split]
        simp [DensePolyParsable.parse]
        have h_d := parseNatChars_natToChars d
        simp_rw [h_d]
        unfold parseMonomial_c_opt_prefix
        split
        · next h =>
          have h_len : (natToChars c ++ ['*']).length = 0 := by rw [h]; rfl
          simp at h_len
        · next h =>
          have h_last : (natToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
          have hm : (['-'] : List Char).getLast? = some '-' := rfl
          rw [h, hm] at h_last
          injection h_last with heq
          contradiction
        · have h_get : (natToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
          have h_drop : (natToChars c ++ ['*']).dropLast = natToChars c := append_star_dropLast _
          simp_rw [if_pos h_get, h_drop]
          simp_rw [parseNatChars_natToChars c]
          rfl

lemma parseIntChars_eq_some_of_parseNatChars (cs : List Char) (n : ℕ) (h : parseNatChars cs = some n) :
  parseIntChars cs = some (n : ℤ) := by
  unfold parseIntChars
  cases cs with
  | nil => contradiction
  | cons c cs =>
    by_cases hc : c = '-'
    · subst hc
      have hnone : parseNatChars ('-' :: cs) = none := rfl
      rw [hnone] at h
      contradiction
    · have hc_not_dash : c ≠ '-' := hc
      have h_int_chars : (match c :: cs with | [] => none | '-' :: cs => (parseNatChars cs).bind fun a => some (-↑a) | _ => (parseNatChars (c :: cs)).bind fun a => some ↑a) = (parseNatChars (c :: cs)).bind fun a => some (a : ℤ) := by
        split
        · contradiction
        · rename_i hc_eq; injection hc_eq with h_c_dash; contradiction
        · rfl
      cases heq : parseNatChars (c :: cs)
      · rw [heq] at h
        contradiction
      · rename_i val
        have h_bind : (Option.bind (some val) fun a => some (a : ℤ)) = some (val : ℤ) := rfl
        rw [heq] at h
        injection h with h_eq_n
        subst h_eq_n
        dsimp [parseIntChars]
        split
        · contradiction
        · rename_i hc_eq; injection hc_eq with h_c_dash; contradiction
        · rfl

lemma parseIntChars_eq_neg_of_parseNatChars (cs : List Char) (n : ℕ) (h : parseNatChars cs = some n) :
  parseIntChars ('-' :: cs) = some (- (n : ℤ)) := by
  unfold parseIntChars
  cases heq : parseNatChars cs
  · rw [heq] at h
    contradiction
  · rename_i val
    have h_bind : (Option.bind (some val) fun a => some (- (a : ℤ))) = some (- (val : ℤ)) := rfl
    rw [heq] at h
    injection h with h_eq_n
    subst h_eq_n
    dsimp [parseIntChars]
    split
    · contradiction
    · rename_i _ cs2 hc_eq
      injection hc_eq with hc_dash hc_string
      subst hc_string
      rw [heq]
      rfl
    · rename_i hc1 hc2;
      have h_dash : '-' :: cs = '-' :: cs := rfl
      exact False.elim (hc2 cs h_dash)

lemma parseMonomial_c_opt_int_pos (hd : List Char) (n : ℕ)
  (h : DensePolyParsable.parse (R := ℕ) (parseMonomial_c_opt_prefix hd) = some n) :
  DensePolyParsable.parse (R := ℤ) (parseMonomial_c_opt_prefix hd) = some (n : ℤ) := by
  dsimp [DensePolyParsable.parse] at h ⊢
  exact parseIntChars_eq_some_of_parseNatChars _ n h

lemma parseMonomial_c_opt_int_neg (hd : List Char) (n : ℕ)
  (h : DensePolyParsable.parse (R := ℕ) (parseMonomial_c_opt_prefix hd) = some n) :
  DensePolyParsable.parse (R := ℤ) (parseMonomial_c_opt_prefix ('-' :: hd)) = some (- (n : ℤ)) := by
  dsimp [DensePolyParsable.parse] at h ⊢
  cases hd with
  | nil =>
    dsimp [parseMonomial_c_opt_prefix] at h ⊢
    exact parseIntChars_eq_neg_of_parseNatChars ['1'] n h
  | cons c cs =>
    dsimp [parseMonomial_c_opt_prefix] at h ⊢
    split at h
    · contradiction
    · contradiction
    · change parseIntChars (if ('-' :: c :: cs).getLast? = some '*' then ('-' :: c :: cs).dropLast else []) = some (- (n : ℤ))
      by_cases h_star : (c :: cs).getLast? = some '*'
      · have h_star_dash : ('-' :: c :: cs).getLast? = some '*' := by
          exact h_star
        rw [if_pos h_star] at h
        rw [if_pos h_star_dash]
        have h_drop : ('-' :: c :: cs).dropLast = '-' :: (c :: cs).dropLast := by
          exact List.dropLast_cons_of_ne_nil (by intro h_emp; contradiction)
        rw [h_drop]
        exact parseIntChars_eq_neg_of_parseNatChars _ n h
      · have h_star_dash : ('-' :: c :: cs).getLast? ≠ some '*' := by
          exact h_star
        rw [if_neg h_star] at h
        rw [if_neg h_star_dash]
        exact parseIntChars_eq_neg_of_parseNatChars _ n h

lemma parseMonomial_int_pos_helper (cs : List Char) (d : ℕ) (n : ℕ) (h : parseMonomial (R := ℕ) cs = some (d, n)) :
  parseMonomial (R := ℤ) cs = some (d, (n : ℤ)) := by
  dsimp [parseMonomial] at h ⊢
  cases h_split : cs.splitOn 'x'
  · rw [h_split] at h; contradiction
  · rename_i hd tail
    cases tail
    · rw [h_split] at h
      dsimp at h ⊢
      cases hc : DensePolyParsable.parse (R := ℕ) hd
      · rw [hc] at h; dsimp at h; contradiction
      · rename_i val_n
        rw [hc] at h; dsimp at h
        injection h with heq; injection heq with hd_eq hn_eq
        subst hd_eq hn_eq
        have hc_int := parseIntChars_eq_some_of_parseNatChars hd val_n hc
        change (parseIntChars hd).bind (fun c => some (0, c)) = some (0, (val_n : ℤ))
        rw [hc_int]
        rfl
    · rename_i tail_head tail_tail
      cases tail_tail
      · rw [h_split] at h
        dsimp at h ⊢
        split at h
        · generalize h_match : parseMonomial_c_opt_prefix hd = hd_match at h ⊢
          cases h_parse : DensePolyParsable.parse (R := ℕ) hd_match
          · rw [h_parse] at h; contradiction
          · rename_i val_n
            rw [h_parse] at h; dsimp at h
            injection h with heq; injection heq with hd_eq hn_eq
            subst hd_eq hn_eq
            have hc_input := h_match.symm ▸ h_parse
            have hc_int := parseMonomial_c_opt_int_pos hd val_n hc_input
            rw [h_match] at hc_int
            change (DensePolyParsable.parse (R := ℤ) hd_match).bind (fun c => some (1, c)) = some (1, (val_n : ℤ))
            rw [hc_int]
            rfl
        · rename_i rest
          generalize hn_chars : parseNatChars rest = res_d at h
          cases res_d
          · contradiction
          · rename_i val_d
            dsimp at h
            generalize h_match : parseMonomial_c_opt_prefix hd = hd_match at h ⊢
            cases h_parse : DensePolyParsable.parse (R := ℕ) hd_match
            · rw [h_parse] at h; contradiction
            · rename_i val_n
              rw [h_parse] at h; dsimp at h
              injection h with heq; injection heq with hd_eq hn_eq
              subst hd_eq hn_eq
              have hc_input := h_match.symm ▸ h_parse
              have hc_int := parseMonomial_c_opt_int_pos hd val_n hc_input
              rw [h_match] at hc_int
              change (Option.bind (some val_d) fun y => (DensePolyParsable.parse (R := ℤ) hd_match).bind fun c => some (y, c)) = some (val_d, (val_n : ℤ))
              rw [hc_int]
              rfl
        · contradiction
      case cons head2 tail2 =>
        rw [h_split] at h
        contradiction

lemma parseMonomial_int_neg_helper (cs : List Char) (d : ℕ) (n : ℕ) (h : parseMonomial (R := ℕ) cs = some (d, n)) :
  parseMonomial (R := ℤ) ('-' :: cs) = some (d, - (n : ℤ)) := by
  dsimp [parseMonomial] at h ⊢
  cases h_split : cs.splitOn 'x'
  · rw [h_split] at h; contradiction
  · rename_i hd tail
    have h_split_neg : ('-' :: cs).splitOn 'x' = ('-' :: hd) :: tail := by
      dsimp [List.splitOn, List.splitOnP] at h_split ⊢
      have h_dash : ('-' == 'x') = false := rfl
      rw [splitOnP_go_cons_false 'x' '-' cs [] (by decide)]
      exact splitOnP_go_accum '-' cs hd tail h_split
    rw [h_split_neg]
    cases tail
    · rw [h_split] at h
      dsimp at h ⊢
      cases hc : DensePolyParsable.parse (R := ℕ) hd
      · rw [hc] at h; dsimp at h; contradiction
      · rename_i val_n
        rw [hc] at h; dsimp at h
        injection h with heq; injection heq with hd_eq hn_eq
        subst hd_eq hn_eq
        have hc_int := parseIntChars_eq_neg_of_parseNatChars hd val_n hc
        change (parseIntChars ('-' :: hd)).bind (fun c => some (0, c)) = some (0, -(val_n : ℤ))
        rw [hc_int]
        rfl
    · rename_i tail_head tail_tail
      cases tail_tail
      · rw [h_split] at h
        dsimp at h ⊢
        split at h
        · generalize h_match : parseMonomial_c_opt_prefix ('-' :: hd) = hd_match at ⊢
          generalize h_match_pos : parseMonomial_c_opt_prefix hd = hd_match_pos at h
          cases h_parse : DensePolyParsable.parse (R := ℕ) hd_match_pos
          · rw [h_parse] at h; contradiction
          · rename_i val_n
            rw [h_parse] at h; dsimp at h
            injection h with heq; injection heq with hd_eq hn_eq
            subst hd_eq hn_eq
            have hc_input := h_match_pos.symm ▸ h_parse
            have hc_int := parseMonomial_c_opt_int_neg hd val_n hc_input
            rw [h_match] at hc_int
            change (DensePolyParsable.parse (R := ℤ) hd_match).bind (fun c => some (1, c)) = some (1, -(val_n : ℤ))
            rw [hc_int]
            rfl
        · rename_i rest
          generalize hn_chars : parseNatChars rest = res_d at h
          cases res_d
          · contradiction
          · rename_i val_d
            dsimp at h
            generalize h_match : parseMonomial_c_opt_prefix ('-' :: hd) = hd_match at ⊢
            generalize h_match_pos : parseMonomial_c_opt_prefix hd = hd_match_pos at h
            cases h_parse : DensePolyParsable.parse (R := ℕ) hd_match_pos
            · rw [h_parse] at h; contradiction
            · rename_i val_n
              rw [h_parse] at h; dsimp at h
              injection h with heq; injection heq with hd_eq hn_eq
              subst hd_eq hn_eq
              have hc_input := h_match_pos.symm ▸ h_parse
              have hc_int := parseMonomial_c_opt_int_neg hd val_n hc_input
              rw [h_match] at hc_int
              change (Option.bind (some val_d) fun y => (DensePolyParsable.parse (R := ℤ) hd_match).bind fun c => some (y, c)) = some (val_d, -(val_n : ℤ))
              rw [hc_int]
              rfl
        · contradiction
      · rw [h_split] at h
        contradiction

lemma parse_monomialToChars_ne_zero_int (d : ℕ) (c : ℤ) (hc : c ≠ 0) :
  parseMonomial (R := ℤ) (monomialToChars d c) = some (d, c) := by
  dsimp [monomialToChars]
  split
  · contradiction
  · split
    · rename_i hd0
      -- d = 0
      dsimp [parseMonomial]
      have h_toChars : DensePolyToChars.toChars c = intToChars c := rfl
      rw [h_toChars]
      have h_split : (intToChars c).splitOn 'x' = [intToChars c] := splitOn_not_mem_x _ (not_mem_intToChars_x c)
      rw [h_split]
      simp [DensePolyParsable.parse]
      rw [parseIntChars_intToChars]
      dsimp
      rw [hd0]
    · rename_i hd0
      -- d ≠ 0
      have h_toChars : DensePolyToChars.toChars c = intToChars c := rfl
      have hx_not_mem := not_mem_intToChars_x c
      by_cases hc1 : c = 1
      · -- x^d or x
        by_cases hd1 : d = 1
        · -- x
          have hc1_decide : (DensePolyToChars.toChars c == ['1']) = true := by
            rw [h_toChars, hc1]
            rfl
          have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = false := by
            rw [h_toChars, hc1]
            rfl
          simp [hc1_decide, hd1]
          dsimp [parseMonomial]
          have h_split : List.splitOn 'x' ['x'] = [[], []] := rfl
          rw [h_split]
          dsimp
          have h_parse : DensePolyParsable.parse (R := ℤ) (parseMonomial_c_opt_prefix []) = some 1 := rfl
          rw [h_parse]
          dsimp
          rw [hc1]
        · -- x^d
          have hc1_decide : (DensePolyToChars.toChars c == ['1']) = true := by
            rw [h_toChars, hc1]
            rfl
          have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = false := by
            rw [h_toChars, hc1]
            rfl
          simp [hc1_decide, hd1]
          dsimp [parseMonomial]
          have h_split : List.splitOn 'x' ('x' :: '^' :: natToChars d) = [[], '^' :: natToChars d] := splitOn_x_pow _ (not_mem_natToChars_x d)
          rw [h_split]
          dsimp
          have h_parse : DensePolyParsable.parse (R := ℤ) (parseMonomial_c_opt_prefix []) = some 1 := rfl
          rw [h_parse]
          simp
          have h_d : parseNatChars (natToChars d) = some d := parseNatChars_natToChars d
          rw [h_d]
          dsimp
          rw [hc1]
      · by_cases hcn1 : c = -1
        · -- -x^d or -x
          by_cases hd1 : d = 1
          · -- -x
            have hc1_decide : (DensePolyToChars.toChars c == ['1']) = false := by
              rw [h_toChars, hcn1]
              rfl
            have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = true := by
              rw [h_toChars, hcn1]
              rfl
            simp [hc1_decide, hc2_decide, hd1]
            dsimp [parseMonomial]
            have h_split : List.splitOn 'x' ['-', 'x'] = [['-'], []] := rfl
            rw [h_split]
            dsimp
            have h_parse : DensePolyParsable.parse (R := ℤ) (parseMonomial_c_opt_prefix ['-']) = some (-1) := rfl
            rw [h_parse]
            dsimp
            rw [hcn1]
          · -- -x^d
            have hc1_decide : (DensePolyToChars.toChars c == ['1']) = false := by
              rw [h_toChars, hcn1]
              rfl
            have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = true := by
              rw [h_toChars, hcn1]
              rfl
            simp [hc1_decide, hc2_decide, hd1]
            dsimp [parseMonomial]
            have h_split : List.splitOn 'x' ('-' :: 'x' :: '^' :: natToChars d) = [['-'], '^' :: natToChars d] := splitOn_neg_x_pow _ (not_mem_natToChars_x d)
            rw [h_split]
            dsimp
            have h_parse : DensePolyParsable.parse (R := ℤ) (parseMonomial_c_opt_prefix ['-']) = some (-1) := rfl
            rw [h_parse]
            simp
            have h_d : parseNatChars (natToChars d) = some d := parseNatChars_natToChars d
            rw [h_d]
            dsimp
            rw [hcn1]
        · by_cases hd1 : d = 1
          · -- cx
            have hc1_decide : (DensePolyToChars.toChars c == ['1']) = false := by
              cases h : (DensePolyToChars.toChars c == ['1'])
              · rfl
              · exfalso
                have h_eq : DensePolyToChars.toChars c = ['1'] := eq_of_beq h
                have h_parse : parseIntChars (DensePolyToChars.toChars c) = some c := by rw [h_toChars, parseIntChars_intToChars]
                rw [h_eq] at h_parse
                have h_1 : parseIntChars ['1'] = some 1 := rfl
                rw [h_1] at h_parse
                injection h_parse with h_inj
                exact hc1 h_inj.symm
            have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = false := by
              cases h : (DensePolyToChars.toChars c == ['-', '1'])
              · rfl
              · exfalso
                have h_eq : DensePolyToChars.toChars c = ['-', '1'] := eq_of_beq h
                have h_parse : parseIntChars (DensePolyToChars.toChars c) = some c := by rw [h_toChars, parseIntChars_intToChars]
                rw [h_eq] at h_parse
                have h_1 : parseIntChars ['-', '1'] = some (-1) := rfl
                rw [h_1] at h_parse
                injection h_parse with h_inj
                exact hcn1 h_inj.symm
            simp [hc1_decide, hc2_decide, hd1]
            rw [h_toChars]
            dsimp [parseMonomial]
            have h_split : List.splitOn 'x' (intToChars c ++ ['*', 'x']) = [intToChars c ++ ['*'], []] := splitOn_append_mul_x _ (not_mem_intToChars_x c)
            rw [h_split]
            dsimp
            unfold parseMonomial_c_opt_prefix
            split
            · next h =>
              have h_len : (intToChars c ++ ['*']).length = 0 := by rw [h]; rfl
              simp at h_len
            · next h =>
              have h_last : (intToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
              have hm : (['-'] : List Char).getLast? = some '-' := rfl
              rw [h, hm] at h_last
              injection h_last with h_inj
              have h_false : ('-' : Char) = '*' → False := by decide
              exact False.elim (h_false h_inj)
            · have h_get : (intToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
              have h_drop : (intToChars c ++ ['*']).dropLast = intToChars c := append_star_dropLast _
              simp_rw [if_pos h_get, h_drop]
              have h_parse : DensePolyParsable.parse (R := ℤ) (intToChars c) = some c := parseIntChars_intToChars c
              rw [h_parse]
              rfl
          · -- cx^d
            have hc1_decide : (DensePolyToChars.toChars c == ['1']) = false := by
              cases h : (DensePolyToChars.toChars c == ['1'])
              · rfl
              · exfalso
                have h_eq : DensePolyToChars.toChars c = ['1'] := eq_of_beq h
                have h_parse : parseIntChars (DensePolyToChars.toChars c) = some c := by rw [h_toChars, parseIntChars_intToChars]
                rw [h_eq] at h_parse
                have h_1 : parseIntChars ['1'] = some 1 := rfl
                rw [h_1] at h_parse
                injection h_parse with h_inj
                exact hc1 h_inj.symm
            have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = false := by
              cases h : (DensePolyToChars.toChars c == ['-', '1'])
              · rfl
              · exfalso
                have h_eq : DensePolyToChars.toChars c = ['-', '1'] := eq_of_beq h
                have h_parse : parseIntChars (DensePolyToChars.toChars c) = some c := by rw [h_toChars, parseIntChars_intToChars]
                rw [h_eq] at h_parse
                have h_1 : parseIntChars ['-', '1'] = some (-1) := rfl
                rw [h_1] at h_parse
                injection h_parse with h_inj
                exact hcn1 h_inj.symm
            simp [hc1_decide, hc2_decide, hd1]
            rw [h_toChars]
            dsimp [parseMonomial]
            have h_split : List.splitOn 'x' (intToChars c ++ '*' :: 'x' :: '^' :: natToChars d) = [intToChars c ++ ['*'], '^' :: natToChars d] := splitOn_append_mul_x_pow _ _ (not_mem_intToChars_x c) (not_mem_natToChars_x d)
            rw [h_split]
            simp [DensePolyParsable.parse]
            have h_d : parseNatChars (natToChars d) = some d := parseNatChars_natToChars d
            rw [h_d]
            unfold parseMonomial_c_opt_prefix
            split
            · next h =>
              have h_len : (intToChars c ++ ['*']).length = 0 := by rw [h]; rfl
              simp at h_len
            · next h =>
              have h_last : (intToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
              have hm : (['-'] : List Char).getLast? = some '-' := rfl
              rw [h, hm] at h_last
              injection h_last with h_inj
              have h_false : ('-' : Char) = '*' → False := by decide
              exact False.elim (h_false h_inj)
            · have h_get : (intToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
              have h_drop : (intToChars c ++ ['*']).dropLast = intToChars c := append_star_dropLast _
              simp_rw [if_pos h_get, h_drop]
              rw [parseIntChars_intToChars c]
              rfl

lemma parseZModChars_of_parseNatChars {n : ℕ} [NeZero n] (cs : List Char) (v : ℕ)
  (h : DensePolyParsable.parse (R := ℕ) cs = some v) :
  DensePolyParsable.parse (R := ZMod n) cs = some (v : ZMod n) := by
  dsimp [DensePolyParsable.parse] at h ⊢
  have ht := parseIntChars_eq_some_of_parseNatChars cs v h
  rw [ht]
  dsimp [Option.map, Option.bind]
  congr 1
  exact Int.cast_natCast v

lemma parseMonomial_zmod_of_nat {n : ℕ} [NeZero n] (cs : List Char) (d : ℕ) (v : ℕ)
  (h : parseMonomial (R := ℕ) cs = some (d, v)) :
  parseMonomial (R := ZMod n) cs = some (d, (v : ZMod n)) := by
  dsimp [parseMonomial] at h ⊢
  cases hsplit : cs.splitOn 'x'
  · rw [hsplit] at h; contradiction
  · rename_i c_cs tail
    cases tail
    · rw [hsplit] at h
      dsimp at h ⊢
      cases hparse : DensePolyParsable.parse (R := ℕ) c_cs
      · rw [hparse] at h; contradiction
      · rename_i val
        rw [hparse] at h; dsimp at h
        injection h with heq
        injection heq with hd_eq hv_eq
        subst hd_eq hv_eq
        have hz := parseZModChars_of_parseNatChars (n := n) c_cs val hparse
        rw [hz]
        rfl
    · rename_i head2 tail2
      cases tail2
      · rw [hsplit] at h
        dsimp at h ⊢
        split at h
        · generalize hpfx : parseMonomial_c_opt_prefix c_cs = pfx at h ⊢
          cases hparse : DensePolyParsable.parse (R := ℕ) pfx
          · rw [hparse] at h; contradiction
          · rename_i val
            rw [hparse] at h; dsimp at h
            injection h with heq
            injection heq with hd_eq hv_eq
            subst hd_eq hv_eq
            have hz := parseZModChars_of_parseNatChars (n := n) pfx val hparse
            rw [hz]
            rfl
        · rename_i rest
          generalize hden : parseNatChars rest = val_d at h ⊢
          cases val_d
          · contradiction
          · rename_i val
            dsimp at h ⊢
            generalize hpfx : parseMonomial_c_opt_prefix c_cs = pfx at h ⊢
            cases hparse : DensePolyParsable.parse (R := ℕ) pfx
            · rw [hparse] at h; contradiction
            · rename_i val2
              rw [hparse] at h; dsimp at h
              injection h with heq
              injection heq with hd_eq hv_eq
              subst hd_eq hv_eq
              have hz := parseZModChars_of_parseNatChars (n := n) pfx val2 hparse
              rw [hz]
              rfl
        · contradiction
      · rw [hsplit] at h
        contradiction

lemma monomialToChars_zmod_eq_nat {n : ℕ} [NeZero n] (d : ℕ) (c : ZMod n) :
  monomialToChars (R := ZMod n) d c = if c = 0 then ['0'] else monomialToChars (R := ℕ) d c.val := by
  dsimp [monomialToChars]
  split
  · rfl
  · rename_i hc
    have hc_val : c.val ≠ 0 := by
      intro h
      have hc0 : c = 0 := by
        calc c = (c.val : ZMod n) := (ZMod.natCast_zmod_val c).symm
          _ = (0 : ZMod n) := by rw [h]; exact Nat.cast_zero
      contradiction
    rw [if_neg hc_val]
    rfl

lemma parse_monomialToChars_ne_zero_zmod {n : ℕ} [NeZero n] (d : ℕ) (c : ZMod n) (hc : c ≠ 0) :
  parseMonomial (R := ZMod n) (monomialToChars d c) = some (d, c) := by
  have hc_val : c.val ≠ 0 := by
    intro h
    have hc0 : c = 0 := by
      calc c = (c.val : ZMod n) := (ZMod.natCast_zmod_val c).symm
        _ = (0 : ZMod n) := by rw [h]; exact Nat.cast_zero
    contradiction
  have h_nat := parse_monomialToChars_ne_zero_nat d c.val hc_val
  rw [monomialToChars_zmod_eq_nat d c]
  rw [if_neg hc]
  have hz := parseMonomial_zmod_of_nat (n := n) _ d c.val h_nat
  have heq : (c.val : ZMod n) = c := ZMod.natCast_zmod_val c
  rw [heq] at hz
  exact hz

lemma parse_monomialToChars_ne_zero_rat (d : ℕ) (c : ℚ) (hc : c ≠ 0) :
  parseMonomial (R := ℚ) (monomialToChars d c) = some (d, c) := by
  dsimp [monomialToChars]
  split
  · contradiction
  · split
    · rename_i hd0
      -- d = 0
      dsimp [parseMonomial]
      have h_toChars : DensePolyToChars.toChars c = ratToChars c := rfl
      rw [h_toChars]
      have h_split : (ratToChars c).splitOn 'x' = [ratToChars c] := splitOn_not_mem_x _ (not_mem_ratToChars_x c)
      rw [h_split]
      simp [DensePolyParsable.parse]
      have h_parse := parseRatChars_ratToChars c
      rw [h_parse]
      dsimp
      rw [hd0]
    · rename_i hd0
      -- d ≠ 0
      have h_toChars : DensePolyToChars.toChars c = ratToChars c := rfl
      by_cases hc1 : c = 1
      · -- x^d or x
        by_cases hd1 : d = 1
        · -- x
          have hc1_decide : (DensePolyToChars.toChars c == ['1']) = true := by
            rw [h_toChars, hc1]
            rfl
          have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = false := by
            rw [h_toChars, hc1]
            rfl
          simp [hc1_decide, hd1]
          dsimp [parseMonomial]
          have h_split : List.splitOn 'x' ['x'] = [[], []] := rfl
          rw [h_split]
          dsimp
          have h_parse : DensePolyParsable.parse (R := ℚ) (parseMonomial_c_opt_prefix []) = some 1 := rfl
          rw [h_parse]
          dsimp
          rw [hc1]
        · -- x^d
          have hc1_decide : (DensePolyToChars.toChars c == ['1']) = true := by
            rw [h_toChars, hc1]
            rfl
          have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = false := by
            rw [h_toChars, hc1]
            rfl
          simp [hc1_decide, hd1]
          dsimp [parseMonomial]
          have h_split : List.splitOn 'x' ('x' :: '^' :: natToChars d) = [[], '^' :: natToChars d] := splitOn_x_pow _ (not_mem_natToChars_x d)
          rw [h_split]
          dsimp
          have h_parse : DensePolyParsable.parse (R := ℚ) (parseMonomial_c_opt_prefix []) = some 1 := rfl
          rw [h_parse]
          simp
          have h_d : parseNatChars (natToChars d) = some d := parseNatChars_natToChars d
          rw [h_d]
          dsimp
          rw [hc1]
      · by_cases hcn1 : c = -1
        · -- -x^d or -x
          by_cases hd1 : d = 1
          · -- -x
            have hc1_decide : (DensePolyToChars.toChars c == ['1']) = false := by
              rw [h_toChars, hcn1]
              rfl
            have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = true := by
              rw [h_toChars, hcn1]
              rfl
            simp [hc1_decide, hc2_decide, hd1]
            dsimp [parseMonomial]
            have h_split : List.splitOn 'x' ['-', 'x'] = [['-'], []] := rfl
            rw [h_split]
            dsimp
            have h_parse : DensePolyParsable.parse (R := ℚ) (parseMonomial_c_opt_prefix ['-']) = some (-1) := rfl
            rw [h_parse]
            dsimp
            rw [hcn1]
          · -- -x^d
            have hc1_decide : (DensePolyToChars.toChars c == ['1']) = false := by
              rw [h_toChars, hcn1]
              rfl
            have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = true := by
              rw [h_toChars, hcn1]
              rfl
            simp [hc1_decide, hc2_decide, hd1]
            dsimp [parseMonomial]
            have h_split : List.splitOn 'x' ('-' :: 'x' :: '^' :: natToChars d) = [['-'], '^' :: natToChars d] := splitOn_neg_x_pow _ (not_mem_natToChars_x d)
            rw [h_split]
            dsimp
            have h_parse : DensePolyParsable.parse (R := ℚ) (parseMonomial_c_opt_prefix ['-']) = some (-1) := rfl
            rw [h_parse]
            simp
            have h_d : parseNatChars (natToChars d) = some d := parseNatChars_natToChars d
            rw [h_d]
            dsimp
            rw [hcn1]
        · by_cases hd1 : d = 1
          · -- cx
            have hc1_decide : (DensePolyToChars.toChars c == ['1']) = false := by
              cases h : (DensePolyToChars.toChars c == ['1'])
              · rfl
              · exfalso
                have h_eq : DensePolyToChars.toChars c = ['1'] := eq_of_beq h
                have h_parse : parseRatChars (DensePolyToChars.toChars c) = some c := by rw [h_toChars, parseRatChars_ratToChars]
                rw [h_eq] at h_parse
                have h_1 : parseRatChars ['1'] = some 1 := rfl
                rw [h_1] at h_parse
                injection h_parse with h_inj
                exact hc1 h_inj.symm
            have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = false := by
              cases h : (DensePolyToChars.toChars c == ['-', '1'])
              · rfl
              · exfalso
                have h_eq : DensePolyToChars.toChars c = ['-', '1'] := eq_of_beq h
                have h_parse : parseRatChars (DensePolyToChars.toChars c) = some c := by rw [h_toChars, parseRatChars_ratToChars]
                rw [h_eq] at h_parse
                have h_1 : parseRatChars ['-', '1'] = some (-1) := rfl
                rw [h_1] at h_parse
                injection h_parse with h_inj
                exact hcn1 h_inj.symm
            simp [hc1_decide, hc2_decide, hd1]
            rw [h_toChars]
            dsimp [parseMonomial]
            have h_split : List.splitOn 'x' (ratToChars c ++ ['*', 'x']) = [ratToChars c ++ ['*'], []] := splitOn_append_mul_x _ (not_mem_ratToChars_x c)
            rw [h_split]
            dsimp
            unfold parseMonomial_c_opt_prefix
            split
            · next h =>
              have h_len : (ratToChars c ++ ['*']).length = 0 := by rw [h]; rfl
              simp at h_len
            · next h =>
              have h_last : (ratToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
              have hm : (['-'] : List Char).getLast? = some '-' := rfl
              rw [h, hm] at h_last
              injection h_last with h_inj
              have h_false : ('-' : Char) = '*' → False := by decide
              exact False.elim (h_false h_inj)
            · have h_get : (ratToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
              have h_drop : (ratToChars c ++ ['*']).dropLast = ratToChars c := append_star_dropLast _
              simp_rw [if_pos h_get, h_drop]
              have h_parse : DensePolyParsable.parse (R := ℚ) (ratToChars c) = some c := parseRatChars_ratToChars c
              rw [h_parse]
              rfl
          · -- cx^d
            have hc1_decide : (DensePolyToChars.toChars c == ['1']) = false := by
              cases h : (DensePolyToChars.toChars c == ['1'])
              · rfl
              · exfalso
                have h_eq : DensePolyToChars.toChars c = ['1'] := eq_of_beq h
                have h_parse : parseRatChars (DensePolyToChars.toChars c) = some c := by rw [h_toChars, parseRatChars_ratToChars]
                rw [h_eq] at h_parse
                have h_1 : parseRatChars ['1'] = some 1 := rfl
                rw [h_1] at h_parse
                injection h_parse with h_inj
                exact hc1 h_inj.symm
            have hc2_decide : (DensePolyToChars.toChars c == ['-', '1']) = false := by
              cases h : (DensePolyToChars.toChars c == ['-', '1'])
              · rfl
              · exfalso
                have h_eq : DensePolyToChars.toChars c = ['-', '1'] := eq_of_beq h
                have h_parse : parseRatChars (DensePolyToChars.toChars c) = some c := by rw [h_toChars, parseRatChars_ratToChars]
                rw [h_eq] at h_parse
                have h_1 : parseRatChars ['-', '1'] = some (-1) := rfl
                rw [h_1] at h_parse
                injection h_parse with h_inj
                exact hcn1 h_inj.symm
            simp [hc1_decide, hc2_decide, hd1]
            rw [h_toChars]
            dsimp [parseMonomial]
            have h_split : List.splitOn 'x' (ratToChars c ++ '*' :: 'x' :: '^' :: natToChars d) = [ratToChars c ++ ['*'], '^' :: natToChars d] := splitOn_append_mul_x_pow _ _ (not_mem_ratToChars_x c) (not_mem_natToChars_x d)
            rw [h_split]
            simp [DensePolyParsable.parse]
            have h_d : parseNatChars (natToChars d) = some d := parseNatChars_natToChars d
            rw [h_d]
            unfold parseMonomial_c_opt_prefix
            split
            · next h =>
              have h_len : (ratToChars c ++ ['*']).length = 0 := by rw [h]; rfl
              simp at h_len
            · next h =>
              have h_last : (ratToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
              have hm : (['-'] : List Char).getLast? = some '-' := rfl
              rw [h, hm] at h_last
              injection h_last with h_inj
              have h_false : ('-' : Char) = '*' → False := by decide
              exact False.elim (h_false h_inj)
            · have h_get : (ratToChars c ++ ['*']).getLast? = some '*' := append_star_getLast? _
              have h_drop : (ratToChars c ++ ['*']).dropLast = ratToChars c := append_star_dropLast _
              simp_rw [if_pos h_get, h_drop]
              rw [parseRatChars_ratToChars c]
              rfl

/-! ### `DensePolyParsableValid` typeclass -/

class DensePolyParsableValid (R : Type _) [DecidableEq R] [Zero R] [DensePolyToChars R] [DensePolyParsable R] : Prop where
  parse_monomialToChars_ne_zero : ∀ (d : ℕ) (c : R) (_ : c ≠ 0), parseMonomial (monomialToChars d c) = some (d, c)

export DensePolyParsableValid (parse_monomialToChars_ne_zero)

instance : DensePolyParsableValid ℕ where
  parse_monomialToChars_ne_zero := parse_monomialToChars_ne_zero_nat

instance : DensePolyParsableValid ℤ where
  parse_monomialToChars_ne_zero := parse_monomialToChars_ne_zero_int

instance : DensePolyParsableValid ℚ where
  parse_monomialToChars_ne_zero := parse_monomialToChars_ne_zero_rat

instance {n : ℕ} [NeZero n] : DensePolyParsableValid (ZMod n) where
  parse_monomialToChars_ne_zero := parse_monomialToChars_ne_zero_zmod

/-! ### `DensePolyToCharsValid` typeclass

This captures the ne-nil and not-start-zero properties of the character representation
for each coefficient type. It allows the `monomialToChars` correctness lemmas to be
proved generically once rather than once per ring type.
-/

/-- A typeclass asserting that `DensePolyToChars.toChars r` is never empty
    and never starts with `'0'` unless `r = 0`. -/
class DensePolyToCharsValid (R : Type*) [DecidableEq R] [Zero R] [DensePolyToChars R] : Prop where
  /-- The char representation is never the empty list. -/
  toChars_ne_nil : ∀ (r : R), DensePolyToChars.toChars r ≠ []
  /-- For nonzero `r`, the char representation does not start with `'0'`. -/
  toChars_not_start_zero : ∀ (r : R) (cs : List Char), r ≠ 0 → DensePolyToChars.toChars r ≠ '0' :: cs

instance : DensePolyToCharsValid ℕ where
  toChars_ne_nil c := natToChars_ne_nil c
  toChars_not_start_zero c cs hc := natToChars_not_start_zero c cs hc

instance : DensePolyToCharsValid ℤ where
  toChars_ne_nil c := intToChars_ne_nil c
  toChars_not_start_zero c cs hc := intToChars_not_start_zero c cs hc

instance : DensePolyToCharsValid ℚ where
  toChars_ne_nil c := ratToChars_ne_nil c
  toChars_not_start_zero c cs hc := ratToChars_not_start_zero c cs hc

instance {n : ℕ} [NeZero n] : DensePolyToCharsValid (ZMod n) where
  toChars_ne_nil c := by
    show natToChars c.val ≠ []
    exact natToChars_ne_nil c.val
  toChars_not_start_zero c cs hc := by
    show natToChars c.val ≠ '0' :: cs
    have hc_val : c.val ≠ 0 := by
      intro h; apply hc
      exact ZMod.val_injective n (h ▸ ZMod.val_zero.symm)
    exact natToChars_not_start_zero c.val cs hc_val

/-- If `DensePolyToCharsValid R`, then `monomialToChars d c` is never `[]`. -/
lemma monomialToChars_ne_nil {R : Type*} [DecidableEq R] [Zero R] [DensePolyToChars R]
    [DensePolyToCharsValid R] (d : ℕ) (c : R) : monomialToChars d c ≠ [] := by
  dsimp [monomialToChars]; split_ifs
  · intro h; contradiction
  · exact DensePolyToCharsValid.toChars_ne_nil c
  · simp
  · simp
  · intro h; contradiction
  · intro h; contradiction
  · intro h; simp [List.append_assoc] at h
  · intro h; simp [List.append_assoc] at h

/-- If `l1 ≠ []` and `l1` never starts with `c`, then neither does `l1 ++ l2`. -/
lemma append_not_start_char {α : Type*} (l1 l2 : List α) (c : α) (h_nil : l1 ≠ [])
    (h_start : ∀ cs, l1 ≠ c :: cs) : ∀ cs, l1 ++ l2 ≠ c :: cs := by
  intro cs h
  cases l1 with
  | nil => contradiction
  | cons head tail =>
    have h_head : head = c := by injection h
    subst h_head
    exact h_start tail rfl

/-- If the head of a list of lists does not start with `c`, neither does the flatten. -/
lemma flatten_not_start_char_of_head_not_start_char {α : Type*} (l : List (List α)) (c : α)
    (h_nil : l ≠ []) (h_not_empty : ∀ m ∈ l, m ≠ []) (h_head : ∀ cs, l.head h_nil ≠ c :: cs) :
    ∀ cs, l.flatten ≠ c :: cs := by
  intro cs h
  cases l with
  | nil => contradiction
  | cons head tail =>
    rw [List.flatten_cons] at h
    have h_head_not_empty : head ≠ [] := h_not_empty head (List.Mem.head _)
    cases head with
    | nil => contradiction
    | cons h_head_elem h_tail_elem =>
      have h_head_eq : h_head_elem = c := by injection h
      exact h_head h_tail_elem (h_head_eq ▸ rfl)

/-- If `DensePolyToCharsValid R` and `c ≠ 0`, then `monomialToChars d c` does not start with `'0'`. -/
lemma monomialToChars_not_start_zero {R : Type*} [DecidableEq R] [Zero R] [DensePolyToChars R]
    [DensePolyToCharsValid R] (d : ℕ) (c : R) (cs : List Char) (hc : c ≠ 0) :
    monomialToChars d c ≠ '0' :: cs := by
  dsimp [monomialToChars]; split_ifs
  · intro h; contradiction
  · exact DensePolyToCharsValid.toChars_not_start_zero c cs hc
  · simp
  · simp
  · simp
  · simp
  · rw [show DensePolyToChars.toChars c ++ ['*'] ++ ['x'] =
          DensePolyToChars.toChars c ++ ['*', 'x'] by simp]
    exact append_not_start_char _ _ '0'
      (DensePolyToCharsValid.toChars_ne_nil c)
      (fun cs => DensePolyToCharsValid.toChars_not_start_zero c cs hc) cs
  · rw [show DensePolyToChars.toChars c ++ ['*'] ++ 'x' :: '^' :: natToChars d =
          DensePolyToChars.toChars c ++ ('*' :: 'x' :: '^' :: natToChars d) by simp]
    exact append_not_start_char _ _ '0'
      (DensePolyToCharsValid.toChars_ne_nil c)
      (fun cs => DensePolyToCharsValid.toChars_not_start_zero c cs hc) cs



-- Backward-compatible aliases for downstream callers
lemma monomialToChars_nat_ne_nil (d : ℕ) (c : ℕ) : monomialToChars d c ≠ [] :=
  monomialToChars_ne_nil d c
lemma monomialToChars_int_ne_nil (d : ℕ) (c : ℤ) : monomialToChars d c ≠ [] :=
  monomialToChars_ne_nil d c
lemma monomialToChars_rat_ne_nil (d : ℕ) (c : ℚ) : monomialToChars d c ≠ [] :=
  monomialToChars_ne_nil d c
lemma monomialToChars_zmod_ne_nil {n : ℕ} [NeZero n] (d : ℕ) (c : ZMod n) : monomialToChars d c ≠ [] :=
  monomialToChars_ne_nil d c
lemma monomialToChars_nat_not_start_zero (d : ℕ) (c : ℕ) (cs : List Char) (hc : c ≠ 0) :
    monomialToChars d c ≠ '0' :: cs :=
  monomialToChars_not_start_zero d c cs hc
lemma monomialToChars_int_not_start_zero (d : ℕ) (c : ℤ) (cs : List Char) (hc : c ≠ 0) :
    monomialToChars d c ≠ '0' :: cs :=
  monomialToChars_not_start_zero d c cs hc
lemma monomialToChars_rat_not_start_zero (d : ℕ) (c : ℚ) (cs : List Char) (hc : c ≠ 0) :
    monomialToChars d c ≠ '0' :: cs :=
  monomialToChars_not_start_zero d c cs hc
lemma monomialToChars_zmod_not_start_zero {n : ℕ} [NeZero n] (d : ℕ) (c : ZMod n) (cs : List Char)
    (hc : c ≠ 0) : monomialToChars d c ≠ '0' :: cs :=
  monomialToChars_not_start_zero d c cs hc




lemma string_ofList_ne_empty_of_ne_nil {l : List Char} (h : l ≠ []) : String.ofList l ≠ "" := by
  intro contra
  have : l.length = 0 := by
    have := String.length_ofList (l := l)
    rw [contra] at this; simp at this; omega
  exact h (List.length_eq_zero_iff.mp this)




lemma listEnum_aux_length {α} (l : List α) (acc : List (ℕ × α)) (n : ℕ) :
  (listEnum.aux acc n l).length = acc.length + l.length := by
  induction l generalizing acc n with
  | nil =>
    have hl : ([] : List α).length = 0 := rfl
    rw [hl, add_zero]
    dsimp [listEnum.aux]
    rw [List.length_reverse]
  | cons x xs ih =>
    dsimp [listEnum.aux]
    rw [ih]
    have h_len : ((n, x) :: acc).length = acc.length + 1 := rfl
    have h_xs : (x :: xs).length = xs.length + 1 := rfl
    omega

lemma listEnum_length {α} (l : List α) : (listEnum l).length = l.length := by
  dsimp [listEnum]
  have h := listEnum_aux_length l [] 0
  have h_acc : ([] : List (ℕ × α)).length = 0 := rfl
  rw [h_acc, zero_add] at h
  exact h

lemma listEnum_eq_nil_iff {α} (l : List α) : listEnum l = [] ↔ l = [] := by
  have hl : (listEnum l).length = l.length := listEnum_length l
  constructor
  · intro h
    rw [h] at hl
    change 0 = l.length at hl
    cases l
    · rfl
    · contradiction
  · intro h
    rw [h]
    rfl

lemma listEnum_aux_mem {α} (l : List α) (acc : List (ℕ × α)) (n : ℕ) (y : α) :
  y ∈ l ∨ (∃ i, (i, y) ∈ acc) → ∃ i, (i, y) ∈ listEnum.aux acc n l := by
  induction l generalizing acc n with
  | nil =>
    intro h
    cases h with
    | inl h_not => contradiction
    | inr h_acc =>
      dsimp [listEnum.aux]
      rcases h_acc with ⟨i, hi⟩
      exact ⟨i, List.mem_reverse.mpr hi⟩
  | cons x xs ih =>
    intro h
    dsimp [listEnum.aux]
    cases h with
    | inl h_mem =>
      match h_mem with
      | .head _ =>
        apply ih ((n, y) :: acc) (n + 1)
        right
        exact ⟨n, List.Mem.head _⟩
      | .tail _ ht =>
        apply ih ((n, x) :: acc) (n + 1)
        left
        exact ht
    | inr h_acc =>
      apply ih ((n, x) :: acc) (n + 1)
      right
      rcases h_acc with ⟨i, hi⟩
      exact ⟨i, List.Mem.tail _ hi⟩

lemma mem_listEnum {α} (l : List α) (y : α) : y ∈ l → ∃ i, (i, y) ∈ listEnum l := by
  intro h
  exact listEnum_aux_mem l [] 0 y (Or.inl h)

lemma filter_nonZero_ne_nil {R} [Zero R] [DecidableEq R] (l : List R) (h_mem : ∃ x ∈ l, x ≠ (0 : R)) :
  (listEnum l).filter (fun (_, c) => c ≠ 0) ≠ [] := by
  rcases h_mem with ⟨x, hx_in, hx_nz⟩
  have h_enum := mem_listEnum l x hx_in
  rcases h_enum with ⟨i, hi⟩
  intro contra
  have h_filter : (i, x) ∉ (listEnum l).filter (fun (_, c) => c ≠ 0) := by
    rw [contra]
    intro hc
    cases hc
  rw [List.mem_filter] at h_filter
  push_neg at h_filter
  have ht := h_filter hi
  dsimp at ht
  rw [decide_eq_true_eq] at ht
  contradiction

private lemma map_ne_nil_of_ne_nil {α β} (f : α → β) (l : List α) (h : l ≠ []) : l.map f ≠ [] := by
  simp [h]

private lemma reverse_ne_nil_of_ne_nil {α} (l : List α) (h : l ≠ []) : l.reverse ≠ [] :=
  List.reverse_ne_nil_iff.mpr h

lemma flatten_ne_nil_of_mem_ne_nil {α} (l : List (List α)) : l ≠ [] → (∀ x ∈ l, x ≠ []) → l.flatten ≠ [] := by
  induction l with
  | nil =>
    intro h _; contradiction
  | cons x xs ih =>
    intro _ hall
    dsimp [List.flatten]
    have hx : x ≠ [] := hall x (List.Mem.head _)
    cases x
    · contradiction
    · apply List.append_ne_nil_of_left_ne_nil
      intro h; contradiction

lemma mem_toList_of_back?_eq_some {α} (a : Array α) (x : α) :
    a.back? = some x → x ∈ a.toList := fun h =>
  List.mem_of_getLast? (Array.getLast?_toList a ▸ h)

lemma mem_of_mem_listEnum_aux {α} (l : List α) (acc : List (ℕ × α)) (n : ℕ) (x : α) (i : ℕ) :
  (i, x) ∈ listEnum.aux acc n l → x ∈ l ∨ (i, x) ∈ acc := by
  induction l generalizing acc n with
  | nil =>
    intro h
    dsimp [listEnum.aux] at h
    exact Or.inr (List.mem_reverse.mp h)
  | cons c cs ih =>
    intro h
    dsimp [listEnum.aux] at h
    have h_rc := ih ((n, c) :: acc) (n + 1) h
    rcases h_rc with h_l | h_acc
    · exact Or.inl (List.Mem.tail _ h_l)
    · rcases (List.mem_cons.mp h_acc) with h_eq | h_in
      · injection h_eq with h1 h2
        subst h2
        exact Or.inl (List.Mem.head _)
      · exact Or.inr h_in

lemma mem_of_mem_listEnum {α} (l : List α) (x : α) (i : ℕ) : (i, x) ∈ listEnum l → x ∈ l := by
  intro h
  have ht := mem_of_mem_listEnum_aux l [] 0 x i h
  rcases ht with hl | hr
  · exact hl
  · contradiction

lemma monomials_mem {R} [DecidableEq R] [Semiring R] [DensePolyToChars R] (coeffs : List R) (m : List Char) :
  m ∈ (listEnum coeffs |>.filter (fun (_, c) => c ≠ 0) |>.map (fun (d, c) => monomialToChars (R := R) d c)) →
  ∃ d c, m = monomialToChars (R := R) d c := by
  intro h
  have h1 := List.mem_map.mp h
  rcases h1 with ⟨⟨d, c⟩, _, hm⟩
  exact ⟨d, c, hm.symm⟩

lemma withSigns_mem {R} [DecidableEq R] [Semiring R] [DensePolyToChars R] (monomials : List (List Char)) (x : List Char) :
  x ∈ (listEnum monomials.reverse).map (fun (i, m) =>
    if i = 0 then m
    else match m with
    | '-' :: _ => m
    | _ => '+' :: m
  ) → ∃ m ∈ monomials, x = m ∨ x = '+' :: m := by
  intro h
  have h1 := List.mem_map.mp h
  rcases h1 with ⟨⟨i, m⟩, h_enum, hx⟩
  have hm_rev : m ∈ monomials.reverse := mem_of_mem_listEnum _ _ _ h_enum
  have hm : m ∈ monomials := List.mem_reverse.mp hm_rev
  use m, hm
  dsimp at hx
  split_ifs at hx
  · exact Or.inl hx.symm
  · split at hx
    · exact Or.inl hx.symm
    · exact Or.inr hx.symm

def joinWithPlus : List (List Char) → List Char
  | [] => []
  | [x] => x
  | x :: xs => x ++ '+' :: joinWithPlus xs

lemma joinWithPlus_append (x : List Char) (xs : List (List Char)) (hxs : xs ≠ []) :
  joinWithPlus (x :: xs) = x ++ '+' :: joinWithPlus xs := by
  cases xs
  · contradiction
  · rfl

lemma splitPolynomialChars_eq (cs : List Char) :
  splitPolynomialChars cs = if cs = [] then [] else (splitPolynomialCharsAux [] [] cs).reverse := by
  rfl

lemma splitPolynomialCharsAux_no_plus_minus (cs : List Char) (h_no_plus : '+' ∉ cs) (h_no_minus : '-' ∉ cs) (acc : List (List Char)) (current : List Char) :
  splitPolynomialCharsAux acc current cs = (current.reverse ++ cs) :: acc := by
  induction cs generalizing acc current with
  | nil =>
    have h : current.reverse ++ [] = current.reverse := by simp
    rw [h]
    rfl
  | cons c cs ih =>
    have hc_plus : c ≠ '+' := by intro hc; subst hc; apply h_no_plus; exact List.Mem.head cs
    have hc_minus : c ≠ '-' := by intro hc; subst hc; apply h_no_minus; exact List.Mem.head cs
    unfold splitPolynomialCharsAux
    split
    · contradiction
    · rename_i hrest; injection hrest with h_c; subst h_c; contradiction
    · rename_i hrest; injection hrest with h_c; subst h_c; contradiction
    · rename_i hrest; injection hrest with h_c h_cs; subst h_c h_cs
      have h_no_plus_tail : '+' ∉ cs := fun h => h_no_plus (List.mem_cons_of_mem c h)
      have h_no_minus_tail : '-' ∉ cs := fun h => h_no_minus (List.mem_cons_of_mem c h)
      have h_ih := ih h_no_plus_tail h_no_minus_tail acc (c :: current)
      rw [h_ih]
      congr 1
      simp

lemma splitPolynomialCharsAux_append_plus (cs1 cs2 : List Char) (h_no_plus : '+' ∉ cs1) (h_no_minus : '-' ∉ cs1) (acc : List (List Char)) (current : List Char) :
  splitPolynomialCharsAux acc current (cs1 ++ '+' :: cs2) = splitPolynomialCharsAux ((current.reverse ++ cs1) :: acc) [] cs2 := by
  induction cs1 generalizing acc current with
  | nil =>
    have h : current.reverse ++ [] = current.reverse := by simp
    rw [h]
    rfl
  | cons c cs1 ih =>
    have hc_plus : c ≠ '+' := by intro hc; subst hc; apply h_no_plus; exact List.Mem.head cs1
    have hc_minus : c ≠ '-' := by intro hc; subst hc; apply h_no_minus; exact List.Mem.head cs1
    have h_cons : (c :: cs1) ++ '+' :: cs2 = c :: (cs1 ++ '+' :: cs2) := rfl
    rw [h_cons]
    conv => lhs; unfold splitPolynomialCharsAux
    split
    · contradiction
    · rename_i hrest; injection hrest with h_c; subst h_c; contradiction
    · rename_i hrest; injection hrest with h_c; subst h_c; contradiction
    · rename_i hrest; injection hrest with h_c h_cs; subst h_c h_cs
      have h_no_plus_tail : '+' ∉ cs1 := fun h => h_no_plus (List.mem_cons_of_mem c h)
      have h_no_minus_tail : '-' ∉ cs1 := fun h => h_no_minus (List.mem_cons_of_mem c h)
      have h_ih := ih h_no_plus_tail h_no_minus_tail acc (c :: current)
      rw [h_ih]
      congr 2
      simp

lemma splitPolynomialCharsAux_joinWithPlus (L : List (List Char)) (h_no_plus : ∀ x ∈ L, '+' ∉ x) (h_no_minus : ∀ x ∈ L, '-' ∉ x) (h_not_empty : ∀ x ∈ L, x ≠ []) (hL : L ≠ []) (acc : List (List Char)) :
  splitPolynomialCharsAux acc [] (joinWithPlus L) = L.reverse ++ acc := by
  induction L generalizing acc with
  | nil =>
    contradiction
  | cons x xs ih =>
    cases hxs : xs with
    | nil =>
      dsimp [joinWithPlus]
      have hx_no_plus := h_no_plus x (by simp)
      have hx_no_minus := h_no_minus x (by simp)
      have h := splitPolynomialCharsAux_no_plus_minus x hx_no_plus hx_no_minus acc []
      rw [h]
      simp
    | cons y ys =>
      have h_join : joinWithPlus (x :: y :: ys) = x ++ '+' :: joinWithPlus (y :: ys) := rfl
      rw [h_join]
      have hx_no_plus := h_no_plus x (by exact List.Mem.head xs)
      have hx_no_minus := h_no_minus x (by exact List.Mem.head xs)
      have hxs_no_plus : ∀ z ∈ y :: ys, '+' ∉ z := fun z hz =>
        h_no_plus z (by rw [hxs]; exact List.mem_cons_of_mem x hz)
      have hxs_no_minus : ∀ z ∈ y :: ys, '-' ∉ z := fun z hz =>
        h_no_minus z (by rw [hxs]; exact List.mem_cons_of_mem x hz)
      have hxs_not_empty : ∀ z ∈ y :: ys, z ≠ [] := fun z hz =>
        h_not_empty z (by rw [hxs]; exact List.mem_cons_of_mem x hz)
      have h_append := splitPolynomialCharsAux_append_plus x (joinWithPlus (y :: ys)) hx_no_plus hx_no_minus acc []
      rw [h_append]
      have h_simp : ([].reverse ++ x) = x := by simp
      rw [h_simp]
      have hxs_not_nil : xs ≠ [] := by rw [hxs]; intro hc; contradiction
      have h_ih := ih (by rw [hxs]; exact hxs_no_plus) (by rw [hxs]; exact hxs_no_minus) (by rw [hxs]; exact hxs_not_empty) hxs_not_nil (x :: acc)
      rw [hxs] at h_ih
      rw [h_ih]
      simp

lemma joinWithPlus_ne_nil (L : List (List Char)) (h_not_empty : ∀ x ∈ L, x ≠ []) (hL : L ≠ []) : joinWithPlus L ≠ [] := by
  cases L with
  | nil => contradiction
  | cons x xs =>
    cases xs with
    | nil =>
      dsimp [joinWithPlus]
      apply h_not_empty x
      exact List.Mem.head []
    | cons y ys =>
      have h_join : joinWithPlus (x :: y :: ys) = x ++ '+' :: joinWithPlus (y :: ys) := rfl
      rw [h_join]
      intro h
      have hx := h_not_empty x (by apply List.Mem.head)
      cases x with
      | nil => contradiction
      | cons c cs =>
        contradiction

lemma splitPolynomialChars_flatten_plus (L : List (List Char))
  (h_no_plus : ∀ x ∈ L, '+' ∉ x) (h_no_minus : ∀ x ∈ L, '-' ∉ x) (h_not_empty : ∀ x ∈ L, x ≠ []) (hL : L ≠ []) :
  splitPolynomialChars (joinWithPlus L) = L := by
  rw [splitPolynomialChars_eq]
  have hz := splitPolynomialCharsAux_joinWithPlus L h_no_plus h_no_minus h_not_empty hL []
  have hn := joinWithPlus_ne_nil L h_not_empty hL
  rw [if_neg hn]
  rw [hz]
  simp

lemma toChars_ne_empty {R} [DecidableEq R] [Semiring R] [DensePolyToChars R] [DensePolyParsable R] [DensePolyParsableValid R]
  (p : DensePoly R)
  (h_mono_ne_nil : ∀ d c, monomialToChars (R := R) d c ≠ []) :
  toChars p ≠ "" := by
  dsimp [toChars]
  split_ifs
  · intro h; revert h; simp
  · rename_i h_p_ne_zero
    have h_back : p.coeffs.back? ≠ none := by
      intro h_none
      have hp : p.coeffs = #[] := Array.back?_eq_none_iff.mp h_none
      have hpe : p.coeffs = (0 : DensePoly R).coeffs := by
        have hz : (0 : DensePoly R).coeffs = #[] := rfl
        rw [hz, hp]
      have hp0 : p = 0 := DensePoly.ext hpe
      contradiction
    have h_back2 : ∃ c, p.coeffs.back? = some c := by
      rcases Option.ne_none_iff_exists.mp h_back with ⟨c, hc_eq⟩
      exact ⟨c, hc_eq.symm⟩
    rcases h_back2 with ⟨c, hc_eq⟩
    have hc_nz : c ≠ 0 := by
      intro hz
      rw [hz] at hc_eq
      exact p.last_ne_zero hc_eq
    have hc_in : c ∈ p.coeffs.toList := mem_toList_of_back?_eq_some _ _ hc_eq

    let coeffs := p.coeffs.toList
    have hd_nz : (listEnum coeffs).filter (fun (_, c) => c ≠ 0) ≠ [] := filter_nonZero_ne_nil coeffs ⟨c, hc_in, hc_nz⟩
    have hm : ((listEnum coeffs).filter (fun (_, c) => c ≠ 0)).map (fun (d, c) => monomialToChars (R := R) d c) ≠ [] := map_ne_nil_of_ne_nil _ _ hd_nz
    have hr : (((listEnum coeffs).filter (fun (_, c) => c ≠ 0)).map (fun (d, c) => monomialToChars (R := R) d c)).reverse ≠ [] := reverse_ne_nil_of_ne_nil _ hm
    have hl_iff := listEnum_eq_nil_iff ((((listEnum coeffs).filter (fun (_, c) => c ≠ 0)).map (fun (d, c) => monomialToChars (R := R) d c)).reverse)
    have hl : listEnum ((((listEnum coeffs).filter (fun (_, c) => c ≠ 0)).map (fun (d, c) => monomialToChars (R := R) d c)).reverse) ≠ [] := mt hl_iff.mp hr
    have hw : (listEnum (((((listEnum coeffs).filter (fun (_, c) => c ≠ 0)).map (fun (d, c) => monomialToChars (R := R) d c)).reverse))).map (fun (i, m) =>
      if i = 0 then m
      else match m with
      | '-' :: _ => m
      | _ => '+' :: m
    ) ≠ [] := map_ne_nil_of_ne_nil _ _ hl

    have hall : ∀ x ∈ (listEnum (((((listEnum coeffs).filter (fun (_, c) => c ≠ 0)).map (fun (d, c) => monomialToChars (R := R) d c)).reverse))).map (fun (i, m) =>
      if i = 0 then m
      else match m with
      | '-' :: _ => m
      | _ => '+' :: m
    ), x ≠ [] := by
      intro x hx
      have hm_mem := withSigns_mem (R := R) _ x hx
      rcases hm_mem with ⟨m, hm_in, h_eq⟩
      have hd_c := monomials_mem (R := R) coeffs m hm_in
      rcases hd_c with ⟨d, c', h_m_eq⟩
      have hm_nz : m ≠ [] := by
        rw [h_m_eq]
        exact h_mono_ne_nil d c'
      rcases h_eq with rfl | rfl
      · exact hm_nz
      · intro h; contradiction

    have hf := flatten_ne_nil_of_mem_ne_nil _ hw hall
    exact string_ofList_ne_empty_of_ne_nil hf

lemma toChars_nat_ne_empty (p : DensePoly ℕ) : toChars p ≠ "" :=
  toChars_ne_empty p monomialToChars_nat_ne_nil

lemma toChars_nat_not_start_zero_of_ne_zero (p : DensePoly ℕ) (hp : p ≠ 0) (cs : List Char) :
  (toChars p).toList ≠ '0' :: cs := by
  dsimp [toChars]
  split_ifs with hp0
  · contradiction
  · simp only [String.toList_ofList]
    let L1 := (listEnum p.coeffs.toList |>.filter (fun (_, c) => c ≠ 0) |>.map (fun (d, c) => monomialToChars d c)).reverse
    let L2 := (listEnum L1).map (fun (i, m) => if i = 0 then m else match m with | '-' :: _ => m | _ => '+' :: m)

    have h_back : p.coeffs.back? ≠ none := by
      intro h_none
      have hp2 : p.coeffs = #[] := Array.back?_eq_none_iff.mp h_none
      have hpe : p.coeffs = (0 : DensePoly ℕ).coeffs := by
        have hz : (0 : DensePoly ℕ).coeffs = #[] := rfl
        rw [hz, hp2]
      have hp0_eq : p = 0 := DensePoly.ext hpe
      contradiction
    have h_back2 : ∃ c, p.coeffs.back? = some c := by
      rcases Option.ne_none_iff_exists.mp h_back with ⟨c, hc_eq⟩
      exact ⟨c, hc_eq.symm⟩
    rcases h_back2 with ⟨c, hc_eq⟩
    have hc_nz : c ≠ 0 := by
      intro hz
      rw [hz] at hc_eq
      exact p.last_ne_zero hc_eq
    have hc_in : c ∈ p.coeffs.toList := mem_toList_of_back?_eq_some _ _ hc_eq

    let coeffs := p.coeffs.toList
    have hd_nz : (listEnum coeffs).filter (fun (_, c) => c ≠ 0) ≠ [] := filter_nonZero_ne_nil coeffs ⟨c, hc_in, hc_nz⟩
    have hm : ((listEnum coeffs).filter (fun (_, c) => c ≠ 0)).map (fun (d, c) => monomialToChars d c) ≠ [] := map_ne_nil_of_ne_nil _ _ hd_nz
    have hL1_not_nil : L1 ≠ [] := reverse_ne_nil_of_ne_nil _ hm

    have hl_iff := listEnum_eq_nil_iff L1
    have hl : listEnum L1 ≠ [] := mt hl_iff.mp hL1_not_nil
    have hL2_not_nil : L2 ≠ [] := map_ne_nil_of_ne_nil _ _ hl

    have h_not_empty : ∀ m ∈ L2, m ≠ [] := by
      intro x hx
      have hm_mem := withSigns_mem (R := ℕ) _ x hx
      rcases hm_mem with ⟨m, hm_in, h_eq⟩
      have hd_c := monomials_mem (R := ℕ) coeffs m hm_in
      rcases hd_c with ⟨d', c'', h_m_eq⟩
      have hm_nz : m ≠ [] := by
        rw [h_m_eq]
        exact monomialToChars_nat_ne_nil d' c''
      rcases h_eq with rfl | rfl
      · exact hm_nz
      · intro h; contradiction

    have h_no_start_zero : ∀ x ∈ L2, ∀ cs', x ≠ '0' :: cs' := by
      intro x hx cs' h_eq_zero
      have hm_mem := withSigns_mem (R := ℕ) _ x hx
      rcases hm_mem with ⟨m, hm_in, h_eq⟩
      have hm_map := List.mem_map.mp hm_in
      rcases hm_map with ⟨⟨d2, c2⟩, h_in2, h_eq2⟩
      have hd_c : c2 ≠ 0 := by
        have h_in_filter := List.mem_filter.mp h_in2
        exact of_decide_eq_true h_in_filter.right
      have hm_val : m = monomialToChars d2 c2 := h_eq2.symm

      have h_m_not_zero := monomialToChars_nat_not_start_zero d2 c2 cs' hd_c

      rcases h_eq with rfl | rfl
      · rw [hm_val] at h_eq_zero
        exact h_m_not_zero h_eq_zero
      · rw [hm_val] at h_eq_zero
        injection h_eq_zero with h_plus
        contradiction

    have h_head : ∀ cs', L2.head hL2_not_nil ≠ '0' :: cs' := by
      intro cs'
      exact h_no_start_zero (L2.head hL2_not_nil) (List.head_mem hL2_not_nil) cs'

    apply flatten_not_start_char_of_head_not_start_char L2 '0' hL2_not_nil h_not_empty h_head cs

lemma mem_toChars_nat_only_valid (p : DensePoly ℕ) (ch : Char) (h : ch ∈ (toChars p).toList) :
  ch = 'x' ∨ ch = '+' ∨ ch = '*' ∨ ch = '^' ∨ ('0'.toNat ≤ ch.toNat ∧ ch.toNat ≤ '9'.toNat) := by
  dsimp [toChars] at h
  split_ifs at h with hp0
  · -- p = 0
    have hz : ("0" : String).toList = ['0'] := rfl
    rw [hz] at h
    have heq : ch = '0' := List.mem_singleton.mp h
    subst heq
    exact Or.inr (Or.inr (Or.inr (Or.inr (by decide))))
  · -- p ≠ 0
    simp only [String.toList_ofList] at h
    have h_flat := h
    rw [List.mem_flatten] at h_flat
    rcases h_flat with ⟨l, hl_in, h_ch_in⟩
    rw [List.mem_map] at hl_in
    rcases hl_in with ⟨⟨i, m⟩, hm_in, hl_eq⟩
    dsimp at hl_eq
    have hm_mem : m ∈ (listEnum p.coeffs.toList |>.filter (fun (_, c) => c ≠ 0) |>.map (fun (d, c) => monomialToChars d c)).reverse := mem_of_mem_listEnum _ _ _ hm_in
    rw [List.mem_reverse, List.mem_map] at hm_mem
    rcases hm_mem with ⟨⟨d, c⟩, _, hm_eq⟩

    have h_mono : ∀ ch_m ∈ m, ch_m = 'x' ∨ ch_m = '*' ∨ ch_m = '^' ∨ ('0'.toNat ≤ ch_m.toNat ∧ ch_m.toNat ≤ '9'.toNat) := by
      intro ch_m hch_m
      rw [←hm_eq] at hch_m
      exact mem_monomialToChars_nat_only_valid d c ch_m hch_m

    split_ifs at hl_eq with hi0
    · rw [←hl_eq] at h_ch_in
      have hv := h_mono ch h_ch_in
      rcases hv with rfl | hr
      · exact Or.inl rfl
      · rcases hr with rfl | hr2
        · exact Or.inr (Or.inr (Or.inl rfl))
        · rcases hr2 with rfl | hr3
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hr3)))
    · cases h_match : m with
      | nil =>
        rw [h_match] at hl_eq
        rw [←hl_eq] at h_ch_in
        have h_ch_eq : ch = '+' := List.mem_singleton.mp h_ch_in
        subst h_ch_eq
        exact Or.inr (Or.inl rfl)
      | cons m_head m_tail =>
        have h_dash : m_head ≠ '-' := by
          intro hc
          have h_in : '-' ∈ m := by rw [h_match, hc]; exact List.Mem.head _
          have h_mono_dash := h_mono '-' h_in
          revert h_mono_dash
          decide
        rw [h_match] at hl_eq
        split at hl_eq
        · rename_i _ h_match_dash
          injection h_match_dash with h_eq
          exact False.elim (h_dash h_eq)
        · rw [←hl_eq] at h_ch_in
          rcases (List.mem_cons.mp h_ch_in) with rfl | hk
          · exact Or.inr (Or.inl rfl)
          · have h_in_m : ch ∈ m := by rw [h_match]; exact hk
            have hv := h_mono ch h_in_m
            rcases hv with rfl | hr
            · exact Or.inl rfl
            · rcases hr with rfl | hr2
              · exact Or.inr (Or.inr (Or.inl rfl))
              · rcases hr2 with rfl | hr3
                · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                · exact Or.inr (Or.inr (Or.inr (Or.inr hr3)))

lemma toChars_int_not_start_zero_of_ne_zero (p : DensePoly ℤ) (hp : p ≠ 0) (cs : List Char) :
  (toChars p).toList ≠ '0' :: cs := by
  dsimp [toChars]
  split_ifs with hp0
  · contradiction
  · simp only [String.toList_ofList]
    let L1 := (listEnum p.coeffs.toList |>.filter (fun (_, c) => c ≠ 0) |>.map (fun (d, c) => monomialToChars d c)).reverse
    let L2 := (listEnum L1).map (fun (i, m) => if i = 0 then m else match m with | '-' :: _ => m | _ => '+' :: m)

    have h_back : p.coeffs.back? ≠ none := by
      intro h_none
      have hp2 : p.coeffs = #[] := Array.back?_eq_none_iff.mp h_none
      have hpe : p.coeffs = (0 : DensePoly ℤ).coeffs := by
        have hz : (0 : DensePoly ℤ).coeffs = #[] := rfl
        rw [hz, hp2]
      have hp0_eq : p = 0 := DensePoly.ext hpe
      contradiction
    have h_back2 : ∃ c, p.coeffs.back? = some c := by
      rcases Option.ne_none_iff_exists.mp h_back with ⟨c, hc_eq⟩
      exact ⟨c, hc_eq.symm⟩
    rcases h_back2 with ⟨c, hc_eq⟩
    have hc_nz : c ≠ 0 := by
      intro hz
      rw [hz] at hc_eq
      exact p.last_ne_zero hc_eq
    have hc_in : c ∈ p.coeffs.toList := mem_toList_of_back?_eq_some _ _ hc_eq

    let coeffs := p.coeffs.toList
    have hd_nz : (listEnum coeffs).filter (fun (_, c) => c ≠ 0) ≠ [] := filter_nonZero_ne_nil coeffs ⟨c, hc_in, hc_nz⟩
    have hm : ((listEnum coeffs).filter (fun (_, c) => c ≠ 0)).map (fun (d, c) => monomialToChars d c) ≠ [] := map_ne_nil_of_ne_nil _ _ hd_nz
    have hL1_not_nil : L1 ≠ [] := reverse_ne_nil_of_ne_nil _ hm

    have hl_iff := listEnum_eq_nil_iff L1
    have hl : listEnum L1 ≠ [] := mt hl_iff.mp hL1_not_nil
    have hL2_not_nil : L2 ≠ [] := map_ne_nil_of_ne_nil _ _ hl

    have h_not_empty : ∀ m ∈ L2, m ≠ [] := by
      intro x hx
      have hm_mem := withSigns_mem (R := ℤ) _ x hx
      rcases hm_mem with ⟨m, hm_in, h_eq⟩
      have hd_c := monomials_mem (R := ℤ) coeffs m hm_in
      rcases hd_c with ⟨d', c'', h_m_eq⟩
      have hm_nz : m ≠ [] := by
        rw [h_m_eq]
        exact monomialToChars_int_ne_nil d' c''
      rcases h_eq with rfl | rfl
      · exact hm_nz
      · intro h; contradiction

    have h_no_start_zero : ∀ x ∈ L2, ∀ cs', x ≠ '0' :: cs' := by
      intro x hx cs' h_eq_zero
      have hm_mem := withSigns_mem (R := ℤ) _ x hx
      rcases hm_mem with ⟨m, hm_in, h_eq⟩
      have hm_map := List.mem_map.mp hm_in
      rcases hm_map with ⟨⟨d2, c2⟩, h_in2, h_eq2⟩
      have hd_c : c2 ≠ 0 := by
        have h_in_filter := List.mem_filter.mp h_in2
        exact of_decide_eq_true h_in_filter.right
      have hm_val : m = monomialToChars d2 c2 := h_eq2.symm

      have h_m_not_zero := monomialToChars_int_not_start_zero d2 c2 cs' hd_c

      rcases h_eq with rfl | rfl
      · rw [hm_val] at h_eq_zero
        exact h_m_not_zero h_eq_zero
      · rw [hm_val] at h_eq_zero
        injection h_eq_zero with h_plus
        contradiction

    have h_head : ∀ cs', L2.head hL2_not_nil ≠ '0' :: cs' := by
      intro cs'
      exact h_no_start_zero (L2.head hL2_not_nil) (List.head_mem hL2_not_nil) cs'

    apply flatten_not_start_char_of_head_not_start_char L2 '0' hL2_not_nil h_not_empty h_head cs

lemma toChars_int_ne_empty (p : DensePoly ℤ) : toChars p ≠ "" :=
  toChars_ne_empty p monomialToChars_int_ne_nil

lemma mem_toChars_int_only_valid (p : DensePoly ℤ) (ch : Char) (h : ch ∈ (toChars p).toList) :
  ch = 'x' ∨ ch = '+' ∨ ch = '-' ∨ ch = '*' ∨ ch = '^' ∨ ('0'.toNat ≤ ch.toNat ∧ ch.toNat ≤ '9'.toNat) := by
  dsimp [toChars] at h
  split_ifs at h with hp0
  · -- p = 0
    have hz : ("0" : String).toList = ['0'] := rfl
    rw [hz] at h
    have heq : ch = '0' := List.mem_singleton.mp h
    subst heq
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))
  · -- p ≠ 0
    simp only [String.toList_ofList] at h
    have h_flat := h
    rw [List.mem_flatten] at h_flat
    rcases h_flat with ⟨l, hl_in, h_ch_in⟩
    rw [List.mem_map] at hl_in
    rcases hl_in with ⟨⟨i, m⟩, hm_in, hl_eq⟩
    dsimp at hl_eq
    have hm_mem : m ∈ (listEnum p.coeffs.toList |>.filter (fun (_, c) => c ≠ 0) |>.map (fun (d, c) => monomialToChars d c)).reverse := mem_of_mem_listEnum _ _ _ hm_in
    rw [List.mem_reverse, List.mem_map] at hm_mem
    rcases hm_mem with ⟨⟨d, c⟩, _, hm_eq⟩

    have h_mono : ∀ ch_m ∈ m, ch_m = 'x' ∨ ch_m = '*' ∨ ch_m = '^' ∨ ch_m = '-' ∨ ('0'.toNat ≤ ch_m.toNat ∧ ch_m.toNat ≤ '9'.toNat) := by
      intro ch_m hch_m
      rw [←hm_eq] at hch_m
      exact mem_monomialToChars_int_only_valid d c ch_m hch_m

    split_ifs at hl_eq with hi0
    · rw [←hl_eq] at h_ch_in
      have hv := h_mono ch h_ch_in
      rcases hv with rfl | hr
      · exact Or.inl rfl
      · rcases hr with rfl | hr2
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · rcases hr2 with rfl | hr3
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · rcases hr3 with rfl | hr4
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr4))))
    · cases h_match : m with
      | nil =>
        rw [h_match] at hl_eq
        split at hl_eq
        · rename_i _ h_match_dash
          contradiction
        · rw [←hl_eq] at h_ch_in
          have h_ch_eq : ch = '+' := List.mem_singleton.mp h_ch_in
          subst h_ch_eq
          exact Or.inr (Or.inl rfl)
      | cons m_head m_tail =>
        rw [h_match] at hl_eq
        split at hl_eq
        · rename_i _ h_match_dash
          rw [←hl_eq] at h_ch_in
          have h_in_m : ch ∈ m := by rw [h_match]; exact h_ch_in
          have hv := h_mono ch h_in_m
          rcases hv with rfl | hr
          · exact Or.inl rfl
          · rcases hr with rfl | hr2
            · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
            · rcases hr2 with rfl | hr3
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              · rcases hr3 with rfl | hr4
                · exact Or.inr (Or.inr (Or.inl rfl))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr4))))
        · rw [←hl_eq] at h_ch_in
          rcases (List.mem_cons.mp h_ch_in) with rfl | hk
          · exact Or.inr (Or.inl rfl)
          · have h_in_m : ch ∈ m := by rw [h_match]; exact hk
            have hv := h_mono ch h_in_m
            rcases hv with rfl | hr
            · exact Or.inl rfl
            · rcases hr with rfl | hr2
              · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
              · rcases hr2 with rfl | hr3
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                · rcases hr3 with rfl | hr4
                  · exact Or.inr (Or.inr (Or.inl rfl))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr4))))

lemma toChars_rat_not_start_zero_of_ne_zero (p : DensePoly ℚ) (hp : p ≠ 0) (cs : List Char) :
  (toChars p).toList ≠ '0' :: cs := by
  dsimp [toChars]
  split_ifs with hp0
  · contradiction
  · simp only [String.toList_ofList]
    let L1 := (listEnum p.coeffs.toList |>.filter (fun (_, c) => c ≠ 0) |>.map (fun (d, c) => monomialToChars d c)).reverse
    let L2 := (listEnum L1).map (fun (i, m) => if i = 0 then m else match m with | '-' :: _ => m | _ => '+' :: m)

    have h_back : p.coeffs.back? ≠ none := by
      intro h_none
      have hp2 : p.coeffs = #[] := Array.back?_eq_none_iff.mp h_none
      have hpe : p.coeffs = (0 : DensePoly ℚ).coeffs := by
        have hz : (0 : DensePoly ℚ).coeffs = #[] := rfl
        rw [hz, hp2]
      have hp0_eq : p = 0 := DensePoly.ext hpe
      contradiction
    have h_back2 : ∃ c, p.coeffs.back? = some c := by
      rcases Option.ne_none_iff_exists.mp h_back with ⟨c, hc_eq⟩
      exact ⟨c, hc_eq.symm⟩
    rcases h_back2 with ⟨c, hc_eq⟩
    have hc_nz : c ≠ 0 := by
      intro hz
      rw [hz] at hc_eq
      exact p.last_ne_zero hc_eq
    have hc_in : c ∈ p.coeffs.toList := mem_toList_of_back?_eq_some _ _ hc_eq

    let coeffs := p.coeffs.toList
    have hd_nz : (listEnum coeffs).filter (fun (_, c) => c ≠ 0) ≠ [] := filter_nonZero_ne_nil coeffs ⟨c, hc_in, hc_nz⟩
    have hm : ((listEnum coeffs).filter (fun (_, c) => c ≠ 0)).map (fun (d, c) => monomialToChars d c) ≠ [] := map_ne_nil_of_ne_nil _ _ hd_nz
    have hL1_not_nil : L1 ≠ [] := reverse_ne_nil_of_ne_nil _ hm

    have hl_iff := listEnum_eq_nil_iff L1
    have hl : listEnum L1 ≠ [] := mt hl_iff.mp hL1_not_nil
    have hL2_not_nil : L2 ≠ [] := map_ne_nil_of_ne_nil _ _ hl

    have h_not_empty : ∀ m ∈ L2, m ≠ [] := by
      intro x hx
      have hm_mem := withSigns_mem (R := ℚ) _ x hx
      rcases hm_mem with ⟨m, hm_in, h_eq⟩
      have hd_c := monomials_mem (R := ℚ) coeffs m hm_in
      rcases hd_c with ⟨d', c'', h_m_eq⟩
      have hm_nz : m ≠ [] := by
        rw [h_m_eq]
        exact monomialToChars_rat_ne_nil d' c''
      rcases h_eq with rfl | rfl
      · exact hm_nz
      · intro h; contradiction

    have h_no_start_zero : ∀ x ∈ L2, ∀ cs', x ≠ '0' :: cs' := by
      intro x hx cs' h_eq_zero
      have hm_mem := withSigns_mem (R := ℚ) _ x hx
      rcases hm_mem with ⟨m, hm_in, h_eq⟩
      have hm_map := List.mem_map.mp hm_in
      rcases hm_map with ⟨⟨d2, c2⟩, h_in2, h_eq2⟩
      have hd_c : c2 ≠ 0 := by
        have h_in_filter := List.mem_filter.mp h_in2
        exact of_decide_eq_true h_in_filter.right
      have hm_val : m = monomialToChars d2 c2 := h_eq2.symm

      have h_m_not_zero := monomialToChars_rat_not_start_zero d2 c2 cs' hd_c

      rcases h_eq with rfl | rfl
      · rw [hm_val] at h_eq_zero
        exact h_m_not_zero h_eq_zero
      · rw [hm_val] at h_eq_zero
        injection h_eq_zero with h_plus
        contradiction

    have h_head : ∀ cs', L2.head hL2_not_nil ≠ '0' :: cs' := by
      intro cs'
      exact h_no_start_zero (L2.head hL2_not_nil) (List.head_mem hL2_not_nil) cs'

    apply flatten_not_start_char_of_head_not_start_char L2 '0' hL2_not_nil h_not_empty h_head cs

lemma toChars_rat_ne_empty (p : DensePoly ℚ) : toChars p ≠ "" :=
  toChars_ne_empty p monomialToChars_rat_ne_nil

lemma mem_toChars_rat_only_valid (p : DensePoly ℚ) (ch : Char) (h : ch ∈ (toChars p).toList) :
  ch = 'x' ∨ ch = '+' ∨ ch = '-' ∨ ch = '*' ∨ ch = '^' ∨ ch = '/' ∨ ('0'.toNat ≤ ch.toNat ∧ ch.toNat ≤ '9'.toNat) := by
  dsimp [toChars] at h
  split_ifs at h with hp0
  · -- p = 0
    have hz : ("0" : String).toList = ['0'] := rfl
    rw [hz] at h
    have heq : ch = '0' := List.mem_singleton.mp h
    subst heq
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))
  · -- p ≠ 0
    simp only [String.toList_ofList] at h
    have h_flat := h
    rw [List.mem_flatten] at h_flat
    rcases h_flat with ⟨l, hl_in, h_ch_in⟩
    rw [List.mem_map] at hl_in
    rcases hl_in with ⟨⟨i, m⟩, hm_in, hl_eq⟩
    dsimp at hl_eq
    have hm_mem : m ∈ (listEnum p.coeffs.toList |>.filter (fun (_, c) => c ≠ 0) |>.map (fun (d, c) => monomialToChars d c)).reverse := mem_of_mem_listEnum _ _ _ hm_in
    rw [List.mem_reverse, List.mem_map] at hm_mem
    rcases hm_mem with ⟨⟨d, c⟩, _, hm_eq⟩

    have h_mono : ∀ ch_m ∈ m, ch_m = 'x' ∨ ch_m = '*' ∨ ch_m = '^' ∨ ch_m = '/' ∨ ch_m = '-' ∨ ('0'.toNat ≤ ch_m.toNat ∧ ch_m.toNat ≤ '9'.toNat) := by
      intro ch_m hch_m
      rw [←hm_eq] at hch_m
      exact mem_monomialToChars_rat_only_valid d c ch_m hch_m

    split_ifs at hl_eq with hi0
    · rw [←hl_eq] at h_ch_in
      have hv := h_mono ch h_ch_in
      rcases hv with rfl | hr
      · exact Or.inl rfl
      · rcases hr with rfl | hr2
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · rcases hr2 with rfl | hr3
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · rcases hr3 with rfl | hr4
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
            · rcases hr4 with rfl | hr5
              · exact Or.inr (Or.inr (Or.inl rfl))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr5)))))
    · cases h_match : m with
      | nil =>
        rw [h_match] at hl_eq
        split at hl_eq
        · rename_i _ h_match_dash
          contradiction
        · rw [←hl_eq] at h_ch_in
          have h_ch_eq : ch = '+' := List.mem_singleton.mp h_ch_in
          subst h_ch_eq
          exact Or.inr (Or.inl rfl)
      | cons m_head m_tail =>
        rw [h_match] at hl_eq
        split at hl_eq
        · rename_i _ h_match_dash
          rw [←hl_eq] at h_ch_in
          have h_in_m : ch ∈ m := by rw [h_match]; exact h_ch_in
          have hv := h_mono ch h_in_m
          rcases hv with rfl | hr
          · exact Or.inl rfl
          · rcases hr with rfl | hr2
            · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
            · rcases hr2 with rfl | hr3
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              · rcases hr3 with rfl | hr4
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
                · rcases hr4 with rfl | hr5
                  · exact Or.inr (Or.inr (Or.inl rfl))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr5)))))
        · rw [←hl_eq] at h_ch_in
          rcases (List.mem_cons.mp h_ch_in) with rfl | hk
          · exact Or.inr (Or.inl rfl)
          · have h_in_m : ch ∈ m := by rw [h_match]; exact hk
            have hv := h_mono ch h_in_m
            rcases hv with rfl | hr
            · exact Or.inl rfl
            · rcases hr with rfl | hr2
              · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
              · rcases hr2 with rfl | hr3
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                · rcases hr3 with rfl | hr4
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
                  · rcases hr4 with rfl | hr5
                    · exact Or.inr (Or.inr (Or.inl rfl))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr5)))))

lemma toChars_zmod_not_start_zero_of_ne_zero {n : ℕ} [NeZero n] (p : DensePoly (ZMod n)) (hp : p ≠ 0) (cs : List Char) :
  (toChars p).toList ≠ '0' :: cs := by
  dsimp [toChars]
  split_ifs with hp0
  · contradiction
  · simp only [String.toList_ofList]
    let L1 := (listEnum p.coeffs.toList |>.filter (fun (_, c) => c ≠ 0) |>.map (fun (d, c) => monomialToChars d c)).reverse
    let L2 := (listEnum L1).map (fun (i, m) => if i = 0 then m else match m with | '-' :: _ => m | _ => '+' :: m)

    have h_back : p.coeffs.back? ≠ none := by
      intro h_none
      have hp2 : p.coeffs = #[] := Array.back?_eq_none_iff.mp h_none
      have hpe : p.coeffs = (0 : DensePoly (ZMod n)).coeffs := by
        have hz : (0 : DensePoly (ZMod n)).coeffs = #[] := rfl
        rw [hz, hp2]
      have hp0_eq : p = 0 := DensePoly.ext hpe
      contradiction
    have h_back2 : ∃ c, p.coeffs.back? = some c := by
      rcases Option.ne_none_iff_exists.mp h_back with ⟨c, hc_eq⟩
      exact ⟨c, hc_eq.symm⟩
    rcases h_back2 with ⟨c, hc_eq⟩
    have hc_nz : c ≠ 0 := by
      intro hz
      rw [hz] at hc_eq
      exact p.last_ne_zero hc_eq
    have hc_in : c ∈ p.coeffs.toList := mem_toList_of_back?_eq_some _ _ hc_eq

    let coeffs := p.coeffs.toList
    have hd_nz : (listEnum coeffs).filter (fun (_, c) => c ≠ 0) ≠ [] := filter_nonZero_ne_nil coeffs ⟨c, hc_in, hc_nz⟩
    have hm : ((listEnum coeffs).filter (fun (_, c) => c ≠ 0)).map (fun (d, c) => monomialToChars d c) ≠ [] := map_ne_nil_of_ne_nil _ _ hd_nz
    have hL1_not_nil : L1 ≠ [] := reverse_ne_nil_of_ne_nil _ hm

    have hl_iff := listEnum_eq_nil_iff L1
    have hl : listEnum L1 ≠ [] := mt hl_iff.mp hL1_not_nil
    have hL2_not_nil : L2 ≠ [] := map_ne_nil_of_ne_nil _ _ hl

    have h_not_empty : ∀ m ∈ L2, m ≠ [] := by
      intro x hx
      have hm_mem := withSigns_mem (R := ZMod n) _ x hx
      rcases hm_mem with ⟨m, hm_in, h_eq⟩
      have hd_c := monomials_mem (R := ZMod n) coeffs m hm_in
      rcases hd_c with ⟨d', c'', h_m_eq⟩
      have hm_nz : m ≠ [] := by
        rw [h_m_eq]
        exact monomialToChars_zmod_ne_nil d' c''
      rcases h_eq with rfl | rfl
      · exact hm_nz
      · intro h; contradiction

    have h_no_start_zero : ∀ x ∈ L2, ∀ cs', x ≠ '0' :: cs' := by
      intro x hx cs' h_eq_zero
      have hm_mem := withSigns_mem (R := ZMod n) _ x hx
      rcases hm_mem with ⟨m, hm_in, h_eq⟩
      have hm_map := List.mem_map.mp hm_in
      rcases hm_map with ⟨⟨d2, c2⟩, h_in2, h_eq2⟩
      have hd_c : c2 ≠ 0 := by
        have h_in_filter := List.mem_filter.mp h_in2
        exact of_decide_eq_true h_in_filter.right
      have hm_val : m = monomialToChars d2 c2 := h_eq2.symm

      have h_m_not_zero := monomialToChars_zmod_not_start_zero d2 c2 cs' hd_c

      rcases h_eq with rfl | rfl
      · rw [hm_val] at h_eq_zero
        exact h_m_not_zero h_eq_zero
      · rw [hm_val] at h_eq_zero
        injection h_eq_zero with h_plus
        contradiction

    have h_head : ∀ cs', L2.head hL2_not_nil ≠ '0' :: cs' := by
      intro cs'
      exact h_no_start_zero (L2.head hL2_not_nil) (List.head_mem hL2_not_nil) cs'

    apply flatten_not_start_char_of_head_not_start_char L2 '0' hL2_not_nil h_not_empty h_head cs

lemma toChars_zmod_ne_empty {n : ℕ} [NeZero n] (p : DensePoly (ZMod n)) : toChars p ≠ "" :=
  toChars_ne_empty p monomialToChars_zmod_ne_nil

lemma mem_toChars_zmod_only_valid {n : ℕ} [NeZero n] (p : DensePoly (ZMod n)) (ch : Char) (h : ch ∈ (toChars p).toList) :
  ch = 'x' ∨ ch = '+' ∨ ch = '*' ∨ ch = '^' ∨ ('0'.toNat ≤ ch.toNat ∧ ch.toNat ≤ '9'.toNat) := by
  dsimp [toChars] at h
  split_ifs at h with hp0
  · -- p = 0
    have hz : ("0" : String).toList = ['0'] := rfl
    rw [hz] at h
    have heq : ch = '0' := List.mem_singleton.mp h
    subst heq
    exact Or.inr (Or.inr (Or.inr (Or.inr (by decide))))
  · -- p ≠ 0
    simp only [String.toList_ofList] at h
    have h_flat := h
    rw [List.mem_flatten] at h_flat
    rcases h_flat with ⟨l, hl_in, h_ch_in⟩
    rw [List.mem_map] at hl_in
    rcases hl_in with ⟨⟨i, m⟩, hm_in, hl_eq⟩
    dsimp at hl_eq
    have hm_mem : m ∈ (listEnum p.coeffs.toList |>.filter (fun (_, c) => c ≠ 0) |>.map (fun (d, c) => monomialToChars d c)).reverse := mem_of_mem_listEnum _ _ _ hm_in
    rw [List.mem_reverse, List.mem_map] at hm_mem
    rcases hm_mem with ⟨⟨d, c⟩, _, hm_eq⟩

    have h_mono : ∀ ch_m ∈ m, ch_m = 'x' ∨ ch_m = '*' ∨ ch_m = '^' ∨ ('0'.toNat ≤ ch_m.toNat ∧ ch_m.toNat ≤ '9'.toNat) := by
      intro ch_m hch_m
      rw [←hm_eq] at hch_m
      exact mem_monomialToChars_zmod_only_valid d c ch_m hch_m

    split_ifs at hl_eq with hi0
    · rw [←hl_eq] at h_ch_in
      have hv := h_mono ch h_ch_in
      rcases hv with rfl | hr
      · exact Or.inl rfl
      · rcases hr with rfl | hr2
        · exact Or.inr (Or.inr (Or.inl rfl))
        · rcases hr2 with rfl | hr3
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hr3)))
    · cases h_match : m with
      | nil =>
        rw [h_match] at hl_eq
        split at hl_eq
        · rename_i _ h_match_dash
          contradiction
        · rw [←hl_eq] at h_ch_in
          have h_ch_eq : ch = '+' := List.mem_singleton.mp h_ch_in
          subst h_ch_eq
          exact Or.inr (Or.inl rfl)
      | cons m_head m_tail =>
        have h_dash : m_head ≠ '-' := by
          intro hc
          have h_in : '-' ∈ m := by rw [h_match, hc]; exact List.Mem.head _
          have h_mono_dash := h_mono '-' h_in
          revert h_mono_dash
          decide
        rw [h_match] at hl_eq
        split at hl_eq
        · rename_i _ h_match_dash
          injection h_match_dash with h_eq
          exact False.elim (h_dash h_eq)
        · rw [←hl_eq] at h_ch_in
          rcases (List.mem_cons.mp h_ch_in) with rfl | hk
          · exact Or.inr (Or.inl rfl)
          · have h_in_m : ch ∈ m := by rw [h_match]; exact hk
            have hv := h_mono ch h_in_m
            rcases hv with rfl | hr
            · exact Or.inl rfl
            · rcases hr with rfl | hr2
              · exact Or.inr (Or.inr (Or.inl rfl))
              · rcases hr2 with rfl | hr3
                · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                · exact Or.inr (Or.inr (Or.inr (Or.inr hr3)))


/-! ### No `+` or `-` in ℕ/ZMod monomial chars -/

/-- Natural-number monomials contain no `+`. -/
lemma not_mem_plus_monomialToChars_nat (d : ℕ) (c : ℕ) : '+' ∉ monomialToChars d c := by
  intro h
  have hv := mem_monomialToChars_nat_only_valid d c '+' h
  rcases hv with h | h | h | ⟨h1, h2⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd (And.intro h1 h2) (by decide)

/-- Natural-number monomials contain no `-`. -/
lemma not_mem_minus_monomialToChars_nat (d : ℕ) (c : ℕ) : '-' ∉ monomialToChars d c := by
  intro h
  have hv := mem_monomialToChars_nat_only_valid d c '-' h
  rcases hv with h | h | h | ⟨h1, h2⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd (And.intro h1 h2) (by decide)

/-- ZMod monomials contain no `+`. -/
lemma not_mem_plus_monomialToChars_zmod {n : ℕ} [NeZero n] (d : ℕ) (c : ZMod n) :
    '+' ∉ monomialToChars d c := by
  intro h
  have hv := mem_monomialToChars_zmod_only_valid d c '+' h
  rcases hv with h | h | h | ⟨h1, h2⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd (And.intro h1 h2) (by decide)

/-- ZMod monomials contain no `-`. -/
lemma not_mem_minus_monomialToChars_zmod {n : ℕ} [NeZero n] (d : ℕ) (c : ZMod n) :
    '-' ∉ monomialToChars d c := by
  intro h
  have hv := mem_monomialToChars_zmod_only_valid d c '-' h
  rcases hv with h | h | h | ⟨h1, h2⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd (And.intro h1 h2) (by decide)





/-! ### `listEnum` and `listToPoly` auxiliary lemmas -/

/-- The first components of `listEnum.aux acc n l` are acc-reversed followed by shifted range. -/
private lemma listEnum_aux_map_fst {α} (n : ℕ) (acc : List (ℕ × α)) (l : List α) :
    (listEnum.aux acc n l).map Prod.fst =
      acc.reverse.map Prod.fst ++ (List.range l.length).map (· + n) := by
  induction l generalizing n acc with
  | nil => simp [listEnum.aux]
  | cons a as ih =>
    simp only [List.length_cons, listEnum.aux, ih, List.reverse_cons, List.map_append,
      List.map_cons, List.append_assoc, List.range_succ_eq_map, List.map_map, Nat.zero_add,
      List.map_nil, List.cons_append, List.nil_append]
    congr 1; congr 1
    apply List.map_congr_left
    intro x _
    simp [Function.comp]; omega

/-- The first components of `listEnum l` are exactly `List.range l.length`. -/
lemma listEnum_map_fst {α} (l : List α) :
    (listEnum l).map Prod.fst = List.range l.length := by
  simp [listEnum, listEnum_aux_map_fst]

/-- The first components of `listEnum l` have no duplicates. -/
lemma listEnum_no_dup_fst {α} (l : List α) :
    ((listEnum l).map Prod.fst).Nodup := by
  rw [listEnum_map_fst]; exact List.nodup_range

/-- Filtering a `listEnum` preserves the no-duplicates property on first components. -/
lemma listEnum_filter_no_dup_fst {R} [Semiring R] [DecidableEq R] (l : List R)
    (p : (ℕ × R) → Bool) :
    (((listEnum l).filter p).map Prod.fst).Nodup := by
  apply List.Sublist.nodup _ (listEnum_no_dup_fst l)
  exact List.Sublist.map _ (List.filter_sublist)

/-! ### No duplicate exponents in the nonzero indexed pairs -/

/-- A `Nodup` list is its own eraseDups. -/
private lemma Nodup_eraseDups_eq {α} [BEq α] [LawfulBEq α] {l : List α} (h : l.Nodup) :
    l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha : a ∉ as := (List.nodup_cons.mp h).1
    have has : as.Nodup := (List.nodup_cons.mp h).2
    rw [List.eraseDups_cons]
    have hfilt : as.filter (fun b => !b == a) = as := by
      apply List.filter_eq_self.mpr
      intro x hx
      have hne : x ≠ a := fun h => ha (h ▸ hx)
      rw [beq_eq_false_iff_ne.mpr hne, Bool.not_false]
    rw [hfilt, ih has]

/-- The exponents of the nonzero indexed pairs from a polynomial's coefficients are distinct. -/
lemma hasDuplicateExponents_false_of_listEnum {R} [Semiring R] [DecidableEq R] (p : DensePoly R) :
    hasDuplicateExponents ((listEnum p.coeffs.toList).filter (fun dc => decide (dc.2 ≠ 0))) = false := by
  simp only [hasDuplicateExponents]
  have hnd := listEnum_filter_no_dup_fst p.coeffs.toList (fun dc => decide (dc.2 ≠ 0))
  have : (listEnum p.coeffs.toList).filter (fun dc => decide (dc.2 ≠ 0)) =
         (listEnum p.coeffs.toList).filter (fun dc => !decide (dc.2 = 0)) := by
    congr 1; ext ⟨d, c⟩; simp [decide_not]
  rw [this] at hnd ⊢
  rw [Nodup_eraseDups_eq hnd]
  simp




/-! ### `listToPoly` round-trip -/

/-- `listEnum.aux acc n l = acc.reverse ++ ((List.range l.length).map (· + n)).zip l`. -/
private lemma listEnum_aux_eq {α} (n : ℕ) (acc : List (ℕ × α)) (l : List α) :
    listEnum.aux acc n l = acc.reverse ++ ((List.range l.length).map (· + n)).zip l := by
  induction l generalizing n acc with
  | nil => simp [listEnum.aux]
  | cons a as ih =>
    rw [listEnum.aux, ih (n + 1) ((n, a) :: acc)]
    simp only [List.reverse_cons, List.length_cons, List.range_succ_eq_map, List.append_assoc]
    simp only [List.zip_cons_cons, List.map_cons, List.map_map]
    -- Need: acc.rev ++ (n,a) :: map f r.zip as = acc.rev ++ (n,a) :: map g r.zip as
    simp only [List.singleton_append, Nat.zero_add, List.zip_map_left]
    congr 1  -- strip acc.reverse ++
    congr 1  -- strip (n, a) ::
    apply List.map_congr_left
    intro ⟨x, b⟩ _; simp [Function.comp, Prod.map]; omega

/-- `listEnum l = (List.range l.length).zip l`. -/
private lemma listEnum_eq_range_zip {α} (l : List α) :
    listEnum l = (List.range l.length).zip l := by
  simp [listEnum, listEnum_aux_eq]

/-- `(List.range n).zip l |>.find? (fst = i) = some (i, l[i])` when `i < n` and `i < l.length`. -/
private lemma range_zip_find_eq_some {α} (n : ℕ) (l : List α) (i : ℕ)
    (hin : i < n) (hil : i < l.length) :
    ((List.range n).zip l).find? (fun dc => decide (dc.1 = i)) = some (i, l[i]) := by
  induction n generalizing l i with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ_eq_map]
    match l with
    | [] => simp at hil
    | a :: as =>
      simp only [List.zip_cons_cons, List.find?_cons] at *
      cases i with
      | zero => rfl
      | succ j =>
        have hjm : j < m := Nat.lt_of_succ_lt_succ hin
        have hjas : j < as.length := Nat.lt_of_succ_lt_succ hil
        rw [List.zip_map_left, List.find?_map]
        -- After rw [zip_map_left, find?_map], goal is a match on decide(0 = j+1).
        -- Since 0 ≠ j+1, the match always takes the false branch.
        have h0ne : decide (0 = j + 1) = false := by simp
        simp only [h0ne]
        -- Rewrite: (f ∘ Prod.map succ id) = (fun dc => decide (succ dc.1 = succ j))
        rw [show (fun dc : ℕ × α => decide (dc.1 = j + 1)) ∘ Prod.map Nat.succ id =
                 fun dc : ℕ × α => decide (dc.1.succ = j + 1) from by rfl]
        rw [show (fun dc : ℕ × α => decide (dc.1.succ = j + 1)) =
                 (fun dc : ℕ × α => decide (dc.1 = j)) from by
          ext ⟨d, c⟩; simp]
        rw [ih as j hjm hjas]
        simp

/-- `(listEnum l).find? (fun dc => decide (dc.1 = i)) = some (i, l[i])` when `i < l.length`. -/
private lemma listEnum_find_eq_some {α} (l : List α) (i : ℕ) (hi : i < l.length) :
    (listEnum l).find? (fun dc => decide (dc.1 = i)) = some (i, l[i]) := by
  rw [listEnum_eq_range_zip]
  exact range_zip_find_eq_some l.length l i hi hi


/-- For the filtered `listEnum`, the coeff lookup at `i` gives `l[i]`. -/
private lemma listEnum_filtered_coeff {R} [Semiring R] [DecidableEq R] (l : List R) (i : ℕ)
    (hi : i < l.length) :
    (match (((listEnum l).filter (fun dc => decide (dc.2 ≠ 0))).find? (fun dc => decide (dc.1 = i))) with
     | some (_, c) => c | none => (0 : R)) = l[i] := by
  -- Convert the filter+find? to a single find? on listEnum l
  -- The predicate is: a.2 ≠ 0 ∧ a.1 = i
  -- Let p := fun a : ℕ × R => decide (a.2 ≠ 0) && decide (a.1 = i)
  -- find? q (filter p' l) = find? (fun a => p' a && q a) l  [by find?_filter]
  -- After simplification, the predicate becomes decide(decide(a.2≠0)=true ∧ decide(a.1=i)=true)
  -- which equals decide(a.2≠0) && decide(a.1=i)
  -- Step 1: normalize the goal to use p directly
  -- The goal LHS is: find? (dc.1=i) (filter (dc.2≠0) listEnum l)
  -- which by find?_filter equals: find? (dc.2≠0 && dc.1=i) (listEnum l)
  -- Convert to a clean form using show:
  suffices h : (listEnum l).find? (fun a => decide (a.2 ≠ 0) && decide (a.1 = i)) =
    (if l[i] = 0 then none else some (i, l[i])) by
    have heq_filter : ((listEnum l).filter (fun dc => decide (dc.2 ≠ 0))).find?
        (fun dc => decide (dc.1 = i)) =
        (listEnum l).find? (fun a => decide (a.2 ≠ 0) && decide (a.1 = i)) := by
      simp [List.find?_filter, Bool.and_comm]
    rw [heq_filter, h]
    split_ifs with h0 <;> simp [h0]
  -- Now prove the cleaner form: find? (a.2≠0 && a.1=i) (listEnum l) = if l[i]=0 then none else some (i, l[i])
  -- Use the decomposition from listEnum_find_eq_some
  have hdec := listEnum_find_eq_some l i hi
  rw [List.find?_eq_some_iff_append] at hdec
  obtain ⟨_, as, bs, heq, hbefore⟩ := hdec
  -- hbefore: ∀ a ∈ as, !decide(a.1 = i) = true, i.e., decide(a.1=i) = false
  -- Step 2: show find? p as = none
  have has_none : as.find? (fun a => decide (a.2 ≠ 0) && decide (a.1 = i)) = none := by
    rw [List.find?_eq_none]
    intro a hmem_as
    simp only [Bool.and_eq_false_iff, Bool.not_eq_true]
    right
    have := hbefore a hmem_as
    simpa using this
  -- Step 3: show find? p bs = none (all b.1 ≠ i in bs since listEnum has unique fst)
  have hbs_none : bs.find? (fun a => decide (a.2 ≠ 0) && decide (a.1 = i)) = none := by
    rw [List.find?_eq_none]
    intro b hmem_b
    simp only [Bool.and_eq_false_iff, Bool.not_eq_true]
    right
    rw [decide_eq_false_iff_not]
    -- i only appears once in listEnum, so b.1 ≠ i
    intro hbi
    have hnodup : List.Nodup ((listEnum l).map Prod.fst) := by
      rw [listEnum_map_fst]; exact List.nodup_range
    rw [heq, List.map_append, List.map_cons] at hnodup
    -- hnodup : Nodup (as.map fst ++ [i, ...] ++ bs.map fst) forms a Pairwise ≠
    -- i appears in both position of (i, l[i]) and b (since b.1 = i = hbi)
    have hmem_i_bs : i ∈ bs.map Prod.fst := by
      rw [List.mem_map]; exact ⟨b, hmem_b, hbi⟩
    have hi_notin_bs : i ∉ bs.map Prod.fst := by
      simp only [List.Nodup, List.pairwise_append, List.pairwise_cons] at hnodup
      -- hnodup.2.1.1 : ∀ a' ∈ bs.map fst, i ≠ a'
      intro hmem_i
      exact absurd rfl (hnodup.2.1.1 i hmem_i)
    exact hi_notin_bs hmem_i_bs
  -- Step 4: compute find? p (as ++ (i, l[i]) :: bs)
  rw [heq, List.find?_append, has_none, Option.none_or, List.find?_cons]
  -- Now: if (decide(l[i]≠0) && decide(i=i)) then some(i,l[i]) else find? p bs
  simp only [hbs_none]
  split_ifs with h0
  · simp [h0]
  · simp [h0]

/-- The `listMax` foldl is monotone in the initial accumulator. -/
private lemma listMax_foldl_mono (acc acc' : ℕ) (l : List ℕ) (h : acc ≤ acc') :
    List.foldl (fun mv x => if x > mv then x else mv) acc l ≤
    List.foldl (fun mv x => if x > mv then x else mv) acc' l := by
  induction l generalizing acc acc' with
  | nil => simp; exact h
  | cons a as ih =>
    simp only [List.foldl_cons]
    apply ih
    split_ifs with h1 h2
    · omega
    · omega
    · omega
    · exact h

/-- The foldl accumulator is ≤ the foldl result. -/
private lemma listMax_le_foldl (acc : ℕ) (l : List ℕ) :
    acc ≤ List.foldl (fun mv x => if x > mv then x else mv) acc l := by
  induction l generalizing acc with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons]
    calc acc ≤ List.foldl (fun mv x => if x > mv then x else mv) acc as := ih acc
      _ ≤ List.foldl (fun mv x => if x > mv then x else mv)
              (if a > acc then a else acc) as := by
          apply listMax_foldl_mono
          split_ifs <;> omega

/-- Any element of a list is ≤ the listMax of that list. -/
private lemma listMax_mem_le (l : List ℕ) (n : ℕ) (hn : n ∈ l) : n ≤ listMax l := by
  simp only [listMax]
  induction l with
  | nil => simp at hn
  | cons a as ih =>
    simp only [List.foldl_cons, List.mem_cons] at *
    rcases hn with rfl | hn'
    · -- n: n ≤ foldl max (if n > 0 then n else 0) as
      calc n ≤ (if n > 0 then n else 0) := by split_ifs <;> omega
        _ ≤ _ := listMax_le_foldl _ _
    · -- n ∈ as
      calc n ≤ List.foldl (fun mv x => if x > mv then x else mv) 0 as := ih hn'
        _ ≤ _ := by
          apply listMax_foldl_mono
          split_ifs <;> omega

/-- When all list elements are ≤ the accumulator, foldl max stays at the accumulator. -/
private lemma listMax_foldl_const (m : ℕ) (as : List ℕ) (h : ∀ x ∈ as, x ≤ m) :
    List.foldl (fun mv x => if x > mv then x else mv) m as = m := by
  induction as with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.mem_cons] at *
    have hb := h b (Or.inl rfl)
    have hbs := fun x hx => h x (Or.inr hx)
    have hstep : (if b > m then b else m) = m := by split_ifs <;> omega
    rw [hstep]; exact ih hbs

/-- listMax is ≤ any upper bound on the list. -/
private lemma listMax_le_of_forall (l : List ℕ) (m : ℕ) (h : ∀ n ∈ l, n ≤ m) :
    listMax l ≤ m := by
  simp only [listMax]
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.mem_cons] at *
    have ha := h a (Or.inl rfl)
    calc List.foldl (fun mv x => if x > mv then x else mv) (if a > 0 then a else 0) as
        ≤ List.foldl (fun mv x => if x > mv then x else mv) m as := by
          apply listMax_foldl_mono; split_ifs <;> omega
      _ = m := listMax_foldl_const m as (fun n hn => h n (Or.inr hn))

/-- The max of the indices of a filtered `listEnum` of a nonempty list with nonzero last element
    is `l.length - 1`. -/
private lemma listMax_listEnum_filter_eq {R} [Semiring R] [DecidableEq R] (l : List R) (hl : l ≠ [])
    (hlast : l.getLast? ≠ some 0) :
    listMax ((listEnum l).filter (fun dc => decide (dc.2 ≠ 0)) |>.map Prod.fst) = l.length - 1 := by
  set filtIdx := (listEnum l).filter (fun dc => decide (dc.2 ≠ 0)) |>.map Prod.fst
  -- Step 1: Upper bound — all filtered indices < l.length, hence ≤ l.length - 1
  have hub : ∀ k ∈ filtIdx, k ≤ l.length - 1 := by
    intro k hk
    simp only [filtIdx, List.mem_map, List.mem_filter] at hk
    obtain ⟨⟨d, c⟩, ⟨hmem, _⟩, rfl⟩ := hk
    -- d ∈ (listEnum l).map Prod.fst = range l.length
    have hd : d ∈ List.range l.length := by
      rw [← listEnum_map_fst]
      exact List.mem_map.mpr ⟨(d, c), hmem, rfl⟩
    rw [List.mem_range] at hd
    omega
  -- Step 2: Lower bound — l.length - 1 ∈ filtIdx (since last elt ≠ 0)
  have hlen : 0 < l.length := List.length_pos_of_ne_nil hl
  have hlb : l.length - 1 ∈ filtIdx := by
    simp only [filtIdx, List.mem_map, List.mem_filter]
    have hi : l.length - 1 < l.length := Nat.sub_lt hlen Nat.one_pos
    refine ⟨⟨l.length - 1, l[l.length - 1]⟩, ⟨?_, ?_⟩, rfl⟩
    · -- (l.length-1, l[l.length-1]) ∈ listEnum l
      exact List.mem_of_find?_eq_some (listEnum_find_eq_some l (l.length - 1) hi)
    · -- l[l.length-1] ≠ 0
      simp only [decide_eq_true_eq, ne_eq]
      intro h0
      apply hlast
      -- hlast: l.getLast? ≠ some 0. Show l.getLast? = some l[l.length-1] = some 0
      rw [List.getLast?_eq_some_getLast hl]
      congr 1
      rw [List.getLast_eq_getElem]
      exact h0
  -- Conclusion: listMax filtIdx = l.length - 1
  apply Nat.le_antisymm
  · exact listMax_le_of_forall filtIdx (l.length - 1) hub
  · exact listMax_mem_le filtIdx (l.length - 1) hlb


/-- Normalizing the coefficient array of an already-valid DensePoly is an identity. -/
private lemma normalize_idem {R} [Semiring R] [DecidableEq R] (p : DensePoly R) :
    normalize p.coeffs = p := by
  apply DensePoly.ext
  simp only [normalize]
  rw [← Array.toList_inj]
  rw [toList_popWhile_eq_dropTrailingZeros]
  simp only [dropTrailingZeros]
  by_cases hempty : p.coeffs.toList = []
  · simp [hempty]
  · obtain ⟨init, last, hrfl⟩ : ∃ xs x, p.coeffs.toList = xs ++ [x] :=
      ⟨p.coeffs.toList.dropLast, p.coeffs.toList.getLast hempty,
       (List.dropLast_append_getLast hempty).symm⟩
    have hlast_ne : last ≠ 0 := by
      have hback := p.last_ne_zero
      have hpl : p.coeffs = init.toArray.push last := by
        apply Array.toList_inj.mp
        simp [hrfl]
      rw [hpl, Array.back?_push] at hback
      intro h; exact hback (congrArg some h)
    simp only [hrfl, List.reverse_append, List.reverse_singleton]
    simp only [List.singleton_append]
    rw [List.dropWhile_cons_of_neg (by simpa)]
    simp

/-- `listToPoly` of the indexed nonzero coefficients of `p` equals `p` itself. -/
lemma listToPoly_indexed_nonzero {R} [Semiring R] [DecidableEq R] (p : DensePoly R) :
    listToPoly ((listEnum p.coeffs.toList).filter (fun dc => decide (dc.2 ≠ 0))) = p := by
  by_cases hzero : p.coeffs = #[]
  · -- Case p = 0: listEnum [] = [], listToPoly [] = 0 = p
    have hp : p = 0 := DensePoly.ext (by simpa using hzero)
    subst hp
    simp [listToPoly, listEnum, listEnum.aux, DensePoly.ext_iff, normalize]
  · -- Case p ≠ 0: coeffs nonempty, use listMax_listEnum_filter_eq
    have hlne := p.last_ne_zero
    have hne : p.coeffs.toList ≠ [] := by rwa [Ne, Array.toList_eq_nil_iff]
    have hlast : p.coeffs.toList.getLast? ≠ some 0 := by
      rw [Array.getLast?_toList]; exact p.last_ne_zero
    have hsize := listMax_listEnum_filter_eq p.coeffs.toList hne hlast
    have hlen : p.coeffs.toList.length = p.coeffs.size := Array.length_toList
    have harr : ((List.range (listMax ((listEnum p.coeffs.toList).filter
        (fun dc => decide (dc.2 ≠ 0)) |>.map Prod.fst) + 1)).map (fun d =>
        match ((listEnum p.coeffs.toList).filter (fun dc => decide (dc.2 ≠ 0))).find?
          (fun dc => decide (dc.1 = d)) with
        | some (_, c) => c | none => (0 : R))).toArray = p.coeffs := by
      apply Array.ext
      · have hpos : 0 < p.coeffs.size := by rw [← hlen]; exact List.length_pos_of_ne_nil hne
        rw [List.size_toArray, List.length_map, List.length_range, hsize, hlen]; omega
      · intro n hlt1 hlt2
        rw [List.size_toArray, List.length_map, List.length_range, hsize, hlen] at hlt1
        have hlt_l : n < p.coeffs.toList.length := by omega
        rw [List.getElem_toArray, List.getElem_map, List.getElem_range]
        exact listEnum_filtered_coeff p.coeffs.toList n hlt_l
    simp only [listToPoly]
    convert normalize_idem p using 2

/-! ### Bridge lemmas for `parseDensePoly_toChars_nat` -/

-- Shorthand: the ordered nonzero (degree, coeff) pairs of p
private abbrev nzPairs (p : DensePoly ℕ) :=
  (listEnum p.coeffs.toList).filter (fun dc => decide (dc.2 ≠ 0))

-- Shorthand: their monomial string representations (low-to-high degree order)
private abbrev monoStrings (p : DensePoly ℕ) :=
  (nzPairs p).map (fun dc => monomialToChars dc.1 dc.2)

-- Helper: prepending '+' to every element and flattening gives '+' :: joinWithPlus
private lemma map_prepend_plus_flatten_eq (L : List (List Char)) (hne : L ≠ []) :
    (L.map ('+' :: ·)).flatten = '+' :: joinWithPlus L := by
  induction L with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.map_cons, List.flatten_cons]
    cases tl with
    | nil => simp [joinWithPlus]
    | cons y ys =>
      rw [ih (List.cons_ne_nil _ _), joinWithPlus_append hd (y :: ys) (List.cons_ne_nil _ _)]
      simp

-- Helper: withSigns.flatten = joinWithPlus L when no '-' in elements
-- Helper: (L.map ('+' :: ·)).flatten = '+' :: joinWithPlus L for nonempty L
private lemma map_prepend_plus_flatten_eq' (L : List (List Char)) (hne : L ≠ []) :
    (L.map ('+' :: ·)).flatten = '+' :: joinWithPlus L := by
  induction L with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.map_cons, List.flatten_cons]
    cases tl with
    | nil => simp [joinWithPlus]
    | cons y ys =>
      rw [ih (List.cons_ne_nil _ _), joinWithPlus_append hd (y :: ys) (List.cons_ne_nil _ _)]
      simp

-- General indexed auxiliary: withSigns transform with index offset n
private lemma withSigns_aux (n : ℕ) : ∀ (L : List (List Char)),
    (∀ m ∈ L, '-' ∉ m) →
    ((((List.range L.length).map (· + n)).zip L).map (fun (i, m) =>
        if i = 0 then m
        else match m with | '-' :: _ => m | _ => '+' :: m)).flatten =
    if n = 0 then joinWithPlus L else (L.map ('+' :: ·)).flatten := by
  intro L
  induction L generalizing n with
  | nil => simp [joinWithPlus]
  | cons hd tl ih =>
    intro hno
    have hno_hd : '-' ∉ hd := hno hd (List.Mem.head tl)
    have ih_n1 := ih (n + 1) (fun m hm => hno m (List.Mem.tail hd hm))
    simp only [Nat.succ_ne_zero, ite_false] at ih_n1
    simp only [List.length_cons, List.range_succ_eq_map, List.map_map, List.map_cons,
               List.zip_cons_cons, List.flatten_cons]
    rw [Nat.zero_add]
    -- Rewrite the tail using ih_n1
    rw [show List.map ((fun x => x + n) ∘ Nat.succ) (List.range tl.length) =
          List.map (fun x => x + (n + 1)) (List.range tl.length) from
            List.map_congr_left (fun x _ => by simp [Function.comp]; omega)]
    rw [ih_n1]
    cases n with
    | zero =>
      simp only [ite_true]
      cases tl with
      | nil => simp [joinWithPlus]
      | cons y ys =>
        rw [map_prepend_plus_flatten_eq' (y :: ys) (List.cons_ne_nil _ _),
            joinWithPlus_append hd (y :: ys) (List.cons_ne_nil _ _)]
    | succ n' =>
      simp only [Nat.succ_ne_zero, ite_false]
      rcases hd with _ | ⟨c, cs⟩
      · simp
      · have hc : c ≠ '-' := fun heq => absurd (heq ▸ List.Mem.head cs) hno_hd
        simp [hc]

-- Main: withSigns.flatten = joinWithPlus when no '-' in elements
private lemma withSigns_flatten_eq_joinWithPlus
    (L : List (List Char)) (hno_minus : ∀ m ∈ L, '-' ∉ m) :
    ((listEnum L).map (fun (i, m) =>
        if i = 0 then m
        else match m with | '-' :: _ => m | _ => '+' :: m)).flatten =
    joinWithPlus L := by
  have key := withSigns_aux 0 L hno_minus
  simp only [ite_true] at key
  simp only [listEnum, listEnum_aux_eq 0 [] L, List.reverse_nil, List.nil_append] at *
  exact key

/-- For a non-zero ℕ-polynomial, `(toChars p).toList = joinWithPlus (monoStrings p).reverse`.
Since ℕ coefficients produce no `-`, the `withSigns` step is exactly `joinWithPlus`. -/
lemma toChars_toList_nat_ne_zero (p : DensePoly ℕ) (hp : p ≠ 0) :
    (toChars p).toList = joinWithPlus (monoStrings p).reverse := by
  simp only [toChars, monoStrings, nzPairs, if_neg hp, String.toList_ofList]
  apply withSigns_flatten_eq_joinWithPlus
  intro m hm
  simp only [List.mem_reverse, List.mem_map] at hm
  obtain ⟨⟨d, c⟩, _, rfl⟩ := hm
  exact not_mem_minus_monomialToChars_nat d c

/-- Splitting `(toChars p).toList` on `+`/`-` recovers the reversed monomial strings. -/
lemma splitPolynomialChars_toChars_nat (p : DensePoly ℕ) (hp : p ≠ 0) :
    splitPolynomialChars (toChars p).toList = (monoStrings p).reverse := by
  rw [toChars_toList_nat_ne_zero p hp]
  apply splitPolynomialChars_flatten_plus
  -- No `+` in any nat monomial string
  · intro x hx
    simp only [monoStrings, nzPairs, List.mem_reverse, List.mem_map] at hx
    obtain ⟨⟨d, c⟩, hmem, rfl⟩ := hx
    exact not_mem_plus_monomialToChars_nat d c
  -- No `-` in any nat monomial string
  · intro x hx
    simp only [monoStrings, nzPairs, List.mem_reverse, List.mem_map] at hx
    obtain ⟨⟨d, c⟩, hmem, rfl⟩ := hx
    exact not_mem_minus_monomialToChars_nat d c
  -- All monomial strings are nonempty
  · intro x hx
    simp only [monoStrings, nzPairs, List.mem_reverse, List.mem_map] at hx
    obtain ⟨⟨d, c⟩, hmem, rfl⟩ := hx
    exact monomialToChars_nat_ne_nil d c
  -- The list of monomial strings is nonempty (p ≠ 0 means there is at least one nonzero coeff)
  · -- (monoStrings p).reverse ≠ [] because p ≠ 0 has at least one nonzero coefficient
    have h_back : p.coeffs.back? ≠ none := by
      intro h_none
      have hp2 : p.coeffs = #[] := Array.back?_eq_none_iff.mp h_none
      have hpe : p.coeffs = (0 : DensePoly ℕ).coeffs := by rw [coeffs_zero, hp2]
      exact hp (DensePoly.ext hpe)
    have h_back2 : ∃ c, p.coeffs.back? = some c := by
      rcases Option.ne_none_iff_exists.mp h_back with ⟨c, hc_eq⟩
      exact ⟨c, hc_eq.symm⟩
    rcases h_back2 with ⟨c, hc_eq⟩
    have hc_nz : c ≠ 0 := by
      intro hz; rw [hz] at hc_eq; exact p.last_ne_zero hc_eq
    have hc_in : c ∈ p.coeffs.toList := mem_toList_of_back?_eq_some _ _ hc_eq
    have hd_nz : (listEnum p.coeffs.toList).filter (fun (_, c) => c ≠ 0) ≠ [] :=
      filter_nonZero_ne_nil p.coeffs.toList ⟨c, hc_in, hc_nz⟩
    exact reverse_ne_nil_of_ne_nil _
      (map_ne_nil_of_ne_nil _ _ hd_nz)

/-- Parsing each monomial string succeeds: the `parsedParts` list has no `none` entries. -/
lemma parsedParts_allSome_nat (p : DensePoly ℕ) (_ : p ≠ 0) :
    ((monoStrings p).reverse.map (fun cs => parseMonomial (R := ℕ) cs)).all
      (fun x => x.isSome) = true := by
  simp only [List.all_eq_true, List.mem_map, List.mem_reverse]
  intro x hx
  obtain ⟨cs, hcs_mem, rfl⟩ := hx
  simp only [nzPairs] at hcs_mem
  obtain ⟨⟨d, c⟩, hmem, rfl⟩ := hcs_mem
  have hc_nz : c ≠ 0 := by
    have := List.mem_filter.mp hmem
    exact of_decide_eq_true this.2
  simp [parse_monomialToChars_ne_zero_nat d c hc_nz]

/-- `filterMap id` of a list of `some` values recovers those values. -/
-- (Standard; may follow from List.filterMap_id_map_some or similar.)
lemma filterMap_id_map_some {α} (l : List α) :
    (l.map some).filterMap id = l := by
  simp [List.filterMap_map]

/-- `find?` by first component is invariant under reversal when first components are unique. -/
private lemma find?_reverse_of_nodup_fst {R} (l : List (ℕ × R))
    (hnd : (l.map Prod.fst).Nodup) (d : ℕ) :
    l.reverse.find? (fun dc => decide (dc.1 = d)) =
    l.find? (fun dc => decide (dc.1 = d)) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hk_not_mem, hnd_tl⟩ := hnd
    simp only [List.reverse_cons, List.find?_append, List.find?_cons]
    rw [ih hnd_tl]
    by_cases hdk : hd.1 = d
    · simp only [hdk, decide_true]
      have hk_none : tl.find? (fun dc => decide (dc.1 = d)) = none := by
        rw [List.find?_eq_none]
        intro a hm
        simp only [decide_eq_true_eq]
        intro heq
        apply hk_not_mem
        exact List.mem_map.mpr ⟨a, hm, heq ▸ hdk ▸ rfl⟩
      simp [hk_none]
    · simp [hdk]

/-- `listMax` (as foldl max 0) is invariant under reversal, using antisymmetry. -/
private lemma listMax_nat_reverse (l : List ℕ) :
    listMax l.reverse = listMax l := by
  apply Nat.le_antisymm
  · apply listMax_le_of_forall
    intro n hn
    rw [List.mem_reverse] at hn
    exact listMax_mem_le l n hn
  · apply listMax_le_of_forall
    intro n hn
    exact listMax_mem_le l.reverse n (List.mem_reverse.mpr hn)

/-- `listToPoly` is invariant under reversing its input when first components are unique.
    This holds for any coefficient type `R` with `DecidableEq`. -/
lemma listToPoly_reverse_eq {R} [DecidableEq R] [Semiring R] (l : List (ℕ × R))
    (hnd : (l.map Prod.fst).Nodup) :
    listToPoly l.reverse = listToPoly l := by
  simp only [listToPoly]
  have hmap : l.reverse.map Prod.fst = (l.map Prod.fst).reverse := by simp
  have hmax : listMax (l.reverse.map Prod.fst) = listMax (l.map Prod.fst) := by
    rw [hmap, listMax_nat_reverse]
  simp only [hmap, listMax_nat_reverse]
  congr 1; congr 1
  apply List.map_congr_left
  intro k _
  rw [find?_reverse_of_nodup_fst l hnd k]

/-- Alias for `listToPoly_reverse_eq` specialized to `ℕ`. -/
lemma listToPoly_reverse_eq_nat (l : List (ℕ × ℕ))
    (hnd : (l.map Prod.fst).Nodup) :
    listToPoly l.reverse = listToPoly l :=
  listToPoly_reverse_eq l hnd

/-! ### Bridge lemmas for `parseDensePoly_toChars_zmod` -/

-- Shorthand: the ordered nonzero (degree, coeff) pairs of a ZMod polynomial
private abbrev nzPairs_zmod {n : ℕ} [NeZero n] (p : DensePoly (ZMod n)) :=
  (listEnum p.coeffs.toList).filter (fun dc => decide (dc.2 ≠ 0))

-- Shorthand: their monomial string representations (low-to-high degree order)
private abbrev monoStrings_zmod {n : ℕ} [NeZero n] (p : DensePoly (ZMod n)) :=
  (nzPairs_zmod p).map (fun dc => monomialToChars dc.1 dc.2)

/-- For a non-zero ZMod-polynomial, `(toChars p).toList = joinWithPlus (monoStrings_zmod p).reverse`.
Since ZMod coefficients produce no `-`, the `withSigns` step is exactly `joinWithPlus`. -/
private lemma toChars_toList_zmod_ne_zero {n : ℕ} [NeZero n]
    (p : DensePoly (ZMod n)) (hp : p ≠ 0) :
    (toChars p).toList = joinWithPlus (monoStrings_zmod p).reverse := by
  simp only [toChars, monoStrings_zmod, nzPairs_zmod, if_neg hp, String.toList_ofList]
  apply withSigns_flatten_eq_joinWithPlus
  intro m hm
  simp only [List.mem_reverse, List.mem_map] at hm
  obtain ⟨⟨d, c⟩, _, rfl⟩ := hm
  exact not_mem_minus_monomialToChars_zmod d c

/-- Splitting `(toChars p).toList` on `+`/`-` recovers the reversed ZMod monomial strings. -/
lemma splitPolynomialChars_toChars_zmod {n : ℕ} [NeZero n]
    (p : DensePoly (ZMod n)) (hp : p ≠ 0) :
    splitPolynomialChars (toChars p).toList = (monoStrings_zmod p).reverse := by
  rw [toChars_toList_zmod_ne_zero p hp]
  apply splitPolynomialChars_flatten_plus
  -- No `+` in any ZMod monomial string
  · intro x hx
    simp only [monoStrings_zmod, nzPairs_zmod, List.mem_reverse, List.mem_map] at hx
    obtain ⟨⟨d, c⟩, _, rfl⟩ := hx
    exact not_mem_plus_monomialToChars_zmod d c
  -- No `-` in any ZMod monomial string
  · intro x hx
    simp only [monoStrings_zmod, nzPairs_zmod, List.mem_reverse, List.mem_map] at hx
    obtain ⟨⟨d, c⟩, _, rfl⟩ := hx
    exact not_mem_minus_monomialToChars_zmod d c
  -- All monomial strings are nonempty
  · intro x hx
    simp only [monoStrings_zmod, nzPairs_zmod, List.mem_reverse, List.mem_map] at hx
    obtain ⟨⟨d, c⟩, _, rfl⟩ := hx
    exact monomialToChars_zmod_ne_nil d c
  -- The list of monomial strings is nonempty (p ≠ 0 means there is at least one nonzero coeff)
  · have h_back : p.coeffs.back? ≠ none := by
      intro h_none
      have hp2 : p.coeffs = #[] := Array.back?_eq_none_iff.mp h_none
      have hpe : p.coeffs = (0 : DensePoly (ZMod n)).coeffs := by rw [coeffs_zero, hp2]
      exact hp (DensePoly.ext hpe)
    have h_back2 : ∃ c, p.coeffs.back? = some c :=
      Option.ne_none_iff_exists.mp h_back |>.imp fun c hc => hc.symm
    rcases h_back2 with ⟨c, hc_eq⟩
    have hc_nz : c ≠ 0 := fun hz => p.last_ne_zero (hz ▸ hc_eq)
    have hc_in : c ∈ p.coeffs.toList := mem_toList_of_back?_eq_some _ _ hc_eq
    have hd_nz : (listEnum p.coeffs.toList).filter (fun (_, c) => c ≠ 0) ≠ [] :=
      filter_nonZero_ne_nil p.coeffs.toList ⟨c, hc_in, hc_nz⟩
    exact reverse_ne_nil_of_ne_nil _ (map_ne_nil_of_ne_nil _ _ hd_nz)

/-- Parsing each ZMod monomial string succeeds. -/
lemma parsedParts_allSome_zmod {n : ℕ} [NeZero n]
    (p : DensePoly (ZMod n)) (_ : p ≠ 0) :
    ((monoStrings_zmod p).reverse.map (fun cs => parseMonomial (R := ZMod n) cs)).all
      (fun x => x.isSome) = true := by
  simp only [List.all_eq_true, List.mem_map, List.mem_reverse]
  intro x hx
  obtain ⟨cs, hcs_mem, rfl⟩ := hx
  simp only [nzPairs_zmod] at hcs_mem
  obtain ⟨⟨d, c⟩, hmem, rfl⟩ := hcs_mem
  have hc_nz : c ≠ 0 := of_decide_eq_true (List.mem_filter.mp hmem).2
  simp [parse_monomialToChars_ne_zero_zmod d c hc_nz]

/-! ### Main round-trip theorem -/

/-- **Main theorem**: parsing the string form of a ℕ-polynomial gives back the original. -/
theorem parseDensePoly_toChars_nat (p : DensePoly ℕ) :
    parseDensePoly (toChars p) = some p := by
  by_cases hp : p = 0
  · -- Case p = 0: toChars 0 = "0", parseDensePoly "0" = some 0 ✓
    subst hp
    simp [parseDensePoly, toChars]
  · -- Case p ≠ 0
    -- Show toChars p ≠ "0" (the string "0" would require toList to start with '0', but it doesn't)
    have hne : toChars p ≠ "0" := by
      intro h
      have hbad := toChars_nat_not_start_zero_of_ne_zero p hp []
      simp only [h, String.toList] at hbad
      exact hbad rfl
    -- Unfold parseDensePoly step by step
    simp only [parseDensePoly, if_neg hne]
    -- parts = splitPolynomialChars (toChars p).toList = (monoStrings p).reverse
    have hparts : splitPolynomialChars (toChars p).toList = (monoStrings p).reverse :=
      splitPolynomialChars_toChars_nat p hp
    rw [hparts]
    -- parsedParts: each monomial string parses to some (d, c)
    have hparsed_some : (monoStrings p).reverse.map (fun cs => parseMonomial (R := ℕ) cs) =
        (nzPairs p).reverse.map (fun dc => some dc) := by
      simp only [monoStrings, List.map_reverse]
      apply congrArg List.reverse
      rw [List.map_map]
      apply List.map_congr_left
      intro x hmem
      obtain ⟨d, c⟩ := x
      simp only [Function.comp]
      have hc_nz : c ≠ 0 := of_decide_eq_true (List.mem_filter.mp hmem).2
      exact parse_monomialToChars_ne_zero_nat d c hc_nz
    rw [hparsed_some]
    -- No None entries: all parsedParts are some, so any isNone = false
    have hno_none : ((nzPairs p).reverse.map (fun dc => some dc)).any (fun x => x.isNone) = false := by
      simp
    rw [if_neg (by rw [hno_none]; decide)]
    -- unwrapped = (nzPairs p).reverse
    rw [filterMap_id_map_some]
    -- hasDuplicateExponents (nzPairs p).reverse = false
    have hnodup_fst : ((nzPairs p).map Prod.fst).Nodup := by
      simp only [nzPairs]
      apply List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist)
      have key : ∀ (n : ℕ) (acc : List (ℕ × ℕ)) (l : List ℕ),
          (listEnum.aux acc n l).map Prod.fst =
          (acc.map Prod.fst).reverse ++ List.range' n l.length := by
        intro n acc l
        induction l generalizing n acc with
        | nil => simp [listEnum.aux]
        | cons a as ih =>
          simp only [listEnum.aux, ih (n+1) ((n, a) :: acc)]
          simp [List.range'_succ, List.append_assoc]
      simp only [listEnum]
      rw [key 0 []]
      simp
      exact List.nodup_range'
    have hnodup_rev : ((nzPairs p).reverse.map Prod.fst).Nodup := by
      rwa [List.map_reverse, List.nodup_reverse]
    have hno_dup : hasDuplicateExponents (nzPairs p).reverse = false := by
      simp only [hasDuplicateExponents, Bool.eq_false_iff, ne_eq, decide_eq_true_eq]
      intro hlen
      exact absurd (Nodup_eraseDups_eq hnodup_rev ▸ hlen) (fun h => h rfl)
    simp only [hno_dup, Bool.false_eq_true, if_false]
    -- listToPoly (nzPairs p).reverse = p
    congr 1
    rw [listToPoly_reverse_eq_nat (nzPairs p) hnodup_fst]
    exact listToPoly_indexed_nonzero p

/-- **Main theorem**: parsing the string form of a ZMod-polynomial gives back the original. -/
theorem parseDensePoly_toChars_zmod {n : ℕ} [NeZero n] (p : DensePoly (ZMod n)) :
    parseDensePoly (toChars p) = some p := by
  by_cases hp : p = 0
  · subst hp; simp [parseDensePoly, toChars]
  · -- Show toChars p ≠ "0"
    have hne : toChars p ≠ "0" := by
      intro h
      have hbad := toChars_zmod_not_start_zero_of_ne_zero p hp []
      simp only [h, String.toList] at hbad
      exact hbad rfl
    simp only [parseDensePoly, if_neg hne]
    -- splitPolynomialChars gives (monoStrings_zmod p).reverse
    have hparts : splitPolynomialChars (toChars p).toList = (monoStrings_zmod p).reverse :=
      splitPolynomialChars_toChars_zmod p hp
    rw [hparts]
    -- Each monomial string parses to some (d, c)
    have hparsed_some : (monoStrings_zmod p).reverse.map (fun cs => parseMonomial (R := ZMod n) cs) =
        (nzPairs_zmod p).reverse.map (fun dc => some dc) := by
      simp only [monoStrings_zmod, List.map_reverse]
      apply congrArg List.reverse
      rw [List.map_map]
      apply List.map_congr_left
      intro x hmem
      obtain ⟨d, c⟩ := x
      simp only [Function.comp]
      have hc_nz : c ≠ 0 := of_decide_eq_true (List.mem_filter.mp hmem).2
      exact parse_monomialToChars_ne_zero_zmod d c hc_nz
    rw [hparsed_some]
    -- No None entries
    have hno_none : ((nzPairs_zmod p).reverse.map (fun dc => some dc)).any (fun x => x.isNone) = false := by
      simp
    rw [if_neg (by rw [hno_none]; decide)]
    -- filterMap id recovers the list
    rw [filterMap_id_map_some]
    -- No duplicate exponents
    have hnodup_fst : ((nzPairs_zmod p).map Prod.fst).Nodup := by
      simp only [nzPairs_zmod]
      apply List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist)
      have key : ∀ (m : ℕ) (acc : List (ℕ × ZMod n)) (l : List (ZMod n)),
          (listEnum.aux acc m l).map Prod.fst =
          (acc.map Prod.fst).reverse ++ List.range' m l.length := by
        intro m acc l
        induction l generalizing m acc with
        | nil => simp [listEnum.aux]
        | cons a as ih =>
          simp only [listEnum.aux, ih (m+1) ((m, a) :: acc)]
          simp [List.range'_succ, List.append_assoc]
      simp only [listEnum]
      rw [key 0 []]
      simp
      exact List.nodup_range'
    have hnodup_rev : ((nzPairs_zmod p).reverse.map Prod.fst).Nodup := by
      rwa [List.map_reverse, List.nodup_reverse]
    have hno_dup : hasDuplicateExponents (nzPairs_zmod p).reverse = false := by
      simp only [hasDuplicateExponents, Bool.eq_false_iff, ne_eq, decide_eq_true_eq]
      intro hlen
      exact absurd (Nodup_eraseDups_eq hnodup_rev ▸ hlen) (fun h => h rfl)
    rw [if_neg (by rw [hno_dup]; decide)]
    -- listToPoly (nzPairs_zmod p).reverse = p
    congr 1
    rw [listToPoly_reverse_eq (nzPairs_zmod p) hnodup_fst]
    exact listToPoly_indexed_nonzero p

/-! ### Bridge lemmas for `parseDensePoly_toChars_int` -/

-- Shorthand: the ordered nonzero (degree, coeff) pairs of an ℤ polynomial
private abbrev nzPairs_int (p : DensePoly ℤ) :=
  (listEnum p.coeffs.toList).filter (fun dc => decide (dc.2 ≠ 0))

-- Shorthand: their monomial string representations (low-to-high degree order)
private abbrev monoStrings_int (p : DensePoly ℤ) :=
  (nzPairs_int p).map (fun dc => monomialToChars dc.1 dc.2)

/-- ℤ monomials contain no `+`. Follows from `mem_monomialToChars_int_only_valid`. -/
lemma not_mem_plus_monomialToChars_int (d : ℕ) (c : ℤ) : '+' ∉ monomialToChars d c := by
  intro h
  have hv := mem_monomialToChars_int_only_valid d c '+' h
  rcases hv with h | h | h | h | hdig <;> simp_all [Char.toNat]

/-- The `-` sign in an ℤ monomial can only appear at position 0, never in the tail.
    This ensures `splitPolynomialChars` won't accidentally split inside a monomial. -/
lemma not_mem_tail_monomialToChars_int (d : ℕ) (c : ℤ) : '-' ∉ (monomialToChars d c).drop 1 :=
  not_mem_tail_monomialToChars d c

/-- Core splitting lemma for `toChars` of ℤ-polynomials.
    Unlike the ℕ/ZMod case, some elements of `L` may start with `-` (negative coefficients).
    `withSigns` handles these by *not* prepending `+` (the leading `-` itself acts as separator).
    `splitPolynomialChars` correctly recovers `L` when:
    - No element contains `+` internally
    - `-` only appears at position 0 of each element (never in the tail)
    - All elements are non-empty -/
-- Helper: no '+' and '-' only at position 0 -> single element parsing from empty current
private lemma spca_npmtm
    (cs : List Char) (hp : '+' ∉ cs) (hm : '-' ∉ cs.drop 1)
    (acc : List (List Char)) :
    splitPolynomialCharsAux acc [] cs = cs :: acc := by
  induction cs generalizing acc with
  | nil => simp [splitPolynomialCharsAux]
  | cons c rest ih =>
    have hp' : '+' ∉ rest := fun h => hp (List.Mem.tail c h)
    have hm_rest : '-' ∉ rest := by simpa [List.drop] using hm
    by_cases hcm : c = '-'
    · subst hcm; simp only [splitPolynomialCharsAux, ite_true]
      rw [splitPolynomialCharsAux_no_plus_minus rest hp' hm_rest acc ['-']]; simp
    · have hm_full : '-' ∉ c :: rest :=
        fun h => (List.mem_cons.mp h).elim (fun e => hcm e.symm) hm_rest
      rw [splitPolynomialCharsAux_no_plus_minus (c :: rest) hp hm_full acc []]; simp

-- Helper: split at a '+' or '-' separator from empty current, '-' only at pos 0 in cs1
-- Helper: cur non-empty + rest has no '+'/'-' means hitting '-' commits cur.reverse ++ rest
private lemma spca_asep_minus_aux (cs2 : List Char)
    (rest : List Char) (hp' : '+' ∉ rest) (hm' : '-' ∉ rest) :
    ∀ (acc : List (List Char)) (cur : List Char) (_hcne : cur ≠ []),
    splitPolynomialCharsAux acc cur (rest ++ '-' :: cs2) =
    splitPolynomialCharsAux ((cur.reverse ++ rest) :: acc) [] ('-' :: cs2) := by
  induction rest with
  | nil =>
    intro acc cur hcne
    simp only [List.nil_append, List.append_nil]
    simp only [splitPolynomialCharsAux, hcne, ↓reduceIte]
  | cons d ds ih =>
    intro acc cur hcne
    have hdp : d ≠ '+' := fun h => hp' (h ▸ List.Mem.head ds)
    have hdm : d ≠ '-' := fun h => hm' (h ▸ List.Mem.head ds)
    simp only [List.cons_append, splitPolynomialCharsAux]
    rw [ih (fun h => hp' (List.Mem.tail d h)) (fun h => hm' (List.Mem.tail d h))
          acc (d :: cur) (List.cons_ne_nil d cur)]
    simp [splitPolynomialCharsAux]

private lemma spca_asep_minus_head (cs2 : List Char)
    (rest : List Char) (hp' : '+' ∉ rest) (hm' : '-' ∉ rest) (acc : List (List Char)) :
    splitPolynomialCharsAux acc ['-'] (rest ++ '-' :: cs2) =
    splitPolynomialCharsAux (('-' :: rest) :: acc) [] ('-' :: cs2) :=
  spca_asep_minus_aux cs2 rest hp' hm' acc ['-'] (List.cons_ne_nil '-' [])

private lemma spca_asep_minus_inner (c : Char) (cs2 : List Char) (_hcm : c ≠ '-')
    (rest : List Char) (hp' : '+' ∉ rest) (hm' : '-' ∉ rest) (acc : List (List Char)) :
    splitPolynomialCharsAux acc [c] (rest ++ '-' :: cs2) =
    splitPolynomialCharsAux ((c :: rest) :: acc) [] ('-' :: cs2) :=
  spca_asep_minus_aux cs2 rest hp' hm' acc [c] (List.cons_ne_nil c [])

private lemma spca_asep
    (cs1 cs2 : List Char) (hp : '+' ∉ cs1) (hm : '-' ∉ cs1.drop 1)
    (hcs1 : cs1 ≠ []) (acc : List (List Char)) (sep : Char) (hsep : sep = '+' ∨ sep = '-') :
    splitPolynomialCharsAux acc [] (cs1 ++ sep :: cs2) =
    splitPolynomialCharsAux (cs1 :: acc) [] (if sep = '-' then sep :: cs2 else cs2) := by
  rcases cs1 with _ | ⟨c, rest⟩
  · exact absurd rfl hcs1
  · have hcp : c ≠ '+' := fun h => hp (h ▸ List.Mem.head rest)
    have hp' : '+' ∉ rest := fun h => hp (List.Mem.tail c h)
    have hm' : '-' ∉ rest := by simpa [List.drop] using hm
    rcases hsep with rfl | rfl
    · simp only [if_neg (by decide : '+' ≠ '-'), List.cons_append]
      by_cases hcm : c = '-'
      · subst hcm
        simp only [splitPolynomialCharsAux, ite_true]
        rw [splitPolynomialCharsAux_append_plus rest cs2 hp' hm' acc ['-']]; simp
      · simp only [splitPolynomialCharsAux]
        rw [splitPolynomialCharsAux_append_plus rest cs2 hp' hm' acc [c]]; simp
    · simp only [ite_true, List.cons_append]
      by_cases hcm : c = '-'
      · subst hcm
        simp only [splitPolynomialCharsAux, ite_true]
        exact spca_asep_minus_head cs2 rest hp' hm' acc
      · simp only [splitPolynomialCharsAux]
        exact spca_asep_minus_inner c cs2 hcm rest hp' hm' acc


-- Helper: (listEnum (x :: xs)).map withSigns = x ++ (xs.map body).flatten
private lemma withSigns_flat_cons_i (x : List Char) (xs : List (List Char)) :
    ((listEnum (x :: xs)).map fun (i, m) =>
        if i = 0 then m else match m with | '-' :: _ => m | _ => '+' :: m).flatten =
    x ++ (xs.map fun m => match m with | '-' :: _ => m | _ => '+' :: m).flatten := by
  simp only [listEnum, listEnum_aux_eq 0 [] (x :: xs), List.reverse_nil, List.nil_append,
             List.length_cons, List.range_succ_eq_map, List.map_map, List.map_cons,
             List.zip_cons_cons, Nat.zero_add, ite_true, List.flatten_cons]
  congr 1
  have key : ∀ (ys : List (List Char)) (k : ℕ),
    List.map (fun x => if x.1 = 0 then x.2 else match x.2 with | '-' :: _ => x.2 | _ => '+' :: x.2)
      ((List.map (fun x => x + (k+1)) (List.range ys.length)).zip ys) =
    List.map (fun m => match m with | '-' :: _ => m | _ => '+' :: m) ys := by
    intro ys k
    induction ys generalizing k with
    | nil => simp
    | cons y ys ih =>
      simp only [List.length_cons, List.range_succ_eq_map, List.map_map, List.map_cons,
                 List.zip_cons_cons]
      congr 1
      rw [show (fun x => x + (k + 1)) ∘ Nat.succ = fun x => x + (k + 1 + 1) from by ext; simp; omega]
      exact ih (k + 1)
  rw [show (fun x : ℕ => x + 0) ∘ Nat.succ = fun x => x + (0 + 1) from by ext; simp]
  exact congrArg List.flatten (key xs 0)

-- Helper: process all elements (each gets a separator prepended)
/-- After `spca_asep` strips the separator, the remaining input is
    `y ++ (ys.map withSigns).flatten` where `y` is raw (no prefix). -/
private lemma spca_wsb_head
    (y : List Char) (ys : List (List Char))
    (hp : ∀ m ∈ y :: ys, '+' ∉ m) (hm : ∀ m ∈ y :: ys, '-' ∉ m.drop 1)
    (hne : ∀ m ∈ y :: ys, m ≠ [])
    (acc : List (List Char)) :
    splitPolynomialCharsAux acc []
      (y ++ (ys.map (fun m => match m with | '-' :: _ => m | _ => '+' :: m)).flatten) =
    (y :: ys).reverse ++ acc := by
  induction ys generalizing y acc with
  | nil =>
    simp only [List.map_nil, List.flatten_nil, List.append_nil]
    have hyp : '+' ∉ y := hp y List.mem_cons_self
    have hym : '-' ∉ y.drop 1 := hm y List.mem_cons_self
    rw [spca_npmtm y hyp hym acc]; simp
  | cons z zs ih =>
    have hyp : '+' ∉ y := hp y List.mem_cons_self
    have hym : '-' ∉ y.drop 1 := hm y List.mem_cons_self
    have hyne : y ≠ [] := hne y List.mem_cons_self
    have hzp : ∀ m ∈ z :: zs, '+' ∉ m := fun m h => hp m (List.mem_cons_of_mem _ h)
    have hzm : ∀ m ∈ z :: zs, '-' ∉ m.drop 1 := fun m h => hm m (List.mem_cons_of_mem _ h)
    have hzne : ∀ m ∈ z :: zs, m ≠ [] := fun m h => hne m (List.mem_cons_of_mem _ h)
    rcases hz : z with _ | ⟨zc, zcs⟩
    · exact absurd (hzne z List.mem_cons_self) (hz ▸ by simp)
    · by_cases hzc : zc = '-'
      · -- z starts with '-', match preserves it, separator is '-'
        subst hzc
        simp only [List.map_cons, List.flatten_cons,
                   List.cons_append]
        rw [spca_asep y _ hyp hym hyne acc '-' (Or.inr rfl)]
        simp only [ite_true]
        -- After spca_asep with '-': remaining = '-' :: zcs ++ REST = z ++ REST
        -- ih z expects: splitPolynomialCharsAux (y :: acc) [] (z ++ (zs.map ...).flatten)
        -- but goal has '-' :: (zcs ++ ...). Substitute z = '-' :: zcs back.
        rw [← List.cons_append, show ('-' :: zcs : List Char) = z from hz.symm]
        rw [ih z hzp hzm hzne (y :: acc)]
        simp [hz]
      · -- z doesn't start with '-', match prepends '+', separator is '+'
        have hmatch_z : (match (zc :: zcs : List Char) with | '-' :: _ => zc :: zcs | _ => '+' :: zc :: zcs) = '+' :: zc :: zcs := by
          split <;> simp_all
        simp only [List.map_cons, hmatch_z, List.flatten_cons]
        -- Reassociate: y ++ ('+' :: zc :: zcs) ++ REST = y ++ '+' :: (zc :: zcs ++ REST)
        rw [show y ++ ('+' :: zc :: zcs ++ (zs.map fun m => match m with | '-' :: _ => m | _ => '+' :: m).flatten) =
            y ++ ('+' :: ((zc :: zcs) ++ (zs.map fun m => match m with | '-' :: _ => m | _ => '+' :: m).flatten)) from by
          simp [List.cons_append]]
        rw [spca_asep y _ hyp hym hyne acc '+' (Or.inl rfl)]
        simp only [show ('+' : Char) ≠ '-' from by decide, if_false]
        -- After spca_asep with '+': remaining = zc :: zcs ++ REST = z ++ REST (no '+')
        rw [show (zc :: zcs : List Char) = z from hz.symm]
        rw [ih z hzp hzm hzne (y :: acc)]
        simp [hz]


private lemma splitPolynomialChars_withSigns (L : List (List Char))
    (hne : L ≠ [])
    (hno_plus : ∀ m ∈ L, '+' ∉ m)
    (hno_tail_minus : ∀ m ∈ L, '-' ∉ m.drop 1)
    (hne_elem : ∀ m ∈ L, m ≠ []) :
    splitPolynomialChars
      (((listEnum L).map (fun (i, m) =>
          if i = 0 then m
          else match m with | '-' :: _ => m | _ => '+' :: m)).flatten) = L := by
  rw [splitPolynomialChars_eq]
  cases L with
  | nil => contradiction
  | cons x xs =>
    have hxne : x ≠ [] := hne_elem x List.mem_cons_self
    rw [withSigns_flat_cons_i x xs]
    have hflat_ne : x ++ (xs.map fun m => match m with | '-' :: _ => m | _ => '+' :: m).flatten ≠ [] :=
      by simp [hxne]
    rw [if_neg hflat_ne]
    have hxp := hno_plus x List.mem_cons_self
    have hxm := hno_tail_minus x List.mem_cons_self
    have hxsp : ∀ m ∈ xs, '+' ∉ m := fun m h => hno_plus m (List.mem_cons_of_mem _ h)
    have hxsm : ∀ m ∈ xs, '-' ∉ m.drop 1 := fun m h => hno_tail_minus m (List.mem_cons_of_mem _ h)
    have hxsne : ∀ m ∈ xs, m ≠ [] := fun m h => hne_elem m (List.mem_cons_of_mem _ h)
    cases hxs : xs with
    | nil =>
      simp only [List.map_nil, List.flatten_nil, List.append_nil]
      rw [spca_npmtm x hxp hxm []]; simp
    | cons y ys =>
      have hxs_ne : xs ≠ [] := hxs ▸ List.cons_ne_nil _ _
      rcases hy : y with _ | ⟨yc, ycs⟩
      · exact absurd (hxsne y (hxs ▸ List.mem_cons_self)) (hy ▸ by simp)
      · by_cases hyc : yc = '-'
        · subst hyc
          simp only [List.map_cons, List.flatten_cons,
                     List.cons_append]
          rw [spca_asep x _ hxp hxm hxne [] '-' (Or.inr rfl)]
          simp only [ite_true]
          rw [← List.cons_append, show ('-' :: ycs : List Char) = y from hy.symm]
          rw [spca_wsb_head y ys (hxs ▸ hxsp) (hxs ▸ hxsm) (hxs ▸ hxsne) [x]]; simp
        · simp only [List.map_cons,
                     show (match (yc :: ycs : List Char) with | '-' :: _ => yc :: ycs | _ => '+' :: yc :: ycs) = '+' :: yc :: ycs from by simp [show ¬(yc = '-') from hyc],
                     List.flatten_cons]
          rw [show x ++ ('+' :: yc :: ycs ++ (ys.map fun m => match m with | '-' :: _ => m | _ => '+' :: m).flatten) =
              x ++ ('+' :: ((yc :: ycs) ++ (ys.map fun m => match m with | '-' :: _ => m | _ => '+' :: m).flatten)) from by simp [List.cons_append]]
          rw [spca_asep x _ hxp hxm hxne [] '+' (Or.inl rfl)]
          simp only [show ('+' : Char) ≠ '-' from by decide, if_false]
          rw [show (yc :: ycs : List Char) = y from hy.symm]
          rw [spca_wsb_head y ys (hxs ▸ hxsp) (hxs ▸ hxsm) (hxs ▸ hxsne) [x]]; simp


/-- For a non-zero ℤ-polynomial, `(toChars p).toList` equals the `withSigns` flattening
    of `(monoStrings_int p).reverse`. -/
private lemma toChars_toList_int_ne_zero (p : DensePoly ℤ) (hp : p ≠ 0) :
    (toChars p).toList = ((listEnum (monoStrings_int p).reverse).map (fun (i, m) =>
        if i = 0 then m
        else match m with | '-' :: _ => m | _ => '+' :: m)).flatten := by
  simp only [toChars, monoStrings_int, nzPairs_int, if_neg hp, String.toList_ofList]
  rfl

/-- Splitting `(toChars p).toList` on `+`/`-` recovers the reversed ℤ monomial strings. -/
lemma splitPolynomialChars_toChars_int (p : DensePoly ℤ) (hp : p ≠ 0) :
    splitPolynomialChars (toChars p).toList = (monoStrings_int p).reverse := by
  rw [toChars_toList_int_ne_zero p hp]
  apply splitPolynomialChars_withSigns
  -- (monoStrings_int p).reverse ≠ []
  · intro h
    apply hp; clear hp
    have h1 : nzPairs_int p = [] := by
      have : monoStrings_int p = [] := by simpa [List.reverse_eq_nil_iff] using h
      simpa [monoStrings_int, List.map_eq_nil_iff] using this
    have hcoeffs : ∀ (i : ℕ) (hi : i < p.coeffs.size), (p.coeffs[i]'hi) = 0 := by
      intro i hi
      by_contra hc
      have hmem : (p.coeffs[i]'hi) ∈ p.coeffs.toList := by
        apply List.getElem_mem
      obtain ⟨j, hj⟩ := mem_listEnum p.coeffs.toList (p.coeffs[i]'hi) hmem
      have hfilt : (j, (p.coeffs[i]'hi)) ∈
          (listEnum p.coeffs.toList).filter (fun dc => decide (dc.2 ≠ 0)) :=
        List.mem_filter.mpr ⟨hj, by simp [hc]⟩
      simp only [nzPairs_int] at h1
      rw [h1] at hfilt
      simp at hfilt
    have hempty : p.coeffs = #[] := by
      by_contra hne
      have hsize : 0 < p.coeffs.size := by
        by_contra hlt; push_neg at hlt
        exact hne (Array.eq_empty_of_size_eq_zero (by omega))
      have hlast := hcoeffs (p.coeffs.size - 1) (by omega)
      have hback : p.coeffs.back? = some 0 := by
        unfold Array.back?
        simp [show p.coeffs.size - 1 < p.coeffs.size from by omega, hlast]
      exact p.last_ne_zero hback
    exact DensePoly.ext hempty
  -- No `+` in any ℤ monomial string
  · intro x hx
    simp only [List.mem_reverse, List.mem_map] at hx
    obtain ⟨⟨d, c⟩, _, rfl⟩ := hx
    exact not_mem_plus_monomialToChars_int d c
  -- `-` only at position 0 of each ℤ monomial string
  · intro x hx
    simp only [List.mem_reverse, List.mem_map] at hx
    obtain ⟨⟨d, c⟩, _, rfl⟩ := hx
    exact not_mem_tail_monomialToChars_int d c
  -- All ℤ monomial strings are nonempty
  · intro x hx
    simp only [List.mem_reverse, List.mem_map] at hx
    obtain ⟨⟨d, c⟩, _, rfl⟩ := hx
    exact monomialToChars_int_ne_nil d c

/-- Parsing each ℤ monomial string succeeds. -/
lemma parsedParts_allSome_int (p : DensePoly ℤ) (_ : p ≠ 0) :
    ((monoStrings_int p).reverse.map (fun cs => parseMonomial (R := ℤ) cs)).all
      (fun x => x.isSome) = true := by
  simp only [List.all_eq_true, List.mem_map, List.mem_reverse]
  intro x hx
  obtain ⟨cs, hcs_mem, rfl⟩ := hx
  simp only [nzPairs_int] at hcs_mem
  obtain ⟨⟨d, c⟩, hmem, rfl⟩ := hcs_mem
  have hc_nz : c ≠ 0 := of_decide_eq_true (List.mem_filter.mp hmem).2
  simp [parse_monomialToChars_ne_zero_int d c hc_nz]

/-- **Main theorem**: parsing the string form of an ℤ-polynomial gives back the original. -/
theorem parseDensePoly_toChars_int (p : DensePoly ℤ) :
    parseDensePoly (toChars p) = some p := by
  by_cases hp : p = 0
  · subst hp; simp [parseDensePoly, toChars]
  · have hne : toChars p ≠ "0" := by
      intro h
      have hbad := toChars_int_not_start_zero_of_ne_zero p hp []
      simp only [h, String.toList] at hbad
      exact hbad rfl
    simp only [parseDensePoly, if_neg hne]
    have hparts : splitPolynomialChars (toChars p).toList = (monoStrings_int p).reverse :=
      splitPolynomialChars_toChars_int p hp
    rw [hparts]
    have hparsed_some : (monoStrings_int p).reverse.map (fun cs => parseMonomial (R := ℤ) cs) =
        (nzPairs_int p).reverse.map (fun dc => some dc) := by
      simp only [monoStrings_int, List.map_reverse]
      apply congrArg List.reverse
      rw [List.map_map]
      apply List.map_congr_left
      intro x hmem
      obtain ⟨d, c⟩ := x
      simp only [Function.comp]
      have hc_nz : c ≠ 0 := of_decide_eq_true (List.mem_filter.mp hmem).2
      exact parse_monomialToChars_ne_zero_int d c hc_nz
    rw [hparsed_some]
    have hno_none : ((nzPairs_int p).reverse.map (fun dc => some dc)).any (fun x => x.isNone) = false := by
      simp
    rw [if_neg (by rw [hno_none]; decide)]
    rw [filterMap_id_map_some]
    have hnodup_fst : ((nzPairs_int p).map Prod.fst).Nodup := by
      simp only [nzPairs_int]
      apply List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist)
      have key : ∀ (m : ℕ) (acc : List (ℕ × ℤ)) (l : List ℤ),
          (listEnum.aux acc m l).map Prod.fst =
          (acc.map Prod.fst).reverse ++ List.range' m l.length := by
        intro m acc l
        induction l generalizing m acc with
        | nil => simp [listEnum.aux]
        | cons a as ih =>
          simp only [listEnum.aux, ih (m+1) ((m, a) :: acc)]
          simp [List.range'_succ, List.append_assoc]
      simp only [listEnum]
      rw [key 0 []]
      simp
      exact List.nodup_range'
    have hnodup_rev : ((nzPairs_int p).reverse.map Prod.fst).Nodup := by
      rwa [List.map_reverse, List.nodup_reverse]
    have hno_dup : hasDuplicateExponents (nzPairs_int p).reverse = false := by
      simp only [hasDuplicateExponents, Bool.eq_false_iff, ne_eq, decide_eq_true_eq]
      intro hlen
      exact absurd (Nodup_eraseDups_eq hnodup_rev ▸ hlen) (fun h => h rfl)
    rw [if_neg (by rw [hno_dup]; decide)]
    congr 1
    rw [listToPoly_reverse_eq (nzPairs_int p) hnodup_fst]
    exact listToPoly_indexed_nonzero p

end Azurite.DensePoly
