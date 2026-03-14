import Azurite.DensePoly.ToString
import Azurite.DensePoly.Parse
import Mathlib.Data.String.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

namespace Azurite.DensePoly

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

lemma splitOnP_go_cons_false (x : Char) (xs acc : List Char) (h : (x == '/') = false) :
  List.splitOnP.go (fun c => c == '/') (x :: xs) acc = List.splitOnP.go (fun c => c == '/') xs (x :: acc) := by
  dsimp [List.splitOnP.go]
  split
  · rename_i h_eq
    rw [h] at h_eq
    contradiction
  · rfl

lemma splitOnP_go_cons_true (xs acc : List Char) :
  List.splitOnP.go (fun c => c == '/') ('/' :: xs) acc = acc.reverse :: List.splitOnP.go (fun c => c == '/') xs [] := by
  rfl

lemma splitOnP_go_not_mem (l acc : List Char) (h : '/' ∉ l) :
  List.splitOnP.go (fun c => c == '/') l acc = [acc.reverse ++ l] := by
  induction l generalizing acc with
  | nil =>
    have h_nil : acc.reverse ++ [] = acc.reverse := List.append_nil _
    rw [h_nil]
    rfl
  | cons x xs ih =>
    have hxq : (x == '/') = false := by
      revert h
      cases h_eq : (x == '/')
      · intro _; rfl
      · intro h
        have hx : x = '/' := eq_of_beq h_eq
        subst hx
        exact False.elim (h (List.Mem.head _))
    rw [splitOnP_go_cons_false x xs acc hxq]
    have hxs : '/' ∉ xs := by intro hc; apply h; exact List.Mem.tail _ hc
    rw [ih (x :: acc) hxs]
    have h_eq_args : ((x :: acc).reverse ++ xs) = (acc.reverse ++ x :: xs) := by
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [h_eq_args]

lemma splitOn_not_mem (l : List Char) (h : '/' ∉ l) : l.splitOn '/' = [l] := by
  unfold List.splitOn List.splitOnP
  have hgo := splitOnP_go_not_mem l [] h
  rw [hgo]
  rfl

lemma splitOnP_go_not_mem_x (l acc : List Char) (h : 'x' ∉ l) :
  List.splitOnP.go (fun c => c == 'x') l acc = [acc.reverse ++ l] := by
  induction l generalizing acc with
  | nil =>
    have h_nil : acc.reverse ++ [] = acc.reverse := List.append_nil _
    rw [h_nil]
    rfl
  | cons c cs ih =>
    have hcq : (c == 'x') = false := by
      revert h
      cases h_eq : (c == 'x')
      · intro _; rfl
      · intro h
        have hc : c = 'x' := eq_of_beq h_eq
        subst hc
        exact False.elim (h (List.Mem.head _))
    dsimp [List.splitOnP.go]
    have h_split_go : (if c == 'x' then acc.reverse :: List.splitOnP.go (fun c => c == 'x') cs [] else List.splitOnP.go (fun c => c == 'x') cs (c :: acc)) = List.splitOnP.go (fun c => c == 'x') cs (c :: acc) := by
      rw [hcq]
      rfl
    rw [h_split_go]
    have hcs : 'x' ∉ cs := by intro a; apply h; exact List.Mem.tail _ a
    rw [ih (c :: acc) hcs]
    have h_eq_args : ((c :: acc).reverse ++ cs) = (acc.reverse ++ c :: cs) := by
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [h_eq_args]

lemma splitOn_not_mem_x (l : List Char) (h : 'x' ∉ l) : l.splitOn 'x' = [l] := by
  unfold List.splitOn List.splitOnP
  have hgo := splitOnP_go_not_mem_x l [] h
  rw [hgo]
  rfl

lemma splitOnP_go_append_not_mem (l1 l2 acc : List Char) (h : '/' ∉ l1) :
  List.splitOnP.go (fun c => c == '/') (l1 ++ l2) acc =
  List.splitOnP.go (fun c => c == '/') l2 (l1.reverse ++ acc) := by
  induction l1 generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    have hxq : (x == '/') = false := by
      revert h
      cases h_eq : (x == '/')
      · intro _; rfl
      · intro h
        have hx : x = '/' := eq_of_beq h_eq
        subst hx
        have h_in : '/' ∈ '/' :: xs := List.Mem.head _
        exact False.elim (h h_in)
    have h_app : (x :: xs) ++ l2 = x :: (xs ++ l2) := rfl
    rw [h_app]
    rw [splitOnP_go_cons_false x (xs ++ l2) acc hxq]
    have hxs : '/' ∉ xs := by intro hc; apply h; exact List.Mem.tail _ hc
    rw [ih (x :: acc) hxs]
    have h_eq_args : (xs.reverse ++ x :: acc) = ((x :: xs).reverse ++ acc) := by
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [h_eq_args]

lemma splitOn_append_singleton_append_not_mem (l1 l2 : List Char) (h1 : '/' ∉ l1) (h2 : '/' ∉ l2) :
  (l1 ++ ['/'] ++ l2).splitOn '/' = [l1, l2] := by
  unfold List.splitOn List.splitOnP
  have h_app2 : l1 ++ ['/'] ++ l2 = l1 ++ ('/' :: l2) := by simp
  rw [h_app2]
  have h_go : List.splitOnP.go (fun c => c == '/') (l1 ++ '/' :: l2) [] =
              List.splitOnP.go (fun c => c == '/') ('/' :: l2) (l1.reverse ++ []) := splitOnP_go_append_not_mem l1 ('/' :: l2) [] h1
  rw [h_go]
  have h_rev_nil : l1.reverse ++ [] = l1.reverse := by simp
  rw [h_rev_nil]
  rw [splitOnP_go_cons_true l2 (l1.reverse)]
  have h_go2 : List.splitOnP.go (fun c => c == '/') l2 [] = [l2] := by
    have hg := splitOnP_go_not_mem l2 [] h2
    simp only [List.reverse_nil, List.nil_append] at hg
    exact hg
  rw [h_go2]
  simp only [List.reverse_reverse]

lemma splitOnP_go_cons_false_x (c : Char) (xs acc : List Char) (h : (c == 'x') = false) :
  List.splitOnP.go (fun ch => ch == 'x') (c :: xs) acc = List.splitOnP.go (fun ch => ch == 'x') xs (c :: acc) := by
  dsimp [List.splitOnP.go]
  split
  · rename_i h_eq
    rw [h] at h_eq
    contradiction
  · rfl

lemma splitOnP_go_cons_true_x (xs acc : List Char) :
  List.splitOnP.go (fun ch => ch == 'x') ('x' :: xs) acc = acc.reverse :: List.splitOnP.go (fun ch => ch == 'x') xs [] := by
  rfl

lemma splitOnP_go_accum_gen (cs acc : List Char) :
  List.splitOnP.go (fun ch => ch == 'x') cs acc =
  match List.splitOnP.go (fun ch => ch == 'x') cs [] with
  | [] => []
  | hd :: tail => (acc.reverse ++ hd) :: tail := by
  revert acc
  induction cs with
  | nil =>
    intro acc
    dsimp [List.splitOnP.go]
    simp
  | cons x xs ih =>
    intro acc
    dsimp [List.splitOnP.go]
    split
    · rename_i h_eq
      simp
    · rename_i h_neq
      rw [ih (x::acc), ih [x]]
      generalize h_go : List.splitOnP.go (fun ch => ch == 'x') xs [] = res
      cases res with
      | nil => rfl
      | cons hd tail =>
        dsimp
        simp [List.append_assoc]

lemma splitOnP_go_accum (c : Char) (cs hd : List Char) (tail : List (List Char)) (h : List.splitOnP.go (fun ch => ch == 'x') cs [] = hd :: tail) :
  List.splitOnP.go (fun ch => ch == 'x') cs [c] = (c :: hd) :: tail := by
  have h_gen := splitOnP_go_accum_gen cs [c]
  rw [h] at h_gen
  exact h_gen

lemma splitOnP_go_append_not_mem_x (l1 l2 acc : List Char) (h : 'x' ∉ l1) :
  List.splitOnP.go (fun c => c == 'x') (l1 ++ l2) acc =
  List.splitOnP.go (fun c => c == 'x') l2 (l1.reverse ++ acc) := by
  induction l1 generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    have hxq : (c == 'x') = false := by
      revert h
      cases h_eq : (c == 'x')
      · intro _; rfl
      · intro h
        have hc : c = 'x' := eq_of_beq h_eq
        subst hc
        have h_in : 'x' ∈ 'x' :: cs := List.Mem.head _
        exact False.elim (h h_in)
    have h_app : (c :: cs) ++ l2 = c :: (cs ++ l2) := rfl
    rw [h_app]
    rw [splitOnP_go_cons_false_x c (cs ++ l2) acc hxq]
    have hcs : 'x' ∉ cs := by intro hc; apply h; exact List.Mem.tail _ hc
    rw [ih (c :: acc) hcs]
    have h_eq_args : (cs.reverse ++ c :: acc) = ((c :: cs).reverse ++ acc) := by
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [h_eq_args]

lemma splitOn_append_singleton_append_not_mem_x (l1 l2 : List Char) (h1 : 'x' ∉ l1) (h2 : 'x' ∉ l2) :
  (l1 ++ ['x'] ++ l2).splitOn 'x' = [l1, l2] := by
  unfold List.splitOn List.splitOnP
  have h_app2 : l1 ++ ['x'] ++ l2 = l1 ++ ('x' :: l2) := by simp
  rw [h_app2]
  have h_go : List.splitOnP.go (fun c => c == 'x') (l1 ++ 'x' :: l2) [] =
              List.splitOnP.go (fun c => c == 'x') ('x' :: l2) (l1.reverse ++ []) := splitOnP_go_append_not_mem_x l1 ('x' :: l2) [] h1
  rw [h_go]
  have h_rev_nil : l1.reverse ++ [] = l1.reverse := by simp
  rw [h_rev_nil]
  rw [splitOnP_go_cons_true_x l2 (l1.reverse)]
  have h_go2 : List.splitOnP.go (fun c => c == 'x') l2 [] = [l2] := by
    have hg := splitOnP_go_not_mem_x l2 [] h2
    simp only [List.reverse_nil, List.nil_append] at hg
    exact hg
  rw [h_go2]
  simp only [List.reverse_reverse]

lemma splitOn_append_mul_x (l : List Char) (h : 'x' ∉ l) :
  (l ++ ['*', 'x']).splitOn 'x' = [l ++ ['*'], []] := by
  have h_app : l ++ ['*', 'x'] = (l ++ ['*']) ++ ['x'] ++ [] := by simp
  rw [h_app]
  apply splitOn_append_singleton_append_not_mem_x
  · intro h_in
    simp only [List.mem_append, List.mem_singleton] at h_in
    cases h_in with
    | inl h_l => exact h h_l
    | inr h_mul =>
      have hx : 'x'.toNat = 120 := rfl
      have hm : '*'.toNat = 42 := rfl
      have h_eq : 'x'.toNat = '*'.toNat := congrArg Char.toNat h_mul
      rw [hx, hm] at h_eq
      contradiction
  · intro h_in
    cases h_in

lemma splitOn_append_mul_x_pow (l d : List Char) (h : 'x' ∉ l) (hd : 'x' ∉ d) :
  (l ++ '*' :: 'x' :: '^' :: d).splitOn 'x' = [l ++ ['*'], '^' :: d] := by
  have h_app : l ++ '*' :: 'x' :: '^' :: d = (l ++ ['*']) ++ ['x'] ++ ('^' :: d) := by simp
  rw [h_app]
  apply splitOn_append_singleton_append_not_mem_x
  · intro h_in
    simp only [List.mem_append, List.mem_singleton] at h_in
    cases h_in with
    | inl h_l => exact h h_l
    | inr h_mul =>
      have hx : 'x'.toNat = 120 := rfl
      have hm : '*'.toNat = 42 := rfl
      have h_eq : 'x'.toNat = '*'.toNat := congrArg Char.toNat h_mul
      rw [hx, hm] at h_eq
      contradiction
  · intro h_in
    simp only [List.mem_cons] at h_in
    cases h_in with
    | inl h_pow =>
      have hx : 'x'.toNat = 120 := rfl
      have hm : '^'.toNat = 94 := rfl
      have h_eq : 'x'.toNat = '^'.toNat := congrArg Char.toNat h_pow
      rw [hx, hm] at h_eq
      contradiction
    | inr h_d => exact hd h_d

lemma rat_ext_eq (q : ℚ) : q = (q.num : ℚ) / (q.den : ℚ) := by
  exact (Rat.num_div_den q).symm

lemma parseRatChars_ratToChars (q : ℚ) : parseRatChars (ratToChars q) = some q := by
  unfold ratToChars
  split_ifs with hd
  · unfold parseRatChars
    rw [splitOn_not_mem (intToChars q.num) (not_mem_intToChars q.num)]
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
    rw [splitOn_append_singleton_append_not_mem (intToChars q.num) (natToChars q.den) h1 h2]
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
      rw [splitOnP_go_cons_false_x '-' cs [] h_dash]
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

lemma monomialToChars_nat_ne_nil (d : ℕ) (c : ℕ) : monomialToChars d c ≠ [] := by
  have h_toChars : DensePolyToChars.toChars c = natToChars c := rfl
  dsimp [monomialToChars]
  rw [h_toChars]
  split_ifs
  · intro h; contradiction
  · exact natToChars_ne_nil _
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; contradiction
  · intro h; contradiction
  · intro h
    have h_assoc : natToChars c ++ ['*'] ++ ['x'] = natToChars c ++ ['*', 'x'] := by simp
    rw [h_assoc] at h
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) h
  · intro h
    have h_assoc : natToChars c ++ ['*'] ++ 'x' :: '^' :: natToChars d = natToChars c ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc] at h
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) h

lemma monomialToChars_int_ne_nil (d : ℕ) (c : ℤ) : monomialToChars d c ≠ [] := by
  have h_toChars : DensePolyToChars.toChars c = intToChars c := rfl
  dsimp [monomialToChars]
  rw [h_toChars]
  split_ifs
  · intro h; contradiction
  · exact intToChars_ne_nil _
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; contradiction
  · intro h; contradiction
  · intro h
    have h_assoc : intToChars c ++ ['*'] ++ ['x'] = intToChars c ++ ['*', 'x'] := by simp
    rw [h_assoc] at h
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) h
  · intro h
    have h_assoc : intToChars c ++ ['*'] ++ 'x' :: '^' :: natToChars d = intToChars c ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc] at h
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) h

lemma monomialToChars_rat_ne_nil (d : ℕ) (c : ℚ) : monomialToChars d c ≠ [] := by
  have h_toChars : DensePolyToChars.toChars c = ratToChars c := rfl
  dsimp [monomialToChars]
  rw [h_toChars]
  split_ifs
  · intro h; contradiction
  · exact ratToChars_ne_nil _
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; contradiction
  · intro h; contradiction
  · intro h
    have h_assoc : ratToChars c ++ ['*'] ++ ['x'] = ratToChars c ++ ['*', 'x'] := by simp
    rw [h_assoc] at h
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) h
  · intro h
    have h_assoc : ratToChars c ++ ['*'] ++ 'x' :: '^' :: natToChars d = ratToChars c ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc] at h
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) h

lemma zmodToChars_not_start_zero {k : ℕ} [NeZero k] (c : ZMod k) (cs : List Char) (hc : c ≠ 0) : zmodToChars c ≠ '0' :: cs := by
  dsimp [zmodToChars]
  have hc_val : c.val ≠ 0 := by
    intro h_0
    apply hc
    have h_c : c.val = (0 : ZMod k).val := by
      rw [h_0, ZMod.val_zero]
    exact ZMod.val_injective k h_c
  exact natToChars_not_start_zero c.val cs hc_val

lemma monomialToChars_zmod_ne_nil {n : ℕ} [NeZero n] (d : ℕ) (c : ZMod n) : monomialToChars d c ≠ [] := by
  have h_toChars : DensePolyToChars.toChars c = natToChars c.val := rfl
  dsimp [monomialToChars]
  rw [h_toChars]
  split_ifs
  · intro h; contradiction
  · exact natToChars_ne_nil _
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; contradiction
  · intro h; contradiction
  · intro h
    have h_assoc : natToChars c.val ++ ['*'] ++ ['x'] = natToChars c.val ++ ['*', 'x'] := by simp
    rw [h_assoc] at h
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) h
  · intro h
    have h_assoc : natToChars c.val ++ ['*'] ++ 'x' :: '^' :: natToChars d = natToChars c.val ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc] at h
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) h

lemma append_not_start_char {α : Type _} (l1 l2 : List α) (c : α) (h_nil : l1 ≠ []) (h_start : ∀ cs, l1 ≠ c :: cs) :
  ∀ cs, l1 ++ l2 ≠ c :: cs := by
  intro cs h
  cases l1
  · contradiction
  · rename_i head tail
    have h_eq : (head :: tail) ++ l2 = head :: (tail ++ l2) := rfl
    rw [h_eq] at h
    have h_head : head = c := by injection h
    subst h_head
    exact h_start tail rfl

lemma monomialToChars_nat_not_start_zero (d : ℕ) (c : ℕ) (cs : List Char) (hc : c ≠ 0) : monomialToChars d c ≠ '0' :: cs := by
  have h_toChars : DensePolyToChars.toChars c = natToChars c := rfl
  dsimp [monomialToChars]
  rw [h_toChars]
  split_ifs
  · intro h; contradiction
  · exact natToChars_not_start_zero c cs hc
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; revert h; simp
  · have h_assoc : natToChars c ++ ['*'] ++ ['x'] = natToChars c ++ ['*', 'x'] := by simp
    rw [h_assoc]
    exact append_not_start_char (natToChars c) ['*', 'x'] '0' (natToChars_ne_nil c) (fun cs => natToChars_not_start_zero c cs hc) cs
  · have h_assoc : natToChars c ++ ['*'] ++ 'x' :: '^' :: natToChars d = natToChars c ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc]
    exact append_not_start_char (natToChars c) ('*' :: 'x' :: '^' :: natToChars d) '0' (natToChars_ne_nil c) (fun cs => natToChars_not_start_zero c cs hc) cs

lemma monomialToChars_int_not_start_zero (d : ℕ) (c : ℤ) (cs : List Char) (hc : c ≠ 0) : monomialToChars d c ≠ '0' :: cs := by
  have h_toChars : DensePolyToChars.toChars c = intToChars c := rfl
  dsimp [monomialToChars]
  rw [h_toChars]
  split_ifs
  · intro h; contradiction
  · exact intToChars_not_start_zero c cs hc
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; revert h; simp
  · have h_assoc : intToChars c ++ ['*'] ++ ['x'] = intToChars c ++ ['*', 'x'] := by simp
    rw [h_assoc]
    exact append_not_start_char (intToChars c) ['*', 'x'] '0' (intToChars_ne_nil c) (fun cs => intToChars_not_start_zero c cs hc) cs
  · have h_assoc : intToChars c ++ ['*'] ++ 'x' :: '^' :: natToChars d = intToChars c ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc]
    exact append_not_start_char (intToChars c) ('*' :: 'x' :: '^' :: natToChars d) '0' (intToChars_ne_nil c) (fun cs => intToChars_not_start_zero c cs hc) cs

lemma monomialToChars_rat_not_start_zero (d : ℕ) (c : ℚ) (cs : List Char) (hc : c ≠ 0) : monomialToChars d c ≠ '0' :: cs := by
  have h_toChars : DensePolyToChars.toChars c = ratToChars c := rfl
  dsimp [monomialToChars]
  rw [h_toChars]
  split_ifs
  · intro h; contradiction
  · exact ratToChars_not_start_zero c cs hc
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; revert h; simp
  · have h_assoc : ratToChars c ++ ['*'] ++ ['x'] = ratToChars c ++ ['*', 'x'] := by simp
    rw [h_assoc]
    exact append_not_start_char (ratToChars c) ['*', 'x'] '0' (ratToChars_ne_nil c) (fun cs => ratToChars_not_start_zero c cs hc) cs
  · have h_assoc : ratToChars c ++ ['*'] ++ 'x' :: '^' :: natToChars d = ratToChars c ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc]
    exact append_not_start_char (ratToChars c) ('*' :: 'x' :: '^' :: natToChars d) '0' (ratToChars_ne_nil c) (fun cs => ratToChars_not_start_zero c cs hc) cs

lemma monomialToChars_zmod_not_start_zero {n : ℕ} [NeZero n] (d : ℕ) (c : ZMod n) (cs : List Char) (hc : c ≠ 0) : monomialToChars d c ≠ '0' :: cs := by
  have h_toChars : DensePolyToChars.toChars c = natToChars c.val := rfl
  dsimp [monomialToChars]
  rw [h_toChars]
  split_ifs
  · intro h; contradiction
  · have hc_val : c.val ≠ 0 := by
      intro h_0
      apply hc
      have h_c : c.val = (0 : ZMod n).val := by
        rw [h_0, ZMod.val_zero]
      exact ZMod.val_injective n h_c
    exact natToChars_not_start_zero c.val cs hc_val
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; revert h; simp
  · intro h; revert h; simp
  · have h_assoc : natToChars c.val ++ ['*'] ++ ['x'] = natToChars c.val ++ ['*', 'x'] := by simp
    rw [h_assoc]
    have hc_val : c.val ≠ 0 := by
      intro h_0
      apply hc
      have h_c : c.val = (0 : ZMod n).val := by
        rw [h_0, ZMod.val_zero]
      exact ZMod.val_injective n h_c
    exact append_not_start_char (natToChars c.val) ['*', 'x'] '0' (natToChars_ne_nil c.val) (fun cs => natToChars_not_start_zero c.val cs hc_val) cs
  · have h_assoc : natToChars c.val ++ ['*'] ++ 'x' :: '^' :: natToChars d = natToChars c.val ++ '*' :: 'x' :: '^' :: natToChars d := by simp
    rw [h_assoc]
    have hc_val : c.val ≠ 0 := by
      intro h_0
      apply hc
      have h_c : c.val = (0 : ZMod n).val := by
        rw [h_0, ZMod.val_zero]
      exact ZMod.val_injective n h_c
    exact append_not_start_char (natToChars c.val) ('*' :: 'x' :: '^' :: natToChars d) '0' (natToChars_ne_nil c.val) (fun cs => natToChars_not_start_zero c.val cs hc_val) cs

lemma string_ofList_ne_empty_of_ne_nil {l : List Char} (h : l ≠ []) : String.ofList l ≠ "" := by
  intro contra
  have h_len : (String.ofList l).length = 0 := by
    calc (String.ofList l).length
      _ = ("" : String).length := by rw [contra]
      _ = 0 := rfl
  have h2 : (String.ofList l).length = l.length := String.length_ofList
  rw [h2] at h_len
  cases l
  · contradiction
  · contradiction

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

lemma map_ne_nil_of_ne_nil {α β} (f : α → β) (l : List α) : l ≠ [] → l.map f ≠ [] := by
  cases l <;> simp

lemma reverse_ne_nil_of_ne_nil {α} (l : List α) : l ≠ [] → l.reverse ≠ [] := by
  cases l <;> simp

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

theorem mem_toList_of_getLast?_eq_some {α} : (l : List α) → (x : α) → l.getLast? = some x → x ∈ l
| [], x, h => by contradiction
| [a], x, h => by
  have hx : a = x := by injection h
  subst hx
  exact List.Mem.head _
| a :: b :: as, x, h => by
  have ht : x ∈ b :: as := mem_toList_of_getLast?_eq_some (b :: as) x h
  exact List.Mem.tail _ ht

lemma mem_toList_of_back?_eq_some {α} (a : Array α) (x : α) :
  a.back? = some x → x ∈ a.toList := by
  intro h
  have ht : a.toList.getLast? = a.back? := by simp
  rw [← ht] at h
  exact mem_toList_of_getLast?_eq_some a.toList x h

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

lemma toChars_int_ne_empty (p : DensePoly ℤ) : toChars p ≠ "" :=
  toChars_ne_empty p monomialToChars_int_ne_nil

lemma toChars_rat_ne_empty (p : DensePoly ℚ) : toChars p ≠ "" :=
  toChars_ne_empty p monomialToChars_rat_ne_nil

lemma toChars_zmod_ne_empty {n : ℕ} [NeZero n] (p : DensePoly (ZMod n)) : toChars p ≠ "" :=
  toChars_ne_empty p monomialToChars_zmod_ne_nil

end Azurite.DensePoly
