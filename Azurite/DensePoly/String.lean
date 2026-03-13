import Azurite.DensePoly.Basic
import Azurite.DensePoly.ToString
import Mathlib.Data.String.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

namespace Azurite.DensePoly

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

@[simp] lemma parse_monomialToString_zero {R : Type _} [DensePolyParsable R] [DecidableEq R] [Zero R] [ToString R] (d : ℕ)
  (hparse : DensePolyParsable.parse "0" = some (0 : R)) :
  parseMonomial (R := R) (monomialToString d (0 : R)) = some (0, 0) := by
  sorry

@[simp] lemma parse_monomialToString_ne_zero_nat (d : ℕ) (c : ℕ) (hc : c ≠ 0) :
  parseMonomial (R := ℕ) (monomialToString d c) = some (d, c) := by
  sorry

@[simp] lemma parse_monomialToString_ne_zero_int (d : ℕ) (c : ℤ) (hc : c ≠ 0) :
  parseMonomial (R := ℤ) (monomialToString d c) = some (d, c) := by
  sorry

lemma natToChars_not_dash (n : ℕ) (cs : List Char) : natToChars n = '-' :: cs → False := by
  intro h
  have h_parse := parseNatChars_natToChars n
  rw [h] at h_parse
  have h_none : parseNatChars ('-' :: cs) = none := rfl
  rw [h_none] at h_parse
  contradiction

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

lemma not_mem_natToCharsAux (fuel n : ℕ) (acc : List Char) (h : '/' ∉ acc) :
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

lemma not_mem_natToChars (n : ℕ) : '/' ∉ natToChars n := by
  unfold natToChars
  split_ifs with hn
  · intro hc; simp at hc
  · exact not_mem_natToCharsAux _ _ _ (by simp)

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
    | inr hr => exact not_mem_natToChars _ hr
  · exact not_mem_natToChars _

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
  rw [splitOnP_go_not_mem l2 [] h2]
  simp only [List.reverse_reverse, List.reverse_nil, List.nil_append]

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
    have h2 := not_mem_natToChars q.den
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

lemma parse_monomialToString_ne_zero_rat (d : ℕ) (c : ℚ) (hc : c ≠ 0) :
  parseMonomial (R := ℚ) (monomialToString d c) = some (d, c) := by
  sorry

lemma parse_monomialToString_ne_zero_zmod {n : ℕ} [NeZero n] (d : ℕ) (c : ZMod n) (hc : c ≠ 0) :
  parseMonomial (R := ZMod n) (monomialToString d c) = some (d, c) := by
  sorry

end Azurite.DensePoly
