import Azurite.DensePoly.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

namespace Azurite.DensePoly

/-- A typeclass for types whose elements can be parsed from a monomial string coefficient. -/
class DensePolyParsable (R : Type _) where
  parse : List Char → Option R

def parseNatCharsAux (cs : List Char) (acc : ℕ) : Option ℕ :=
  match cs with
  | [] => some acc
  | c :: cs =>
    if c.isDigit then
      parseNatCharsAux cs (acc * 10 + (c.toNat - '0'.toNat))
    else none

def parseNatChars (cs : List Char) : Option ℕ :=
  match cs with
  | [] => none
  | _ => parseNatCharsAux cs 0

def natToCharsAux (fuel : ℕ) (n : ℕ) (acc : List Char) : List Char :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    if n = 0 then acc
    else
      let digit := Char.ofNat ('0'.toNat + (n % 10))
      natToCharsAux f (n / 10) (digit :: acc)

def natToChars (n : ℕ) : List Char :=
  if n = 0 then ['0']
  else natToCharsAux n n []

def parseIntChars (cs : List Char) : Option ℤ :=
  match cs with
  | [] => none
  | '-' :: cs => (parseNatChars cs).map (fun n => - (n : ℤ))
  | _ => (parseNatChars cs).map (fun n => (n : ℤ))

def intToChars (z : ℤ) : List Char :=
  if z < 0 then
    let n := z.natAbs
    if n = 0 then ['0']
    else '-' :: natToCharsAux n n []
  else
    let n := z.natAbs
    if n = 0 then ['0']
    else natToCharsAux n n []

instance : DensePolyParsable ℕ where
  parse cs := parseNatChars cs

instance : DensePolyParsable ℤ where
  parse cs := parseIntChars cs

def parseRatChars (cs : List Char) : Option ℚ :=
  match cs.splitOn '/' with
  | [num_cs] =>
    (parseIntChars num_cs).map (fun n => (n : ℚ))
  | [num_cs, den_cs] =>
    match parseIntChars num_cs, parseNatChars den_cs with
    | some num, some den =>
      if den = 0 then none
      else some ((num : ℚ) / (den : ℚ))
    | _, _ => none
  | _ => none

def ratToChars (q : ℚ) : List Char :=
  if q.den = 1 then intToChars q.num
  else intToChars q.num ++ ['/'] ++ natToChars q.den

instance : DensePolyParsable ℚ where
  parse cs := parseRatChars cs

instance {n : ℕ} [NeZero n] : DensePolyParsable (ZMod n) where
  parse cs := (parseIntChars cs).map (fun x => (x : ZMod n))

/-- A typeclass for types whose elements can be formatted as a list of characters for polynomial coefficients. -/
class DensePolyToChars (R : Type _) where
  toChars : R → List Char

instance : DensePolyToChars ℕ where
  toChars := natToChars

instance : DensePolyToChars ℤ where
  toChars := intToChars

instance : DensePolyToChars ℚ where
  toChars := ratToChars

def zmodToChars {n : ℕ} [NeZero n] (c : ZMod n) : List Char := natToChars c.val

instance {n : ℕ} [NeZero n] : DensePolyToChars (ZMod n) where
  toChars := zmodToChars

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

lemma not_mem_drop_of_not_mem {α : Type _} {a : α} {l : List α} (n : ℕ) (h : a ∉ l) :
  a ∉ l.drop n := by
  intro hc
  exact h (List.mem_of_mem_drop hc)

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
    · apply not_mem_drop_of_not_mem
      apply not_mem_natToCharsAux
      intro hc; nomatch hc

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
  no_dash_in_tail := fun n => not_mem_drop_of_not_mem 1 (not_mem_natToChars n)

instance : NoDashInTail ℤ where
  no_dash_in_tail := not_mem_tail_intToChars

instance : NoDashInTail ℚ where
  no_dash_in_tail := not_mem_tail_ratToChars

lemma drop_one_append {α : Type _} (l1 l2 : List α) :
  (l1 ++ l2).drop 1 = if l1 = [] then l2.drop 1 else l1.drop 1 ++ l2 := by
  cases l1
  · rfl
  · rfl

/--
Formats a monomial with degree `d` and coefficient `c` as a `List Char`.
Handles "1" and "-1" intuitively based on `DensePolyToChars R`.
-/
def monomialToChars {R : Type _} [DecidableEq R] [Zero R] [DensePolyToChars R] (d : ℕ) (c : R) : List Char :=
  if c = 0 then
    ['0']
  else if d = 0 then
    DensePolyToChars.toChars c
  else
    let s := DensePolyToChars.toChars c
    let pfx := if s == ['1'] then [] else if s == ['-', '1'] then ['-'] else s ++ ['*']
    let sfx := if d = 1 then ['x'] else ['x', '^'] ++ natToChars d
    pfx ++ sfx

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

instance {n : ℕ} [NeZero n] : ToString (ZMod n) where
  toString x := toString x.val

end Azurite.DensePoly
