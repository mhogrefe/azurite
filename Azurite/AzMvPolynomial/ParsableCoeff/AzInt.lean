/-
  `ParsableCoeff AzInt` instance: routes through the limb-level
  `AzInt.toString` / `AzInt.parse` pipeline.
-/
import Azurite.AzInt.Equiv.Parse
import Azurite.AzInt.Instances
import Azurite.AzMvPolynomial.ParsableCoeff
import Azurite.AzMvPolynomial.ParsableCoeff.AzNat

namespace Azurite

open AzPolynomial

/-! ### Char-list facade over `AzInt.toString` / `AzInt.parse` -/

/-- `AzInt.toChars z := (AzInt.toString z).toList`. -/
def AzInt.toChars (z : AzInt) : List Char := (AzInt.toString z).toList

/-- `AzInt.parseChars cs := AzInt.parse (String.ofList cs)`. -/
def AzInt.parseChars (cs : List Char) : Option AzInt := AzInt.parse (String.ofList cs)

private theorem AzInt.parseChars_toChars (z : AzInt) :
    AzInt.parseChars (AzInt.toChars z) = some z := by
  unfold AzInt.parseChars AzInt.toChars
  rw [show String.ofList (AzInt.toString z).toList = AzInt.toString z from by
    apply String.toList_inj.mp; rw [String.toList_ofList]]
  exact AzInt.parse_toString z

/-! ### Char-set facts about `AzInt.toString` -/

private theorem AzInt.toChars_eq (z : AzInt) :
    AzInt.toChars z =
      if z.sign then AzNat.toChars z.abs
      else '-' :: AzNat.toChars z.abs := by
  unfold AzInt.toChars AzInt.toString AzNat.toChars
  by_cases h_sign : z.sign
  · rw [if_pos h_sign, if_pos h_sign]
  · rw [if_neg h_sign, if_neg h_sign, String.toList_append]
    rfl

private theorem AzInt.toChars_nonempty (z : AzInt) : AzInt.toChars z ≠ [] := by
  rw [AzInt.toChars_eq]
  split_ifs with h_sign
  · exact AzNat.toString_ne_empty z.abs
  · intro h; cases h

/-- Every character of `AzInt.toChars z` is a decimal digit `'0'`–`'9'`
or `'-'`. -/
private theorem AzInt.mem_toChars_digit_or_dash (z : AzInt) (c : Char)
    (hc : c ∈ AzInt.toChars z) :
    c = '-' ∨ ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat) := by
  rw [AzInt.toChars_eq] at hc
  split_ifs at hc with h_sign
  · right; exact AzNat.toString_char_digit z.abs c hc
  · rcases List.mem_cons.mp hc with rfl | hc'
    · left; rfl
    · right; exact AzNat.toString_char_digit z.abs c hc'

private theorem AzInt.toChars_no_syntax (z : AzInt) (c : Char) (hc : c ∈ AzInt.toChars z)
    (hsyn : isCoeffSyntaxChar c) : False := by
  have h_zero : ('0' : Char).toNat = 48 := rfl
  have h_nine : ('9' : Char).toNat = 57 := rfl
  have h_plus : ('+' : Char).toNat = 43 := rfl
  have h_star : ('*' : Char).toNat = 42 := rfl
  have h_caret : ('^' : Char).toNat = 94 := rfl
  rcases hsyn with rfl | rfl | rfl
  all_goals
    rcases AzInt.mem_toChars_digit_or_dash z _ hc with hdash | ⟨h_lo, h_hi⟩
    · cases hdash
    · omega

private theorem AzInt.toChars_no_minus_tail (z : AzInt) (c : Char)
    (hc : c ∈ (AzInt.toChars z).tail) (heq : c = '-') : False := by
  rw [AzInt.toChars_eq] at hc
  split_ifs at hc with h_sign
  · -- positive: toChars = AzNat.toChars z.abs (all digits). Tail of that has no '-'.
    have h_mem : c ∈ AzNat.toChars z.abs := List.mem_of_mem_tail hc
    have ⟨h_lo, _⟩ := AzNat.toString_char_digit z.abs c h_mem
    subst heq; have : ('-' : Char).toNat = 45 := rfl
    have h_zero : ('0' : Char).toNat = 48 := rfl; omega
  · -- negative: toChars = '-' :: AzNat.toChars z.abs. Tail is z.abs's chars.
    have h_mem : c ∈ AzNat.toChars z.abs := by simpa using hc
    have ⟨h_lo, _⟩ := AzNat.toString_char_digit z.abs c h_mem
    subst heq; have : ('-' : Char).toNat = 45 := rfl
    have h_zero : ('0' : Char).toNat = 48 := rfl; omega

private theorem AzInt.toChars_head_is_syntax (z : AzInt) (c : Char) (t : List Char)
    (hct : AzInt.toChars z = c :: t) : isPolySyntaxChar c := by
  have h_mem : c ∈ AzInt.toChars z := hct ▸ List.mem_cons_self ..
  rcases AzInt.mem_toChars_digit_or_dash z c h_mem with rfl | hdig
  · right; right; left; rfl
  · left; exact hdig

private theorem AzInt.toChars_minus_next_syntax (z : AzInt) (t : List Char)
    (hct : AzInt.toChars z = '-' :: t) :
    ∃ c t', t = c :: t' ∧ isPolySyntaxChar c := by
  rw [AzInt.toChars_eq] at hct
  split_ifs at hct with h_sign
  · -- positive: AzNat.toChars z.abs starts with '-' — impossible since all chars are digits.
    have h_mem : ('-' : Char) ∈ AzNat.toChars z.abs := hct ▸ List.mem_cons_self ..
    have ⟨h_lo, _⟩ := AzNat.toString_char_digit z.abs '-' h_mem
    have h_dash : ('-' : Char).toNat = 45 := rfl
    have h_zero : ('0' : Char).toNat = 48 := rfl
    rw [h_dash, h_zero] at h_lo
    omega
  · -- negative: '-' :: AzNat.toChars z.abs = '-' :: t, so t = AzNat.toChars z.abs.
    have h_t_eq : t = AzNat.toChars z.abs := ((List.cons.inj hct).2).symm
    have h_ne := AzNat.toString_ne_empty z.abs
    have h_ne' : AzNat.toChars z.abs ≠ [] := h_ne
    obtain ⟨c', t', hc't'⟩ := List.exists_cons_of_ne_nil h_ne'
    have h_c'_mem : c' ∈ AzNat.toChars z.abs := hc't' ▸ List.mem_cons_self ..
    have h_c'_dig : '0'.toNat ≤ c'.toNat ∧ c'.toNat ≤ '9'.toNat :=
      AzNat.toString_char_digit z.abs c' h_c'_mem
    exact ⟨c', t', h_t_eq.trans hc't', Or.inl h_c'_dig⟩

private theorem AzInt.toChars_zero : AzInt.toChars (0 : AzInt) = ['0'] := by
  rw [AzInt.toChars_eq]
  rw [show (0 : AzInt).sign = true from rfl, if_pos rfl]
  exact AzNat.toString_zero

private theorem AzInt.toChars_no_comma (z : AzInt) : ',' ∉ AzInt.toChars z := by
  intro hc
  rcases AzInt.mem_toChars_digit_or_dash z ',' hc with hdash | ⟨h_lo, h_hi⟩
  · cases hdash
  · have : (',' : Char).toNat = 44 := rfl
    have h_zero : ('0' : Char).toNat = 48 := rfl
    omega

private theorem AzInt.toChars_no_semicolon (z : AzInt) : ';' ∉ AzInt.toChars z := by
  intro hc
  rcases AzInt.mem_toChars_digit_or_dash z ';' hc with hdash | ⟨h_lo, h_hi⟩
  · cases hdash
  · have : (';' : Char).toNat = 59 := rfl
    have h_nine : ('9' : Char).toNat = 57 := rfl
    omega

instance : ParsableCoeff AzInt where
  toChars := AzInt.toChars
  parseChars := AzInt.parseChars
  parse_toChars := AzInt.parseChars_toChars
  toChars_nonempty := AzInt.toChars_nonempty
  toChars_no_syntax := fun z c hc hsyn => AzInt.toChars_no_syntax z c hc hsyn
  toChars_no_minus_tail := fun z c hc heq => AzInt.toChars_no_minus_tail z c hc heq
  toChars_head_is_syntax := AzInt.toChars_head_is_syntax
  negOne := some ⟨-1, by
    intro h; have := congrArg AzInt.toInt h
    rw [AzInt.toInt_neg, AzInt.toInt_one, AzInt.toInt_zero] at this; omega, by
    intro h; have := congrArg AzInt.toInt h
    rw [AzInt.toInt_neg, AzInt.toInt_one] at this; omega⟩
  toChars_minus_next_syntax := AzInt.toChars_minus_next_syntax
  toChars_zero := AzInt.toChars_zero
  toChars_no_comma := AzInt.toChars_no_comma
  toChars_no_semicolon := AzInt.toChars_no_semicolon

end Azurite
