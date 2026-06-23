/-
  `ParsableCoeff AzRat` instance: routes through the limb-level
  `AzRat.toChars` / `AzRat.parse` pipeline (`"0"`, `"4"`, `"1/3"`,
  `"-1/3"`), so `AzRat` works as a coefficient type for `AzPolynomial` /
  `AzMvPolynomial` string conversion.
-/
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Azurite.AzRat.Equiv.Parse
import Azurite.AzRat.Instances

namespace Azurite

open AzPolynomial

/-! ### Char-list facade over `AzRat.parse` (`AzRat.toChars` is already a
char list) -/

/-- `AzRat.parseChars cs := AzRat.parse (String.ofList cs)`. -/
def AzRat.parseChars (cs : List Char) : Option AzRat := AzRat.parse (String.ofList cs)

theorem AzRat.parseChars_toChars (q : AzRat) :
    AzRat.parseChars q.toChars = some q := by
  show AzRat.parse (String.ofList q.toChars) = some q
  exact AzRat.parse_toString q

/-! ### Char-set facts about `AzRat.toChars` -/

/-- `AzRat.toChars` in terms of the `AzInt`/`AzNat` char lists: signed
numerator, then `'/'` and the denominator unless the denominator is `1`. -/
theorem AzRat.toChars_eq (q : AzRat) :
    q.toChars = if q.den = 1 then AzInt.toChars q.numInt
      else AzInt.toChars q.numInt ++ '/' :: AzNat.toChars q.den := rfl

theorem AzRat.toChars_nonempty (q : AzRat) : q.toChars ≠ [] := by
  rw [AzRat.toChars_eq]
  split_ifs
  · exact AzInt.toChars_nonempty _
  · intro h
    exact AzInt.toChars_nonempty q.numInt (List.append_eq_nil_iff.mp h).1

/-- Every character of `AzRat.toChars q` is `'-'`, `'/'`, or a decimal digit
`'0'`–`'9'`. -/
theorem AzRat.mem_toChars_digit_or_dash_or_slash (q : AzRat) (c : Char)
    (hc : c ∈ q.toChars) :
    c = '-' ∨ c = '/' ∨ ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat) := by
  rw [AzRat.toChars_eq] at hc
  split_ifs at hc with hden
  · rcases AzInt.mem_toChars_digit_or_dash _ c hc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rcases List.mem_append.mp hc with h | h
    · rcases AzInt.mem_toChars_digit_or_dash _ c h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (AzNat.toString_char_digit _ c h'))

theorem AzRat.toChars_no_syntax (q : AzRat) (c : Char) (hc : c ∈ q.toChars)
    (hsyn : isCoeffSyntaxChar c) : False := by
  have h_zero : ('0' : Char).toNat = 48 := rfl
  have h_nine : ('9' : Char).toNat = 57 := rfl
  have h_plus : ('+' : Char).toNat = 43 := rfl
  have h_star : ('*' : Char).toNat = 42 := rfl
  have h_caret : ('^' : Char).toNat = 94 := rfl
  rcases hsyn with rfl | rfl | rfl
  all_goals
    rcases AzRat.mem_toChars_digit_or_dash_or_slash q _ hc with hdash | hslash | ⟨h_lo, h_hi⟩
    · cases hdash
    · cases hslash
    · omega

theorem AzRat.toChars_no_minus_tail (q : AzRat) (c : Char)
    (hc : c ∈ q.toChars.tail) (heq : c = '-') : False := by
  rw [AzRat.toChars_eq] at hc
  split_ifs at hc with hden
  · exact AzInt.toChars_no_minus_tail _ c hc heq
  · obtain ⟨c0, t0, h0⟩ := List.exists_cons_of_ne_nil (AzInt.toChars_nonempty q.numInt)
    rw [h0, List.cons_append, List.tail_cons] at hc
    rcases List.mem_append.mp hc with h | h
    · exact AzInt.toChars_no_minus_tail q.numInt c (by rw [h0]; exact h) heq
    · rcases List.mem_cons.mp h with rfl | h'
      · cases heq
      · have ⟨h_lo, _⟩ := AzNat.toString_char_digit q.den c h'
        subst heq
        have h_dash : ('-' : Char).toNat = 45 := rfl
        have h_zero : ('0' : Char).toNat = 48 := rfl
        omega

theorem AzRat.toChars_head_is_syntax (q : AzRat) (c : Char) (t : List Char)
    (hct : q.toChars = c :: t) : isPolySyntaxChar c := by
  rw [AzRat.toChars_eq] at hct
  split_ifs at hct with hden
  · exact AzInt.toChars_head_is_syntax _ c t hct
  · obtain ⟨c0, t0, h0⟩ := List.exists_cons_of_ne_nil (AzInt.toChars_nonempty q.numInt)
    rw [h0, List.cons_append] at hct
    obtain ⟨rfl, -⟩ := List.cons.inj hct
    exact AzInt.toChars_head_is_syntax q.numInt c0 t0 h0

theorem AzRat.toChars_minus_next_syntax (q : AzRat) (t : List Char)
    (hct : q.toChars = '-' :: t) :
    ∃ c t', t = c :: t' ∧ isPolySyntaxChar c := by
  rw [AzRat.toChars_eq] at hct
  split_ifs at hct with hden
  · exact AzInt.toChars_minus_next_syntax _ t hct
  · obtain ⟨c0, t0, h0⟩ := List.exists_cons_of_ne_nil (AzInt.toChars_nonempty q.numInt)
    rw [h0, List.cons_append] at hct
    obtain ⟨hc0, ht⟩ := List.cons.inj hct
    obtain ⟨c1, t1, h1, hsyn⟩ :=
      AzInt.toChars_minus_next_syntax q.numInt t0 (by rw [h0, hc0])
    exact ⟨c1, t1 ++ '/' :: AzNat.toChars q.den, by rw [← ht, h1, List.cons_append], hsyn⟩

theorem AzRat.toChars_zero : (0 : AzRat).toChars = ['0'] := by
  rw [AzRat.toChars_eq, if_pos (show (0 : AzRat).den = 1 from rfl)]
  exact AzInt.toChars_zero

theorem AzRat.toChars_no_comma (q : AzRat) : ',' ∉ q.toChars := by
  intro hc
  rcases AzRat.mem_toChars_digit_or_dash_or_slash q ',' hc with h | h | ⟨h_lo, h_hi⟩
  · cases h
  · cases h
  · have : (',' : Char).toNat = 44 := rfl
    have h_zero : ('0' : Char).toNat = 48 := rfl
    omega

theorem AzRat.toChars_no_semicolon (q : AzRat) : ';' ∉ q.toChars := by
  intro hc
  rcases AzRat.mem_toChars_digit_or_dash_or_slash q ';' hc with h | h | ⟨h_lo, h_hi⟩
  · cases h
  · cases h
  · have : (';' : Char).toNat = 59 := rfl
    have h_nine : ('9' : Char).toNat = 57 := rfl
    omega

instance : ParsableCoeff AzRat where
  toChars := AzRat.toChars
  parseChars := AzRat.parseChars
  parse_toChars := AzRat.parseChars_toChars
  toChars_nonempty := AzRat.toChars_nonempty
  toChars_no_syntax := fun q c hc hsyn => AzRat.toChars_no_syntax q c hc hsyn
  toChars_no_minus_tail := fun q c hc heq => AzRat.toChars_no_minus_tail q c hc heq
  toChars_head_is_syntax := AzRat.toChars_head_is_syntax
  negOne := some ⟨-1, fun h => by
    have := congrArg AzRat.toRat h
    rw [AzRat.toRat_neg, AzRat.toRat_one, AzRat.toRat_zero] at this
    norm_num at this, fun h => by
    have := congrArg AzRat.toRat h
    rw [AzRat.toRat_neg, AzRat.toRat_one] at this
    norm_num at this⟩
  toChars_minus_next_syntax := AzRat.toChars_minus_next_syntax
  toChars_zero := AzRat.toChars_zero
  toChars_no_comma := AzRat.toChars_no_comma
  toChars_no_semicolon := AzRat.toChars_no_semicolon

end Azurite
