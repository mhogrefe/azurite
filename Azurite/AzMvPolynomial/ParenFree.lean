/-
  `ParenFreeCoeff` and `ParenFreeVar`: typeclass assertions that a
  `ParsableCoeff` / `ParsableVar` instance's character-list representation
  never contains a `(` or `)`.

  These enable nested-polynomial serialization (`AzPolynomial.MvCoeffParse`)
  where coefficients are wrapped in `(...)`: the outer parser can reliably
  locate the closing paren because no inner character is itself a paren.

  Instances are provided for all stock coefficient types (`ℕ`, `ℤ`, `ℚ`,
  `ZMod m`) and all stock variable types (`IndexedVar`, `IndexedCapsVar`,
  `AbcVar`, `AbcCapsVar`, `XyzVar`, `XyzCapsVar`, `GreekVar`, `GreekCapsVar`).
-/
import Azurite.AzMvPolynomial.Var
import Azurite.AzMvPolynomial.ParsableCoeff

namespace Azurite

open AzPolynomial

/-- Typeclass assertion that a `ParsableCoeff` instance's character-list
    representation never contains `(` or `)`.  Combined with `ParenFreeVar`
    this lifts to `AzMvPolynomial.toCharsWith F` via
    `AzMvPolynomial.char_notin_toCharsWith`. -/
class ParenFreeCoeff (R : Type _) [Semiring R] [NeZero (1 : R)] [ParsableCoeff R] : Prop where
  toChars_no_lparen : ∀ r : R, '(' ∉ ParsableCoeff.toChars r
  toChars_no_rparen : ∀ r : R, ')' ∉ ParsableCoeff.toChars r

/-- Typeclass assertion that a `ParsableVar` instance's character-list
    representation never contains `(` or `)`. -/
class ParenFreeVar (α : Type _) (n : outParam ℕ) [LinearOrder α] [ParsableVar α n] : Prop where
  toChars_no_lparen : ∀ v : α, '(' ∉ ParsableVar.toChars v
  toChars_no_rparen : ∀ v : α, ')' ∉ ParsableVar.toChars v

/-! ### ParenFreeCoeff instances -/

/- `ParenFreeCoeff` instances for the non-Az types `ℕ`, `ℤ`, `ℚ`, and `ZMod` have
   been removed along with their `ParsableCoeff` instances; use the Az
   coefficient types instead. -/

/-! ### ParenFreeVar instances -/

/-- Helper: neither `(` nor `)` lies in the subscript-digit Unicode range. -/
private theorem paren_not_in_subscript_range (c : Char) (hc : c = '(' ∨ c = ')')
    (h : c.toNat ≥ 8320 ∧ c.toNat ≤ 8329) : False := by
  rcases hc with rfl | rfl
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)

instance {n : ℕ} : ParenFreeVar (IndexedVar n) n where
  toChars_no_lparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char)
      = ['x'] ++ natToSubscriptChars v.val from rfl,
      List.cons_append, List.nil_append, List.mem_cons] at hc
    rcases hc with heq | hc
    · exact absurd heq (by decide)
    · exact paren_not_in_subscript_range '(' (Or.inl rfl)
        (mem_natToSubscriptChars_range v.val '(' hc)
  toChars_no_rparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char)
      = ['x'] ++ natToSubscriptChars v.val from rfl,
      List.cons_append, List.nil_append, List.mem_cons] at hc
    rcases hc with heq | hc
    · exact absurd heq (by decide)
    · exact paren_not_in_subscript_range ')' (Or.inr rfl)
        (mem_natToSubscriptChars_range v.val ')' hc)

instance {n : ℕ} : ParenFreeVar (IndexedCapsVar n) n where
  toChars_no_lparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char)
      = ['X'] ++ natToSubscriptChars v.val from rfl,
      List.cons_append, List.nil_append, List.mem_cons] at hc
    rcases hc with heq | hc
    · exact absurd heq (by decide)
    · exact paren_not_in_subscript_range '(' (Or.inl rfl)
        (mem_natToSubscriptChars_range v.val '(' hc)
  toChars_no_rparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char)
      = ['X'] ++ natToSubscriptChars v.val from rfl,
      List.cons_append, List.nil_append, List.mem_cons] at hc
    rcases hc with heq | hc
    · exact absurd heq (by decide)
    · exact paren_not_in_subscript_range ')' (Or.inr rfl)
        (mem_natToSubscriptChars_range v.val ')' hc)

/-- Helper: a char with `toNat ≥ 42` is neither `(` (toNat 40) nor `)` (toNat 41). -/
private theorem not_paren_of_ge_42 (c : Char) (hge : c.toNat ≥ 42) :
    c ≠ '(' ∧ c ≠ ')' := by
  refine ⟨?_, ?_⟩ <;> (intro h; rw [h] at hge; exact absurd hge (by decide))

instance {n : ℕ} [Fact (n ≤ 26)] : ParenFreeVar (AbcVar n) n where
  toChars_no_lparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    have hge := v.is_valid.1
    simp only [show ('a' : Char).toNat = 97 from by decide] at hge
    exact (not_paren_of_ge_42 v.ch (by omega)).1 hc.symm
  toChars_no_rparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    have hge := v.is_valid.1
    simp only [show ('a' : Char).toNat = 97 from by decide] at hge
    exact (not_paren_of_ge_42 v.ch (by omega)).2 hc.symm

instance {n : ℕ} [Fact (n ≤ 26)] : ParenFreeVar (AbcCapsVar n) n where
  toChars_no_lparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    have hge := v.is_valid.1
    simp only [show ('A' : Char).toNat = 65 from by decide] at hge
    exact (not_paren_of_ge_42 v.ch (by omega)).1 hc.symm
  toChars_no_rparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    have hge := v.is_valid.1
    simp only [show ('A' : Char).toNat = 65 from by decide] at hge
    exact (not_paren_of_ge_42 v.ch (by omega)).2 hc.symm

instance {n : ℕ} [Fact (n ≤ 26)] : ParenFreeVar (XyzVar n) n where
  toChars_no_lparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    have hge := v.is_valid.1
    simp only [show ('a' : Char).toNat = 97 from by decide] at hge
    exact (not_paren_of_ge_42 v.ch (by omega)).1 hc.symm
  toChars_no_rparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    have hge := v.is_valid.1
    simp only [show ('a' : Char).toNat = 97 from by decide] at hge
    exact (not_paren_of_ge_42 v.ch (by omega)).2 hc.symm

instance {n : ℕ} [Fact (n ≤ 26)] : ParenFreeVar (XyzCapsVar n) n where
  toChars_no_lparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    have hge := v.is_valid.1
    simp only [show ('A' : Char).toNat = 65 from by decide] at hge
    exact (not_paren_of_ge_42 v.ch (by omega)).1 hc.symm
  toChars_no_rparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    have hge := v.is_valid.1
    simp only [show ('A' : Char).toNat = 65 from by decide] at hge
    exact (not_paren_of_ge_42 v.ch (by omega)).2 hc.symm

instance {n : ℕ} [Fact (n ≤ 24)] : ParenFreeVar (GreekVar n) n where
  toChars_no_lparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    exact (not_paren_of_ge_42 v.ch (by have := v.is_valid.1; omega)).1 hc.symm
  toChars_no_rparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    exact (not_paren_of_ge_42 v.ch (by have := v.is_valid.1; omega)).2 hc.symm

instance {n : ℕ} [Fact (n ≤ 24)] : ParenFreeVar (GreekCapsVar n) n where
  toChars_no_lparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    exact (not_paren_of_ge_42 v.ch (by have := v.is_valid.1; omega)).1 hc.symm
  toChars_no_rparen v hc := by
    simp only [show (ParsableVar.toChars v : List Char) = [v.ch] from rfl,
      List.mem_singleton] at hc
    exact (not_paren_of_ge_42 v.ch (by have := v.is_valid.1; omega)).2 hc.symm

end Azurite
