import Mathlib.Order.PiLex

/-! # BPR Section 2.1 — Definition 2.14: Lexicographic ordering

> The *lexicographic ordering* on `Fin k → B` for a linearly ordered
> type `B`: `a <ₗₑₓ b` iff there exists an index `i` such that
> `a j = b j` for all `j < i` and `a i < b i`.

This is `Pi.Lex (· < ·) (· < ·)` in Mathlib
(`Mathlib.Order.PiLex`).
-/

namespace Azurite.BPR

/-- **BPR Definition 2.14.** The *lexicographic ordering* on `Fin k → B` for a
    linearly ordered type `B`: `a <ₗₑₓ b` iff there exists an index `i` such that
    `a j = b j` for all `j < i` and `a i < b i`.

    This is `Pi.Lex (· < ·) (· < ·)` in Mathlib (`Mathlib.Order.PiLex`). -/
def LexOrder (k : ℕ) (B : Type*) [LT B] (a b : Fin k → B) : Prop :=
  Pi.Lex (· < ·) (· < ·) a b

end Azurite.BPR
