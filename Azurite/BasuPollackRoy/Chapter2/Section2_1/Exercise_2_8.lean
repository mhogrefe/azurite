import Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_14
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Finsupp.Basic
import Mathlib.Order.PiLex

/-! # BPR Section 2.1 — Exercise 2.8: Lex ordering is well-founded

> A strictly decreasing sequence for the lexicographic ordering on
> `ℕᵏ` is necessarily finite. Equivalently, the lex ordering on
> multi-indices is well-founded.

The classical proof is by induction on `k`: for `k = 0` every sequence
is constant; for `k + 1`, the first component must eventually stabilize
(by well-foundedness of `ℕ`), after which the problem reduces to
`ℕᵏ`.

In Mathlib this is `Pi.Lex.wellFounded` applied to `Fin k` (finite,
linearly ordered) and `ℕ` (well-ordered).
-/

namespace Azurite.BPR

/-- **BPR Exercise 2.8.** A strictly decreasing sequence for the lexicographic
    ordering on `ℕᵏ` is necessarily finite. Equivalently, the lex ordering on
    multi-indices is well-founded.

    The classical proof is by induction on `k`: for `k = 0` every sequence is
    constant; for `k + 1`, the first component must eventually stabilize (by
    well-foundedness of `ℕ`), after which the problem reduces to `ℕᵏ`.

    In Mathlib this is `Pi.Lex.wellFounded` applied to `Fin k` (finite, linearly
    ordered) and `ℕ` (well-ordered). -/
theorem exercise_2_8 (k : ℕ) :
    WellFounded (fun α β : Fin k →₀ ℕ => LexOrder k ℕ α β) := by
  unfold LexOrder
  exact InvImage.wf (fun (x : Fin k →₀ ℕ) => (x : Fin k → ℕ))
    (Pi.Lex.wellFounded (r := (· < ·)) (s := fun _ : Fin k => (· < ·)))

end Azurite.BPR
