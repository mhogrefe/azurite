import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-! # BPR Section 2.1 — Definition 2.15: Graded lexicographic ordering

> The *graded lexicographic ordering* on multi-indices `Fin k →₀ ℕ`:
> `α <_grlex β` iff either `|α| < |β|` (smaller total degree), or
> `|α| = |β|` and `α <_lex β`.

This is the strict order on `DegLex (Fin k →₀ ℕ)` from
`Mathlib.Data.Finsupp.MonomialOrder.DegLex`, accessed via `toDegLex`.
-/

namespace Azurite.BPR

/-- **BPR Definition 2.15.** The *graded lexicographic ordering* on the set of
    monomials in `k` variables: `X^α <_grlex X^β` iff either `|α| < |β|`
    (total degree is smaller) or `|α| = |β|` and `α <_lex β`.

    In Mathlib this is the `<` on `DegLex (Fin k →₀ ℕ)`, accessed via
    `toDegLex` / `ofDegLex` from `Mathlib.Data.Finsupp.MonomialOrder.DegLex`. -/
def GrlexOrder (k : ℕ) (α β : Fin k →₀ ℕ) : Prop :=
  toDegLex α < toDegLex β

end Azurite.BPR
