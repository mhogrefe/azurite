import Azurite.AzRationalFunction.Parse
import Azurite.AzPolynomial.Compare

/-!
# A total order on `AzRationalFunction`

Compare by the **display fraction** — the reconstituted reduced integer
pair `(displayNum, displayDen)` — lexicographically in the canonical
`AzPolynomial` order (degree, then top-down lexicographic), denominator
first. The display pair determines the value
(`ofNumDen_displayNum_displayDen`), so this is a total order; and since a
polynomial `p` displays as `(p, 1)`, the canonical map `ofPolynomial` is
strictly order-preserving: polynomials sort first (denominator `1`) and
among themselves exactly in the `AzPolynomial` order.

`LT`/`LE`/`Ord` instances (with decidability) live here; the `LinearOrder`
instance with its laws and the order-embedding theorems are in
`Azurite.AzRationalFunction.Equiv.Compare`.
-/

namespace Azurite.AzRationalFunction

open Azurite.AzPolynomial

/-- Degree-then-lex comparison of the display fractions, denominator
first. -/
def compare (r s : AzRationalFunction) : Ordering :=
  match AzPolynomial.compare (displayDen r) (displayDen s) with
  | .eq => AzPolynomial.compare (displayNum r) (displayNum s)
  | o => o

instance : Ord AzRationalFunction := ⟨compare⟩

instance : LT AzRationalFunction := ⟨fun r s => compare r s = .lt⟩

instance : LE AzRationalFunction := ⟨fun r s => compare r s ≠ .gt⟩

instance : DecidableLT AzRationalFunction := fun _ _ => inferInstanceAs (Decidable (_ = _))

instance : DecidableLE AzRationalFunction := fun _ _ => inferInstanceAs (Decidable (_ ≠ _))

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def rr (s : String) : AzRationalFunction := (parse s).get!

-- the canonical map preserves the `AzPolynomial` order
#guard rr "x" < rr "-5*x^2"
#guard rr "0" < rr "-3"
#guard rr "x^2+x+1" < rr "x^2+x+2"
#guard rr "-6*x-9" < rr "x^2"
-- polynomials (denominator 1) precede proper fractions
#guard rr "x^5" < rr "1/x"
-- fractions: denominator first, then numerator
#guard rr "1/x" < rr "1/(x+1)"
#guard rr "1/x" < rr "x^2/(x+1)"
#guard rr "(x-1)/(x+1)" < rr "x/(x+1)"
#guard compare (rr "2*x/4") (rr "x/2") == .eq
#guard (0 : AzRationalFunction) < 1

end Tests

end Azurite.AzRationalFunction
