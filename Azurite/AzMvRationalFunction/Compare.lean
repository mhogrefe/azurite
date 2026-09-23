/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvRationalFunction.Parse
import Azurite.AzMvPolynomial.Compare

/-!
# A total order on `AzMvRationalFunction`

Compare by the **display fraction** — the reconstituted reduced integer
pair `(displayNum, displayDen)` — lexicographically in the canonical
`AzMvPolynomial` order (total degree, then top-down lexicographic by the
monomial order), denominator first. The display pair determines the value
(`ofNumDen_displayNum_displayDen`), so this is a total order; and since a
polynomial `p` displays as `(p, 1)`, the canonical map `ofMvPolynomial` is
strictly order-preserving: polynomials sort first (denominator `1`) and
among themselves exactly in the `AzMvPolynomial` order.

`LT`/`LE`/`Ord` instances (with decidability) live here; the `LinearOrder`
instance with its laws and the order-embedding theorems are in
`Azurite.AzMvRationalFunction.Equiv.Compare`.
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- Total-degree-then-lex comparison of the display fractions, denominator
first. -/
def compare (r s : AzMvRationalFunction n ord) : Ordering :=
  match AzMvPolynomial.compare (displayDen r) (displayDen s) with
  | .eq => AzMvPolynomial.compare (displayNum r) (displayNum s)
  | o => o

instance : Ord (AzMvRationalFunction n ord) := ⟨compare⟩

instance : LT (AzMvRationalFunction n ord) := ⟨fun r s => compare r s = .lt⟩

instance : LE (AzMvRationalFunction n ord) := ⟨fun r s => compare r s ≠ .gt⟩

instance : DecidableLT (AzMvRationalFunction n ord) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))

instance : DecidableLE (AzMvRationalFunction n ord) :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _))

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance : Fact (2 ≤ 26) := ⟨by omega⟩

private def r2 (s : String) : AzMvRationalFunction 2 .Degrevlex :=
  (parseStrWith (XyzVar 2) s).getD 0

-- the canonical map preserves the `AzMvPolynomial` order
#guard r2 "x" < r2 "-5*x^2"
#guard r2 "0" < r2 "-3"
#guard r2 "x^2+x+1" < r2 "x^2+x+2"
-- polynomials (denominator 1) precede proper fractions
#guard r2 "x^5" < r2 "1/x"
-- fractions: denominator first, then numerator
#guard r2 "1/x" < r2 "1/(x+1)"
#guard r2 "1/x" < r2 "x^2/(x+1)"
#guard compare (r2 "2*x/4") (r2 "x/2") == .eq
#guard (0 : AzMvRationalFunction 2 .Degrevlex) < 1

end Tests

end Azurite.AzMvRationalFunction
