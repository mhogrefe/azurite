/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.Basic
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.ToString
import Azurite.AzInt.Equiv.Compare
import Azurite.AzRat.Instances

/-!
# A total order on `AzMvPolynomial` (ordered coefficients)

Multivariate polynomials are ordered **by total degree first, then
lexicographically by the monomial order with the higher monomials most
significant** — the direct analogue of the univariate degree-then-top-down
order, and a canonical total order for sorting lists of polynomials.

Concretely, since each term array is normalized (sorted strictly descending
by monic part, no zero coefficients, no duplicates), the comparison is:

* compare the *degree keys* — `0` for the zero polynomial (making it the
  least element, exactly as the univariate order's zero-size does), and
  `totalDegree + 1` otherwise, so total degree dominates;
* on a tie, scan the two descending term lists together, comparing
  coefficients **at the larger monic where they differ, an absent term
  contributing `0`** (`compareTerms`).

The zero-least convention makes the canonical map from `AzPolynomial`
order-preserving (`Azurite.AzMvPolynomial.Equiv.Compare`), matching the
univariate order where `0` precedes even the negative constants.

`LT`/`LE`/`Ord` (with decidability) live here; the `LinearOrder` instance
with its laws, and the order-preservation of the univariate embedding, are
in `Azurite.AzMvPolynomial.Equiv.Compare`.

(Inside this namespace `compare` on coefficients / monics / naturals must be
written `Ord.compare` — `AzMvPolynomial.compare` shadows the export.)
-/

namespace Azurite.AzMvPolynomial

variable {R : Type _} [Semiring R] [LinearOrder R] {n : ℕ} {ord : MonomialOrder}

/-- Scan two descending, normalized term lists together, comparing
"lexicographically with implicit zeros": at the largest monic where the two
differ, compare the coefficients (an absent term contributing `0`; a present
coefficient is never `0`, so those comparisons are always decisive). -/
def compareTerms : List (Monomial n R ord) → List (Monomial n R ord) → Ordering
  | [], [] => .eq
  | [], (y :: _) => Ord.compare (0 : R) y.coeff.val
  | (x :: _), [] => Ord.compare x.coeff.val (0 : R)
  | (x :: xs), (y :: ys) =>
    match Ord.compare x.monic y.monic with
    | .gt => Ord.compare x.coeff.val (0 : R)
    | .lt => Ord.compare (0 : R) y.coeff.val
    | .eq =>
      match Ord.compare x.coeff.val y.coeff.val with
      | .eq => compareTerms xs ys
      | o => o

/-- The degree key: `0` for the zero polynomial (least element), otherwise
`totalDegree + 1`, so total degree dominates the comparison. -/
def degreeKey (p : AzMvPolynomial n R ord) : ℕ :=
  if p.terms.isEmpty then 0 else p.totalDegree + 1

/-- **Total-degree-then-lexicographic comparison**: by degree key, then the
top-down monomial scan of the descending term lists. -/
def compare (p q : AzMvPolynomial n R ord) : Ordering :=
  match Ord.compare (degreeKey p) (degreeKey q) with
  | .eq => compareTerms p.terms.toList q.terms.toList
  | o => o

instance : Ord (AzMvPolynomial n R ord) := ⟨compare⟩

instance : LT (AzMvPolynomial n R ord) := ⟨fun p q => compare p q = .lt⟩

instance : LE (AzMvPolynomial n R ord) := ⟨fun p q => compare p q ≠ .gt⟩

instance : DecidableLT (AzMvPolynomial n R ord) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))

instance : DecidableLE (AzMvPolynomial n R ord) :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _))

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance fact1Le26 : Fact (1 ≤ 26) := ⟨by omega⟩
private instance fact2Le26 : Fact (2 ≤ 26) := ⟨by omega⟩
private instance fact3Le26 : Fact (3 ≤ 26) := ⟨by omega⟩

private def p2 (s : String) : AzMvPolynomial 2 AzInt .Degrevlex :=
  (AzMvPolynomial.parseStrWith (XyzVar 2) s).getD 0
private def p3 (s : String) : AzMvPolynomial 3 AzInt .Degrevlex :=
  (AzMvPolynomial.parseStrWith (XyzVar 3) s).getD 0

-- total degree dominates, regardless of signs and monomial order
#guard p2 "x" < p2 "-5*x^2"
#guard p2 "x*y" < p2 "x^3"
#guard p2 "0" < p2 "x"
-- the zero polynomial is the least element, even below negative constants
#guard p2 "0" < p2 "-5"
-- equal total degree: the larger monic decides (by the `ord` monomial order)
#guard p2 "y^2" < p2 "x^2"
#guard p2 "x*y" < p2 "x^2"
-- equal leading monomial: compare its coefficient …
#guard p2 "2*x^2+100*y^2" < p2 "3*x^2-100*y^2"
-- … then scan down to the next monomial (implicit zero for the missing term)
#guard p2 "x^2+5*y^2" < p2 "x^2+6*y^2"
#guard p2 "x^2" < p2 "x^2+y^2"
#guard p2 "x^2-y^2" < p2 "x^2"
#guard AzMvPolynomial.compare (p2 "x^2+x*y+1") (p2 "x^2+x*y+1") == .eq
-- three variables
#guard p3 "x*y*z" < p3 "x^3"
#guard p3 "z" < p3 "y"
#guard p3 "y" < p3 "x"
-- sorting a list gives the canonical order
#guard ([p2 "x^2", p2 "0", p2 "-x^3", p2 "x^2-y^2", p2 "5"].mergeSort (· ≤ ·)).map
    (fun p => p.toStrWith (XyzVar 2))
    == ["0", "5", "x^2-y^2", "x^2", "-x^3"]

end Tests

end Azurite.AzMvPolynomial
