/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse
import Azurite.AzInt.Instances
import Azurite.AzInt.ParsableElement
import Azurite.AzInt.Equiv.Compare
import Azurite.AzRat.Instances
import Azurite.AzRat.ParsableElement
import Mathlib.Algebra.Order.AbsoluteValue.Basic

/-!
# Norm Square, Length, and Measure

Computable counterparts of BPR §10.1's norm, length, and measure of a
polynomial (`Azurite.BPR.polyNorm`/`polyLength`/`polyMeasure`), for
polynomials with coefficients in an ordered ring (where `|aᵢ|² = aᵢ²`):

* `normSq p = ∑ᵢ aᵢ²` — the **square** of the norm `∥P∥ = √(∑ᵢ |aᵢ|²)`; the
  norm itself is irrational in general, but its square is exactly computable;
* `length p = ∑ᵢ |aᵢ|` — the length `Len(P)`;
* `measure p roots = |aₚ| · ∏ᵢ max(1, |zᵢ|)` — the measure `Mea(P)`,
  relative to a **given** root list, the parameterization of BPR's display
  (10.1) itself: the roots of `P` are algebraic and cannot be produced
  exactly from the coefficients, so the caller supplies them (with
  multiplicity) and the measure is exact in terms of them.

All three are single `O(n)` folds over the coefficient array (resp. the root
list).
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R]

/-- **Square of the norm**: `∥P∥² = ∑ᵢ aᵢ²`. -/
def normSq (p : AzPolynomial R) : R :=
  p.coeffs.foldl (fun acc a => acc + a * a) 0

variable {S : Type _} [Ring S] [LinearOrder S]

/-- **Length**: `Len(P) = ∑ᵢ |aᵢ|`. -/
def length (p : AzPolynomial S) : S :=
  p.coeffs.foldl (fun acc a => acc + |a|) 0

/-- **Measure** relative to a given root list:
`Mea(P) = |aₚ| · ∏ᵢ max(1, |zᵢ|)` where the `zᵢ` are supplied by the caller
(with multiplicity), per BPR display (10.1). -/
def measure (p : AzPolynomial S) (roots : List S) : S :=
  roots.foldl (fun acc z => acc * max 1 |z|) |p.leadingCoeff|

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def pp (s : String) : AzPolynomial AzInt := (parseAzPolynomial s).get!
private def pq (s : String) : AzPolynomial AzRat := (parseAzPolynomial s).get!

-- ∥3x² − 4x + 5∥² = 9 + 16 + 25
#guard normSq (pp "3*x^2-4*x+5") == (AzInt.parse "50").get!

-- Len(3x² − 4x + 5) = 3 + 4 + 5
#guard length (pp "3*x^2-4*x+5") == (AzInt.parse "12").get!

-- Mea(x² − 4) = 1 · 2 · 2 with roots ±2
#guard measure (pp "x^2-4") [(AzInt.parse "2").get!, (AzInt.parse "-2").get!]
    == (AzInt.parse "4").get!

-- roots inside the unit disc contribute 1: Mea(x² − x) = 1
#guard measure (pp "x^2-x") [(AzInt.parse "0").get!, (AzInt.parse "1").get!]
    == (AzInt.parse "1").get!

-- the leading coefficient multiplies: Mea(3x − 6) = 3 · 2
#guard measure (pp "3*x-6") [(AzInt.parse "2").get!] == (AzInt.parse "6").get!

-- Mahler-style: Mea(4x² − 1) = 4 · 1 · 1 with roots ±1/2
#guard measure (pq "4*x^2-1") [(AzRat.parse "1/2").get!, (AzRat.parse "-1/2").get!]
    == (AzRat.parse "4").get!

-- rational coefficients
#guard normSq (pq "x^2-1/2") == (AzRat.parse "5/4").get!
#guard length (pq "x^2-1/2") == (AzRat.parse "3/2").get!

-- zero polynomial
#guard normSq (0 : AzPolynomial AzInt) == 0
#guard length (0 : AzPolynomial AzInt) == 0
#guard measure (0 : AzPolynomial AzInt) [] == 0

end Tests

end Azurite.AzPolynomial
