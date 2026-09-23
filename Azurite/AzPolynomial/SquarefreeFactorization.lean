/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Compare
import Azurite.AzPolynomial.Gcd
import Azurite.AzPolynomial.Pow

/-!
# Yun's square-free factorization (GCL Algorithm 8.2)

Geddes–Czapor–Labahn, *Algorithms for Computer Algebra*, Algorithm 8.2
(`SquareFree2`): given a normalized polynomial `a` (primitive over a UFD of
characteristic zero; monic over a field), compute its square-free
factorization — a list of pairs `(gᵢ, i)` with each `gᵢ` square-free and
`∏ gᵢ^i = a`.

The algorithm: `b := a′`, `c := gcd(a, b)`. If `c` is constant, `a` is
already square-free (output `[(a, 1)]`). Otherwise `w := a/c`,
`y := b/c`, `z := y − w′`, and while `z ≠ 0`:
`g := gcd(w, z)`, emit `(g, i)`, `w := w/g`, `y := z/g`, `z := y − w′`;
finally emit `(w, i)`.

Interpretation notes on the GCL pseudocode: `g(x) + GCD(w(x), z(x))` reads
`g := gcd(w, z)`; `Output ++ g(x)^i` appends the *pair* `(g, i)`; in the
`c = 1` branch the loop is skipped and the trailing `Output ++ w^i` (with
`i = 1`) emits `(a, 1)`. One standard subtlety the pseudocode glosses over:
when `a` has no factors of multiplicity `i`, the corresponding `gᵢ` is a
constant — we *filter these out*, so every output polynomial is nonconstant
square-free and the exponents are strictly increasing (giving a canonical,
ordered, duplicate-free output). All gcds delegate to the `GcdImpl`
normalized gcd (monic over a field, primitive-positive over `ℤ`), and the
divisions are exact.

The loop is fueled by `deg a` (the multiplicity of any factor is at most
`deg a`, so the fuel is never exhausted on legitimate inputs).
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R] [GcdImpl R]
  [PolynomialDerivative R]

/-- The Yun loop: at entry `w` is the product of the remaining square-free
classes, and `z = y − w′` drives the next gcd. Emits `(gcd(w, z), i)` per
round (constants filtered), then the final `(w, i)`. -/
def yunLoop : (fuel : ℕ) → (i : ℕ) → (w z : AzPolynomial R) →
    (acc : List (AzPolynomial R × ℕ)) → List (AzPolynomial R × ℕ)
  | 0, i, w, _, acc => acc ++ [(w, i)]
  | fuel + 1, i, w, z, acc =>
    if z = 0 then acc ++ [(w, i)]
    else
      let g := gcd w z
      let w' := (exactDivQuoRem w g).1
      let y' := (exactDivQuoRem z g).1
      yunLoop fuel (i + 1) w' (y' - derivative w')
        (if g.natDegree = 0 then acc else acc ++ [(g, i)])

/-- The Yun run in its natural (multiplicity-ascending) order — the core of
`squarefreeFactorization`, which sorts this output canonically. -/
def squarefreeFactorizationCore (a : AzPolynomial R) : List (AzPolynomial R × ℕ) :=
  if a.natDegree = 0 then []
  else
    let b := derivative a
    let c := gcd a b
    if c.natDegree = 0 then [(a, 1)]
    else
      let w := (exactDivQuoRem a c).1
      let y := (exactDivQuoRem b c).1
      yunLoop a.natDegree 1 w (y - derivative w) []

/-- **Yun's square-free factorization** (GCL Algorithm 8.2). For a
normalized input (monic over a field; primitive with positive leading
coefficient over `ℤ`), returns the square-free factorization
`[(g₁, e₁), …, (gₖ, eₖ)]` with each `gᵢ` nonconstant square-free and
pairwise coprime, `∏ gᵢ^{eᵢ} = a`, and the `gᵢ` **strictly increasing in
the canonical polynomial order** (degree, then top-down lexicographic —
factor lists ascend, as in `60 = 2²·3·5`). Constants return `[]` (the
empty product — a normalized constant is `1`). -/
def squarefreeFactorization [LinearOrder R] (a : AzPolynomial R) :
    List (AzPolynomial R × ℕ) :=
  (squarefreeFactorizationCore a).mergeSort (fun gi gj => gi.1 ≤ gj.1)

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def pp (s : String) : AzPolynomial AzInt := (parseAzPolynomial s).get!
private def pq (s : String) : AzPolynomial AzRat := (parseAzPolynomial s).get!

-- squarefree input: a single pair at exponent 1
#guard (squarefreeFactorization (pp "x^2+1")).map (fun gi => (toChars gi.1, gi.2))
  == [("x^2+1", 1)]
-- `(X−1)(X+2)²`: two classes, `x−1 < x+2` in the canonical order
#guard (squarefreeFactorization (pp "x^3+3*x^2-4")).map (fun gi => (toChars gi.1, gi.2))
  == [("x-1", 1), ("x+2", 2)]
-- `(X−1)³(X+1)`: gap at multiplicity 2 filtered; sorted `x−1 < x+1`,
-- so the exponents are NOT monotone — the polynomials are
#guard (squarefreeFactorization (pp "x^4-2*x^3+2*x-1")).map (fun gi => (toChars gi.1, gi.2))
  == [("x-1", 3), ("x+1", 1)]
-- pure power `(X+2)³` — in particular `(X+2)⁵` yields ONE pair, never
-- split across duplicate polynomials
#guard (squarefreeFactorization (pp "x^3+6*x^2+12*x+8")).map (fun gi => (toChars gi.1, gi.2))
  == [("x+2", 3)]
#guard (squarefreeFactorization (pp "x^5+10*x^4+40*x^3+80*x^2+80*x+32")).map
    (fun gi => (toChars gi.1, gi.2))
  == [("x+2", 5)]
-- the GCL running example shape: `(X²+1)(X−1)²(X+3)³`, ascending:
-- `x−1 < x+3 < x²+1` (degree first, then top-down lexicographic)
#guard (squarefreeFactorization
    (pp "x^7+7*x^6+11*x^5-11*x^4-17*x^3+9*x^2-27*x+27")).map
    (fun gi => (toChars gi.1, gi.2))
  == [("x-1", 2), ("x+3", 3), ("x^2+1", 1)]
-- product check on the previous example
#guard (let f := squarefreeFactorization
          (pp "x^7+7*x^6+11*x^5-11*x^4-17*x^3+9*x^2-27*x+27")
        toChars ((f.map (fun gi => gi.1.pow gi.2)).foldl (· * ·) 1)
          == "x^7+7*x^6+11*x^5-11*x^4-17*x^3+9*x^2-27*x+27")
-- monic over `AzRat`
#guard (squarefreeFactorization (pq "x^3-3/2*x^2+3/4*x-1/8")).map
    (fun gi => (toChars gi.1, gi.2))
  == [("x-1/2", 3)]
-- constants
#guard squarefreeFactorization (pp "1") == []

end Tests

end Azurite.AzPolynomial
