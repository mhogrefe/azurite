/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite
import Examples.Basics

/-!
# Azurite by example

A tour of the library through things it can compute, each paired with the theorem that says the
computation is correct.  Every `#guard` below is evaluated when the file is built (`lake build`),
so this file doubles as a smoke test.  The `#guard`s run in Lean's interpreter, which is fine for
these inputs; for the compiled speed of the real thing, `lake exe examples` (`Examples/Main.lean`)
certifies a 247-digit prime in under a minute.

`Examples/Basics.lean` covers the everyday operations: constructing, printing, parsing and
casting polynomials.
-/

open Azurite

/-! ## 1. Primality of large numbers

`AzNat.isPrime` runs Miller–Rabin to reject composites quickly, then the APR-CL test
(Adleman–Pomerance–Rumely, in the Cohen–Lenstra form) to certify primes, falling back to trial
division only if APR-CL gives up.  Its verdict is a theorem, not a heuristic:

    AzNat.isPrime_eq_true_iff : isPrime n = true ↔ Nat.Prime n.toNat

Large numbers are `AzNat`s: multi-limb naturals implemented in Lean whose arithmetic is proven to
agree with `Nat`, so no step of the certification runs outside verified code. -/

/-- Parse a decimal literal as an `AzNat`. -/
def nat (s : String) : AzNat := (AzNat.parse s).get!

-- The Mersenne prime `2^127 − 1`.
#guard (nat "170141183460469231731687303715884105727").isPrime == true

-- `10^18 + 9`, the least prime above `10^18`.
#guard (nat "1000000000000000009").isPrime == true

-- `2^127 + 1` is composite (Miller–Rabin rejects it at once).
#guard (nat "170141183460469231731687303715884105729").isPrime == false

-- The smallest strong pseudoprime to the first twelve prime bases (Sorenson–Webster): the
-- twelve fixed Miller–Rabin bases accept it, and the APR-CL stage refutes it.
#guard (nat "3317044064679887385961981").isPrime == false

-- Far beyond trial division: a 78-digit Carmichael number `p₁ p₂ p₃`, built by Arnault's method
-- (`scripts/arnault_pseudoprime.py`) so that every base up to 37 is a quadratic non-residue
-- modulo each factor.  Miller–Rabin with those twelve bases accepts it; APR-CL proves it
-- composite.
def arnault78 : AzNat :=
  nat "329036778720847191859656903270547530434744909229466474573683130695545173606867"

#guard arnault78 == nat "1438716200461591714022683" * nat "450318170744478206489099467"
  * nat "507866818762941875050006747"
#guard AzNat.millerRabin arnault78 0 0 == true
#guard arnault78.isPrime == false

example (n : AzNat) : n.isPrime = true ↔ Nat.Prime n.toNat := AzNat.isPrime_eq_true_iff n

/-! ## 2. Factoring polynomials over finite fields

`AzPolynomial.factorization q f seed` is the complete factorization algorithm of von zur Gathen
and Gerhard's *Modern Computer Algebra*, Chapter 14: squarefree decomposition, distinct-degree
factorization, and Cantor–Zassenhaus equal-degree splitting.  The result is the list of monic
irreducible factors with multiplicities, and

    AzPolynomial.factorization_correct

says the factors are irreducible, pairwise distinct, and multiply back to `f`.  The coefficient
field here is `AzZMod p`, the computable `ℤ/p`. -/

section FiniteFields

open Azurite.AzPolynomial

instance : Fact (Nat.Prime (AzNat.ofNat 3).toNat) := ⟨by rw [AzNat.toNat_ofNat]; decide⟩
instance : Fact (Nat.Prime (AzNat.ofNat 7).toNat) := ⟨by rw [AzNat.toNat_ofNat]; decide⟩

/-- Parse a polynomial over `𝔽₃`. -/
def f3 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 3)) := (parseAzPolynomial s).get!
/-- Parse a polynomial over `𝔽₇`. -/
def f7 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 7)) := (parseAzPolynomial s).get!

/-- Print a factorization as `(factor, multiplicity)` pairs. -/
def showFactors {m : AzNat} [Fact (Nat.Prime m.toNat)]
    (l : List (AzPolynomial (AzZMod m) × ℕ)) : List (String × ℕ) :=
  l.map fun p => (toChars p.1, p.2)

-- `x^7 − x` splits into all seven linear factors over `𝔽₇` (Fermat's little theorem).
#guard showFactors (factorization (AzNat.ofNat 7) (f7 "x^7+6*x") 0)
  == [("x", 1), ("x+1", 1), ("x+2", 1), ("x+3", 1), ("x+4", 1), ("x+5", 1), ("x+6", 1)]

-- `x^4 + 1` is irreducible over `ℤ` but splits over every finite field; over `𝔽₃` into two
-- quadratics.
#guard showFactors (factorization (AzNat.ofNat 3) (f3 "x^4+1") 0)
  == [("x^2+x+2", 1), ("x^2+2*x+2", 1)]

-- `x^12 − 1` over `𝔽₇`: the six nonzero elements contribute linear factors, the rest is the
-- product of the three quadratics `x² + c` with `−c` a non-square.
#guard showFactors (factorization (AzNat.ofNat 7) (f7 "x^12+6") 0)
  == [("x+1", 1), ("x+2", 1), ("x+3", 1), ("x+4", 1), ("x+5", 1), ("x+6", 1),
      ("x^2+1", 1), ("x^2+2", 1), ("x^2+4", 1)]

-- Repeated factors are found with their multiplicities: `(x+1)³` over `𝔽₃`, where the
-- derivative vanishes identically and a naive squarefree step would fail.
#guard showFactors (factorization (AzNat.ofNat 3) (f3 "x^3+1") 0) == [("x+1", 3)]

end FiniteFields

/-! ## 3. Squarefree factorization of multivariate polynomials

`AzMvPolynomial.mvSquarefreeFactorization` decomposes a polynomial in `ℤ[x, y, z, …]` into
pairwise coprime squarefree parts with multiplicities, by Yun's algorithm in one variable at a
time over the tower `ℤ[y, z][x]`, recursing on the content.  The product identity

    AzMvPolynomial.mvSquarefreeFactorization_prod

is proven; the squarefreeness and coprimality of the parts are work in progress. -/

section Multivariate

instance : Fact (3 ≤ 26) := ⟨by omega⟩

/-- Parse a polynomial in `x, y, z` with integer coefficients (degrevlex order). -/
def mv (s : String) : AzMvPolynomial 3 AzInt .Degrevlex :=
  (AzMvPolynomial.parseStrWith (XyzVar 3) s).getD 0

/-- Print a factorization as `(factor, multiplicity)` pairs. -/
def showMv (l : List (AzMvPolynomial 3 AzInt .Degrevlex × ℕ)) : List (String × ℕ) :=
  l.map fun ge => (ge.1.toStrWith (XyzVar 3), ge.2)

-- `(x + y + z)² · (xy − z)`, handed over in expanded form:
-- `x³y + 2x²y² + xy³ + 2x²yz + 2xy²z + xyz² − x²z − 2xyz − y²z − 2xz² − 2yz² − z³`.
#guard showMv (AzMvPolynomial.mvSquarefreeFactorization (mv "x+y+z" * mv "x+y+z" * mv "x*y-z"))
  == [("x+y+z", 2), ("x*y-z", 1)]

-- `(x² − y²)(x − y) z³ = (x − y)² (x + y) z³`: the algorithm separates the squarefree classes.
#guard showMv (AzMvPolynomial.mvSquarefreeFactorization
    (mv "x^2-y^2" * mv "x-y" * mv "z" * mv "z" * mv "z"))
  == [("z", 3), ("x-y", 2), ("x+y", 1)]

end Multivariate

/-! ## 4. Exact linear algebra

Matrices over the computable rings, with fraction-free Bareiss elimination for determinants and
the Newton-sums characteristic polynomial of Basu–Pollack–Roy, both proven equal to Mathlib's
`Matrix.det` and `Matrix.charpoly` (`bareissDet_eq_Matrix_det`, `toPoly_charPoly`). -/

#guard
  match (AzMatrix.parseStr "[2, 1, 1; 1, 3, 2; 1, 0, 1]" : Option (AzMatrix AzRat 3 3)) with
  | some M => AzRat.toString M.bareissDet == "4"
      && AzPolynomial.toChars M.charPoly == "x^3-6*x^2+9*x-4"
  | none => false

#guard
  match (AzMatrix.parseStr "[1, 2, 3; 4, 5, 6; 7, 8, 10]" : Option (AzMatrix AzInt 3 3)) with
  | some M => toString M.bareissDet == "-3"
  | none => false
