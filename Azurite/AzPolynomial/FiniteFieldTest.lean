/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **The finite field primality test** (C&P Algorithm 4.3.4, complete):
  the certificate checker `lenstraTest` wrapped in the usual
  random-head, exhaustive-tail candidate search.

  Per attempt index `i`, the witness pair is drawn from the hybrid
  polynomial stream of the equal-degree-splitting arc
  (`hybridPolyCandidate`: pseudorandom for the first `2^64` indices,
  then the exhaustive bounded-degree enumeration — practically
  random, provably surjective): `f := x^I + (stream at (unpair i).1)`
  ranges over ALL monic polynomials of degree `I`, and
  `g := stream at (unpair i).2` over all polynomials of degree `< I`;
  the `Nat.unpair` split makes the PAIR stream surjective, which is
  what a future completeness theorem needs.  The book's algorithm
  keeps `f` fixed while resampling `g` — a running-time optimization;
  we resample the pair, which has the same verdict semantics.

  Soundness is pure verdict pass-through from the checker: whichever
  attempt returns `some b` proves primality (`b = true`) or
  compositeness (`b = false`) of `n` outright
  (`finiteFieldTest_eq_some_true` / `_eq_some_false`, in
  `Azurite/AzPolynomial/Equiv/FiniteFieldTest.lean`).  `none` after
  all attempts is inconclusive.  Completeness (a prime `n` gets
  `some true` once the exhaustive tail reaches a valid witness pair,
  which `exists_lenstra_witness` provides) is deferred, as for the
  `n − 1` test.
-/
import Azurite.AzPolynomial.LenstraTest
import Azurite.AzPolynomial.EqualDegreeSplitting

namespace Azurite.AzPolynomial

variable {m : AzNat}

/-- The attempt-`i` witness pair: a monic degree-`I` candidate `f` and
a degree-`< I` candidate `g`, from independent (unpaired) indices of
the hybrid stream. -/
def witnessPair (m : AzNat) [NeZero m.toNat] (I : ℕ) (seed : UInt64)
    (i : ℕ) : AzPolynomial (AzZMod m) × AzPolynomial (AzZMod m) :=
  (monomial I 1 + hybridPolyCandidate (AzZMod m) seed I (Nat.unpair i).1,
    hybridPolyCandidate (AzZMod m) seed I (Nat.unpair i).2)

/-- The attempt loop: run the certificate checker on successive
witness pairs until it reaches a verdict. -/
def finiteFieldTestAux (m : AzNat) [NeZero m.toNat] (I : ℕ) (F : AzNat)
    (qs : List AzNat) (seed : UInt64) : ℕ → ℕ → Option Bool
  | 0, _ => none
  | attempts + 1, i =>
    match lenstraTest m I F qs (witnessPair m I seed i).1
        (witnessPair m I seed i).2 with
    | some b => some b
    | none => finiteFieldTestAux m I F qs seed attempts (i + 1)

/-- **The finite field primality test** (C&P Algorithm 4.3.4): given
`F ∣ n^I − 1` with `F ≥ √n` and the prime factorization `qs` of `F`,
search `attempts` hybrid-stream witness pairs.  `some true` PROVES
`n` prime, `some false` proves `n` composite, `none` is
inconclusive. -/
def finiteFieldTest (m : AzNat) [NeZero m.toNat] (I : ℕ) (F : AzNat)
    (qs : List AzNat) (attempts : ℕ) (seed : UInt64) : Option Bool :=
  finiteFieldTestAux m I F qs seed attempts 0

end Azurite.AzPolynomial

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzPolynomial

-- `3` proven prime through a random `GF(9)` certificate
#guard finiteFieldTest (AzNat.ofNat 3) 2 (AzNat.ofNat 8)
  [AzNat.ofNat 2, AzNat.ofNat 2, AzNat.ofNat 2] 50 0 == some true

-- `7` proven prime through a random `GF(49)` certificate
#guard finiteFieldTest (AzNat.ofNat 7) 2 (AzNat.ofNat 48)
  [AzNat.ofNat 2, AzNat.ofNat 2, AzNat.ofNat 2, AzNat.ofNat 2,
   AzNat.ofNat 3] 50 0 == some true

-- `15` proven composite (a random witness fails the Fermat check)
#guard finiteFieldTest (AzNat.ofNat 15) 1 (AzNat.ofNat 14)
  [AzNat.ofNat 2, AzNat.ofNat 7] 50 0 == some false

-- the base-2 pseudoprime `341 = 11·31`: a random witness betrays it
#guard finiteFieldTest (AzNat.ofNat 341) 1 (AzNat.ofNat 340)
  [AzNat.ofNat 2, AzNat.ofNat 2, AzNat.ofNat 5, AzNat.ofNat 17]
  50 0 == some false

-- invalid certificate data is never conclusive
#guard finiteFieldTest (AzNat.ofNat 5) 1 (AzNat.ofNat 3)
  [AzNat.ofNat 3] 50 0 == none

end Tests
