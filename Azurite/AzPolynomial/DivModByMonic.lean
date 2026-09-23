/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Sub
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Parse

import Mathlib.Algebra.Ring.Defs

/-!
# Division by a Monic Polynomial over an arbitrary `CommRing`

This module implements Euclidean division of a polynomial `P` by a **monic**
polynomial `f`, over any commutative ring `R` — **no field / inverse required**.

Because `f` is monic, subtracting `c • X^k * f` (where `c` is the leading
coefficient of the running remainder and `k` is the degree gap) cancels the
remainder's leading term exactly, without ever dividing a coefficient.  This is
the polynomial analogue of `AzNat.mod` used to build `AzZMod`, and it is the
reduction primitive underlying `AzPolyMod` (`R[x] / (f)`).

## Algorithm (`divModByMonicAux`)

Starting from `rem := P`, `quo := 0`, while `deg rem ≥ deg f` (and `rem ≠ 0`):
- `c := leadingCoeff rem`, `k := natDegree rem − natDegree f`;
- `rem := rem − c • (X^k * f)` (cancels the leading term since `f` is monic);
- `quo := quo + c • X^k`.

Termination is by an explicit fuel counter (`P.coeffs.size + 1` steps suffice for
monic `f`, since each step drops the degree by at least one).  On the fuel-out
branch the remainder is reset to `0` so that the returned remainder **always**
satisfies `deg < deg f` (`divModByMonicAux_rem_size`) for any `f`, monic or not —
this is what makes the `AzPolyMod` reduced invariant provable without a monic
hypothesis.  For monic `f` the fuel-out branch is never reached, so the result is
the genuine quotient/remainder pair.

Phase-2 correctness (`P = divByMonic P f * f + modByMonic P f` and monic-ness
assumptions) will mirror the `QuoRem` / `ExactDiv` equivalence proofs.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- Fuel-driven core of division by a monic polynomial.

Returns `(quotient-so-far-contribution, remainder)`.  `rem` is the running
remainder; each recursive step shaves its leading term using the monic divisor
`f`.  The fuel-out branch (`0, rem` with `deg rem ≥ deg f`) resets the remainder
to `0`, guaranteeing `deg (result.2) < deg f` unconditionally (see
`divModByMonicAux_rem_size`). -/
def divModByMonicAux (f : AzPolynomial R) : ℕ → AzPolynomial R → AzPolynomial R × AzPolynomial R
  | 0, rem => (0, if rem.coeffs.size < f.coeffs.size then rem else 0)
  | fuel + 1, rem =>
    if rem.coeffs.size < f.coeffs.size then (0, rem)
    else
      let k := rem.natDegree - f.natDegree
      let c := rem.leadingCoeff
      let m := monomial k c          -- `c * X^k`
      let rem' := rem - mulBasecaseFold m f   -- subtract `c * X^k * f`
      let res := divModByMonicAux f fuel rem'
      (m + res.1, res.2)

/-- **Division by a monic polynomial.** Returns `(quotient, remainder)` with
`P = quotient * f + remainder` and `deg remainder < deg f` when `f` is monic. -/
def divModByMonic (P f : AzPolynomial R) : AzPolynomial R × AzPolynomial R :=
  divModByMonicAux f (P.coeffs.size + 1) P

/-- The remainder of `P` modulo the monic polynomial `f`. -/
def modByMonic (P f : AzPolynomial R) : AzPolynomial R := (divModByMonic P f).2

/-- The quotient of `P` divided by the monic polynomial `f`. -/
def divByMonic (P f : AzPolynomial R) : AzPolynomial R := (divModByMonic P f).1

/-- The remainder produced by `divModByMonicAux` always has size (hence degree)
strictly below `f`, for **any** `f` with `0 < f.coeffs.size`.  This is the
`AzPolyMod` reduced-invariant lemma; it needs no monic hypothesis because the
fuel-out branch resets the remainder to `0`. -/
theorem divModByMonicAux_rem_size (f : AzPolynomial R) (hf : 0 < f.coeffs.size) :
    ∀ (fuel : ℕ) (rem : AzPolynomial R),
      (divModByMonicAux f fuel rem).2.coeffs.size < f.coeffs.size := by
  intro fuel
  induction fuel with
  | zero =>
    intro rem
    simp only [divModByMonicAux]
    split
    · assumption
    · simpa using hf
  | succ n ih =>
    intro rem
    simp only [divModByMonicAux]
    split
    · assumption
    · exact ih _

/-- The remainder `modByMonic P f` has size (hence degree) strictly below `f`
whenever `f` is nonzero. -/
theorem modByMonic_coeffs_size_lt (P f : AzPolynomial R) (hf : 0 < f.coeffs.size) :
    (modByMonic P f).coeffs.size < f.coeffs.size :=
  divModByMonicAux_rem_size f hf _ P

end Azurite.AzPolynomial

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzPolynomial

/-- Divide `P` by monic `f` and render `(quotient, remainder)` as strings. -/
private def divModStr (P f : String) : String × String :=
  let p := (parseAzPolynomial (R := AzInt) P).get!
  let g := (parseAzPolynomial (R := AzInt) f).get!
  let (q, r) := divModByMonic p g
  (toChars q, toChars r)

-- (x^2 + 2x + 1) / (x + 1) = (x + 1, 0)
#guard divModStr "x^2+2*x+1" "x+1" == ("x+1", "0")
-- (x^2 + 1) / (x + 1) = (x - 1, 2)
#guard divModStr "x^2+1" "x+1" == ("x-1", "2")
-- (x^3 - 2x + 1) / (x^2 + 1) = (x, -3x + 1)
#guard divModStr "x^3-2*x+1" "x^2+1" == ("x", "-3*x+1")
-- (x^3) / (x^2 - x - 1) = (x + 1, 2x + 1)   [Fibonacci-style monic]
#guard divModStr "x^3" "x^3-x-1" == ("1", "x+1")
-- deg P < deg f: (x + 1) / (x^2 + 1) = (0, x + 1)
#guard divModStr "x+1" "x^2+1" == ("0", "x+1")
-- P = 0
#guard divModStr "0" "x^2+1" == ("0", "0")

-- Reconstruction  P = q * f + r  (integer coefficients, monic divisor).
private def reconstructs (P f : String) : Bool :=
  let p := (parseAzPolynomial (R := AzInt) P).get!
  let g := (parseAzPolynomial (R := AzInt) f).get!
  let (q, r) := divModByMonic p g
  toChars (q * g + r) == toChars p

#guard reconstructs "x^4+3*x^2+7" "x^2+1"
#guard reconstructs "5*x^5-4*x^3+2*x-9" "x^3-x-1"
#guard reconstructs "x^2+2*x+1" "x+1"
#guard reconstructs "7" "x^2+1"

end Tests
