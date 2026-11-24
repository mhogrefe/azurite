/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Data.Nat.Sqrt

/-!
# Reduced binary quadratic forms and fundamental discriminants (generator side)

Small-number bookkeeping for the certificate generator (`docs/ecpp_plan.md`, layer 3; nothing
here is proven, the certificates are checked by `ECPP.check`).  A discriminant is `−D` with
`D : ℕ` positive.

* `reducedForms D`: the reduced primitive forms `(A, B, C)` of discriminant `−D` with `B ≥ 0`,
  each with a flag telling whether `(A, −B, C)` is a different reduced form.
* `classNumber D`.
* `isFundamental D`, `primeDiscriminants D` (the factorization of `−D` into prime
  discriminants `−4`, `±8`, `(−1)^((p−1)/2) p`).
* `discriminantTable Dmax hmax`: the fundamental `D ≤ Dmax` with class number at most `hmax`,
  by increasing class number.
-/

namespace Azurite.ECPP

/-- A reduced form `(A, B, C)` with `B ≥ 0`; `paired` when `(A, −B, C)` is another reduced
form. -/
structure RedForm where
  a : Nat
  b : Nat
  c : Nat
  paired : Bool
  deriving Repr, DecidableEq

/-- The reduced primitive forms of discriminant `−D` with `B ≥ 0`. -/
def reducedForms (D : Nat) : List RedForm := Id.run do
  let mut out : List RedForm := []
  let bmax := Nat.sqrt (D / 3)
  for b in [0:bmax + 1] do
    if b % 2 == D % 2 then
      let n := (b * b + D) / 4
      if (b * b + D) % 4 == 0 then
        for a in [max b 1:Nat.sqrt n + 1] do
          if n % a == 0 then
            let c := n / a
            if Nat.gcd (Nat.gcd a b) c == 1 then
              out := ⟨a, b, c, decide (0 < b ∧ b < a ∧ a < c)⟩ :: out
  return out.reverse

/-- The class number of the discriminant `−D`. -/
def classNumber (D : Nat) : Nat :=
  (reducedForms D).foldl (fun s f => s + if f.paired then 2 else 1) 0

/-- Is `n` squarefree? (small `n`) -/
def isSquarefreeNat (n : Nat) : Bool :=
  n != 0 && (List.range (Nat.sqrt n + 1)).all fun d => d < 2 || n % (d * d) != 0

/-- Is `−D` a fundamental discriminant? -/
def isFundamental (D : Nat) : Bool :=
  (D % 4 == 3 && isSquarefreeNat D) ||
    (D % 4 == 0 && ((D / 4) % 4 == 1 || (D / 4) % 4 == 2) && isSquarefreeNat (D / 4))

/-- The odd prime factors of a squarefree-odd-part number (small `n`). -/
def oddPrimeFactors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun p =>
    p ≥ 3 && p % 2 == 1 && n % p == 0 &&
      (List.range (Nat.sqrt p + 1)).all fun d => d < 2 || p % d != 0

/-- The prime discriminants whose product is the fundamental discriminant `−D`: the odd ones
`(−1)^((p−1)/2) p` and, for even `D`, one of `−4`, `8`, `−8`. -/
def primeDiscriminants (D : Nat) : List Int :=
  let odd : List Int := (oddPrimeFactors D).map fun (p : Nat) =>
    if p % 4 == 1 then (p : Int) else -(p : Int)
  let prod := odd.foldl (· * ·) 1
  let e := -(D : Int) / prod
  if e == 1 then odd else e :: odd

/-- The fundamental `D ≤ Dmax` with class number at most `hmax`, as `(D, h)`, by increasing
class number and then increasing `D`. -/
def discriminantTable (Dmax hmax : Nat) : List (Nat × Nat) :=
  let all := ((List.range (Dmax + 1)).filter fun D => D ≥ 3 && isFundamental D).map
    fun D => (D, classNumber D)
  let kept := all.filter fun x => x.2 ≤ hmax
  (kept.toArray.qsort fun x y => x.2 < y.2 || (x.2 == y.2 && x.1 < y.1)).toList

#guard classNumber 3 = 1
#guard classNumber 23 = 3
#guard classNumber 47 = 5
#guard classNumber 71 = 7
#guard classNumber 163 = 1
#guard classNumber 84 = 4
#guard primeDiscriminants 3 = [-3]
#guard primeDiscriminants 4 = [-4]
#guard primeDiscriminants 15 = [-3, 5]
#guard primeDiscriminants 24 = [8, -3]
#guard primeDiscriminants 40 = [-8, 5]
#guard primeDiscriminants 84 = [-4, -3, -7]
#guard (discriminantTable 30 2).map (·.1) = [3, 4, 7, 8, 11, 19, 15, 20, 24]

end Azurite.ECPP
