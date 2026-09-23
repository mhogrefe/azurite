/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **The finite field primality certificate checker** — the
  deterministic core of C&P Algorithm 4.3.4 (steps 2–4, plus the
  step-1 irreducibility test), executable for `n` of UNKNOWN
  primality.

  Inputs: `n`, the extension degree `I`, `F ∣ n^I − 1` with its prime
  factor list `qs` (with multiplicity), and the candidate witnesses
  `f, g ∈ Z_n[x]` (`f` monic of degree `I`, `g` nonzero of degree
  `< I`).  The checker validates the certificate data, then:

  1. runs the optimistic irreducibility sweep on `f`
     (`irreducibleOrFactor`);
  2. verifies `g^(n^I−1) ≡ 1 (mod f)` and, for each `q ∈ qs`,
     `gcd(g^((n^I−1)/q) − 1, f) = 1` — powers by `powModByMonic`,
     gcds by `gcdOrFactor`, so failures exhibit factors of `n`;
  3. forms `(T − g)(T − g^n) ⋯ (T − g^(n^(I−1)))` mod `f` by the
     coefficient recursion for multiplication by `T − a`
     (`mulLin`), and checks every coefficient is constant;
  4. searches `n^j mod F` (`1 ≤ j < I`) for a proper factor of `n`.

  Verdicts (`Option Bool`): `some true` — `n` is PROVEN prime
  (`lenstraTest_eq_some_true`); `some false` — `n` is proven
  composite (a factor was exhibited, or a condition failed that
  Theorem 4.3.3's witness theory guarantees for primes);
  `none` — inconclusive (invalid certificate data, or `f`/`g` is
  not a valid witness — the caller should resample).  Soundness
  lives in `Azurite/AzPolynomial/Equiv/LenstraTest.lean`.
-/
import Azurite.AzPolynomial.IrreducibleOrFactor
import Azurite.AzNat.IsPrime
import Azurite.AzNat.Pow

namespace Azurite.AzPolynomial

section MulLin

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- Tail of the coefficient recursion for `(T − a)·P mod f`: `prev` is
the coefficient one index below the current one. -/
def mulLinAux (f a : AzPolynomial R) (prev : AzPolynomial R) :
    List (AzPolynomial R) → List (AzPolynomial R)
  | [] => [prev]
  | c :: cs => modByMonic (prev - a * c) f :: mulLinAux f a c cs

/-- Coefficients of `(T − a) · P` from those of `P` (ascending lists
over `R[x]`), every entry reduced mod the monic `f`. -/
def mulLin (f a : AzPolynomial R) :
    List (AzPolynomial R) → List (AzPolynomial R)
  | [] => []
  | c :: cs => modByMonic (-(a * c)) f :: mulLinAux f a c cs

/-- The Frobenius conjugate list `[g, g^q, g^(q²), …]` (length `I`),
each entry reduced mod `f`. -/
def conjugates (f : AzPolynomial R) (q : AzNat) :
    AzPolynomial R → ℕ → List (AzPolynomial R)
  | _, 0 => []
  | g, I + 1 => g :: conjugates f q (powModByMonic g q f) I

end MulLin

variable {m : AzNat} [NeZero m.toNat]

/-- Coefficients (ascending, in `Z_m[x]`, reduced mod `f`) of
`(T − g)(T − g^m) ⋯ (T − g^(m^(I−1)))`. -/
def symCoeffs (f g : AzPolynomial (AzZMod m)) (I : ℕ) :
    List (AzPolynomial (AzZMod m)) :=
  (conjugates f m (modByMonic g f) I).foldl (fun cs a => mulLin f a cs) [1]

/-- Step 2's per-prime loop: check `gcd(g^(N/q) − 1, f) = 1` for each
`q`, through `gcdOrFactor`. -/
def primitiveLoop (f g : AzPolynomial (AzZMod m)) (N : AzNat) :
    List AzNat → AzNat ⊕ Bool
  | [] => .inr true
  | q :: qs =>
    match gcdOrFactor m (powModByMonic g (N / q) f - 1) f with
    | .inl d => .inl d
    | .inr w => if w = 1 then primitiveLoop f g N qs else .inr false

/-- Step 4: does some residue `n^j mod F` (`1 ≤ j < I`) exhibit a
proper factor of `n`? -/
def divisorSearch (n F : AzNat) (I : ℕ) : Bool :=
  (List.range I).any fun j =>
    decide (0 < j ∧ AzNat.ofNat 1 < n.pow j % F ∧ n.pow j % F < n
      ∧ n % (n.pow j % F) = 0)

/-- **The finite field primality certificate checker** (C&P Algorithm
4.3.4 for given witnesses): `some true` proves `n` prime, `some false`
proves `n` composite, `none` is inconclusive (resample `f`, `g`). -/
def lenstraTest (n : AzNat) [NeZero n.toNat] (I : ℕ) (F : AzNat)
    (qs : List AzNat) (f g : AzPolynomial (AzZMod n)) : Option Bool :=
  if ¬(AzNat.ofNat 1 < n ∧ 0 < I ∧ f.Monic ∧ f.natDegree = I ∧ g ≠ 0
      ∧ g.natDegree < I ∧ qs.all AzNat.isPrime
      ∧ qs.foldl (· * ·) (AzNat.ofNat 1) = F
      ∧ (n.pow I - 1) % F = 0 ∧ n ≤ F * F) then none
  else
    match irreducibleOrFactor n f with
    | .inl _ => some false
    | .inr false => none
    | .inr true =>
      if powModByMonic g (n.pow I - 1) f ≠ 1 then some false
      else
        match primitiveLoop f g (n.pow I - 1) qs with
        | .inl _ => some false
        | .inr false => none
        | .inr true =>
          if ¬(symCoeffs f g I).all (fun c => c.natDegree == 0) then
            some false
          else if divisorSearch n F I then some false
          else some true

end Azurite.AzPolynomial

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzPolynomial

private instance : Fact (1 < (AzNat.ofNat 3).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; omega⟩

private instance : Fact (1 < (AzNat.ofNat 5).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; omega⟩

private instance : Fact (1 < (AzNat.ofNat 15).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; omega⟩

private instance : Fact (1 < (AzNat.ofNat 341).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; omega⟩

private def t3 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 3)) :=
  (parseAzPolynomial s).get!

private def t5 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 5)) :=
  (parseAzPolynomial s).get!

private def t15 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 15)) :=
  (parseAzPolynomial s).get!

private def t341 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 341)) :=
  (parseAzPolynomial s).get!

-- `3` proven prime in the degenerate band `I = 1` (`F = 2`, `f = x`, `g = 2`)
#guard lenstraTest (AzNat.ofNat 3) 1 (AzNat.ofNat 2) [AzNat.ofNat 2]
  (t3 "x") (t3 "2") == some true

-- `3` proven prime through a REAL quadratic extension: `GF(9)`,
-- `F = 8 = 3² − 1`, `f = x² + 1`, `g = x + 1` a primitive element
#guard lenstraTest (AzNat.ofNat 3) 2 (AzNat.ofNat 8)
  [AzNat.ofNat 2, AzNat.ofNat 2, AzNat.ofNat 2]
  (t3 "x^2+1") (t3 "x+1") == some true

-- `15` proven composite by the Fermat check (`2^14 ≡ 4 (mod 15)`)
#guard lenstraTest (AzNat.ofNat 15) 1 (AzNat.ofNat 14)
  [AzNat.ofNat 2, AzNat.ofNat 7] (t15 "x") (t15 "2") == some false

-- `341 = 11·31` is a base-2 Fermat pseudoprime: the Fermat check
-- passes, but `g = 2` fails the primitivity check — inconclusive
#guard lenstraTest (AzNat.ofNat 341) 1 (AzNat.ofNat 340)
  [AzNat.ofNat 2, AzNat.ofNat 2, AzNat.ofNat 5, AzNat.ofNat 17]
  (t341 "x") (t341 "2") == none

-- a reducible `f` is rejected as a witness (inconclusive, resample)
#guard lenstraTest (AzNat.ofNat 5) 2 (AzNat.ofNat 24)
  [AzNat.ofNat 2, AzNat.ofNat 2, AzNat.ofNat 2, AzNat.ofNat 3]
  (t5 "x^2+1") (t5 "x+1") == none

-- invalid certificate data (`F ∤ n^I − 1`) is rejected
#guard lenstraTest (AzNat.ofNat 5) 1 (AzNat.ofNat 3) [AzNat.ofNat 3]
  (t5 "x") (t5 "2") == none

end Tests
