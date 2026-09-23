/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite

/-!
# `lake exe examples`

The compiled companion of `Examples.lean`: the same computations at native speed, on inputs too
large for the interpreter that evaluates `#guard`s.  The centerpieces are the 247-digit prime
factor of `2^892 + 1` from Cohen and A. K. Lenstra's 1987 paper, certified by the proven APR-CL
test, and a 305-digit Carmichael number that passes Miller–Rabin for all twelve of Azurite's
fixed bases and is refuted by the same test.
-/

open Azurite Azurite.AzPolynomial

/-- Run `f` between two clock reads, returning its result and the elapsed milliseconds.  The
result is written to a mutable reference between the reads: the write is an effect, so the compiler
cannot move the computation out from between them (a plain `let` would be sunk to its use). -/
@[noinline] def timed {α : Type} [Inhabited α] (f : Nat → α) : IO (α × Nat) := do
  let ref ← IO.mkRef (default : α)
  let t₀ ← IO.monoMsNow
  ref.set (f t₀)
  let t₁ ← IO.monoMsNow
  let r ← ref.get
  return (r, t₁ - t₀)

/-- Report the verdicts of Miller–Rabin alone and of the full test on `n` (given in decimal),
with the time taken by the full test.  Not inlined, so that inside this function the number is a
parameter rather than a constant the compiler could evaluate ahead of time. -/
@[noinline] def reportPrime (label n : String) : IO Unit := do
  let m := (AzNat.parse n).get!
  let mr := AzNat.millerRabin m 0 0
  let (verdict, ms) ← timed fun _ => AzNat.isPrime m
  IO.println s!"{label} ({n.length} digits):"
  IO.println s!"  Miller–Rabin, twelve fixed bases: {if mr then "passes" else "rejected"}"
  IO.println s!"  isPrime (APR-CL):                {if verdict then "prime" else "composite"} \
    ({ms} ms)"

instance : Fact (Nat.Prime (AzNat.ofNat 7).toNat) := ⟨by rw [AzNat.toNat_ofNat]; decide⟩

/-- Factor a polynomial over `𝔽₇` given as a string. -/
@[noinline] def reportFactorization (s : String) : IO Unit := do
  let f := (parseAzPolynomial s : Option (AzPolynomial (AzZMod (AzNat.ofNat 7)))).get!
  let (factors, ms) ← timed fun _ => factorization (AzNat.ofNat 7) f 0
  let shown := factors.map fun p =>
    if p.2 == 1 then s!"({toChars p.1})" else s!"({toChars p.1})^{p.2}"
  IO.println s!"{toChars f} = {" · ".intercalate shown}  ({ms} ms)"

instance : Fact (3 ≤ 26) := ⟨by omega⟩

/-- Squarefree-factor the product of the polynomials in `ℤ[x, y, z]` given as strings. -/
@[noinline] def reportSquarefree (factors : List String) : IO Unit := do
  let mv (s : String) : AzMvPolynomial 3 AzInt .Degrevlex :=
    (AzMvPolynomial.parseStrWith (XyzVar 3) s).getD 0
  let g := (factors.map mv).foldl (· * ·) 1
  let (parts, ms) ← timed fun _ => AzMvPolynomial.mvSquarefreeFactorization g
  let shown := parts.map fun ge =>
    if ge.2 == 1 then s!"({ge.1.toStrWith (XyzVar 3)})"
    else s!"({ge.1.toStrWith (XyzVar 3)})^{ge.2}"
  IO.println s!"{g.toStrWith (XyzVar 3)}"
  IO.println s!"  = {" · ".intercalate shown}  ({ms} ms)"

/-- A 305-digit Carmichael number `p₁ p₂ p₃` from Arnault's construction
(`scripts/arnault_pseudoprime.py`): every base up to 37 is a quadratic non-residue modulo each
factor, so it is a strong pseudoprime to all twelve fixed Miller–Rabin bases. -/
def arnault305 : String :=
  "41242747005721162038548341321499615152910657163605971213313452876675832289811005186576688893327893992003242562715703015455677688583475223875165817012584772042407486282863527575008147582507834622927667539942460507392492236948171947378700497551379308182002071044516339445432076900995805343523469691342679867"

def main : IO Unit := do
  IO.println "── Primality: Miller–Rabin rejection, then the proven APR-CL test ──"
  reportPrime "2^127 − 1" "170141183460469231731687303715884105727"
  reportPrime "The smallest strong pseudoprime to twelve bases" "3317044064679887385961981"
  reportPrime "The 180-digit prime of Cohen–Lenstra, Table 4" (toString CL.prime180_table2)
  reportPrime "The 247-digit prime factor of 2^892 + 1" (toString CL.prime247_2_892)
  reportPrime "A 305-digit Carmichael number (Arnault's construction)" arnault305
  IO.println ""
  IO.println "── Factorization over 𝔽₇ (AzPolynomial.factorization) ──"
  reportFactorization "x^12+6"
  IO.println ""
  IO.println "── Squarefree factorization in ℤ[x, y, z] (AzMvPolynomial.mvSquarefreeFactorization) ──"
  reportSquarefree ["x+y+z", "x+y+z", "x*y-z"]
