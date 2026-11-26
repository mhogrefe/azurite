/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Check
import Azurite.ECPP.Gen.Modular
import Azurite.AzNat.Gcd
import Azurite.AzNat.SqrtRem

/-!
# Elliptic curve primality proving: certificates for exchange

The checker's `StepCert` carries a point of order `q`.  The certificates other programs
write and read carry instead the order `m = c q` of the curve and a point `P` that has not
yet been multiplied by the cofactor `c`.  An `ExportStep` is that record:

* `n`: the number the step proves prime; `D`: the discriminant of the curve's complex
  multiplication (for information only: nothing reads it, `0` when unknown);
* the curve `y² = x³ + ax + b` over `ℤ/n`; its order `m`; the next number `q`, a divisor of
  `m` with `m/q > 1`; the point `P = (x, y)`.

A certificate is a list of steps in a chain: the first `n` is the number to be proven prime,
and the `n` of every later step is the `q` of the step before it.

`toStepCert` multiplies `P` by `m/q` and gives the `StepCert` with the affine result;
`checkExport` checks the chain and runs the proven `check` on the converted steps (an empty
certificate is for an `n` of at most 64 bits, settled by `AzNat.isPrimeAprcl`).  Soundness
(`Equiv/Export.lean`): `checkExport n cert = true → Nat.Prime n.toNat`.

Two text formats, each with a printer and a parser that skips white space:

* **multi-line** (`printFlint`, `parseFlint`):

      ecpp certificate, <k> steps
      [0] n = <n>
          D = <D>
          a = <a>
          b = <b>
          m = <m>
          q = <q>
          x = <x>
          y = <y>
      [1] n = …

* **one line** (`printPari`, `parsePari`): `[[N, t, s, a, [x, y]], …]` with `N = n`,
  `t = n + 1 − m` (signed) and `s = m/q`; `[]` for the empty certificate.  `b` is not
  written: the parser takes `b = y² − x³ − ax mod N`, `m = N + 1 − t`, `q = m/s` (which must
  be exact) and `D = 0`.

Numbers are decimal without leading zeros.
-/

namespace Azurite.ECPP

open AzZMod

/-- **One step of a certificate for exchange**: see the file header. -/
structure ExportStep where
  n : AzNat
  D : AzNat
  a : AzNat
  b : AzNat
  m : AzNat
  q : AzNat
  x : AzNat
  y : AzNat
  deriving DecidableEq

/-- **The checker's step from an exchange step** for `n`: the point `(m/q) · (x, y)` in
affine coordinates.  `none` if `q` does not divide `m`, if `m/q ≤ 1`, or if the multiple is
not an affine point modulo `n` (the point at infinity, or a `Z` that is not invertible). -/
def toStepCert (n : AzNat) (e : ExportStep) : Option StepCert :=
  if h : 1 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    if e.q = 0 then none
    else
      let c := e.m / e.q
      if e.m % e.q ≠ 0 ∨ c ≤ 1 then none
      else
        let a := ofAzNat n e.a
        match jacMul a (ofAzNat n e.x) (ofAzNat n e.y) (c.size + 1) c with
        | none => none
        | some V =>
          match V.2.2.inv? with
          | none => none
          | some zi =>
            let zi2 := Square.square zi
            some ⟨a.val, (ofAzNat n e.b).val, (V.1 * zi2).val, (V.2.1 * (zi2 * zi)).val, e.q⟩
  else none

/-- The steps form a chain from `n`. -/
def chainFrom : AzNat → List ExportStep → Bool
  | _, [] => true
  | n, e :: es => decide (e.n = n) && chainFrom e.q es

/-- **The checker of a certificate for exchange**: the chain, the conversion of every step,
and the proven `check`; the empty certificate is accepted for a prime `n` of at most 64
bits. -/
def checkExport (n : AzNat) (cert : List ExportStep) : Bool :=
  if cert.isEmpty then decide (n.size ≤ 64) && n.isPrimeAprcl
  else
    chainFrom n cert &&
      match cert.mapM fun e => toStepCert e.n e with
      | some cs => check n cs
      | none => false

/-! ## The conditions of other verifiers

Other verifiers ask of a step `(⌊√q⌋ − 1)⁴ > n` where `checkStep` asks, with `s = ⌊√n⌋`,
`s + 1 < q` and `4s < (q − s − 1)²`.  The first implies the second
(`strictBound_nat`, `Equiv/Export.lean`), and the search only takes steps that satisfy it, so
that its certificates are accepted elsewhere too. -/

/-- **The bound of other verifiers**: `(⌊√q⌋ − 1)⁴ > n`. -/
def strictBound (n q : AzNat) : Bool :=
  let r := AzNat.sqrt q - AzNat.ofNat 1
  let r2 := r * r
  decide (n < r2 * r2)

/-- The conditions of other verifiers on one step: `q ∣ m` with `m/q > 1`; `strictBound`;
`n > 3` and `gcd(n, 6) = 1`; the point lies on the curve. -/
def strictStep (e : ExportStep) : Bool :=
  decide (e.q ≠ 0) && decide (e.m % e.q = 0) && decide (1 < e.m / e.q)
    && strictBound e.n e.q
    && decide (3 < e.n) && decide (AzNat.gcd e.n (AzNat.ofNat 6) = 1)
    && decide (e.y * e.y % e.n = (e.x * e.x * e.x + e.a * e.x + e.b) % e.n)

/-- The conditions of other verifiers on a certificate for `n`: those on every step, and at
most 64 bits in the last `q` (in `n` for the empty certificate). -/
def strictCert (n : AzNat) (cert : List ExportStep) : Bool :=
  cert.all strictStep && decide (((cert.getLast?.map (·.q)).getD n).size ≤ 64)

/-! ## The multi-line format -/

/-- A decimal number without sign or leading zeros. -/
def parseDecimal (cs : List Char) : Option AzNat :=
  if cs.isEmpty || !cs.all Char.isDigit || (cs.length > 1 && cs.head? == some '0') then none
  else AzNat.parse (String.ofList cs)

/-- The names of the fields of a step, in the order of the multi-line format. -/
def fieldNames : List String := ["n", "D", "a", "b", "m", "q", "x", "y"]

/-- **Print a certificate in the multi-line format.** -/
def printFlint (cert : List ExportStep) : String :=
  s!"ecpp certificate, {cert.length} steps\n" ++
    String.join (cert.zipIdx.map fun (e, i) =>
      s!"[{i}] n = {e.n}\n    D = {e.D}\n    a = {e.a}\n    b = {e.b}\n    m = {e.m}\n" ++
        s!"    q = {e.q}\n    x = {e.x}\n    y = {e.y}\n")

/-- `name = value` for each of the names, from a list of words: the values and the rest. -/
def parseFields : List String → List String → Option (List AzNat × List String)
  | [], ts => some ([], ts)
  | f :: fs, t :: eq :: v :: ts =>
    if t = f ∧ eq = "=" then do
      let x ← parseDecimal v.toList
      let (xs, rest) ← parseFields fs ts
      pure (x :: xs, rest)
    else none
  | _, _ => none

/-- `k` steps numbered from `i`, from a list of words that they must use up. -/
def parseFlintSteps : Nat → Nat → List String → Option (List ExportStep)
  | 0, _, ts => if ts.isEmpty then some [] else none
  | k + 1, i, t :: ts =>
    if t = s!"[{i}]" then
      match parseFields fieldNames ts with
      | some ([n, D, a, b, m, q, x, y], rest) =>
        (parseFlintSteps k (i + 1) rest).map (⟨n, D, a, b, m, q, x, y⟩ :: ·)
      | _ => none
    else none
  | _, _, _ => none

/-- **Parse the multi-line format** (any white space between the words). -/
def parseFlint (s : String) : Option (List ExportStep) :=
  let words := ((s.toList.splitOnP Char.isWhitespace).filter (!·.isEmpty)).map String.ofList
  match words with
  | "ecpp" :: "certificate," :: k :: "steps" :: rest =>
    (parseDecimal k.toList).bind fun k => parseFlintSteps k.toNat 0 rest
  | _ => none

/-! ## The one-line format -/

/-- `n + 1 − m` in decimal, with a sign when negative. -/
def traceString (n m : AzNat) : String :=
  if m ≤ n + 1 then s!"{n + 1 - m}" else s!"-{m - n - 1}"

/-- **Print a certificate in the one-line format.** -/
def printPari (cert : List ExportStep) : String :=
  "[" ++ ", ".intercalate (cert.map fun e =>
    s!"[{e.n}, {traceString e.n e.m}, {e.m / e.q}, {e.a}, [{e.x}, {e.y}]]") ++ "]"

/-- A step from the six numbers of the one-line format (the fifth still with its opening
bracket). -/
def parsePariStep (fields : List (List Char)) : Option ExportStep :=
  match fields with
  | [N, t, s, a, '[' :: x, y] => do
    let N ← parseDecimal N
    let s ← parseDecimal s
    let a ← parseDecimal a
    let x ← parseDecimal x
    let y ← parseDecimal y
    let m ← match t with
      | '-' :: t' => (parseDecimal t').bind fun v => if v = 0 then none else some (N + 1 + v)
      | _ => (parseDecimal t).bind fun v => if v ≤ N + 1 then some (N + 1 - v) else none
    if N = 0 ∨ s = 0 ∨ m % s ≠ 0 then none
    else
      let b := (y * y % N + N - (x * x * x + a * x) % N) % N
      pure ⟨N, 0, a, b, m, m / s, x, y⟩
  | _ => none

/-- **Parse the one-line format** (white space anywhere is skipped). -/
def parsePari (s : String) : Option (List ExportStep) :=
  let cs := s.toList.filter (!·.isWhitespace)
  if cs = ['[', ']'] then some []
  else
    match cs with
    | '[' :: '[' :: body =>
      match body.reverse with
      | ']' :: ']' :: ']' :: inner =>
        let steps := (String.ofList inner.reverse).splitOn "]],["
        steps.mapM fun st => parsePariStep (st.toList.splitOnP (· == ','))
      | _ => none
    | _ => none

end Azurite.ECPP
