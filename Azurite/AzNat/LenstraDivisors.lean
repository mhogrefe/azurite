/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Algorithm 4.2.11 at limb level**: Lenstra's divisors in residue
  classes on `AzNat`/`AzInt` — the port of the proven reference
  implementation `Azurite.CP.lenstraDivisors`
  (`CrandallPomerance/Chapter4/Theorem_4_2_12.lean`, with the two
  book errata corrected: left-closed odd window, fixed `c₁`).

  Given `n, r, s` with `0 < r < s < n`, `s ∤ n`, and a modular inverse
  `rs` of `r` mod `s`, `lenstraDivisors n r s rs` lists all divisors
  of `n` congruent to `r (mod s)`.  All arithmetic is limb-level:
  `AzNat` division with remainder for the Euclidean chain, `AzInt`
  ring operations and Euclidean division for the `b`/`c`-chains,
  windows and quadratic, and `sqrtRem` for the discriminant test.

  The correctness bridge (`Azurite/AzNat/Equiv/LenstraDivisors.lean`)
  proves `(lenstraDivisors n r s rs).map toNat` equal to the reference
  list, so the reference spec `CP.mem_lenstraDivisors` transfers:
  under the usual hypotheses, `d ∈ lenstraDivisors n r s rs` iff
  `d.toNat ∣ n.toNat` and `d.toNat ≡ r.toNat (mod s.toNat)`.
-/
import Azurite.AzNat.Div
import Azurite.AzNat.Pow
import Azurite.AzNat.SqrtRem
import Azurite.AzInt.DivMod
import Azurite.AzInt.Pow
import Azurite.AzInt.Compare
import Azurite.AzInt.Instances
import Azurite.AzNat.Equiv.Basic

namespace Azurite

namespace AzNat

/-- The chain state at an even index `2k` (limb-level counterpart of
`CP.LenstraState`). -/
structure LenstraState where
  a0 : AzNat
  a1 : AzNat
  b0 : AzInt
  b1 : AzInt
  c0 : AzInt
  c1 : AzInt

/-- One double-step of the Euclidean chain (counterpart of
`CP.lstep`). -/
def lstep (σ : LenstraState) : LenstraState :=
  if σ.a0 = 0 then σ
  else if σ.a0 % σ.a1 = 0 then
    ⟨0, 0, σ.b0 - (σ.a0 / σ.a1).toAzInt * σ.b1, 0,
      σ.c0 - (σ.a0 / σ.a1).toAzInt * σ.c1, 0⟩
  else
    ⟨σ.a0 % σ.a1,
      σ.a1 - (σ.a1 - 1) / (σ.a0 % σ.a1) * (σ.a0 % σ.a1),
      σ.b0 - (σ.a0 / σ.a1).toAzInt * σ.b1,
      σ.b1 - ((σ.a1 - 1) / (σ.a0 % σ.a1)).toAzInt
        * (σ.b0 - (σ.a0 / σ.a1).toAzInt * σ.b1),
      σ.c0 - (σ.a0 / σ.a1).toAzInt * σ.c1,
      σ.c1 - ((σ.a1 - 1) / (σ.a0 % σ.a1)).toAzInt
        * (σ.c0 - (σ.a0 / σ.a1).toAzInt * σ.c1)⟩

/-- The chain state after `k` double-steps. -/
def lchain (s a₁ : AzNat) (c₁ : AzInt) : ℕ → LenstraState
  | 0 => ⟨s, a₁, 0, 1, 0, c₁⟩
  | k + 1 => lstep (lchain s a₁ c₁ k)

/-- Fuel-based first-zero search (the recursion depth is the actual
chain length; only the DECREMENTS touch the fuel number). -/
def lKAux (s a₁ : AzNat) (c₁ : AzInt) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k =>
      if (lchain s a₁ c₁ k).a0 = 0 then k else lKAux s a₁ c₁ fuel (k + 1)

/-- The number of double-steps of the chain. -/
def lK (s a₁ : AzNat) (c₁ : AzInt) : ℕ := lKAux s a₁ c₁ s.toNat 0

/-- The terminal index `t`. -/
def lT (s a₁ : AzNat) (c₁ : AzInt) : ℕ := 2 * lK s a₁ c₁

/-- The sequence `(aᵢ)`, as `AzInt`. -/
def lA (s a₁ : AzNat) (c₁ : AzInt) (i : ℕ) : AzInt :=
  if i % 2 = 0 then (lchain s a₁ c₁ (i / 2)).a0.toAzInt
  else (lchain s a₁ c₁ (i / 2)).a1.toAzInt

/-- The sequence `(bᵢ)`. -/
def lB (s a₁ : AzNat) (c₁ : AzInt) (i : ℕ) : AzInt :=
  if i % 2 = 0 then (lchain s a₁ c₁ (i / 2)).b0
  else (lchain s a₁ c₁ (i / 2)).b1

/-- The sequence `(cᵢ)`. -/
def lC (s a₁ : AzNat) (c₁ : AzInt) (i : ℕ) : AzInt :=
  if i % 2 = 0 then (lchain s a₁ c₁ (i / 2)).c0
  else (lchain s a₁ c₁ (i / 2)).c1

/-- Integer square-root test via `sqrtRem`: `some w` iff `D = w²`. -/
def intSqrt? (D : AzInt) : Option AzInt :=
  if D < 0 then none
  else if (sqrtRem D.natAbs).2 = 0 then some (sqrtRem D.natAbs).1.toAzInt
  else none

/-- Verify a candidate and report it (counterpart of
`CP.reportIfDivisor`; divisibility is a remainder test). -/
def reportIfDivisor (n r s : AzNat) (u : AzInt) : List AzNat :=
  if 0 < u ∧ n % u.natAbs = 0 ∧ u.natAbs % s = r then [u.natAbs] else []

/-- Solve the system (4.16) at one `(i, c)` (counterpart of
`CP.solveSystem`). -/
def solveSystem (n r r' s : AzNat) (a b c : AzInt) : List AzNat :=
  if a = 0 then
    if b = 0 then []
    else if c % b = 0 ∧ 0 ≤ c / b then
      if 0 < c / b * s.toAzInt + r'.toAzInt
          ∧ n % (c / b * s.toAzInt + r'.toAzInt).natAbs = 0 then
        reportIfDivisor n r s
          (n / (c / b * s.toAzInt + r'.toAzInt).natAbs).toAzInt
      else []
    else []
  else
    match intSqrt? ((c * s.toAzInt + a * r.toAzInt + b * r'.toAzInt) ^ 2
        - 4 * a * b * n.toAzInt) with
    | none => []
    | some w =>
      (if (c * s.toAzInt + a * r.toAzInt + b * r'.toAzInt + w)
          % (2 * a) = 0 then
        reportIfDivisor n r s
          ((c * s.toAzInt + a * r.toAzInt + b * r'.toAzInt + w) / (2 * a))
       else []) ++
      (if (c * s.toAzInt + a * r.toAzInt + b * r'.toAzInt - w)
          % (2 * a) = 0 then
        reportIfDivisor n r s
          ((c * s.toAzInt + a * r.toAzInt + b * r'.toAzInt - w) / (2 * a))
       else [])

/-- The even-window candidates `c ≡ cᵢ (mod s)`, `|c| < s`. -/
def evenWindow (s : AzNat) (cᵢ : AzInt) : List AzInt :=
  if cᵢ % s.toAzInt = 0 then [0]
  else [cᵢ % s.toAzInt, cᵢ % s.toAzInt - s.toAzInt]

/-- The odd-window candidates `c ≡ cᵢ (mod s)`,
`2aᵢbᵢ ≤ c < aᵢbᵢ + n/s²` (left-closed, per the corrected window). -/
def oddWindow (n s : AzNat) (a b cᵢ : AzInt) : List AzInt :=
  (List.range ((n / s.pow 3).toNat + 1)).filterMap fun (j : ℕ) =>
    if s.toAzInt ^ 2 * ((2 * (a * b) + (cᵢ - 2 * (a * b)) % s.toAzInt
        + (ofNat j).toAzInt * s.toAzInt) - a * b) < n.toAzInt
    then some (2 * (a * b) + (cᵢ - 2 * (a * b)) % s.toAzInt
      + (ofNat j).toAzInt * s.toAzInt)
    else none

/-- The chain parameters `(a₁, c₁)` from `(n, r, s, rs)`. -/
def lenstraChainArgs (n r s rs : AzNat) : AzNat × AzInt :=
  (n * rs % s * rs % s,
    rs.toAzInt * ((n.toAzInt - r.toAzInt * (n * rs % s).toAzInt)
      / s.toAzInt))

/-- **Algorithm 4.2.11 at limb level**: all divisors of `n` congruent
to `r (mod s)` (possibly with repetitions; see
`Azurite.AzNat.mem_lenstraDivisors` for the spec). -/
def lenstraDivisors (n r s rs : AzNat) : List AzNat :=
  (List.range (lT s (lenstraChainArgs n r s rs).1
      (lenstraChainArgs n r s rs).2 + 1)).flatMap fun i =>
    ((if i % 2 = 0 then
        evenWindow s (lC s (lenstraChainArgs n r s rs).1
          (lenstraChainArgs n r s rs).2 i)
      else oddWindow n s
        (lA s (lenstraChainArgs n r s rs).1 (lenstraChainArgs n r s rs).2 i)
        (lB s (lenstraChainArgs n r s rs).1 (lenstraChainArgs n r s rs).2 i)
        (lC s (lenstraChainArgs n r s rs).1
          (lenstraChainArgs n r s rs).2 i)).flatMap
      fun c => solveSystem n r (n * rs % s) s
        (lA s (lenstraChainArgs n r s rs).1 (lenstraChainArgs n r s rs).2 i)
        (lB s (lenstraChainArgs n r s rs).1 (lenstraChainArgs n r s rs).2 i)
        c)

section Tests

-- the divisors of `91` congruent to `2 (mod 5)`: exactly `7`
#guard ofNat 7 ∈ lenstraDivisors (ofNat 91) (ofNat 2) (ofNat 5) (ofNat 3)
#guard ofNat 13 ∉ lenstraDivisors (ofNat 91) (ofNat 2) (ofNat 5) (ofNat 3)

-- the `(50, 1, 4)` instance where the book's printed window loses `5`
#guard ofNat 1 ∈ lenstraDivisors (ofNat 50) (ofNat 1) (ofNat 4) (ofNat 1)
#guard ofNat 5 ∈ lenstraDivisors (ofNat 50) (ofNat 1) (ofNat 4) (ofNat 1)
#guard ofNat 25 ∈ lenstraDivisors (ofNat 50) (ofNat 1) (ofNat 4) (ofNat 1)
#guard ofNat 10 ∉ lenstraDivisors (ofNat 50) (ofNat 1) (ofNat 4) (ofNat 1)

-- `1001 = 7·11·13`, divisors `≡ 1 (mod 10)`
#guard ofNat 11 ∈ lenstraDivisors (ofNat 1001) (ofNat 1) (ofNat 10) (ofNat 1)
#guard ofNat 91 ∈ lenstraDivisors (ofNat 1001) (ofNat 1) (ofNat 10) (ofNat 1)
#guard ofNat 7 ∉ lenstraDivisors (ofNat 1001) (ofNat 1) (ofNat 10) (ofNat 1)

end Tests

end AzNat

end Azurite
