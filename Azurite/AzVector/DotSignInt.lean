/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzVector.DotSign
import Azurite.AzInt.CompareProducts
import Azurite.AzInt.Parse
import Azurite.AzInt.Add
import Azurite.AzInt.Mul
import Azurite.AzNat.Sub

/-!
## The sign of a dot product of integer vectors

`AzInt.dotSign v w` is the ordering of `v ⬝ w` against `0` for two vectors of integers,
computed with as few multiplications as possible.  Each nonzero term `vᵢ wᵢ` is a signed
magnitude `±|vᵢ| |wᵢ|`; the terms are split by sign into two lists of magnitude pairs, and the
sign of the dot product is the comparison of the two sums `P` and `N` of their products:

1. one list empty: the sign of the other list (no multiplication);
2. one term on each side: `AzNat.compareProducts` on the two pairs, with its screens;
3. otherwise an interval screen on bit lengths: with `K` the largest `size x + size y` on a
   side and `m` its number of terms, that side's sum is below `2^(K + size m)`, while the other
   side's sum is at least `2^(K' − 2)` from its largest term alone; a surplus of `size m + 2`
   bits between the two maxima therefore decides without any product;
4. otherwise the single largest pair (by bit length) is set aside, the products of all the
   other pairs are summed into `P'` and `N'`, and the largest term `T` is decided against the
   difference by `AzNat.compareProduct`: for a positive `T`, `P' + T > N'` at once when
   `N' ≤ P'`, and otherwise the sign is `compareProduct x y (N' − P')`; symmetrically for a
   negative `T`.  The most expensive multiplication is thus performed only when the screens of
   `compareProduct` cannot settle it.

Correctness: `Equiv/DotSignInt.lean` (`dotSign_eq`, `dotSign_eq_compare_dot`).
-/

namespace Azurite.AzInt

open Azurite (AzVector)

variable {n : Nat}

/-- Remove a pair of maximal `size x + size y` from a list, returning it and the rest. -/
def extractMax : List (AzNat × AzNat) → Option ((AzNat × AzNat) × List (AzNat × AzNat))
  | [] => none
  | p :: ps =>
    match extractMax ps with
    | none => some (p, [])
    | some (q, rest) =>
      if q.1.size + q.2.size ≤ p.1.size + p.2.size then some (p, ps) else some (q, p :: rest)

/-- `Σ x · y` over a list of pairs. -/
def sumProducts (l : List (AzNat × AzNat)) : AzNat := l.foldl (fun acc p => acc + p.1 * p.2) 0

/-- The largest `size x + size y` over a list of pairs. -/
def maxSize (l : List (AzNat × AzNat)) : Nat := l.foldl (fun m p => max m (p.1.size + p.2.size)) 0

/-- The general case of `compareSums`, both lists nonempty: the interval screen on bit lengths,
then set the largest pair aside, sum the products of the others, and decide the largest term
by `AzNat.compareProduct`. -/
def compareSumsGeneral (pos neg : List (AzNat × AzNat)) : Ordering :=
  if maxSize pos + Nat.size pos.length + 2 ≤ maxSize neg then .lt
  else if maxSize neg + Nat.size neg.length + 2 ≤ maxSize pos then .gt
  else
  match extractMax pos, extractMax neg with
  | some (p, pos'), some (q, neg') =>
    if q.1.size + q.2.size ≤ p.1.size + p.2.size then
      -- the largest term is positive: `P' + x y` against `N'`
      let P' := sumProducts pos'
      let N' := sumProducts neg
      if N' ≤ P' then .gt else AzNat.compareProduct p.1 p.2 (N' - P')
    else
      let P' := sumProducts pos
      let N' := sumProducts neg'
      if P' ≤ N' then .lt else (AzNat.compareProduct q.1 q.2 (P' - N')).swap
  | _, _ => .eq  -- unreachable: both lists are nonempty

/-- The comparison of `Σ_{pos} x · y` with `Σ_{neg} x · y`, for lists of pairs of positive
numbers, avoiding the largest multiplication when possible. -/
def compareSums (pos neg : List (AzNat × AzNat)) : Ordering :=
  match pos, neg with
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | [p], [q] => AzNat.compareProducts p.1 p.2 q.1 q.2
  | _, _ => compareSumsGeneral pos neg

/-- The nonzero terms as magnitude pairs, split by sign: the positive terms first, the negative
ones second. -/
def splitTerms : List (AzInt × AzInt) → List (AzNat × AzNat) × List (AzNat × AzNat)
  | [] => ([], [])
  | (a, b) :: rest =>
    let s := splitTerms rest
    if a.abs = 0 ∨ b.abs = 0 then s
    else if a.sign == b.sign then ((a.abs, b.abs) :: s.1, s.2)
    else (s.1, (a.abs, b.abs) :: s.2)

/-- The nonzero terms of `v ⬝ w` as magnitude pairs, split by sign. -/
def dotTerms (v w : AzVector AzInt n) : List (AzNat × AzNat) × List (AzNat × AzNat) :=
  splitTerms ((List.finRange n).map fun i => (v.toFn i, w.toFn i))

/-- **The sign of `v ⬝ w`** for integer vectors, as its ordering against `0`. -/
def dotSign (v w : AzVector AzInt n) : Ordering :=
  let t := dotTerms v w
  compareSums t.1 t.2

end Azurite.AzInt

/-! ### Tests -/

section Tests

open Azurite Azurite.AzInt

private def V (l : List String) (h : l.length = n := by decide) : AzVector AzInt n :=
  AzVector.ofList (l.map fun s => (AzInt.parse s).get!) (by simpa using h)

#guard dotSign (V (n := 0) []) (V []) == .eq
#guard dotSign (V (n := 3) ["0", "0", "0"]) (V ["1", "-2", "3"]) == .eq
#guard dotSign (V (n := 3) ["1", "0", "3"]) (V ["0", "5", "0"]) == .eq
#guard dotSign (V (n := 3) ["1", "0", "3"]) (V ["0", "5", "7"]) == .gt
#guard dotSign (V (n := 3) ["-1", "0", "3"]) (V ["0", "5", "-7"]) == .lt
#guard dotSign (V (n := 2) ["3", "7"]) (V ["7", "-3"]) == .eq                    -- 21 − 21
#guard dotSign (V (n := 2) ["3", "7"]) (V ["8", "-3"]) == .gt                    -- 24 − 21
#guard dotSign (V (n := 2) ["3", "-7"]) (V ["7", "4"]) == .lt                    -- 21 − 28
#guard dotSign (V (n := 3) ["1", "1", "1"]) (V ["1", "1", "-2"]) == .eq
#guard dotSign (V (n := 3) ["1", "1", "1"]) (V ["1", "1", "-3"]) == .lt
#guard dotSign (V (n := 3) ["1", "1", "1"]) (V ["1", "1", "-1"]) == .gt
#guard dotSign (V (n := 4) ["1000000000000", "2", "-3", "5"])
  (V ["1000000000000", "-7", "11", "-13"]) == .gt
#guard dotSign (V (n := 4) ["1000000000000", "2", "-3", "5"])
  (V ["-1000000000000", "-7", "11", "-13"]) == .lt
#guard dotSign (V (n := 3) ["18446744073709551616", "-1", "-1"])
  (V ["18446744073709551616", "170141183460469231731687303715884105728",
      "170141183460469231731687303715884105728"]) == .eq
-- the interval screen: many small terms against one huge one, and the reverse
#guard dotSign (V (n := 4) ["1", "1", "1", "-1"])
  (V ["1", "1", "1", "1267650600228229401496703205376"]) == .lt
#guard dotSign (V (n := 4) ["-1", "-1", "-1", "1"])
  (V ["1", "1", "1", "1267650600228229401496703205376"]) == .gt
#guard dotSign (V (n := 5) ["3", "5", "7", "-11", "13"]) (V ["5", "7", "11", "1000000000000", "17"])
  == .lt
-- agreement with the dot product on a grid of vectors
private def grid : List (AzVector AzInt 3) :=
  [V ["0", "0", "0"], V ["1", "0", "0"], V ["0", "-2", "0"], V ["1", "1", "1"], V ["1", "-1", "1"],
   V ["-5", "0", "7"], V ["1", "2", "-3"], V ["255", "-256", "65536"],
   V ["18446744073709551616", "-3", "0"], V ["-1", "18446744073709551615", "1"]]
#guard grid.all fun v => grid.all fun w => dotSign v w == AzInt.compare (v.dot w) 0

end Tests
