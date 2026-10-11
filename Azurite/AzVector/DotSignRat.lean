/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzVector.DotSignInt
import Azurite.AzRat.CompareProducts
import Azurite.AzRat.Add
import Azurite.Algorithm.BalancedProduct

/-!
## The sign of a dot product of rational vectors

`AzRat.dotSign v w` is the ordering of `v ⬝ w` against `0` for two vectors of rationals.  Each
nonzero term `vᵢ wᵢ` is a signed fraction `±(nᵢ mᵢ)/(dᵢ eᵢ)`; the terms are split by sign into
two lists, and the sign of the dot product is the comparison of the two sums `P` and `N`:

1. one list empty: the sign of the other list (no multiplication);
2. one term on each side: the four-factor magnitude comparison `AzRat.compareProductsMag`,
   with its screens;
3. an interval screen on bit lengths: a term with factor sizes `s₁, s₂` (numerators) and
   `s₃, s₄` (denominators) lies in `[2^(e−2), 2^(e+2))` with `e = s₁ + s₂ − s₃ − s₄`, so a
   side's sum is below `2^(E + size m + 2)` for its largest `e` and term count `m`, while the
   other side's is at least `2^(E' − 2)`; a surplus of `size m + 4` between the two maxima
   decides without any product;
4. otherwise each side is summed as an **unreduced fraction** by a balanced tree
   (`Frac`, `balancedSum`: `a/b + c/d = (ad + cb)/(bd)`, no gcd), and the two fractions are
   compared by `AzNat.compareProducts` on their cross products, whose screens may still avoid
   the last two multiplications.

Unlike the integer case, a single term cannot be set aside cheaply: comparing it with the rest
needs the rest's denominators anyway.  The denominators of the unreduced sums are products of
all the term denominators; any exact method needs at least their least common multiple.

Correctness: `Equiv/DotSignRat.lean` (`dotSign_eq`, `dotSign_eq_compare_dot`).
-/

namespace Azurite

/-- An unreduced fraction `num / den` of natural numbers, with addition. -/
@[ext] structure Frac where
  num : AzNat
  den : AzNat

instance : Add Frac := ⟨fun p q => ⟨p.num * q.den + q.num * p.den, p.den * q.den⟩⟩
instance : Zero Frac := ⟨⟨0, 1⟩⟩

theorem Frac.add_def (p q : Frac) : p + q = ⟨p.num * q.den + q.num * p.den, p.den * q.den⟩ := rfl
theorem Frac.zero_def : (0 : Frac) = ⟨0, 1⟩ := rfl

/-- The sum of unreduced fractions by a balanced tree. -/
def Frac.sum (l : List Frac) : Frac := Azurite.balancedSum l

namespace AzRat

open Azurite (AzVector)

variable {n : Nat}

/-- The magnitude factors of a nonzero term: `(nx · ny) / (dx · dy)`. -/
structure Term where
  nx : AzNat
  ny : AzNat
  dx : AzNat
  dy : AzNat

/-- The term as an unreduced fraction. -/
def Term.toFrac (t : Term) : Frac := ⟨t.nx * t.ny, t.dx * t.dy⟩

/-- The exponent `e` with `2^(e−2) ≤ value < 2^(e+2)`. -/
def Term.exp (t : Term) : Int := (t.nx.size + t.ny.size : Int) - (t.dx.size + t.dy.size : Int)

/-- The largest exponent of a list of terms (`0` for the empty list). -/
def maxExp : List Term → Int
  | [] => 0
  | t :: ts => ts.foldl (fun m t => max m t.exp) t.exp

/-- The general case: the interval screen, then the two unreduced sums compared by their
cross products. -/
def compareSumsGeneral (pos neg : List Term) : Ordering :=
  if maxExp pos + (Nat.size pos.length : Int) + 4 ≤ maxExp neg then .lt
  else if maxExp neg + (Nat.size neg.length : Int) + 4 ≤ maxExp pos then .gt
  else
    let P := Frac.sum (pos.map Term.toFrac)
    let N := Frac.sum (neg.map Term.toFrac)
    AzNat.compareProducts P.num N.den N.num P.den

/-- The comparison of the two sums of terms. -/
def compareSums (pos neg : List Term) : Ordering :=
  match pos, neg with
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | [p], [q] => compareProductsMag p.nx p.dx p.ny p.dy q.nx q.dx q.ny q.dy
  | _, _ => compareSumsGeneral pos neg

/-- The nonzero terms split by sign: the positive terms first, the negative ones second. -/
def splitTerms : List (AzRat × AzRat) → List Term × List Term
  | [] => ([], [])
  | (x, y) :: rest =>
    let s := splitTerms rest
    if x.num = 0 ∨ y.num = 0 then s
    else if x.sign == y.sign then (⟨x.num, y.num, x.den, y.den⟩ :: s.1, s.2)
    else (s.1, ⟨x.num, y.num, x.den, y.den⟩ :: s.2)

/-- **The sign of `v ⬝ w`** for rational vectors, as its ordering against `0`. -/
def dotSign (v w : AzVector AzRat n) : Ordering :=
  let t := splitTerms ((List.finRange n).map fun i => (v.toFn i, w.toFn i))
  compareSums t.1 t.2

end AzRat

end Azurite

/-! ### Tests -/

section Tests

open Azurite Azurite.AzRat

private def V (l : List String) (h : l.length = n := by decide) : AzVector AzRat n :=
  AzVector.ofList (l.map fun s => (AzRat.parse s).get!) (by simpa using h)

#guard dotSign (V (n := 0) []) (V []) == .eq
#guard dotSign (V (n := 2) ["0", "0"]) (V ["1/2", "-2/3"]) == .eq
#guard dotSign (V (n := 2) ["1/2", "1/3"]) (V ["2/3", "-1"]) == .eq                 -- 1/3 − 1/3
#guard dotSign (V (n := 2) ["1/2", "1/3"]) (V ["2/3", "-1/2"]) == .gt               -- 1/3 − 1/6
#guard dotSign (V (n := 2) ["1/2", "-1/3"]) (V ["2/3", "3/2"]) == .lt               -- 1/3 − 1/2
#guard dotSign (V (n := 3) ["1/2", "1/3", "1/6"]) (V ["1", "1", "-5"]) == .eq       -- 5/6 − 5/6
#guard dotSign (V (n := 3) ["1/2", "1/3", "1/6"]) (V ["1", "1", "-4"]) == .gt
#guard dotSign (V (n := 3) ["1/2", "1/3", "1/6"]) (V ["1", "1", "-6"]) == .lt
#guard dotSign (V (n := 3) ["1/2", "1/3", "1/6"]) (V ["1", "1", "1"]) == .gt
#guard dotSign (V (n := 3) ["-1/2", "-1/3", "0"]) (V ["1", "1", "7"]) == .lt
-- the interval screen
#guard dotSign (V (n := 4) ["1/3", "1/5", "1/7", "-1"])
  (V ["1/3", "1/5", "1/7", "1267650600228229401496703205376"]) == .lt
#guard dotSign (V (n := 4) ["1/3", "1/5", "1/7", "-1/1267650600228229401496703205376"])
  (V ["1/3", "1/5", "1/7", "1"]) == .gt
-- agreement with the dot product on a grid of vectors
private def grid : List (AzVector AzRat 3) :=
  [V ["0", "0", "0"], V ["1", "0", "0"], V ["0", "-2/3", "0"], V ["1/2", "1/3", "1/6"],
   V ["1/2", "-1/3", "1/6"], V ["-5/7", "0", "7/5"], V ["1", "2", "-3"],
   V ["255/256", "-256/255", "65536"], V ["18446744073709551616/3", "-3", "0"],
   V ["-1/18446744073709551615", "18446744073709551615", "1"]]
#guard grid.all fun v => grid.all fun w => dotSign v w == AzRat.cmp (v.dot w) 0

end Tests
