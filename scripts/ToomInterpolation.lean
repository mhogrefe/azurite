/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite

/-!
# Toom–Cook interpolation matrices, derived with Azurite's own arithmetic

A Toom-(r, s) multiplication splits `A` into `r` limb blocks and `B` into `s`, so the product
`C = A·B` has degree `d = r + s − 2` in the block base.  Evaluating `A` and `B` at `d + 1` points,
multiplying pointwise and solving the Vandermonde system recovers the coefficients of `C`.

For each variant this script builds the Vandermonde matrix over `AzRat`, inverts it by
Gauss–Jordan elimination on `AzMatrix`, checks `W · V = 1` exactly, and prints every coefficient
of `C` as an integer combination of the point products divided by one small integer.  Those
divisors are precisely the exact divisions the Lean implementation of the variant needs.

A point `p/q` is realized in integers as the scaled evaluation `q^d · P(p/q)`, so its row is
`c_i ↦ p^i · q^(d−i)`; `∞` selects the leading coefficient.

Toom-6.5 and Toom-8.5 (`toom6h`, `toom8h`) are the balanced-as-possible variants with 12 and 16
points: 7 × 6 and 9 × 8 blocks.

Run with `lake env lean --run scripts/ToomInterpolation.lean [variant ...]`.
-/

open Azurite

/-- An evaluation point `p/q`, or `∞`. -/
inductive Pt where
  | fin (p : Int) (q : Nat)
  | inf

def Pt.label : Pt → String
  | .inf => "∞"
  | .fin p 1 => toString p
  | .fin p q => s!"{p}/{q}"

structure Variant where
  name : String
  r : Nat
  s : Nat
  pts : List Pt

def pm (n : Int) (q : Nat := 1) : List Pt := [.fin n q, .fin (-n) q]

def variants : List Variant :=
  [ ⟨"toom22", 2, 2, [.fin 0 1, .fin 1 1, .inf]⟩,
    ⟨"toom32", 3, 2, [.fin 0 1, .fin 1 1, .fin (-1) 1, .inf]⟩,
    ⟨"toom33", 3, 3, [.fin 0 1] ++ pm 1 ++ [.fin 2 1, .inf]⟩,
    ⟨"toom42", 4, 2, [.fin 0 1] ++ pm 1 ++ [.fin 2 1, .inf]⟩,
    ⟨"toom43", 4, 3, [.fin 0 1] ++ pm 1 ++ pm 2 ++ [.inf]⟩,
    ⟨"toom52", 5, 2, [.fin 0 1] ++ pm 1 ++ pm 2 ++ [.inf]⟩,
    ⟨"toom44", 4, 4, [.fin 0 1] ++ pm 1 ++ pm 2 ++ [.fin 1 2, .inf]⟩,
    ⟨"toom53", 5, 3, [.fin 0 1] ++ pm 1 ++ pm 2 ++ [.fin 1 2, .inf]⟩,
    ⟨"toom54", 5, 4, [.fin 0 1] ++ pm 1 ++ pm 2 ++ pm 1 2 ++ [.inf]⟩,
    ⟨"toom63", 6, 3, [.fin 0 1] ++ pm 1 ++ pm 2 ++ pm 1 2 ++ [.inf]⟩,
    ⟨"toom6h", 7, 6, [.fin 0 1] ++ pm 1 ++ pm 2 ++ pm 1 2 ++ pm 4 ++ pm 1 4 ++ [.inf]⟩,
    ⟨"toom8h", 9, 8, [.fin 0 1] ++ pm 1 ++ pm 2 ++ pm 1 2 ++ pm 4 ++ pm 1 4 ++ pm 8 ++ pm 1 8
        ++ [.inf]⟩ ]

/-- Entry `(pt, i)` of the (scaled) Vandermonde matrix for degree `d`. -/
def vEntry (d : Nat) (pt : Pt) (i : Nat) : AzRat :=
  match pt with
  | .inf => if i = d then 1 else 0
  | .fin p q => (p : AzRat) ^ i * (q : AzRat) ^ (d - i)

/-- Gauss–Jordan inverse of a square `AzMatrix` over a field; `none` if singular. -/
def gaussJordanInv {K : Type} [Field K] [DecidableEq K] {n : Nat} (A : AzMatrix K n n) :
    Option (AzMatrix K n n) := Id.run do
  let mut a := A
  let mut w : AzMatrix K n n := AzMatrix.ofFn fun i j => if i = j then 1 else 0
  for col in List.finRange n do
    match (List.finRange n).find? (fun r => col ≤ r ∧ a.get r col ≠ 0) with
    | none => return none
    | some piv =>
      let swap (m : AzMatrix K n n) : AzMatrix K n n :=
        AzMatrix.ofFn fun i j =>
          if i = col then m.get piv j else if i = piv then m.get col j else m.get i j
      let a₁ := swap a
      let w₁ := swap w
      let inv := (a₁.get col col)⁻¹
      let elim (m : AzMatrix K n n) : AzMatrix K n n :=
        AzMatrix.ofFn fun i j =>
          if i = col then inv * m.get col j
          else m.get i j - a₁.get i col * (inv * m.get col j)
      a := elim a₁
      w := elim w₁
  return some w

/-- Least common multiple of a list of `AzNat`s. -/
def lcmList (l : List AzNat) : AzNat :=
  l.foldl (fun acc x => acc * x / AzNat.gcd acc x) 1

def report (v : Variant) : IO Unit := do
  let d := v.r + v.s - 2
  let n := d + 1
  if v.pts.length ≠ n then
    IO.println s!"── {v.name}: {v.pts.length} points given, {n} needed"
    return
  let pt (i : Fin n) : Pt := v.pts.getD i .inf
  let V : AzMatrix AzRat n n := AzMatrix.ofFn fun i j => vEntry d (pt i) j
  let some W := gaussJordanInv V | IO.println s!"── {v.name}: singular Vandermonde matrix"
  let I : AzMatrix AzRat n n := AzMatrix.ofFn fun i j => if i = j then 1 else 0
  let ok := decide (W * V = I)
  IO.println s!"── {v.name}: A in {v.r} blocks, B in {v.s} blocks, degree {d}, \
    {n} multiplications of ≈ n/{max v.r v.s} limbs each — W·V = 1: {ok}"
  IO.println s!"   points: {", ".intercalate (v.pts.map Pt.label)}"
  let mut dens : List AzNat := []
  for i in List.finRange n do
    let rowDen := lcmList ((List.finRange n).map fun j => (W.get i j).den)
    dens := rowDen :: dens
    let terms := (List.finRange n).filterMap fun j =>
      let x := W.get i j * (rowDen.toAzRat)
      if x = 0 then none
      else some s!"{if x.sign then "+" else "-"} {x.num}·v({(pt j).label})"
    IO.println s!"   c{i.val} = ({" ".intercalate terms}) / {rowDen}"
  let two : AzNat := AzNat.ofNat 2
  let oddPart (m : AzNat) : AzNat := Id.run do
    let mut x := m
    while x % two = 0 ∧ x ≠ 0 do x := x / two
    return x
  let odd := (dens.map oddPart).eraseDups.filter (· ≠ 1)
  let pow2 := (dens.map fun m => m / oddPart m).foldl (fun acc x => if acc < x then x else acc) 1
  IO.println s!"   exact divisions: by powers of two up to {pow2}\
    {if odd.isEmpty then "" else s!", and by the odd numbers {", ".intercalate (odd.map toString)}"}"
  IO.println ""

def main (args : List String) : IO Unit := do
  let chosen := if args.isEmpty then variants else variants.filter (args.contains ·.name)
  for v in chosen do report v
