/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div
import Azurite.AzNat.Div.Schoolbook2
import Azurite.AzNat.Mul
import Azurite.AzNat.Pow
import Azurite.Benchmark.Common

/-!
# Benchmark: the pieces of a schoolbook division

`benchmark az_nat_div_parts 1`: for divisors of `n` limbs and dividends of `2n` limbs (the
reduction of a product), the cost of `%`, of the schoolbook loop alone, and of one
subtract-multiply row, one add-back row and one comparison, and the pieces of the fixed cost
of a call (comparison, copy and shift of the dividend, shift of the divisor, reciprocals,
extraction of the remainder and of the quotient).  Nanoseconds per operation over
2000 operand pairs.  The first divisor of each size has its top bit set (no normalizing
shift), the second is that divisor shifted right by five bits.
-/

open Azurite Azurite.Benchmark

namespace Azurite.Benchmark.DivParts

def run (_limit : Nat) (_cfg : Std.HashMap String String) : IO Unit := do
  for n in [3, 4, 8, 16, 32] do
    let V := AzNat.pow (AzNat.ofNat 2) (64 * n) - AzNat.ofNat 159
    let V' := V >>> 5
    let big := AzNat.pow (AzNat.ofNat 1000003) (7 * n + 3)
    let xs : Array AzNat := (Array.range 2000).map fun i =>
      (big * AzNat.ofNat (i * i + 7 * i + 11) + AzNat.ofNat i) % V
    let ys : Array AzNat := (Array.range 2000).map fun i =>
      (big * AzNat.ofNat (3 * i * i + i + 5) + AzNat.ofNat (2 * i + 1)) % V
    let ps : Array AzNat := (Array.range 2000).map fun i => xs[i]! * ys[i]!
    let ps' : Array AzNat := ps.map fun (p : AzNat) => p >>> 10
    let loop (f : Nat → Nat) : IO UInt64 := do
      let t0 ← IO.monoNanosNow
      let mut s := 0
      for i in [0:2000] do
        s := s + f i
      let t1 ← IO.monoNanosNow
      if s == 0 then IO.println "?"
      return ((t1 - t0) / 2000).toUInt64
    let tMod ← loop fun i => (ps[i]! % V).limbs.size + 1
    let tMod' ← loop fun i => (ps'[i]! % V').limbs.size + 1
    let tDiv ← loop fun i => (ps[i]! / V).limbs.size + 1
    let tPrep ← loop fun i => (ps[i]!.limbs ++ #[0]).size
    let b := V.limbs
    let tSchool ← loop fun i =>
      let a : Array UInt64 := ps[i]!.limbs ++ #[0]
      let m := a.size - n
      if h : 0 < n ∧ 0 + n + m ≤ a.size ∧ 0 + n ≤ b.size then
        if h2 : 2 ^ 63 ≤ (b[0 + n - 1]'(by omega)).toNat then
          (AzNat.schoolbookDivModLimbs a b 0 0 n m h.1 h.2.1 h.2.2 h2).1.size
        else 1
      else 1
    let tFast ← loop fun i =>
      let a : Array UInt64 := ps[i]!.limbs ++ #[0]
      let m := a.size - n
      if h : 0 < n ∧ 0 + n + m ≤ a.size ∧ 0 + n ≤ b.size then
        if h2 : 2 ^ 63 ≤ (b[0 + n - 1]'(by omega)).toNat then
          (AzNat.schoolbookDivModLimbsFast a b 0 0 n m h.1 h.2.1 h.2.2 h2).1.size
        else 1
      else 1
    let same := (List.range 2000).all fun i =>
      let a : Array UInt64 := ps[i]!.limbs ++ #[0]
      let m := a.size - n
      if h : 0 < n ∧ 0 + n + m ≤ a.size ∧ 0 + n ≤ b.size then
        if h2 : 2 ^ 63 ≤ (b[0 + n - 1]'(by omega)).toNat then
          AzNat.schoolbookDivModLimbsFast a b 0 0 n m h.1 h.2.1 h.2.2 h2
            == AzNat.schoolbookDivModLimbs a b 0 0 n m h.1 h.2.1 h.2.2 h2
        else false
      else false
    let tRow2 ← loop fun i =>
      let a : Array UInt64 := ps[i]!.limbs ++ #[0]
      if h : 0 + n + 2 ≤ a.size ∧ 0 + n ≤ b.size then
        (AzNat.subMul2Limbs a b 0 0 n (xs[i]!.limbs[0]!) (ys[i]!.limbs[0]!) h.1 h.2).1.size
      else 1
    let tRow ← loop fun i =>
      let a : Array UInt64 := ps[i]!.limbs ++ #[0]
      if h : 0 + n + 1 ≤ a.size ∧ 0 + n ≤ b.size then
        (AzNat.subMulLimbs a b 0 0 n (xs[i]!.limbs[0]!) h.1 h.2).1.size
      else 1
    let tAdd ← loop fun i =>
      let a : Array UInt64 := ps[i]!.limbs ++ #[0]
      if h : 0 + n ≤ a.size ∧ 0 + n ≤ b.size then
        (AzNat.addSameLengthLimbs a b 0 0 n h.1 h.2).1.size
      else 1
    let tCmp ← loop fun i =>
      let a : Array UInt64 := ps[i]!.limbs
      if h : 0 + n ≤ a.size ∧ 0 + n ≤ b.size then
        (if AzNat.compareLimbs a b 0 0 n h.1 h.2 == .lt then 1 else 2)
      else 1
    let tMul ← loop fun i => (xs[i]! * ys[i]!).limbs.size + 1
    -- the pieces of the fixed cost of one call (`Div/Classic.lean`), for the shifted divisor
    let b' := V'.limbs
    let k := 5
    let tLt ← loop fun i => if ps'[i]! < V' then 1 else 2
    let tUshift ← loop fun i =>
      let a : Array UInt64 := ps'[i]!.limbs ++ #[0]
      if h : 0 ≤ a.size ∧ a.size ≤ a.size ∧ 1 ≤ k ∧ k ≤ 63 then
        (AzNat.shiftLimbsLeft a 0 a.size k h.1 h.2.1 h.2.2.1 h.2.2.2).1.size
      else 1
    let tVshift ← loop fun i =>
      if h : 0 ≤ n - 1 ∧ n - 1 ≤ b'.size ∧ 1 ≤ k ∧ k ≤ 63 then
        (AzNat.shiftLimbsLeft b' 0 (n - 1) k h.1 h.2.1 h.2.2.1 h.2.2.2).1.size + i
      else 1
    let ds : Array { d : UInt64 // 2 ^ 63 ≤ d.toNat } := (Array.range 2000).filterMap fun i =>
      let d := xs[i]!.limbs[0]! ||| ((1 : UInt64) <<< 63)
      if h : 2 ^ 63 ≤ d.toNat then some ⟨d, h⟩ else none
    let es : Array UInt64 := (Array.range 2000).map fun i => ys[i]!.limbs[0]!
    let tRecip ← loop fun i =>
      if h : i < ds.size then
        (UInt64.reciprocal3By2 ds[i].1 es[i]! ds[i].2 >>> 62).toNat + 1
      else 1
    let tRecip1 ← loop fun i =>
      if h : i < ds.size then (UInt64.reciprocal ds[i].1 ds[i].2 >>> 62).toNat + 1 else 1
    let tRem ← loop fun i =>
      ((AzNat.ofLimbs (ps[i]!.limbs.extract 0 n)) >>> k).limbs.size + 1
    let tQuot ← loop fun i =>
      (AzNat.ofLimbs (ps[i]!.limbs.extract n (2 * n) ++ #[0])).limbs.size + 1
    -- an odd number of quotient limbs: the dividend one limb shorter
    let ps1 : Array AzNat := ps.map fun (p : AzNat) => p >>> 64
    let tModOdd ← loop fun i => (ps1[i]! % V).limbs.size + 1
    IO.println s!"{n} limbs, fixed cost (ns): U < V {tLt}, copy + shift of the dividend {tUshift}, shift of the divisor {tVshift}, reciprocal3By2 {tRecip}, reciprocal {tRecip1}, remainder (extract, trim, shift) {tRem}, quotient (extract, trim) {tQuot}; mod with one quotient limb fewer {tModOdd}"
    IO.println s!"{n} limbs (ns): mod {tMod}, mod with shift {tMod'}, div {tDiv}, mul {tMul}; buffer copy {tPrep}, copy + schoolbook loop {tSchool}, copy + two-limb loop {tFast} ({same}), copy + one row {tRow}, copy + one double row {tRow2}, copy + one add-back {tAdd}, compare {tCmp}"

end Azurite.Benchmark.DivParts
