/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Random.Gen
import Azurite.UInt64.MulAddWithCarry
import Azurite.UInt64.AddWithCarry
import Azurite.Benchmark.Common

/-!
# Limb-width experiment: `Array UInt64` versus `Array UInt32`

In Lean's runtime a `UInt64` stored in an `Array` is a heap-allocated box
(`lean_box_uint64` allocates; `lean_unbox_uint64` dereferences), while on 64-bit
platforms a `UInt32` is a tagged pointer (`lean_box_uint32 = lean_box`, no allocation).
This micro-benchmark measures what that costs by timing the same two loops over both
representations of the same value: a carry-chain addition pass (one store per limb) and a
naive row-by-row schoolbook multiplication (one `wideMul`-class product per limb pair).
The 32-bit version uses twice as many limbs for the same bit length, so the columns are
directly comparable per value.  Nothing here is proven or used by the library.
-/

namespace Azurite.Benchmark.LimbWidth

open Azurite.Random

/-- Left-pad to `width`. -/
private def padLeft (width : Nat) (s : String) : String :=
  let n := s.length
  if n ≥ width then s else String.ofList (List.replicate (width - n) ' ') ++ s

/-- Carry-chain addition of two `n`-limb arrays, in place in `a`. -/
def add64.go (b : Array UInt64) (n : Nat) (a : Array UInt64) (i : Nat) (carry : Bool)
    (hA : n ≤ a.size) (hB : n ≤ b.size) : Array UInt64 × Bool :=
  if h : i < n then
    have hiA : i < a.size := by omega
    have hiB : i < b.size := by omega
    let s := UInt64.addWithCarry a[i] b[i] carry
    add64.go b n (a.set i s.1) (i + 1) s.2 (by rw [Array.size_set]; exact hA) hB
  else (a, carry)
  termination_by n - i

/-- Carry-chain addition of two `n`-limb 32-bit arrays, in place in `a`. -/
def add32.go (b : Array UInt32) (n : Nat) (a : Array UInt32) (i : Nat) (carry : UInt32)
    (hA : n ≤ a.size) (hB : n ≤ b.size) : Array UInt32 × UInt32 :=
  if h : i < n then
    have hiA : i < a.size := by omega
    have hiB : i < b.size := by omega
    let s : UInt64 := a[i].toUInt64 + b[i].toUInt64 + carry.toUInt64
    add32.go b n (a.set i s.toUInt32) (i + 1) (s >>> 32).toUInt32
      (by rw [Array.size_set]; exact hA) hB
  else (a, carry)
  termination_by n - i

/-- One schoolbook row: `acc[j + i] += a[i] * bj` for `i < n`, 64-bit limbs. -/
def row64.go (a : Array UInt64) (n : Nat) (bj : UInt64) (j : Nat) (acc : Array UInt64)
    (i : Nat) (carry : UInt64) (hA : n ≤ a.size) (hAcc : j + n < acc.size) :
    Array UInt64 :=
  if h : i < n then
    have hiA : i < a.size := by omega
    have hiAcc : j + i < acc.size := by omega
    let mac := UInt64.mulAddWithCarry a[i] bj acc[j + i] carry
    row64.go a n bj j (acc.set (j + i) mac.2) (i + 1) mac.1 hA
      (by rw [Array.size_set]; exact hAcc)
  else
    acc.set (j + n) carry
  termination_by n - i

/-- One schoolbook row with 32-bit limbs: the product is a single native 64-bit multiply. -/
def row32.go (a : Array UInt32) (n : Nat) (bj : UInt32) (j : Nat) (acc : Array UInt32)
    (i : Nat) (carry : UInt32) (hA : n ≤ a.size) (hAcc : j + n < acc.size) :
    Array UInt32 :=
  if h : i < n then
    have hiA : i < a.size := by omega
    have hiAcc : j + i < acc.size := by omega
    let p : UInt64 := a[i].toUInt64 * bj.toUInt64 + acc[j + i].toUInt64 + carry.toUInt64
    row32.go a n bj j (acc.set (j + i) p.toUInt32) (i + 1) (p >>> 32).toUInt32 hA
      (by rw [Array.size_set]; exact hAcc)
  else
    acc.set (j + n) carry
  termination_by n - i

theorem row64.go_size (a : Array UInt64) (n : Nat) (bj : UInt64) (j : Nat) (acc : Array UInt64)
    (i : Nat) (carry : UInt64) (hA : n ≤ a.size) (hAcc : j + n < acc.size) :
    (row64.go a n bj j acc i carry hA hAcc).size = acc.size := by
  induction h_sub : n - i generalizing acc i carry with
  | zero =>
    rw [row64.go]; simp [show ¬ i < n from by omega]
  | succ k ih =>
    rw [row64.go]; simp only [show i < n from by omega, ↓reduceDIte]
    rw [ih _ _ _ _ (by omega), Array.size_set]

theorem row32.go_size (a : Array UInt32) (n : Nat) (bj : UInt32) (j : Nat) (acc : Array UInt32)
    (i : Nat) (carry : UInt32) (hA : n ≤ a.size) (hAcc : j + n < acc.size) :
    (row32.go a n bj j acc i carry hA hAcc).size = acc.size := by
  induction h_sub : n - i generalizing acc i carry with
  | zero =>
    rw [row32.go]; simp [show ¬ i < n from by omega]
  | succ k ih =>
    rw [row32.go]; simp only [show i < n from by omega, ↓reduceDIte]
    rw [ih _ _ _ _ (by omega), Array.size_set]

/-- Naive schoolbook product of two `n`-limb arrays (64-bit limbs), `2n` limbs out. -/
def mul64.go (a b : Array UInt64) (n : Nat) (acc : Array UInt64) (j : Nat)
    (hA : n ≤ a.size) (hB : n ≤ b.size) (hAcc : acc.size = 2 * n) : Array UInt64 :=
  if h : j < n then
    have hjB : j < b.size := by omega
    have hjn : j + n < acc.size := by omega
    let acc' := row64.go a n b[j] j acc 0 0 hA hjn
    mul64.go a b n acc' (j + 1) hA hB (by rw [row64.go_size]; exact hAcc)
  else acc
  termination_by n - j

/-- Naive schoolbook product of two `n`-limb arrays (32-bit limbs), `2n` limbs out. -/
def mul32.go (a b : Array UInt32) (n : Nat) (acc : Array UInt32) (j : Nat)
    (hA : n ≤ a.size) (hB : n ≤ b.size) (hAcc : acc.size = 2 * n) : Array UInt32 :=
  if h : j < n then
    have hjB : j < b.size := by omega
    have hjn : j + n < acc.size := by omega
    let acc' := row32.go a n b[j] j acc 0 0 hA hjn
    mul32.go a b n acc' (j + 1) hA hB (by rw [row32.go_size]; exact hAcc)
  else acc
  termination_by n - j

/-- `n` random 64-bit limbs. -/
def randomLimbs64 (n : Nat) (g : SplitMix64) : Array UInt64 × SplitMix64 := Id.run do
  let mut g := g
  let mut xs : Array UInt64 := #[]
  for _ in List.range n do
    let (x, g') := SplitMix64.next g
    g := g'
    xs := xs.push x
  return (xs, g)

/-- The same value as `2n` 32-bit limbs (low half first). -/
def split32 (xs : Array UInt64) : Array UInt32 := Id.run do
  let mut ys : Array UInt32 := #[]
  for x in xs do
    ys := ys.push x.toUInt32
    ys := ys.push (x >>> 32).toUInt32
  return ys

/-- `iters` addition passes (64-bit), each depending on the iteration so none is hoisted. -/
@[noinline] def benchAdd64 (a b : Array UInt64) (n iters salt : Nat)
    (hA : n ≤ a.size) (hB : n ≤ b.size) : Nat := Id.run do
  let mut acc := 0
  for it in [0:iters] do
    acc := acc + (add64.go b n a 0 ((it + salt) % 2 == 1) hA hB).1.size
  return acc

/-- `iters` addition passes (32-bit). -/
@[noinline] def benchAdd32 (a b : Array UInt32) (n iters salt : Nat)
    (hA : n ≤ a.size) (hB : n ≤ b.size) : Nat := Id.run do
  let mut acc := 0
  for it in [0:iters] do
    acc := acc + (add32.go b n a 0 ((it + salt) % 2).toUInt32 hA hB).1.size
  return acc

/-- `iters` schoolbook products (64-bit), each into a fresh accumulator. -/
@[noinline] def benchMul64 (a b : Array UInt64) (n iters salt : Nat)
    (hA : n ≤ a.size) (hB : n ≤ b.size) : Nat := Id.run do
  let mut acc := 0
  for it in [0:iters] do
    acc := acc + (mul64.go a b n (Array.replicate (2 * n) (it + salt).toUInt64) 0 hA hB
      (by rw [Array.size_replicate])).size
  return acc

/-- `iters` schoolbook products (32-bit), each into a fresh accumulator. -/
@[noinline] def benchMul32 (a b : Array UInt32) (n iters salt : Nat)
    (hA : n ≤ a.size) (hB : n ≤ b.size) : Nat := Id.run do
  let mut acc := 0
  for it in [0:iters] do
    acc := acc + (mul32.go a b n (Array.replicate (2 * n) (it + salt).toUInt32) 0 hA hB
      (by rw [Array.size_replicate])).size
  return acc

/-- Median of three wall-clock timings of `f salt`, in ns.  The salt is derived from the start
    timestamp and the result is consumed before the stop timestamp, so the compiler can neither
    hoist the call above the clock nor sink it below. -/
private def timeMedian (f : Nat → Nat) : IO UInt64 := do
  let once : IO UInt64 := do
    let t0 ← monoNanos
    let r := f (t0.toNat % 4)
    if r == 0 then IO.eprintln "" else pure ()
    let t1 ← monoNanos
    return t1 - t0
  let t1 ← once
  let t2 ← once
  let t3 ← once
  return median3 t1 t2 t3

/-- Run the experiment on `n`-limb (64-bit) values: ns per 64-bit limb for the addition pass
    and ns per 64×64 limb product for schoolbook (the 32-bit columns are normalised to the
    same units, i.e. per two 32-bit limbs and per four 32×32 products). -/
def run (sizes : Array Nat) (seed : UInt64) : IO Unit := do
  IO.eprintln "[LimbWidth] same values as 64-bit limbs (boxed) and 32-bit limbs (tagged)"
  IO.eprintln "  add: ns per 64-bit limb of one pass; mul: ns per 64×64 limb product (schoolbook)"
  IO.eprintln (padLeft 8 "limbs64" ++ padLeft 10 "add64" ++ padLeft 10 "add32" ++ padLeft 8 "%"
    ++ padLeft 10 "mul64" ++ padLeft 10 "mul32" ++ padLeft 8 "%")
  let mut g := mkSplitMix64 seed
  for n in sizes do
    let (a, g₁) := randomLimbs64 n g
    let (b, g₂) := randomLimbs64 n g₁
    g := g₂
    let a32 := split32 a
    let b32 := split32 b
    if hA : n ≤ a.size then
      if hB : n ≤ b.size then
        if hA32 : 2 * n ≤ a32.size then
          if hB32 : 2 * n ≤ b32.size then
            let itersAdd := max 1 (2000000 / max 1 n)
            let itersMul := max 1 (2000000 / max 1 (n * n))
            let tAdd64 ← timeMedian (fun salt => benchAdd64 a b n itersAdd salt hA hB)
            let tAdd32 ← timeMedian (fun salt => benchAdd32 a32 b32 (2 * n) itersAdd salt hA32 hB32)
            let tMul64 ← timeMedian (fun salt => benchMul64 a b n itersMul salt hA hB)
            let tMul32 ← timeMedian (fun salt => benchMul32 a32 b32 (2 * n) itersMul salt hA32 hB32)
            let perAdd := fun (t : UInt64) => (t.toNat * 100) / (itersAdd * n)
            let perMul := fun (t : UInt64) => (t.toNat * 100) / (itersMul * n * n)
            let fmt := fun (x : Nat) => s!"{x / 100}.{(x % 100) / 10}{x % 10}"
            let pct := fun (x y : Nat) => if y == 0 then 0 else x * 100 / y
            IO.eprintln (padLeft 8 s!"{n}" ++ padLeft 10 (fmt (perAdd tAdd64))
              ++ padLeft 10 (fmt (perAdd tAdd32)) ++ padLeft 8 s!"{pct (perAdd tAdd32) (perAdd tAdd64)}"
              ++ padLeft 10 (fmt (perMul tMul64)) ++ padLeft 10 (fmt (perMul tMul32))
              ++ padLeft 8 s!"{pct (perMul tMul32) (perMul tMul64)}")
          else pure ()
        else pure ()
      else pure ()
    else pure ()

end Azurite.Benchmark.LimbWidth
