/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Random.Bool
import Azurite.Random.NatGen
import Azurite.Random.Pair

namespace Azurite.Random

/--
A generator that produces `Int` values by independently sampling a sign (`Bool`) and an
absolute value (`Nat`) from two decorrelated sub-generators.
- `true` → `Int.ofNat absVal`  (non-negative)
- `false` → `-Int.ofNat absVal` (non-positive)

Wraps a `PairRandomGen` so sign and magnitude are seeded independently.
-/
structure IntRandomGen where
  pairGen : PairRandomGen Bool Nat (BoolRandomGen SplitMix64) (NatRandomGen SplitMix64)

/-- Create an `IntRandomGen`. `meanBitLength` controls the magnitude distribution. -/
def mkIntRandomGen (meanBitLength : Rat) (seed : UInt64) : IntRandomGen :=
  { pairGen := mkPairRandomGen (α := Bool) (β := Nat)
      mkBoolRandomGen
      (mkNatRandomGen meanBitLength)
      seed}

def IntRandomGen.next (ig : IntRandomGen) : Int × IntRandomGen :=
  let ((sign, absVal), pairGen') := PairRandomGen.next ig.pairGen
  let n : Int := if sign then Int.ofNat absVal else -Int.ofNat absVal
  (n, { pairGen := pairGen' })

instance : RandomGen IntRandomGen Int where
  next := IntRandomGen.next

/--
A generator that produces nonzero `Int` values, by pairing a sign (`BoolRandomGen`) with a
strictly positive magnitude (`PositiveNatRandomGen`). Since the magnitude is always ≥ 1, the
result is never 0.
-/
structure NonzeroIntRandomGen where
  pairGen : PairRandomGen Bool Nat (BoolRandomGen SplitMix64) (PositiveNatRandomGen SplitMix64)

/-- Create a `NonzeroIntRandomGen`. `meanBitLength` controls the magnitude distribution. -/
def mkNonzeroIntRandomGen (meanBitLength : Rat) (seed : UInt64) : NonzeroIntRandomGen :=
  { pairGen := mkPairRandomGen (α := Bool) (β := Nat)
      mkBoolRandomGen
      (mkPositiveNatRandomGen meanBitLength)
      seed}

def NonzeroIntRandomGen.next (ig : NonzeroIntRandomGen) : Int × NonzeroIntRandomGen :=
  let ((sign, absVal), pairGen') := PairRandomGen.next ig.pairGen
  let n : Int := if sign then Int.ofNat absVal else -Int.ofNat absVal
  (n, { pairGen := pairGen' })

instance : RandomGen NonzeroIntRandomGen Int where
  next := NonzeroIntRandomGen.next

theorem nonzero_int_random_gen_nonzero (ig : NonzeroIntRandomGen) :
    let (v, _) := NonzeroIntRandomGen.next ig
    v ≠ 0 := by
  simp only [NonzeroIntRandomGen.next, PairRandomGen.next]
  rw [show RandomGen.next ig.pairGen.gen2 = PositiveNatRandomGen.next ig.pairGen.gen2 from rfl]
  -- The Bool sign can be anything; the Nat absVal is always ≥ 1
  have hpos : 1 ≤ (PositiveNatRandomGen.next ig.pairGen.gen2).1 :=
    positive_nat_random_gen_positive ig.pairGen.gen2
  have hX : (PositiveNatRandomGen.next ig.pairGen.gen2).1 ≠ 0 := by omega
  -- Int.ofNat absVal ≠ 0 and -Int.ofNat absVal ≠ 0 both follow from absVal ≥ 1
  by_cases hsign : (RandomGen.next ig.pairGen.gen1).1 = true <;>
    simp only [hsign, Bool.false_eq_true, ite_true, ite_false] <;>
    simpa using hX

end Azurite.Random
