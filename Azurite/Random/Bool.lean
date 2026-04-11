import Azurite.Random.Gen
import Azurite.Random.Nat
import Batteries.Data.Rat

namespace Azurite.Random

/--
A generic generator modifier that takes a `UInt64` generator and yields `Bool`s efficiently,
stretching a single `UInt64` into 64 boolean values.
-/
structure BoolRandomGen (G : Type) [RandomGen G UInt64] where
  gen : G
  cache : UInt64
  bitsLeft : Nat
  deriving Repr

/-- Initialize the efficient `Bool` generator spanning from an underlying `UInt64` PRNG. -/
def mkBoolRandomGen (seed : UInt64) : BoolRandomGen SplitMix64 :=
  { gen := mkSplitMix64 seed, cache := 0, bitsLeft := 0}

def BoolRandomGen.next {G : Type} [RandomGen G UInt64] (bg : BoolRandomGen G) : Bool × BoolRandomGen G :=
  if bg.bitsLeft == 0 then
    let (newCache, newGen) : UInt64 × G := RandomGen.next bg.gen
    let b := (newCache &&& (1 : UInt64)) == (1 : UInt64)
    let nextBg := { gen := newGen, cache := newCache >>> (1 : UInt64), bitsLeft := 63}
    (b, nextBg)
  else
    let b := (bg.cache &&& (1 : UInt64)) == (1 : UInt64)
    let nextBg := { bg with cache := bg.cache >>> (1 : UInt64), bitsLeft := bg.bitsLeft - 1}
    (b, nextBg)

instance {G : Type} [RandomGen G UInt64] : RandomGen (BoolRandomGen G) Bool where
  next := BoolRandomGen.next

/--
A generator that produces `Bool`s where `true` is weighted by a given rational probability `0 < p < 1`.
-/
structure WeightedBoolRandomGen (G : Type) [RandomGen G UInt64] where
  natGen : NatLessThanRandomGen G
  p : Rat
  deriving Repr

/-- Initialize the `WeightedBoolRandomGen` given a rational probability `p = n / d`. -/
def mkWeightedBoolRandomGen (p : Rat) (seed : UInt64) : WeightedBoolRandomGen SplitMix64 :=
  { natGen := mkNatLessThanRandomGen p.den seed, p := p}

def WeightedBoolRandomGen.next {G : Type} [RandomGen G UInt64] (bg : WeightedBoolRandomGen G) : Bool × WeightedBoolRandomGen G :=
  if bg.p ≤ 0 then
    (false, bg)
  else if 1 ≤ bg.p then
    (true, bg)
  else
    let (val, nextNatGen) := RandomGen.next bg.natGen
    let b := val < bg.p.num.toNat
    (b, { bg with natGen := nextNatGen})

instance {G : Type} [RandomGen G UInt64] : RandomGen (WeightedBoolRandomGen G) Bool where
  next := WeightedBoolRandomGen.next

end Azurite.Random
