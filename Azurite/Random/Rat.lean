import Azurite.Random.Int
import Azurite.Random.Pair

namespace Azurite.Random

/--
A generator that produces `Rat` values by independently sampling an `Int` numerator and a
positive `Nat` denominator, then constructing the reduced fraction via `mkRat`.

`meanBitLength` controls the bit-length distribution of both numerator and denominator
independently.
-/
structure RatRandomGen where
  pairGen : PairRandomGen Int Nat IntRandomGen (PositiveNatRandomGen SplitMix64)

/-- Create a `RatRandomGen`. Both numerator and denominator have geometric bit-length
distribution with the given mean; they are seeded independently. -/
def mkRatRandomGen (meanBitLength : Rat) (seed : UInt64) : RatRandomGen :=
  { pairGen := mkPairRandomGen (α := Int) (β := Nat)
      (mkIntRandomGen meanBitLength)
      (mkPositiveNatRandomGen meanBitLength)
      seed }

def RatRandomGen.next (rg : RatRandomGen) : Rat × RatRandomGen :=
  let ((num, den), pairGen') := PairRandomGen.next rg.pairGen
  (mkRat num den, { pairGen := pairGen' })

instance : RandomGen RatRandomGen Rat where
  next := RatRandomGen.next

end Azurite.Random
