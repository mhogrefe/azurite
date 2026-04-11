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
      seed}

def RatRandomGen.next (rg : RatRandomGen) : Rat × RatRandomGen :=
  let ((num, den), pairGen') := PairRandomGen.next rg.pairGen
  (mkRat num den, { pairGen := pairGen' })

instance : RandomGen RatRandomGen Rat where
  next := RatRandomGen.next

/--
A generator that produces nonzero `Rat` values by independently sampling a nonzero `Int`
numerator and a positive `Nat` denominator, then constructing the reduced fraction via `mkRat`.
Since the numerator is always nonzero and the denominator is always positive, the result is
never zero.
-/
structure NonzeroRatRandomGen where
  pairGen : PairRandomGen Int Nat NonzeroIntRandomGen (PositiveNatRandomGen SplitMix64)

/-- Create a `NonzeroRatRandomGen`. Both numerator and denominator have geometric bit-length
distribution with the given mean; they are seeded independently. -/
def mkNonzeroRatRandomGen (meanBitLength : Rat) (seed : UInt64) : NonzeroRatRandomGen :=
  { pairGen := mkPairRandomGen (α := Int) (β := Nat)
      (mkNonzeroIntRandomGen meanBitLength)
      (mkPositiveNatRandomGen meanBitLength)
      seed}

def NonzeroRatRandomGen.next (rg : NonzeroRatRandomGen) : Rat × NonzeroRatRandomGen :=
  let ((num, den), pairGen') := PairRandomGen.next rg.pairGen
  (mkRat num den, { pairGen := pairGen' })

instance : RandomGen NonzeroRatRandomGen Rat where
  next := NonzeroRatRandomGen.next

theorem nonzero_rat_random_gen_nonzero (rg : NonzeroRatRandomGen) :
    let (v, _) := NonzeroRatRandomGen.next rg
    v ≠ 0 := by
  simp only [NonzeroRatRandomGen.next, PairRandomGen.next]
  have h_num := nonzero_int_random_gen_nonzero rg.pairGen.gen1
  set num := (NonzeroIntRandomGen.next rg.pairGen.gen1).1
  set den := (PositiveNatRandomGen.next rg.pairGen.gen2).1
  have h_den : 1 ≤ den := positive_nat_random_gen_positive rg.pairGen.gen2
  have h_den_ne : (den : ℕ) ≠ 0 := by omega
  intro h
  exact h_num ((Rat.mkRat_eq_zero h_den_ne).mp h)

end Azurite.Random
