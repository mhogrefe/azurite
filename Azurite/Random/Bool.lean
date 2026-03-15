import Azurite.Random.Gen

namespace Azurite.Random

/--
A generic generator modifier that takes a `UInt64` generator and yields `Bool`s efficiently,
stretching a single `UInt64` into 64 boolean values.
-/
structure BoolGen (G : Type) [RandomGen G UInt64] where
  gen : G
  cache : UInt64
  bitsLeft : Nat
  deriving Repr

/-- Initialize the efficient `Bool` generator spanning from an underlying `UInt64` PRNG. -/
def mkBoolGen {G : Type} [RandomGen G UInt64] (g : G) : BoolGen G :=
  { gen := g, cache := 0, bitsLeft := 0 }

def BoolGen.next {G : Type} [RandomGen G UInt64] (bg : BoolGen G) : Bool × BoolGen G :=
  if bg.bitsLeft == 0 then
    let (newCache, newGen) : UInt64 × G := RandomGen.next bg.gen
    let b := (newCache &&& (1 : UInt64)) == (1 : UInt64)
    let nextBg := { gen := newGen, cache := newCache >>> (1 : UInt64), bitsLeft := 63 }
    (b, nextBg)
  else
    let b := (bg.cache &&& (1 : UInt64)) == (1 : UInt64)
    let nextBg := { bg with cache := bg.cache >>> (1 : UInt64), bitsLeft := bg.bitsLeft - 1 }
    (b, nextBg)

instance {G : Type} [RandomGen G UInt64] : RandomGen (BoolGen G) Bool where
  next := BoolGen.next

end Azurite.Random
