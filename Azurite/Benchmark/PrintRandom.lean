import Azurite.Random

partial def printLoop {G : Type} [Azurite.Random.RandomGen G Bool] (prng : G) : IO Unit := do
  let (val, nextPrng) : Bool × G := Azurite.Random.RandomGen.next prng
  IO.println (if val then "true" else "false")
  printLoop nextPrng

def main (args : List String) : IO Unit := do
  let seed : UInt64 :=
    if _ : args.length > 0 then
      match args[0]!.toNat? with
      | some n => n.toUInt64
      | none   => 1337
    else
      1337

  -- Generate weighted Bool stream where true appears 1/3 of the time
  let p : Rat := 1 / 3
  let mut boolGen := Azurite.Random.mkWeightedBoolRandomGen p seed

  -- Print an endless stream of random weighted Bools
  printLoop boolGen
