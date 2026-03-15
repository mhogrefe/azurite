import Azurite.Random

partial def printLoop {G : Type} [Azurite.Random.RandomGen G Nat] (prng : G) : IO Unit := do
  let (val, nextPrng) : Nat × G := Azurite.Random.RandomGen.next prng
  IO.println val
  printLoop nextPrng

def main (args : List String) : IO Unit := do
  let seed : UInt64 :=
    if _ : args.length > 0 then
      match args[0]!.toNat? with
      | some n => n.toUInt64
      | none   => 1337
    else
      1337

  let mut natGen := Azurite.Random.mkNatWithBitsGen 200 seed

  -- Print an endless stream of random 200-bit Nats
  printLoop natGen
