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

  -- Generate random values strictly less than 1,000,000,000.
  let mut natGen := Azurite.Random.mkNatLessThanGen 1000000000 seed

  -- Print an endless stream of random bounded Nats
  printLoop natGen
