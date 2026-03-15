import Azurite.Random.Gen

partial def printLoop (prng : Azurite.Random.SplitMix64) : IO Unit := do
  let (val, nextPrng) := prng.next
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

  let mut prng := Azurite.Random.mkSplitMix64 seed

  -- Print an endless stream of random UInt64
  printLoop prng
