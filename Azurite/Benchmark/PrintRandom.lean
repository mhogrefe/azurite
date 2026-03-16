import Azurite.Random

partial def printLoop {G : Type} [Azurite.Random.RandomGen G (Nat × Nat)] (prng : G) : IO Unit := do
  let (val, nextPrng) : (Nat × Nat) × G := Azurite.Random.RandomGen.next prng
  IO.println s!"({val.1}, {val.2})"
  printLoop nextPrng

def main (args : List String) : IO Unit := do
  let seed : UInt64 :=
    if _ : args.length > 0 then
      match args[0]!.toNat? with
      | some n => n.toUInt64
      | none   => 1337
    else
      1337

  -- Generate pairs (Nat, Nat) where first ~ Geometric(mean=10), second ~ Geometric(mean=11).
  -- Seeds are derived independently to avoid correlations between the two elements.
  let pairGen := Azurite.Random.mkPairRandomGen (α := Nat) (β := Nat)
    (Azurite.Random.mkNatGeometricRandomGen 10)
    (Azurite.Random.mkNatGeometricRandomGen 11)
    seed

  printLoop pairGen
