import Azurite.Random.Gen

namespace Azurite.Random

/--
Generates pairs `(T, T)` by sequentially drawing the first element then the second
from the same underlying generator `G`.
-/
structure PairRandomGenFromSingle (α : Type) (G : Type) [RandomGen G α] where
  gen : G
  deriving Repr

/-- Initialize a `PairRandomGenFromSingle` from an existing generator. -/
def mkPairRandomGenFromSingle {α G : Type} [RandomGen G α] (gen : G) : PairRandomGenFromSingle α G :=
  { gen := gen}

def PairRandomGenFromSingle.next {α G : Type} [RandomGen G α]
    (pg : PairRandomGenFromSingle α G) : (α × α) × PairRandomGenFromSingle α G :=
  let (fst, g₁) : α × G := RandomGen.next pg.gen
  let (snd, g₂) : α × G := RandomGen.next g₁
  ((fst, snd), { pg with gen := g₂ })

instance {α G : Type} [RandomGen G α] : RandomGen (PairRandomGenFromSingle α G) (α × α) where
  next := PairRandomGenFromSingle.next

/--
Generates pairs `(α, β)` from two independent generators `G` and `H`.
The two generators are seeded independently via `deriveSeed` with tags `"1"` and `"2"`,
eliminating correlations between the two elements of each pair.
-/
structure PairRandomGen (α : Type) (β : Type) (G : Type) (H : Type)
    [RandomGen G α] [RandomGen H β] where
  gen1 : G
  gen2 : H
  deriving Repr

/-- Initialize a `PairRandomGen` from a shared seed and two generator constructors.
The seed is scrambled differently for each generator to prevent correlations. -/
def mkPairRandomGen {α β G H : Type} [RandomGen G α] [RandomGen H β]
    (mkGen1 : UInt64 → G) (mkGen2 : UInt64 → H) (seed : UInt64) : PairRandomGen α β G H :=
  { gen1 := mkGen1 (deriveSeed seed "1"), gen2 := mkGen2 (deriveSeed seed "2") }

def PairRandomGen.next {α β G H : Type} [RandomGen G α] [RandomGen H β]
    (pg : PairRandomGen α β G H) : (α × β) × PairRandomGen α β G H :=
  let (fst, g₁) : α × G := RandomGen.next pg.gen1
  let (snd, g₂) : β × H := RandomGen.next pg.gen2
  ((fst, snd), { gen1 := g₁, gen2 := g₂ })

instance {α β G H : Type} [RandomGen G α] [RandomGen H β] :
    RandomGen (PairRandomGen α β G H) (α × β) where
  next := PairRandomGen.next

end Azurite.Random
