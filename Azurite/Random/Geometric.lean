import Azurite.Random.Bool

namespace Azurite.Random

/--
A generator that produces `Nat` values sampled from a geometric distribution with mean `m > 0`.
Internally uses a `WeightedBoolRandomGen` with `p = 1 / (m + 1)` and counts the number of
`false` values before the first `true`.

To ensure totality, if `⌈m⌉ * 1024` consecutive `false` values are seen, that count is
returned immediately rather than looping forever.
-/
structure NatGeometricRandomGen (G : Type) [RandomGen G UInt64] where
  boolGen : WeightedBoolRandomGen G
  m : Rat
  deriving Repr

/-- Initialize a `NatGeometricRandomGen` with mean `m > 0`. -/
def mkNatGeometricRandomGen (m : Rat) (seed : UInt64) : NatGeometricRandomGen SplitMix64 :=
  let p := 1 / (m + 1)
  { boolGen := mkWeightedBoolRandomGen p seed, m := m}

/-- Internal loop: count `false`s before the first `true`, bounded by `fuel`. -/
def NatGeometricRandomGen.nextLoop {G : Type} [RandomGen G UInt64] :
    Nat → Nat → WeightedBoolRandomGen G → Nat × WeightedBoolRandomGen G
  | 0, count, bg => (count, bg)
  | fuel + 1, count, bg =>
    let (b, bg') : Bool × WeightedBoolRandomGen G := RandomGen.next bg
    if b then
      (count, bg')
    else
      NatGeometricRandomGen.nextLoop fuel (count + 1) bg'

def NatGeometricRandomGen.next {G : Type} [RandomGen G UInt64]
    (bg : NatGeometricRandomGen G) : Nat × NatGeometricRandomGen G :=
  -- ⌈m⌉ for m > 0: (num + den - 1) / den (ceiling division)
  let m_ceil := (bg.m.num.toNat + bg.m.den - 1) / bg.m.den
  let L := m_ceil * 1024
  let (val, boolGen') := NatGeometricRandomGen.nextLoop L 0 bg.boolGen
  (val, { bg with boolGen := boolGen' })

instance {G : Type} [RandomGen G UInt64] : RandomGen (NatGeometricRandomGen G) Nat where
  next := NatGeometricRandomGen.next

/--
A generator that produces positive `Nat` values (≥ 1) sampled from a geometric distribution
with mean `m > 0`. Uses `p = 1 / m` and counts the number of `false` values before the first
`true`, starting the counter at 1 (so at least 1 is always returned).

To ensure totality, if `⌈m⌉ * 1024` consecutive `false` values are seen, that count is
returned immediately rather than looping forever.
-/
structure PositiveNatGeometricRandomGen (G : Type) [RandomGen G UInt64] where
  boolGen : WeightedBoolRandomGen G
  m : Rat
  deriving Repr

/-- Initialize a `PositiveNatGeometricRandomGen` with mean `m > 0`. -/
def mkPositiveNatGeometricRandomGen (m : Rat) (seed : UInt64) : PositiveNatGeometricRandomGen SplitMix64 :=
  let p := 1 / m
  { boolGen := mkWeightedBoolRandomGen p seed, m := m}

def PositiveNatGeometricRandomGen.next {G : Type} [RandomGen G UInt64]
    (bg : PositiveNatGeometricRandomGen G) : Nat × PositiveNatGeometricRandomGen G :=
  -- ⌈m⌉ for m > 0: (num + den - 1) / den (ceiling division)
  let m_ceil := (bg.m.num.toNat + bg.m.den - 1) / bg.m.den
  let L := m_ceil * 1024
  -- Reuse NatGeometricRandomGen.nextLoop, but start counter at 1
  let (val, boolGen') := NatGeometricRandomGen.nextLoop L 1 bg.boolGen
  (val, { bg with boolGen := boolGen' })

instance {G : Type} [RandomGen G UInt64] : RandomGen (PositiveNatGeometricRandomGen G) Nat where
  next := PositiveNatGeometricRandomGen.next

/-- The output of `nextLoop` is always ≥ the initial counter value. -/
private lemma nextLoop_lower_bound {G : Type} [RandomGen G UInt64]
    (fuel count : Nat) (bg : WeightedBoolRandomGen G) :
    count ≤ (NatGeometricRandomGen.nextLoop fuel count bg).1 := by
  induction fuel generalizing count bg with
  | zero => simp [NatGeometricRandomGen.nextLoop]
  | succ f ih =>
    simp only [NatGeometricRandomGen.nextLoop]
    split
    · -- bool = true: returns count
      exact le_refl count
    · -- bool = false: recurse with count + 1
      exact Nat.le_of_succ_le (ih (count + 1) _)

theorem positive_nat_geometric_positive {G : Type} [RandomGen G UInt64]
    (bg : PositiveNatGeometricRandomGen G) :
    let (v, _) := PositiveNatGeometricRandomGen.next bg
    1 ≤ v := by
  simp only [PositiveNatGeometricRandomGen.next]
  exact nextLoop_lower_bound _ 1 _

end Azurite.Random
