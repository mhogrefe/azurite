import Batteries.Data.HashMap
import Azurite.Random.Nat
import Azurite.Random.Geometric

namespace Azurite.Random

/-- Helper: look up or create a `NatWithBitsRandomGen SplitMix64` for bit length `b`.
    The result always has `.b = b`. -/
private def getNatGen (b : Nat) (seed : UInt64)
    (cache : Std.HashMap Nat SplitMix64) : NatWithBitsRandomGen SplitMix64 × Std.HashMap Nat SplitMix64 :=
  match cache[b]? with
  | some g => ({ gen := g, b := b}, cache)
  | none   =>
    let newSeed := deriveSeed seed (toString b)
    let g := mkSplitMix64 newSeed
    ({ gen := g, b := b}, cache.insert b g)

/-- The `.b` field of the result of `getNatGen` always equals `b`. -/
private lemma getNatGen_b_eq (b : Nat) (seed : UInt64) (cache : Std.HashMap Nat SplitMix64) :
    (getNatGen b seed cache).1.b = b := by
  simp [getNatGen]
  split <;> rfl

/--
A generator that produces `Nat` values (including 0) biased towards numbers with a specific
bit-length. Each call:
1. Samples a bit length `b ∈ {0, 1, 2, ...}` from a geometric distribution with mean `meanBitLength`.
2. Looks up (or lazily creates) a `NatWithBitsRandomGen` for `b` in a cache.
3. Returns a `Nat` from that generator.

When `b = 0` the result is always `0`. For `b > 0` the result is in `[2^(b-1), 2^b - 1]`.
Cache entries are seeded deterministically via `deriveSeed seed (toString b)`.
-/
structure NatRandomGen (G : Type) [RandomGen G UInt64] where
  bitLenGen : NatGeometricRandomGen G
  -- Stores the raw SplitMix64 state for each bit length seen so far.
  -- Keyed by bit length; NatWithBitsRandomGen is reconstructed on use (with .b = key by construction).
  genCache : Std.HashMap Nat SplitMix64
  seed      : UInt64

/-- Create a `NatRandomGen` with geometric bit-length distribution with the given mean. -/
def mkNatRandomGen (meanBitLength : Rat) (seed : UInt64) : NatRandomGen SplitMix64 :=
  { bitLenGen := mkNatGeometricRandomGen meanBitLength (deriveSeed seed "bitLenGen"),
    genCache := {},
    seed      := seed}

def NatRandomGen.next {G : Type} [RandomGen G UInt64]
    (ng : NatRandomGen G) : Nat × NatRandomGen G :=
  let (b, bitLenGen') := RandomGen.next ng.bitLenGen
  let (natGen, cache') := getNatGen b ng.seed ng.genCache
  let (n, natGen') := NatWithBitsRandomGen.next natGen
  (n, { bitLenGen := bitLenGen', genCache := cache'.insert b natGen'.gen, seed := ng.seed})

instance {G : Type} [RandomGen G UInt64] : RandomGen (NatRandomGen G) Nat where
  next := NatRandomGen.next

/--
A generator that produces positive `Nat` values (≥ 1) biased towards numbers with a specific
bit-length. Identical to `NatRandomGen` except it uses `PositiveNatGeometricRandomGen` to
sample bit lengths from `{1, 2, 3, ...}`, ensuring `b ≥ 1` and thus the result is always ≥ 1.
-/
structure PositiveNatRandomGen (G : Type) [RandomGen G UInt64] where
  bitLenGen : PositiveNatGeometricRandomGen G
  genCache : Std.HashMap Nat SplitMix64
  seed      : UInt64

/-- Create a `PositiveNatRandomGen` with geometric bit-length distribution with the given mean. -/
def mkPositiveNatRandomGen (meanBitLength : Rat) (seed : UInt64) : PositiveNatRandomGen SplitMix64 :=
  { bitLenGen := mkPositiveNatGeometricRandomGen meanBitLength (deriveSeed seed "bitLenGen"),
    genCache := {},
    seed      := seed}

def PositiveNatRandomGen.next {G : Type} [RandomGen G UInt64]
    (ng : PositiveNatRandomGen G) : Nat × PositiveNatRandomGen G :=
  let (b, bitLenGen') := RandomGen.next ng.bitLenGen
  let (natGen, cache') := getNatGen b ng.seed ng.genCache
  let (n, natGen') := NatWithBitsRandomGen.next natGen
  (n, { bitLenGen := bitLenGen', genCache := cache'.insert b natGen'.gen, seed := ng.seed})

instance {G : Type} [RandomGen G UInt64] : RandomGen (PositiveNatRandomGen G) Nat where
  next := PositiveNatRandomGen.next

theorem positive_nat_random_gen_positive {G : Type} [RandomGen G UInt64]
    (ng : PositiveNatRandomGen G) :
    let (v, _) := PositiveNatRandomGen.next ng
    1 ≤ v := by
  simp only [PositiveNatRandomGen.next]
  -- Let b be the sampled bit length; PositiveNatGeometricRandomGen guarantees b ≥ 1
  set b := (PositiveNatGeometricRandomGen.next ng.bitLenGen).1 with hb_def
  have hb_pos : 1 ≤ b := positive_nat_geometric_positive ng.bitLenGen
  -- The natGen has .b = b by construction
  have hnatGen_b : (getNatGen b ng.seed ng.genCache).1.b = b :=
    getNatGen_b_eq b ng.seed ng.genCache
  -- Since b ≥ 1, natGen.b ≠ 0; by next_bounds the output is ≥ 2^(b-1) ≥ 1
  have hb_ne : (getNatGen b ng.seed ng.genCache).1.b ≠ 0 := by omega
  have hbounds := NatWithBitsRandomGen.next_bounds (getNatGen b ng.seed ng.genCache).1 hb_ne
  have hlow : 2 ^ ((getNatGen b ng.seed ng.genCache).1.b - 1)
      ≤ (NatWithBitsRandomGen.next (getNatGen b ng.seed ng.genCache).1).1 := hbounds.1
  have h2 : 1 ≤ 2 ^ ((getNatGen b ng.seed ng.genCache).1.b - 1) := Nat.one_le_two_pow
  have hfinal : 1 ≤ (NatWithBitsRandomGen.next (getNatGen b ng.seed ng.genCache).1).1 := by omega
  exact hfinal

end Azurite.Random
