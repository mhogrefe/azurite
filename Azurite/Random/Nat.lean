import Azurite.Random.Gen

namespace Azurite.Random

/--
Recursively pull `count` 64-bit UInt64 blocks from the generator, assembling them into a
single large `Nat` using bitshifts.
-/
def genNatChunks {G : Type} [RandomGen G UInt64] : Nat → G → Nat × G
| 0, g => (0, g)
| n + 1, g =>
  let (u, g') : UInt64 × G := RandomGen.next g
  let (rest, g'') := genNatChunks n g'
  ((rest <<< 64) ||| u.toNat, g'')

/--
A generator that produces uniformly random `Nat` values of exactly `b` bits.
If `b = 0`, it produces exactly `0`.
If `b > 0`, it produces values in the range `[2^(b-1), 2^b - 1]`.
-/
structure NatWithBitsRandomGen (G : Type) [RandomGen G UInt64] where
  gen : G
  b : Nat
  deriving Repr

/-- Create a generic `NatWithBitsRandomGen` from a base generator `G` that outputs `UInt64` chunks. -/
def mkNatWithBitsRandomGen (b : Nat) (seed : UInt64) : NatWithBitsRandomGen SplitMix64 :=
  { gen := mkSplitMix64 seed, b := b }

def NatWithBitsRandomGen.next {G : Type} [RandomGen G UInt64] (bg : NatWithBitsRandomGen G) : Nat × NatWithBitsRandomGen G :=
  if bg.b == 0 then
    (0, bg)
  else
    -- Calculate how many 64-bit chunks we need to gather at least `b` bits.
    let chunks := (bg.b + 63) / 64
    let (raw, g') := genNatChunks chunks bg.gen

    -- We want exactly `b` bits, meaning range [2^(b-1), 2^b - 1].
    -- The lowest (b-1) bits are completely random.
    -- The top bit, at index (b-1), must be 1.
    let mask := (1 : Nat) <<< (bg.b - 1)
    let lower_mask := mask - 1
    let raw_lower := raw &&& lower_mask
    let final := raw_lower ||| mask

    (final, { bg with gen := g' })

theorem next_bounds {G : Type} [RandomGen G UInt64] (bg : NatWithBitsRandomGen G) (hb : bg.b ≠ 0) :
  let (v, _) := NatWithBitsRandomGen.next bg
  2^(bg.b - 1) ≤ v ∧ v < 2^bg.b := by
  change 2^(bg.b - 1) ≤ (NatWithBitsRandomGen.next bg).1 ∧ (NatWithBitsRandomGen.next bg).1 < 2^bg.b
  simp only [NatWithBitsRandomGen.next]
  split
  · -- case bg.b == 0
    rename_i h_eq_zero
    have h_b_zero : bg.b = 0 := of_decide_eq_true h_eq_zero
    contradiction
  · -- case bg.b != 0
    rename_i h_not_zero
    let chunks := (bg.b + 63) / 64
    set raw := (genNatChunks chunks bg.gen).1
    set mask := (1 : Nat) <<< (bg.b - 1) with h_mask_def
    set lower_mask := mask - 1

    have h_mask_eq : mask = 2^(bg.b - 1) := by
      rw [h_mask_def]
      rw [Nat.shiftLeft_eq]
      omega

    constructor
    · -- 2^(b-1) <= final
      have h1 : 2^(bg.b - 1) = mask := h_mask_eq.symm
      rw [h1]
      exact Nat.right_le_or
    · -- final < 2^b
      have h_raw_lower_lt : raw &&& lower_mask < 2^(bg.b - 1) := by
        have h_upper : lower_mask < 2^(bg.b - 1) := by
          change mask - 1 < 2^(bg.b - 1)
          rw [h_mask_eq]
          have : 1 ≤ 2^(bg.b - 1) := Nat.one_le_two_pow
          omega
        exact Nat.and_lt_two_pow raw h_upper

      have h_mask_lt : mask < 2^bg.b := by
        rw [h_mask_eq]
        apply Nat.pow_lt_pow_right (by decide)
        omega

      have h_mask_lt2 : 2^(bg.b - 1) < 2^bg.b := by
        apply Nat.pow_lt_pow_right (by decide)
        omega

      have h_raw_lower_lt2 : raw &&& lower_mask < 2^bg.b := Nat.lt_trans h_raw_lower_lt h_mask_lt2

      rw [h_mask_eq]
      exact Nat.or_lt_two_pow h_raw_lower_lt2 h_mask_lt2

instance {G : Type} [RandomGen G UInt64] : RandomGen (NatWithBitsRandomGen G) Nat where
  next := NatWithBitsRandomGen.next

/--
A generator that produces uniformly random `Nat` values of at most `b` bits.
If `b = 0`, it produces exactly `0`.
If `b > 0`, it produces values in the range `[0, 2^b - 1]`.
-/
structure NatUpToBitsRandomGen (G : Type) [RandomGen G UInt64] where
  gen : G
  b : Nat
  deriving Repr

/-- Create a generic `NatUpToBitsRandomGen` from a base generator `G` that outputs `UInt64` chunks. -/
def mkNatUpToBitsRandomGen (b : Nat) (seed : UInt64) : NatUpToBitsRandomGen SplitMix64 :=
  { gen := mkSplitMix64 seed, b := b }

def NatUpToBitsRandomGen.next {G : Type} [RandomGen G UInt64] (bg : NatUpToBitsRandomGen G) : Nat × NatUpToBitsRandomGen G :=
  if bg.b == 0 then
    (0, bg)
  else
    let chunks := (bg.b + 63) / 64
    let (raw, g') := genNatChunks chunks bg.gen
    let mask := (1 : Nat) <<< bg.b - 1
    let final := raw &&& mask
    (final, { bg with gen := g' })

theorem upto_bounds {G : Type} [RandomGen G UInt64] (bg : NatUpToBitsRandomGen G) (hb : bg.b ≠ 0) :
  let (v, _) := NatUpToBitsRandomGen.next bg
  v < 2^bg.b := by
  change (NatUpToBitsRandomGen.next bg).1 < 2^bg.b
  simp only [NatUpToBitsRandomGen.next]
  split
  · -- case bg.b == 0
    rename_i h_eq_zero
    have h_b_zero : bg.b = 0 := of_decide_eq_true h_eq_zero
    contradiction
  · -- case bg.b != 0
    rename_i h_not_zero
    let chunks := (bg.b + 63) / 64
    set raw := (genNatChunks chunks bg.gen).1
    set mask := ((1 : Nat) <<< bg.b) - 1 with h_mask_def

    have h_upper : mask < 2^bg.b := by
      rw [h_mask_def]
      rw [Nat.shiftLeft_eq]
      have : 1 ≤ 2^bg.b := Nat.one_le_two_pow
      omega

    exact Nat.and_lt_two_pow raw h_upper

instance {G : Type} [RandomGen G UInt64] : RandomGen (NatUpToBitsRandomGen G) Nat where
  next := NatUpToBitsRandomGen.next

/--
A generator that produces uniformly random `Nat` values strictly less than `k`.
Uses a rejection sampling approach with a maximum of `1024` attempts before defaulting to `0`.
-/
structure NatLessThanRandomGen (G : Type) [RandomGen G UInt64] where
  gen : G
  k : Nat
  b : Nat
  deriving Repr

/-- Create a generic `NatLessThanRandomGen` with a defined upper bound `k`. -/
def mkNatLessThanRandomGen (k : Nat) (seed : UInt64) : NatLessThanRandomGen SplitMix64 :=
  let b := if k == 0 then 0 else k.log2 + 1
  { gen := mkSplitMix64 seed, k := k, b := b }

/-- Internal retry loop mapping out `1024` attempts bounded by `fuel`. -/
def NatLessThanRandomGen.nextLoop {G : Type} [RandomGen G UInt64] :
  Nat → Nat → Nat → G → Nat × G
| 0, _, _, g => (0, g)
| fuel + 1, k, b, g =>
  let chunks := (b + 63) / 64
  let (raw, g') := genNatChunks chunks g
  let mask := (1 : Nat) <<< b - 1
  let final := raw &&& mask
  if final < k then
    (final, g')
  else
    NatLessThanRandomGen.nextLoop fuel k b g'

def NatLessThanRandomGen.next {G : Type} [RandomGen G UInt64] (bg : NatLessThanRandomGen G) : Nat × NatLessThanRandomGen G :=
  if bg.k ≤ 1 then
    (0, bg)
  else
    let (val, g') := NatLessThanRandomGen.nextLoop 1024 bg.k bg.b bg.gen
    (val, { bg with gen := g' })

theorem less_than_loop_bounds {G : Type} [RandomGen G UInt64] (fuel k b : Nat) (g : G) (hk : k ≠ 0) :
  let (v, _) := NatLessThanRandomGen.nextLoop fuel k b g
  v < k := by
  induction fuel generalizing g with
  | zero =>
    change 0 < k
    omega
  | succ f ih =>
    change (NatLessThanRandomGen.nextLoop (f + 1) k b g).1 < k
    simp only [NatLessThanRandomGen.nextLoop]
    split
    · rename_i h_lt
      exact h_lt
    · rename_i h_not_lt
      exact ih _

theorem less_than_bounds {G : Type} [RandomGen G UInt64] (bg : NatLessThanRandomGen G) (hk : bg.k ≠ 0) :
  let (v, _) := NatLessThanRandomGen.next bg
  v < bg.k := by
  change (NatLessThanRandomGen.next bg).1 < bg.k
  simp only [NatLessThanRandomGen.next]
  split
  · -- case bg.k <= 1
    rename_i h_le_one
    have h_k_one : bg.k = 1 := by omega
    omega
  · -- case bg.k > 1
    exact less_than_loop_bounds 1024 bg.k bg.b bg.gen hk

instance {G : Type} [RandomGen G UInt64] : RandomGen (NatLessThanRandomGen G) Nat where
  next := NatLessThanRandomGen.next

end Azurite.Random
