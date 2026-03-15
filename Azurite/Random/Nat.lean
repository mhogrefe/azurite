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
structure NatWithBitsGen (G : Type) [RandomGen G UInt64] where
  gen : G
  b : Nat
  deriving Repr

/-- Create a generic `NatWithBitsGen` from a base generator `G` that outputs `UInt64` chunks. -/
def mkNatWithBitsGen (b : Nat) (seed : UInt64) : NatWithBitsGen SplitMix64 :=
  { gen := mkSplitMix64 seed, b := b }

def NatWithBitsGen.next {G : Type} [RandomGen G UInt64] (bg : NatWithBitsGen G) : Nat × NatWithBitsGen G :=
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

theorem next_bounds {G : Type} [RandomGen G UInt64] (bg : NatWithBitsGen G) (hb : bg.b ≠ 0) :
  let (v, _) := NatWithBitsGen.next bg
  2^(bg.b - 1) ≤ v ∧ v < 2^bg.b := by
  change 2^(bg.b - 1) ≤ (NatWithBitsGen.next bg).1 ∧ (NatWithBitsGen.next bg).1 < 2^bg.b
  simp only [NatWithBitsGen.next]
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

instance {G : Type} [RandomGen G UInt64] : RandomGen (NatWithBitsGen G) Nat where
  next := NatWithBitsGen.next

end Azurite.Random
