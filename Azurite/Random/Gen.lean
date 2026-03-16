import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Azurite.Random
/--
A simple somewhat-fast implementation of a pseudorandom number generator using SplitMix64.
Not cryptographically secure. Gives a sequence of 64-bit unsigned integers.
-/
structure SplitMix64 where
  state : UInt64
  deriving Inhabited, Repr

/-- Create a SplitMix64 PRNG instance from a seed. -/
def mkSplitMix64 (seed : UInt64) : SplitMix64 :=
  { state := seed }

/-- 
A generic typeclass for a pseudorandom number generator mapping a Generator state `G` to
randomness of type `α`.
-/
class RandomGen (G : Type u) (α : Type v) where
  next : G → α × G
/-- The mixing constant used in SplitMix64 state advancement. -/
def SplitMix64.gamma : Nat := 0x9e3779b97f4a7c15

lemma SplitMix64.gamma_odd : Odd SplitMix64.gamma := by decide

/-- Proves that the gamma multiplier is coprime to the $2^{64}$ maximum state bounds. -/
lemma SplitMix64.gamma_coprime_2_64 : Nat.Coprime SplitMix64.gamma (2^64) := by
  have h_pow : Nat.Coprime SplitMix64.gamma (2^64) ↔ Nat.Coprime SplitMix64.gamma 2 :=
    Nat.coprime_pow_right_iff (by decide) SplitMix64.gamma 2
  rw [h_pow]
  rw [Nat.coprime_two_right]
  exact SplitMix64.gamma_odd

/--
Advance the SplitMix64 state and return the random result along with the new state.
Based on the standard 64-bit SplitMix64 reference implementation.
-/
def SplitMix64.next (r : SplitMix64) : UInt64 × SplitMix64 :=
  let nextState := r.state + 0x9e3779b97f4a7c15
  let z1 := nextState
  let z2 := (z1 ^^^ (z1 >>> 30)) * 0xbf58476d1ce4e5b9
  let z3 := (z2 ^^^ (z2 >>> 27)) * 0x94d049bb133111eb
  let z4 := z3 ^^^ (z3 >>> 31)
  (z4, { state := nextState })

instance : RandomGen SplitMix64 UInt64 where
  next := SplitMix64.next

def mix_nat (state : Nat) : Nat :=
  let z1 := state % (2^64)
  let z2 := (z1 ^^^ (z1 >>> 30)) * 0xbf58476d1ce4e5b9 % (2^64)
  let z3 := (z2 ^^^ (z2 >>> 27)) * 0x94d049bb133111eb % (2^64)
  (z3 ^^^ (z3 >>> 31)) % (2^64)

def stateSeq (seed : Nat) : Nat → Nat
| 0 => seed % (2^64)
| n + 1 => (stateSeq seed n + SplitMix64.gamma) % (2^64)

def valSeq (seed : Nat) (n : Nat) : Nat :=
  mix_nat (stateSeq seed n)

def eventually_constant (seed : Nat) :=
  ∃ c N, ∀ n ≥ N, valSeq seed n = c

lemma mix_not_constant : mix_nat 0 ≠ mix_nat 1 := by decide

/-- Derive a new `UInt64` seed from a base seed and a string tag, by XORing with the tag's hash.
Useful for deterministically creating independent seeds from a single root seed. -/
def deriveSeed (seed : UInt64) (tag : String) : UInt64 :=
  seed ^^^ UInt64.ofNat (hash tag).toNat
