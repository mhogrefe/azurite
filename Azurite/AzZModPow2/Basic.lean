import Azurite.AzNat.ModPow2
import Azurite.AzNat.LowMask
import Azurite.AzNat.Add
import Azurite.AzNat.AddModPow2
import Azurite.AzNat.Equiv.AddModPow2
import Azurite.AzNat.SubModPow2
import Azurite.AzNat.Equiv.SubModPow2
import Azurite.AzNat.MulModPow2.Dispatch
import Azurite.AzNat.Equiv.MulModPow2.Dispatch
import Azurite.AzNat.Sub
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.LowMask
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Tactic.Positivity

namespace Azurite

/-!
## `AzZModPow2 k` — integers modulo `2^k`

The `Pow2` specialization of the planned general `AzZMod`, backed by `AzNat`.
Reduction modulo `2^k` is masking the low `k` bits (`AzNat.modPow2`) — never
division — which is the reason to special-case powers of two.  `val` is the
canonical residue in `[0, 2^k)` (so equality is the real `DecidableEq`).  For
`k = 0` the only residue is `0` (`AzZModPow2 0` is trivial, matching `ZMod 1`).
-/

/-- Integers modulo `2^k`, as a canonical `AzNat` residue in `[0, 2^k)`. -/
structure AzZModPow2 (k : Nat) where
  /-- The canonical residue, in `[0, 2^k)`. -/
  val : AzNat
  /-- Canonicity: `val` is reduced modulo `2^k`. -/
  isLt : val.toNat < 2 ^ k
  deriving DecidableEq

namespace AzZModPow2

variable {k : Nat}

@[ext] theorem ext {a b : AzZModPow2 k} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

/-- Reduce an `AzNat` modulo `2^k` (low-`k`-bit mask). -/
def ofAzNat (k : Nat) (n : AzNat) : AzZModPow2 k :=
  ⟨n.modPow2 k, by rw [AzNat.toNat_modPow2]; exact Nat.mod_lt _ (by positivity)⟩

/-- The canonical residue as an `AzNat`. -/
def toAzNat (a : AzZModPow2 k) : AzNat := a.val

@[simp] theorem toAzNat_eq_val (a : AzZModPow2 k) : a.toAzNat = a.val := rfl

/-- Reducing an already-canonical residue is the identity. -/
@[simp] theorem ofAzNat_val (a : AzZModPow2 k) : ofAzNat k a.val = a := by
  apply ext
  show a.val.modPow2 k = a.val
  apply AzNat.toNat_injective
  rw [AzNat.toNat_modPow2, Nat.mod_eq_of_lt a.isLt]

instance : Zero (AzZModPow2 k) := ⟨⟨0, by rw [AzNat.toNat_zero]; positivity⟩⟩
instance : One (AzZModPow2 k) := ⟨ofAzNat k 1⟩
instance : Inhabited (AzZModPow2 k) := ⟨0⟩

@[simp] theorem val_zero : (0 : AzZModPow2 k).val = 0 := rfl

/-- Construct from a `Nat` literal (reduced modulo `2^k`). -/
def ofNat (k m : Nat) : AzZModPow2 k := ofAzNat k (AzNat.ofNat m)

/-- Numeric literals `≥ 2` reduce modulo `2^k`. -/
instance instOfNat {m : Nat} [m.AtLeastTwo] : OfNat (AzZModPow2 k) m :=
  ⟨ofNat k m⟩

/-- **Negation** in `ℤ / 2^k`: `-a = (2^k - a) mod 2^k`, as the two's complement
`((2^k - 1) - a) + 1`. The subtraction is against the all-ones mask `lowMask k`,
so it operates limb-by-limb directly on `val` (each output limb is the complement
of the corresponding limb of `val`) with no borrow, and the `+1` carry is short;
no `2^k` is materialized and no separate masking pass is needed. The `0` residue
is short-circuited (`-0 = 0`). -/
def neg (a : AzZModPow2 k) : AzZModPow2 k :=
  if h : a.val.limbs.size = 0 then 0
  else ⟨AzNat.lowMask k - a.val + 1, by
    rw [AzNat.toNat_add, AzNat.toNat_one, AzNat.toNat_sub, AzNat.toNat_lowMask]
    have h1 : a.val.toNat ≠ 0 := fun h0 => h ((AzNat.toNat_eq_zero_iff a.val).mp h0)
    have h2 : a.val.toNat < 2 ^ k := a.isLt
    have hpos : 0 < (2 : ℕ) ^ k := by positivity
    omega⟩

instance : Neg (AzZModPow2 k) := ⟨neg⟩

/-- **Addition** in `ℤ / 2^k`: `a + b mod 2^k`, by the fused single-pass
add-and-mask `AzNat.addModPow2`, which walks only the low `(k+63)/64` limbs and
masks to the low `k` bits, never forming the carry-limb that `AzNat.add` would
append. -/
def add (a b : AzZModPow2 k) : AzZModPow2 k :=
  ⟨AzNat.addModPow2 a.val b.val k, by
    rw [AzNat.toNat_addModPow2]; exact Nat.mod_lt _ (by positivity)⟩

instance : Add (AzZModPow2 k) := ⟨add⟩

/-- **Subtraction** in `ℤ / 2^k`: `a - b mod 2^k`, by the fused single-pass
subtract-and-mask `AzNat.subModPow2`, the borrow analogue of `add`.  It walks only
the low `(k+63)/64` limbs, subtracts with borrow, drops the final borrow-out (the
`+2^k` wrap when `a < b`), and masks to the low `k` bits. -/
def sub (a b : AzZModPow2 k) : AzZModPow2 k :=
  ⟨AzNat.subModPow2 a.val b.val k, by
    unfold AzNat.subModPow2
    rw [AzNat.toNat_modPow2]; exact Nat.mod_lt _ (by positivity)⟩

instance : Sub (AzZModPow2 k) := ⟨sub⟩

/-- **Multiplication** in `ℤ / 2^k`: `a * b mod 2^k`, by the size-dispatched
low-product `AzNat.mulDispatchModPow2`, which picks the schoolbook, Karatsuba, or
Toom-3 low product by operand size and computes only the low `(k+63)/64` limbs. -/
def mul (a b : AzZModPow2 k) : AzZModPow2 k :=
  ⟨AzNat.mulDispatchModPow2 a.val b.val k, by
    rw [AzNat.toNat_mulDispatchModPow2]; exact Nat.mod_lt _ (by positivity)⟩

instance : Mul (AzZModPow2 k) := ⟨mul⟩

end AzZModPow2

end Azurite

/-! ### Tests -/

section Tests

open Azurite Azurite.AzZModPow2

-- In `ℤ/16`: `-1 = 15`, `-0 = 0`, `-3 = 13`, `-(17 mod 16 = 1) = 15`.
#guard (-(AzZModPow2.ofNat 4 1)) == (AzZModPow2.ofNat 4 15)
#guard (-(AzZModPow2.ofNat 4 0)) == (AzZModPow2.ofNat 4 0)
#guard (-(AzZModPow2.ofNat 4 3)) == (AzZModPow2.ofNat 4 13)
#guard (-(AzZModPow2.ofNat 4 17)) == (AzZModPow2.ofNat 4 15)
-- In `ℤ/256`: `-200 = 56`.
#guard (-(AzZModPow2.ofNat 8 200)) == (AzZModPow2.ofNat 8 56)
-- Multi-limb `ℤ/2^128`: `-1 = 2^128 - 1`.
#guard (-(AzZModPow2.ofNat 128 1)) == (AzZModPow2.ofNat 128 (2 ^ 128 - 1))

-- Addition wraps mod `2^k`. `ℤ/16`: `9+10 = 19 ≡ 3`, `15+1 = 16 ≡ 0`.
#guard (AzZModPow2.ofNat 4 9 + AzZModPow2.ofNat 4 10) == (AzZModPow2.ofNat 4 3)
#guard (AzZModPow2.ofNat 4 15 + AzZModPow2.ofNat 4 1) == (AzZModPow2.ofNat 4 0)
#guard (AzZModPow2.ofNat 8 200 + AzZModPow2.ofNat 8 100) == (AzZModPow2.ofNat 8 44)
-- Multi-limb carry-out across the `2^128` boundary: `(2^128-1) + 1 ≡ 0`.
#guard (AzZModPow2.ofNat 128 (2 ^ 128 - 1) + AzZModPow2.ofNat 128 1) ==
  (AzZModPow2.ofNat 128 0)
#guard (AzZModPow2.ofNat 128 (2 ^ 128 - 1) + AzZModPow2.ofNat 128 5) ==
  (AzZModPow2.ofNat 128 4)

-- Subtraction wraps mod `2^k`. `ℤ/16`: `3-5 = -2 ≡ 14`, `5-3 = 2`, `0-1 ≡ 15`.
#guard (AzZModPow2.ofNat 4 3 - AzZModPow2.ofNat 4 5) == (AzZModPow2.ofNat 4 14)
#guard (AzZModPow2.ofNat 4 5 - AzZModPow2.ofNat 4 3) == (AzZModPow2.ofNat 4 2)
#guard (AzZModPow2.ofNat 4 0 - AzZModPow2.ofNat 4 1) == (AzZModPow2.ofNat 4 15)
#guard (AzZModPow2.ofNat 8 44 - AzZModPow2.ofNat 8 100) == (AzZModPow2.ofNat 8 200)
-- Multi-limb borrow across the `2^128` boundary: `0 - 1 ≡ 2^128 - 1`.
#guard (AzZModPow2.ofNat 128 0 - AzZModPow2.ofNat 128 1) ==
  (AzZModPow2.ofNat 128 (2 ^ 128 - 1))
#guard (AzZModPow2.ofNat 128 4 - AzZModPow2.ofNat 128 5) ==
  (AzZModPow2.ofNat 128 (2 ^ 128 - 1))

-- Multiplication wraps mod `2^k`. `ℤ/16`: `5*7 = 35 ≡ 3`, `15*15 = 225 ≡ 1`.
#guard (AzZModPow2.ofNat 4 5 * AzZModPow2.ofNat 4 7) == (AzZModPow2.ofNat 4 3)
#guard (AzZModPow2.ofNat 4 15 * AzZModPow2.ofNat 4 15) == (AzZModPow2.ofNat 4 1)
#guard (AzZModPow2.ofNat 8 200 * AzZModPow2.ofNat 8 100) == (AzZModPow2.ofNat 8 32)
#guard (AzZModPow2.ofNat 32 0 * AzZModPow2.ofNat 32 123456789) == (AzZModPow2.ofNat 32 0)
#guard (AzZModPow2.ofNat 32 1 * AzZModPow2.ofNat 32 123456789) ==
  (AzZModPow2.ofNat 32 123456789)
-- Multi-limb: `(2^64-1)^2 = 2^128 - 2^65 + 1 ≡ 1 (mod 2^64)`; full value mod `2^128`.
#guard (AzZModPow2.ofNat 64 (2 ^ 64 - 1) * AzZModPow2.ofNat 64 (2 ^ 64 - 1)) ==
  (AzZModPow2.ofNat 64 1)
#guard (AzZModPow2.ofNat 128 (2 ^ 64 - 1) * AzZModPow2.ofNat 128 (2 ^ 64 - 1)) ==
  (AzZModPow2.ofNat 128 ((2 ^ 64 - 1) * (2 ^ 64 - 1) % 2 ^ 128))

end Tests
