import Azurite.AzNat.Add
import Azurite.AzNat.Div
import Azurite.AzNat.Sub
import Azurite.AzNat.Mul
import Azurite.AzNat.Square
import Azurite.AzNat.Compare
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzNat.Equiv.Square.ToomCook3
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Basic
import Azurite.Algorithm.FastPow
import Mathlib.Data.Nat.Cast.Defs

namespace Azurite

/-!
## `AzZMod m` — integers modulo a general `AzNat`

The general companion of [`AzZModPow2`](../AzZModPow2/Basic.lean): residues modulo
an arbitrary `AzNat` modulus `m`, with `AzZModPow2 k` the power-of-two
specialization where reduction is masking rather than division.

The modulus is an **`AzNat` value index** (not a `Nat`).  This is the deliberate
choice that keeps computation limb-level: reduction is `AzNat.mod` against `m`,
which is already an `AzNat` and so never has to be reconstructed from a `Nat`
literal (that would route a possibly huge modulus through `Nat` arithmetic).
`AzZModPow2 k` can index by the small `Nat` `k` only because its modulus `2^k`
is never materialized — masking needs just the bit-count.

`val` is the canonical residue in `[0, m)` (so equality is the real
`DecidableEq`).  A nonzero modulus (`NeZero m.toNat`) is required for the type to
be inhabited and for the `ZMod m.toNat` bridge; it is taken as an instance
argument wherever needed, mirroring `ZMod`'s `[NeZero n]`.
-/

/-- Integers modulo `m`, as a canonical `AzNat` residue in `[0, m)`. -/
structure AzZMod (m : AzNat) where
  /-- The canonical residue, in `[0, m)`. -/
  val : AzNat
  /-- Canonicity: `val` is reduced modulo `m`. -/
  isLt : val.toNat < m.toNat
  deriving DecidableEq

namespace AzZMod

variable {m : AzNat}

@[ext] theorem ext {a b : AzZMod m} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

/-- `NeZero` of the value of an `AzNat` literal, so a literal modulus such as
`AzNat.ofNat 7` automatically supplies the `NeZero m.toNat` the residue
operations need. -/
instance instNeZeroToNatOfNat (n : Nat) [NeZero n] : NeZero (AzNat.ofNat n).toNat :=
  ⟨by rw [AzNat.toNat_ofNat]; exact NeZero.ne n⟩

/-- Reduce an `AzNat` modulo `m` (limb-level `AzNat.mod`). -/
def ofAzNat (m : AzNat) [NeZero m.toNat] (n : AzNat) : AzZMod m :=
  ⟨n % m, by rw [AzNat.toNat_mod]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩

/-- The canonical residue as an `AzNat`. -/
def toAzNat (a : AzZMod m) : AzNat := a.val

@[simp] theorem toAzNat_eq_val (a : AzZMod m) : a.toAzNat = a.val := rfl

/-- Reducing an already-canonical residue is the identity. -/
@[simp] theorem ofAzNat_val [NeZero m.toNat] (a : AzZMod m) : ofAzNat m a.val = a := by
  apply ext
  show a.val % m = a.val
  apply AzNat.toNat_injective
  rw [AzNat.toNat_mod, Nat.mod_eq_of_lt a.isLt]

instance [NeZero m.toNat] : Zero (AzZMod m) :=
  ⟨⟨0, by rw [AzNat.toNat_zero]; exact Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
instance [NeZero m.toNat] : One (AzZMod m) := ⟨ofAzNat m 1⟩
instance [NeZero m.toNat] : Inhabited (AzZMod m) := ⟨0⟩

@[simp] theorem val_zero [NeZero m.toNat] : (0 : AzZMod m).val = 0 := rfl

/-- Construct from a `Nat` literal (reduced modulo `m`). -/
def ofNat (m : AzNat) [NeZero m.toNat] (a : Nat) : AzZMod m := ofAzNat m (AzNat.ofNat a)

/-- Numeric literals `≥ 2` reduce modulo `m`. -/
instance instOfNat [NeZero m.toNat] {a : Nat} [a.AtLeastTwo] : OfNat (AzZMod m) a :=
  ⟨ofNat m a⟩

/-- **Negation** in `ℤ / m`: `-a = (m - a) mod m`.  Since `a` is canonical
(`a.val < m`), the difference `m - a.val` is already in `[0, m)`, so the
truncating `AzNat` subtraction needs no further reduction; the `0` residue is
short-circuited (`-0 = 0`). -/
def neg [NeZero m.toNat] (a : AzZMod m) : AzZMod m :=
  if h : a.val.limbs.size = 0 then 0
  else ⟨m - a.val, by
    rw [AzNat.toNat_sub]
    have h1 : a.val.toNat ≠ 0 := fun h0 => h ((AzNat.toNat_eq_zero_iff a.val).mp h0)
    have h2 : a.val.toNat < m.toNat := a.isLt
    omega⟩

instance [NeZero m.toNat] : Neg (AzZMod m) := ⟨neg⟩

/-- **Addition** in `ℤ / m`: add the residues, then conditionally subtract `m`.
Both inputs are canonical (`< m`), so the sum is `< 2m`; a single comparison and
truncating subtraction reduce it back into `[0, m)` — cheaper than a full
division. -/
def add [NeZero m.toNat] (a b : AzZMod m) : AzZMod m :=
  let s := a.val + b.val
  if h : m ≤ s then
    ⟨s - m, by
      have hs : s.toNat = a.val.toNat + b.val.toNat := AzNat.toNat_add a.val b.val
      have hms : m.toNat ≤ s.toNat := (AzNat.le_iff_toNat_le m s).mp h
      rw [AzNat.toNat_sub]
      have ha : a.val.toNat < m.toNat := a.isLt
      have hb : b.val.toNat < m.toNat := b.isLt
      omega⟩
  else
    ⟨s, by
      have hns : ¬ m.toNat ≤ s.toNat := fun hle => h ((AzNat.le_iff_toNat_le m s).mpr hle)
      omega⟩

instance [NeZero m.toNat] : Add (AzZMod m) := ⟨add⟩

/-- **Subtraction** in `ℤ / m`: the borrow analogue of `add`.  When `b.val ≤ a.val`
the truncating difference `a.val - b.val` is already canonical; otherwise add the
modulus first (`a.val + m - b.val`) to undo the borrow, landing back in `[0, m)`. -/
def sub [NeZero m.toNat] (a b : AzZMod m) : AzZMod m :=
  if h : b.val ≤ a.val then
    ⟨a.val - b.val, by
      rw [AzNat.toNat_sub]
      have ha : a.val.toNat < m.toNat := a.isLt
      omega⟩
  else
    ⟨a.val + m - b.val, by
      rw [AzNat.toNat_sub, AzNat.toNat_add]
      have hba : ¬ b.val.toNat ≤ a.val.toNat :=
        fun hle => h ((AzNat.le_iff_toNat_le b.val a.val).mpr hle)
      have hb : b.val.toNat < m.toNat := b.isLt
      omega⟩

instance [NeZero m.toNat] : Sub (AzZMod m) := ⟨sub⟩

/-- **Multiplication** in `ℤ / m`: the full product reduced modulo `m`
(`(a * b) mod m`).  Straightforward for now — a divisionless reduction
(Barrett/Montgomery) is a future optimization. -/
def mul [NeZero m.toNat] (a b : AzZMod m) : AzZMod m := ofAzNat m (a.val * b.val)

instance [NeZero m.toNat] : Mul (AzZMod m) := ⟨mul⟩

/-- **Squaring** in `ℤ / m`, via the fast `AzNat.square` (exploiting symmetry)
reduced modulo `m`.  Overrides the default `x * x` so a future sliding-window
power can use the cheaper square. -/
instance instSquare [NeZero m.toNat] : Azurite.Square (AzZMod m) where
  square a := ofAzNat m (AzNat.square a.val)
  square_eq a := by
    apply ext
    apply AzNat.toNat_injective
    show (AzNat.square a.val % m).toNat = (a.val * a.val % m).toNat
    rw [AzNat.toNat_mod, AzNat.toNat_mod, AzNat.toNat_square, AzNat.toNat_mul, pow_two]

end AzZMod

end Azurite

/-! ### Tests -/

section Tests

open Azurite Azurite.AzZMod

-- In `ℤ/7`: `19 ≡ 5`, `7 ≡ 0`, `6` is canonical.
#guard AzZMod.ofNat (AzNat.ofNat 7) 19 == AzZMod.ofNat (AzNat.ofNat 7) 5
#guard AzZMod.ofNat (AzNat.ofNat 7) 7 == AzZMod.ofNat (AzNat.ofNat 7) 0
#guard AzZMod.ofNat (AzNat.ofNat 7) 6 == AzZMod.ofNat (AzNat.ofNat 7) 6
-- A non-power-of-two, multi-digit modulus `ℤ/1000`: `123456 ≡ 456`.
#guard AzZMod.ofNat (AzNat.ofNat 1000) 123456 == AzZMod.ofNat (AzNat.ofNat 1000) 456
-- Reduction is genuine division, not masking: `ℤ/100`, `250 ≡ 50`.
#guard AzZMod.ofNat (AzNat.ofNat 100) 250 == AzZMod.ofNat (AzNat.ofNat 100) 50

-- Negation in `ℤ/7`: `-3 ≡ 4`, `-0 ≡ 0`, `-1 ≡ 6`; multi-digit `ℤ/1000`: `-456 ≡ 544`.
#guard -(AzZMod.ofNat (AzNat.ofNat 7) 3) == AzZMod.ofNat (AzNat.ofNat 7) 4
#guard -(AzZMod.ofNat (AzNat.ofNat 7) 0) == AzZMod.ofNat (AzNat.ofNat 7) 0
#guard -(AzZMod.ofNat (AzNat.ofNat 7) 1) == AzZMod.ofNat (AzNat.ofNat 7) 6
#guard -(AzZMod.ofNat (AzNat.ofNat 1000) 456) == AzZMod.ofNat (AzNat.ofNat 1000) 544

-- Addition in `ℤ/7`: `4+5 = 9 ≡ 2` (wraps), `2+3 = 5` (no wrap); `ℤ/1000`: `600+700 = 1300 ≡ 300`.
#guard AzZMod.ofNat (AzNat.ofNat 7) 4 + AzZMod.ofNat (AzNat.ofNat 7) 5 == AzZMod.ofNat (AzNat.ofNat 7) 2
#guard AzZMod.ofNat (AzNat.ofNat 7) 2 + AzZMod.ofNat (AzNat.ofNat 7) 3 == AzZMod.ofNat (AzNat.ofNat 7) 5
#guard AzZMod.ofNat (AzNat.ofNat 1000) 600 + AzZMod.ofNat (AzNat.ofNat 1000) 700 ==
  AzZMod.ofNat (AzNat.ofNat 1000) 300

-- Subtraction in `ℤ/7`: `5-3 = 2` (no borrow), `3-5 ≡ 5` (borrow), `0-1 ≡ 6`; `ℤ/1000`: `300-700 ≡ 600`.
#guard AzZMod.ofNat (AzNat.ofNat 7) 5 - AzZMod.ofNat (AzNat.ofNat 7) 3 == AzZMod.ofNat (AzNat.ofNat 7) 2
#guard AzZMod.ofNat (AzNat.ofNat 7) 3 - AzZMod.ofNat (AzNat.ofNat 7) 5 == AzZMod.ofNat (AzNat.ofNat 7) 5
#guard AzZMod.ofNat (AzNat.ofNat 7) 0 - AzZMod.ofNat (AzNat.ofNat 7) 1 == AzZMod.ofNat (AzNat.ofNat 7) 6
#guard AzZMod.ofNat (AzNat.ofNat 1000) 300 - AzZMod.ofNat (AzNat.ofNat 1000) 700 ==
  AzZMod.ofNat (AzNat.ofNat 1000) 600

-- Multiplication in `ℤ/7`: `5*3 = 15 ≡ 1`, `4*5 = 20 ≡ 6`, `6*6 = 36 ≡ 1`; `ℤ/1000`: `123*456 = 56088 ≡ 88`.
#guard AzZMod.ofNat (AzNat.ofNat 7) 5 * AzZMod.ofNat (AzNat.ofNat 7) 3 == AzZMod.ofNat (AzNat.ofNat 7) 1
#guard AzZMod.ofNat (AzNat.ofNat 7) 4 * AzZMod.ofNat (AzNat.ofNat 7) 5 == AzZMod.ofNat (AzNat.ofNat 7) 6
#guard AzZMod.ofNat (AzNat.ofNat 7) 6 * AzZMod.ofNat (AzNat.ofNat 7) 6 == AzZMod.ofNat (AzNat.ofNat 7) 1
#guard AzZMod.ofNat (AzNat.ofNat 1000) 123 * AzZMod.ofNat (AzNat.ofNat 1000) 456 ==
  AzZMod.ofNat (AzNat.ofNat 1000) 88

-- Squaring in `ℤ/7`: `3² = 9 ≡ 2`, `6² = 36 ≡ 1`; `ℤ/1000`: `123² = 15129 ≡ 129`.
#guard Square.square (AzZMod.ofNat (AzNat.ofNat 7) 3) == AzZMod.ofNat (AzNat.ofNat 7) 2
#guard Square.square (AzZMod.ofNat (AzNat.ofNat 7) 6) == AzZMod.ofNat (AzNat.ofNat 7) 1
#guard Square.square (AzZMod.ofNat (AzNat.ofNat 1000) 123) == AzZMod.ofNat (AzNat.ofNat 1000) 129

end Tests
