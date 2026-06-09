import Azurite.AzNat.GetBits
import Azurite.AzNat.Size
import Azurite.AzNat.Compare
import Azurite.AzNat.Equiv.GetBits
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.Compare
import Mathlib.Data.Nat.Size

/-!
# Normalized comparison (allocation-free `AzNat`)

`normalizedCompare x y` compares `x` and `y` as if their bit encodings were left-aligned to a
common length — equivalently, for positive inputs, it compares the reals `x / 2^(size x)` and
`y / 2^(size y)`, both in `[1/2, 1)`.

The implementation is **allocation-free**: instead of materialising a shifted copy of an operand,
it reads the `k`-th limb of `x · 2^shift` directly from `x`'s limbs via `getBitsAsLimb` (one
`UInt64`), comparing top-down against `y`'s limbs.

Correctness (`normalizedCompare_eq_normalizedCompareNat`) is proved by reducing the loop to the
radix-`2^64` comparison of `x.toNat · 2^shift` and `y.toNat`, then bridging to the legacy
`normalizedCompareNat` (whose rational semantics is `normalizedCompareNat_eq_rat`).
-/

namespace Azurite.AzNat

/-! ### Implementation -/

/-- The `k`-th 64-bit limb of `a · 2^shift` (with `shift = 64·q + r`, `r < 64`), read directly from
`a`'s limbs without materialising the shifted value. Equals `a.toNat · 2^shift / 2^(64k) % 2^64`. -/
def shiftedLimb (a : AzNat) (q r k : Nat) (hr : r < 64) : UInt64 :=
  if k < q then 0
  else if k = q then (a.getBitsAsLimb 0 (64 - r) (by omega)) <<< UInt64.ofNat r
  else a.getBitsAsLimb (64 * (k - q) - r) (64 * (k - q) - r + 64) (by omega)

/-- Compare `a · 2^shift` against `b` (with `shift = 64·q + r`) by reading `a`'s shifted limbs on
the fly and `b`'s limbs via `getBitsAsLimb`, lexicographically from limb `k-1` down to `0`. -/
def cmpShiftedLimbs (a b : AzNat) (q r : Nat) (hr : r < 64) (k : Nat) : Ordering :=
  match k with
  | 0 => Ordering.eq
  | k + 1 =>
    match Ord.compare (shiftedLimb a q r k hr) (b.getBitsAsLimb (64 * k) (64 * k + 64) (by omega)) with
    | Ordering.eq => cmpShiftedLimbs a b q r hr k
    | o => o

/-- `normalizedCompare x y` compares `x` and `y` with their most-significant bits aligned.
Allocation-free: the size difference is absorbed by reading shifted limbs on the fly. -/
def normalizedCompare (x y : AzNat) : Ordering :=
  if x = 0 then
    if y = 0 then Ordering.eq else Ordering.lt
  else if y = 0 then
    Ordering.gt
  else
    let sx := x.size
    let sy := y.size
    if sx = sy then
      compare x y
    else if sx < sy then
      let shift := sy - sx
      cmpShiftedLimbs x y (shift / 64) (shift % 64) (Nat.mod_lt _ (by decide)) y.limbs.size
    else
      let shift := sx - sy
      (cmpShiftedLimbs y x (shift / 64) (shift % 64) (Nat.mod_lt _ (by decide)) x.limbs.size).swap

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

#guard normalizedCompare (ofNat 0) (ofNat 0) == Ordering.eq
#guard normalizedCompare (ofNat 0) (ofNat 1) == Ordering.lt
#guard normalizedCompare (ofNat 1) (ofNat 0) == Ordering.gt
#guard normalizedCompare (ofNat 2) (ofNat 4) == Ordering.eq
#guard normalizedCompare (ofNat 5) (ofNat 11) == Ordering.lt
#guard normalizedCompare (ofNat 5) (ofNat 9) == Ordering.gt
#guard normalizedCompare (ofNat (2 ^ 200)) (ofNat (2 ^ 500)) == Ordering.eq
#guard normalizedCompare (ofNat (2 ^ 500 + 1)) (ofNat (2 ^ 200 + 1)) == Ordering.lt
#guard normalizedCompare (ofNat (2 ^ 200 + 1)) (ofNat (2 ^ 500 + 1)) == Ordering.gt

-- Cross-check against a direct cross-multiplication reference, over many sizes / shift residues
-- (including cross-limb shifts). This is exactly the correctness statement
-- `normalizedCompare_eq_cross` proved in `Equiv/NormalizedCompare`.
private def refNormCompare (a b : ℕ) : Ordering := Ord.compare (a * 2 ^ Nat.size b) (b * 2 ^ Nat.size a)

#guard (List.range 40).all (fun a => (List.range 40).all (fun b => normalizedCompare (ofNat a) (ofNat b) == refNormCompare a b))
#guard [0, 1, 5, 63, 64, 65, 127, 200, 1000].all (fun s => [1, 7, 12345].all (fun t => normalizedCompare (ofNat (2 ^ s + t)) (ofNat (2 ^ 333 + 99)) == refNormCompare (2 ^ s + t) (2 ^ 333 + 99)))

end Tests

end Azurite.AzNat
