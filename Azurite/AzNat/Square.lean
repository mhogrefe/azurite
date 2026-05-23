import Azurite.AzNat.Square.Schoolbook
import Azurite.AzNat.Square.Karatsuba
import Azurite.AzNat.Square.ToomCook3

namespace Azurite.AzNat

-- ── Limb-level dispatcher and AzNat wrapper ─────────────────────────────────

/-- Default minimum-length threshold for Karatsuba squaring (in 64-bit limbs).
    Below this size the `squareLimbs` dispatcher picks `schoolbookSquareLimbs`;
    above it, `karatsubaSquareLimbs`. Unlike `mulDispatchThreshold` there is
    no balance ratio because squaring takes a single operand — the recursive
    split's two halves always differ in length by at most one. -/
def squareDispatchThreshold : Nat := 32

/-- Default cutoff (in limbs) for switching Karatsuba squaring → Toom-Cook 3
    squaring.  Tuned via `tune_aznat_square_toomcook3`: at
    `len ≥ 128` (≈ 8192 bits), Toom-Cook 3 squaring beats Karatsuba
    squaring.  Half the mul-side crossover (256) since each Toom-Cook 3
    level for squaring replaces five multiplications with five squarings,
    making the per-level overhead pay off sooner. -/
def squareDispatchToomCook3Cutoff : Nat := 128

/-- Parametrized limb-level square dispatcher (used directly by `Tune`).
    Three-way dispatch:

    * `len < minThreshold` → `schoolbookSquareLimbs`;
    * `minThreshold ≤ len < toomCook3Cutoff` → `karatsubaSquareLimbs`;
    * `toomCook3Cutoff ≤ len` → `toomCook3SquareLimbs`. -/
def squareLimbsParam (minThreshold toomCook3Cutoff : Nat) (a : Array UInt64)
    (lo len : Nat) (hA : lo + len ≤ a.size) : Array UInt64 :=
  if toomCook3Cutoff ≤ len then
    toomCook3SquareLimbs toomCook3Cutoff minThreshold a lo len hA
  else if minThreshold ≤ len then
    karatsubaSquareLimbs minThreshold a lo len hA
  else
    schoolbookSquareLimbs a lo len hA

/-- Limb-level squaring using the default dispatch parameters. -/
def squareLimbs (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) : Array UInt64 :=
  squareLimbsParam squareDispatchThreshold squareDispatchToomCook3Cutoff a lo len hA

/-- AzNat wrapper for `squareLimbsParam`; lets the tuner sweep the
    dispatch parameters. -/
def squareDispatchParam (minThreshold toomCook3Cutoff : Nat) (a : AzNat) : AzNat :=
  ofLimbs (squareLimbsParam minThreshold toomCook3Cutoff a.limbs 0 a.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Square an `AzNat`.  Dispatches three-way between schoolbook, Karatsuba,
    and Toom-Cook 3 via `squareLimbs`. -/
def square (a : AzNat) : AzNat :=
  ofLimbs (squareLimbs a.limbs 0 a.limbs.size (Nat.zero_add _ ▸ Nat.le_refl _))

-- ── Always-one-algorithm wrappers (for benchmarking) ────────────────────────

/-- Square an `AzNat` forced to use `schoolbookSquareLimbs`. For benchmarking;
    callers should normally use `square`. -/
def squareSchoolbook (a : AzNat) : AzNat :=
  ofLimbs (schoolbookSquareLimbs a.limbs 0 a.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Square an `AzNat` forced to use `karatsubaSquareLimbs`. For benchmarking;
    parallels `mulKaratsuba`. -/
def squareKaratsuba (threshold : Nat) (a : AzNat) : AzNat :=
  ofLimbs (karatsubaSquareLimbs threshold a.limbs 0 a.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Square an `AzNat` forced to use `toomCook3SquareLimbs`.  For benchmarking;
    parallels `mulToomCook3`.  Takes the two thresholds explicitly so the
    benchmark can use the same fallback as the mul-side. -/
def squareToomCook3 (toomThreshold karaThreshold : Nat) (a : AzNat) : AzNat :=
  ofLimbs (toomCook3SquareLimbs toomThreshold karaThreshold a.limbs 0 a.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _))

end Azurite.AzNat
