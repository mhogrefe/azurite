import Azurite.AzNat.Square.Schoolbook
import Azurite.AzNat.Square.Karatsuba

namespace Azurite.AzNat

-- ── Limb-level dispatcher and AzNat wrapper ─────────────────────────────────

/-- Default minimum-length threshold for Karatsuba squaring (in 64-bit limbs).
    Below this size the `squareLimbs` dispatcher picks `schoolbookSquareLimbs`;
    above it, `karatsubaSquareLimbs`. Unlike `mulDispatchThreshold` there is
    no balance ratio because squaring takes a single operand — the recursive
    split's two halves always differ in length by at most one. -/
def squareDispatchThreshold : Nat := 32

/-- Parametrized limb-level square dispatcher (used directly by `Tune`).
    Dispatches between `schoolbookSquareLimbs` and `karatsubaSquareLimbs`
    on a single criterion: `lenLimbs ≥ minThreshold` → Karatsuba, else
    schoolbook. -/
def squareLimbsParam (minThreshold : Nat) (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) : Array UInt64 :=
  if minThreshold ≤ len then
    karatsubaSquareLimbs minThreshold a lo len hA
  else
    schoolbookSquareLimbs a lo len hA

/-- Limb-level squaring using the default `squareDispatchThreshold`. -/
def squareLimbs (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) : Array UInt64 :=
  squareLimbsParam squareDispatchThreshold a lo len hA

/-- AzNat wrapper for `squareLimbsParam`; lets the tuner sweep `minThreshold`. -/
def squareDispatchParam (minThreshold : Nat) (a : AzNat) : AzNat :=
  ofLimbs (squareLimbsParam minThreshold a.limbs 0 a.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Square an `AzNat`. Dispatches between schoolbook and Karatsuba via
    `squareLimbs`. -/
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

end Azurite.AzNat
