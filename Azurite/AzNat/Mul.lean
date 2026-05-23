import Azurite.AzNat.Mul.Schoolbook
import Azurite.AzNat.Mul.Karatsuba

namespace Azurite.AzNat

-- ── Limb-level dispatcher and AzNat wrapper ─────────────────────────────────

/-- Default minimum-length threshold for Karatsuba (in 64-bit limbs).  Tuned
    via `Azurite.AzNat.Tune.tuneAzNatDispatch2D`: the 2-D `(minThreshold, k)`
    sweep over an unfiltered random distribution favors a low threshold
    combined with the ratio criterion below. -/
def mulDispatchThreshold : Nat := 16

/-- Default ratio threshold (numerator/denominator).  Karatsuba is used when
    `lenMin / lenMax ≥ mulDispatchKNum / mulDispatchKDen`, i.e.
    `mulDispatchKDen · lenMin ≥ mulDispatchKNum · lenMax`.

    Tuner result: `k ≈ 1/4` (≈ 22% faster than the old `1/2`). -/
def mulDispatchKNum : Nat := 1
def mulDispatchKDen : Nat := 4

/-- Parametrized limb-level dispatcher (used directly by `Tune`).  Dispatches
    between `schoolbookMulLimbs` and `karatsubaMulLimbs` based on:

    * `lenMin ≥ minThreshold`  — both operands have non-trivial size, AND
    * `kDen · lenMin ≥ kNum · lenMax`  — the shorter operand is not too short
      relative to the longer (ratio `kNum/kDen`).

    Both criteria must hold to pick Karatsuba; otherwise schoolbook. -/
def mulLimbsParam (minThreshold kNum kDen : Nat)
    (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) : Array UInt64 :=
  let lenMax := max lenA lenB
  let lenMin := min lenA lenB
  if minThreshold ≤ lenMin && kDen * lenMin ≥ kNum * lenMax then
    -- Karatsuba branch: extract slices, pad to lenMax, recurse.
    let aSlice : Array UInt64 := a.extract loA (loA + lenA)
    let bSlice : Array UInt64 := b.extract loB (loB + lenB)
    let aPadded : Array UInt64 := aSlice ++ Array.replicate (lenMax - lenA) 0
    let bPadded : Array UInt64 := bSlice ++ Array.replicate (lenMax - lenB) 0
    have hA' : 0 + lenMax ≤ aPadded.size := by
      show 0 + lenMax ≤ (aSlice ++ Array.replicate (lenMax - lenA) (0 : UInt64)).size
      rw [Array.size_append, Array.size_replicate]
      have hSlice : aSlice.size = lenA := by
        show (a.extract loA (loA + lenA)).size = lenA
        rw [Array.size_extract]; omega
      have hMax : lenA ≤ lenMax := Nat.le_max_left _ _
      omega
    have hB' : 0 + lenMax ≤ bPadded.size := by
      show 0 + lenMax ≤ (bSlice ++ Array.replicate (lenMax - lenB) (0 : UInt64)).size
      rw [Array.size_append, Array.size_replicate]
      have hSlice : bSlice.size = lenB := by
        show (b.extract loB (loB + lenB)).size = lenB
        rw [Array.size_extract]; omega
      have hMax : lenB ≤ lenMax := Nat.le_max_right _ _
      omega
    karatsubaMulLimbs minThreshold aPadded bPadded 0 0 lenMax hA' hB'
  else
    schoolbookMulLimbs a b loA lenA loB lenB hA hB

/-- Limb-level multiplication using the default `(mulDispatchThreshold,
    mulDispatchKNum / mulDispatchKDen)` parameters. -/
def mulLimbs (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) : Array UInt64 :=
  mulLimbsParam mulDispatchThreshold mulDispatchKNum mulDispatchKDen
    a b loA lenA loB lenB hA hB

/-- AzNat wrapper for `mulLimbsParam`; lets the tuner sweep the dispatch
    parameters. -/
def mulDispatchParam (minThreshold kNum kDen : Nat) (a b : AzNat) : AzNat :=
  ofLimbs (mulLimbsParam minThreshold kNum kDen
    a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Multiplication of two `AzNat`s.  Dispatches between schoolbook and
    Karatsuba via `mulLimbs`. -/
def mul (a b : AzNat) : AzNat :=
  ofLimbs (mulLimbs a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))

instance : Mul AzNat := ⟨mul⟩

-- ── Always-one-algorithm wrappers (for benchmarking) ────────────────────────

/-- Multiplication of `AzNat`s forced to use schoolbook.  For benchmarking;
    callers should use `*` (or `mul`) for the dispatched best-of-both. -/
def mulSchoolbook (a b : AzNat) : AzNat :=
  ofLimbs (schoolbookMulLimbs a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Multiplication of `AzNat`s forced to use Karatsuba.  Pads the shorter
    operand with high zero limbs.  For benchmarking; callers should use `*`
    (or `mul`) for the dispatched best-of-both. -/
def mulKaratsuba (threshold : Nat) (a b : AzNat) : AzNat :=
  if a.limbs.size = 0 ∨ b.limbs.size = 0 then 0
  else
    let n := max a.limbs.size b.limbs.size
    let aPadded : Array UInt64 := a.limbs ++ Array.replicate (n - a.limbs.size) 0
    let bPadded : Array UInt64 := b.limbs ++ Array.replicate (n - b.limbs.size) 0
    have hA : 0 + n ≤ aPadded.size := by
      show 0 + n ≤ (a.limbs ++ Array.replicate (n - a.limbs.size) (0 : UInt64)).size
      rw [Array.size_append, Array.size_replicate]
      have h := Nat.le_max_left a.limbs.size b.limbs.size
      omega
    have hB : 0 + n ≤ bPadded.size := by
      show 0 + n ≤ (b.limbs ++ Array.replicate (n - b.limbs.size) (0 : UInt64)).size
      rw [Array.size_append, Array.size_replicate]
      have h := Nat.le_max_right a.limbs.size b.limbs.size
      omega
    ofLimbs (karatsubaMulLimbs threshold aPadded bPadded 0 0 n hA hB)

end Azurite.AzNat
