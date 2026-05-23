import Azurite.AzNat.Compare
import Azurite.AzNat.DivBy6
import Azurite.AzNat.Mul.Karatsuba
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight

/-!
# Toom-Cook 3-way multiplication for AzNat

Implements Algorithm 1.4 from Brent–Zimmermann, *Modern Computer Arithmetic*.

For `A, B < β^n` with `β = 2^64`, `k = ⌈n/3⌉`, splits each operand into three
parts and reduces one `n`-limb multiplication to **five** recursive
multiplications of about `n/3` limbs. Asymptotic complexity
`Θ(n^{log_3 5}) ≈ Θ(n^{1.46})`, beating Karatsuba's `n^{1.585}`.

  v_0  := a_0 · b_0                              (k × k)
  v_1  := (a_0 + a_1 + a_2)(b_0 + b_1 + b_2)     ((k+1) × (k+1))
  v_-1 := (a_0 - a_1 + a_2)(b_0 - b_1 + b_2)     ((k+1) × (k+1)), signed
  v_2  := (a_0 + 2 a_1 + 4 a_2)(b_0 + 2 b_1 + 4 b_2) ((k+1) × (k+1))
  v_∞  := a_2 · b_2                              (m × m), m = n - 2k

Interpolation (all divisions are exact):
  t_1 := (3 v_0 + v_2 + 2 v_-1) / 6 - 2 v_∞       (sign-corrected)
  t_2 := (v_1 + v_-1) / 2                          (sign-corrected)
  c_0 := v_0
  c_1 := v_1 - t_1
  c_2 := t_2 - v_0 - v_∞
  c_3 := t_1 - t_2
  c_4 := v_∞

The result `AB = c_0 + c_1 β^k + c_2 β^{2k} + c_3 β^{3k} + c_4 β^{4k}` lives
in `2n` limbs.

All linear-time interpolation steps use `AzNat`-level arithmetic
(limb-level under the hood: `addLimbs`, `subLimbs`, `mulUInt64`,
`shiftLeft`, `shiftRight`, plus the specialized `divBy6`).  No
intermediate value is ever materialized as a `Nat`; the only `Nat`s
that appear are array indices and limb counts.
-/

namespace Azurite.AzNat

-- ── Size-fitting helper ─────────────────────────────────────────────────────

/-- Truncate or zero-pad `a` to exactly `n` limbs.  When `a.toNat < 2^(64·n)`
    (i.e. `a` fits in `n` limbs), this is value-preserving; otherwise the
    high limbs of `a` are silently discarded.  Used at boundaries where a
    fresh exact-size buffer is needed (e.g. the `2·len`-limb result of
    `toomCook3MulLimbsRec`). -/
def truncatePad (a : Array UInt64) (n : Nat) : Array UInt64 :=
  let truncated := a.extract 0 n
  truncated ++ Array.replicate (n - truncated.size) 0

theorem truncatePad_size (a : Array UInt64) (n : Nat) :
    (truncatePad a n).size = n := by
  unfold truncatePad
  rw [Array.size_append, Array.size_replicate, Array.size_extract]
  omega

-- ── Sum / signed-difference helpers for the three-way split ─────────────────

/-- `a_0 + a_1 + a_2` in a fresh `(k + 1)`-limb buffer, where
    `a_0 = a[lo, lo+k)`, `a_1 = a[lo+k, lo+2k)`, `a_2 = a[lo+2k, lo+2k+m)`. -/
def sum012 (a : Array UInt64) (lo k m : Nat) : Array UInt64 :=
  let s0 : AzNat := ofLimbs (a.extract lo (lo + k))
  let s1 : AzNat := ofLimbs (a.extract (lo + k) (lo + k + k))
  let s2 : AzNat := ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))
  truncatePad (s0 + s1 + s2).limbs (k + 1)

/-- `a_0 + 2·a_1 + 4·a_2` in a fresh `(k + 1)`-limb buffer. -/
def sum124 (a : Array UInt64) (lo k m : Nat) : Array UInt64 :=
  let s0 : AzNat := ofLimbs (a.extract lo (lo + k))
  let s1 : AzNat := ofLimbs (a.extract (lo + k) (lo + k + k))
  let s2 : AzNat := ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))
  truncatePad (s0 + mulUInt64 s1 2 + mulUInt64 s2 4).limbs (k + 1)

/-- `|a_0 - a_1 + a_2|` in a fresh `(k + 1)`-limb buffer plus a sign bit
    (`true` when the unsigned value is `≥ 0`). -/
def diffM1 (a : Array UInt64) (lo k m : Nat) : Array UInt64 × Bool :=
  let s0 : AzNat := ofLimbs (a.extract lo (lo + k))
  let s1 : AzNat := ofLimbs (a.extract (lo + k) (lo + k + k))
  let s2 : AzNat := ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))
  let lhs := s0 + s2
  if lhs < s1 then
    (truncatePad (s1 - lhs).limbs (k + 1), false)
  else
    (truncatePad (lhs - s1).limbs (k + 1), true)

theorem diffM1_size (a : Array UInt64) (lo k m : Nat) :
    (diffM1 a lo k m).1.size = k + 1 := by
  unfold diffM1
  by_cases h : ofLimbs (a.extract lo (lo + k)) + ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))
              < ofLimbs (a.extract (lo + k) (lo + k + k))
  · simp only [h, ↓reduceIte]; exact truncatePad_size _ _
  · simp only [h, ↓reduceIte]; exact truncatePad_size _ _

theorem diffM1_size_ge (a : Array UInt64) (lo k m : Nat) :
    0 + (k + 1) ≤ (diffM1 a lo k m).1.size := by
  rw [diffM1_size]; omega

-- ── Interpolation step (non-recursive helper) ───────────────────────────────

/-- The Toom-Cook 3 interpolation step, isolated as a non-recursive helper.
    Given the five sub-products `v_0, v_1, v_2, v_{-1}, v_∞` as `AzNat`s and
    the sign bit `vm1_sign = (sgn(A_0-A_1+A_2) == sgn(B_0-B_1+B_2))`,
    computes the assembled product `c_0 + c_1 β^k + c_2 β^{2k} + c_3 β^{3k}
    + c_4 β^{4k}` (with `β = 2^64`).

    Factored out from `toomCook3MulLimbsRec` so that the correctness proof
    operates on this small standalone function instead of unfolding the
    full recursive body. -/
def toomCook3Interpolate (v0_az v1_az v2_az vm1_az vinf_az : AzNat)
    (vm1_sign : Bool) (k : Nat) : AzNat :=
  -- (3 v_0 + v_2 + 2 v_-1) / 6  with v_-1 signed.
  let three_v0_plus_v2 := mulUInt64 v0_az 3 + v2_az
  let two_vm1 := mulUInt64 vm1_az 2
  let t1_num : AzNat :=
    if vm1_sign then three_v0_plus_v2 + two_vm1
    else three_v0_plus_v2 - two_vm1
  let t1 := (divBy6 t1_num).1 - mulUInt64 vinf_az 2
  -- (v_1 + v_-1) / 2  with v_-1 signed.
  let t2_num : AzNat :=
    if vm1_sign then v1_az + vm1_az
    else v1_az - vm1_az
  let t2 := t2_num >>> 1
  -- Coefficients of the product polynomial.
  let c0 := v0_az
  let c1 := v1_az - t1
  let c2 := t2 - v0_az - vinf_az
  let c3 := t1 - t2
  let c4 := vinf_az
  -- Assemble: AB = c_0 + c_1 β^k + c_2 β^{2k} + c_3 β^{3k} + c_4 β^{4k}.
  let bk : Nat := 64 * k
  c0 + (c1 <<< bk) + (c2 <<< (2 * bk)) + (c3 <<< (3 * bk)) + (c4 <<< (4 * bk))

-- ── Toom-Cook 3-way ─────────────────────────────────────────────────────────

/-- Recursive Toom-Cook 3-way multiplication of two equal-length slices.
    Falls back to `karatsubaMulLimbs` when `len < threshold`. -/
def toomCook3MulLimbsRec (threshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    { c : Array UInt64 // c.size = 2 * len } :=
  if h_base : len < threshold ∨ len < 3 then
    ⟨karatsubaMulLimbs threshold a b loA loB len hA hB, by
      rw [karatsubaMulLimbs_size]⟩
  else
    have hlen : 3 ≤ len := by omega
    let k := (len + 2) / 3
    let m := len - 2 * k
    have hk_pos : 0 < k := by show 0 < (len + 2) / 3; omega
    have hk_lt : k < len := by show (len + 2) / 3 < len; omega
    have hk1_lt : k + 1 < len := by show (len + 2) / 3 + 1 < len; omega
    have h2k_le : 2 * k ≤ len := by show 2 * ((len + 2) / 3) ≤ len; omega
    have hm_le_k : m ≤ k := by show len - 2 * ((len + 2) / 3) ≤ (len + 2) / 3; omega
    have hm_lt : m < len := by show len - 2 * ((len + 2) / 3) < len; omega
    -- Slice bounds for the recursive calls.
    have hA0 : loA + k ≤ a.size := by omega
    have hB0 : loB + k ≤ b.size := by omega
    have hA2 : (loA + 2 * k) + m ≤ a.size := by omega
    have hB2 : (loB + 2 * k) + m ≤ b.size := by omega
    -- v_0 = a_0 · b_0
    let v0 := toomCook3MulLimbsRec threshold a b loA loB k hA0 hB0
    -- v_∞ = a_2 · b_2
    let vinf := toomCook3MulLimbsRec threshold a b (loA + 2 * k) (loB + 2 * k) m hA2 hB2
    -- Evaluation sums (k+1 limbs each).
    let s0a := sum012 a loA k m
    let s0b := sum012 b loB k m
    let s2a := sum124 a loA k m
    let s2b := sum124 b loB k m
    let da := diffM1 a loA k m
    let db := diffM1 b loB k m
    -- Each helper returns an exactly `(k + 1)`-limb buffer.
    have hs0a : 0 + (k + 1) ≤ s0a.size := by
      show 0 + (k + 1) ≤ (sum012 a loA k m).size
      unfold sum012; rw [truncatePad_size]; omega
    have hs0b : 0 + (k + 1) ≤ s0b.size := by
      show 0 + (k + 1) ≤ (sum012 b loB k m).size
      unfold sum012; rw [truncatePad_size]; omega
    have hs2a : 0 + (k + 1) ≤ s2a.size := by
      show 0 + (k + 1) ≤ (sum124 a loA k m).size
      unfold sum124; rw [truncatePad_size]; omega
    have hs2b : 0 + (k + 1) ≤ s2b.size := by
      show 0 + (k + 1) ≤ (sum124 b loB k m).size
      unfold sum124; rw [truncatePad_size]; omega
    have hda : 0 + (k + 1) ≤ da.1.size := diffM1_size_ge _ _ _ _
    have hdb : 0 + (k + 1) ≤ db.1.size := diffM1_size_ge _ _ _ _
    -- v_1, v_2, v_-1 (each (k+1) × (k+1) → 2(k+1) limbs).
    let v1 := toomCook3MulLimbsRec threshold s0a s0b 0 0 (k + 1) hs0a hs0b
    let v2 := toomCook3MulLimbsRec threshold s2a s2b 0 0 (k + 1) hs2a hs2b
    let vm1 := toomCook3MulLimbsRec threshold da.1 db.1 0 0 (k + 1) hda hdb
    -- Interpolation factored out into a non-recursive helper.
    let result := toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
                    (ofLimbs vm1.1) (ofLimbs vinf.1) (da.2 == db.2) k
    ⟨truncatePad result.limbs (2 * len), truncatePad_size _ _⟩
  termination_by len
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-- Toom-Cook 3-way multiplication, mirroring the signature shape of
    `schoolbookMulLimbs` (a single shared `len`). Falls back to Karatsuba
    when `len < threshold`. -/
def toomCook3MulLimbs (threshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) : Array UInt64 :=
  (toomCook3MulLimbsRec threshold a b loA loB len hA hB).1

theorem toomCook3MulLimbs_size (threshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (toomCook3MulLimbs threshold a b loA loB len hA hB).size = 2 * len :=
  (toomCook3MulLimbsRec threshold a b loA loB len hA hB).2

end Azurite.AzNat
