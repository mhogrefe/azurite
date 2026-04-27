import Azurite.AzNat.Add
import Azurite.AzNat.Sub
import Azurite.AzNat.Mul

namespace Azurite.AzNat

-- ── absSubLimbsKM stages ────────────────────────────────────────────────────

namespace absSubLimbsKM

/-- Stage 1: copy `a[loA..loA+k]` into a fresh `k`-limb buffer.
    Implemented by adding `a`'s slice into a zero buffer.

    OPTIMIZATION (TODO): two improvements possible without changing semantics:
    1. Replace `addSameLengthLimbs` with `Array.extract`/plain copy — we are
       paying `addWithCarry` overhead per limb to copy a value that never
       overflows (input carry is always 0).
    2. Fuse `copy` + `subPart` into a single pass: the low `m` limbs of the
       buffer are immediately overwritten by `subPart`, so copying them here
       is wasted work.  Only the high `k − m` limbs strictly need to come
       from `a`.  This requires a new "subtract two `a`-slices into a fresh
       buffer" primitive.  Impact on overall Karatsuba runtime is small
       (the `2k × 2k` recursive multiplications dominate), but worth noting. -/
def copy (a : Array UInt64) (loA k : Nat) (hA : loA + k ≤ a.size) :
    { c : Array UInt64 // c.size = k } :=
  let buf₀ : Array UInt64 := Array.replicate k 0
  have hbuf₀_sz : buf₀.size = k := Array.size_replicate
  have hbuf₀ : 0 + k ≤ buf₀.size := by rw [hbuf₀_sz]; omega
  let r := addSameLengthLimbs buf₀ a 0 loA k hbuf₀ hA
  ⟨r.1, by
    show (addSameLengthLimbs buf₀ a 0 loA k hbuf₀ hA).1.size = k
    rw [addSameLengthLimbs_size, hbuf₀_sz]⟩

/-- Stage 2: subtract `a[loA+k..loA+k+m]` from a length-`k` buffer.
    Returns `(diff, borrow)`: `borrow = true` ⇔ original buffer < subtrahend. -/
def subPart (a cpy : Array UInt64) (loA k m : Nat)
    (hCpy : cpy.size = k) (ha : loA + k + m ≤ a.size)
    (h_le : m ≤ k) (h_kpos : 0 < k) (h_mpos : 0 < m) :
    { d : Array UInt64 // d.size = k } × Bool :=
  have hcpy_size' : 0 + k ≤ cpy.size := by rw [hCpy]; omega
  have ha1 : (loA + k) + m ≤ a.size := by omega
  let r := subGeqLimbs cpy a 0 k (loA + k) m hcpy_size' ha1 h_le h_kpos h_mpos
  (⟨r.1, by
    show (subGeqLimbs cpy a 0 k (loA + k) m hcpy_size' ha1 h_le h_kpos h_mpos).1.size = k
    rw [subGeqLimbs_size, hCpy]⟩, r.2)

/-- Stage 3: negate a length-`k` buffer (compute `β^k − toNat d`). -/
def negPart (d : Array UInt64) (k : Nat) (hd : d.size = k) :
    { n : Array UInt64 // n.size = k } :=
  let zero : Array UInt64 := Array.replicate k 0
  have hzero_sz : zero.size = k := Array.size_replicate
  have hzero : 0 + k ≤ zero.size := by rw [hzero_sz]; omega
  have hd' : 0 + k ≤ d.size := by rw [hd]; omega
  let r := subSameLengthLimbs zero d 0 0 k hzero hd'
  ⟨r.1, by
    show (subSameLengthLimbs zero d 0 0 k hzero hd').1.size = k
    rw [subSameLengthLimbs_size, hzero_sz]⟩

end absSubLimbsKM

/--
Compute `|A₀ − A₁|` where `A₀ = a[loA : loA + k]` and `A₁ = a[loA + k : loA + k + m]`
with `m ≤ k`. The result is a fresh `k`-limb array along with a sign bit:
`true` iff `A₀ ≥ A₁`.
-/
def absSubLimbsKM (a : Array UInt64) (loA k m : Nat)
    (hA : loA + k + m ≤ a.size) (h_le : m ≤ k) (h_kpos : 0 < k) (h_mpos : 0 < m) :
    { d : Array UInt64 // d.size = k } × Bool :=
  let cpy := absSubLimbsKM.copy a loA k (by omega)
  let sub := absSubLimbsKM.subPart a cpy.1 loA k m cpy.2 hA h_le h_kpos h_mpos
  if sub.2 then
    (absSubLimbsKM.negPart sub.1.1 k sub.1.2, false)
  else
    (sub.1, true)

-- ── karatsubaMulLimbsRec stages ─────────────────────────────────────────────

namespace karatsubaMulLimbsRec

/-- Combine `C₀`, `C₁`, `C₂` into the middle term `C₀ + C₁ ± C₂` in a
    `(2k+1)`-limb buffer.  When `sameSign = true` we subtract `C₂`, otherwise
    we add `C₂`. -/
def middleBuf (k m : Nat) (C₀ C₁ C₂ : Array UInt64) (sameSign : Bool)
    (hC₀ : C₀.size = 2 * k) (hC₁ : C₁.size = 2 * m) (hC₂ : C₂.size = 2 * k)
    (h_kpos : 0 < k) (h_mpos : 0 < m) (h_le : m ≤ k) :
    { mid : Array UInt64 // mid.size = 2 * k + 1 } :=
  let mid₀ : Array UInt64 := Array.replicate (2 * k + 1) 0
  have hmid₀_sz : mid₀.size = 2 * k + 1 := Array.size_replicate
  have h_2k_pos : 0 < 2 * k := by omega
  have h_2k1_pos : 0 < 2 * k + 1 := by omega
  have h_2k_le_2k1 : 2 * k ≤ 2 * k + 1 := by omega
  have h_2m_pos : 0 < 2 * m := by omega
  have h_2m_le_2k1 : 2 * m ≤ 2 * k + 1 := by omega
  have h_addC0_dst : 0 + (2 * k + 1) ≤ mid₀.size := by rw [hmid₀_sz]; omega
  have h_addC0_src : 0 + 2 * k ≤ C₀.size := by rw [hC₀]; omega
  let mid₁ := addGeqLimbs mid₀ C₀ 0 (2 * k + 1) 0 (2 * k)
                h_addC0_dst h_addC0_src h_2k_le_2k1 h_2k1_pos h_2k_pos
  have hmid₁_sz : mid₁.1.size = 2 * k + 1 := by
    show (addGeqLimbs mid₀ C₀ 0 (2 * k + 1) 0 (2 * k)
            h_addC0_dst h_addC0_src h_2k_le_2k1 h_2k1_pos h_2k_pos).1.size = 2 * k + 1
    rw [addGeqLimbs_size, hmid₀_sz]
  have h_addC1_dst : 0 + (2 * k + 1) ≤ mid₁.1.size := by rw [hmid₁_sz]; omega
  have h_addC1_src : 0 + 2 * m ≤ C₁.size := by rw [hC₁]; omega
  let mid₂ := addGeqLimbs mid₁.1 C₁ 0 (2 * k + 1) 0 (2 * m)
                h_addC1_dst h_addC1_src h_2m_le_2k1 h_2k1_pos h_2m_pos
  have hmid₂_sz : mid₂.1.size = 2 * k + 1 := by
    show (addGeqLimbs mid₁.1 C₁ 0 (2 * k + 1) 0 (2 * m)
            h_addC1_dst h_addC1_src h_2m_le_2k1 h_2k1_pos h_2m_pos).1.size = 2 * k + 1
    rw [addGeqLimbs_size, hmid₁_sz]
  have h_C2_dst : 0 + (2 * k + 1) ≤ mid₂.1.size := by rw [hmid₂_sz]; omega
  have h_C2_src : 0 + 2 * k ≤ C₂.size := by rw [hC₂]; omega
  if sameSign then
    ⟨(subGeqLimbs mid₂.1 C₂ 0 (2 * k + 1) 0 (2 * k)
        h_C2_dst h_C2_src h_2k_le_2k1 h_2k1_pos h_2k_pos).1,
      by rw [subGeqLimbs_size, hmid₂_sz]⟩
  else
    ⟨(addGeqLimbs mid₂.1 C₂ 0 (2 * k + 1) 0 (2 * k)
        h_C2_dst h_C2_src h_2k_le_2k1 h_2k1_pos h_2k_pos).1,
      by rw [addGeqLimbs_size, hmid₂_sz]⟩

/-- Assemble the final result: append `C₀ ++ C₁` and add `middle · β^k`.
    The high limbs of `middle` past `min(2k+1, 2*len − k)` are mathematically
    zero (provable from `middle = A₀B₁ + A₁B₀ < 2β^(k+m)`); the truncation is
    safe in `assemble_toNat`. -/
def assemble (k m len : Nat) (C₀ C₁ middle : Array UInt64)
    (hC₀ : C₀.size = 2 * k) (hC₁ : C₁.size = 2 * m) (hMid : middle.size = 2 * k + 1)
    (hkm : k + m = len) (h_kpos : 0 < k) (h_mpos : 0 < m) (_h_le : m ≤ k) :
    { c : Array UInt64 // c.size = 2 * len } :=
  let acc₀ := C₀ ++ C₁
  have hacc₀_sz : acc₀.size = 2 * len := by
    show (C₀ ++ C₁).size = 2 * len
    rw [Array.size_append, hC₀, hC₁]; omega
  have hlen : 2 ≤ len := by omega
  let addLen := min (2 * k + 1) (2 * len - k)
  have h_addLen_le_lenA : addLen ≤ 2 * len - k := by
    show min (2 * k + 1) (2 * len - k) ≤ 2 * len - k; omega
  have _h_addLen_le_mid : addLen ≤ 2 * k + 1 := by
    show min (2 * k + 1) (2 * len - k) ≤ 2 * k + 1; omega
  have h_lenA_pos : 0 < 2 * len - k := by omega
  have h_addLen_pos : 0 < addLen := by
    show 0 < min (2 * k + 1) (2 * len - k); omega
  have h_acc_dst : k + (2 * len - k) ≤ acc₀.size := by rw [hacc₀_sz]; omega
  have h_mid_src : 0 + addLen ≤ middle.size := by rw [hMid]; omega
  let acc := addGeqLimbs acc₀ middle k (2 * len - k) 0 addLen
               h_acc_dst h_mid_src h_addLen_le_lenA h_lenA_pos h_addLen_pos
  ⟨acc.1, by
    show (addGeqLimbs acc₀ middle k (2 * len - k) 0 addLen
            h_acc_dst h_mid_src h_addLen_le_lenA h_lenA_pos h_addLen_pos).1.size = 2 * len
    rw [addGeqLimbs_size, hacc₀_sz]⟩

end karatsubaMulLimbsRec

/--
Karatsuba multiplication of two equal-length limb slices. Returns a fresh
array of size `2 * len`.

The `threshold` parameter is the size below which we fall back to
`schoolbookMulLimbs`. When `len < max 2 threshold`, schoolbook is used
directly (we always need `len ≥ 2` to split).

Algorithm 1.3 (Karatsuba):
  k := ⌈len/2⌉; m := len - k    (so `m ≤ k`)
  C₀ := A₀ · B₀  (k × k → 2k limbs)
  C₁ := A₁ · B₁  (m × m → 2m limbs)
  C₂ := |A₀ − A₁| · |B₀ − B₁|  (k × k → 2k limbs)
  result := C₀ + (C₀ + C₁ − s · C₂) · β^k + C₁ · β^{2k}
where `s = +1` if `sign(A₀−A₁) = sign(B₀−B₁)`, else `s = −1`.
-/
def karatsubaMulLimbsRec (threshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    { c : Array UInt64 // c.size = 2 * len } :=
  if h_base : len < 2 ∨ len < threshold then
    ⟨schoolbookMulLimbs a b loA len loB len hA hB, by
      rw [schoolbookMulLimbs_size]; omega⟩
  else
    have hlen : 2 ≤ len := by omega
    let k := (len + 1) / 2
    let m := len - k
    have hk_pos : 0 < k := by show 0 < (len + 1) / 2; omega
    have hk_lt : k < len := by show (len + 1) / 2 < len; omega
    have hm_pos : 0 < m := by show 0 < len - (len + 1) / 2; omega
    have hm_le : m ≤ k := by show len - (len + 1) / 2 ≤ (len + 1) / 2; omega
    have hm_lt : m < len := by show len - (len + 1) / 2 < len; omega
    have hkm : k + m = len := by
      show (len + 1) / 2 + (len - (len + 1) / 2) = len; omega
    have hA0 : loA + k ≤ a.size := by omega
    have hB0 : loB + k ≤ b.size := by omega
    let C0 := karatsubaMulLimbsRec threshold a b loA loB k hA0 hB0
    have hA1 : (loA + k) + m ≤ a.size := by omega
    have hB1 : (loB + k) + m ≤ b.size := by omega
    let C1 := karatsubaMulLimbsRec threshold a b (loA + k) (loB + k) m hA1 hB1
    have hAabs : loA + k + m ≤ a.size := by omega
    have hBabs : loB + k + m ≤ b.size := by omega
    let absA := absSubLimbsKM a loA k m hAabs hm_le hk_pos hm_pos
    let absB := absSubLimbsKM b loB k m hBabs hm_le hk_pos hm_pos
    have hAabs_lim : 0 + k ≤ absA.1.1.size := by rw [absA.1.2]; omega
    have hBabs_lim : 0 + k ≤ absB.1.1.size := by rw [absB.1.2]; omega
    let C2 := karatsubaMulLimbsRec threshold absA.1.1 absB.1.1 0 0 k hAabs_lim hBabs_lim
    let middle := karatsubaMulLimbsRec.middleBuf k m C0.1 C1.1 C2.1
                    (absA.2 == absB.2) C0.2 C1.2 C2.2 hk_pos hm_pos hm_le
    karatsubaMulLimbsRec.assemble k m len C0.1 C1.1 middle.1
      C0.2 C1.2 middle.2 hkm hk_pos hm_pos hm_le
  termination_by len
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-- Karatsuba multiplication of two equal-length limb slices, with the same
    signature shape as `schoolbookMulLimbs` (a single shared `len`).  Falls
    back to `schoolbookMulLimbs` when `len < max 2 threshold`. -/
def karatsubaMulLimbs (threshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) : Array UInt64 :=
  (karatsubaMulLimbsRec threshold a b loA loB len hA hB).1

/-- The result of Karatsuba multiplication has size `2 * len`. -/
theorem karatsubaMulLimbs_size (threshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (karatsubaMulLimbs threshold a b loA loB len hA hB).size = 2 * len :=
  (karatsubaMulLimbsRec threshold a b loA loB len hA hB).2

-- ── Limb-level dispatcher and AzNat wrapper ─────────────────────────────────

/-- Default Karatsuba schoolbook-fallback threshold (in 64-bit limbs).  Tuned
    via `Azurite.AzNat.Tune` on a typical machine; the `az_nat_mul_compare`
    benchmark shows Karatsuba already winning around limb count 25-32 on
    balanced operands. -/
def mulDispatchThreshold : Nat := 32

/-- Multiplication of two limb slices.  Dispatches between `schoolbookMulLimbs`
    and `karatsubaMulLimbs` based on operand size and balance:

    * Both operands ≥ `mulDispatchThreshold` limbs AND the size ratio
      `min/max` is at least 1/2 → Karatsuba (with the shorter slice padded
      to match).
    * Otherwise → schoolbook.

    Putting the dispatch here means every caller (`AzNat.mul`, future
    polynomial-coefficient mul, etc.) automatically benefits from the best
    available algorithm. -/
def mulLimbs (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) : Array UInt64 :=
  let lenMax := max lenA lenB
  let lenMin := min lenA lenB
  if mulDispatchThreshold ≤ lenMin && 2 * lenMin ≥ lenMax then
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
    karatsubaMulLimbs mulDispatchThreshold aPadded bPadded 0 0 lenMax hA' hB'
  else
    schoolbookMulLimbs a b loA lenA loB lenB hA hB

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
