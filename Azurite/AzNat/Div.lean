import Azurite.AzNat.Add
import Azurite.AzNat.Basic
import Azurite.AzNat.Compare
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Sub
import Azurite.UInt64.AddWithCarry
import Azurite.UInt64.Div2By1
import Azurite.UInt64.Div3By2
import Azurite.UInt64.DivMod
import Azurite.UInt64.Equiv.LeadingZeros
import Azurite.UInt64.LeadingZeros
import Azurite.UInt64.MulWithCarry
import Azurite.UInt64.Reciprocal
import Azurite.UInt64.Reciprocal3By2
import Azurite.UInt64.SubWithBorrow

namespace Azurite.AzNat

/-!
Formalization of Algorithm 7 (DIV_NBY1) from
"Improved division by invariant integers" by Niels Möller and Torbjörn Granlund,
extended to handle any nonzero divisor via on-the-fly normalization.
-/

/-- Inner loop of `divModLimb`: from `j = hi - lo` down to `0`, process limb
    `a[lo + j - 1]` by calling `div2By1` with the running remainder as the high
    half. The shift count `k ≤ 63` normalizes the divisor on the fly: the
    effective limb fed into `div2By1` is
    `(a[lo + j - 1] <<< k) ||| (a[lo + j - 2] >>> (64 - k))`. The quotient limb
    overwrites `a[lo + j - 1]` in place. -/
def divModLimb.go (d' inv : UInt64) (k : Nat) (hk : k ≤ 63) (a : Array UInt64)
    (lo j : Nat) (r : UInt64) (hbnd : lo + j ≤ a.size) : Array UInt64 × UInt64 :=
  match j with
  | 0 => (a, r)
  | j + 1 =>
    have h_idx : lo + j < a.size := by omega
    let u_j := a[lo + j]
    let u_carry : UInt64 :=
      if k = 0 then 0
      else if hj0 : j = 0 then 0
      else
        have hjp : lo + j - 1 < a.size := by omega
        a[lo + j - 1]'hjp >>> UInt64.ofNat (64 - k)
    let u_j_shifted := (u_j <<< UInt64.ofNat k) ||| u_carry
    let qr := UInt64.div2By1 r u_j_shifted d' inv
    divModLimb.go d' inv k hk (a.set (lo + j) qr.1) lo j qr.2
      (by rw [Array.size_set]; omega)
  termination_by j

/-- Multi-limb division of the slice `a[lo:hi)` by a nonzero `UInt64` divisor
    `d`, in place. Implements Algorithm 7 (DIV_NBY1) of Möller–Granlund,
    extended to arbitrary nonzero divisors via on-the-fly normalization: shift
    `d` left by `k = leadingZeros d` to put it in `[2^63, 2^64)`, apply Alg. 7
    to the (virtually) shifted dividend, then shift the resulting remainder
    right by `k`. The slice limbs are overwritten with the quotient limbs;
    returns the modified array and the 64-bit remainder. -/
def divModLimb (a : Array UInt64) (lo hi : Nat) (d : UInt64) (hd : d ≠ 0)
    (_hlo : lo ≤ hi) (hhi : hi ≤ a.size) : Array UInt64 × UInt64 :=
  let k := UInt64.leadingZeros d
  let kU : UInt64 := UInt64.ofNat k
  let d' := d <<< kU
  have hk_le : k ≤ 63 := UInt64.leadingZeros_le d hd
  have hd'_norm : 2 ^ 63 ≤ d'.toNat :=
    UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros d hd
  let inv := UInt64.reciprocal d' hd'_norm
  let len := hi - lo
  let r0 : UInt64 :=
    if k = 0 then 0
    else if hlen0 : len = 0 then 0
    else
      have h_top : hi - 1 < a.size := by omega
      a[hi - 1]'h_top >>> UInt64.ofNat (64 - k)
  let res := divModLimb.go d' inv k hk_le a lo len r0 (by omega)
  (res.1, res.2 >>> kU)

/-- Inner loop of `divModLimb2`: from `j = hi - lo` down to `0`, process limb
    `a[lo + j - 1]` by calling `div3By2` with the running 128-bit remainder
    `(r1, r0)` as the high two halves of the 192-bit dividend
    `(r1, r0, a[lo + j - 1])`. The quotient limb overwrites `a[lo + j - 1]` in
    place; the new running remainder is the 128-bit value returned by
    `div3By2`. -/
def divModLimb2.go (d1 d0 v : UInt64) (a : Array UInt64) (lo j : Nat)
    (r1 r0 : UInt64) (hbnd : lo + j ≤ a.size) :
    Array UInt64 × UInt64 × UInt64 :=
  match j with
  | 0 => (a, r1, r0)
  | j + 1 =>
    have h_idx : lo + j < a.size := by omega
    let u_j := a[lo + j]
    let qr := UInt64.div3By2 r1 r0 u_j d1 d0 v
    divModLimb2.go d1 d0 v (a.set (lo + j) qr.1) lo j qr.2.1 qr.2.2
      (by rw [Array.size_set]; omega)
  termination_by j

/-- Multi-limb division of the slice `a[lo:hi)` by a normalized 2-limb divisor
    `(d1, d0)` with `2^63 ≤ d1.toNat`, in place. Iterates Algorithm 5
    (DIV3BY2) of Möller–Granlund top-to-bottom: starting from a zero
    128-bit running remainder, each step calls `div3By2` on the running
    remainder concatenated with the next limb to produce a new quotient limb
    (overwriting the slice) and a new 128-bit remainder. Returns the modified
    array and the final 128-bit remainder `(r1, r0)`. -/
def divModLimb2 (a : Array UInt64) (lo hi : Nat) (d1 d0 : UInt64)
    (hd1 : 2 ^ 63 ≤ d1.toNat) (_hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    Array UInt64 × UInt64 × UInt64 :=
  let v := UInt64.reciprocal3By2 d1 d0 hd1
  let len := hi - lo
  divModLimb2.go d1 d0 v a lo len 0 0 (by omega)

/-- Divide an `AzNat` `U` by a nonzero `UInt64` divisor `d`, returning the
    quotient `AzNat` and remainder `UInt64`. Single-limb dividends short-circuit
    to `UInt64.divMod`; multi-limb dividends use `divModLimb`. -/
def divModUInt64 (U : AzNat) (d : UInt64) (hd : d ≠ 0) : AzNat × UInt64 :=
  if h0 : U.limbs.size = 0 then (0, 0)
  else if h1 : U.limbs.size = 1 then
    have h_pos : 0 < U.limbs.size := by rw [h1]; decide
    let qr := UInt64.divMod (U.limbs[0]'h_pos) d
    (ofLimbs #[qr.1], qr.2)
  else
    let res := divModLimb U.limbs 0 U.limbs.size d hd
      (Nat.zero_le _) (Nat.le_refl _)
    (ofLimbs res.1, res.2)

/-!
Formalization of Algorithm 1.6 (BasecaseDivRem) from
"Modern Computer Arithmetic" by Brent and Zimmermann.
Divides an `(n + m)`-limb dividend `A` by a normalized `n`-limb divisor `B`
in place, producing an `n`-limb remainder (overwriting the low part of `A`),
`m` quotient limbs (overwriting the high part of `A`), and a separate
top quotient limb `q_m`.
-/

/-- Inner loop of `subMulLimbs`: from position `loA + k`, subtracts
    `b[loB + k] * q` from `a[loA + k]` while threading a multiplication carry
    (high half of the most recent product) and a single-bit subtraction borrow.
    Returns the modified array, the final mul carry, and the final sub borrow. -/
def subMulLimbs.go (b : Array UInt64) (loB n : Nat) (q : UInt64)
    (a : Array UInt64) (loA k : Nat) (mulCarry : UInt64) (subBorrow : Bool)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    Array UInt64 × UInt64 × Bool :=
  if h : k < n then
    have hAi : loA + k < a.size := by omega
    have hBi : loB + k < b.size := by omega
    let mc := UInt64.mulWithCarry b[loB + k] q mulCarry
    let swb := UInt64.subWithBorrow a[loA + k] mc.2 subBorrow
    subMulLimbs.go b loB n q (a.set (loA + k) swb.1) loA (k + 1) mc.1 swb.2
      (by rw [Array.size_set]; exact hA) hB
  else
    (a, mulCarry, subBorrow)
  termination_by n - k

/-- Size preservation of `subMulLimbs.go`. -/
theorem subMulLimbs.go_size (b : Array UInt64) (loB n : Nat) (q : UInt64)
    (a : Array UInt64) (loA k : Nat) (mulCarry : UInt64) (subBorrow : Bool)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    (subMulLimbs.go b loB n q a loA k mulCarry subBorrow hA hB).1.size = a.size := by
  induction h_sub : n - k generalizing a k mulCarry subBorrow with
  | zero =>
    have h_ge : n ≤ k := by omega
    rw [subMulLimbs.go]; simp [Nat.not_lt.mpr h_ge]
  | succ p ih =>
    have h_lt : k < n := by omega
    rw [subMulLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ _ (by omega), Array.size_set]

/-- Subtract `q * b[loB : loB + n]` from `a[loA : loA + n + 1]` in place. The
    final mul carry and sub borrow are absorbed into the high limb at position
    `loA + n`. Returns the modified array and a final borrow-out (true means
    the multi-precision result went negative). -/
def subMulLimbs (a b : Array UInt64) (loA loB n : Nat) (q : UInt64)
    (hA : loA + n + 1 ≤ a.size) (hB : loB + n ≤ b.size) :
    Array UInt64 × Bool :=
  let r := subMulLimbs.go b loB n q a loA 0 0 false (by omega) hB
  have h_size_eq : r.1.size = a.size :=
    subMulLimbs.go_size b loB n q a loA 0 0 false (by omega) hB
  have h_top_idx : loA + n < r.1.size := by rw [h_size_eq]; omega
  let topVal := r.1[loA + n]'h_top_idx
  let swb := UInt64.subWithBorrow topVal r.2.1 r.2.2
  (r.1.set (loA + n) swb.1, swb.2)

/-- Size preservation of `subMulLimbs`. -/
theorem subMulLimbs_size (a b : Array UInt64) (loA loB n : Nat) (q : UInt64)
    (hA : loA + n + 1 ≤ a.size) (hB : loB + n ≤ b.size) :
    (subMulLimbs a b loA loB n q hA hB).1.size = a.size := by
  unfold subMulLimbs
  simp only [Array.size_set]
  exact subMulLimbs.go_size _ _ _ _ _ _ _ _ _ _ _

/-- Addback fixup loop for `schoolbookDivModLimbs`. If a pending borrow indicates
    that the trial subtraction overshot, adds `b[loB : loB + n]` back into
    `a[loA : loA + n]` and decrements `q`. Iterates at most `fuel` times; for
    a normalized divisor with the standard quotient-selection cap, two
    iterations suffice. -/
def schoolbookDivModLimbs.addback (a b : Array UInt64) (loA loB n : Nat) (q : UInt64)
    (borrow : Bool) (fuel : Nat) (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    Array UInt64 × UInt64 :=
  match fuel with
  | 0 => (a, q)
  | fuel' + 1 =>
    if borrow then
      let r := addSameLengthLimbs a b loA loB n hA hB
      schoolbookDivModLimbs.addback r.1 b loA loB n (q - 1) (!r.2) fuel'
        (by rw [addSameLengthLimbs_size]; exact hA) hB
    else
      (a, q)

/-- Size preservation of `schoolbookDivModLimbs.addback`. -/
theorem schoolbookDivModLimbs.addback_size (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (borrow : Bool) (fuel : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    (schoolbookDivModLimbs.addback a b loA loB n q borrow fuel hA hB).1.size = a.size := by
  induction fuel generalizing a q borrow with
  | zero => rw [schoolbookDivModLimbs.addback]
  | succ fuel' ih =>
    rw [schoolbookDivModLimbs.addback]
    by_cases hb : borrow
    · simp only [hb, ↓reduceIte]
      rw [ih _ _ _]
      exact addSameLengthLimbs_size _ _ _ _ _ _ _
    · simp [hb]

/-- Inner loop of `schoolbookDivModLimbs`: processes the digits `j+1, j, ..., 1`
    (i.e., remaining iteration count `j+1`) of the quotient from high to low.
    At each step, picks a trial digit via `div2By1` (capped at `β - 1`), runs
    `subMulLimbs`, performs the addback fixup, and stores the corrected digit
    at position `loA + n + j_curr` (which has just been zeroed by the fixup). -/
def schoolbookDivModLimbs.go (a b : Array UInt64) (loA loB n j : Nat)
    (bn1 : UInt64) (inv : UInt64)
    (hA : loA + n + j ≤ a.size) (hB : loB + n ≤ b.size) (h_n_pos : 0 < n) :
    Array UInt64 :=
  match j with
  | 0 => a  -- Step 2: for-loop terminates.
  | j + 1 =>
    have h_a_top : loA + n + j < a.size := by omega
    have h_a_next : loA + (n - 1) + j < a.size := by omega
    let aj_top := a[loA + n + j]'h_a_top
    let aj_next := a[loA + (n - 1) + j]'h_a_next
    -- Steps 3 + 4: quotient selection capped at β - 1.
    let q_init : UInt64 :=
      if bn1 ≤ aj_top then
        (0 : UInt64) - 1
      else
        (UInt64.div2By1 aj_top aj_next bn1 inv).1
    -- Step 5: A := A - q_j * β^j * B.
    have hSub : (loA + j) + n + 1 ≤ a.size := by omega
    let r := subMulLimbs a b (loA + j) loB n q_init hSub hB
    have h_r_size : r.1.size = a.size := subMulLimbs_size _ _ _ _ _ _ _ _
    have h_addback : (loA + j) + n ≤ r.1.size := by rw [h_r_size]; omega
    -- Steps 6 + 7 + 8: while A < 0, decrement q_j and add β^j * B back
    -- (at most twice, hence fuel = 2).
    let fixup := schoolbookDivModLimbs.addback r.1 b (loA + j) loB n q_init r.2 2 h_addback hB
    have h_fixup_size : fixup.1.size = a.size := by
      rw [show fixup.1.size = r.1.size from
            schoolbookDivModLimbs.addback_size _ _ _ _ _ _ _ _ _ _, h_r_size]
    have h_store_idx : loA + n + j < fixup.1.size := by
      rw [h_fixup_size]; omega
    -- Store q_j at the now-zero top of the affected slice.
    let a' := fixup.1.set (loA + n + j) fixup.2
    schoolbookDivModLimbs.go a' b loA loB n j bn1 inv
      (by rw [Array.size_set, h_fixup_size]; omega) hB h_n_pos
  termination_by j

/-- Size preservation of `schoolbookDivModLimbs.go`. -/
theorem schoolbookDivModLimbs.go_size (a b : Array UInt64) (loA loB n j : Nat)
    (bn1 inv : UInt64)
    (hA : loA + n + j ≤ a.size) (hB : loB + n ≤ b.size) (h_n_pos : 0 < n) :
    (schoolbookDivModLimbs.go a b loA loB n j bn1 inv hA hB h_n_pos).size = a.size := by
  induction j generalizing a with
  | zero => rw [schoolbookDivModLimbs.go]
  | succ j ih =>
    rw [schoolbookDivModLimbs.go]
    rw [ih, Array.size_set, schoolbookDivModLimbs.addback_size, subMulLimbs_size]

/-- Multi-limb division of an `(n + m)`-limb dividend `a[loA : loA + n + m]`
    by a normalized `n`-limb divisor `b[loB : loB + n]` (with the high limb of
    `b` in `[2^63, 2^64)`), in place. Implements Algorithm 1.6 (BasecaseDivRem)
    of Brent and Zimmermann.

    On return, the slice `a[loA : loA + n + m]` is overwritten so that
    `a[loA : loA + n]` holds the `n`-limb remainder and
    `a[loA + n : loA + n + m]` holds the low `m` limbs of the quotient. The
    top quotient limb `q_m ∈ {0, 1}` is returned as the second component. -/
def schoolbookDivModLimbs (a b : Array UInt64) (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat) :
    Array UInt64 × UInt64 :=
  have h_bn1_idx : loB + n - 1 < b.size := by omega
  let bn1 := b[loB + n - 1]'h_bn1_idx
  let inv := UInt64.reciprocal bn1 hbn1
  -- Step 1: compare A's top n limbs (at offset loA + m) with B; if ≥, set
  -- q_m := 1 and subtract β^m * B from A. Else q_m := 0.
  have h_top_slice : loA + m + n ≤ a.size := by omega
  let cmp := compareLimbs a b (loA + m) loB n h_top_slice hB
  if cmp = Ordering.lt then
    let a' := schoolbookDivModLimbs.go a b loA loB n m bn1 inv (by omega) hB h_n_pos
    (a', 0)
  else
    let r := subSameLengthLimbs a b (loA + m) loB n h_top_slice hB
    have h_r_size : r.1.size = a.size := subSameLengthLimbs_size _ _ _ _ _ _ _
    let a' := schoolbookDivModLimbs.go r.1 b loA loB n m bn1 inv
                (by rw [h_r_size]; omega) hB h_n_pos
    (a', 1)

/-- Divide `U` by `V`, returning `(quotient, remainder)`. By convention,
    `divMod U 0 = (0, U)`. Dispatches to the smallest specialized primitive
    based on the divisor's limb count: a 1-limb divisor uses `divModUInt64`
    (which normalizes internally); a 2-limb divisor normalizes via
    `leadingZeros` and dispatches to `divModLimb2`; an `n`-limb divisor with
    `n ≥ 3` normalizes and dispatches to `schoolbookDivModLimbs`. The remainder
    is right-shifted by the normalization shift to recover the unscaled value. -/
def divMod (U V : AzNat) : AzNat × AzNat :=
  if h0V : V.limbs.size = 0 then (0, U)
  else if h1V : V.limbs.size = 1 then
    have hV0 : 0 < V.limbs.size := by omega
    let v := V.limbs[0]'hV0
    have hv : v ≠ 0 := by
      intro hv0
      apply V.last_ne_zero
      rw [Array.back?_eq_getElem?]
      rw [show V.limbs.size - 1 = 0 from by omega]
      rw [Array.getElem?_eq_getElem hV0]
      exact congrArg some hv0
    let qr := divModUInt64 U v hv
    (qr.1, ofLimbs #[qr.2])
  else if hUV : U.limbs.size < V.limbs.size then (0, U)
  else
    -- V.limbs.size ≥ 2 ; U.limbs.size ≥ V.limbs.size
    let n := V.limbs.size
    let nU := U.limbs.size
    have h_n_ge_2 : 2 ≤ n := by omega
    have h_nU_ge_n : n ≤ nU := Nat.le_of_not_lt hUV
    have h_top_lt : n - 1 < V.limbs.size := by omega
    have h_n2_lt : n - 2 < V.limbs.size := by omega
    have h_lo_lt : 0 < V.limbs.size := by omega
    let topB := V.limbs[n - 1]'h_top_lt
    have h_topB_ne : topB ≠ 0 := by
      intro h
      apply V.last_ne_zero
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem h_top_lt]
      exact congrArg some h
    let k := UInt64.leadingZeros topB
    have hk_le : k ≤ 63 := UInt64.leadingZeros_le topB h_topB_ne
    let kU : UInt64 := UInt64.ofNat k
    let carryToTop : UInt64 :=
      if hk0 : k = 0 then 0
      else V.limbs[n - 2]'h_n2_lt >>> UInt64.ofNat (64 - k)
    let d_top : UInt64 := (topB <<< kU) ||| carryToTop
    have h_d_top_ge : 2 ^ 63 ≤ d_top.toNat := by
      have h_shl_ge : 2 ^ 63 ≤ (topB <<< kU).toNat :=
        UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros topB h_topB_ne
      show 2 ^ 63 ≤ ((topB <<< kU) ||| carryToTop).toNat
      rw [UInt64.toNat_or]
      exact Nat.le_trans h_shl_ge Nat.left_le_or
    -- Build dividend buffer of size nU + 1 (extra zero limb absorbs the shift carry).
    let UBufRaw : Array UInt64 := U.limbs ++ #[0]
    have h_UBufRaw_size : UBufRaw.size = nU + 1 := by
      show (U.limbs ++ #[0]).size = nU + 1
      rw [Array.size_append]; rfl
    let UBuf : Array UInt64 :=
      if hk0 : k = 0 then UBufRaw
      else
        have hk_lb : 1 ≤ k := by omega
        (shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
          (by rw [h_UBufRaw_size]) hk_lb hk_le).1
    have h_UBuf_size : UBuf.size = nU + 1 := by
      show (if hk0 : k = 0 then UBufRaw else _).size = nU + 1
      split_ifs with hk0
      · exact h_UBufRaw_size
      · rw [shiftLimbsLeft_size]; exact h_UBufRaw_size
    if _h2V : n = 2 then
      -- 2-limb divisor: dispatch to divModLimb2.
      let d0 : UInt64 := V.limbs[0]'h_lo_lt <<< kU
      have hd1 : 2 ^ 63 ≤ d_top.toNat := h_d_top_ge
      let res := divModLimb2 UBuf 0 (nU + 1) d_top d0 hd1
        (Nat.zero_le _) (by rw [h_UBuf_size])
      let quot := ofLimbs res.1
      let remNorm := ofLimbs #[res.2.2, res.2.1]
      (quot, remNorm >>> k)
    else
      -- n ≥ 3: dispatch to schoolbookDivModLimbs.
      have h_n_ge_3 : 3 ≤ n := by omega
      -- Build VBuf of size n with low limbs shifted and top limb manually normalized.
      let VBufRaw : Array UInt64 :=
        if hk0 : k = 0 then V.limbs
        else
          have hk_lb : 1 ≤ k := by omega
          (shiftLimbsLeft V.limbs 0 (n - 1) k (by omega) (by omega) hk_lb hk_le).1
      have h_VBufRaw_size : VBufRaw.size = n := by
        show (if hk0 : k = 0 then V.limbs else _).size = n
        split_ifs with hk0
        · rfl
        · rw [shiftLimbsLeft_size]
      have h_top_in_raw : n - 1 < VBufRaw.size := by rw [h_VBufRaw_size]; omega
      let VBuf : Array UInt64 := VBufRaw.set (n - 1) d_top h_top_in_raw
      have h_VBuf_size : VBuf.size = n := by
        show (VBufRaw.set _ _ _).size = n
        rw [Array.size_set]; exact h_VBufRaw_size
      let m := nU + 1 - n
      have h_n_pos : 0 < n := by omega
      have h_loA : 0 + n + m ≤ UBuf.size := by
        show 0 + n + (nU + 1 - n) ≤ UBuf.size
        rw [h_UBuf_size]; omega
      have h_loB : 0 + n ≤ VBuf.size := by rw [h_VBuf_size]; omega
      have h_VBuf_norm :
          2 ^ 63 ≤ (VBuf[0 + n - 1]'(by rw [h_VBuf_size]; omega)).toNat := by
        have h_eq : VBuf[0 + n - 1]'(by rw [h_VBuf_size]; omega) = d_top := by
          show (VBufRaw.set (n - 1) d_top h_top_in_raw)[0 + n - 1] = d_top
          rw [Array.getElem_set]
          rw [if_pos (show (n - 1 : Nat) = 0 + n - 1 from by omega)]
        rw [h_eq]; exact h_d_top_ge
      let res :=
        schoolbookDivModLimbs UBuf VBuf 0 0 n m h_n_pos h_loA h_loB h_VBuf_norm
      let quotLimbs := res.1.extract n (n + m) ++ #[res.2]
      let quot := ofLimbs quotLimbs
      let remLimbs := res.1.extract 0 n
      let remNorm := ofLimbs remLimbs
      (quot, remNorm >>> k)

/-- Division of two `AzNat`s.  Specialised: mirrors `divMod`'s structure
    but skips remainder post-processing (extract + `ofLimbs` normalisation
    + the `>>> k` denormalisation shift).  For multi-limb divisors with
    balanced or mod-N-style sizes the savings are O(n) where `n` is the
    divisor size — `divMod.1` would otherwise produce the remainder only
    to discard it.  Proven equal to `(divMod U V).1` in
    `Equiv/Div/DivMod.lean`. -/
def div (U V : AzNat) : AzNat :=
  if h0V : V.limbs.size = 0 then 0
  else if h1V : V.limbs.size = 1 then
    have hV0 : 0 < V.limbs.size := by omega
    let v := V.limbs[0]'hV0
    have hv : v ≠ 0 := by
      intro hv0
      apply V.last_ne_zero
      rw [Array.back?_eq_getElem?]
      rw [show V.limbs.size - 1 = 0 from by omega]
      rw [Array.getElem?_eq_getElem hV0]
      exact congrArg some hv0
    (divModUInt64 U v hv).1
  else if hUV : U.limbs.size < V.limbs.size then 0
  else
    let n := V.limbs.size
    let nU := U.limbs.size
    have h_n_ge_2 : 2 ≤ n := by omega
    have h_nU_ge_n : n ≤ nU := Nat.le_of_not_lt hUV
    have h_top_lt : n - 1 < V.limbs.size := by omega
    have h_n2_lt : n - 2 < V.limbs.size := by omega
    have h_lo_lt : 0 < V.limbs.size := by omega
    let topB := V.limbs[n - 1]'h_top_lt
    have h_topB_ne : topB ≠ 0 := by
      intro h
      apply V.last_ne_zero
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem h_top_lt]
      exact congrArg some h
    let k := UInt64.leadingZeros topB
    have hk_le : k ≤ 63 := UInt64.leadingZeros_le topB h_topB_ne
    let kU : UInt64 := UInt64.ofNat k
    let carryToTop : UInt64 :=
      if hk0 : k = 0 then 0
      else V.limbs[n - 2]'h_n2_lt >>> UInt64.ofNat (64 - k)
    let d_top : UInt64 := (topB <<< kU) ||| carryToTop
    have h_d_top_ge : 2 ^ 63 ≤ d_top.toNat := by
      have h_shl_ge : 2 ^ 63 ≤ (topB <<< kU).toNat :=
        UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros topB h_topB_ne
      show 2 ^ 63 ≤ ((topB <<< kU) ||| carryToTop).toNat
      rw [UInt64.toNat_or]
      exact Nat.le_trans h_shl_ge Nat.left_le_or
    let UBufRaw : Array UInt64 := U.limbs ++ #[0]
    have h_UBufRaw_size : UBufRaw.size = nU + 1 := by
      show (U.limbs ++ #[0]).size = nU + 1
      rw [Array.size_append]; rfl
    let UBuf : Array UInt64 :=
      if hk0 : k = 0 then UBufRaw
      else
        have hk_lb : 1 ≤ k := by omega
        (shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
          (by rw [h_UBufRaw_size]) hk_lb hk_le).1
    have h_UBuf_size : UBuf.size = nU + 1 := by
      show (if hk0 : k = 0 then UBufRaw else _).size = nU + 1
      split_ifs with hk0
      · exact h_UBufRaw_size
      · rw [shiftLimbsLeft_size]; exact h_UBufRaw_size
    if _h2V : n = 2 then
      let d0 : UInt64 := V.limbs[0]'h_lo_lt <<< kU
      have hd1 : 2 ^ 63 ≤ d_top.toNat := h_d_top_ge
      let res := divModLimb2 UBuf 0 (nU + 1) d_top d0 hd1
        (Nat.zero_le _) (by rw [h_UBuf_size])
      ofLimbs res.1
    else
      have h_n_ge_3 : 3 ≤ n := by omega
      let VBufRaw : Array UInt64 :=
        if hk0 : k = 0 then V.limbs
        else
          have hk_lb : 1 ≤ k := by omega
          (shiftLimbsLeft V.limbs 0 (n - 1) k (by omega) (by omega) hk_lb hk_le).1
      have h_VBufRaw_size : VBufRaw.size = n := by
        show (if hk0 : k = 0 then V.limbs else _).size = n
        split_ifs with hk0
        · rfl
        · rw [shiftLimbsLeft_size]
      have h_top_in_raw : n - 1 < VBufRaw.size := by rw [h_VBufRaw_size]; omega
      let VBuf : Array UInt64 := VBufRaw.set (n - 1) d_top h_top_in_raw
      have h_VBuf_size : VBuf.size = n := by
        show (VBufRaw.set _ _ _).size = n
        rw [Array.size_set]; exact h_VBufRaw_size
      let m := nU + 1 - n
      have h_n_pos : 0 < n := by omega
      have h_loA : 0 + n + m ≤ UBuf.size := by
        show 0 + n + (nU + 1 - n) ≤ UBuf.size
        rw [h_UBuf_size]; omega
      have h_loB : 0 + n ≤ VBuf.size := by rw [h_VBuf_size]; omega
      have h_VBuf_norm :
          2 ^ 63 ≤ (VBuf[0 + n - 1]'(by rw [h_VBuf_size]; omega)).toNat := by
        have h_eq : VBuf[0 + n - 1]'(by rw [h_VBuf_size]; omega) = d_top := by
          show (VBufRaw.set (n - 1) d_top h_top_in_raw)[0 + n - 1] = d_top
          rw [Array.getElem_set]
          rw [if_pos (show (n - 1 : Nat) = 0 + n - 1 from by omega)]
        rw [h_eq]; exact h_d_top_ge
      let res :=
        schoolbookDivModLimbs UBuf VBuf 0 0 n m h_n_pos h_loA h_loB h_VBuf_norm
      let quotLimbs := res.1.extract n (n + m) ++ #[res.2]
      ofLimbs quotLimbs

/-- Modulus of two `AzNat`s.  Specialised: mirrors `divMod`'s structure but
    skips quotient assembly.  The 1-limb branch skips the `ofLimbs #[qr.1]`
    quotient wrap; the n = 2 branch skips `ofLimbs res.1`; the n ≥ 3 branch
    skips the `extract n (n + m) ++ #[res.2]` and `ofLimbs` quotient
    assembly.  Proven equal to `(divMod U V).2` in `Equiv/Div/DivMod.lean`. -/
def mod (U V : AzNat) : AzNat :=
  if h0V : V.limbs.size = 0 then U
  else if h1V : V.limbs.size = 1 then
    have hV0 : 0 < V.limbs.size := by omega
    let v := V.limbs[0]'hV0
    have hv : v ≠ 0 := by
      intro hv0
      apply V.last_ne_zero
      rw [Array.back?_eq_getElem?]
      rw [show V.limbs.size - 1 = 0 from by omega]
      rw [Array.getElem?_eq_getElem hV0]
      exact congrArg some hv0
    ofLimbs #[(divModUInt64 U v hv).2]
  else if hUV : U.limbs.size < V.limbs.size then U
  else
    let n := V.limbs.size
    let nU := U.limbs.size
    have h_n_ge_2 : 2 ≤ n := by omega
    have h_nU_ge_n : n ≤ nU := Nat.le_of_not_lt hUV
    have h_top_lt : n - 1 < V.limbs.size := by omega
    have h_n2_lt : n - 2 < V.limbs.size := by omega
    have h_lo_lt : 0 < V.limbs.size := by omega
    let topB := V.limbs[n - 1]'h_top_lt
    have h_topB_ne : topB ≠ 0 := by
      intro h
      apply V.last_ne_zero
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem h_top_lt]
      exact congrArg some h
    let k := UInt64.leadingZeros topB
    have hk_le : k ≤ 63 := UInt64.leadingZeros_le topB h_topB_ne
    let kU : UInt64 := UInt64.ofNat k
    let carryToTop : UInt64 :=
      if hk0 : k = 0 then 0
      else V.limbs[n - 2]'h_n2_lt >>> UInt64.ofNat (64 - k)
    let d_top : UInt64 := (topB <<< kU) ||| carryToTop
    have h_d_top_ge : 2 ^ 63 ≤ d_top.toNat := by
      have h_shl_ge : 2 ^ 63 ≤ (topB <<< kU).toNat :=
        UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros topB h_topB_ne
      show 2 ^ 63 ≤ ((topB <<< kU) ||| carryToTop).toNat
      rw [UInt64.toNat_or]
      exact Nat.le_trans h_shl_ge Nat.left_le_or
    let UBufRaw : Array UInt64 := U.limbs ++ #[0]
    have h_UBufRaw_size : UBufRaw.size = nU + 1 := by
      show (U.limbs ++ #[0]).size = nU + 1
      rw [Array.size_append]; rfl
    let UBuf : Array UInt64 :=
      if hk0 : k = 0 then UBufRaw
      else
        have hk_lb : 1 ≤ k := by omega
        (shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
          (by rw [h_UBufRaw_size]) hk_lb hk_le).1
    have h_UBuf_size : UBuf.size = nU + 1 := by
      show (if hk0 : k = 0 then UBufRaw else _).size = nU + 1
      split_ifs with hk0
      · exact h_UBufRaw_size
      · rw [shiftLimbsLeft_size]; exact h_UBufRaw_size
    if _h2V : n = 2 then
      let d0 : UInt64 := V.limbs[0]'h_lo_lt <<< kU
      have hd1 : 2 ^ 63 ≤ d_top.toNat := h_d_top_ge
      let res := divModLimb2 UBuf 0 (nU + 1) d_top d0 hd1
        (Nat.zero_le _) (by rw [h_UBuf_size])
      let remNorm := ofLimbs #[res.2.2, res.2.1]
      remNorm >>> k
    else
      have h_n_ge_3 : 3 ≤ n := by omega
      let VBufRaw : Array UInt64 :=
        if hk0 : k = 0 then V.limbs
        else
          have hk_lb : 1 ≤ k := by omega
          (shiftLimbsLeft V.limbs 0 (n - 1) k (by omega) (by omega) hk_lb hk_le).1
      have h_VBufRaw_size : VBufRaw.size = n := by
        show (if hk0 : k = 0 then V.limbs else _).size = n
        split_ifs with hk0
        · rfl
        · rw [shiftLimbsLeft_size]
      have h_top_in_raw : n - 1 < VBufRaw.size := by rw [h_VBufRaw_size]; omega
      let VBuf : Array UInt64 := VBufRaw.set (n - 1) d_top h_top_in_raw
      have h_VBuf_size : VBuf.size = n := by
        show (VBufRaw.set _ _ _).size = n
        rw [Array.size_set]; exact h_VBufRaw_size
      let m := nU + 1 - n
      have h_n_pos : 0 < n := by omega
      have h_loA : 0 + n + m ≤ UBuf.size := by
        show 0 + n + (nU + 1 - n) ≤ UBuf.size
        rw [h_UBuf_size]; omega
      have h_loB : 0 + n ≤ VBuf.size := by rw [h_VBuf_size]; omega
      have h_VBuf_norm :
          2 ^ 63 ≤ (VBuf[0 + n - 1]'(by rw [h_VBuf_size]; omega)).toNat := by
        have h_eq : VBuf[0 + n - 1]'(by rw [h_VBuf_size]; omega) = d_top := by
          show (VBufRaw.set (n - 1) d_top h_top_in_raw)[0 + n - 1] = d_top
          rw [Array.getElem_set]
          rw [if_pos (show (n - 1 : Nat) = 0 + n - 1 from by omega)]
        rw [h_eq]; exact h_d_top_ge
      let res :=
        schoolbookDivModLimbs UBuf VBuf 0 0 n m h_n_pos h_loA h_loB h_VBuf_norm
      let remLimbs := res.1.extract 0 n
      let remNorm := ofLimbs remLimbs
      remNorm >>> k

instance : Div AzNat := ⟨div⟩
instance : Mod AzNat := ⟨mod⟩

end Azurite.AzNat
