import Azurite.AzNat.Div.Schoolbook
import Azurite.AzNat.Div.Recursive

namespace Azurite.AzNat

/-- Divide `U` by `V`, returning `(quotient, remainder)`. By convention,
    `divMod U 0 = (0, U)`. Dispatches to the smallest specialized primitive
    based on the divisor's limb count: a 1-limb divisor uses `divModUInt64`
    (which normalizes internally); a 2-limb divisor normalizes via
    `leadingZeros` and dispatches to `divModLimb2`; an `n`-limb divisor with
    `n ≥ 3` normalizes and dispatches to `recursiveDivModLimbsArr`. The remainder
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
  else if U < V then (0, U)
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
      -- n ≥ 3: dispatch to recursiveDivModLimbsArr (D&C).
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
        recursiveDivModLimbsArr 32 UBuf VBuf 0 0 n m h_n_pos h_loA h_loB h_VBuf_norm
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
  else if U < V then 0
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
        recursiveDivModLimbsArr 32 UBuf VBuf 0 0 n m h_n_pos h_loA h_loB h_VBuf_norm
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
  else if U < V then U
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
        recursiveDivModLimbsArr 32 UBuf VBuf 0 0 n m h_n_pos h_loA h_loB h_VBuf_norm
      let remLimbs := res.1.extract 0 n
      let remNorm := ofLimbs remLimbs
      remNorm >>> k

instance : Div AzNat := ⟨div⟩
instance : Mod AzNat := ⟨mod⟩

/-- AzNat-level wrapper for the slice-style `recursiveDivModLimbs`.
    Normalizes V by shifting left by `leadingZeros` of its top limb,
    builds a working buffer for U, calls `recursiveDivModLimbsArr`, and
    extracts Q (top `m+1` limbs) and R (bottom `n` limbs, right-shifted
    by the normalization).

    Trivial cases (V = 0, single-limb V, U < V, V ≤ 2 limbs) are
    delegated to the existing `divMod` (since the D&C win doesn't apply
    at those sizes anyway). -/
def recursiveDivModFast (threshold : Nat) (U V : AzNat) : AzNat × AzNat :=
  if h0V : V.limbs.size = 0 then (0, U)
  else if hVsmall : V.limbs.size ≤ 2 then divMod U V
  else if hUV : U.limbs.size < V.limbs.size then (0, U)
  else
    -- V has ≥ 3 limbs, U.size ≥ V.size.  Normalize V, build buffer for U.
    let n := V.limbs.size
    let nU := U.limbs.size
    have h_n_ge_3 : 3 ≤ n := by omega
    have h_nU_ge_n : n ≤ nU := Nat.le_of_not_lt hUV
    have h_top_lt : n - 1 < V.limbs.size := by omega
    have h_n2_lt : n - 2 < V.limbs.size := by omega
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
    -- Call the slice-style D&C divrem.
    let res :=
      recursiveDivModLimbsArr threshold UBuf VBuf 0 0 n m h_n_pos h_loA h_loB h_VBuf_norm
    -- Extract Q (low m limbs + 1 returned top limb) and R (low n limbs).
    let quotLimbs := res.1.extract n (n + m) ++ #[res.2]
    let quot := ofLimbs quotLimbs
    let remLimbs := res.1.extract 0 n
    let remNorm := ofLimbs remLimbs
    (quot, remNorm >>> k)

end Azurite.AzNat

section Examples

open Azurite Azurite.AzNat

#guard recursiveDivModFast 32 (AzNat.ofNat 100) (AzNat.ofNat 7)
  = divMod (AzNat.ofNat 100) (AzNat.ofNat 7)

#guard recursiveDivModFast 2 (AzNat.ofNat (2 ^ 640 + 12345)) (AzNat.ofNat (2 ^ 320 + 1))
  = divMod (AzNat.ofNat (2 ^ 640 + 12345)) (AzNat.ofNat (2 ^ 320 + 1))

#guard recursiveDivModFast 2 (AzNat.ofNat (2 ^ 1280 + 999)) (AzNat.ofNat (2 ^ 640 + 17))
  = divMod (AzNat.ofNat (2 ^ 1280 + 999)) (AzNat.ofNat (2 ^ 640 + 17))

#guard recursiveDivModFast 2 (AzNat.ofNat (2 ^ 2048 - 1)) (AzNat.ofNat (2 ^ 512 + 7))
  = divMod (AzNat.ofNat (2 ^ 2048 - 1)) (AzNat.ofNat (2 ^ 512 + 7))

end Examples
