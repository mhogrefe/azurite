import Azurite.AzNat.Equiv.Div.DivModLimb
import Azurite.AzNat.Equiv.Div.DivModLimb2
import Azurite.AzNat.Equiv.Div.Schoolbook
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.UInt64.Equiv.LeadingZeros

namespace Azurite.AzNat

/-- A nonempty `AzNat` has positive `toNat`: the top limb is nonzero (by
    `last_ne_zero`), so the whole number is at least `2 ^ (64 * (n - 1))`. -/
theorem toNat_pos_of_size_pos (V : AzNat) (h : 0 < V.limbs.size) :
    2 ^ (64 * (V.limbs.size - 1)) ≤ V.toNat := by
  have h_top_idx : V.limbs.size - 1 < V.limbs.size := Nat.sub_lt h Nat.zero_lt_one
  have h_top_ne : V.limbs[V.limbs.size - 1]'h_top_idx ≠ 0 := by
    intro h0
    apply V.last_ne_zero
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem h_top_idx]
    exact congrArg some h0
  have h_top_pos : 0 < (V.limbs[V.limbs.size - 1]'h_top_idx).toNat := by
    by_contra h_le
    have : (V.limbs[V.limbs.size - 1]'h_top_idx).toNat = 0 := by omega
    exact h_top_ne (UInt64.eq_of_toNat_eq this)
  show toNatLimbsList V.limbs.toList ≥ _
  -- Decompose V.limbs.toList as (take (size-1)) ++ [top].
  have h_lt : V.limbs.size - 1 < V.limbs.toList.length := by
    rw [Array.length_toList]; exact h_top_idx
  have h_take_succ_eq : V.limbs.toList.take (V.limbs.size - 1) ++
        [V.limbs.toList[V.limbs.size - 1]'h_lt]
      = V.limbs.toList.take (V.limbs.size - 1 + 1) := by
    rw [List.take_succ_eq_append_getElem]
  have h_take_full : V.limbs.toList.take (V.limbs.size - 1 + 1) = V.limbs.toList := by
    apply List.take_of_length_le
    rw [Array.length_toList]; omega
  have h_arr_eq : V.limbs.toList[V.limbs.size - 1]'h_lt
                    = V.limbs[V.limbs.size - 1]'h_top_idx := Array.getElem_toList _
  have h_decomp : V.limbs.toList
                    = V.limbs.toList.take (V.limbs.size - 1)
                        ++ [V.limbs[V.limbs.size - 1]'h_top_idx] := by
    rw [← h_arr_eq, h_take_succ_eq, h_take_full]
  rw [h_decomp]
  rw [toNatLimbsList_append]
  have h_take_len : (V.limbs.toList.take (V.limbs.size - 1)).length = V.limbs.size - 1 := by
    rw [List.length_take, Array.length_toList]; omega
  rw [h_take_len]
  have h_single : toNatLimbsList [V.limbs[V.limbs.size - 1]'h_top_idx]
                    = (V.limbs[V.limbs.size - 1]'h_top_idx).toNat := by
    show toNatLimbsList ((V.limbs[V.limbs.size - 1]'h_top_idx) :: []) = _
    rw [toNatLimbsList_cons]; simp [toNatLimbsList]
  rw [h_single]
  calc 2 ^ (64 * (V.limbs.size - 1))
      = 1 * 2 ^ (64 * (V.limbs.size - 1)) := by ring
    _ ≤ (V.limbs[V.limbs.size - 1]'h_top_idx).toNat * 2 ^ (64 * (V.limbs.size - 1)) :=
        Nat.mul_le_mul_right _ h_top_pos
    _ ≤ (V.limbs[V.limbs.size - 1]'h_top_idx).toNat * 2 ^ (64 * (V.limbs.size - 1)) +
          toNatLimbsList (V.limbs.toList.take (V.limbs.size - 1)) := Nat.le_add_right _ _

/-- `U.toNat = 0` iff `U.limbs` is empty. -/
theorem toNat_eq_zero_iff (U : AzNat) : U.toNat = 0 ↔ U.limbs.size = 0 := by
  constructor
  · intro h
    by_contra h_ne
    have h_pos : 0 < U.limbs.size := Nat.pos_of_ne_zero h_ne
    have h_lb := toNat_pos_of_size_pos U h_pos
    have h_pow_pos : 0 < (2 : Nat) ^ (64 * (U.limbs.size - 1)) := Nat.two_pow_pos _
    omega
  · intro h
    have h_nil : U.limbs.toList = [] := by
      have : U.limbs.toList.length = 0 := h
      exact List.length_eq_zero_iff.mp this
    show toNatLimbsList U.limbs.toList = 0
    rw [h_nil]; rfl

/-- `U.toNat < 2 ^ (64 * U.limbs.size)`. -/
theorem toNat_lt_pow (U : AzNat) : U.toNat < 2 ^ (64 * U.limbs.size) := by
  show toNatLimbsList U.limbs.toList < _
  have h := toNatLimbsList_lt_pow U.limbs.toList
  have h_len : U.limbs.toList.length = U.limbs.size := rfl
  rw [h_len] at h; exact h

/-- A single limb taken from `V` with `size = 1`: `V.toNat = V.limbs[0].toNat`. -/
theorem toNat_of_size_one (V : AzNat) (h : V.limbs.size = 1) :
    V.toNat = (V.limbs[0]'(by omega)).toNat := by
  show toNatLimbsList V.limbs.toList = _
  have h_len : V.limbs.toList.length = 1 := h
  match hL : V.limbs.toList with
  | [] => rw [hL] at h_len; simp at h_len
  | [x] =>
    rw [show toNatLimbsList [x] = x.toNat from by simp [toNatLimbsList]]
    have h_get : V.limbs[0]'(by omega) = x := by
      have h_eq : V.limbs[0]'(by omega)
          = V.limbs.toList[0]'(by rw [Array.length_toList]; omega) :=
        (Array.getElem_toList (by omega)).symm
      rw [h_eq]
      simp [hL]
    rw [h_get]
  | x :: y :: ys => rw [hL] at h_len; simp at h_len

/-- `toNat` of `ofLimbs #[v]` is `v.toNat`. -/
theorem toNat_ofLimbs_singleton (v : UInt64) : (ofLimbs #[v]).toNat = v.toNat := by
  rw [toNat_ofLimbs]
  show toNatLimbsList [v] = v.toNat
  simp [toNatLimbsList]

/-- `toNat` of `ofLimbs #[lo, hi]` is `hi * 2^64 + lo`. -/
theorem toNat_ofLimbs_pair (lo hi : UInt64) :
    (ofLimbs #[lo, hi]).toNat = hi.toNat * 2 ^ 64 + lo.toNat := by
  rw [toNat_ofLimbs]
  show toNatLimbsList [lo, hi] = _
  rw [show ([lo, hi] : List UInt64) = lo :: [hi] from rfl, toNatLimbsList_cons]
  simp [toNatLimbsList]

/-- For an `AzNat` with exactly two limbs, `toNat` is the obvious 2-limb value. -/
theorem toNat_of_size_two (V : AzNat) (h : V.limbs.size = 2) :
    V.toNat = (V.limbs[1]'(by omega)).toNat * 2 ^ 64 + (V.limbs[0]'(by omega)).toNat := by
  show toNatLimbsList V.limbs.toList = _
  have h_len : V.limbs.toList.length = 2 := h
  match hL : V.limbs.toList with
  | [] => rw [hL] at h_len; simp at h_len
  | [_] => rw [hL] at h_len; simp at h_len
  | [x, y] =>
    have h_get0 : V.limbs[0]'(by omega) = x := by
      have h_eq : V.limbs[0]'(by omega)
          = V.limbs.toList[0]'(by rw [Array.length_toList]; omega) :=
        (Array.getElem_toList (by omega)).symm
      rw [h_eq]; simp [hL]
    have h_get1 : V.limbs[1]'(by omega) = y := by
      have h_eq : V.limbs[1]'(by omega)
          = V.limbs.toList[1]'(by rw [Array.length_toList]; omega) :=
        (Array.getElem_toList (by omega)).symm
      rw [h_eq]; simp [hL]
    rw [h_get0, h_get1]
    show toNatLimbsList [x, y] = _
    rw [show ([x, y] : List UInt64) = x :: [y] from rfl, toNatLimbsList_cons]
    show toNatLimbsList [y] * 2 ^ 64 + x.toNat = y.toNat * 2 ^ 64 + x.toNat
    rw [show toNatLimbsList [y] = y.toNat from by simp [toNatLimbsList]]
  | _ :: _ :: _ :: _ => rw [hL] at h_len; simp at h_len

/-- For a divisor of size ≥ 1, `V.toNat` strictly exceeds anything with fewer limbs. -/
theorem toNat_lt_of_size_lt (U V : AzNat) (h : U.limbs.size < V.limbs.size) :
    U.toNat < V.toNat := by
  have hV_pos : 0 < V.limbs.size := by omega
  have h_U_lt : U.toNat < 2 ^ (64 * U.limbs.size) := toNat_lt_pow U
  have h_V_lb : 2 ^ (64 * (V.limbs.size - 1)) ≤ V.toNat :=
    toNat_pos_of_size_pos V hV_pos
  have h_pow_le : 2 ^ (64 * U.limbs.size) ≤ 2 ^ (64 * (V.limbs.size - 1)) := by
    apply Nat.pow_le_pow_right (by decide)
    omega
  omega

/-- The dividend buffer (with extra zero limb) has `toNat = U.toNat`. -/
private theorem toNatLimbsList_UBufRaw (U : AzNat) :
    toNatLimbsList ((U.limbs ++ #[(0 : UInt64)]).toList) = U.toNat := by
  rw [Array.toList_append]
  show toNatLimbsList (U.limbs.toList ++ [(0 : UInt64)]) = _
  rw [toNatLimbsList_append]
  show toNatLimbsList [(0 : UInt64)] * _ + _ = _
  have h_zero : toNatLimbsList [(0 : UInt64)] = 0 := by simp [toNatLimbsList]
  rw [h_zero, Nat.zero_mul, Nat.zero_add]
  rfl

/-- Shifting a `(nU + 1)`-limb buffer holding `U.toNat` left by `k ≤ 63` bits
    keeps the value within the buffer (the carry bit is zero), so the shifted
    buffer represents `U.toNat * 2 ^ k`. -/
private theorem toNatLimbsList_shifted_UBufRaw (U : AzNat) (k : Nat)
    (hk_lb : 1 ≤ k) (hk_ub : k ≤ 63) :
    let UBufRaw : Array UInt64 := U.limbs ++ #[(0 : UInt64)]
    have h_size : UBufRaw.size = U.limbs.size + 1 := by
      show (U.limbs ++ #[(0 : UInt64)]).size = U.limbs.size + 1
      rw [Array.size_append]; rfl
    toNatLimbsList
        (shiftLimbsLeft UBufRaw 0 (U.limbs.size + 1) k (Nat.zero_le _)
          (by rw [h_size]) hk_lb hk_ub).1.toList
      = U.toNat * 2 ^ k := by
  intro UBufRaw h_size
  set nU := U.limbs.size with hnU_def
  set shifted := (shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
                    (by rw [h_size]) hk_lb hk_ub).1 with hshifted_def
  set carryOut := (shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
                    (by rw [h_size]) hk_lb hk_ub).2 with hcarry_def
  have h_shifted_size : shifted.size = nU + 1 := by
    rw [hshifted_def, shiftLimbsLeft_size]; exact h_size
  have h_shifted_len : shifted.toList.length = nU + 1 := by
    rw [Array.length_toList, h_shifted_size]
  have h_raw_len : UBufRaw.toList.length = nU + 1 := by
    rw [Array.length_toList, h_size]
  -- shiftLimbsLeft_toNat gives the slice + carry identity.
  have h_inv := shiftLimbsLeft_toNat UBufRaw 0 (nU + 1) k (Nat.zero_le _)
                  (by rw [h_size]) hk_lb hk_ub
  simp only at h_inv
  rw [← hshifted_def, ← hcarry_def] at h_inv
  -- Slices reduce to full lists.
  have h_drop_shifted : shifted.toList.drop 0 = shifted.toList := List.drop_zero
  have h_drop_raw : UBufRaw.toList.drop 0 = UBufRaw.toList := List.drop_zero
  have h_take_shifted : shifted.toList.take (nU + 1 - 0) = shifted.toList := by
    apply List.take_of_length_le
    rw [h_shifted_len]; omega
  have h_take_raw : UBufRaw.toList.take (nU + 1 - 0) = UBufRaw.toList := by
    apply List.take_of_length_le
    rw [h_raw_len]; omega
  rw [h_drop_shifted, h_take_shifted, h_drop_raw, h_take_raw] at h_inv
  -- Show carryOut = 0 by bounding shifted's toNat and U.toNat * 2^k.
  rw [show 64 * (nU + 1 - 0) = 64 * (nU + 1) from by omega] at h_inv
  rw [toNatLimbsList_UBufRaw] at h_inv
  have h_shifted_lt : toNatLimbsList shifted.toList < 2 ^ (64 * (nU + 1)) := by
    have h := toNatLimbsList_lt_pow shifted.toList
    rw [h_shifted_len] at h; exact h
  have h_U_lt : U.toNat < 2 ^ (64 * nU) := toNat_lt_pow U
  have h_U_2k_lt : U.toNat * 2 ^ k < 2 ^ (64 * (nU + 1)) := by
    have h_pow_split : (2 : Nat) ^ (64 * (nU + 1)) = 2 ^ (64 * nU) * 2 ^ 64 := by
      rw [show 64 * (nU + 1) = 64 * nU + 64 from by ring, Nat.pow_add]
    rw [h_pow_split]
    calc U.toNat * 2 ^ k
        < 2 ^ (64 * nU) * 2 ^ k :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h_U_lt
      _ ≤ 2 ^ (64 * nU) * 2 ^ 64 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  have h_carry_zero : carryOut.toNat = 0 := by
    by_contra h_ne
    have h_carry_pos : 0 < carryOut.toNat := Nat.pos_of_ne_zero h_ne
    have h_pow_pos : 0 < (2 : Nat) ^ (64 * (nU + 1)) := Nat.two_pow_pos _
    have h_carry_term : 2 ^ (64 * (nU + 1)) ≤ carryOut.toNat * 2 ^ (64 * (nU + 1)) := by
      calc 2 ^ (64 * (nU + 1))
          = 1 * 2 ^ (64 * (nU + 1)) := by ring
        _ ≤ carryOut.toNat * 2 ^ (64 * (nU + 1)) := Nat.mul_le_mul_right _ h_carry_pos
    omega
  have h_carry_zero' : carryOut.toNat * 2 ^ (64 * (nU + 1)) = 0 := by
    rw [h_carry_zero]; ring
  rw [h_carry_zero'] at h_inv
  omega

/-- For a normalized top limb (`leadingZeros = k`), shifting by `k` bits
    fits within `2 ^ 64` and equals plain multiplication. -/
private theorem topB_shl_lt (topB : UInt64) (k : Nat) (hk_eq : k = topB.leadingZeros)
    (h_topB_ne : topB ≠ 0) :
    (topB <<< UInt64.ofNat k).toNat = topB.toNat * 2 ^ k
    ∧ topB.toNat * 2 ^ k < 2 ^ 64 := by
  have hd_nat_ne : topB.toNat ≠ 0 := fun h =>
    h_topB_ne (UInt64.eq_of_toNat_eq (h.trans rfl))
  have hd_lt : topB.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hL_lt_64 : topB.toNat.log2 < 64 := (Nat.log2_lt hd_nat_ne).mpr hd_lt
  have hL_le_63 : topB.toNat.log2 ≤ 63 := by omega
  set L := topB.toNat.log2
  have hk_def : k = 63 - L := by
    rw [hk_eq]
    show topB.leadingZeros = 63 - L
    show (if topB = 0 then 64 else 63 - topB.toNat.log2) = 63 - L
    rw [if_neg h_topB_ne]
  have hk_le : k ≤ 63 := by rw [hk_def]; exact Nat.sub_le _ _
  have hLk : L + k = 63 := by rw [hk_def]; omega
  have hpow_hi : topB.toNat < 2 ^ (L + 1) :=
    (Nat.log2_lt hd_nat_ne).mp (Nat.lt_succ_of_le (Nat.le_refl _))
  have h_ofNat_k : (UInt64.ofNat k).toNat = k := by
    show k % 2 ^ 64 = k; exact Nat.mod_eq_of_lt (by omega)
  have h_k_mod : k % 64 = k := Nat.mod_eq_of_lt (by omega)
  have h_prod_lt : topB.toNat * 2 ^ k < 2 ^ 64 := by
    calc topB.toNat * 2 ^ k
        < 2 ^ (L + 1) * 2 ^ k :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hpow_hi
      _ = 2 ^ (L + 1 + k) := (Nat.pow_add 2 (L + 1) k).symm
      _ = 2 ^ 64 := by congr 1; omega
  refine ⟨?_, h_prod_lt⟩
  rw [UInt64.toNat_shiftLeft, h_ofNat_k, h_k_mod, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt h_prod_lt]

/-- Combine the divModLimb2 result with the de-normalization (`>>> k`) to
    produce the divMod correctness identity, given the three normalization
    facts: `UBuf` represents `U * 2^k`, `(d_top, d0)` represents `V * 2^k`,
    and `d_top` is normalized. -/
private theorem divMod_size2_finish (U V : AzNat)
    (k : Nat) (_hk_le : k ≤ 63)
    (UBuf : Array UInt64) (d_top d0 : UInt64)
    (h_UBuf_size : UBuf.size = U.limbs.size + 1)
    (h_dtop_norm : 2 ^ 63 ≤ d_top.toNat)
    (h_UBuf_toNat : toNatLimbsList UBuf.toList = U.toNat * 2 ^ k)
    (h_dtop_d0 : d_top.toNat * 2 ^ 64 + d0.toNat = V.toNat * 2 ^ k)
    (hV_pos : 0 < V.toNat) :
    let res := divModLimb2 UBuf 0 (U.limbs.size + 1) d_top d0 h_dtop_norm
                 (Nat.zero_le _) (by rw [h_UBuf_size])
    (ofLimbs res.1).toNat * V.toNat
        + (ofLimbs #[res.2.2, res.2.1] >>> k).toNat = U.toNat
    ∧ (V.toNat ≠ 0 → (ofLimbs #[res.2.2, res.2.1] >>> k).toNat < V.toNat) := by
  intro res
  have h_div := divModLimb2_toNat UBuf 0 (U.limbs.size + 1) d_top d0 h_dtop_norm
                  (Nat.zero_le _) (by rw [h_UBuf_size])
  simp only at h_div
  obtain ⟨h_eq, h_lt⟩ := h_div
  -- The slice [0, U.limbs.size + 1) is the whole UBuf.
  have h_UBuf_len : UBuf.toList.length = U.limbs.size + 1 := by
    rw [Array.length_toList, h_UBuf_size]
  have h_drop_full : UBuf.toList.drop 0 = UBuf.toList := List.drop_zero
  have h_take_full : UBuf.toList.take (U.limbs.size + 1 - 0) = UBuf.toList := by
    apply List.take_of_length_le; rw [h_UBuf_len]; omega
  rw [h_drop_full, h_take_full] at h_eq
  rw [h_UBuf_toNat] at h_eq
  -- The same slice for res.1, but res.1 has the same size as UBuf.
  have h_res1_size : res.1.size = UBuf.size := by
    show (divModLimb2 UBuf 0 (U.limbs.size + 1) d_top d0 h_dtop_norm
            (Nat.zero_le _) (by rw [h_UBuf_size])).1.size = UBuf.size
    unfold divModLimb2
    exact divModLimb2.go_size _ _ _ _ _ _ _ _ _
  have h_res1_len : res.1.toList.length = U.limbs.size + 1 := by
    rw [Array.length_toList, h_res1_size, h_UBuf_size]
  have h_drop_res : res.1.toList.drop 0 = res.1.toList := List.drop_zero
  have h_take_res : res.1.toList.take (U.limbs.size + 1 - 0) = res.1.toList := by
    apply List.take_of_length_le; rw [h_res1_len]; omega
  rw [h_drop_res, h_take_res] at h_eq
  -- Substitute V*2^k for d_top*2^64+d0.
  rw [h_dtop_d0] at h_eq h_lt
  -- res.1.toNat = toNatLimbsList of its toList.
  set quot_nat := toNatLimbsList res.1.toList with hquot_def
  set R_norm := res.2.1.toNat * 2 ^ 64 + res.2.2.toNat with hR_def
  -- Now h_eq : U * 2^k = quot_nat * (V * 2^k) + R_norm
  -- h_lt : R_norm < V * 2^k
  have h_pow_pos : 0 < (2 : Nat) ^ k := Nat.two_pow_pos _
  have hV_2k_pos : 0 < V.toNat * 2 ^ k := Nat.mul_pos hV_pos h_pow_pos
  -- quot_nat ≤ U / V (so quot_nat * V ≤ U)
  have h_quot_V_le_U : quot_nat * V.toNat ≤ U.toNat := by
    have h_le_2k : quot_nat * V.toNat * 2 ^ k ≤ U.toNat * 2 ^ k := by
      have h_assoc : quot_nat * V.toNat * 2 ^ k = quot_nat * (V.toNat * 2 ^ k) := by ring
      rw [h_assoc, h_eq]; omega
    exact Nat.le_of_mul_le_mul_right h_le_2k h_pow_pos
  -- R_norm = (U - quot * V) * 2^k
  have h_R_eq : R_norm = (U.toNat - quot_nat * V.toNat) * 2 ^ k := by
    have h_assoc : quot_nat * (V.toNat * 2 ^ k) = quot_nat * V.toNat * 2 ^ k := by ring
    rw [h_assoc] at h_eq
    have h_sub_eq : (U.toNat - quot_nat * V.toNat) * 2 ^ k
                   = U.toNat * 2 ^ k - quot_nat * V.toNat * 2 ^ k := by
      rw [Nat.sub_mul]
    rw [h_sub_eq, h_eq, Nat.add_sub_cancel_left]
  -- ofLimbs #[res.2.2, res.2.1] gives R_norm.
  have h_remNorm_eq : (ofLimbs #[res.2.2, res.2.1]).toNat = R_norm := by
    rw [hR_def]; exact toNat_ofLimbs_pair _ _
  -- Now apply >>> k.
  have h_shr : (ofLimbs #[res.2.2, res.2.1] >>> k).toNat
              = (ofLimbs #[res.2.2, res.2.1]).toNat / 2 ^ k := by
    rw [hShiftRight_eq, toNat_shiftRight]
  rw [h_shr, h_remNorm_eq, h_R_eq]
  rw [Nat.mul_div_cancel _ h_pow_pos]
  -- Also ofLimbs of res.1 = quot_nat.
  have h_quot_eq : (ofLimbs res.1).toNat = quot_nat := by
    rw [toNat_ofLimbs, hquot_def]
  rw [h_quot_eq]
  refine ⟨?_, ?_⟩
  · -- quot_nat * V + (U - quot_nat * V) = U
    omega
  · intro _
    -- (U - quot_nat * V) < V
    -- Use h_lt : R_norm < V * 2^k, with R_norm = (U - quot_nat*V) * 2^k.
    have h_lt' : (U.toNat - quot_nat * V.toNat) * 2 ^ k < V.toNat * 2 ^ k := by
      rw [← h_R_eq]; exact h_lt
    exact Nat.lt_of_mul_lt_mul_right h_lt'

/-- Combine the schoolbookDivModLimbs result with the de-normalization (`>>> k`)
    to produce the divMod correctness identity, given the normalization facts
    that UBuf represents `U * 2^k`, VBuf represents `V * 2^k`, and VBuf's top
    limb is normalized. -/
private theorem divMod_size_ge3_finish (U V : AzNat)
    (k : Nat) (_hk_le : k ≤ 63)
    (UBuf VBuf : Array UInt64)
    (h_n_ge_3 : 3 ≤ V.limbs.size)
    (h_n_le_nU : V.limbs.size ≤ U.limbs.size)
    (h_UBuf_size : UBuf.size = U.limbs.size + 1)
    (h_VBuf_size : VBuf.size = V.limbs.size)
    (h_VBuf_norm :
      2 ^ 63 ≤ (VBuf[0 + V.limbs.size - 1]'(by rw [h_VBuf_size]; omega)).toNat)
    (h_UBuf_toNat : toNatLimbsList UBuf.toList = U.toNat * 2 ^ k)
    (h_VBuf_toNat : toNatLimbsList VBuf.toList = V.toNat * 2 ^ k)
    (_hV_pos : 0 < V.toNat) :
    let res := schoolbookDivModLimbs UBuf VBuf 0 0 V.limbs.size
                  (U.limbs.size + 1 - V.limbs.size)
                  (by omega) (by rw [h_UBuf_size]; omega)
                  (by rw [h_VBuf_size]; omega) h_VBuf_norm
    (ofLimbs (res.1.extract V.limbs.size
                (V.limbs.size + (U.limbs.size + 1 - V.limbs.size))
              ++ #[res.2])).toNat * V.toNat
        + (ofLimbs (res.1.extract 0 V.limbs.size) >>> k).toNat = U.toNat
    ∧ (V.toNat ≠ 0 →
        (ofLimbs (res.1.extract 0 V.limbs.size) >>> k).toNat < V.toNat) := by
  intro res
  set n := V.limbs.size with hn_def
  set m := U.limbs.size + 1 - n with hm_def
  -- Apply schoolbookDivModLimbs_toNat.
  have h_div := schoolbookDivModLimbs_toNat UBuf VBuf 0 0 n m
                  (by omega) (by rw [h_UBuf_size]; omega)
                  (by rw [h_VBuf_size]; omega) h_VBuf_norm
  simp only [List.drop_zero, Nat.zero_add] at h_div
  obtain ⟨h_R_lt, h_eq, h_qm_le⟩ := h_div
  -- The full UBuf and VBuf lists are exactly the slices.
  have h_UBuf_len : UBuf.toList.length = U.limbs.size + 1 := by
    rw [Array.length_toList, h_UBuf_size]
  have h_VBuf_len : VBuf.toList.length = n := by
    rw [Array.length_toList, h_VBuf_size]
  have h_n_plus_m : n + m = U.limbs.size + 1 := by
    show n + (U.limbs.size + 1 - n) = _; omega
  have h_take_VBuf : VBuf.toList.take n = VBuf.toList := by
    apply List.take_of_length_le; rw [h_VBuf_len]
  have h_take_UBuf : UBuf.toList.take (n + m) = UBuf.toList := by
    apply List.take_of_length_le; rw [h_UBuf_len, h_n_plus_m]
  rw [h_take_VBuf] at h_eq h_R_lt
  rw [h_take_UBuf] at h_eq
  rw [h_UBuf_toNat] at h_eq
  rw [h_VBuf_toNat] at h_eq h_R_lt
  -- Identify res.1's slices.
  have h_res_size : res.1.size = UBuf.size := by
    show (schoolbookDivModLimbs UBuf VBuf 0 0 n m _ _ _ _).1.size = UBuf.size
    unfold schoolbookDivModLimbs
    simp only
    split_ifs
    · rw [schoolbookDivModLimbs.go_size]
    · rw [schoolbookDivModLimbs.go_size, subSameLengthLimbs_size]
  have h_res_len : res.1.toList.length = U.limbs.size + 1 := by
    rw [Array.length_toList, h_res_size, h_UBuf_size]
  -- Set up the slice quantities.
  set R : Nat := toNatLimbsList (res.1.toList.take n) with hR_def
  set Q' : Nat := toNatLimbsList ((res.1.toList.drop n).take m) with hQ'_def
  -- Express ofLimbs slices in terms of toNatLimbsList.
  have h_extract_R :
      (ofLimbs (res.1.extract 0 n)).toNat = R := by
    rw [toNat_ofLimbs, Array.toList_extract, List.extract_eq_take_drop, hR_def]
    show toNatLimbsList ((res.1.toList.drop 0).take (n - 0)) = _
    rw [List.drop_zero, Nat.sub_zero]
  have h_extract_Q' :
      (res.1.extract n (n + m)).toList = (res.1.toList.drop n).take m := by
    rw [Array.toList_extract, List.extract_eq_take_drop]
    show (res.1.toList.drop n).take (n + m - n) = (res.1.toList.drop n).take m
    rw [Nat.add_sub_cancel_left]
  -- Quotient list = Q' ++ [q_m] limb-wise.
  set q_m : UInt64 := res.2 with hqm_def
  have h_quot_eq :
      (ofLimbs (res.1.extract n (n + m) ++ #[q_m])).toNat
        = q_m.toNat * 2 ^ (64 * m) + Q' := by
    rw [toNat_ofLimbs, Array.toList_append, h_extract_Q']
    show toNatLimbsList ((res.1.toList.drop n).take m ++ [q_m]) = _
    rw [toNatLimbsList_append]
    have h_take_len : ((res.1.toList.drop n).take m).length = m := by
      rw [List.length_take, List.length_drop, h_res_len]
      have h_n_le : n ≤ U.limbs.size + 1 := by omega
      omega
    rw [h_take_len, hQ'_def]
    show toNatLimbsList [q_m] * 2 ^ (64 * m) + Q' = q_m.toNat * 2 ^ (64 * m) + Q'
    have : toNatLimbsList [q_m] = q_m.toNat := by simp [toNatLimbsList]
    rw [this]
  -- Now produce the conclusion. (h_eq and h_R_lt already contain R, Q' via `set`.)
  show (ofLimbs (res.1.extract n (n + m) ++ #[res.2])).toNat * V.toNat
        + (ofLimbs (res.1.extract 0 n) >>> k).toNat = U.toNat
        ∧ _
  rw [show res.2 = q_m from rfl, h_quot_eq]
  set Q : Nat := q_m.toNat * 2 ^ (64 * m) + Q' with hQ_def
  have h_R_lt_2k : R < V.toNat * 2 ^ k := h_R_lt
  -- From U * 2^k = Q * (V * 2^k) + R, derive Q * V ≤ U.
  have h_pow_pos : 0 < (2 : Nat) ^ k := Nat.two_pow_pos _
  have h_Q_V_le_U : Q * V.toNat ≤ U.toNat := by
    have h_le_2k : Q * V.toNat * 2 ^ k ≤ U.toNat * 2 ^ k := by
      have h_assoc : Q * V.toNat * 2 ^ k = Q * (V.toNat * 2 ^ k) := by ring
      rw [h_assoc, h_eq]; omega
    exact Nat.le_of_mul_le_mul_right h_le_2k h_pow_pos
  -- Express R as (U - Q*V) * 2^k.
  have h_R_eq : R = (U.toNat - Q * V.toNat) * 2 ^ k := by
    have h_assoc : Q * (V.toNat * 2 ^ k) = Q * V.toNat * 2 ^ k := by ring
    rw [h_assoc] at h_eq
    have h_sub_eq : (U.toNat - Q * V.toNat) * 2 ^ k
                    = U.toNat * 2 ^ k - Q * V.toNat * 2 ^ k := by
      rw [Nat.sub_mul]
    rw [h_sub_eq, h_eq, Nat.add_sub_cancel_left]
  -- ofLimbs (extract 0 n).toNat = R, then >>> k divides by 2^k.
  have h_shr : (ofLimbs (res.1.extract 0 n) >>> k).toNat
                = (ofLimbs (res.1.extract 0 n)).toNat / 2 ^ k := by
    rw [hShiftRight_eq, toNat_shiftRight]
  rw [h_shr, h_extract_R, h_R_eq]
  rw [Nat.mul_div_cancel _ h_pow_pos]
  refine ⟨?_, ?_⟩
  · -- Q * V + (U - Q*V) = U
    omega
  · intro _
    -- (U - Q*V) < V
    have h_lt' : (U.toNat - Q * V.toNat) * 2 ^ k < V.toNat * 2 ^ k := by
      rw [← h_R_eq]; exact h_R_lt_2k
    exact Nat.lt_of_mul_lt_mul_right h_lt'

set_option maxHeartbeats 800000 in
/-- **Top-level correctness of `divMod`**: `divMod U V` returns `(Q, R)` such
    that `Q * V + R = U`, with `R < V` whenever `V > 0`. By convention,
    `divMod U 0 = (0, U)`, so the value identity holds (with vacuous bound). -/
theorem divMod_toNat (U V : AzNat) :
    (divMod U V).1.toNat * V.toNat + (divMod U V).2.toNat = U.toNat
    ∧ (V.toNat ≠ 0 → (divMod U V).2.toNat < V.toNat) := by
  unfold divMod
  -- Case 1: V.limbs.size = 0 (i.e., V = 0).
  by_cases h0V : V.limbs.size = 0
  · simp only [h0V, ↓reduceDIte]
    have h_V_zero : V.toNat = 0 := (toNat_eq_zero_iff V).mpr h0V
    refine ⟨?_, ?_⟩
    · show (0 : AzNat).toNat * V.toNat + U.toNat = U.toNat
      rw [h_V_zero]; show 0 * 0 + U.toNat = U.toNat; ring
    · intro h_ne; exact absurd h_V_zero h_ne
  · simp only [h0V, ↓reduceDIte]
    have hV_pos : 0 < V.limbs.size := Nat.pos_of_ne_zero h0V
    have hV_toNat_pos : 0 < V.toNat := by
      have := toNat_pos_of_size_pos V hV_pos
      have h_pow_pos : 0 < (2 : Nat) ^ (64 * (V.limbs.size - 1)) := Nat.two_pow_pos _
      omega
    -- Case 2: V.limbs.size = 1.
    by_cases h1V : V.limbs.size = 1
    · simp only [h1V, ↓reduceDIte]
      have hV0 : 0 < V.limbs.size := by omega
      set v := V.limbs[0]'hV0 with hv_def
      have hv_ne : v ≠ 0 := by
        intro hv0
        apply V.last_ne_zero
        rw [Array.back?_eq_getElem?]
        rw [show V.limbs.size - 1 = 0 from by omega]
        rw [Array.getElem?_eq_getElem hV0]
        exact congrArg some hv0
      have h_V_eq_v : V.toNat = v.toNat := by
        rw [hv_def]; exact toNat_of_size_one V h1V
      set qr := divModUInt64 U v hv_ne with hqr_def
      have h_div := toNat_divModUInt64 U v hv_ne
      simp only at h_div
      obtain ⟨h_eq, h_lt⟩ := h_div
      refine ⟨?_, ?_⟩
      · show qr.1.toNat * V.toNat + (ofLimbs #[qr.2]).toNat = U.toNat
        rw [toNat_ofLimbs_singleton, h_V_eq_v]; exact h_eq
      · intro _
        show (ofLimbs #[qr.2]).toNat < V.toNat
        rw [toNat_ofLimbs_singleton, h_V_eq_v]; exact h_lt
    · simp only [h1V, ↓reduceDIte]
      -- Case 3: U.limbs.size < V.limbs.size.
      by_cases hUV : U.limbs.size < V.limbs.size
      · simp only [hUV, ↓reduceDIte]
        refine ⟨?_, ?_⟩
        · show (0 : AzNat).toNat * V.toNat + U.toNat = U.toNat
          show 0 * V.toNat + U.toNat = U.toNat; ring
        · intro _; exact toNat_lt_of_size_lt U V hUV
      · simp only [hUV, ↓reduceDIte]
        -- Cases 4 and 5: V.limbs.size ≥ 2 and U.limbs.size ≥ V.limbs.size.
        have h_n_ge_2 : 2 ≤ V.limbs.size := by omega
        have h_nU_ge_n : V.limbs.size ≤ U.limbs.size := Nat.le_of_not_lt hUV
        by_cases h2V : V.limbs.size = 2
        · -- Case 4: V.limbs.size = 2. Dispatches to divModLimb2.
          simp only [h2V, ↓reduceDIte,
                     show (2 - 1 : Nat) = 1 from rfl,
                     show (2 - 2 : Nat) = 0 from rfl]
          have h_topB_idx : (1 : Nat) < V.limbs.size := by omega
          have h_v0_idx : (0 : Nat) < V.limbs.size := by omega
          set topB : UInt64 := V.limbs[1]'h_topB_idx with htopB_def
          set v0 : UInt64 := V.limbs[0]'h_v0_idx with hv0_def
          have h_topB_ne : topB ≠ 0 := by
            intro h0
            apply V.last_ne_zero
            rw [Array.back?_eq_getElem?]
            rw [show V.limbs.size - 1 = 1 from by omega]
            rw [Array.getElem?_eq_getElem h_topB_idx]
            exact congrArg some h0
          have hk_le : V.limbs[1].leadingZeros ≤ 63 :=
            UInt64.leadingZeros_le _ h_topB_ne
          have hV_eq : V.toNat = V.limbs[1].toNat * 2 ^ 64 + V.limbs[0].toNat := by
            rw [← htopB_def, ← hv0_def]; exact toNat_of_size_two V h2V
          have h_UBufRaw_size : (U.limbs ++ #[(0:UInt64)]).size = U.limbs.size + 1 := by
            rw [Array.size_append]; rfl
          split_ifs with hk0
          · -- k = 0 branch: UBuf = U.limbs ++ #[0], d_top = topB ||| 0 = topB, d0 = v0.
            have hk_zero : V.limbs[1].leadingZeros = 0 := hk0
            have h_kU_zero : (UInt64.ofNat V.limbs[1].leadingZeros : UInt64) = 0 := by
              rw [hk_zero]; rfl
            -- Simplify d_top and d0.
            have h_dtop_eq :
                V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros ||| (0:UInt64)
                  = V.limbs[1] := by
              rw [h_kU_zero, UInt64.shiftLeft_zero, UInt64.or_zero]
            have h_d0_eq :
                V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros = V.limbs[0] := by
              rw [h_kU_zero, UInt64.shiftLeft_zero]
            -- d_top normalization (after simplification, d_top = topB).
            have h_dtop_norm :
                2 ^ 63 ≤ (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros |||
                            (0:UInt64)).toNat := by
              rw [h_dtop_eq]
              have h := UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros V.limbs[1] h_topB_ne
              rw [h_kU_zero, UInt64.shiftLeft_zero] at h; exact h
            -- UBuf = U.limbs ++ #[0]; toNatLimbsList = U.toNat * 2^0 = U.toNat.
            have h_UBuf_toNat :
                toNatLimbsList ((U.limbs ++ #[(0:UInt64)]).toList)
                  = U.toNat * 2 ^ V.limbs[1].leadingZeros := by
              rw [hk_zero, Nat.pow_zero, Nat.mul_one]
              exact toNatLimbsList_UBufRaw U
            -- d_top * 2^64 + d0 = V * 2^0 = V.
            have h_dtop_d0_eq :
                (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros |||
                  (0:UInt64)).toNat * 2 ^ 64
                  + (V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros).toNat
                  = V.toNat * 2 ^ V.limbs[1].leadingZeros := by
              rw [h_dtop_eq, h_d0_eq, hk_zero, Nat.pow_zero, Nat.mul_one]
              exact hV_eq.symm
            -- Apply finish with concrete d_top, d0 expressions.
            exact divMod_size2_finish U V V.limbs[1].leadingZeros hk_le
                    (U.limbs ++ #[0])
                    (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros ||| 0)
                    (V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros)
                    h_UBufRaw_size h_dtop_norm h_UBuf_toNat h_dtop_d0_eq hV_toNat_pos
          · -- k > 0 branch.
            have hk_pos : 1 ≤ V.limbs[1].leadingZeros := Nat.one_le_iff_ne_zero.mpr hk0
            -- (v0 >> (64-k)).toNat < 2^k (used as carry bound).
            obtain ⟨_, h_v0_carry_lt⟩ :=
              limb_shift_step V.limbs[0] 0 V.limbs[1].leadingZeros
                hk_pos hk_le (Nat.two_pow_pos _)
            -- topB * 2^k < 2^64 (used to derive (topB >> (64-k)).toNat = 0).
            obtain ⟨_, h_topB_shl_lt⟩ :=
              topB_shl_lt V.limbs[1] V.limbs[1].leadingZeros rfl h_topB_ne
            have h_topB_lt_pow :
                V.limbs[1].toNat < 2 ^ (64 - V.limbs[1].leadingZeros) := by
              have h_pow_pos : 0 < (2:Nat) ^ V.limbs[1].leadingZeros := Nat.two_pow_pos _
              have h_split : (2:Nat) ^ 64
                  = 2 ^ (64 - V.limbs[1].leadingZeros) * 2 ^ V.limbs[1].leadingZeros := by
                rw [← Nat.pow_add]; congr 1; omega
              rw [h_split] at h_topB_shl_lt
              exact (Nat.mul_lt_mul_right h_pow_pos).mp h_topB_shl_lt
            have h_topB_shr_zero :
                (V.limbs[1] >>> UInt64.ofNat (64 - V.limbs[1].leadingZeros)).toNat = 0 := by
              rw [UInt64.toNat_shiftRight]
              have h_ofNat :
                  (UInt64.ofNat (64 - V.limbs[1].leadingZeros) : UInt64).toNat
                    = 64 - V.limbs[1].leadingZeros := by
                show (64 - V.limbs[1].leadingZeros) % 2 ^ 64 = _
                apply Nat.mod_eq_of_lt; omega
              rw [h_ofNat]
              rw [Nat.mod_eq_of_lt (show 64 - V.limbs[1].leadingZeros < 64 from by omega)]
              rw [Nat.shiftRight_eq_div_pow]
              exact Nat.div_eq_of_lt h_topB_lt_pow
            -- d_top equation via limb_shift_step on topB.
            obtain ⟨h_dtop_or_eq, _⟩ :=
              limb_shift_step V.limbs[1]
                (V.limbs[0] >>> UInt64.ofNat (64 - V.limbs[1].leadingZeros))
                V.limbs[1].leadingZeros hk_pos hk_le h_v0_carry_lt
            rw [h_topB_shr_zero, Nat.zero_mul, Nat.add_zero] at h_dtop_or_eq
            -- d0 equation via limb_shift_step on v0 with carry 0.
            obtain ⟨h_v0_shl_eq, _⟩ :=
              limb_shift_step V.limbs[0] 0 V.limbs[1].leadingZeros
                hk_pos hk_le (Nat.two_pow_pos _)
            rw [UInt64.or_zero, UInt64.toNat_zero, Nat.add_zero] at h_v0_shl_eq
            -- Three preconditions for divMod_size2_finish.
            have h_size_eq :
                (shiftLimbsLeft (U.limbs ++ #[(0:UInt64)]) 0 (U.limbs.size + 1)
                    V.limbs[1].leadingZeros (Nat.zero_le _) (by rw [h_UBufRaw_size])
                    hk_pos hk_le).1.size = U.limbs.size + 1 := by
              rw [shiftLimbsLeft_size]; exact h_UBufRaw_size
            have h_dtop_norm :
                2 ^ 63 ≤ (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros |||
                            V.limbs[0] >>> UInt64.ofNat (64 - V.limbs[1].leadingZeros)).toNat := by
              have h_shl_ge :=
                UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros V.limbs[1] h_topB_ne
              rw [UInt64.toNat_or]
              exact Nat.le_trans h_shl_ge Nat.left_le_or
            have h_UBuf_toNat :
                toNatLimbsList
                    (shiftLimbsLeft (U.limbs ++ #[(0:UInt64)]) 0 (U.limbs.size + 1)
                      V.limbs[1].leadingZeros (Nat.zero_le _) (by rw [h_UBufRaw_size])
                      hk_pos hk_le).1.toList
                  = U.toNat * 2 ^ V.limbs[1].leadingZeros :=
              toNatLimbsList_shifted_UBufRaw U V.limbs[1].leadingZeros hk_pos hk_le
            have h_dtop_d0_eq :
                (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros |||
                  V.limbs[0] >>> UInt64.ofNat (64 - V.limbs[1].leadingZeros)).toNat * 2 ^ 64 +
                  (V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros).toNat =
                V.toNat * 2 ^ V.limbs[1].leadingZeros := by
              rw [h_dtop_or_eq, hV_eq]
              calc (V.limbs[1].toNat * 2 ^ V.limbs[1].leadingZeros
                      + (V.limbs[0] >>> UInt64.ofNat
                          (64 - V.limbs[1].leadingZeros)).toNat) * 2 ^ 64
                    + (V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros).toNat
                  = V.limbs[1].toNat * 2 ^ V.limbs[1].leadingZeros * 2 ^ 64
                      + ((V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros).toNat
                         + (V.limbs[0] >>> UInt64.ofNat
                            (64 - V.limbs[1].leadingZeros)).toNat * 2 ^ 64) := by ring
                _ = V.limbs[1].toNat * 2 ^ V.limbs[1].leadingZeros * 2 ^ 64
                      + V.limbs[0].toNat * 2 ^ V.limbs[1].leadingZeros := by
                      rw [h_v0_shl_eq]
                _ = (V.limbs[1].toNat * 2 ^ 64 + V.limbs[0].toNat)
                      * 2 ^ V.limbs[1].leadingZeros := by ring
            exact divMod_size2_finish U V V.limbs[1].leadingZeros hk_le _ _ _
                    h_size_eq h_dtop_norm h_UBuf_toNat h_dtop_d0_eq hV_toNat_pos
        · -- Case 5: V.limbs.size ≥ 3.
          simp only [h2V, ↓reduceDIte]
          set n := V.limbs.size with hn_def
          set nU := U.limbs.size with hnU_def
          have h_n_ge_3 : 3 ≤ n := by omega
          have h_top_idx : n - 1 < V.limbs.size := by omega
          have h_n2_idx : n - 2 < V.limbs.size := by omega
          set topB : UInt64 := V.limbs[n - 1]'h_top_idx with htopB_def
          have h_topB_ne : topB ≠ 0 := by
            intro h0
            apply V.last_ne_zero
            rw [Array.back?_eq_getElem?]
            rw [show V.limbs.size - 1 = n - 1 from rfl]
            rw [Array.getElem?_eq_getElem h_top_idx]
            exact congrArg some h0
          have hk_le : topB.leadingZeros ≤ 63 :=
            UInt64.leadingZeros_le _ h_topB_ne
          have h_UBufRaw_size : (U.limbs ++ #[(0 : UInt64)]).size = nU + 1 := by
            rw [Array.size_append]; rfl
          split_ifs with hk0
          · -- k = 0 branch.
            have hk_zero : topB.leadingZeros = 0 := hk0
            have h_kU_zero : (UInt64.ofNat topB.leadingZeros : UInt64) = 0 := by
              rw [hk_zero]; rfl
            -- d_top = topB <<< 0 ||| 0 = topB.
            have h_dtop_eq :
                topB <<< UInt64.ofNat topB.leadingZeros ||| (0:UInt64)
                  = topB := by
              rw [h_kU_zero, UInt64.shiftLeft_zero, UInt64.or_zero]
            -- VBuf = V.limbs.set (n-1) topB. Since V.limbs[n-1] = topB,
            -- the set is a no-op at the value level.
            have h_set_no_op : V.limbs.set (n - 1) topB h_top_idx = V.limbs := by
              apply Array.ext
              · rw [Array.size_set]
              · intro i hi1 hi2
                rw [Array.getElem_set]
                split_ifs with h_eq
                · subst h_eq; exact htopB_def
                · rfl
            -- h_VBuf_norm: VBuf[n-1] = topB, and topB has high bit ≥ 2^63 since
            -- leadingZeros = 0.
            have h_topB_norm : 2 ^ 63 ≤ topB.toNat := by
              have h := UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros topB h_topB_ne
              rw [h_kU_zero, UInt64.shiftLeft_zero] at h; exact h
            -- toNatLimbsList of VBuf (after set) = V.toNat.
            have h_VBuf_toNat :
                toNatLimbsList ((V.limbs.set (n - 1)
                    (topB <<< UInt64.ofNat topB.leadingZeros ||| 0)
                    h_top_idx).toList)
                  = V.toNat * 2 ^ topB.leadingZeros := by
              rw [h_dtop_eq, h_set_no_op, hk_zero, Nat.pow_zero, Nat.mul_one]
              rfl
            have h_UBuf_toNat :
                toNatLimbsList ((U.limbs ++ #[(0:UInt64)]).toList)
                  = U.toNat * 2 ^ topB.leadingZeros := by
              rw [hk_zero, Nat.pow_zero, Nat.mul_one]
              exact toNatLimbsList_UBufRaw U
            have h_VBuf_size_eq :
                (V.limbs.set (n - 1)
                    (topB <<< UInt64.ofNat topB.leadingZeros ||| 0)
                    h_top_idx).size = n := by
              rw [Array.size_set]
            have h_VBuf_norm :
                2 ^ 63 ≤ ((V.limbs.set (n - 1)
                    (topB <<< UInt64.ofNat topB.leadingZeros ||| 0)
                    h_top_idx)[0 + n - 1]'(by rw [h_VBuf_size_eq]; omega)).toNat := by
              have h_idx_eq : (0 + n - 1 : Nat) = n - 1 := by omega
              have h_get_eq :
                  (V.limbs.set (n - 1)
                      (topB <<< UInt64.ofNat topB.leadingZeros ||| 0)
                      h_top_idx)[0 + n - 1]'(by rw [h_VBuf_size_eq]; omega)
                  = topB <<< UInt64.ofNat topB.leadingZeros ||| 0 := by
                conv_lhs => rw [Array.getElem_set]
                rw [if_pos h_idx_eq.symm]
              rw [h_get_eq, h_dtop_eq]
              exact h_topB_norm
            exact divMod_size_ge3_finish U V topB.leadingZeros hk_le
                    (U.limbs ++ #[0])
                    (V.limbs.set (n - 1)
                      (topB <<< UInt64.ofNat topB.leadingZeros ||| 0) h_top_idx)
                    h_n_ge_3 h_nU_ge_n h_UBufRaw_size h_VBuf_size_eq
                    h_VBuf_norm h_UBuf_toNat h_VBuf_toNat hV_toNat_pos
          · -- k > 0 branch.
            have hk_pos : 1 ≤ topB.leadingZeros := Nat.one_le_iff_ne_zero.mpr hk0
            -- Bound on V.limbs[n - 2] >>> (64 - k) from limb_shift_step.
            obtain ⟨_, h_carry_lt⟩ :=
              limb_shift_step (V.limbs[n - 2]'h_n2_idx) 0 topB.leadingZeros
                hk_pos hk_le (Nat.two_pow_pos _)
            -- Bound on topB * 2^k.
            obtain ⟨_, h_topB_shl_lt⟩ :=
              topB_shl_lt topB topB.leadingZeros rfl h_topB_ne
            -- Show topB >>> (64 - k) = 0.
            have h_topB_lt_pow :
                topB.toNat < 2 ^ (64 - topB.leadingZeros) := by
              have h_pow_pos : 0 < (2:Nat) ^ topB.leadingZeros := Nat.two_pow_pos _
              have h_split : (2:Nat) ^ 64
                  = 2 ^ (64 - topB.leadingZeros) * 2 ^ topB.leadingZeros := by
                rw [← Nat.pow_add]; congr 1; omega
              rw [h_split] at h_topB_shl_lt
              exact (Nat.mul_lt_mul_right h_pow_pos).mp h_topB_shl_lt
            have h_topB_shr_zero :
                (topB >>> UInt64.ofNat (64 - topB.leadingZeros)).toNat = 0 := by
              rw [UInt64.toNat_shiftRight]
              have h_ofNat : (UInt64.ofNat (64 - topB.leadingZeros) : UInt64).toNat
                  = 64 - topB.leadingZeros := by
                show (64 - topB.leadingZeros) % 2 ^ 64 = _
                apply Nat.mod_eq_of_lt; omega
              rw [h_ofNat,
                  Nat.mod_eq_of_lt (show 64 - topB.leadingZeros < 64 from by omega),
                  Nat.shiftRight_eq_div_pow]
              exact Nat.div_eq_of_lt h_topB_lt_pow
            -- d_top = topB <<< k ||| (V.limbs[n - 2] >>> (64 - k)).
            obtain ⟨h_dtop_or_eq, _⟩ :=
              limb_shift_step topB
                (V.limbs[n - 2]'h_n2_idx >>> UInt64.ofNat (64 - topB.leadingZeros))
                topB.leadingZeros hk_pos hk_le h_carry_lt
            rw [h_topB_shr_zero, Nat.zero_mul, Nat.add_zero] at h_dtop_or_eq
            -- d_top normalization.
            have h_dtop_norm :
                2 ^ 63 ≤ (topB <<< UInt64.ofNat topB.leadingZeros |||
                  (V.limbs[n - 2]'h_n2_idx >>>
                    UInt64.ofNat (64 - topB.leadingZeros))).toNat := by
              have h_shl_ge :=
                UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros topB h_topB_ne
              rw [UInt64.toNat_or]
              exact Nat.le_trans h_shl_ge Nat.left_le_or
            -- VBufRaw size and getElem at n-1 (preserved by shiftLimbsLeft 0 (n-1)).
            set VBufRaw : Array UInt64 :=
              (shiftLimbsLeft V.limbs 0 (n - 1) topB.leadingZeros (by omega) (by omega)
                hk_pos hk_le).1 with hVBufRaw_def
            have h_VBufRaw_size : VBufRaw.size = n := by
              rw [hVBufRaw_def, shiftLimbsLeft_size]
            have h_VBufRaw_len : VBufRaw.toList.length = n := by
              rw [Array.length_toList, h_VBufRaw_size]
            have h_top_in_raw : n - 1 < VBufRaw.size := by rw [h_VBufRaw_size]; omega
            -- VBuf and its size.
            set d_top : UInt64 :=
              topB <<< UInt64.ofNat topB.leadingZeros |||
                V.limbs[n - 2]'h_n2_idx >>> UInt64.ofNat (64 - topB.leadingZeros)
              with hdtop_def
            set VBuf : Array UInt64 := VBufRaw.set (n - 1) d_top h_top_in_raw
              with hVBuf_def
            have h_VBuf_size_eq : VBuf.size = n := by
              rw [hVBuf_def, Array.size_set]; exact h_VBufRaw_size
            have h_VBuf_norm :
                2 ^ 63 ≤ (VBuf[0 + n - 1]'(by rw [h_VBuf_size_eq]; omega)).toNat := by
              have h_idx_eq : (0 + n - 1 : Nat) = n - 1 := by omega
              have h_get_eq :
                  VBuf[0 + n - 1]'(by rw [h_VBuf_size_eq]; omega) = d_top := by
                show (VBufRaw.set (n - 1) d_top h_top_in_raw)[0 + n - 1] = d_top
                rw [Array.getElem_set]
                rw [if_pos h_idx_eq.symm]
              rw [h_get_eq]; exact h_dtop_norm
            -- UBuf representation.
            have h_UBuf_size_dyn :
                (shiftLimbsLeft (U.limbs ++ #[(0:UInt64)]) 0 (nU + 1) topB.leadingZeros
                   (Nat.zero_le _) (by rw [h_UBufRaw_size]) hk_pos hk_le).1.size
                  = nU + 1 := by
              rw [shiftLimbsLeft_size]; exact h_UBufRaw_size
            have h_UBuf_toNat :
                toNatLimbsList
                    (shiftLimbsLeft (U.limbs ++ #[(0:UInt64)]) 0 (nU + 1)
                      topB.leadingZeros (Nat.zero_le _) (by rw [h_UBufRaw_size])
                      hk_pos hk_le).1.toList
                  = U.toNat * 2 ^ topB.leadingZeros :=
              toNatLimbsList_shifted_UBufRaw U topB.leadingZeros hk_pos hk_le
            -- VBuf representation: toNatLimbsList VBuf.toList = V.toNat * 2^k.
            have h_VBuf_toNat :
                toNatLimbsList VBuf.toList = V.toNat * 2 ^ topB.leadingZeros := by
              -- Step 1: VBuf.toList = VBufRaw.toList.take (n-1) ++ [d_top].
              have h_n_minus_1_lt : n - 1 < VBufRaw.toList.length := by
                rw [h_VBufRaw_len]; omega
              have h_drop_eq :
                  VBufRaw.toList.drop (n - 1)
                    = [VBufRaw.toList[n - 1]'h_n_minus_1_lt] := by
                rw [List.drop_eq_getElem_cons h_n_minus_1_lt]
                congr 1
                exact List.drop_of_length_le (by rw [h_VBufRaw_len]; omega)
              have h_VBufRaw_split :
                  VBufRaw.toList
                    = VBufRaw.toList.take (n - 1)
                      ++ [VBufRaw.toList[n - 1]'h_n_minus_1_lt] := by
                conv_lhs =>
                  rw [← List.take_append_drop (n - 1) VBufRaw.toList, h_drop_eq]
              have h_VBuf_toList :
                  VBuf.toList = VBufRaw.toList.take (n - 1) ++ [d_top] := by
                rw [hVBuf_def, Array.toList_set]
                conv_lhs => rw [h_VBufRaw_split]
                rw [List.set_append_right _ _
                      (by rw [List.length_take, h_VBufRaw_len]; omega)]
                congr 1
                rw [show (n - 1) - (VBufRaw.toList.take (n - 1)).length = 0
                      from by rw [List.length_take, h_VBufRaw_len]; omega]
                rfl
              -- Step 2: toNatLimbsList of VBuf.toList.
              rw [h_VBuf_toList, toNatLimbsList_append]
              have h_take_len :
                  (VBufRaw.toList.take (n - 1)).length = n - 1 := by
                rw [List.length_take]; omega
              rw [h_take_len]
              have h_dtop_singleton : toNatLimbsList [d_top] = d_top.toNat := by
                simp [toNatLimbsList]
              rw [h_dtop_singleton]
              -- Step 3: V.toNat splits as topB * 2^(64*(n-1)) + bottom.
              have hV_split :
                  V.toNat
                    = topB.toNat * 2 ^ (64 * (n - 1))
                      + toNatLimbsList (V.limbs.toList.take (n - 1)) := by
                show toNatLimbsList V.limbs.toList = _
                have h_V_len : V.limbs.toList.length = n := rfl
                have h_n_lt_V : n - 1 < V.limbs.toList.length := by
                  rw [h_V_len]; omega
                have h_V_drop_eq :
                    V.limbs.toList.drop (n - 1)
                      = [V.limbs.toList[n - 1]'h_n_lt_V] := by
                  rw [List.drop_eq_getElem_cons h_n_lt_V]
                  congr 1
                  exact List.drop_of_length_le (by rw [h_V_len]; omega)
                conv_lhs =>
                  rw [← List.take_append_drop (n - 1) V.limbs.toList, h_V_drop_eq]
                rw [toNatLimbsList_append]
                have h_take_len_V :
                    (V.limbs.toList.take (n - 1)).length = n - 1 := by
                  rw [List.length_take]; omega
                rw [h_take_len_V]
                have h_singleton :
                    toNatLimbsList [V.limbs.toList[n - 1]'h_n_lt_V] = topB.toNat := by
                  rw [show V.limbs.toList[n - 1]'h_n_lt_V
                          = V.limbs[n - 1]'h_top_idx
                      from (Array.getElem_toList _).symm,
                      ← htopB_def]
                  simp [toNatLimbsList]
                rw [h_singleton]
              -- Step 4: shiftLimbsLeft_toNat for the bottom n-1 limbs.
              have h_inv :=
                shiftLimbsLeft_toNat V.limbs 0 (n - 1) topB.leadingZeros
                  (by omega) (by omega) hk_pos hk_le
              simp only [List.drop_zero, Nat.sub_zero] at h_inv
              rw [← hVBufRaw_def] at h_inv
              -- carry from shiftLimbsLeft = V.limbs[n - 2] >>> (64 - k).
              have h_carry_eq :
                  (shiftLimbsLeft V.limbs 0 (n - 1) topB.leadingZeros (by omega)
                    (by omega) hk_pos hk_le).2
                    = V.limbs[(n - 1) - 1]'(by omega)
                        >>> UInt64.ofNat (64 - topB.leadingZeros) := by
                apply shiftLimbsLeft_carry_eq; omega
              rw [h_carry_eq] at h_inv
              have h_n2_idx_eq :
                  V.limbs[(n - 1) - 1]'(by omega) = V.limbs[n - 2]'h_n2_idx := by
                congr 1
              rw [h_n2_idx_eq] at h_inv
              -- Now combine. d_top.toNat = topB * 2^k + carry.toNat.
              rw [show d_top = topB <<< UInt64.ofNat topB.leadingZeros
                          ||| (V.limbs[n - 2]'h_n2_idx
                            >>> UInt64.ofNat (64 - topB.leadingZeros)) from rfl,
                  h_dtop_or_eq]
              rw [hV_split]
              -- Set abbreviations to make omega/ring tractable.
              set k := topB.leadingZeros with hk_def
              set V_take := toNatLimbsList (V.limbs.toList.take (n - 1)) with hVtake_def
              set bot := toNatLimbsList (VBufRaw.toList.take (n - 1)) with hbot_def
              set ctop : Nat :=
                (V.limbs[n - 2]'h_n2_idx >>> UInt64.ofNat (64 - k)).toNat
                with hctop_def
              -- h_inv : bot + ctop * 2^(64*(n-1)) = V_take * 2^k.
              -- Goal: (topB.toNat * 2^k + ctop) * 2^(64*(n-1)) + bot
              --        = (topB.toNat * 2^(64*(n-1)) + V_take) * 2^k.
              have h_le : ctop * 2 ^ (64 * (n - 1)) ≤ V_take * 2 ^ k := by omega
              have h_bot_eq :
                  bot
                    = V_take * 2 ^ k - ctop * 2 ^ (64 * (n - 1)) := by omega
              rw [h_bot_eq]
              have h_add_sub :
                  (topB.toNat * 2 ^ k + ctop) * 2 ^ (64 * (n - 1))
                      + (V_take * 2 ^ k - ctop * 2 ^ (64 * (n - 1)))
                    = topB.toNat * 2 ^ k * 2 ^ (64 * (n - 1)) + V_take * 2 ^ k := by
                have h_expand :
                    (topB.toNat * 2 ^ k + ctop) * 2 ^ (64 * (n - 1))
                      = topB.toNat * 2 ^ k * 2 ^ (64 * (n - 1))
                        + ctop * 2 ^ (64 * (n - 1)) := by ring
                rw [h_expand]
                omega
              rw [h_add_sub]
              ring
            exact divMod_size_ge3_finish U V topB.leadingZeros hk_le
                    (shiftLimbsLeft (U.limbs ++ #[(0:UInt64)]) 0 (nU + 1)
                      topB.leadingZeros (Nat.zero_le _) (by rw [h_UBufRaw_size])
                      hk_pos hk_le).1
                    VBuf
                    h_n_ge_3 h_nU_ge_n h_UBuf_size_dyn h_VBuf_size_eq
                    h_VBuf_norm h_UBuf_toNat h_VBuf_toNat hV_toNat_pos

/-! ### Correctness of `div` and `mod` -/

/-- When the divisor is zero, `divMod` returns `(0, U)`. -/
private lemma divMod_of_toNat_zero (U V : AzNat) (hV : V.toNat = 0) :
    divMod U V = (0, U) := by
  have h_size : V.limbs.size = 0 := (toNat_eq_zero_iff V).mp hV
  unfold divMod
  rw [dif_pos h_size]

/-- `(U / V).toNat = U.toNat / V.toNat`. -/
@[simp] theorem toNat_div (U V : AzNat) : (U / V).toNat = U.toNat / V.toNat := by
  show (divMod U V).1.toNat = _
  by_cases hV : V.toNat = 0
  · rw [divMod_of_toNat_zero U V hV, hV, Nat.div_zero, toNat_zero]
  · obtain ⟨h_id, h_lt⟩ := divMod_toNat U V
    have h_lt' := h_lt hV
    have h_pos : 0 < V.toNat := Nat.pos_of_ne_zero hV
    have h_eq : U.toNat
        = (divMod U V).2.toNat + (divMod U V).1.toNat * V.toNat := by omega
    rw [h_eq, Nat.add_mul_div_right _ _ h_pos, Nat.div_eq_of_lt h_lt', Nat.zero_add]

/-- `(U % V).toNat = U.toNat % V.toNat`. -/
@[simp] theorem toNat_mod (U V : AzNat) : (U % V).toNat = U.toNat % V.toNat := by
  show (divMod U V).2.toNat = _
  by_cases hV : V.toNat = 0
  · rw [divMod_of_toNat_zero U V hV, hV, Nat.mod_zero]
  · obtain ⟨h_id, h_lt⟩ := divMod_toNat U V
    have h_lt' := h_lt hV
    have h_pos : 0 < V.toNat := Nat.pos_of_ne_zero hV
    have h_eq : U.toNat
        = (divMod U V).2.toNat + (divMod U V).1.toNat * V.toNat := by omega
    rw [h_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_lt']

/-- `ofNat`-version of `toNat_div`. -/
theorem ofNat_div (m n : Nat) : ofNat (m / n) = ofNat m / ofNat n := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_div, toNat_ofNat, toNat_ofNat]

/-- `ofNat`-version of `toNat_mod`. -/
theorem ofNat_mod (m n : Nat) : ofNat (m % n) = ofNat m % ofNat n := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_mod, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat
