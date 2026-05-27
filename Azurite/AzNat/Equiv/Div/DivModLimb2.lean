import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Div.DivModLimb
import Azurite.AzNat.Equiv.Compare
import Azurite.UInt64.Equiv.Div3By2

namespace Azurite.AzNat

/-- Size preservation of `divModLimb2.go`. -/
theorem divModLimb2.go_size (d1 d0 v : UInt64) (a : Array UInt64) (lo j : Nat)
    (r1 r0 : UInt64) (hbnd : lo + j ≤ a.size) :
    (divModLimb2.go d1 d0 v a lo j r1 r0 hbnd).1.size = a.size := by
  induction j generalizing a r1 r0 with
  | zero => rw [divModLimb2.go]
  | succ j ih =>
    rw [divModLimb2.go]
    rw [ih, Array.size_set]

/-- `divModLimb2.go` preserves positions before `lo`. -/
theorem divModLimb2.go_toList_take (d1 d0 v : UInt64) (a : Array UInt64) (lo j : Nat)
    (r1 r0 : UInt64) (hbnd : lo + j ≤ a.size) :
    (divModLimb2.go d1 d0 v a lo j r1 r0 hbnd).1.toList.take lo
      = a.toList.take lo := by
  induction j generalizing a r1 r0 with
  | zero => rw [divModLimb2.go]
  | succ j ih =>
    rw [divModLimb2.go]
    rw [ih]
    rw [Array.toList_set, List.take_set_of_le (by omega)]

/-- `divModLimb2.go` preserves positions at or after `lo + j`. -/
theorem divModLimb2.go_toList_drop (d1 d0 v : UInt64) (a : Array UInt64) (lo j : Nat)
    (r1 r0 : UInt64) (hbnd : lo + j ≤ a.size) :
    (divModLimb2.go d1 d0 v a lo j r1 r0 hbnd).1.toList.drop (lo + j)
      = a.toList.drop (lo + j) := by
  induction j generalizing a r1 r0 with
  | zero => rw [divModLimb2.go]
  | succ j ih =>
    rw [divModLimb2.go]
    have h_eq : ∀ (l : List UInt64),
        l.drop (lo + (j + 1)) = (l.drop (lo + j)).drop 1 := fun l => by
      rw [List.drop_drop]; congr 1
    rw [h_eq, h_eq, ih]
    rw [Array.toList_set, List.drop_set]
    rw [if_neg (lt_irrefl _)]
    rw [show lo + j - (lo + j) = 0 from by omega]
    exact List.drop_set_of_lt (by decide : 0 < 1)

/-- Suffix preservation gives the value at position `lo + j` after `go`. -/
private lemma divModLimb2.go_getElem_lo_j_succ (d1 d0 v : UInt64)
    (a : Array UInt64) (lo j : Nat) (hbnd : lo + (j + 1) ≤ a.size)
    (h_idx : lo + j < a.size) (newVal : UInt64) (newR1 newR0 : UInt64)
    (h_size_set : lo + j ≤ (a.set (lo + j) newVal).size) :
    let final := divModLimb2.go d1 d0 v (a.set (lo + j) newVal) lo j newR1 newR0 h_size_set
    let h_final_size : lo + j < final.1.size := by
      rw [divModLimb2.go_size, Array.size_set]; exact h_idx
    final.1[lo + j]'h_final_size = newVal := by
  intro final h_final_size
  have h_drop := divModLimb2.go_toList_drop d1 d0 v (a.set (lo + j) newVal) lo j
                  newR1 newR0 h_size_set
  have h_lenL : final.1.toList.length = a.size := by
    rw [Array.length_toList, divModLimb2.go_size, Array.size_set]
  have h_lenR : (a.set (lo + j) newVal).toList.length = a.size := by
    rw [Array.length_toList, Array.size_set]
  have hL_pos : 0 < (final.1.toList.drop (lo + j)).length := by
    rw [List.length_drop, h_lenL]; omega
  have hR_pos : 0 < ((a.set (lo + j) newVal).toList.drop (lo + j)).length := by
    rw [List.length_drop, h_lenR]; omega
  have h_idx_set : lo + j < (a.set (lo + j) newVal).size := by
    rw [Array.size_set]; exact h_idx
  have h1 : final.1[lo + j]'h_final_size = (final.1.toList.drop (lo + j))[0]'hL_pos := by
    rw [List.getElem_drop]
    exact (Array.getElem_toList h_final_size).symm
  have h2 : ((a.set (lo + j) newVal).toList.drop (lo + j))[0]'hR_pos
          = (a.set (lo + j) newVal)[lo + j]'h_idx_set := by
    rw [List.getElem_drop]
    exact Array.getElem_toList _
  have h3 : (final.1.toList.drop (lo + j))[0]'hL_pos
          = ((a.set (lo + j) newVal).toList.drop (lo + j))[0]'hR_pos := by
    exact List.getElem_of_eq h_drop hL_pos
  rw [h1, h3, h2]
  exact Array.getElem_set_self _

/-- Main correctness invariant of `divModLimb2.go`. -/
private theorem divModLimb2.go_correct (d1 d0 v : UInt64) (a : Array UInt64)
    (lo j : Nat) (r1 r0 : UInt64) (hbnd : lo + j ≤ a.size)
    (hd1 : 2 ^ 63 ≤ d1.toNat) (hv : v = UInt64.reciprocal3By2 d1 d0 hd1)
    (hr : r1.toNat * 2 ^ 64 + r0.toNat < d1.toNat * 2 ^ 64 + d0.toNat) :
    (r1.toNat * 2 ^ 64 + r0.toNat) * 2 ^ (64 * j)
        + toNatLimbsList ((a.toList.drop lo).take j)
      = toNatLimbsList
          (((divModLimb2.go d1 d0 v a lo j r1 r0 hbnd).1.toList.drop lo).take j)
          * (d1.toNat * 2 ^ 64 + d0.toNat)
        + ((divModLimb2.go d1 d0 v a lo j r1 r0 hbnd).2.1.toNat * 2 ^ 64
          + (divModLimb2.go d1 d0 v a lo j r1 r0 hbnd).2.2.toNat)
    ∧ (divModLimb2.go d1 d0 v a lo j r1 r0 hbnd).2.1.toNat * 2 ^ 64
        + (divModLimb2.go d1 d0 v a lo j r1 r0 hbnd).2.2.toNat
        < d1.toNat * 2 ^ 64 + d0.toNat := by
  induction j generalizing a r1 r0 with
  | zero =>
    rw [divModLimb2.go]
    refine ⟨?_, hr⟩
    simp [toNatLimbsList]
  | succ j ih =>
    have h_idx : lo + j < a.size := by omega
    set u_j := a[lo + j]'h_idx with hu_j_def
    set qr := UInt64.div3By2 r1 r0 u_j d1 d0 v with hqr_def
    set a' := a.set (lo + j) qr.1 with ha'_def
    have h_size' : lo + j ≤ a'.size := by rw [ha'_def, Array.size_set]; omega
    have h_step : divModLimb2.go d1 d0 v a lo (j + 1) r1 r0 hbnd =
                  divModLimb2.go d1 d0 v a' lo j qr.2.1 qr.2.2 h_size' := by
      rw [divModLimb2.go]
    rw [h_step]
    -- div3By2 correctness.
    have hdiv := UInt64.toNat_div3By2 r1 r0 u_j d1 d0 v hd1 hr hv
    rw [← hqr_def] at hdiv
    obtain ⟨h_div_eq, h_qr_lt⟩ := hdiv
    -- IH on (a', j, qr.2.1, qr.2.2).
    have h_ih := ih a' qr.2.1 qr.2.2 h_size' h_qr_lt
    obtain ⟨h_ih_eq, h_ih_r_lt⟩ := h_ih
    set final := divModLimb2.go d1 d0 v a' lo j qr.2.1 qr.2.2 h_size' with hfinal_def
    refine ⟨?_, h_ih_r_lt⟩
    -- Suffix preservation: final.1[lo+j] = qr.1.
    have h_final_size : lo + j < final.1.size := by
      rw [hfinal_def, divModLimb2.go_size, ha'_def, Array.size_set]; exact h_idx
    have h_final_at_j : final.1[lo + j]'h_final_size = qr.1 :=
      divModLimb2.go_getElem_lo_j_succ d1 d0 v a lo j hbnd h_idx qr.1 qr.2.1 qr.2.2 h_size'
    -- a' agrees with a on positions [lo, lo + j).
    have h_a'_drop_take :
        (a'.toList.drop lo).take j = (a.toList.drop lo).take j := by
      rw [ha'_def, Array.toList_set, List.drop_set]
      simp only [show ¬ lo + j < lo from by omega, ↓reduceIte]
      rw [List.take_set_of_le (by omega)]
    rw [h_a'_drop_take] at h_ih_eq
    -- Q-side split.
    have h_Q_split :
        toNatLimbsList ((final.1.toList.drop lo).take (j + 1))
          = toNatLimbsList ((final.1.toList.drop lo).take j)
            + qr.1.toNat * 2 ^ (64 * j) := by
      rw [toNatLimbsList_drop_take_succ final.1 lo j h_final_size, h_final_at_j]
    -- A-side split.
    have h_A_split :
        toNatLimbsList ((a.toList.drop lo).take (j + 1))
          = toNatLimbsList ((a.toList.drop lo).take j) + u_j.toNat * 2 ^ (64 * j) :=
      toNatLimbsList_drop_take_succ a lo j h_idx
    rw [h_Q_split, h_A_split]
    have h_pow : (2 : Nat) ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by
      rw [show 64 * (j + 1) = 64 * j + 64 from by ring, Nat.pow_add]
    rw [h_pow]
    -- Linear combination of h_ih_eq and h_div_eq closes the equational goal.
    set A_j : Nat := toNatLimbsList ((a.toList.drop lo).take j)
    set Q_j : Nat := toNatLimbsList ((final.1.toList.drop lo).take j)
    set R2 : Nat := final.2.1.toNat * 2 ^ 64 + final.2.2.toNat
    -- h_ih_eq: (qr.2.1*2^64 + qr.2.2) * 2^(64j) + A_j = Q_j * (d1*2^64+d0) + R2
    -- h_div_eq: qr.1 * (d1*2^64+d0) + (qr.2.1*2^64+qr.2.2) = r1*2^128 + r0*2^64 + u_j
    linear_combination h_ih_eq - 2 ^ (64 * j) * h_div_eq

/-- Correctness of `divModLimb2`: the slice `[lo, hi)` divided by the normalized
    2-limb divisor `(d1, d0)` produces a quotient slice (overwriting the
    original) plus a 128-bit remainder `(r1, r0)`. -/
theorem divModLimb2_toNat (a : Array UInt64) (lo hi : Nat) (d1 d0 : UInt64)
    (hd1 : 2 ^ 63 ≤ d1.toNat) (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    let (a', r1, r0) := divModLimb2 a lo hi d1 d0 hd1 hlo hhi
    toNatLimbsList ((a.toList.drop lo).take (hi - lo))
      = toNatLimbsList ((a'.toList.drop lo).take (hi - lo))
          * (d1.toNat * 2 ^ 64 + d0.toNat)
        + (r1.toNat * 2 ^ 64 + r0.toNat)
    ∧ r1.toNat * 2 ^ 64 + r0.toNat < d1.toNat * 2 ^ 64 + d0.toNat := by
  unfold divModLimb2
  set v := UInt64.reciprocal3By2 d1 d0 hd1 with hv_def
  set len := hi - lo with hlen_def
  set res := divModLimb2.go d1 d0 v a lo len 0 0 (by omega) with hres_def
  have h_r_init : (0 : UInt64).toNat * 2 ^ 64 + (0 : UInt64).toNat
                  < d1.toNat * 2 ^ 64 + d0.toNat := by
    show 0 * 2 ^ 64 + 0 < d1.toNat * 2 ^ 64 + d0.toNat
    have h_d1_pos : 0 < d1.toNat := lt_of_lt_of_le (Nat.two_pow_pos 63) hd1
    have h_pow_pos : 0 < (2 : Nat) ^ 64 := Nat.two_pow_pos _
    have h_prod_pos : 0 < d1.toNat * 2 ^ 64 := Nat.mul_pos h_d1_pos h_pow_pos
    linarith
  have h_inner := divModLimb2.go_correct d1 d0 v a lo len 0 0 (by omega) hd1 hv_def h_r_init
  rw [← hres_def] at h_inner
  obtain ⟨h_inner_eq, h_inner_r_lt⟩ := h_inner
  refine ⟨?_, h_inner_r_lt⟩
  -- Initial remainder is 0; eliminate the leading scaled term.
  have h_zero_term : ((0 : UInt64).toNat * 2 ^ 64 + (0 : UInt64).toNat) * 2 ^ (64 * len) = 0 := by
    show (0 * 2 ^ 64 + 0) * 2 ^ (64 * len) = 0; ring
  rw [h_zero_term, Nat.zero_add] at h_inner_eq
  exact h_inner_eq

/-! ### Utility lemmas for `toNat` of small `AzNat` values -/

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

/-! ### Dividend buffer helpers and the size-2 divMod finish lemma -/

/-- The dividend buffer (with extra zero limb) has `toNat = U.toNat`. -/
theorem toNatLimbsList_UBufRaw (U : AzNat) :
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
theorem toNatLimbsList_shifted_UBufRaw (U : AzNat) (k : Nat)
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
  have h_inv := shiftLimbsLeft_toNat UBufRaw 0 (nU + 1) k (Nat.zero_le _)
                  (by rw [h_size]) hk_lb hk_ub
  simp only at h_inv
  rw [← hshifted_def, ← hcarry_def] at h_inv
  have h_drop_shifted : shifted.toList.drop 0 = shifted.toList := List.drop_zero
  have h_drop_raw : UBufRaw.toList.drop 0 = UBufRaw.toList := List.drop_zero
  have h_take_shifted : shifted.toList.take (nU + 1 - 0) = shifted.toList := by
    apply List.take_of_length_le
    rw [h_shifted_len]; omega
  have h_take_raw : UBufRaw.toList.take (nU + 1 - 0) = UBufRaw.toList := by
    apply List.take_of_length_le
    rw [h_raw_len]; omega
  rw [h_drop_shifted, h_take_shifted, h_drop_raw, h_take_raw] at h_inv
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
theorem topB_shl_lt (topB : UInt64) (k : Nat) (hk_eq : k = topB.leadingZeros)
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
theorem divMod_size2_finish (U V : AzNat)
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
  have h_UBuf_len : UBuf.toList.length = U.limbs.size + 1 := by
    rw [Array.length_toList, h_UBuf_size]
  have h_drop_full : UBuf.toList.drop 0 = UBuf.toList := List.drop_zero
  have h_take_full : UBuf.toList.take (U.limbs.size + 1 - 0) = UBuf.toList := by
    apply List.take_of_length_le; rw [h_UBuf_len]; omega
  rw [h_drop_full, h_take_full] at h_eq
  rw [h_UBuf_toNat] at h_eq
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
  rw [h_dtop_d0] at h_eq h_lt
  set quot_nat := toNatLimbsList res.1.toList with hquot_def
  set R_norm := res.2.1.toNat * 2 ^ 64 + res.2.2.toNat with hR_def
  have h_pow_pos : 0 < (2 : Nat) ^ k := Nat.two_pow_pos _
  have hV_2k_pos : 0 < V.toNat * 2 ^ k := Nat.mul_pos hV_pos h_pow_pos
  have h_quot_V_le_U : quot_nat * V.toNat ≤ U.toNat := by
    have h_le_2k : quot_nat * V.toNat * 2 ^ k ≤ U.toNat * 2 ^ k := by
      have h_assoc : quot_nat * V.toNat * 2 ^ k = quot_nat * (V.toNat * 2 ^ k) := by ring
      rw [h_assoc, h_eq]; omega
    exact Nat.le_of_mul_le_mul_right h_le_2k h_pow_pos
  have h_R_eq : R_norm = (U.toNat - quot_nat * V.toNat) * 2 ^ k := by
    have h_assoc : quot_nat * (V.toNat * 2 ^ k) = quot_nat * V.toNat * 2 ^ k := by ring
    rw [h_assoc] at h_eq
    have h_sub_eq : (U.toNat - quot_nat * V.toNat) * 2 ^ k
                   = U.toNat * 2 ^ k - quot_nat * V.toNat * 2 ^ k := by
      rw [Nat.sub_mul]
    rw [h_sub_eq, h_eq, Nat.add_sub_cancel_left]
  have h_remNorm_eq : (ofLimbs #[res.2.2, res.2.1]).toNat = R_norm := by
    rw [hR_def]; exact toNat_ofLimbs_pair _ _
  have h_shr : (ofLimbs #[res.2.2, res.2.1] >>> k).toNat
              = (ofLimbs #[res.2.2, res.2.1]).toNat / 2 ^ k := by
    rw [hShiftRight_eq, toNat_shiftRight]
  rw [h_shr, h_remNorm_eq, h_R_eq]
  rw [Nat.mul_div_cancel _ h_pow_pos]
  have h_quot_eq : (ofLimbs res.1).toNat = quot_nat := by
    rw [toNat_ofLimbs, hquot_def]
  rw [h_quot_eq]
  refine ⟨?_, ?_⟩
  · omega
  · intro _
    have h_lt' : (U.toNat - quot_nat * V.toNat) * 2 ^ k < V.toNat * 2 ^ k := by
      rw [← h_R_eq]; exact h_lt
    exact Nat.lt_of_mul_lt_mul_right h_lt'

set_option maxHeartbeats 800000 in
/-- Correctness of `divMod U V` when `V.limbs.size ≤ 2`. Used by
    `recursiveDivModFast_toNat` to handle the schoolbook delegation. -/
theorem divMod_toNat_of_size_le2 (U V : AzNat) (hVsmall : V.limbs.size ≤ 2) :
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
      -- V.limbs.size = 2 (since 0 < size ≤ 2 and size ≠ 1).
      have h2V : V.limbs.size = 2 := by omega
      -- Case 3: U.limbs.size < V.limbs.size.
      by_cases hUV : U.limbs.size < V.limbs.size
      · simp only [hUV, ↓reduceDIte]
        refine ⟨?_, ?_⟩
        · show (0 : AzNat).toNat * V.toNat + U.toNat = U.toNat
          show 0 * V.toNat + U.toNat = U.toNat; ring
        · intro _; exact toNat_lt_of_size_lt U V hUV
      · simp only [hUV, ↓reduceDIte]
        by_cases hUV_num : U < V
        · simp only [hUV_num, ↓reduceIte]
          exact ⟨by simp, fun _ => (lt_iff_toNat_lt U V).mp hUV_num⟩
        · simp only [hUV_num, ↓reduceIte]
          have h_nU_ge_n : V.limbs.size ≤ U.limbs.size := Nat.le_of_not_lt hUV
          -- Case 4: V.limbs.size = 2. Dispatches to divModLimb2.
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
          · -- k = 0 branch.
            have hk_zero : V.limbs[1].leadingZeros = 0 := hk0
            have h_kU_zero : (UInt64.ofNat V.limbs[1].leadingZeros : UInt64) = 0 := by
              rw [hk_zero]; rfl
            have h_dtop_eq :
                V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros ||| (0:UInt64)
                  = V.limbs[1] := by
              rw [h_kU_zero, UInt64.shiftLeft_zero, UInt64.or_zero]
            have h_d0_eq :
                V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros = V.limbs[0] := by
              rw [h_kU_zero, UInt64.shiftLeft_zero]
            have h_dtop_norm :
                2 ^ 63 ≤ (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros |||
                            (0:UInt64)).toNat := by
              rw [h_dtop_eq]
              have h := UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros V.limbs[1] h_topB_ne
              rw [h_kU_zero, UInt64.shiftLeft_zero] at h; exact h
            have h_UBuf_toNat :
                toNatLimbsList ((U.limbs ++ #[(0:UInt64)]).toList)
                  = U.toNat * 2 ^ V.limbs[1].leadingZeros := by
              rw [hk_zero, Nat.pow_zero, Nat.mul_one]
              exact toNatLimbsList_UBufRaw U
            have h_dtop_d0_eq :
                (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros |||
                  (0:UInt64)).toNat * 2 ^ 64
                  + (V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros).toNat
                  = V.toNat * 2 ^ V.limbs[1].leadingZeros := by
              rw [h_dtop_eq, h_d0_eq, hk_zero, Nat.pow_zero, Nat.mul_one]
              exact hV_eq.symm
            exact divMod_size2_finish U V V.limbs[1].leadingZeros hk_le
                    (U.limbs ++ #[0])
                    (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros ||| 0)
                    (V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros)
                    h_UBufRaw_size h_dtop_norm h_UBuf_toNat h_dtop_d0_eq hV_toNat_pos
          · -- k > 0 branch.
            have hk_pos : 1 ≤ V.limbs[1].leadingZeros := Nat.one_le_iff_ne_zero.mpr hk0
            obtain ⟨_, h_v0_carry_lt⟩ :=
              limb_shift_step V.limbs[0] 0 V.limbs[1].leadingZeros
                hk_pos hk_le (Nat.two_pow_pos _)
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
            obtain ⟨h_dtop_or_eq, _⟩ :=
              limb_shift_step V.limbs[1]
                (V.limbs[0] >>> UInt64.ofNat (64 - V.limbs[1].leadingZeros))
                V.limbs[1].leadingZeros hk_pos hk_le h_v0_carry_lt
            rw [h_topB_shr_zero, Nat.zero_mul, Nat.add_zero] at h_dtop_or_eq
            obtain ⟨h_v0_shl_eq, _⟩ :=
              limb_shift_step V.limbs[0] 0 V.limbs[1].leadingZeros
                hk_pos hk_le (Nat.two_pow_pos _)
            rw [UInt64.or_zero, UInt64.toNat_zero, Nat.add_zero] at h_v0_shl_eq
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

end Azurite.AzNat
