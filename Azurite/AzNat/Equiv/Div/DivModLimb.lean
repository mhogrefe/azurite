import Azurite.AzNat.Div.Schoolbook
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.UInt64.Equiv.Basic
import Azurite.UInt64.Equiv.Div2By1
import Azurite.UInt64.Equiv.DivMod
import Azurite.UInt64.Equiv.LeadingZeros

namespace Azurite.AzNat

/-- Size preservation of `divModLimb.go`. -/
theorem divModLimb.go_size (d' inv : UInt64) (k : Nat) (hk : k ≤ 63)
    (a : Array UInt64) (lo j : Nat) (r : UInt64) (hbnd : lo + j ≤ a.size) :
    (divModLimb.go d' inv k hk a lo j r hbnd).1.size = a.size := by
  induction j generalizing a r with
  | zero => rw [divModLimb.go]
  | succ j ih =>
    rw [divModLimb.go]
    simp only []
    rw [ih, Array.size_set]

/-- `divModLimb.go` preserves positions before `lo`. -/
theorem divModLimb.go_toList_take (d' inv : UInt64) (k : Nat) (hk : k ≤ 63)
    (a : Array UInt64) (lo j : Nat) (r : UInt64) (hbnd : lo + j ≤ a.size) :
    (divModLimb.go d' inv k hk a lo j r hbnd).1.toList.take lo = a.toList.take lo := by
  induction j generalizing a r with
  | zero => rw [divModLimb.go]
  | succ j ih =>
    rw [divModLimb.go]
    simp only []
    rw [ih]
    rw [Array.toList_set, List.take_set_of_le (by omega)]

/-- `divModLimb.go` preserves positions at or after `lo + j`. -/
theorem divModLimb.go_toList_drop (d' inv : UInt64) (k : Nat) (hk : k ≤ 63)
    (a : Array UInt64) (lo j : Nat) (r : UInt64) (hbnd : lo + j ≤ a.size) :
    (divModLimb.go d' inv k hk a lo j r hbnd).1.toList.drop (lo + j)
      = a.toList.drop (lo + j) := by
  induction j generalizing a r with
  | zero => rw [divModLimb.go]
  | succ j ih =>
    rw [divModLimb.go]
    simp only []
    have h_eq : ∀ (l : List UInt64),
        l.drop (lo + (j + 1)) = (l.drop (lo + j)).drop 1 := fun l => by
      rw [List.drop_drop]; congr 1
    rw [h_eq, h_eq, ih]
    rw [Array.toList_set, List.drop_set]
    rw [ite_eq_right (lt_irrefl _)]
    rw [show lo + j - (lo + j) = 0 from by omega]
    exact List.drop_set_of_lt (by decide : 0 < 1)

/-- Suffix preservation gives the value at position `lo + j` after `go`. -/
private lemma divModLimb.go_getElem_lo_j_succ (d' inv : UInt64) (k : Nat) (hk : k ≤ 63)
    (a : Array UInt64) (lo j : Nat)
    (hbnd : lo + (j + 1) ≤ a.size)
    (h_idx : lo + j < a.size) (newVal : UInt64) (newR : UInt64)
    (h_size_set : lo + j ≤ (a.set (lo + j) newVal).size) :
    let final := divModLimb.go d' inv k hk (a.set (lo + j) newVal) lo j newR h_size_set
    let h_final_size : lo + j < final.1.size := by
      rw [divModLimb.go_size, Array.size_set]; exact h_idx
    final.1[lo + j]'h_final_size = newVal := by
  intro final h_final_size
  have h_drop := divModLimb.go_toList_drop d' inv k hk (a.set (lo + j) newVal) lo j
                  newR h_size_set
  have h_lenL : final.1.toList.length = a.size := by
    rw [Array.length_toList, divModLimb.go_size, Array.size_set]
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

/-- The high `k` bits of `A * 2^k` (where `A` is the toNat of a `j`-limb slice)
    equal `a[lo+j-1] >> (64-k)` (or 0 in the trivial cases). -/
private lemma top_bits_eq_u_carry (a : Array UInt64) (lo j k : Nat) (hk : k ≤ 63)
    (h_bnd : lo + j ≤ a.size) :
    toNatLimbsList ((a.toList.drop lo).take j) * 2 ^ k / 2 ^ (64 * j)
      = (if k = 0 then (0 : UInt64)
         else if hj0 : j = 0 then (0 : UInt64)
         else a[lo + j - 1]'(by omega) >>> UInt64.ofNat (64 - k)).toNat := by
  have h_A_lt : toNatLimbsList ((a.toList.drop lo).take j) < 2 ^ (64 * j) := by
    have hL := toNatLimbsList_lt_pow ((a.toList.drop lo).take j)
    have h_take_len : ((a.toList.drop lo).take j).length ≤ j := List.length_take_le _ _
    calc toNatLimbsList ((a.toList.drop lo).take j)
          < 2 ^ (64 * ((a.toList.drop lo).take j).length) := hL
        _ ≤ 2 ^ (64 * j) := Nat.pow_le_pow_right (by decide) (by omega)
  by_cases hk0 : k = 0
  · subst hk0
    rw [ite_eq_left rfl, show (2 : Nat) ^ 0 = 1 from rfl, Nat.mul_one]
    show toNatLimbsList _ / _ = (0 : UInt64).toNat
    exact Nat.div_eq_of_lt h_A_lt
  · rw [ite_eq_right hk0]
    by_cases hj0 : j = 0
    · subst hj0
      rw [dite_eq_left rfl]
      show toNatLimbsList _ * _ / _ = (0 : UInt64).toNat
      simp [toNatLimbsList]
    · rw [dite_eq_right hj0]
      have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have hk_lt : k < 64 := by omega
      have h_idx : lo + (j - 1) < a.size := by omega
      have h_idx' : lo + j - 1 < a.size := by omega
      -- Decompose: take j = take (j-1) ++ [a[lo + (j-1)]]
      set X := toNatLimbsList ((a.toList.drop lo).take (j - 1)) with hX_def
      set V := (a[lo + j - 1]'h_idx').toNat with hV_def
      have h_A_decomp :
          toNatLimbsList ((a.toList.drop lo).take j) = X + V * 2 ^ (64 * (j - 1)) := by
        have h_eq : (j - 1) + 1 = j := by omega
        conv_lhs => rw [← h_eq]
        rw [toNatLimbsList_drop_take_succ a lo (j - 1) h_idx]
        rw [hX_def, hV_def]
        have h_arr : a[lo + (j - 1)]'h_idx = a[lo + j - 1]'h_idx' := by
          congr 1; omega
        rw [h_arr]
      have h_X_lt : X < 2 ^ (64 * (j - 1)) := by
        have hL := toNatLimbsList_lt_pow ((a.toList.drop lo).take (j - 1))
        have h_take_len : ((a.toList.drop lo).take (j - 1)).length ≤ j - 1 :=
          List.length_take_le _ _
        calc X < 2 ^ (64 * ((a.toList.drop lo).take (j - 1)).length) := hL
          _ ≤ 2 ^ (64 * (j - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      have hV_lt : V < 2 ^ 64 := UInt64.toNat_lt _
      -- HI := V / 2^(64-k), LO := V % 2^(64-k); V = HI * 2^(64-k) + LO.
      set HI := V / 2 ^ (64 - k) with hHI_def
      set LO := V % 2 ^ (64 - k) with hLO_def
      have h_V_decomp : V = HI * 2 ^ (64 - k) + LO := by
        rw [hHI_def, hLO_def]; exact (Nat.div_add_mod' V _).symm
      have h_LO_lt : LO < 2 ^ (64 - k) := by
        rw [hLO_def]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have h_HI_lt : HI < 2 ^ k := by
        rw [hHI_def]
        apply Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _) |>.mpr
        rw [Nat.mul_comm, ← Nat.pow_add, show 64 - k + k = 64 from by omega]
        exact hV_lt
      -- A * 2^k = HI * 2^(64j) + Y, where Y := X * 2^k + LO * 2^(64*(j-1)+k) < 2^(64j)
      set Y := X * 2 ^ k + LO * 2 ^ (64 * (j - 1) + k) with hY_def
      have h_A2k : toNatLimbsList ((a.toList.drop lo).take j) * 2 ^ k
          = HI * 2 ^ (64 * j) + Y := by
        rw [h_A_decomp, hY_def]
        have h_pow : (2 : Nat) ^ (64 * j) = 2 ^ (64 * (j - 1)) * 2 ^ 64 := by
          rw [← Nat.pow_add]; congr 1; omega
        have h_pow_sub : (2 : Nat) ^ (64 - k) * 2 ^ k = 2 ^ 64 := by
          rw [← Nat.pow_add]; congr 1; omega
        have h_pow_lo : (2 : Nat) ^ (64 * (j - 1) + k) = 2 ^ (64 * (j - 1)) * 2 ^ k := by
          rw [Nat.pow_add]
        have h_eq : V * 2 ^ (64 * (j - 1)) * 2 ^ k
                  = HI * 2 ^ (64 * j) + LO * 2 ^ (64 * (j - 1) + k) := by
          rw [h_pow, h_pow_lo, h_V_decomp]
          have h1 : (HI * 2 ^ (64 - k) + LO) * 2 ^ (64 * (j - 1)) * 2 ^ k
                  = HI * 2 ^ (64 - k) * 2 ^ k * 2 ^ (64 * (j - 1))
                    + LO * (2 ^ (64 * (j - 1)) * 2 ^ k) := by ring
          rw [h1, Nat.mul_assoc HI _ (2 ^ k), h_pow_sub]
          ring
        linarith [h_eq]
      have h_Y_lt : Y < 2 ^ (64 * j) := by
        rw [hY_def]
        -- X * 2^k + LO * 2^(64(j-1)+k) = (X + LO * 2^(64(j-1))) * 2^k
        -- where X + LO * 2^(64(j-1)) < 2^(64j-k)
        have h_eq : X * 2 ^ k + LO * 2 ^ (64 * (j - 1) + k)
                  = (X + LO * 2 ^ (64 * (j - 1))) * 2 ^ k := by
          rw [Nat.add_mul]
          rw [Nat.mul_assoc LO _ (2 ^ k), ← Nat.pow_add]
        rw [h_eq]
        have h_inner_lt : X + LO * 2 ^ (64 * (j - 1)) < 2 ^ (64 * j - k) := by
          have h_LO_le : LO ≤ 2 ^ (64 - k) - 1 := by omega
          have h_X_le : X ≤ 2 ^ (64 * (j - 1)) - 1 := by omega
          have h_calc : X + LO * 2 ^ (64 * (j - 1))
              ≤ (2 ^ (64 * (j - 1)) - 1) + (2 ^ (64 - k) - 1) * 2 ^ (64 * (j - 1)) := by
            apply Nat.add_le_add h_X_le
            exact Nat.mul_le_mul_right _ h_LO_le
          have h_simpl : (2 ^ (64 * (j - 1)) - 1) + (2 ^ (64 - k) - 1) * 2 ^ (64 * (j - 1))
              = 2 ^ (64 - k) * 2 ^ (64 * (j - 1)) - 1 := by
            have h_pos : 0 < 2 ^ (64 - k) := Nat.two_pow_pos _
            have : (2 ^ (64 - k) - 1) * 2 ^ (64 * (j - 1))
                  = 2 ^ (64 - k) * 2 ^ (64 * (j - 1)) - 2 ^ (64 * (j - 1)) := by
              rw [Nat.sub_mul, Nat.one_mul]
            rw [this]
            have h_ge : 2 ^ (64 * (j - 1)) ≤ 2 ^ (64 - k) * 2 ^ (64 * (j - 1)) := by
              conv_lhs => rw [show (2 : Nat) ^ (64 * (j - 1)) = 1 * 2 ^ (64 * (j - 1)) from
                                (Nat.one_mul _).symm]
              exact Nat.mul_le_mul_right _ h_pos
            omega
          have h_pow_eq : 2 ^ (64 - k) * 2 ^ (64 * (j - 1)) = 2 ^ (64 * j - k) := by
            rw [← Nat.pow_add]; congr 1
            -- 64 - k + 64 * (j - 1) = 64 * j - k
            have h64 : 64 * (j - 1) + 64 = 64 * j := by
              rw [Nat.mul_sub_one]; omega
            omega
          rw [h_pow_eq] at h_simpl
          have h_pos : 0 < 2 ^ (64 * j - k) := Nat.two_pow_pos _
          omega
        have h_pow_split : (2 : Nat) ^ (64 * j) = 2 ^ (64 * j - k) * 2 ^ k := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [h_pow_split]
        exact Nat.mul_lt_mul_of_pos_right h_inner_lt (Nat.two_pow_pos _)
      -- Conclude: A * 2^k / 2^(64j) = HI.
      rw [h_A2k]
      rw [show HI * 2 ^ (64 * j) + Y = Y + 2 ^ (64 * j) * HI from by ring,
          Nat.add_mul_div_left _ _ (Nat.two_pow_pos (64 * j))]
      rw [Nat.div_eq_of_lt h_Y_lt]
      rw [Nat.zero_add]
      -- Show HI = (a[lo + j - 1] >>> UInt64.ofNat (64 - k)).toNat
      rw [_root_.UInt64.toNat_shiftRight]
      have h_ofNat : (UInt64.ofNat (64 - k)).toNat = 64 - k := by
        show (64 - k) % 2 ^ 64 = 64 - k
        exact Nat.mod_eq_of_lt (by omega)
      rw [h_ofNat]
      have h_sub_mod : (64 - k) % 64 = 64 - k := Nat.mod_eq_of_lt (by omega)
      rw [h_sub_mod, Nat.shiftRight_eq_div_pow]

/-- Main correctness invariant of `divModLimb.go`. -/
private theorem divModLimb.go_correct (d' inv : UInt64) (k : Nat) (hk : k ≤ 63)
    (a : Array UInt64) (lo j : Nat) (r : UInt64) (hbnd : lo + j ≤ a.size)
    (hd' : 2 ^ 63 ≤ d'.toNat) (hinv : inv = UInt64.reciprocal d' hd')
    (hr : r.toNat < d'.toNat) :
    r.toNat * 2 ^ (64 * j)
        + (toNatLimbsList ((a.toList.drop lo).take j) * 2 ^ k) % 2 ^ (64 * j)
      = toNatLimbsList
          (((divModLimb.go d' inv k hk a lo j r hbnd).1.toList.drop lo).take j)
          * d'.toNat
        + (divModLimb.go d' inv k hk a lo j r hbnd).2.toNat
    ∧ (divModLimb.go d' inv k hk a lo j r hbnd).2.toNat < d'.toNat := by
  induction j generalizing a r with
  | zero =>
    rw [divModLimb.go]
    refine ⟨?_, hr⟩
    simp [toNatLimbsList]
  | succ j ih =>
    have h_idx : lo + j < a.size := by omega
    set u_j := a[lo + j]'h_idx with hu_j_def
    set u_carry : UInt64 :=
      (if k = 0 then 0
      else if hj0 : j = 0 then 0
      else a[lo + j - 1]'(by omega) >>> UInt64.ofNat (64 - k)) with hu_carry_def
    set u_j_shifted := (u_j <<< UInt64.ofNat k) ||| u_carry with hu_j_shifted_def
    set qr := UInt64.div2By1 r u_j_shifted d' inv with hqr_def
    set a' := a.set (lo + j) qr.1 with ha'_def
    have h_size' : lo + j ≤ a'.size := by rw [ha'_def, Array.size_set]; omega
    have h_step : divModLimb.go d' inv k hk a lo (j + 1) r hbnd =
                  divModLimb.go d' inv k hk a' lo j qr.2 h_size' := by
      rw [divModLimb.go]
    rw [h_step]
    -- div2By1 correctness
    have hdiv := UInt64.toNat_div2By1 r u_j_shifted d' inv hd' hr hinv
    rw [← hqr_def] at hdiv
    obtain ⟨h_div_eq, h_r1_lt⟩ := hdiv
    -- IH on (a', j, qr.2)
    have h_ih := ih a' qr.2 h_size' h_r1_lt
    obtain ⟨h_ih_eq, h_ih_r_lt⟩ := h_ih
    -- final = recursive result.
    set final := divModLimb.go d' inv k hk a' lo j qr.2 h_size' with hfinal_def
    refine ⟨?_, h_ih_r_lt⟩
    -- Suffix preservation: final.1[lo+j] = qr.1.
    have h_final_size : lo + j < final.1.size := by
      rw [hfinal_def, divModLimb.go_size, ha'_def, Array.size_set]; exact h_idx
    have h_final_at_j : final.1[lo + j]'h_final_size = qr.1 :=
      divModLimb.go_getElem_lo_j_succ d' inv k hk a lo j hbnd h_idx qr.1 qr.2 h_size'
    -- a' agrees with a on positions [lo, lo + j).
    have h_a'_drop_take :
        (a'.toList.drop lo).take j = (a.toList.drop lo).take j := by
      rw [ha'_def, Array.toList_set, List.drop_set]
      simp only [show ¬ lo + j < lo from by omega, ↓reduceIte]
      rw [List.take_set_of_le (by omega)]
    -- Q-side split.
    have h_Q_split :
        toNatLimbsList ((final.1.toList.drop lo).take (j + 1))
          = toNatLimbsList ((final.1.toList.drop lo).take j) + qr.1.toNat * 2 ^ (64 * j) := by
      rw [toNatLimbsList_drop_take_succ final.1 lo j h_final_size, h_final_at_j]
    -- A-side split (A_succ = A + u_j * 2^(64j)).
    have h_A_split :
        toNatLimbsList ((a.toList.drop lo).take (j + 1))
          = toNatLimbsList ((a.toList.drop lo).take j) + u_j.toNat * 2 ^ (64 * j) :=
      toNatLimbsList_drop_take_succ a lo j h_idx
    -- A < 2^(64j).
    have h_A_lt : toNatLimbsList ((a.toList.drop lo).take j) < 2 ^ (64 * j) := by
      have hL := toNatLimbsList_lt_pow ((a.toList.drop lo).take j)
      have h_take_len : ((a.toList.drop lo).take j).length ≤ j := List.length_take_le _ _
      calc toNatLimbsList ((a.toList.drop lo).take j)
            < 2 ^ (64 * ((a.toList.drop lo).take j).length) := hL
          _ ≤ 2 ^ (64 * j) := Nat.pow_le_pow_right (by decide) (by omega)
    -- u_carry.toNat ≤ 2^k - (something) — we use the equality between top bits and u_carry.
    have h_T_eq : toNatLimbsList ((a.toList.drop lo).take j) * 2 ^ k / 2 ^ (64 * j)
                  = u_carry.toNat := by
      rw [hu_carry_def]
      exact top_bits_eq_u_carry a lo j k hk (by omega)
    -- Bound on u_carry: u_carry.toNat ≤ 2^k - 1 (when k ≥ 1) or = 0 (when k = 0).
    have h_uc_lt : (1 ≤ k ∧ u_carry.toNat < 2 ^ k) ∨ k = 0 := by
      by_cases hk0 : k = 0
      · right; exact hk0
      left
      refine ⟨Nat.pos_of_ne_zero hk0, ?_⟩
      rw [hu_carry_def]
      rw [ite_eq_right hk0]
      by_cases hj0 : j = 0
      · rw [dite_eq_left hj0]
        show 0 < 2 ^ k
        exact Nat.two_pow_pos _
      · rw [dite_eq_right hj0]
        rw [_root_.UInt64.toNat_shiftRight]
        have h_ofNat : (UInt64.ofNat (64 - k)).toNat = 64 - k := by
          show (64 - k) % 2 ^ 64 = 64 - k
          exact Nat.mod_eq_of_lt (by omega)
        rw [h_ofNat]
        have hsubmod : (64 - k) % 64 = 64 - k := Nat.mod_eq_of_lt (by omega)
        rw [hsubmod, Nat.shiftRight_eq_div_pow]
        have hxlt : (a[lo + j - 1]'(by omega)).toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
        have h_pow_eq : 2 ^ (64 - k) * 2 ^ k = 2 ^ 64 := by
          rw [← Nat.pow_add]; congr 1; omega
        apply Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _) |>.mpr
        rw [Nat.mul_comm, h_pow_eq]; exact hxlt
    -- A-mod identity:
    -- A_succ * 2^k mod 2^(64*(j+1)) = (A * 2^k mod 2^(64*j)) + u_j_shifted * 2^(64*j).
    have h_A_mod_eq :
        toNatLimbsList ((a.toList.drop lo).take (j + 1)) * 2 ^ k % 2 ^ (64 * (j + 1))
          = toNatLimbsList ((a.toList.drop lo).take j) * 2 ^ k % 2 ^ (64 * j)
            + u_j_shifted.toNat * 2 ^ (64 * j) := by
      rw [h_A_split]
      -- Let A := A_j, T := A * 2^k / 2^(64j) (= u_carry.toNat), Y := A * 2^k mod 2^(64j).
      set A := toNatLimbsList ((a.toList.drop lo).take j) with hA_def
      set Y := A * 2 ^ k % 2 ^ (64 * j) with hY_def
      set T := A * 2 ^ k / 2 ^ (64 * j) with hT_def
      have h_div_mod : A * 2 ^ k = T * 2 ^ (64 * j) + Y := by
        rw [hT_def, hY_def]; exact (Nat.div_add_mod' _ _).symm
      have h_Y_lt : Y < 2 ^ (64 * j) := by
        rw [hY_def]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have h_T_eq_uc : T = u_carry.toNat := h_T_eq
      -- Compute (A + u_j * 2^(64j)) * 2^k.
      have h_LHS_decomp :
          (A + u_j.toNat * 2 ^ (64 * j)) * 2 ^ k
            = Y + (T + u_j.toNat * 2 ^ k) * 2 ^ (64 * j) := by
        have : (A + u_j.toNat * 2 ^ (64 * j)) * 2 ^ k
              = A * 2 ^ k + u_j.toNat * 2 ^ (64 * j) * 2 ^ k := by ring
        rw [this, h_div_mod]; ring
      rw [h_LHS_decomp]
      -- Now compute (T + u_j.toNat * 2^k). Show it ≡ u_j_shifted.toNat (mod 2^64).
      -- Specifically: T + u_j.toNat * 2^k = u_j_shifted.toNat + top * 2^64.
      rcases h_uc_lt with ⟨hk_pos, h_uc_strict⟩ | hk_zero
      · -- k ≥ 1 case
        have h_T_lt : T < 2 ^ k := by rw [h_T_eq_uc]; exact h_uc_strict
        -- Apply limb_shift_step.
        have h_uc_lt_pow : u_carry.toNat < 2 ^ k := h_uc_strict
        obtain ⟨h_limb, _⟩ := limb_shift_step u_j u_carry k hk_pos hk h_uc_lt_pow
        -- h_limb : u_j_shifted.toNat + (u_j >>> ofNat (64-k)).toNat * 2^64
        --        = u_j.toNat * 2^k + u_carry.toNat
        change u_j_shifted.toNat + _ * 2 ^ 64 = u_j.toNat * 2 ^ k + u_carry.toNat at h_limb
        set top := (u_j >>> UInt64.ofNat (64 - k)).toNat with htop_def
        have h_limb_eq : T + u_j.toNat * 2 ^ k = u_j_shifted.toNat + top * 2 ^ 64 := by
          rw [h_T_eq_uc]; rw [show u_carry.toNat + u_j.toNat * 2 ^ k
                                  = u_j.toNat * 2 ^ k + u_carry.toNat from by ring]
          omega
        -- Y + (T + u_j * 2^k) * 2^(64j) = Y + (u_j_shifted + top * 2^64) * 2^(64j)
        --                              = Y + u_j_shifted * 2^(64j) + top * 2^(64(j+1))
        have h_pow_split : (2 : Nat) ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by
          rw [show 64 * (j + 1) = 64 * j + 64 from by ring, Nat.pow_add]
        rw [h_limb_eq]
        rw [show Y + (u_j_shifted.toNat + top * 2 ^ 64) * 2 ^ (64 * j)
              = Y + u_j_shifted.toNat * 2 ^ (64 * j) + top * (2 ^ (64 * j) * 2 ^ 64) from by ring]
        rw [← h_pow_split]
        -- Y + u_j_shifted.toNat * 2^(64j) < 2^(64(j+1)).
        have h_us_lt : u_j_shifted.toNat < 2 ^ 64 := UInt64.toNat_lt _
        have h_us_64j_lt : u_j_shifted.toNat * 2 ^ (64 * j) ≤ (2 ^ 64 - 1) * 2 ^ (64 * j) := by
          apply Nat.mul_le_mul_right
          omega
        have h_sum_lt : Y + u_j_shifted.toNat * 2 ^ (64 * j) < 2 ^ (64 * (j + 1)) := by
          rw [h_pow_split]
          have h_pos : 0 < 2 ^ (64 * j) := Nat.two_pow_pos _
          have : (2 ^ 64 - 1) * 2 ^ (64 * j) + 2 ^ (64 * j) = 2 ^ 64 * 2 ^ (64 * j) := by
            rw [Nat.sub_mul, Nat.one_mul]
            omega
          have h_us_64j : u_j_shifted.toNat * 2 ^ (64 * j) ≤ 2 ^ 64 * 2 ^ (64 * j) - 2 ^ (64 * j) := by
            have := h_us_64j_lt
            rw [Nat.sub_mul, Nat.one_mul] at this
            exact this
          rw [Nat.mul_comm (2 ^ (64 * j)) (2 ^ 64)]
          omega
        rw [Nat.add_mul_mod_self_right]
        rw [Nat.mod_eq_of_lt h_sum_lt]
      · -- k = 0 case
        subst hk_zero
        -- u_carry = 0, u_j_shifted = u_j.
        have h_uc_zero : u_carry.toNat = 0 := by
          rw [hu_carry_def]; simp
        have h_us_eq : u_j_shifted = u_j := by
          rw [hu_j_shifted_def]
          have h_uc_zero' : u_carry = 0 := by
            apply UInt64.eq_of_toNat_eq
            rw [h_uc_zero]; rfl
          rw [h_uc_zero']
          rw [show (UInt64.ofNat 0 : UInt64) = (0 : UInt64) from rfl]
          rw [_root_.UInt64.shiftLeft_zero]
          rw [_root_.UInt64.or_zero]
        rw [h_us_eq]
        -- T = u_carry.toNat = 0.
        have h_T_zero : T = 0 := by rw [h_T_eq_uc, h_uc_zero]
        rw [h_T_zero]
        rw [show ((0 : Nat) + u_j.toNat * 2 ^ 0) = u_j.toNat from by simp]
        rw [show 2 ^ 0 = 1 from rfl, Nat.mul_one] at h_div_mod
        -- Goal: (A + u_j.toNat * 2^(64j)) % 2^(64(j+1)) = Y + u_j.toNat * 2^(64j)
        -- where Y = A % 2^(64j) = A (since A < 2^(64j))
        -- and u_j.toNat * 2^(64j) ≤ ... < 2^(64(j+1))
        have h_Y_eq_A : Y = A := by
          rw [hY_def, show 2 ^ 0 = 1 from rfl, Nat.mul_one]
          exact Nat.mod_eq_of_lt h_A_lt
        rw [h_Y_eq_A]
        have h_pow_split : (2 : Nat) ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by
          rw [show 64 * (j + 1) = 64 * j + 64 from by ring, Nat.pow_add]
        have h_uj_lt : u_j.toNat < 2 ^ 64 := UInt64.toNat_lt _
        have h_sum_lt : A + u_j.toNat * 2 ^ (64 * j) < 2 ^ (64 * (j + 1)) := by
          rw [h_pow_split]
          have h_uj_64j : u_j.toNat * 2 ^ (64 * j) ≤ (2 ^ 64 - 1) * 2 ^ (64 * j) := by
            apply Nat.mul_le_mul_right; omega
          have h_eq : (2 ^ 64 - 1) * 2 ^ (64 * j) + 2 ^ (64 * j) = 2 ^ 64 * 2 ^ (64 * j) := by
            rw [Nat.sub_mul, Nat.one_mul]
            have h_pos : 0 < 2 ^ (64 * j) := Nat.two_pow_pos _
            have h_pow_pos : 2 ^ (64 * j) ≤ 2 ^ 64 * 2 ^ (64 * j) := by
              conv_lhs => rw [show (2 : Nat) ^ (64 * j) = 1 * 2 ^ (64 * j) from
                                (Nat.one_mul _).symm]
              exact Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr (by positivity))
            omega
          rw [Nat.mul_comm (2 ^ (64 * j)) (2 ^ 64)]
          omega
        exact Nat.mod_eq_of_lt h_sum_lt
    -- Combine.
    rw [h_Q_split]
    rw [h_A_mod_eq]
    rw [h_a'_drop_take] at h_ih_eq
    -- Goal: r * 2^(64(j+1)) + (A_j * 2^k mod 2^(64j)) + u_j_shifted * 2^(64j)
    --     = (Q_j + qr.1 * 2^(64j)) * d' + final.2
    have h_pow : (2 : Nat) ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by
      rw [show 64 * (j + 1) = 64 * j + 64 from by ring, Nat.pow_add]
    rw [h_pow]
    -- Substitutions.
    set Y : Nat := toNatLimbsList ((a.toList.drop lo).take j) * 2 ^ k % 2 ^ (64 * j) with hY_def
    set Q : Nat := toNatLimbsList ((final.1.toList.drop lo).take j) with hQ_def
    -- h_ih_eq : qr.2.toNat * 2^(64j) + Y = Q * d'.toNat + final.2.toNat
    -- h_div_eq : qr.1.toNat * d'.toNat + qr.2.toNat = r.toNat * 2^64 + u_j_shifted.toNat
    have h_div_scaled : (qr.1.toNat * d'.toNat + qr.2.toNat) * 2 ^ (64 * j)
                      = (r.toNat * 2 ^ 64 + u_j_shifted.toNat) * 2 ^ (64 * j) := by
      rw [h_div_eq]
    linear_combination h_ih_eq - h_div_scaled

/-- Correctness of `divModLimb`: the slice `[lo, hi)` divided by `d` produces a
    quotient slice (overwriting the original) plus a single-limb remainder. -/
theorem divModLimb_toNat (a : Array UInt64) (lo hi : Nat) (d : UInt64) (hd : d ≠ 0)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    let (a', r) := divModLimb a lo hi d hd hlo hhi
    toNatLimbsList ((a.toList.drop lo).take (hi - lo))
      = toNatLimbsList ((a'.toList.drop lo).take (hi - lo)) * d.toNat + r.toNat
    ∧ r.toNat < d.toNat := by
  unfold divModLimb
  simp only []
  set k := UInt64.leadingZeros d with hk_eq
  set kU : UInt64 := UInt64.ofNat k with hkU_def
  set d' := d <<< kU with hd'_def
  have hk_le : k ≤ 63 := UInt64.leadingZeros_le d hd
  have hd'_norm : 2 ^ 63 ≤ d'.toNat :=
    UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros d hd
  set inv := UInt64.reciprocal d' hd'_norm with hinv_def
  set len := hi - lo with hlen_def
  -- Initial r0.
  set r0 : UInt64 :=
    if k = 0 then 0
    else if hlen0 : len = 0 then 0
    else
      have h_top : hi - 1 < a.size := by omega
      a[hi - 1]'h_top >>> UInt64.ofNat (64 - k) with hr0_def
  -- Result of go.
  set res := divModLimb.go d' inv k hk_le a lo len r0 (by omega) with hres_def
  -- d'.toNat bound for d.toNat.
  have hd'_lt : d'.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have hd_pos : 0 < d.toNat := by
    have h := UInt64.toNat_lt d
    by_contra h_le
    push Not at h_le
    have h_zero : d.toNat = 0 := by omega
    have : d = 0 := UInt64.eq_of_toNat_eq h_zero
    exact hd this
  have hd'_pos : 0 < d'.toNat := by omega
  -- d' = d * 2^k (in Nat).
  have h_d'_eq : d'.toNat = d.toNat * 2 ^ k := by
    rw [hd'_def]
    rw [_root_.UInt64.toNat_shiftLeft]
    rw [hkU_def]
    have h_ofNat : (UInt64.ofNat k).toNat = k := by
      show k % 2 ^ 64 = k
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_ofNat]
    have h_k_mod : k % 64 = k := Nat.mod_eq_of_lt (by omega)
    rw [h_k_mod, Nat.shiftLeft_eq]
    have h_prod_lt : d.toNat * 2 ^ k < 2 ^ 64 := by
      have hd_lt : d.toNat < 2 ^ 64 := UInt64.toNat_lt _
      -- d * 2^k ≤ 2^63 * 2^k ≤ 2^64? Hmm, that requires d ≤ 2^(63-k+1)... wait we
      -- actually have 2^63 ≤ d * 2^k from the normalization, which gives d ≥ 2^(63-k).
      -- Let's just use that d'.toNat < 2^64.
      have h_d'_eq_calc : (d <<< (UInt64.ofNat k : UInt64)).toNat = d.toNat * 2 ^ k % 2 ^ 64 := by
        rw [_root_.UInt64.toNat_shiftLeft, h_ofNat, h_k_mod, Nat.shiftLeft_eq]
      have hd'_lt' := hd'_lt
      rw [hd'_def, hkU_def] at hd'_lt'
      rw [h_d'_eq_calc] at hd'_lt'
      -- We have d * 2^k mod 2^64 < 2^64 and 2^63 ≤ d'.toNat.
      have h_lower : 2 ^ 63 ≤ d.toNat * 2 ^ k % 2 ^ 64 := by
        have := hd'_norm
        rw [hd'_def, hkU_def] at this
        rw [h_d'_eq_calc] at this
        exact this
      -- We claim d * 2^k < 2^64. Use uniqueness of mod.
      by_contra h_ge
      push Not at h_ge
      -- d * 2^k ≥ 2^64.
      have h_div_pos : 0 < d.toNat * 2 ^ k / 2 ^ 64 := by
        rw [Nat.lt_iff_add_one_le]
        rw [show 0 + 1 = 1 from rfl]
        apply Nat.one_le_div_iff (Nat.two_pow_pos _) |>.mpr
        exact h_ge
      -- d.toNat * 2^k / 2^64 ≥ 1, and remainder is in [2^63, 2^64).
      -- But also d.toNat * 2^k = (d.toNat * 2^k / 2^64) * 2^64 + (d.toNat * 2^k mod 2^64)
      -- So d.toNat * 2^k ≥ 2^64 + 2^63.
      have h_dec : d.toNat * 2 ^ k = (d.toNat * 2^k / 2^64) * 2^64 + (d.toNat * 2^k % 2^64) :=
        (Nat.div_add_mod' _ _).symm
      -- We need d.toNat * 2^k < 2^64. But we don't know that yet!
      -- Actually we DO: d.toNat < 2^64, and 2^k ≤ 2^63, so d.toNat * 2^k ≤ (2^64 - 1) * 2^63
      -- which can still be huge. Hmm.
      -- Wait, the normalization is the OTHER way: d * 2^(leadingZeros) is in [2^63, 2^64).
      -- So d * 2^k < 2^64 BY ASSUMPTION (the normalization theorem two_pow_63_le_toNat_shiftLeft_leadingZeros).
      -- Indeed, d <<< k.toNat = d.toNat * 2^k mod 2^64 IF d.toNat * 2^k < 2^64.
      -- The assumption gives d.toNat * 2^k mod 2^64 ≥ 2^63 — which only forces non-zero, not bound.
      -- So we need the full d.toNat * 2^k < 2^64 from elsewhere.
      -- Actually, UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros uses k = leadingZeros d,
      -- which by definition gives d.toNat * 2^k < 2^64. Look at proof.
      -- Let me extract this fact.
      have hk_def : k = if d = 0 then 64 else 63 - d.toNat.log2 := rfl
      have hk_eq' : k = 63 - d.toNat.log2 := by rw [hk_def]; rw [ite_eq_right hd]
      have hL_lt_64 : d.toNat.log2 < 64 := (Nat.log2_lt (by omega)).mpr (UInt64.toNat_lt _)
      have hL_le_63 : d.toNat.log2 ≤ 63 := by omega
      have hpow_hi : d.toNat < 2 ^ (d.toNat.log2 + 1) :=
        (Nat.log2_lt (by omega)).mp (Nat.lt_succ_of_le (Nat.le_refl _))
      have h_prod_lt' : d.toNat * 2 ^ k < 2 ^ 64 := by
        calc d.toNat * 2 ^ k
            < 2 ^ (d.toNat.log2 + 1) * 2 ^ k :=
              (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hpow_hi
          _ = 2 ^ (d.toNat.log2 + 1 + k) := (Nat.pow_add 2 (d.toNat.log2 + 1) k).symm
          _ = 2 ^ 64 := by congr 1; rw [hk_eq']; omega
      omega
    rw [Nat.mod_eq_of_lt h_prod_lt]
  -- Apply the inner correctness.
  have h_lo_len : lo + len ≤ a.size := by rw [hlen_def]; omega
  have h_r0_lt : r0.toNat < d'.toNat := by
    rw [hr0_def]
    by_cases hk0 : k = 0
    · simp only [hk0, ↓reduceIte]
      show 0 < d'.toNat
      exact hd'_pos
    · simp only [hk0, ↓reduceIte]
      by_cases hlen0 : len = 0
      · simp only [hlen0, ↓reduceDIte]
        show 0 < d'.toNat
        exact hd'_pos
      · simp only [hlen0, ↓reduceDIte]
        rw [_root_.UInt64.toNat_shiftRight]
        have h_ofNat : (UInt64.ofNat (64 - k)).toNat = 64 - k := by
          show (64 - k) % 2 ^ 64 = 64 - k
          exact Nat.mod_eq_of_lt (by omega)
        rw [h_ofNat]
        have hsubmod : (64 - k) % 64 = 64 - k := Nat.mod_eq_of_lt (by omega)
        rw [hsubmod, Nat.shiftRight_eq_div_pow]
        -- a[hi-1].toNat / 2^(64-k) < 2^k ≤ 2^63 ≤ d'.toNat.
        have hxlt : (a[hi - 1]'(by omega)).toNat < 2 ^ 64 :=
          _root_.UInt64.toNat_lt _
        have h_quo_lt : (a[hi - 1]'(by omega)).toNat / 2 ^ (64 - k) < 2 ^ k := by
          apply Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _) |>.mpr
          rw [Nat.mul_comm, ← Nat.pow_add, show 64 - k + k = 64 from by omega]
          exact hxlt
        have h_pow_le : 2 ^ k ≤ 2 ^ 63 :=
          Nat.pow_le_pow_right (by decide) (by omega)
        omega
  have h_inner := divModLimb.go_correct d' inv k hk_le a lo len r0 (by omega) hd'_norm
                    (by rw [hinv_def]) h_r0_lt
  rw [← hres_def] at h_inner
  obtain ⟨h_inner_eq, h_inner_r_lt⟩ := h_inner
  -- We've established:
  --   r0 * 2^(64*len) + (A * 2^k mod 2^(64*len)) = Q * d'.toNat + res.2.toNat
  --   res.2.toNat < d'.toNat
  -- Need to show:
  --   A = Q * d.toNat + (res.2 >>> kU).toNat   (the actual quotient and remainder)
  -- where A = toNatLimbsList ((a.toList.drop lo).take len).
  -- Step 1: r0 = a[hi-1] >> (64-k) = A * 2^k / 2^(64*len) (when len ≥ 1, k ≥ 1).
  --   When k = 0: r0 = 0 and A < 2^(64*len) so A * 2^0 / 2^(64*len) = 0. ✓
  --   When len = 0: A = 0 and r0 = 0. ✓
  -- Step 2: A * 2^k = r0 * 2^(64*len) + (A * 2^k mod 2^(64*len))
  -- Step 3: A * 2^k = Q * d' + res.2.toNat = Q * d.toNat * 2^k + res.2.toNat
  -- Step 4: A * 2^k ≡ res.2.toNat (mod 2^k), and res.2.toNat = (res.2 / 2^k) * 2^k + res.2 mod 2^k
  --                                                          = (res.2 >> k) * 2^k + (res.2 mod 2^k)
  --   But res.2 < d' = d * 2^k, so res.2 = q' * d + r' (Nat-divide), and "res.2 mod d = res.2 mod (d*2^k) ?" Hmm.
  -- Better: A * 2^k mod (2^k) = 0. So res.2.toNat mod 2^k = 0 (mod the algebraic identity).
  -- Hence res.2.toNat is divisible by 2^k, and res.2.toNat / 2^k = (res.2 >>> k).toNat.
  -- And A = Q * d + (res.2.toNat / 2^k) = Q * d + (res.2 >>> k).toNat.
  have h_r0_eq : r0.toNat = toNatLimbsList ((a.toList.drop lo).take len) * 2 ^ k / 2 ^ (64 * len) := by
    rw [hr0_def]
    by_cases hk0 : k = 0
    · rw [ite_eq_left hk0]
      show (0 : Nat) = _ * 2 ^ k / _
      rw [hk0, show (2 : Nat) ^ 0 = 1 from rfl, Nat.mul_one]
      have h_A_lt : toNatLimbsList ((a.toList.drop lo).take len) < 2 ^ (64 * len) := by
        have hL := toNatLimbsList_lt_pow ((a.toList.drop lo).take len)
        have h_take_len : ((a.toList.drop lo).take len).length ≤ len :=
          List.length_take_le _ _
        calc toNatLimbsList ((a.toList.drop lo).take len)
              < 2 ^ (64 * ((a.toList.drop lo).take len).length) := hL
            _ ≤ 2 ^ (64 * len) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.div_eq_of_lt h_A_lt]
    · rw [ite_eq_right hk0]
      by_cases hlen0 : len = 0
      · rw [dite_eq_left hlen0]
        show (0 : Nat) = _
        rw [hlen0]
        simp [toNatLimbsList]
      · rw [dite_eq_right hlen0]
        dsimp only
        have h_top_idx : lo + (len - 1) < a.size := by rw [hlen_def]; omega
        have h_idx_alt : hi - 1 < a.size := by omega
        have h_eq_arr : a[hi - 1]'h_idx_alt = a[lo + (len - 1)]'h_top_idx := by
          congr 1
          omega
        rw [h_eq_arr]
        have h_top := top_bits_eq_u_carry a lo len k hk_le (by rw [hlen_def]; omega)
        rw [ite_eq_right hk0, dite_eq_right hlen0] at h_top
        have h_arr_eq : a[lo + (len - 1)]'h_top_idx = a[lo + len - 1]'(by omega) := by
          congr 1; omega
        rw [h_arr_eq, ← h_top]
  -- Now derive: A * 2^k = res_Q * d'.toNat + res.2.toNat where res_Q = toNatLimbsList ...
  set A := toNatLimbsList ((a.toList.drop lo).take len) with hA_def
  set Q_inner := toNatLimbsList ((res.1.toList.drop lo).take len) with hQ_def
  have h_A_div : A * 2 ^ k = Q_inner * d'.toNat + res.2.toNat := by
    have h_A_lt : A < 2 ^ (64 * len) := by
      rw [hA_def]
      have hL := toNatLimbsList_lt_pow ((a.toList.drop lo).take len)
      have h_take_len : ((a.toList.drop lo).take len).length ≤ len :=
        List.length_take_le _ _
      calc toNatLimbsList ((a.toList.drop lo).take len)
            < 2 ^ (64 * ((a.toList.drop lo).take len).length) := hL
          _ ≤ 2 ^ (64 * len) := Nat.pow_le_pow_right (by decide) (by omega)
    -- A * 2^k = (A * 2^k / 2^(64*len)) * 2^(64*len) + (A * 2^k mod 2^(64*len))
    --        = r0.toNat * 2^(64*len) + (A * 2^k mod 2^(64*len))
    have h_dm : A * 2 ^ k = (A * 2^k / 2 ^ (64*len)) * 2 ^ (64*len) + (A * 2^k % 2 ^ (64*len)) :=
      (Nat.div_add_mod' _ _).symm
    rw [← h_r0_eq] at h_dm
    rw [h_dm]
    -- h_inner_eq: r0.toNat * 2^(64*len) + (A * 2^k mod 2^(64*len)) = Q * d' + res.2
    rw [h_inner_eq]
  -- Step 4: res.2.toNat = (res.2 / 2^k) * 2^k = (res.2 >>> kU).toNat * 2^k.
  -- Since res.2.toNat < d'.toNat = d.toNat * 2^k, res.2.toNat / 2^k = (res.2 >>> k).toNat < d.toNat.
  -- And A * 2^k = Q * d * 2^k + res.2.toNat. Mod 2^k: 0 = res.2.toNat mod 2^k. So 2^k ∣ res.2.toNat.
  -- Step 5: A = Q * d + res.2.toNat / 2^k = Q * d + (res.2 >>> kU).toNat.
  have h_pow_k_le : (2 : Nat) ^ k ≤ 2 ^ 63 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h_2k_div_res2 : 2 ^ k ∣ res.2.toNat := by
    -- A * 2^k = Q * d' + res.2 = Q * d * 2^k + res.2. So res.2 = (A - Q * d) * 2^k. Hence 2^k | res.2.
    -- Formally:
    have h := h_A_div
    rw [h_d'_eq] at h
    -- A * 2^k = Q_inner * (d.toNat * 2^k) + res.2.toNat
    -- ⟹ res.2.toNat = A * 2^k - Q_inner * d.toNat * 2^k = (A - Q_inner * d.toNat) * 2^k
    -- ... but we need A ≥ Q_inner * d.toNat. Use Nat.dvd_sub:
    have h_div : 2 ^ k ∣ A * 2 ^ k - Q_inner * (d.toNat * 2 ^ k) := by
      apply Nat.dvd_sub
      · exact Dvd.intro_left _ rfl
      · rw [show Q_inner * (d.toNat * 2 ^ k) = (Q_inner * d.toNat) * 2 ^ k from by ring]
        exact Dvd.intro_left _ rfl
    have h_eq : res.2.toNat = A * 2 ^ k - Q_inner * (d.toNat * 2 ^ k) := by omega
    rw [h_eq]; exact h_div
  have h_res2_eq : res.2.toNat = (res.2 >>> kU).toNat * 2 ^ k := by
    rw [_root_.UInt64.toNat_shiftRight]
    have h_kU : kU.toNat = k := by
      rw [hkU_def]
      show k % 2 ^ 64 = k
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_kU]
    have h_kmod : k % 64 = k := Nat.mod_eq_of_lt (by omega)
    rw [h_kmod, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_mul_cancel h_2k_div_res2]
  have h_res2_lt_d : (res.2 >>> kU).toNat < d.toNat := by
    have h_lt := h_inner_r_lt
    rw [h_d'_eq] at h_lt
    rw [h_res2_eq] at h_lt
    exact (Nat.lt_of_mul_lt_mul_right h_lt :)
  -- Step 6: A = Q * d + (res.2 >>> kU).toNat.
  -- A * 2^k = Q * d * 2^k + (res.2 >>> kU).toNat * 2^k. Divide both sides by 2^k.
  have h_main : A = Q_inner * d.toNat + (res.2 >>> kU).toNat := by
    have h := h_A_div
    rw [h_d'_eq, h_res2_eq] at h
    have h_eq2 : A * 2 ^ k = (Q_inner * d.toNat + (res.2 >>> kU).toNat) * 2 ^ k := by
      rw [Nat.add_mul]; rw [show Q_inner * d.toNat * 2^k = Q_inner * (d.toNat * 2^k) from by ring]
      exact h
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos _
    exact Nat.eq_of_mul_eq_mul_right hpos h_eq2
  refine ⟨?_, h_res2_lt_d⟩
  -- Need: A = Q_inner * d.toNat + (res.2 >>> kU).toNat (matches goal up to renaming).
  exact h_main

/-- Correctness of `AzNat.divModUInt64`: returns the quotient and remainder of
    `U / d` for nonzero `d`. -/
theorem toNat_divModUInt64 (U : AzNat) (d : UInt64) (hd : d ≠ 0) :
    let (Q, r) := divModUInt64 U d hd
    Q.toNat * d.toNat + r.toNat = U.toNat ∧ r.toNat < d.toNat := by
  have hd_pos : 0 < d.toNat := by
    by_contra h
    push Not at h
    have : d.toNat = 0 := by omega
    exact hd (UInt64.eq_of_toNat_eq this)
  show (divModUInt64 U d hd).1.toNat * d.toNat + (divModUInt64 U d hd).2.toNat = U.toNat
       ∧ (divModUInt64 U d hd).2.toNat < d.toNat
  unfold divModUInt64
  by_cases h0 : U.limbs.size = 0
  · simp only [h0, ↓reduceDIte]
    have h_nil : U.limbs.toList = [] := by
      have : U.limbs.toList.length = 0 := h0
      exact List.length_eq_zero_iff.mp this
    have h_zero : U.toNat = 0 := by show toNatLimbsList _ = 0; rw [h_nil]; rfl
    refine ⟨?_, hd_pos⟩
    show (0 : AzNat).toNat * d.toNat + (0 : UInt64).toNat = U.toNat
    rw [h_zero]
    show toNat 0 * d.toNat + UInt64.toNat 0 = 0
    have h_az : toNat (0 : AzNat) = 0 := rfl
    have h_u : UInt64.toNat 0 = 0 := rfl
    rw [h_az, h_u]; ring
  · simp only [h0, ↓reduceDIte]
    by_cases h1 : U.limbs.size = 1
    · simp only [h1, ↓reduceDIte]
      have h_pos : 0 < U.limbs.size := by rw [h1]; decide
      set qr := UInt64.divMod (U.limbs[0]'h_pos) d with hqr_def
      refine ⟨?_, ?_⟩
      · show (ofLimbs #[qr.1]).toNat * d.toNat + qr.2.toNat = U.toNat
        rw [toNat_ofLimbs]
        have h_arr : (#[qr.1] : Array UInt64).toList = [qr.1] := rfl
        rw [h_arr]
        have h_single : toNatLimbsList [qr.1] = qr.1.toNat := by
          rw [show ([qr.1] : List UInt64) = qr.1 :: [] from rfl, toNatLimbsList_cons]
          simp [toNatLimbsList]
        rw [h_single]
        have h_div_fst : qr.1.toNat = (U.limbs[0]'h_pos).toNat / d.toNat := by
          rw [hqr_def]; exact UInt64.toNat_divMod_fst _ _
        have h_div_snd : qr.2.toNat = (U.limbs[0]'h_pos).toNat % d.toNat := by
          rw [hqr_def]; exact UInt64.toNat_divMod_snd _ _
        rw [h_div_fst, h_div_snd]
        have h_U_eq : U.toNat = (U.limbs[0]'h_pos).toNat := by
          show toNatLimbsList U.limbs.toList = _
          have h_len : U.limbs.toList.length = 1 := h1
          match hL : U.limbs.toList with
          | [] => rw [hL] at h_len; simp at h_len
          | [x] =>
            rw [show toNatLimbsList [x] = x.toNat from by simp [toNatLimbsList]]
            have h_get : (U.limbs[0]'h_pos) = x := by
              have h_eq_get : U.limbs[0]'h_pos
                  = U.limbs.toList[0]'(by rw [Array.length_toList]; exact h_pos) :=
                (Array.getElem_toList h_pos).symm
              rw [h_eq_get]
              simp [hL]
            rw [h_get]
          | x :: y :: ys => rw [hL] at h_len; simp at h_len
        rw [h_U_eq]
        exact (Nat.div_add_mod' _ _)
      · show qr.2.toNat < d.toNat
        rw [hqr_def, UInt64.toNat_divMod_snd]
        exact Nat.mod_lt _ hd_pos
    · simp only [h1, ↓reduceDIte]
      set res := divModLimb U.limbs 0 U.limbs.size d hd
                  (Nat.zero_le _) (Nat.le_refl _) with hres_def
      refine ⟨?_, ?_⟩
      · show (ofLimbs res.1).toNat * d.toNat + res.2.toNat = U.toNat
        rw [toNat_ofLimbs]
        have h_main := divModLimb_toNat U.limbs 0 U.limbs.size d hd
                        (Nat.zero_le _) (Nat.le_refl _)
        simp only [List.drop_zero, Nat.sub_zero] at h_main
        have h_take_full : U.limbs.toList.take U.limbs.size = U.limbs.toList := by
          rw [List.take_of_length_le]; rw [Array.length_toList]
        rw [h_take_full] at h_main
        obtain ⟨h_eq, _⟩ := h_main
        have h_size_res : res.1.size = U.limbs.size := by
          rw [hres_def]
          unfold divModLimb
          simp only []
          exact divModLimb.go_size _ _ _ _ _ _ _ _ _
        have h_take_full_res : res.1.toList.take U.limbs.size = res.1.toList := by
          rw [List.take_of_length_le]; rw [Array.length_toList, h_size_res]
        rw [h_take_full_res] at h_eq
        show toNatLimbsList res.1.toList * d.toNat + res.2.toNat = U.toNat
        rw [show U.toNat = toNatLimbsList U.limbs.toList from rfl]
        exact h_eq.symm
      · show res.2.toNat < d.toNat
        have h_main := divModLimb_toNat U.limbs 0 U.limbs.size d hd
                        (Nat.zero_le _) (Nat.le_refl _)
        exact h_main.2

end Azurite.AzNat
