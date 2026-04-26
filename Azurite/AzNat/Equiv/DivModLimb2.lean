import Azurite.AzNat.Equiv.DivModLimb
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


end Azurite.AzNat
