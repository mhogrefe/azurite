import Azurite.AzNat.Equiv.LimbDigitsPow2
import Azurite.AzNat.OfLimbDigitsPow2
import Mathlib.Data.Nat.Bitwise

namespace Azurite.AzNat

/-! ### Helper: `testBit` of `Nat.ofDigits (2 ^ k)` for bounded digits

If every digit is `< 2 ^ k` and `k ≥ 1`, then the bits of `Nat.ofDigits (2^k) L`
are partitioned across the digits: bit `b` lives in digit `b / k` at within-digit
position `b % k`. -/

private theorem testBit_ofDigits_pow2 (k : Nat) (hk : 1 ≤ k) :
    ∀ (L : List Nat) (_ : ∀ x ∈ L, x < 2 ^ k) (b : Nat),
      (Nat.ofDigits (2 ^ k : Nat) L).testBit b =
        ((L[b / k]?).getD 0).testBit (b % k) := by
  intro L
  induction L with
  | nil =>
    intro _ b
    rw [Nat.ofDigits_nil]
    simp [Nat.zero_testBit]
  | cons d L ih =>
    intro hL b
    have h_d_lt : d < 2 ^ k := hL d (List.mem_cons_self)
    have h_L_lt : ∀ x ∈ L, x < 2 ^ k := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    rw [Nat.ofDigits_cons]
    show ((d : Nat) + 2 ^ k * Nat.ofDigits (2 ^ k : Nat) L).testBit b = _
    rw [show (d : Nat) + 2 ^ k * Nat.ofDigits (2 ^ k : Nat) L
          = 2 ^ k * Nat.ofDigits (2 ^ k : Nat) L + d from by ring]
    rw [Nat.testBit_two_pow_mul_add _ h_d_lt]
    by_cases hb : b < k
    · rw [if_pos hb]
      have h_div : b / k = 0 := Nat.div_eq_of_lt hb
      have h_mod : b % k = b := Nat.mod_eq_of_lt hb
      rw [h_div, h_mod]
      simp
    · rw [if_neg hb]
      push Not at hb
      rw [ih h_L_lt (b - k)]
      have h_div : b / k = (b - k) / k + 1 := by
        have h := Nat.add_div_right (b - k) (by omega : 0 < k)
        rw [Nat.sub_add_cancel hb] at h
        exact h
      have h_mod : b % k = (b - k) % k := by
        have h := Nat.add_mod_right (b - k) k
        rw [Nat.sub_add_cancel hb] at h
        exact h
      rw [h_div, h_mod]
      simp

/-! ### Helper: `testBit` of `(ofLimbs limbs).toNat` via the limb decomposition

The bits of an `AzNat`'s `toNat` are partitioned across its limbs: bit `b`
lives in limb `b / 64` at within-limb position `b % 64`. -/

private theorem toNatLimbsList_eq_ofDigits' (l : List UInt64) :
    toNatLimbsList l = Nat.ofDigits (2 ^ 64 : Nat) (l.map UInt64.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [toNatLimbsList_cons, ih, List.map_cons, Nat.ofDigits_cons]
    push_cast; ring

private theorem testBit_toNat_ofLimbs (limbs : Array UInt64) (b : Nat) :
    (AzNat.ofLimbs limbs).toNat.testBit b =
      ((limbs.toList[b / 64]?).getD 0).toNat.testBit (b % 64) := by
  rw [toNat_ofLimbs, toNatLimbsList_eq_ofDigits']
  have h_bound : ∀ x ∈ limbs.toList.map UInt64.toNat, x < 2 ^ 64 := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨u, _, hu⟩ := hx
    rw [← hu]; exact UInt64.toNat_lt u
  rw [testBit_ofDigits_pow2 64 (by omega) _ h_bound b]
  by_cases h : b / 64 < limbs.toList.length
  · have h_map : b / 64 < (limbs.toList.map UInt64.toNat).length := by
      rw [List.length_map]; exact h
    rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem h_map, List.getElem_map]
    simp
  · push Not at h
    have h_map : (limbs.toList.map UInt64.toNat).length ≤ b / 64 := by
      rw [List.length_map]; exact h
    rw [List.getElem?_eq_none h, List.getElem?_eq_none h_map]
    simp [Nat.zero_testBit]

/-! ### `k = 64` branch: digits are limbs directly -/

private theorem toNat_ofLimbDigitsPow2_of_64 (digits : Array UInt64) :
    (AzNat.ofLimbDigitsPow2 64 digits).toNat =
      Nat.ofDigits (2 ^ 64 : Nat) (digits.toList.map UInt64.toNat) := by
  unfold AzNat.ofLimbDigitsPow2
  rw [if_pos rfl, toNat_ofLimbs, toNatLimbsList_eq_ofDigits']

/-! ### `k | 64`, `k < 64` branch: OR-fold builds the limb value bit-by-bit

A foldl that ORs left-shifted bounded values gives a Nat whose bits are
partitioned across the digits: bit `r` of the result is bit `r % k` of
the `(r / k)`-th value, when `r / k < n` (the fold's length) and the value
is bounded by `2 ^ k`. -/

private theorem testBit_foldl_lor_shifted_bounded
    (k : Nat) (hk : 1 ≤ k) (hk_lt : k < 64) (hk_div : 64 % k = 0)
    (f : Nat → UInt64) (hf : ∀ j, (f j).toNat < 2 ^ k) :
    ∀ (n : Nat) (r : Nat), n ≤ 64 / k → r < 64 →
    ((List.range n).foldl
        (fun acc j => acc ||| ((f j) <<< UInt64.ofNat (j * k)))
        (0 : UInt64)).toNat.testBit r =
      (decide (r / k < n) && (f (r / k)).toNat.testBit (r % k)) := by
  have h_64_div : (64 / k) * k = 64 := by
    have h := Nat.div_add_mod 64 k
    rw [Nat.mul_comm] at h
    omega
  intro n
  induction n with
  | zero =>
    intro r _ _
    show (0 : UInt64).toNat.testBit r = _
    rw [show ((0 : UInt64).toNat = 0) from rfl, Nat.zero_testBit]
    simp
  | succ n ih =>
    intro r hn hr
    have hn' : n ≤ 64 / k := by omega
    have h_n_lt : n < 64 / k := by omega
    have h_nk_lt : n * k < 64 := by
      have h_n_lt_k : n * k < (64 / k) * k := (Nat.mul_lt_mul_right hk).mpr h_n_lt
      omega
    have h_n1k_le : (n + 1) * k ≤ 64 := by
      have : (n + 1) * k ≤ (64 / k) * k := Nat.mul_le_mul_right k (by omega)
      omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [UInt64.toNat_or, Nat.testBit_or, ih r hn' hr]
    -- Compute testBit r of (f n <<< (n * k))
    rw [UInt64.toNat_shiftLeft]
    have h_shift_amt : (UInt64.ofNat (n * k)).toNat % 64 = n * k := by
      have h_nk_lt_pow : n * k < 2 ^ 64 := by
        have : (64 : Nat) < 2 ^ 64 := by decide
        omega
      show (n * k) % 2 ^ 64 % 64 = n * k
      rw [Nat.mod_eq_of_lt h_nk_lt_pow]
      exact Nat.mod_eq_of_lt h_nk_lt
    rw [h_shift_amt, Nat.shiftLeft_eq]
    have h_prod_lt : (f n).toNat * 2 ^ (n * k) < 2 ^ 64 := by
      have h_fn := hf n
      have h1 : (f n).toNat * 2 ^ (n * k) < 2 ^ k * 2 ^ (n * k) :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h_fn
      have h2 : 2 ^ k * 2 ^ (n * k) = 2 ^ ((n + 1) * k) := by
        rw [← Nat.pow_add]
        congr 1
        ring
      have h3 : 2 ^ ((n + 1) * k) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) h_n1k_le
      omega
    rw [Nat.mod_eq_of_lt h_prod_lt, Nat.testBit_mul_two_pow]
    -- Now combine
    by_cases h_rn : r / k < n
    · -- IH branch contributes; the new term doesn't.
      have h_r_lt_nk : r < n * k := (Nat.div_lt_iff_lt_mul hk).mp h_rn
      have h_term_zero : ((decide (n * k ≤ r) && (f n).toNat.testBit (r - n * k)) = false) := by
        have : ¬ n * k ≤ r := by omega
        simp [this]
      rw [h_term_zero, Bool.or_false]
      have h_lhs : decide (r / k < n) = true := by simp [h_rn]
      have h_rhs : decide (r / k < n + 1) = true := by
        have : r / k < n + 1 := by omega
        simp [this]
      rw [h_lhs, h_rhs]
    · push Not at h_rn
      have h_lhs : decide (r / k < n) = false := by
        have : ¬ r / k < n := by omega
        simp [this]
      rw [h_lhs, Bool.false_and, Bool.false_or]
      by_cases h_eq : r / k = n
      · -- The new term contributes f n at the right position.
        have h_nk_le_r : n * k ≤ r := by
          have : k * (r / k) ≤ r := Nat.mul_div_le r k
          rw [Nat.mul_comm] at this
          rw [← h_eq]; exact this
        have h_r_minus : r - n * k = r % k := by
          have h_dm := Nat.div_add_mod r k
          rw [Nat.mul_comm] at h_dm
          rw [← h_eq]
          omega
        have h_term_true : decide (n * k ≤ r) = true := by simp [h_nk_le_r]
        rw [h_term_true, Bool.true_and, h_r_minus]
        have h_eq' : (f (r / k)).toNat.testBit (r % k) = (f n).toNat.testBit (r % k) := by
          rw [h_eq]
        rw [h_eq']
        have h_rhs : decide (r / k < n + 1) = true := by
          have : r / k < n + 1 := by omega
          simp [this]
        rw [h_rhs, Bool.true_and]
      · -- r/k > n; both sides are false.
        have h_rk_gt : n + 1 ≤ r / k := by omega
        have h_r_ge : n * k + k ≤ r := by
          have h_div_le : (n + 1) * k ≤ (r / k) * k := Nat.mul_le_mul_right k h_rk_gt
          have h_rk_le_r : k * (r / k) ≤ r := Nat.mul_div_le r k
          rw [Nat.mul_comm] at h_rk_le_r
          have h_n1_eq : (n + 1) * k = n * k + k := by ring
          omega
        have h_k_le : k ≤ r - n * k := by omega
        have h_high : (f n).toNat.testBit (r - n * k) = false := by
          apply Nat.testBit_eq_false_of_lt
          have hf_n := hf n
          calc (f n).toNat < 2 ^ k := hf_n
            _ ≤ 2 ^ (r - n * k) := Nat.pow_le_pow_right (by omega) h_k_le
        rw [h_high, Bool.and_false]
        have h_rhs : decide (r / k < n + 1) = false := by
          have : ¬ r / k < n + 1 := by omega
          simp [this]
        rw [h_rhs, Bool.false_and]

/-! ### Map-`toNat` indexing helper -/

private theorem getElem?_map_toNat_getD (digits : Array UInt64) (i : Nat) :
    ((digits.toList.map UInt64.toNat)[i]?).getD 0 =
      ((digits.toList[i]?).getD 0).toNat := by
  by_cases h : i < digits.toList.length
  · have h_map : i < (digits.toList.map UInt64.toNat).length := by
      rw [List.length_map]; exact h
    rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem h_map, List.getElem_map]
    simp
  · push Not at h
    have h_map : (digits.toList.map UInt64.toNat).length ≤ i := by
      rw [List.length_map]; exact h
    rw [List.getElem?_eq_none h, List.getElem?_eq_none h_map]
    simp

/-! ### Adapter: skip-on-OOB foldl ↔ OR-with-zero foldl

Lets us apply `testBit_foldl_lor_shifted_bounded` to the actual definition's
`if h : i < digits.size then ... else acc` step. -/

private theorem foldl_skip_eq_or_zero (k : Nat) (digits : Array UInt64) (q n : Nat) :
    (List.range n).foldl (fun (acc : UInt64) j =>
        if h : q * (64 / k) + j < digits.size then
          acc ||| ((digits[q * (64 / k) + j]'h) <<< UInt64.ofNat (j * k))
        else acc) 0
    =
    (List.range n).foldl (fun (acc : UInt64) j =>
        acc ||| ((if h : q * (64 / k) + j < digits.size then
                    digits[q * (64 / k) + j]'h
                  else (0 : UInt64)) <<< UInt64.ofNat (j * k))) 0 := by
  congr 1
  funext acc j
  by_cases h : q * (64 / k) + j < digits.size
  · simp [h]
  · simp [h, UInt64.zero_shiftLeft, UInt64.or_zero]

/-! ### `k | 64`, `k < 64` branch correctness

For `1 ≤ k < 64` with `k | 64` (so `k ∈ {1, 2, 4, 8, 16, 32}`), the per-limb
construction reconstructs `Nat.ofDigits (2 ^ k)` of the digit array. -/

/-! ### Per-limb bit identity for the `k | 64` branch -/

private theorem testBit_limb_div_64 (k : Nat) (hk : 1 ≤ k) (hk_lt : k < 64)
    (hk_div : 64 % k = 0) (digits : Array UInt64)
    (hd : ∀ x ∈ digits.toList.map UInt64.toNat, x < 2 ^ k)
    (q : Nat) (r : Nat) (hr : r < 64) :
    ((Array.range (64 / k)).foldl (init := (0 : UInt64)) (fun acc j =>
        let i := q * (64 / k) + j
        if h : i < digits.size then
          acc ||| ((digits[i]'h) <<< UInt64.ofNat (j * k))
        else acc)).toNat.testBit r =
      ((digits.toList[q * (64 / k) + r / k]?).getD 0).toNat.testBit (r % k) := by
  set perLimb := 64 / k with h_perLimb_def
  have h_perLimb_pos : 0 < perLimb := Nat.div_pos (by omega) hk
  have h_64_eq : perLimb * k = 64 := by
    rw [h_perLimb_def]
    have h := Nat.div_add_mod 64 k
    rw [Nat.mul_comm] at h
    omega
  -- Convert Array.foldl to List.foldl on List.range
  rw [← Array.foldl_toList, Array.toList_range]
  -- Adapter: rewrite "skip" to "OR with 0"
  rw [foldl_skip_eq_or_zero]
  -- Apply testBit_foldl_lor_shifted_bounded with f j = digit-or-0
  let f : Nat → UInt64 := fun j =>
    if h : q * perLimb + j < digits.size then digits[q * perLimb + j]'h else 0
  have hf_bound : ∀ j, (f j).toNat < 2 ^ k := by
    intro j
    by_cases h : q * perLimb + j < digits.size
    · have : f j = digits[q * perLimb + j]'h := by simp [f, h]
      rw [this]
      apply hd
      rw [List.mem_map]
      exact ⟨digits[q * perLimb + j]'h, List.getElem_mem h, rfl⟩
    · have : f j = (0 : UInt64) := by simp [f, h]
      rw [this]
      show (0 : Nat) < 2 ^ k
      positivity
  -- The current foldl step uses `if h : ... else 0`. Recognize as `f`.
  rw [show (fun (acc : UInt64) j =>
        acc ||| ((if h : q * (64 / k) + j < digits.size then
                    digits[q * (64 / k) + j]'h
                  else (0 : UInt64)) <<< UInt64.ofNat (j * k))) =
        (fun acc j => acc ||| ((f j) <<< UInt64.ofNat (j * k))) from rfl]
  rw [testBit_foldl_lor_shifted_bounded k hk hk_lt hk_div f hf_bound perLimb r
        (le_refl _) hr]
  -- Now goal: (decide (r/k < perLimb) && (f (r/k)).toNat.testBit (r%k)) = RHS
  have h_rk_lt : r / k < perLimb := by
    rw [Nat.div_lt_iff_lt_mul hk, h_64_eq]
    exact hr
  have h_dec : decide (r / k < perLimb) = true := by simp [h_rk_lt]
  rw [h_dec, Bool.true_and]
  -- Now: (f (r/k)).toNat.testBit (r%k) = ((digits.toList[q * perLimb + r/k]?).getD 0).toNat.testBit (r%k)
  -- Compute f (r/k)
  by_cases h_in : q * perLimb + r / k < digits.size
  · have h_f_val : f (r / k) = digits[q * perLimb + r / k]'h_in := by simp [f, h_in]
    rw [h_f_val]
    have h_list : q * perLimb + r / k < digits.toList.length := by
      rw [Array.length_toList]; exact h_in
    rw [List.getElem?_eq_getElem h_list]
    simp
  · have h_f_val : f (r / k) = (0 : UInt64) := by simp [f, h_in]
    rw [h_f_val]
    have h_list : digits.toList.length ≤ q * perLimb + r / k := by
      rw [Array.length_toList]; omega
    rw [List.getElem?_eq_none h_list]
    simp

private theorem toNat_ofLimbDigitsPow2_of_div_64 (k : Nat) (hk : 1 ≤ k) (hk_lt : k < 64)
    (hk_div : 64 % k = 0) (digits : Array UInt64)
    (hd : ∀ x ∈ digits.toList.map UInt64.toNat, x < 2 ^ k) :
    (AzNat.ofLimbDigitsPow2 k digits).toNat =
      Nat.ofDigits (2 ^ k : Nat) (digits.toList.map UInt64.toNat) := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_ofDigits_pow2 k hk _ hd b, getElem?_map_toNat_getD]
  unfold AzNat.ofLimbDigitsPow2
  have h64 : ¬ k = 64 := by omega
  have h_div_dec : 1 ≤ k ∧ k < 64 ∧ 64 % k = 0 := ⟨hk, hk_lt, hk_div⟩
  rw [if_neg h64, dif_pos h_div_dec]
  rw [testBit_toNat_ofLimbs]
  set perLimb := 64 / k with h_perLimb_def
  set numLimbs := (digits.size + perLimb - 1) / perLimb with h_numLimbs_def
  have h_perLimb_pos : 0 < perLimb := Nat.div_pos (by omega) hk
  have h_64_eq : perLimb * k = 64 := by
    rw [h_perLimb_def]
    have h := Nat.div_add_mod 64 k
    rw [Nat.mul_comm] at h
    omega
  have h_b_mod_lt : b % 64 < 64 := Nat.mod_lt _ (by omega)
  -- Decomposition: b / k = (b/64) * perLimb + (b%64) / k, b % k = (b%64) % k.
  have h_b_decomp_eq : b = b % 64 + (b / 64 * perLimb) * k := by
    have hb := Nat.div_add_mod b 64
    have h1 : (b / 64 * perLimb) * k = (b / 64) * (perLimb * k) := by ring
    have h2 : (b / 64) * (perLimb * k) = (b / 64) * 64 := by rw [h_64_eq]
    omega
  have h_b_div : b / k = (b / 64) * perLimb + (b % 64) / k := by
    conv_lhs => rw [h_b_decomp_eq]
    rw [show b / 64 * perLimb * k = k * (b / 64 * perLimb) from by ring]
    rw [Nat.add_mul_div_left _ _ hk, Nat.add_comm]
  have h_b_mod : b % k = (b % 64) % k := by
    conv_lhs => rw [h_b_decomp_eq]
    rw [Nat.add_mul_mod_self_right]
  rw [h_b_div, h_b_mod]
  -- Case split on b/64 < numLimbs.
  by_cases h_q_lt : b / 64 < numLimbs
  · -- limbs.toList[b/64]? = some (the foldl)
    set f_outer : Fin numLimbs → UInt64 := fun q =>
      (Array.range perLimb).foldl (init := (0 : UInt64)) fun acc j =>
        let i := q.val * perLimb + j
        if h : i < digits.size then
          acc ||| ((digits[i]'h) <<< UInt64.ofNat (j * k))
        else acc with h_f_outer
    have h_ofFn_toList_len :
        (Array.ofFn (n := numLimbs) f_outer).toList.length = numLimbs := by
      rw [Array.toList_ofFn, List.length_ofFn]
    have h_get :
        ((Array.ofFn (n := numLimbs) f_outer).toList[b / 64]?).getD 0 =
          f_outer ⟨b / 64, h_q_lt⟩ := by
      rw [Array.toList_ofFn]
      have h_lt : b / 64 < (List.ofFn f_outer).length := by
        rw [List.length_ofFn]; exact h_q_lt
      rw [List.getElem?_eq_getElem h_lt, List.getElem_ofFn]
      rfl
    rw [h_get]
    -- Now (f_outer ⟨b/64, _⟩).toNat.testBit (b%64) = ...
    show ((Array.range perLimb).foldl (init := (0 : UInt64)) (fun acc j =>
        let i := (b / 64) * perLimb + j
        if h : i < digits.size then
          acc ||| ((digits[i]'h) <<< UInt64.ofNat (j * k))
        else acc)).toNat.testBit (b % 64) = _
    exact testBit_limb_div_64 k hk hk_lt hk_div digits hd (b / 64) (b % 64) h_b_mod_lt
  · -- b/64 ≥ numLimbs: limbs OOB, LHS = 0; need RHS = 0 too.
    push Not at h_q_lt
    have h_limb_zero :
        ((Array.ofFn (n := numLimbs) (fun q : Fin numLimbs =>
            (Array.range perLimb).foldl (init := (0 : UInt64)) fun acc j =>
              let i := q.val * perLimb + j
              if h : i < digits.size then
                acc ||| ((digits[i]'h) <<< UInt64.ofNat (j * k))
              else acc)).toList[b / 64]?).getD 0 = (0 : UInt64) := by
      have h_len : (Array.ofFn (n := numLimbs) (fun q : Fin numLimbs =>
          (Array.range perLimb).foldl (init := (0 : UInt64)) fun acc j =>
            let i := q.val * perLimb + j
            if h : i < digits.size then
              acc ||| ((digits[i]'h) <<< UInt64.ofNat (j * k))
            else acc)).toList.length ≤ b / 64 := by
        rw [Array.toList_ofFn, List.length_ofFn]
        exact h_q_lt
      rw [List.getElem?_eq_none h_len]
      rfl
    rw [h_limb_zero]
    -- LHS = (0 : UInt64).toNat.testBit (b%64) = 0
    -- Need RHS = 0 too: (digits.toList[b/64 * perLimb + b%64 / k]?).getD 0 = 0
    have h_digits_oob : digits.toList.length ≤ b / 64 * perLimb + b % 64 / k := by
      rw [Array.length_toList]
      have h_numLimbs_ge : digits.size ≤ numLimbs * perLimb := by
        rw [h_numLimbs_def, Nat.mul_comm]
        have h_dm := Nat.div_add_mod (digits.size + perLimb - 1) perLimb
        have h_mod_lt : (digits.size + perLimb - 1) % perLimb < perLimb :=
          Nat.mod_lt _ h_perLimb_pos
        omega
      have h_bq_ge : numLimbs * perLimb ≤ b / 64 * perLimb :=
        Nat.mul_le_mul_right perLimb h_q_lt
      calc digits.size ≤ numLimbs * perLimb := h_numLimbs_ge
        _ ≤ b / 64 * perLimb := h_bq_ge
        _ ≤ b / 64 * perLimb + b % 64 / k := Nat.le_add_right _ _
    rw [List.getElem?_eq_none h_digits_oob]
    show (((0 : UInt64).toNat).testBit (b % 64) : Bool) = _
    show (0 : Nat).testBit (b % 64) = ((((none : Option UInt64).getD 0 : UInt64).toNat).testBit (b % 64 % k))
    simp [Nat.zero_testBit]

/-! ### `k ∤ 64` branch correctness

For `1 ≤ k < 64` with `k ∤ 64`, each limb is built by OR-ing contributions
from a window of digits that straddle the limb boundary. The first digit
(at index `iLo := q * 64 / k`) may need a right shift; later digits in
the window need a left shift. -/

/-- Per-limb bit identity for the `k ∤ 64` branch. After processing all
    `n` digits in the window `[iLo, iLo + n)` (where `iLo := q * 64 / k`),
    the accumulator's bit `r` matches the corresponding bit of the global
    digit array. -/
private theorem testBit_foldl_cross_limb
    (k : Nat) (hk : 1 ≤ k) (hk_lt : k < 64)
    (digits : Array UInt64) (hd : ∀ x ∈ digits.toList.map UInt64.toNat, x < 2 ^ k)
    (q : Nat) :
    ∀ (n : Nat) (r : Nat),
      r < 64 → q * 64 / k + n ≤ (q * 64 + 63) / k + 1 →
    ((List.range n).foldl (fun (acc : UInt64) j =>
        let i := q * 64 / k + j
        if h : i < digits.size then
          let d := digits[i]'h
          if i * k ≥ q * 64 then
            acc ||| (d <<< UInt64.ofNat (i * k - q * 64))
          else
            acc ||| (d >>> UInt64.ofNat (q * 64 - i * k))
        else acc) 0).toNat.testBit r =
      (decide ((q * 64 + r) / k < q * 64 / k + n) &&
        ((digits.toList[(q * 64 + r) / k]?).getD 0).toNat.testBit ((q * 64 + r) % k)) := by
  intro n
  set iLo := q * 64 / k with h_iLo_def
  have h_div_mod_q64 : iLo * k + q * 64 % k = q * 64 := by
    have h := Nat.div_add_mod (q * 64) k
    rw [Nat.mul_comm] at h
    exact h
  have h_iLo_le : iLo * k ≤ q * 64 := by omega
  have h_iLo_succ_gt : (iLo + 1) * k > q * 64 := by
    have h_mod_lt : q * 64 % k < k := Nat.mod_lt _ hk
    have h_eq : (iLo + 1) * k = iLo * k + k := by ring
    omega
  induction n with
  | zero =>
    intro r _ _
    show (0 : UInt64).toNat.testBit r = _
    rw [show ((0 : UInt64).toNat = 0) from rfl, Nat.zero_testBit]
    have h_iLo_le' : iLo ≤ (q * 64 + r) / k :=
      Nat.div_le_div_right (by omega)
    have h_dec : decide ((q * 64 + r) / k < iLo + 0) = false :=
      decide_eq_false (by omega)
    rw [h_dec, Bool.false_and]
  | succ n ih =>
    intro r hr h_n
    have hn' : iLo + n ≤ (q * 64 + 63) / k + 1 := by omega
    have h_iLo_le_div : iLo ≤ (q * 64 + r) / k :=
      Nat.div_le_div_right (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set prev := (List.range n).foldl (fun (acc : UInt64) j =>
        let i := q * 64 / k + j
        if h : i < digits.size then
          let d := digits[i]'h
          if i * k ≥ q * 64 then
            acc ||| (d <<< UInt64.ofNat (i * k - q * 64))
          else
            acc ||| (d >>> UInt64.ofNat (q * 64 - i * k))
        else acc) 0 with h_prev_def
    have h_prev_bit : prev.toNat.testBit r =
        (decide ((q * 64 + r) / k < iLo + n) &&
          ((digits.toList[(q * 64 + r) / k]?).getD 0).toNat.testBit ((q * 64 + r) % k)) :=
      ih r hr hn'
    -- The new step (j = n) adds digit at i = iLo + n.
    set i := iLo + n with h_i_def
    -- Bit of new value at local position r matches global bit b = q*64 + r at position b%k of digit b/k,
    -- when b/k = i and i < digits.size.
    by_cases h_i_in : i < digits.size
    · -- i < digits.size: take the if branch
      simp only [h_i_in, ↓reduceDIte]
      -- Now split on i*k ≥ q*64.
      have h_digit_lt : (digits[i]'h_i_in).toNat < 2 ^ k := by
        apply hd
        rw [List.mem_map]
        exact ⟨digits[i]'h_i_in, List.getElem_mem h_i_in, rfl⟩
      by_cases h_shift : i * k ≥ q * 64
      · -- Left shift
        rw [if_pos h_shift, UInt64.toNat_or, Nat.testBit_or, h_prev_bit]
        -- Compute (digits[i] <<< (i*k - q*64)).toNat.testBit r
        have h_s_lt : i * k - q * 64 < 64 := by
          have h_iHi := Nat.div_add_mod (q * 64 + 63) k
          rw [Nat.mul_comm] at h_iHi
          have : i ≤ (q * 64 + 63) / k := by
            have : i = iLo + n := h_i_def
            omega
          have h_ik_le : i * k ≤ (q * 64 + 63) / k * k := Nat.mul_le_mul_right k this
          have h_mod_nn : 0 ≤ (q * 64 + 63) % k := Nat.zero_le _
          omega
        rw [UInt64.toNat_shiftLeft]
        have h_amt : (UInt64.ofNat (i * k - q * 64)).toNat % 64 = i * k - q * 64 := by
          have h_pow : i * k - q * 64 < 2 ^ 64 := by
            have : (64 : Nat) < 2 ^ 64 := by decide
            omega
          show (i * k - q * 64) % 2 ^ 64 % 64 = i * k - q * 64
          rw [Nat.mod_eq_of_lt h_pow, Nat.mod_eq_of_lt h_s_lt]
        rw [h_amt]
        rw [Nat.shiftLeft_eq]
        -- (digits[i]).toNat * 2 ^ (i*k - q*64) might exceed 2^64, but the mod 2^64
        -- preserves bits in [0, 64).
        rw [Nat.testBit_mod_two_pow]
        rw [show (decide (r < 64) = true) from by simp [hr]]
        rw [Bool.true_and, Nat.testBit_mul_two_pow]
        -- Goal: (... && digit.testBit (r - (i*k - q*64))) || something = ...
        -- Now compute when this is nonzero: r ≥ s = i*k - q*64 AND r - s < k.
        -- This means r ∈ [s, s + k) which corresponds to b = q*64 + r ∈ [i*k, (i+1)*k), so b/k = i.
        by_cases h_b_div_lt : (q * 64 + r) / k < iLo + n
        · -- IH branch contributes. New step's contribution: need to show it doesn't (since b/k < i = iLo+n).
          have h_b_lt_i : (q * 64 + r) / k < i := by omega
          have h_b_lt_ik : q * 64 + r < i * k := by
            have h_ik_le : (q * 64 + r) / k * k + (q * 64 + r) % k = q * 64 + r := by
              have := Nat.div_add_mod (q * 64 + r) k
              rw [Nat.mul_comm] at this; exact this
            have h_mod : (q * 64 + r) % k < k := Nat.mod_lt _ hk
            have h_le : ((q * 64 + r) / k + 1) * k ≤ i * k := Nat.mul_le_mul_right k (by omega)
            have h_succ : ((q * 64 + r) / k + 1) * k = (q * 64 + r) / k * k + k := by ring
            omega
          have h_r_lt_s : r < i * k - q * 64 := by omega
          have h_not_s_le : ¬ i * k - q * 64 ≤ r := by omega
          rw [show (decide (i * k - q * 64 ≤ r) = false) from by simp [h_not_s_le]]
          rw [Bool.false_and, Bool.or_false]
          have h_dec : decide ((q * 64 + r) / k < iLo + (n + 1)) = true := by
            have : (q * 64 + r) / k < iLo + (n + 1) := by omega
            simp [this]
          have h_dec_n : decide ((q * 64 + r) / k < iLo + n) = true := by simp [h_b_div_lt]
          rw [h_dec_n, h_dec]
        · -- IH branch doesn't contribute. Check new step.
          push Not at h_b_div_lt
          have h_dec_n : decide ((q * 64 + r) / k < iLo + n) = false := by
            have : ¬ (q * 64 + r) / k < iLo + n := by omega
            simp [this]
          rw [h_dec_n, Bool.false_and, Bool.false_or]
          -- Now we need to compute the new step's contribution and match RHS.
          by_cases h_b_eq : (q * 64 + r) / k = i
          · -- The new digit IS the responsible one.
            have h_dm := Nat.div_add_mod (q * 64 + r) k
            rw [Nat.mul_comm] at h_dm
            have h_b_lt_ik1 : q * 64 + r < (i + 1) * k := by
              have h_mod : (q * 64 + r) % k < k := Nat.mod_lt _ hk
              have h_succ : (i + 1) * k = i * k + k := by ring
              have h_dm' := h_dm
              rw [h_b_eq] at h_dm'
              omega
            have h_ik_le_b : i * k ≤ q * 64 + r := by
              have h_dm' := h_dm
              rw [h_b_eq] at h_dm'
              omega
            have h_s_le_r : i * k - q * 64 ≤ r := by omega
            have h_r_minus_s_lt_64 : r - (i * k - q * 64) < 64 := by omega
            have h_r_minus_s_eq : r - (i * k - q * 64) = (q * 64 + r) - i * k := by omega
            rw [show (decide (i * k - q * 64 ≤ r) = true) from by simp [h_s_le_r]]
            rw [Bool.true_and]
            have h_b_mod : (q * 64 + r) % k = (q * 64 + r) - i * k := by
              have h_dm' := h_dm
              rw [h_b_eq] at h_dm'
              omega
            have h_list_get : ((digits.toList[(q * 64 + r) / k]?).getD 0) =
                digits[i]'h_i_in := by
              rw [h_b_eq]
              have h_lt : i < digits.toList.length := by
                rw [Array.length_toList]; exact h_i_in
              rw [List.getElem?_eq_getElem h_lt]
              simp
            rw [h_list_get, h_r_minus_s_eq, ← h_b_mod]
            have h_dec_succ : decide ((q * 64 + r) / k < iLo + (n + 1)) = true := by
              have : (q * 64 + r) / k < iLo + (n + 1) := by omega
              simp [this]
            rw [h_dec_succ, Bool.true_and]
          · -- The new digit isn't responsible either. Both contributions are 0.
            have h_b_ge : (q * 64 + r) / k > i := by omega
            have h_b_ge_ik1 : q * 64 + r ≥ (i + 1) * k := by
              have h_dm := Nat.div_add_mod (q * 64 + r) k
              rw [Nat.mul_comm] at h_dm
              have h_b_div_ge : (q * 64 + r) / k ≥ i + 1 := by omega
              have h_mul_ge : ((q * 64 + r) / k) * k ≥ (i + 1) * k :=
                Nat.mul_le_mul_right k h_b_div_ge
              omega
            have h_r_ge_s_k : r ≥ i * k - q * 64 + k := by
              have h_succ : (i + 1) * k = i * k + k := by ring
              omega
            have h_digit_high : (digits[i]'h_i_in).toNat.testBit (r - (i * k - q * 64)) = false := by
              apply Nat.testBit_eq_false_of_lt
              calc (digits[i]'h_i_in).toNat < 2 ^ k := h_digit_lt
                _ ≤ 2 ^ (r - (i * k - q * 64)) :=
                    Nat.pow_le_pow_right (by omega) (by omega)
            rw [h_digit_high, Bool.and_false]
            have h_dec_succ : decide ((q * 64 + r) / k < iLo + (n + 1)) = false := by
              have : ¬ (q * 64 + r) / k < iLo + (n + 1) := by omega
              simp [this]
            rw [h_dec_succ, Bool.false_and]
      · -- Right shift (i*k < q*64, only happens when i = iLo with iLo*k < q*64, so n = 0)
        push Not at h_shift
        rw [if_neg (by omega : ¬ i * k ≥ q * 64)]
        rw [UInt64.toNat_or, Nat.testBit_or, h_prev_bit]
        -- Compute (digits[i] >>> (q*64 - i*k)).toNat.testBit r
        have h_n_zero : n = 0 := by
          by_contra h_pos
          push Not at h_pos
          have h_n_ge : 1 ≤ n := by omega
          have h_iLn_ge : (iLo + n) * k ≥ (iLo + 1) * k := Nat.mul_le_mul_right k (by omega)
          have h_i_eq : i * k = (iLo + n) * k := by rw [h_i_def]
          rw [h_i_eq] at h_shift
          omega
        subst h_n_zero
        have h_i_eq_iLo : i = iLo := by simp [h_i_def]
        have h_s : q * 64 - i * k > 0 := by omega
        have h_s_lt_k : q * 64 - i * k < k := by
          rw [h_i_eq_iLo]
          have h_dm := Nat.div_add_mod (q * 64) k
          rw [Nat.mul_comm] at h_dm
          have h_mod_lt : q * 64 % k < k := Nat.mod_lt _ hk
          omega
        have h_s_lt_64 : q * 64 - i * k < 64 := by omega
        rw [UInt64.toNat_shiftRight]
        have h_amt : (UInt64.ofNat (q * 64 - i * k)).toNat % 64 = q * 64 - i * k := by
          have h_pow : q * 64 - i * k < 2 ^ 64 := by
            have : (64 : Nat) < 2 ^ 64 := by decide
            omega
          show (q * 64 - i * k) % 2 ^ 64 % 64 = q * 64 - i * k
          rw [Nat.mod_eq_of_lt h_pow, Nat.mod_eq_of_lt h_s_lt_64]
        rw [h_amt]
        -- (digits[i].toNat >>> (q*64 - i*k)).testBit r = digits[i].testBit (r + (q*64 - i*k))
        rw [Nat.testBit_shiftRight]
        -- Now goal involves: digit.testBit (r + (q*64 - i*k)) combined with IH
        by_cases h_b_div_lt : (q * 64 + r) / k < iLo + 0
        · -- IH branch contributes. But b/k < iLo + 0 means b/k < iLo, contradicting h_iLo_le_div.
          exfalso
          have : iLo ≤ (q * 64 + r) / k := h_iLo_le_div
          omega
        · -- IH branch doesn't contribute. Check new step.
          have h_dec_n : decide ((q * 64 + r) / k < iLo + 0) = false := by
            simp; omega
          rw [h_dec_n, Bool.false_and, Bool.false_or]
          by_cases h_b_eq : (q * 64 + r) / k = i
          · -- New digit IS the responsible one.
            have h_dm := Nat.div_add_mod (q * 64 + r) k
            rw [Nat.mul_comm] at h_dm
            have h_b_lt_ik1 : q * 64 + r < (i + 1) * k := by
              have h_mod : (q * 64 + r) % k < k := Nat.mod_lt _ hk
              have h_succ : (i + 1) * k = i * k + k := by ring
              have h_dm' := h_dm
              rw [h_b_eq] at h_dm'
              omega
            have h_r_plus_s_eq : q * 64 - i * k + r = (q * 64 + r) - i * k := by omega
            have h_b_mod : (q * 64 + r) % k = (q * 64 + r) - i * k := by
              have h_dm' := h_dm
              rw [h_b_eq] at h_dm'
              omega
            have h_list_get : ((digits.toList[(q * 64 + r) / k]?).getD 0) =
                digits[i]'h_i_in := by
              rw [h_b_eq]
              have h_lt : i < digits.toList.length := by
                rw [Array.length_toList]; exact h_i_in
              rw [List.getElem?_eq_getElem h_lt]
              simp
            rw [h_list_get, h_r_plus_s_eq, ← h_b_mod]
            have h_dec_succ : decide ((q * 64 + r) / k < iLo + (0 + 1)) = true := by
              have : (q * 64 + r) / k < iLo + (0 + 1) := by
                rw [h_b_eq, h_i_eq_iLo]; omega
              simp [this]
            rw [h_dec_succ, Bool.true_and]
          · -- New digit isn't responsible. Need digit-bit to be 0.
            have h_b_ge : (q * 64 + r) / k > i := by
              rw [h_i_eq_iLo]
              omega
            have h_b_ge_ik1 : q * 64 + r ≥ (i + 1) * k := by
              have h_dm := Nat.div_add_mod (q * 64 + r) k
              rw [Nat.mul_comm] at h_dm
              have h_b_div_ge : (q * 64 + r) / k ≥ i + 1 := by omega
              have h_mul_ge : ((q * 64 + r) / k) * k ≥ (i + 1) * k :=
                Nat.mul_le_mul_right k h_b_div_ge
              omega
            have h_r_plus_s_ge_k : r + (q * 64 - i * k) ≥ k := by
              have h_succ : (i + 1) * k = i * k + k := by ring
              omega
            have h_digit_high : (digits[i]'h_i_in).toNat.testBit (q * 64 - i * k + r) = false := by
              apply Nat.testBit_eq_false_of_lt
              calc (digits[i]'h_i_in).toNat < 2 ^ k := h_digit_lt
                _ ≤ 2 ^ (q * 64 - i * k + r) :=
                    Nat.pow_le_pow_right (by omega) (by omega)
            rw [h_digit_high]
            have h_dec_succ : decide ((q * 64 + r) / k < iLo + (0 + 1)) = false := by
              have : ¬ (q * 64 + r) / k < iLo + (0 + 1) := by
                rw [h_i_eq_iLo] at h_b_ge
                omega
              simp [this]
            rw [h_dec_succ, Bool.false_and]
    · -- i ≥ digits.size: step skips. Need to show same identity holds with extended bound.
      simp only [h_i_in, ↓reduceDIte]
      rw [h_prev_bit]
      by_cases h_b_div_lt : (q * 64 + r) / k < iLo + n
      · have h_dec_n : decide ((q * 64 + r) / k < iLo + n) = true := by simp [h_b_div_lt]
        have h_dec_succ : decide ((q * 64 + r) / k < iLo + (n + 1)) = true := by
          have : (q * 64 + r) / k < iLo + (n + 1) := by omega
          simp [this]
        rw [h_dec_n, h_dec_succ]
      · push Not at h_b_div_lt
        by_cases h_b_eq : (q * 64 + r) / k = i
        · have h_list : digits.toList.length ≤ (q * 64 + r) / k := by
            rw [Array.length_toList, h_b_eq]
            push Not at h_i_in
            exact h_i_in
          rw [List.getElem?_eq_none h_list]
          simp [Nat.zero_testBit]
        · have h_dec_n : decide ((q * 64 + r) / k < iLo + n) = false := by
            have : ¬ (q * 64 + r) / k < iLo + n := by omega
            simp [this]
          have h_dec_succ : decide ((q * 64 + r) / k < iLo + (n + 1)) = false := by
            have : ¬ (q * 64 + r) / k < iLo + (n + 1) := by omega
            simp [this]
          rw [h_dec_n, h_dec_succ]

private theorem toNat_ofLimbDigitsPow2_of_not_div_64 (k : Nat) (hk : 1 ≤ k) (hk_lt : k < 64)
    (hk_not_div : ¬ (1 ≤ k ∧ k < 64 ∧ 64 % k = 0)) (digits : Array UInt64)
    (hd : ∀ x ∈ digits.toList.map UInt64.toNat, x < 2 ^ k) :
    (AzNat.ofLimbDigitsPow2 k digits).toNat =
      Nat.ofDigits (2 ^ k : Nat) (digits.toList.map UInt64.toNat) := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_ofDigits_pow2 k hk _ hd b, getElem?_map_toNat_getD]
  unfold AzNat.ofLimbDigitsPow2
  have h64 : ¬ k = 64 := by omega
  have h_lt_64 : 1 ≤ k ∧ k < 64 := ⟨hk, hk_lt⟩
  rw [if_neg h64, dif_neg hk_not_div, dif_pos h_lt_64]
  rw [testBit_toNat_ofLimbs]
  set totalBits := digits.size * k with h_totalBits_def
  set numLimbs := (totalBits + 63) / 64 with h_numLimbs_def
  have h_b_mod_lt : b % 64 < 64 := Nat.mod_lt _ (by omega)
  -- The global bit position
  set bGlobal := b / 64 * 64 + b % 64 with h_bGlobal_def
  have h_bGlobal_eq : bGlobal = b := by
    rw [h_bGlobal_def]; omega
  by_cases h_q_lt : b / 64 < numLimbs
  · -- Apply per-limb identity
    set f_outer : Fin numLimbs → UInt64 := fun q =>
      let qBits := q.val * 64
      let iLo := qBits / k
      let iHi := (qBits + 63) / k
      (Array.range (iHi + 1 - iLo)).foldl (init := (0 : UInt64)) fun acc j =>
        let i := iLo + j
        if h : i < digits.size then
          let d := digits[i]'h
          if i * k ≥ qBits then
            acc ||| (d <<< UInt64.ofNat (i * k - qBits))
          else
            acc ||| (d >>> UInt64.ofNat (qBits - i * k))
        else acc with h_f_outer_def
    have h_get : ((Array.ofFn (n := numLimbs) f_outer).toList[b / 64]?).getD 0 =
        f_outer ⟨b / 64, h_q_lt⟩ := by
      rw [Array.toList_ofFn]
      have h_lt : b / 64 < (List.ofFn f_outer).length := by
        rw [List.length_ofFn]; exact h_q_lt
      rw [List.getElem?_eq_getElem h_lt, List.getElem_ofFn]
      rfl
    rw [h_get]
    show ((Array.range (((b / 64) * 64 + 63) / k + 1 - (b / 64) * 64 / k)).foldl
            (init := (0 : UInt64)) (fun acc j =>
              let i := (b / 64) * 64 / k + j
              if h : i < digits.size then
                let d := digits[i]'h
                if i * k ≥ (b / 64) * 64 then
                  acc ||| (d <<< UInt64.ofNat (i * k - (b / 64) * 64))
                else
                  acc ||| (d >>> UInt64.ofNat ((b / 64) * 64 - i * k))
              else acc)).toNat.testBit (b % 64) = _
    rw [← Array.foldl_toList, Array.toList_range]
    have h_n_bound :
        (b / 64) * 64 / k + (((b / 64) * 64 + 63) / k + 1 - (b / 64) * 64 / k) ≤
          ((b / 64) * 64 + 63) / k + 1 := by
      have h_le : (b / 64) * 64 / k ≤ ((b / 64) * 64 + 63) / k :=
        Nat.div_le_div_right (by omega)
      omega
    rw [testBit_foldl_cross_limb k hk hk_lt digits hd (b / 64) _ (b % 64) h_b_mod_lt h_n_bound]
    -- The decide condition: ((b/64)*64 + b%64) / k < (b/64)*64/k + ((b/64)*64+63)/k + 1 - (b/64)*64/k
    --                     = ((b/64)*64+63)/k + 1.
    -- And ((b/64)*64 + b%64) / k ≤ ((b/64)*64 + 63) / k (since b%64 ≤ 63).
    have h_dec : decide
        (((b / 64) * 64 + b % 64) / k <
         (b / 64) * 64 / k + (((b / 64) * 64 + 63) / k + 1 - (b / 64) * 64 / k)) = true := by
      have h_le : ((b / 64) * 64 + b % 64) / k ≤ ((b / 64) * 64 + 63) / k :=
        Nat.div_le_div_right (by omega)
      have h_iLo_le_iHi : (b / 64) * 64 / k ≤ ((b / 64) * 64 + 63) / k :=
        Nat.div_le_div_right (by omega)
      have : ((b / 64) * 64 + b % 64) / k <
             (b / 64) * 64 / k + (((b / 64) * 64 + 63) / k + 1 - (b / 64) * 64 / k) := by omega
      simp [this]
    rw [h_dec, Bool.true_and]
    -- Now: ((digits.toList[((b/64)*64 + b%64) / k]?).getD 0).toNat.testBit (((b/64)*64 + b%64) % k)
    -- = ((digits.toList[b / k]?).getD 0).toNat.testBit (b % k).
    have h_b_eq : (b / 64) * 64 + b % 64 = b := by omega
    rw [h_b_eq]
  · -- b/64 ≥ numLimbs: LHS = 0. Need RHS = 0.
    push Not at h_q_lt
    set f_oob : Fin numLimbs → UInt64 := fun q =>
      let qBits := q.val * 64
      let iLo := qBits / k
      let iHi := (qBits + 63) / k
      (Array.range (iHi + 1 - iLo)).foldl (init := (0 : UInt64)) fun acc j =>
        let i := iLo + j
        if h : i < digits.size then
          let d := digits[i]'h
          if i * k ≥ qBits then
            acc ||| (d <<< UInt64.ofNat (i * k - qBits))
          else
            acc ||| (d >>> UInt64.ofNat (qBits - i * k))
        else acc with h_f_oob_def
    have h_len_oob : (Array.ofFn (n := numLimbs) f_oob).toList.length ≤ b / 64 := by
      rw [Array.toList_ofFn, List.length_ofFn]
      exact h_q_lt
    rw [List.getElem?_eq_none h_len_oob]
    -- RHS: need b/k ≥ digits.size.
    have h_digits_oob : digits.toList.length ≤ b / k := by
      rw [Array.length_toList]
      -- b ≥ numLimbs * 64, want b/k ≥ digits.size.
      have h_b_ge : b ≥ numLimbs * 64 := by
        have h_b_decomp : b = (b / 64) * 64 + b % 64 := by omega
        have h_q_64_ge : (b / 64) * 64 ≥ numLimbs * 64 :=
          Nat.mul_le_mul_right 64 h_q_lt
        omega
      -- numLimbs * 64 ≥ digits.size * k (by def of numLimbs)
      have h_numLimbs_ge_div : numLimbs * 64 ≥ digits.size * k := by
        rw [h_numLimbs_def, h_totalBits_def]
        have h_dm := Nat.div_add_mod (digits.size * k + 63) 64
        have h_mod_lt : (digits.size * k + 63) % 64 < 64 := Nat.mod_lt _ (by omega)
        have h_eq : 64 * ((digits.size * k + 63) / 64) + (digits.size * k + 63) % 64
                    = digits.size * k + 63 := h_dm
        rw [Nat.mul_comm]
        omega
      have h_b_ge_div : b ≥ digits.size * k := by omega
      have h_bk_ge : b / k ≥ (digits.size * k) / k := Nat.div_le_div_right h_b_ge_div
      have h_dk : (digits.size * k) / k = digits.size := by
        rw [Nat.mul_div_cancel _ hk]
      omega
    rw [List.getElem?_eq_none h_digits_oob]
    simp [Nat.zero_testBit]

/-! ### Main correctness theorem -/

/-- **Correctness of `AzNat.ofLimbDigitsPow2`.** For `1 ≤ k ≤ 64` and each input
    digit `< 2 ^ k`, the reconstructed `AzNat` has the value `Nat.ofDigits (2^k)`
    of the digit list. -/
theorem toNat_ofLimbDigitsPow2 (k : Nat) (hk : 1 ≤ k) (hk64 : k ≤ 64)
    (digits : Array UInt64) (hd : ∀ x ∈ digits.toList.map UInt64.toNat, x < 2 ^ k) :
    (AzNat.ofLimbDigitsPow2 k digits).toNat =
      Nat.ofDigits (2 ^ k : Nat) (digits.toList.map UInt64.toNat) := by
  by_cases h_64 : k = 64
  · subst h_64
    exact toNat_ofLimbDigitsPow2_of_64 digits
  · have hk_lt : k < 64 := by omega
    by_cases h_div : 1 ≤ k ∧ k < 64 ∧ 64 % k = 0
    · exact toNat_ofLimbDigitsPow2_of_div_64 k h_div.1 h_div.2.1 h_div.2.2 digits hd
    · exact toNat_ofLimbDigitsPow2_of_not_div_64 k hk hk_lt h_div digits hd

/-! ### Round-trip: `ofLimbDigitsPow2 ∘ limbDigitsPow2 = id` -/

/-- **Round-trip with `limbDigitsPow2`.** For `1 ≤ k ≤ 64`, reconstructing an
    `AzNat` from its base-`2^k` digits gives back the original. -/
theorem ofLimbDigitsPow2_limbDigitsPow2 (k : Nat) (hk : 1 ≤ k) (hk64 : k ≤ 64)
    (n : AzNat) :
    AzNat.ofLimbDigitsPow2 k (n.limbDigitsPow2 k) = n := by
  apply toNat_injective
  have h_2k : 1 < 2 ^ k := by
    have : (1 : Nat) = 2 ^ 0 := by simp
    rw [this]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have h_digits_lt : ∀ x ∈ (n.limbDigitsPow2 k).toList.map UInt64.toNat, x < 2 ^ k := by
    intro x hx
    rw [limbDigitsPow2_eq k hk hk64 n] at hx
    exact Nat.digits_lt_base h_2k hx
  rw [toNat_ofLimbDigitsPow2 k hk hk64 (n.limbDigitsPow2 k) h_digits_lt]
  rw [limbDigitsPow2_eq k hk hk64 n]
  rw [Nat.ofDigits_digits]

end Azurite.AzNat
