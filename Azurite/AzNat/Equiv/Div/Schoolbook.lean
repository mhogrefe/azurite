import Azurite.AzNat.Equiv.Div.BodyStep
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Sub

namespace Azurite.AzNat

/-- `bodyStep` matches what `schoolbookDivModLimbs.go` computes for `j+1` before
    the recursive tail-call. Specifically, `go a b loA loB n (j+1) bn1 inv ...`
    equals `go (bodyStep a b loA loB n j q_init ...) b loA loB n j bn1 inv ...`
    where `q_init` is the trial digit that `go` would pick. -/
private theorem schoolbookDivModLimbs.go_succ_eq_bodyStep
    (a b : Array UInt64) (loA loB n j : Nat) (bn1 inv : UInt64)
    (hA : loA + n + (j + 1) ≤ a.size) (hB : loB + n ≤ b.size) (h_n_pos : 0 < n) :
    schoolbookDivModLimbs.go a b loA loB n (j + 1) bn1 inv hA hB h_n_pos
      = schoolbookDivModLimbs.go
          (schoolbookDivModLimbs.bodyStep a b loA loB n j
            (if bn1 ≤ a[loA + n + j]'(by omega) then (0 : UInt64) - 1
             else (UInt64.div2By1 (a[loA + n + j]'(by omega))
                     (a[loA + (n - 1) + j]'(by omega)) bn1 inv).1)
            (by omega) hB)
          b loA loB n j bn1 inv
          (by rw [schoolbookDivModLimbs.bodyStep_size]; omega) hB h_n_pos := by
  conv_lhs => rw [schoolbookDivModLimbs.go]
  rfl

/-- **BZ correctness invariant for `schoolbookDivModLimbs.go`**.

    Pre-condition: the dividend slice `a[loA : loA + n + j]` satisfies the
    Brent-Zimmermann invariant `A < β^j · B`, where `B` is the divisor
    `b[loB : loB + n]` and `β = 2^64`.

    Post-condition: after running `j` body iterations of `go`, the resulting
    array `a'` has the remainder in `a'[loA : loA + n]` (with `R < B`) and
    the `j` quotient digits in `a'[loA + n : loA + n + j]`, satisfying
    `A = Q · B + R`.

    Both the base case and inductive step are proved; the latter consumes
    the helper `bodyStep_BZ`. -/
private theorem schoolbookDivModLimbs.go_toNat
    (a b : Array UInt64) (loA loB n j : Nat) (bn1 inv : UInt64)
    (hA : loA + n + j ≤ a.size) (hB : loB + n ≤ b.size) (h_n_pos : 0 < n)
    (hbn1_eq : ∃ h_idx : loB + n - 1 < b.size, bn1 = b[loB + n - 1]'h_idx)
    (hbn1_norm : 2 ^ 63 ≤ bn1.toNat)
    (hinv : ∃ h, inv = UInt64.reciprocal bn1 h)
    (h_B_pos : 0 < toNatLimbsList ((b.toList.drop loB).take n))
    (h_inv_BZ : toNatLimbsList ((a.toList.drop loA).take (n + j))
                  < 2 ^ (64 * j) * toNatLimbsList ((b.toList.drop loB).take n)) :
    let a' := schoolbookDivModLimbs.go a b loA loB n j bn1 inv hA hB h_n_pos
    toNatLimbsList ((a'.toList.drop loA).take n)
        < toNatLimbsList ((b.toList.drop loB).take n)
      ∧ toNatLimbsList ((a.toList.drop loA).take (n + j))
          = toNatLimbsList ((a'.toList.drop (loA + n)).take j)
              * toNatLimbsList ((b.toList.drop loB).take n)
            + toNatLimbsList ((a'.toList.drop loA).take n) := by
  induction j generalizing a with
  | zero =>
    rw [schoolbookDivModLimbs.go]
    refine ⟨?_, ?_⟩
    · simpa using h_inv_BZ
    · simp [List.take_zero, toNatLimbsList]
  | succ j ih =>
    set B : Nat := toNatLimbsList ((b.toList.drop loB).take n) with hB_def
    -- Step 1: rewrite `go ... (j+1)` as `go (bodyStep ...) ... j` via
    -- `go_succ_eq_bodyStep`.
    rw [schoolbookDivModLimbs.go_succ_eq_bodyStep]
    -- The trial digit `go` computes.
    set q_init : UInt64 :=
      if bn1 ≤ a[loA + n + j]'(by omega) then (0 : UInt64) - 1
      else (UInt64.div2By1 (a[loA + n + j]'(by omega))
              (a[loA + (n - 1) + j]'(by omega)) bn1 inv).1 with hq_init_def
    set a₁ := schoolbookDivModLimbs.bodyStep a b loA loB n j q_init (by omega) hB
      with ha₁_def
    -- Step 2: derive the local BZ invariant on the (n+1)-limb slice from
    -- the global BZ invariant. Decompose `(a.drop loA).take (n + j + 1)`
    -- as low-`j` ++ top-`(n+1)` (at offset `loA + j`).
    have h_split_a :
        toNatLimbsList ((a.toList.drop loA).take (n + (j + 1)))
          = toNatLimbsList ((a.toList.drop loA).take j)
            + toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1)) * 2 ^ (64 * j) := by
      have h_eq : (n + (j + 1)) - j = n + 1 := by omega
      have h := toNatLimbsList_drop_take_split a loA (n + (j + 1)) j
                  (by omega) (by omega)
      rw [h_eq] at h
      exact h
    have h_low_lt : toNatLimbsList ((a.toList.drop loA).take j) < 2 ^ (64 * j) := by
      have h := toNatLimbsList_lt_pow ((a.toList.drop loA).take j)
      have h_len : ((a.toList.drop loA).take j).length ≤ j := by
        rw [List.length_take]; exact Nat.min_le_left _ _
      calc toNatLimbsList ((a.toList.drop loA).take j)
          < 2 ^ (64 * ((a.toList.drop loA).take j).length) := h
        _ ≤ 2 ^ (64 * j) := Nat.pow_le_pow_right (by norm_num)
                              (Nat.mul_le_mul_left 64 h_len)
    -- BZ invariant for j+1 says A < β^(j+1) · B.
    rw [h_split_a] at h_inv_BZ
    set A_low : Nat := toNatLimbsList ((a.toList.drop loA).take j) with hA_low_def
    set A_top : Nat := toNatLimbsList ((a.toList.drop (loA + j)).take (n + 1))
      with hA_top_def
    -- Derive the local invariant `A_top < β · B`.
    have h_BZ_local : A_top < 2 ^ 64 * B := by
      have h_pow_succ : (2 : Nat) ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by
        rw [show 64 * (j + 1) = 64 * j + 64 from by ring, Nat.pow_add]
      rw [h_pow_succ] at h_inv_BZ
      have h_pow_pos : 0 < (2 : Nat) ^ (64 * j) := Nat.two_pow_pos _
      -- `A_low + A_top * 2^(64*j) < 2^(64*j) * 2^64 * B`
      -- ⟹ `A_top * 2^(64*j) < 2^(64*j) * 2^64 * B` (subtract `A_low`)
      -- ⟹ `A_top < 2^64 * B`
      have h1 : A_top * 2 ^ (64 * j) < 2 ^ (64 * j) * 2 ^ 64 * B := by linarith
      have h_eq : 2 ^ (64 * j) * 2 ^ 64 * B = 2 ^ 64 * B * 2 ^ (64 * j) := by ring
      rw [h_eq] at h1
      exact Nat.lt_of_mul_lt_mul_right h1
    -- Step 3: invoke bodyStep_BZ to get the local correctness identity.
    have h_bodyStep_BZ := schoolbookDivModLimbs.bodyStep_BZ a b loA loB n j bn1 inv
      (by omega) hB h_n_pos hbn1_eq hbn1_norm hinv h_BZ_local h_B_pos
    -- Unwrap let-bindings inside bodyStep_BZ's statement.
    simp only at h_bodyStep_BZ
    -- bodyStep_BZ gives: low-n of a₁ at offset (loA+j) < B, and value identity.
    obtain ⟨h_R_lt, h_value_local⟩ := h_bodyStep_BZ
    set R : Nat := toNatLimbsList ((a₁.toList.drop (loA + j)).take n) with hR_def
    set digit : Nat := (a₁[loA + n + j]'(by
      rw [ha₁_def, schoolbookDivModLimbs.bodyStep_size]; omega)).toNat with hdigit_def
    -- Step 4: derive new BZ invariant on a₁ for step j: A_new < β^j · B.
    -- Decompose `(a₁.drop loA).take (n + j) = (a₁.drop loA).take j ++
    --   (a₁.drop (loA+j)).take n`. The low j slice equals A_low (preserved
    -- by bodyStep_toList_take_le with m0 = loA + j ... wait, take_le gives
    -- prefix preservation up to loA + j, but we need only up to ... the take
    -- is the first j entries of (drop loA), which corresponds to indices
    -- [loA, loA + j). prefix preservation up to loA + j gives us this).
    have h_a₁_size : a₁.size = a.size := by
      rw [ha₁_def]; exact schoolbookDivModLimbs.bodyStep_size _ _ _ _ _ _ _ _ _
    have h_low_preserved :
        (a₁.toList.drop loA).take j = (a.toList.drop loA).take j := by
      have h_take := schoolbookDivModLimbs.bodyStep_toList_take_le a b loA loB n j
        q_init (by omega) hB (loA + j) (Nat.le_refl _)
      -- bodyStep preserves the prefix up to loA + j. Restrict to (drop loA).take j.
      rw [← ha₁_def] at h_take
      -- (a₁.drop loA).take j = (a₁.take (loA + j)).drop loA
      have h1 : (a₁.toList.drop loA).take j
          = (a₁.toList.take (loA + j)).drop loA := by
        rw [List.take_drop, List.drop_take]
      have h2 : (a.toList.drop loA).take j
          = (a.toList.take (loA + j)).drop loA := by
        rw [List.take_drop, List.drop_take]
      rw [h1, h2, h_take]
    have h_split_a₁ :
        toNatLimbsList ((a₁.toList.drop loA).take (n + j))
          = toNatLimbsList ((a₁.toList.drop loA).take j)
            + toNatLimbsList ((a₁.toList.drop (loA + j)).take n) * 2 ^ (64 * j) := by
      have h_eq : (n + j) - j = n := by omega
      have h := toNatLimbsList_drop_take_split a₁ loA (n + j) j
                  (by omega) (by rw [h_a₁_size]; omega)
      rw [h_eq] at h
      exact h
    have h_a₁_low_value : toNatLimbsList ((a₁.toList.drop loA).take j) = A_low := by
      rw [h_low_preserved, hA_low_def]
    have h_a₁_BZ : toNatLimbsList ((a₁.toList.drop loA).take (n + j))
                     < 2 ^ (64 * j) * B := by
      rw [h_split_a₁, h_a₁_low_value]
      -- A_low + R * β^j < β^j * B   (need: A_low < β^j and R < B)
      -- ⟹ A_low < β^j ≤ β^j · (B - R)... use direct inequality:
      -- A_low + R * β^j ≤ (β^j - 1) + R * β^j = (R + 1) * β^j - 1 < (R+1) * β^j ≤ B * β^j
      have h_pow_pos : 0 < (2 : Nat) ^ (64 * j) := Nat.two_pow_pos _
      have h_R_succ : R + 1 ≤ B := h_R_lt
      have : A_low + R * 2 ^ (64 * j) < (R + 1) * 2 ^ (64 * j) := by
        have : R * 2 ^ (64 * j) + 2 ^ (64 * j) = (R + 1) * 2 ^ (64 * j) := by ring
        omega
      have h2 : (R + 1) * 2 ^ (64 * j) ≤ B * 2 ^ (64 * j) :=
        Nat.mul_le_mul_right _ h_R_succ
      have h_comm : B * 2 ^ (64 * j) = 2 ^ (64 * j) * B := by ring
      linarith
    -- Step 5: apply IH to a₁.
    have h_ih := ih a₁ (by rw [h_a₁_size]; omega) h_a₁_BZ
    simp only at h_ih
    obtain ⟨h_remainder_lt, h_recursive_value⟩ := h_ih
    set a₂ := schoolbookDivModLimbs.go a₁ b loA loB n j bn1 inv (by rw [h_a₁_size]; omega)
      hB h_n_pos with ha₂_def
    -- Step 6: combine the value identities to conclude.
    refine ⟨h_remainder_lt, ?_⟩
    -- Final algebraic combination: chain h_split_a, h_value_local,
    -- h_split_a₁ + h_a₁_low_value (giving A_new = A_low + R * β^j), the IH,
    -- and h_split_a₂_Q (decomposing the (j+1)-digit quotient slice).
    have h_a₂_size : a₂.size = a.size := by
      rw [ha₂_def, schoolbookDivModLimbs.go_size, h_a₁_size]
    have h_a₂_digit_idx : loA + n + j < a₂.size := by rw [h_a₂_size]; omega
    have h_a₁_digit_idx : loA + n + j < a₁.size := by rw [h_a₁_size]; omega
    -- a₂[loA+n+j] = a₁[loA+n+j] (suffix preservation through the recursive go).
    have h_drop_preserved :
        a₂.toList.drop (loA + n + j) = a₁.toList.drop (loA + n + j) := by
      rw [ha₂_def]
      exact schoolbookDivModLimbs.go_toList_drop a₁ b loA loB n j bn1 inv _ hB h_n_pos
    have h_a₂_eq_a₁_at :
        (a₂[loA + n + j]'h_a₂_digit_idx) = (a₁[loA + n + j]'h_a₁_digit_idx) := by
      have h_lenA₂ : a₂.toList.length = a.size := by
        rw [Array.length_toList, h_a₂_size]
      have h_lenA₁ : a₁.toList.length = a.size := by
        rw [Array.length_toList, h_a₁_size]
      have hpos₂ : 0 < (a₂.toList.drop (loA + n + j)).length := by
        rw [List.length_drop, h_lenA₂]; omega
      have hpos₁ : 0 < (a₁.toList.drop (loA + n + j)).length := by
        rw [List.length_drop, h_lenA₁]; omega
      have h1 : (a₂[loA + n + j]'h_a₂_digit_idx)
                  = (a₂.toList.drop (loA + n + j))[0]'hpos₂ := by
        rw [List.getElem_drop]; simp [Array.getElem_toList]
      have h2 : (a₁[loA + n + j]'h_a₁_digit_idx)
                  = (a₁.toList.drop (loA + n + j))[0]'hpos₁ := by
        rw [List.getElem_drop]; simp [Array.getElem_toList]
      rw [h1, h2]
      exact List.getElem_of_eq h_drop_preserved hpos₂
    have h_a₂_digit : (a₂[loA + n + j]'h_a₂_digit_idx).toNat = digit := by
      rw [h_a₂_eq_a₁_at, hdigit_def]
    -- Decomposition of the recursive quotient slice (j+1 limbs at loA+n).
    have h_split_a₂_Q :
        toNatLimbsList ((a₂.toList.drop (loA + n)).take (j + 1))
          = toNatLimbsList ((a₂.toList.drop (loA + n)).take j)
            + (a₂[loA + n + j]'h_a₂_digit_idx).toNat * 2 ^ (64 * j) :=
      toNatLimbsList_drop_take_succ a₂ (loA + n) j h_a₂_digit_idx
    -- Translate IH conclusion in terms of the named variables.
    have h_a₁_full :
        toNatLimbsList ((a₁.toList.drop loA).take (n + j)) = A_low + R * 2 ^ (64 * j) := by
      rw [h_split_a₁, h_a₁_low_value]
    rw [h_a₁_full] at h_recursive_value
    -- Convert h_value_local to use A_top.
    rw [← hA_top_def] at h_value_local
    -- Rewrite the goal using the decompositions.
    rw [h_split_a, h_value_local, h_split_a₂_Q, h_a₂_digit]
    -- Goal: A_low + (digit * B + R) * β^j
    --        = (Q_recur + digit * β^j) * B + a₂R
    -- Hypothesis h_recursive_value: A_low + R * β^j = Q_recur * B + a₂R
    linarith [h_recursive_value]

/-! ### Top-level correctness of `schoolbookDivModLimbs` -/

/-- Helper: with a normalized divisor (`bn1.toNat ≥ 2^63`), the multi-limb
    divisor `B` satisfies `B ≥ 2^(64*n - 1)`, hence `2 * B ≥ 2^(64*n)`. This
    encapsulates the normalization → high-bound implication used in the
    not-`lt` case of `schoolbookDivModLimbs_toNat`. -/
private theorem schoolbookDivModLimbs.divisor_bound (b : Array UInt64) (loB n : Nat)
    (h_n_pos : 0 < n) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat) :
    2 ^ (64 * n - 1) ≤ toNatLimbsList ((b.toList.drop loB).take n) := by
  have h_split := toNatLimbsList_drop_take_split b loB n (n - 1) (by omega) hB
  have h_sub : n - (n - 1) = 1 := by omega
  rw [h_sub] at h_split
  have h_loB_eq : loB + (n - 1) = loB + n - 1 := by omega
  rw [h_loB_eq] at h_split
  rw [h_split]
  -- The 1-limb top slice equals the high limb.
  have h_idx : loB + n - 1 < b.size := by omega
  have h_top_eq : toNatLimbsList ((b.toList.drop (loB + n - 1)).take 1)
                    = (b[loB + n - 1]'h_idx).toNat := by
    have h := toNatLimbsList_drop_take_succ b (loB + n - 1) 0 h_idx
    simpa [toNatLimbsList] using h
  rw [h_top_eq]
  have h_pow_eq : (2 : Nat) ^ (64 * n - 1) = 2 ^ 63 * 2 ^ (64 * (n - 1)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [h_pow_eq]
  calc 2 ^ 63 * 2 ^ (64 * (n - 1))
      ≤ (b[loB + n - 1]'h_idx).toNat * 2 ^ (64 * (n - 1)) :=
        Nat.mul_le_mul_right _ hbn1
    _ ≤ _ := Nat.le_add_left _ _

/-- **Top-level correctness of `schoolbookDivModLimbs`** (BZ Algorithm 1.6).

    Divides the `(n+m)`-limb dividend `A := a[loA : loA+n+m]` by the
    normalized `n`-limb divisor `B := b[loB : loB+n]`, producing:

      - the `n`-limb remainder `R := a'[loA : loA+n]`,
      - the `m` low limbs of the quotient `Q' := a'[loA+n : loA+n+m]`, and
      - the top quotient limb `q_m ∈ {0, 1}` (returned as `res.2`).

    The full division identity is:

      `A = (q_m · β^m + Q') · B + R`     with `R < B` and `q_m ≤ 1`. -/
theorem schoolbookDivModLimbs_toNat (a b : Array UInt64) (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat) :
    let res := schoolbookDivModLimbs a b loA loB n m h_n_pos hA hB hbn1
    toNatLimbsList ((res.1.toList.drop loA).take n)
        < toNatLimbsList ((b.toList.drop loB).take n)
      ∧ toNatLimbsList ((a.toList.drop loA).take (n + m))
          = (res.2.toNat * 2 ^ (64 * m)
             + toNatLimbsList ((res.1.toList.drop (loA + n)).take m))
            * toNatLimbsList ((b.toList.drop loB).take n)
          + toNatLimbsList ((res.1.toList.drop loA).take n)
      ∧ res.2.toNat ≤ 1 := by
  set bn1 : UInt64 := b[loB + n - 1]'(by omega) with hbn1_def
  set inv : UInt64 := UInt64.reciprocal bn1 hbn1 with hinv_def
  set B : Nat := toNatLimbsList ((b.toList.drop loB).take n) with hB_def
  -- B ≥ 2^(64n - 1), hence 2B ≥ β^n.
  have h_B_lb : 2 ^ (64 * n - 1) ≤ B :=
    schoolbookDivModLimbs.divisor_bound b loB n h_n_pos hB hbn1
  have h_B_pos : 0 < B := by
    have : 0 < (2 : Nat) ^ (64 * n - 1) := Nat.two_pow_pos _
    linarith
  have h_2B_lb : 2 ^ (64 * n) ≤ 2 * B := by
    have h_pow_eq : (2 : Nat) ^ (64 * n) = 2 * 2 ^ (64 * n - 1) := by
      have h_eq : 64 * n = (64 * n - 1) + 1 := by omega
      conv_lhs => rw [h_eq]
      rw [Nat.pow_succ]; ring
    rw [h_pow_eq]; linarith
  -- Decompose A = A_low + A_top · β^m.
  set A_low : Nat := toNatLimbsList ((a.toList.drop loA).take m) with hA_low_def
  set A_top : Nat := toNatLimbsList ((a.toList.drop (loA + m)).take n) with hA_top_def
  have h_A_split :
      toNatLimbsList ((a.toList.drop loA).take (n + m))
        = A_low + A_top * 2 ^ (64 * m) := by
    have h := toNatLimbsList_drop_take_split a loA (n + m) m (by omega) (by omega)
    have h_sub : (n + m) - m = n := by omega
    rw [h_sub] at h
    exact h
  have h_A_low_lt : A_low < 2 ^ (64 * m) := by
    have h := toNatLimbsList_lt_pow ((a.toList.drop loA).take m)
    have h_len : ((a.toList.drop loA).take m).length ≤ m := by
      rw [List.length_take]; exact Nat.min_le_left _ _
    calc A_low
        < 2 ^ (64 * ((a.toList.drop loA).take m).length) := h
      _ ≤ 2 ^ (64 * m) := Nat.pow_le_pow_right (by norm_num)
                            (Nat.mul_le_mul_left 64 h_len)
  have h_A_top_lt : A_top < 2 ^ (64 * n) := by
    have h := toNatLimbsList_lt_pow ((a.toList.drop (loA + m)).take n)
    have h_len : ((a.toList.drop (loA + m)).take n).length ≤ n := by
      rw [List.length_take]; exact Nat.min_le_left _ _
    calc A_top
        < 2 ^ (64 * ((a.toList.drop (loA + m)).take n).length) := h
      _ ≤ 2 ^ (64 * n) := Nat.pow_le_pow_right (by norm_num)
                            (Nat.mul_le_mul_left 64 h_len)
  -- Translate `compareLimbs a b (loA + m) loB n` into a Nat comparison.
  have h_cmp_eq := compareLimbs_eq_compare_slice a b (loA + m) loB n
                     (by omega) hB
  rw [← hA_top_def, ← hB_def] at h_cmp_eq
  -- Unfold the definition.
  unfold schoolbookDivModLimbs
  simp only
  by_cases h_cmp_lt :
      compareLimbs a b (loA + m) loB n (by omega) hB = Ordering.lt
  · -- Lt case: q_m = 0, no subSameLengthLimbs.
    rw [if_pos h_cmp_lt]
    have h_top_lt_B : A_top < B := by
      rw [h_cmp_eq] at h_cmp_lt
      exact Nat.compare_eq_lt.mp h_cmp_lt
    -- BZ invariant for go: A < β^m · B.
    have h_BZ : toNatLimbsList ((a.toList.drop loA).take (n + m))
                  < 2 ^ (64 * m) * B := by
      rw [h_A_split]
      have h1 : A_top * 2 ^ (64 * m) ≤ (B - 1) * 2 ^ (64 * m) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : A_low + (B - 1) * 2 ^ (64 * m) < B * 2 ^ (64 * m) := by
        have : (B - 1) * 2 ^ (64 * m) + 2 ^ (64 * m) = B * 2 ^ (64 * m) := by
          have : B = (B - 1) + 1 := by omega
          conv_rhs => rw [this]
          ring
        omega
      have h_comm : B * 2 ^ (64 * m) = 2 ^ (64 * m) * B := by ring
      linarith
    have hbn1_eq : ∃ h_idx : loB + n - 1 < b.size,
        bn1 = b[loB + n - 1]'h_idx := ⟨by omega, hbn1_def⟩
    have hinv_ex : ∃ h, inv = UInt64.reciprocal bn1 h := ⟨hbn1, hinv_def⟩
    have h_go := schoolbookDivModLimbs.go_toNat a b loA loB n m bn1 inv
                   (by omega) hB h_n_pos hbn1_eq hbn1 hinv_ex h_B_pos h_BZ
    simp only at h_go
    obtain ⟨h_R_lt, h_value⟩ := h_go
    refine ⟨?_, ?_, ?_⟩
    · exact h_R_lt
    · -- Goal: ... = (0 * β^m + Q') · B + R = Q' · B + R = h_value's RHS.
      have h_zero : (0 : UInt64).toNat = 0 := by decide
      rw [h_zero, Nat.zero_mul, Nat.zero_add]
      exact h_value
    · have h_zero : (0 : UInt64).toNat = 0 := by decide
      rw [h_zero]; omega
  · -- Not-Lt case: A_top ≥ B; subtract B from top, then go with q_m = 1.
    rw [if_neg h_cmp_lt]
    have h_top_ge_B : B ≤ A_top := by
      rw [h_cmp_eq] at h_cmp_lt
      cases h : Ord.compare A_top B with
      | lt => rw [h] at h_cmp_lt; exact absurd rfl h_cmp_lt
      | eq => exact (Nat.compare_eq_eq.mp h).symm.le
      | gt => exact (Nat.compare_eq_gt.mp h).le
    -- subSameLengthLimbs at (loA + m) subtracts B from A_top.
    set r := subSameLengthLimbs a b (loA + m) loB n (by omega) hB with hr_def
    have h_r_size : r.1.size = a.size := by
      rw [hr_def]; exact subSameLengthLimbs_size _ _ _ _ _ _ _
    have h_sub_toNat := subSameLengthLimbs_toNat a b (loA + m) loB n
                          (by omega) hB
    rw [← hr_def] at h_sub_toNat
    simp only at h_sub_toNat
    -- A_top + c · β^n = A_top' + B  where A_top' is r.1's slice at offset (loA+m).
    set A_top' : Nat := toNatLimbsList ((r.1.toList.drop (loA + m)).take n)
      with hA_top'_def
    -- c = false because A_top ≥ B.
    have h_c_false : r.2 = false := by
      cases h_c : r.2 with
      | false => rfl
      | true =>
        exfalso
        rw [h_c] at h_sub_toNat
        simp at h_sub_toNat
        -- A_top + 2^(64n) = A_top' + B
        -- A_top' < 2^(64n) (always), so A_top + 2^(64n) < 2^(64n) + B → A_top < B.
        have h_A_top'_lt : A_top' < 2 ^ (64 * n) := by
          have h := toNatLimbsList_lt_pow ((r.1.toList.drop (loA + m)).take n)
          have h_len : ((r.1.toList.drop (loA + m)).take n).length ≤ n := by
            rw [List.length_take]; exact Nat.min_le_left _ _
          calc A_top'
              < 2 ^ (64 * ((r.1.toList.drop (loA + m)).take n).length) := h
            _ ≤ 2 ^ (64 * n) := Nat.pow_le_pow_right (by norm_num)
                                  (Nat.mul_le_mul_left 64 h_len)
        omega
    rw [h_c_false] at h_sub_toNat
    simp at h_sub_toNat
    -- Now h_sub_toNat : A_top = A_top' + B, so A_top' = A_top - B.
    have h_A_top'_eq : A_top' = A_top - B := by omega
    -- A_top' < B (from A_top < 2B).
    have h_A_top'_lt_B : A_top' < B := by
      rw [h_A_top'_eq]; omega
    -- Prefix preservation: r.1's low slice (drop loA).take m = a's.
    have h_take_eq : r.1.toList.take (loA + m) = a.toList.take (loA + m) := by
      have h_take := subSameLengthLimbs.go_toList_take_le b (loA + m) loB n
                       a 0 false (by omega) hB (loA + m) (by omega)
      show (subSameLengthLimbs.go b (loA + m) loB n a 0 false (by omega) hB).1.toList.take
              (loA + m) = a.toList.take (loA + m)
      exact h_take
    have h_low_preserved :
        (r.1.toList.drop loA).take m = (a.toList.drop loA).take m := by
      have h1 : (r.1.toList.drop loA).take m
          = (r.1.toList.take (loA + m)).drop loA := by
        rw [List.take_drop, List.drop_take]
      have h2 : (a.toList.drop loA).take m
          = (a.toList.take (loA + m)).drop loA := by
        rw [List.take_drop, List.drop_take]
      rw [h1, h_take_eq, ← h2]
    -- Decomposition of r.1's (n+m)-limb slice.
    have h_r1_split :
        toNatLimbsList ((r.1.toList.drop loA).take (n + m))
          = A_low + A_top' * 2 ^ (64 * m) := by
      have h := toNatLimbsList_drop_take_split r.1 loA (n + m) m (by omega)
                  (by rw [h_r_size]; omega)
      have h_sub : (n + m) - m = n := by omega
      rw [h_sub] at h
      rw [h]
      have h_low : toNatLimbsList ((r.1.toList.drop loA).take m)
                     = A_low := by rw [h_low_preserved, hA_low_def]
      rw [h_low]
    -- BZ invariant for go on r.1.
    have h_BZ : toNatLimbsList ((r.1.toList.drop loA).take (n + m))
                  < 2 ^ (64 * m) * B := by
      rw [h_r1_split]
      have h1 : A_top' * 2 ^ (64 * m) ≤ (B - 1) * 2 ^ (64 * m) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : A_low + (B - 1) * 2 ^ (64 * m) < B * 2 ^ (64 * m) := by
        have h_eq : (B - 1) * 2 ^ (64 * m) + 2 ^ (64 * m) = B * 2 ^ (64 * m) := by
          have : B = (B - 1) + 1 := by omega
          conv_rhs => rw [this]
          ring
        omega
      have h_comm : B * 2 ^ (64 * m) = 2 ^ (64 * m) * B := by ring
      linarith
    have hbn1_eq : ∃ h_idx : loB + n - 1 < b.size,
        bn1 = b[loB + n - 1]'h_idx := ⟨by omega, hbn1_def⟩
    have hinv_ex : ∃ h, inv = UInt64.reciprocal bn1 h := ⟨hbn1, hinv_def⟩
    have h_go := schoolbookDivModLimbs.go_toNat r.1 b loA loB n m bn1 inv
                   (by rw [h_r_size]; omega) hB h_n_pos hbn1_eq hbn1 hinv_ex
                   h_B_pos h_BZ
    simp only at h_go
    obtain ⟨h_R_lt, h_value⟩ := h_go
    refine ⟨?_, ?_, ?_⟩
    · exact h_R_lt
    · -- A = A_low + A_top·β^m = (A_low + A_top'·β^m) + B·β^m = (Q' + β^m)·B + R
      --   = (1·β^m + Q')·B + R.
      have h_one : (1 : UInt64).toNat = 1 := by decide
      rw [h_one, Nat.one_mul]
      rw [h_A_split]
      rw [show A_top = A_top' + B from by omega]
      have h_eq : A_low + (A_top' + B) * 2 ^ (64 * m)
          = (A_low + A_top' * 2 ^ (64 * m)) + B * 2 ^ (64 * m) := by ring
      rw [h_eq]
      rw [show A_low + A_top' * 2 ^ (64 * m)
            = toNatLimbsList ((r.1.toList.drop loA).take (n + m)) from
              h_r1_split.symm]
      rw [h_value]
      ring
    · show (1 : UInt64).toNat ≤ 1
      decide

end Azurite.AzNat
