/-
  Equivalence proof: `AzMatrix.bareissDet M = Matrix.det M.toFn` over an
  integral domain with `ExactDiv` (which now bundles the lawfulness field).

  The fraction-free Dodgson-Jordan-Bareiss algorithm (`bareissDet`) computes
  the determinant via the recurrence (8.9), using BPR Proposition 8.20
  (`bareissMinor_recurrence`) to keep each intermediate division exact. The
  proof tracks a per-step invariant relating the current matrix `M_curr` to a
  *reference matrix* `M_ref` (the original `M` after the cumulative column
  swaps performed so far):

  * After `k` Bareiss-elimination steps, `M_curr[i][j]` equals the Bareiss
    minor `b^{(k)}_{i,j}(M_ref)` for `i, j ≥ k`.
  * The divisor parameter `b_prev` carries the previous principal minor
    `det(M_ref_{[0..k-1] × [0..k-1]})`.
  * The first `k` Gauss pivots of `M_ref` are nonzero (the hypothesis used
    by BPR Proposition 8.20 to drive the recurrence).

  Each `bareissEliminate` step advances the invariant from level `k` to
  `k + 1` via Proposition 8.20. Each column swap updates `M_ref` accordingly
  and flips its determinant, which the `(-1)^s` factor in the output formula
  (8.10) cancels. The terminal base case `start = n - 1` reads off
  `M_curr[n-1][n-1] = b^{(n-1)}_{n-1,n-1}(M_ref) = det(M_ref)`, completing
  the proof.

  The argument lifts the Field-version Prop 8.20 (`bareissMinor_recurrence`)
  and the Field-version abort-case argument to the integral-domain setting
  via the embedding `D → FractionRing D` (a field) — injective for integral
  domains by `IsFractionRing.injective`. At each `bareissEliminate` step,
  the `ExactDiv` lawfulness field together with the lifted Prop 8.20
  guarantees the divisor exactly divides the numerator, so the algorithm
  stays in `D`.
-/
import Azurite.AzMatrix.BareissDet
import Azurite.AzMatrix.Equiv.Bareiss
import Azurite.AzMatrix.Equiv.Det
import Azurite.Algorithm.ExactDiv
import Mathlib.RingTheory.Localization.FractionRing

set_option linter.unusedSectionVars false

namespace Azurite

variable {D : Type _} [CommRing D] [IsDomain D] [DecidableEq D]
         [Azurite.ExactDiv D]
         {n : Nat}

/-! ### Entrywise unfolding of `bareissEliminate` -/

omit [DecidableEq D] in
theorem AzMatrix.toFn_bareissEliminate
    (M : AzMatrix D n n) (k : Fin n) (b_prev : D) (i j : Fin n) :
    (M.bareissEliminate k b_prev).toFn i j =
      if i.val ≤ k.val then M.toFn i j
      else if j.val < k.val then M.toFn i j
      else if j = k then 0
      else Azurite.ExactDiv.exactDiv
        (M.toFn k k * M.toFn i j - M.toFn i k * M.toFn k j) b_prev := by
  show (AzMatrix.bareissEliminate M k b_prev).toFn i j = _
  unfold AzMatrix.bareissEliminate
  rw [AzMatrix.toFn_ofFn]
  rfl

/-! ### `bareissEliminate` preserves `PartialZero` -/

omit [DecidableEq D] in
theorem AzMatrix.bareissEliminate_preservesPartialZero
    (M : AzMatrix D n n) (start : Nat) (h_lt : start < n) (b_prev : D)
    (h_inv : M.PartialZero start) :
    (M.bareissEliminate ⟨start, h_lt⟩ b_prev).PartialZero (start + 1) := by
  intro i j h_lt_ij h_bnd
  rw [AzMatrix.toFn_bareissEliminate]
  by_cases h_i_le : i.val ≤ start
  · rw [if_pos h_i_le]
    have h_j_lt_start : j.val < start := by omega
    exact h_inv i j h_lt_ij h_j_lt_start
  · rw [if_neg h_i_le]
    by_cases h_j_lt : j.val < start
    · rw [if_pos h_j_lt]
      exact h_inv i j h_lt_ij h_j_lt
    · rw [if_neg h_j_lt]
      have h_j_eq : j.val = start := by omega
      have h_j_kp : j = ⟨start, h_lt⟩ := Fin.ext h_j_eq
      rw [if_pos h_j_kp]

/-! ### Determinant flips sign under a column swap (Domain version) -/

omit [DecidableEq D] [Azurite.ExactDiv D] in
theorem AzMatrix.det_swapCols_domain
    (M : AzMatrix D n n) (j₁ j₂ : Fin n) (h_neq : j₁ ≠ j₂) :
    Matrix.det (M.swapCols j₁ j₂).toFn = -Matrix.det M.toFn := by
  rw [AzMatrix.toFn_swapCols_eq_submatrix]
  rw [show Matrix.submatrix M.toFn id ⇑(Equiv.swap j₁ j₂)
      = Matrix.submatrix (Matrix.of M.toFn) id ⇑(Equiv.swap j₁ j₂) from rfl]
  rw [Matrix.det_permute']
  rw [Equiv.Perm.sign_swap h_neq]
  push_cast
  rw [neg_one_mul]
  rfl

/-! ### Column swap preserves low-level `principalMinor`s

  The principal minor at level `ℓ < k` is the determinant of the top-left
  `(ℓ+1)×(ℓ+1)` block, which uses only columns `0..ℓ`. A column swap at
  columns `k` and `j` with both `≥ k > ℓ` leaves those columns alone, so
  the principal minor is unchanged. (Field-free; pure submatrix argument.) -/

omit [DecidableEq D] [Azurite.ExactDiv D] in
theorem AzMatrix.principalMinor_swapCols_low_level
    (M : AzMatrix D n n) (k : Nat) (hk : k < n) (j : Fin n) (hjk : k < j.val)
    (ℓ : Nat) (hℓ : ℓ < k) :
    (M.swapCols ⟨k, hk⟩ j).principalMinor ℓ (by omega) =
      M.principalMinor ℓ (by omega) := by
  rw [AzMatrix.principalMinor_eq_top_left_det,
      AzMatrix.principalMinor_eq_top_left_det]
  congr 1
  funext i' j'
  show (M.swapCols ⟨k, hk⟩ j).toFn
      (Fin.castLE (Nat.succ_le_of_lt (show ℓ < n by omega)) i')
      (Fin.castLE (Nat.succ_le_of_lt (show ℓ < n by omega)) j')
    = M.toFn (Fin.castLE (Nat.succ_le_of_lt (show ℓ < n by omega)) i')
      (Fin.castLE (Nat.succ_le_of_lt (show ℓ < n by omega)) j')
  rw [AzMatrix.toFn_swapCols]
  set j'_lift : Fin n := Fin.castLE (Nat.succ_le_of_lt (show ℓ < n by omega)) j'
    with hj'_lift
  have h_j'_val : j'_lift.val = j'.val := rfl
  have h_neq_kp : j'_lift ≠ ⟨k, hk⟩ := by
    intro h_eq
    have : j'_lift.val = k := congrArg Fin.val h_eq
    rw [h_j'_val] at this; have := j'.isLt; omega
  have h_neq_j : j'_lift ≠ j := by
    intro h_eq
    have : j'_lift.val = j.val := congrArg Fin.val h_eq
    rw [h_j'_val] at this; have := j'.isLt; omega
  rw [if_neg h_neq_kp, if_neg h_neq_j]

/-! ### `bareissMinor` under column swap

  Swapping columns `k` and `j` (with `j > k`) of the reference matrix
  permutes the last column-index argument of `bareissMinor` according to
  the same swap. Columns `0, …, k-1` of the Bareiss block are unaffected
  (the swap targets are both `≥ k`), while the final column is column `j'`
  of the swapped matrix, i.e., column `swap(j')` of the original. -/

omit [DecidableEq D] in
theorem AzMatrix.bareissIdx_swap_comp
    {k : Nat} (hk : k ≤ n) (j j' : Fin n) (h_j_gt : k < j.val) :
    (Equiv.swap (⟨k, lt_trans h_j_gt j.isLt⟩ : Fin n) j) ∘
        AzMatrix.bareissIdx k hk j' =
      AzMatrix.bareissIdx k hk
        (Equiv.swap (⟨k, lt_trans h_j_gt j.isLt⟩ : Fin n) j j') := by
  funext l'
  show (Equiv.swap _ j) (AzMatrix.bareissIdx k hk j' l') = _
  by_cases h : l'.val < k
  · -- l' < k: bareissIdx maps to ⟨l'.val, _⟩, neither k nor j
    rw [AzMatrix.bareissIdx_val_of_lt hk j' l' h]
    rw [AzMatrix.bareissIdx_val_of_lt hk _ l' h]
    have h_neq_k : (⟨l'.val, lt_of_lt_of_le h hk⟩ : Fin n) ≠
        ⟨k, lt_trans h_j_gt j.isLt⟩ := by
      intro h_eq; have : l'.val = k := congrArg Fin.val h_eq; omega
    have h_neq_j : (⟨l'.val, lt_of_lt_of_le h hk⟩ : Fin n) ≠ j := by
      intro h_eq; have : l'.val = j.val := congrArg Fin.val h_eq; omega
    rw [Equiv.swap_apply_of_ne_of_ne h_neq_k h_neq_j]
  · -- l' = Fin.last k: bareissIdx maps to j'
    have h_eq : l'.val = k := by have := l'.isLt; omega
    rw [AzMatrix.bareissIdx_of_val_eq hk j' l' h_eq]
    rw [AzMatrix.bareissIdx_of_val_eq hk _ l' h_eq]

omit [DecidableEq D] in
theorem AzMatrix.bareissMinor_swapCols
    (M : AzMatrix D n n) (k : Nat) (hk : k ≤ n) (j : Fin n) (h_j_gt : k < j.val)
    (i j' : Fin n) :
    (M.swapCols ⟨k, lt_trans h_j_gt j.isLt⟩ j).bareissMinor k hk i j' =
      M.bareissMinor k hk i (Equiv.swap
        (⟨k, lt_trans h_j_gt j.isLt⟩ : Fin n) j j') := by
  unfold AzMatrix.bareissMinor
  rw [AzMatrix.toFn_bareissBlock, AzMatrix.toFn_bareissBlock,
      AzMatrix.toFn_swapCols_eq_submatrix]
  show Matrix.det (Matrix.submatrix M.toFn
      (id ∘ AzMatrix.bareissIdx k hk i)
      (Equiv.swap _ j ∘ AzMatrix.bareissIdx k hk j')) = _
  rw [Function.id_comp]
  rw [AzMatrix.bareissIdx_swap_comp hk j j' h_j_gt]

/-! ### Level-0 and level-1 Bareiss minors -/

omit [DecidableEq D] in
/-- `bareissMinor M 0 i j = M[i][j]` (determinant of a 1×1 block). -/
theorem AzMatrix.bareissMinor_zero (M : AzMatrix D n n) (h_n : 0 ≤ n)
    (i j : Fin n) : M.bareissMinor 0 h_n i j = M.toFn i j := by
  unfold AzMatrix.bareissMinor
  rw [AzMatrix.toFn_bareissBlock]
  rw [Matrix.det_fin_one]
  show M.toFn (AzMatrix.bareissIdx 0 h_n i 0) (AzMatrix.bareissIdx 0 h_n j 0)
    = M.toFn i j
  rw [AzMatrix.bareissIdx_of_val_eq h_n i (0 : Fin 1) (by decide)]
  rw [AzMatrix.bareissIdx_of_val_eq h_n j (0 : Fin 1) (by decide)]

omit [DecidableEq D] in
/-- 2×2 expansion of `bareissMinor M 1`. -/
theorem AzMatrix.bareissMinor_one (M : AzMatrix D n n) (h_n : 1 ≤ n)
    (i j : Fin n) (_hi : 0 < i.val) (_hj : 0 < j.val) :
    M.bareissMinor 1 h_n i j =
      M.toFn ⟨0, by omega⟩ ⟨0, by omega⟩ * M.toFn i j -
        M.toFn i ⟨0, by omega⟩ * M.toFn ⟨0, by omega⟩ j := by
  unfold AzMatrix.bareissMinor
  rw [AzMatrix.toFn_bareissBlock, Matrix.det_fin_two]
  show M.toFn (AzMatrix.bareissIdx 1 h_n i 0) (AzMatrix.bareissIdx 1 h_n j 0)
        * M.toFn (AzMatrix.bareissIdx 1 h_n i 1) (AzMatrix.bareissIdx 1 h_n j 1)
      - M.toFn (AzMatrix.bareissIdx 1 h_n i 0) (AzMatrix.bareissIdx 1 h_n j 1)
        * M.toFn (AzMatrix.bareissIdx 1 h_n i 1) (AzMatrix.bareissIdx 1 h_n j 0)
    = _
  have h0_eq : AzMatrix.bareissIdx 1 h_n i (0 : Fin 2) = ⟨0, by omega⟩ :=
    AzMatrix.bareissIdx_val_of_lt h_n i 0 (by decide)
  have h0_eq_j : AzMatrix.bareissIdx 1 h_n j (0 : Fin 2) = ⟨0, by omega⟩ :=
    AzMatrix.bareissIdx_val_of_lt h_n j 0 (by decide)
  have h1_eq : AzMatrix.bareissIdx 1 h_n i (1 : Fin 2) = i :=
    AzMatrix.bareissIdx_of_val_eq h_n i 1 (by decide)
  have h1_eq_j : AzMatrix.bareissIdx 1 h_n j (1 : Fin 2) = j :=
    AzMatrix.bareissIdx_of_val_eq h_n j 1 (by decide)
  rw [h0_eq, h0_eq_j, h1_eq, h1_eq_j]
  ring

/-! ### Domain version of `bareissMinor_recurrence` (Prop 8.20)

  Lifted from the Field version via `algebraMap D (FractionRing D)`. The
  hypothesis is reformulated in terms of `principalMinor` nonzero, which is
  the natural condition over a domain (gaussSteps doesn't make sense
  without field division). -/

omit [DecidableEq D] [Azurite.ExactDiv D] in
/-- Lifting: `algebraMap` commutes with `bareissMinor`. -/
private theorem AzMatrix.algebraMap_bareissMinor
    {E : Type _} [CommRing E] (f : D →+* E)
    (M : AzMatrix D n n) (k : Nat) (hk : k ≤ n) (i j : Fin n) :
    f (M.bareissMinor k hk i j) =
      (M.map f).bareissMinor k hk i j := by
  unfold AzMatrix.bareissMinor
  rw [AzMatrix.toFn_bareissBlock, AzMatrix.toFn_bareissBlock]
  rw [RingHom.map_det]
  congr 1
  funext i' j'
  show f (M.toFn (AzMatrix.bareissIdx k hk i i') (AzMatrix.bareissIdx k hk j j'))
    = (M.map ⇑f).toFn (AzMatrix.bareissIdx k hk i i') (AzMatrix.bareissIdx k hk j j')
  rw [AzMatrix.toFn_map]

omit [DecidableEq D] [Azurite.ExactDiv D] in
/-- Lifting: `algebraMap` commutes with `principalMinor`. -/
private theorem AzMatrix.algebraMap_principalMinor
    {E : Type _} [CommRing E] (f : D →+* E)
    (M : AzMatrix D n n) (k : Nat) (hk : k < n) :
    f (M.principalMinor k hk) = (M.map f).principalMinor k hk :=
  M.algebraMap_bareissMinor f k hk.le ⟨k, hk⟩ ⟨k, hk⟩

omit [Azurite.ExactDiv D] in
/-- Field equivalence: in a field, principal minors nonzero at all levels
    `ℓ ≤ k` implies the first `k + 1` Gauss pivots are nonzero. By induction:
    for each `ℓ`, the level-`ℓ` Gauss pivot is the ratio of `principalMinor ℓ`
    to `pivotProd ℓ`, both nonzero. -/
private theorem AzMatrix.gauss_pivots_nz_of_principalMinors_nz
    {F : Type _} [Field F] [DecidableEq F] (N : AzMatrix F n n) :
    ∀ k : Nat, (∀ ℓ : Nat, ℓ ≤ k → (h : ℓ < n) → N.principalMinor ℓ h ≠ 0) →
    ∀ ℓ : Nat, ℓ ≤ k → (h : ℓ < n) →
      (N.gaussSteps ℓ).toFn ⟨ℓ, h⟩ ⟨ℓ, h⟩ ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro h_pms ℓ hℓk h
    have hℓ0 : ℓ = 0 := by omega
    subst hℓ0
    have h_pm_nz := h_pms 0 (by omega) h
    rw [N.principalMinor_eq_pivotProd 0 h (fun _ hℓ _ => absurd hℓ (Nat.not_lt_zero _)),
        N.pivotProd_succ 0 h] at h_pm_nz
    exact right_ne_zero_of_mul h_pm_nz
  | succ k ih =>
    intro h_pms ℓ hℓk h
    by_cases h_lt : ℓ ≤ k
    · exact ih (fun ℓ' hℓ' h' => h_pms ℓ' (by omega) h') ℓ h_lt h
    · have hℓ_eq : ℓ = k + 1 := by omega
      subst hℓ_eq
      have h_prev_piv : ∀ ℓ' : Nat, ℓ' < k + 1 → (h' : ℓ' < n) →
          (N.gaussSteps ℓ').toFn ⟨ℓ', h'⟩ ⟨ℓ', h'⟩ ≠ 0 :=
        fun ℓ' hℓ' h' => ih (fun ℓ'' hℓ'' h'' => h_pms ℓ'' (by omega) h'')
          ℓ' (by omega) h'
      have h_pm_nz := h_pms (k + 1) (by omega) h
      rw [N.principalMinor_eq_pivotProd (k + 1) h h_prev_piv,
          N.pivotProd_succ (k + 1) h] at h_pm_nz
      exact right_ne_zero_of_mul h_pm_nz

/-- **BPR Proposition 8.20 over a domain.** Same identity as the Field
    version `bareissMinor_recurrence`, but stated with `principalMinor`
    nonzero (the natural condition over a domain). Proven by lifting to
    `FractionRing D`. -/
theorem AzMatrix.bareissMinor_recurrence_domain
    (M : AzMatrix D n n) (k : Nat) (i j : Fin n)
    (hi : k + 2 ≤ i.val) (hj : k + 2 ≤ j.val)
    (h_pms : ∀ ℓ : Nat, ℓ ≤ k + 1 → (h : ℓ < n) →
      M.principalMinor ℓ h ≠ 0) :
    M.bareissMinor (k + 2) (by have := i.isLt; omega) i j *
        M.principalMinor k (by have := i.isLt; omega) =
      M.principalMinor (k + 1) (by have := i.isLt; omega) *
          M.bareissMinor (k + 1) (by have := i.isLt; omega) i j -
        M.bareissMinor (k + 1) (by have := i.isLt; omega) i
          ⟨k + 1, by have := i.isLt; omega⟩ *
          M.bareissMinor (k + 1) (by have := i.isLt; omega)
            ⟨k + 1, by have := i.isLt; omega⟩ j := by
  classical
  let K := FractionRing D
  let f : D →+* K := algebraMap D K
  have h_inj : Function.Injective f := IsFractionRing.injective D K
  -- Lift principalMinors to K and convert to Gauss pivots nonzero.
  have h_pms_K : ∀ ℓ : Nat, ℓ ≤ k + 1 → (h : ℓ < n) →
      (M.map f).principalMinor ℓ h ≠ 0 := by
    intro ℓ hℓ h
    rw [← M.algebraMap_principalMinor f ℓ h]
    intro h_eq
    have : M.principalMinor ℓ h = 0 := h_inj (by rw [h_eq, map_zero])
    exact h_pms ℓ hℓ h this
  have h_piv_K : ∀ ℓ : Nat, ℓ ≤ k + 1 → (h : ℓ < n) →
      ((M.map f).gaussSteps ℓ).toFn ⟨ℓ, h⟩ ⟨ℓ, h⟩ ≠ 0 :=
    (M.map f).gauss_pivots_nz_of_principalMinors_nz (k + 1) h_pms_K
  have h_K := (M.map f).bareissMinor_recurrence k i j hi hj h_piv_K
  -- Pull back to D via algebraMap injectivity.
  apply h_inj
  rw [map_mul, map_sub, map_mul, map_mul]
  rw [M.algebraMap_bareissMinor f, M.algebraMap_principalMinor f,
      M.algebraMap_principalMinor f, M.algebraMap_bareissMinor f,
      M.algebraMap_bareissMinor f, M.algebraMap_bareissMinor f]
  exact h_K

/-! ### The transition lemma: one `bareissEliminate` step advances the level

  If `M_curr` matches `bareissMinor M_ref k` on the lower-right block and
  `b_prev = principalMinor M_ref (k-1)` (with `b_prev = 1` at `k = 0`), then
  applying one `bareissEliminate` step produces the level-`(k+1)` Bareiss
  minor of `M_ref` on the next-smaller lower-right block. This is the core
  step that drives the algorithm. -/

theorem AzMatrix.bareissEliminate_advances_level
    (M_ref M_curr : AzMatrix D n n) (k : Nat) (hk : k + 1 < n)
    (b_prev : D)
    (h_inv : ∀ i j : Fin n, k ≤ i.val → k ≤ j.val →
      M_curr.toFn i j = M_ref.bareissMinor k (by omega) i j)
    (h_b_prev : if hk0 : 0 < k then
        b_prev = M_ref.principalMinor (k - 1) (by omega)
      else b_prev = 1)
    (h_pms : ∀ ℓ : Nat, ℓ ≤ k → (h : ℓ < n) →
      M_ref.principalMinor ℓ h ≠ 0)
    (i j : Fin n) (hi : k + 1 ≤ i.val) (hj : k + 1 ≤ j.val) :
    (M_curr.bareissEliminate ⟨k, by omega⟩ b_prev).toFn i j =
      M_ref.bareissMinor (k + 1) hk.le i j := by
  rw [AzMatrix.toFn_bareissEliminate]
  have h_not_i_le : ¬ i.val ≤ k := by omega
  rw [if_neg h_not_i_le]
  have h_not_j_lt : ¬ j.val < k := by omega
  rw [if_neg h_not_j_lt]
  have h_j_neq_kp : j ≠ ⟨k, by omega⟩ := by
    intro h_eq; have : j.val = k := congrArg Fin.val h_eq; omega
  rw [if_neg h_j_neq_kp]
  have h_kk := h_inv ⟨k, by omega⟩ ⟨k, by omega⟩ (le_refl _) (le_refl _)
  have h_ij := h_inv i j (by omega) (by omega)
  have h_ik := h_inv i ⟨k, by omega⟩ (by omega) (le_refl _)
  have h_kj := h_inv ⟨k, by omega⟩ j (le_refl _) (by omega)
  rw [h_kk, h_ij, h_ik, h_kj]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · -- k = 0 case: divisor is 1, use 2×2 direct formula.
    subst hk0
    simp only [show ¬ (0 < 0) from by omega, dite_false] at h_b_prev
    rw [h_b_prev]
    have hn_1 : 1 ≤ n := by omega
    rw [M_ref.bareissMinor_zero (by omega) ⟨0, by omega⟩ ⟨0, by omega⟩]
    rw [M_ref.bareissMinor_zero (by omega) i j]
    rw [M_ref.bareissMinor_zero (by omega) i ⟨0, by omega⟩]
    rw [M_ref.bareissMinor_zero (by omega) ⟨0, by omega⟩ j]
    rw [M_ref.bareissMinor_one hn_1 i j (by omega) (by omega)]
    -- exactDiv X 1 = X by LawfulExactDiv.
    have h_one_ne : (1 : D) ≠ 0 := one_ne_zero
    have h_dvd_one : (1 : D) ∣
        (M_ref.toFn ⟨0, by omega⟩ ⟨0, by omega⟩ * M_ref.toFn i j -
          M_ref.toFn i ⟨0, by omega⟩ * M_ref.toFn ⟨0, by omega⟩ j) :=
      ⟨_, (one_mul _).symm⟩
    have h_law := Azurite.ExactDiv.exactDiv_mul_self
      (M_ref.toFn ⟨0, by omega⟩ ⟨0, by omega⟩ * M_ref.toFn i j -
        M_ref.toFn i ⟨0, by omega⟩ * M_ref.toFn ⟨0, by omega⟩ j)
      1 h_dvd_one h_one_ne
    rw [mul_one] at h_law
    exact h_law
  · -- k ≥ 1: apply Domain Prop 8.20 + LawfulExactDiv + domain cancellation.
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk0)
    simp only [show 0 < k' + 1 from by omega, dite_true] at h_b_prev
    have h_pms' : ∀ ℓ : Nat, ℓ ≤ k' + 1 → (h : ℓ < n) →
        M_ref.principalMinor ℓ h ≠ 0 :=
      fun ℓ hℓ h => h_pms ℓ hℓ h
    -- Convert `k'.succ` to `k' + 1` throughout.
    change Azurite.ExactDiv.exactDiv
        (M_ref.bareissMinor (k' + 1) _ ⟨k' + 1, _⟩ ⟨k' + 1, _⟩ *
          M_ref.bareissMinor (k' + 1) _ i j -
          M_ref.bareissMinor (k' + 1) _ i ⟨k' + 1, _⟩ *
          M_ref.bareissMinor (k' + 1) _ ⟨k' + 1, _⟩ j) b_prev =
        M_ref.bareissMinor (k' + 2) _ i j
    have h_rec := M_ref.bareissMinor_recurrence_domain k' i j hi hj h_pms'
    -- Identify b_prev = principalMinor k'.
    have h_pm_eq : M_ref.principalMinor (k' + 1 - 1)
        (show k' + 1 - 1 < n by omega) =
        M_ref.principalMinor k' (by omega) := by
      have h_sub : k' + 1 - 1 = k' := by omega
      simp only [h_sub]
    rw [h_pm_eq] at h_b_prev
    rw [h_b_prev]
    -- (k'+1, k'+1) entry IS principalMinor (k'+1).
    show Azurite.ExactDiv.exactDiv
        (M_ref.principalMinor (k' + 1) _ *
          M_ref.bareissMinor (k' + 1) _ i j -
          M_ref.bareissMinor (k' + 1) _ i ⟨k' + 1, _⟩ *
          M_ref.bareissMinor (k' + 1) _ ⟨k' + 1, _⟩ j)
        (M_ref.principalMinor k' _) =
        M_ref.bareissMinor (k' + 2) _ i j
    have h_pm_nz : M_ref.principalMinor k' (by omega) ≠ 0 :=
      h_pms k' (by omega) (by omega)
    set numerator : D :=
      M_ref.principalMinor (k' + 1) (by omega) *
        M_ref.bareissMinor (k' + 1) (by omega) i j -
      M_ref.bareissMinor (k' + 1) (by omega) i ⟨k' + 1, by omega⟩ *
        M_ref.bareissMinor (k' + 1) (by omega) ⟨k' + 1, by omega⟩ j
      with h_num
    set p_minor : D := M_ref.principalMinor k' (by omega) with h_pmin
    set b_minor : D := M_ref.bareissMinor (k' + 2) (by omega) i j with h_bmin
    have h_eq_num : numerator = b_minor * p_minor := by
      rw [h_num, h_bmin, h_pmin]; exact h_rec.symm
    have h_dvd : p_minor ∣ numerator :=
      ⟨b_minor, by rw [h_eq_num]; ring⟩
    have h_law := Azurite.ExactDiv.exactDiv_mul_self numerator p_minor h_dvd h_pm_nz
    show Azurite.ExactDiv.exactDiv numerator p_minor = b_minor
    apply mul_right_cancel₀ h_pm_nz
    rw [h_law, h_eq_num]

/-! ### Bareiss invariant -/

/-- The full invariant maintained by `bareissAux`. At step `start`, the
    current matrix `M_curr` has the level-`start` Bareiss minors of a
    *reference matrix* `M_ref` (the original matrix with cumulative column
    swaps applied) on its lower-right block, with `b_prev` carrying the
    previous principal minor. -/
structure AzMatrix.BareissInv (M_curr M_ref : AzMatrix D n n)
    (start : Nat) (b_prev : D) : Prop where
  /-- `start ≤ n - 1` (in truncated `Nat`): for `n = 0` this gives `start = 0`,
      and for `n ≥ 1` it gives `start ≤ n - 1` — matching the algorithm flow,
      which only ever has `start` reaching `n - 1`. -/
  start_le_pred : start ≤ n - 1
  partialZero : M_curr.PartialZero start
  bareiss : ∀ i j : Fin n, start ≤ i.val → start ≤ j.val →
    M_curr.toFn i j = M_ref.bareissMinor start (by omega) i j
  b_prev_eq : if h : 0 < start then
      b_prev = M_ref.principalMinor (start - 1) (by omega)
    else b_prev = 1
  principalMinors_nz : ∀ ℓ : Nat, ℓ < start → (h : ℓ < n) →
    M_ref.principalMinor ℓ h ≠ 0

namespace AzMatrix.BareissInv

omit [DecidableEq D] in
/-- Auxiliary: `start ≤ n` follows from `start ≤ n - 1`. -/
theorem start_le {M_curr M_ref : AzMatrix D n n} {start : Nat} {b_prev : D}
    (h : M_curr.BareissInv M_ref start b_prev) : start ≤ n := by
  have := h.start_le_pred; omega

end AzMatrix.BareissInv

/-! ### `bareissMinor` at the top level recovers the full determinant -/

omit [DecidableEq D] in
/-- `bareissMinor M (n-1) ⟨n-1,_⟩ ⟨n-1,_⟩` is the determinant of `M`. -/
theorem AzMatrix.bareissMinor_last (M : AzMatrix D n n) (hn : 0 < n) :
    M.bareissMinor (n - 1) (by omega) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ =
      Matrix.det M.toFn := by
  unfold AzMatrix.bareissMinor
  rw [AzMatrix.toFn_bareissBlock]
  -- The bareissIdx map at level n-1 with last column = ⟨n-1, _⟩ is Fin.cast.
  have h_dim : n - 1 + 1 = n := by omega
  have h_idx : AzMatrix.bareissIdx (n - 1) (by omega) ⟨n - 1, by omega⟩ =
      Fin.cast h_dim := by
    funext l
    by_cases h : l.val < n - 1
    · rw [AzMatrix.bareissIdx_val_of_lt _ _ l h]
      rfl
    · have h_eq : l.val = n - 1 := by have := l.isLt; omega
      rw [AzMatrix.bareissIdx_of_val_eq _ _ l h_eq]
      exact Fin.ext h_eq.symm
  rw [h_idx]
  exact Matrix.det_submatrix_equiv_self (Fin.castOrderIso h_dim).toEquiv M.toFn

/-! ### Invariant transition: no-swap step (case 2 of the induction) -/

/-- After one `bareissEliminate` step at pivot `⟨start, _⟩` with the matching
    `b_prev`, the invariant advances from `start` to `start + 1`. Used in
    the `findPivot = some kp` (no swap) branch of `bareissAux`. -/
theorem AzMatrix.BareissInv.step_no_swap
    {M_curr M_ref : AzMatrix D n n} {start : Nat} {b_prev : D}
    (h_inv : M_curr.BareissInv M_ref start b_prev)
    (h_lt : start + 1 < n)
    (h_find : M_curr.findPivot ⟨start, by omega⟩ = some ⟨start, by omega⟩) :
    (M_curr.bareissEliminate ⟨start, by omega⟩ b_prev).BareissInv M_ref
      (start + 1) (M_curr.get ⟨start, by omega⟩ ⟨start, by omega⟩) := by
  classical
  -- Establish nonzero pivot at position (start, start).
  have h_pivot_nz : M_curr.toFn ⟨start, by omega⟩ ⟨start, by omega⟩ ≠ 0 :=
    M_curr.findPivot_some_nonzero ⟨start, by omega⟩ ⟨start, by omega⟩ h_find
  -- M_curr[start][start] = principalMinor M_ref start (by invariant).
  have h_pp_eq : M_curr.toFn ⟨start, by omega⟩ ⟨start, by omega⟩ =
      M_ref.bareissMinor start h_inv.start_le ⟨start, by omega⟩ ⟨start, by omega⟩ :=
    h_inv.bareiss ⟨start, by omega⟩ ⟨start, by omega⟩ (Nat.le_refl _) (Nat.le_refl _)
  have h_pp_minor_nz : M_ref.principalMinor start (by omega) ≠ 0 := by
    show M_ref.bareissMinor start (by omega) _ _ ≠ 0
    rw [← h_pp_eq]; exact h_pivot_nz
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · exact M_curr.bareissEliminate_preservesPartialZero start (by omega) b_prev
      h_inv.partialZero
  · intro i j hi hj
    exact M_ref.bareissEliminate_advances_level M_curr start h_lt b_prev
      h_inv.bareiss h_inv.b_prev_eq
      (fun ℓ hℓ h => by
        rcases lt_or_eq_of_le hℓ with hℓ_lt | hℓ_eq
        · exact h_inv.principalMinors_nz ℓ hℓ_lt h
        · subst hℓ_eq; exact h_pp_minor_nz)
      i j hi hj
  · simp only [show 0 < start + 1 from by omega, dite_true]
    show M_curr.toFn _ _ = M_ref.principalMinor (start + 1 - 1) _
    rw [h_pp_eq]
    show M_ref.bareissMinor start _ _ _ = M_ref.principalMinor _ _
    rfl
  · intro ℓ hℓ h
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hℓ) with hℓ_lt | hℓ_eq
    · exact h_inv.principalMinors_nz ℓ hℓ_lt h
    · subst hℓ_eq; exact h_pp_minor_nz

/-! ### Invariant transition: swap step (case 3 of the induction) -/

/-- After swapping columns `⟨start, _⟩` and `j` (with `j ≠ ⟨start, _⟩` and `j ≥
    start` by `findPivot`) and applying one `bareissEliminate` step, the
    invariant advances to `start + 1` with the new reference matrix
    `swapCols M_ref ⟨start, _⟩ j`. -/
theorem AzMatrix.BareissInv.step_swap
    {M_curr M_ref : AzMatrix D n n} {start : Nat} {b_prev : D}
    (h_inv : M_curr.BareissInv M_ref start b_prev)
    (h_lt : start + 1 < n) (j : Fin n)
    (h_find : M_curr.findPivot ⟨start, by omega⟩ = some j)
    (h_neq : j ≠ ⟨start, by omega⟩) :
    let M' := M_curr.swapCols ⟨start, by omega⟩ j
    (M'.bareissEliminate ⟨start, by omega⟩ b_prev).BareissInv
      (M_ref.swapCols ⟨start, by omega⟩ j) (start + 1) (M'.get ⟨start, by omega⟩ ⟨start, by omega⟩) := by
  classical
  -- The pivot column j satisfies j.val ≥ start, and j.val > start (since j ≠ kp).
  have h_j_ge : start ≤ j.val :=
    M_curr.findPivot_some_le ⟨start, by omega⟩ j h_find
  have h_j_gt : start < j.val := by
    rcases lt_or_eq_of_le h_j_ge with h | h
    · exact h
    · exact absurd (Fin.ext h.symm : j = ⟨start, _⟩) h_neq
  -- After swap, the pivot at (start, start) equals M_curr.toFn kp j ≠ 0.
  have h_orig_nz : M_curr.toFn ⟨start, by omega⟩ j ≠ 0 :=
    M_curr.findPivot_some_nonzero ⟨start, by omega⟩ j h_find
  set kp : Fin n := ⟨start, by omega⟩ with hkp
  set M' := M_curr.swapCols kp j with hM'
  set M_ref' := M_ref.swapCols kp j with hM_ref'
  -- The new pivot value.
  have h_new_pivot_val : M'.toFn kp kp = M_curr.toFn kp j := by
    rw [hM']
    rw [AzMatrix.toFn_swapCols, if_pos rfl]
  -- The new M_curr matches bareissMinor of M_ref' at level start.
  have h_bareiss_new :
      ∀ i j' : Fin n, start ≤ i.val → start ≤ j'.val →
        M'.toFn i j' = M_ref'.bareissMinor start h_inv.start_le i j' := by
    intro i j' hi hj'
    rw [hM', hM_ref']
    rw [AzMatrix.toFn_swapCols]
    -- Case-split on j' vs the swap targets.
    by_cases h_j'_eq_kp : j' = kp
    · -- j' = kp; swap sends kp → j.
      rw [if_pos h_j'_eq_kp, h_j'_eq_kp]
      have h_swap_kp : (Equiv.swap kp j) kp = j := Equiv.swap_apply_left _ _
      rw [M_ref.bareissMinor_swapCols start h_inv.start_le j h_j_gt i kp]
      rw [h_swap_kp]
      exact h_inv.bareiss i j hi h_j_ge
    · by_cases h_j'_eq_j : j' = j
      · -- j' = j; swap sends j → kp.
        rw [if_neg h_j'_eq_kp, if_pos h_j'_eq_j, h_j'_eq_j]
        have h_swap_j : (Equiv.swap kp j) j = kp := Equiv.swap_apply_right _ _
        rw [M_ref.bareissMinor_swapCols start h_inv.start_le j h_j_gt i j]
        rw [h_swap_j]
        exact h_inv.bareiss i kp hi (le_refl _)
      · -- j' ≠ kp and j' ≠ j; swap fixes j'.
        rw [if_neg h_j'_eq_kp, if_neg h_j'_eq_j]
        rw [M_ref.bareissMinor_swapCols start h_inv.start_le j h_j_gt i j']
        rw [Equiv.swap_apply_of_ne_of_ne h_j'_eq_kp h_j'_eq_j]
        exact h_inv.bareiss i j' hi hj'
  -- The new pivot M'.get kp kp matches principalMinor M_ref' start.
  have h_new_pivot_eq_pm :
      M'.toFn kp kp = M_ref'.bareissMinor start h_inv.start_le kp kp :=
    h_bareiss_new kp kp (le_refl _) (le_refl _)
  have h_pp_minor_nz : M_ref'.principalMinor start (by omega) ≠ 0 := by
    show M_ref'.bareissMinor start (by omega) kp kp ≠ 0
    rw [← h_new_pivot_eq_pm]
    rw [h_new_pivot_val]
    exact h_orig_nz
  -- The first `start` principal minors of M_ref' equal those of M_ref
  -- (swap-invariance of low-level principal minors).
  have h_old_pms_M_ref' : ∀ ℓ : Nat, ℓ < start → (h : ℓ < n) →
      M_ref'.principalMinor ℓ h ≠ 0 := by
    intro ℓ hℓ h
    rw [hM_ref', M_ref.principalMinor_swapCols_low_level start (by omega) j h_j_gt ℓ hℓ]
    exact h_inv.principalMinors_nz ℓ hℓ h
  -- Pre-establish PartialZero for M'.
  have h_pz_M' : M'.PartialZero start :=
    M_curr.swapCols_preservesPartialZero start (by omega) h_inv.partialZero j h_j_ge
  -- And b_prev = principalMinor M_ref' (start - 1) (for start > 0); = 1 otherwise.
  have h_b_prev_M_ref' : if h : 0 < start then
      b_prev = M_ref'.principalMinor (start - 1) (by omega)
    else b_prev = 1 := by
    by_cases hs : 0 < start
    · simp only [dif_pos hs]
      have h_bp := h_inv.b_prev_eq
      simp only [dif_pos hs] at h_bp
      rw [h_bp]
      -- principalMinor (start - 1) is unchanged because the swap is at columns
      -- ≥ start, both outside the top-left start × start block.
      show M_ref.principalMinor (start - 1) _ = M_ref'.principalMinor (start - 1) _
      rw [M_ref.principalMinor_eq_top_left_det (start - 1) (by omega)]
      rw [hM_ref']
      rw [(M_ref.swapCols kp j).principalMinor_eq_top_left_det (start - 1) (by omega)]
      congr 1
      funext i' j'
      show M_ref.toFn
          (Fin.castLE (Nat.succ_le_of_lt (show start - 1 < n by omega)) i')
          (Fin.castLE (Nat.succ_le_of_lt (show start - 1 < n by omega)) j')
        = (M_ref.swapCols kp j).toFn
          (Fin.castLE (Nat.succ_le_of_lt (show start - 1 < n by omega)) i')
          (Fin.castLE (Nat.succ_le_of_lt (show start - 1 < n by omega)) j')
      rw [AzMatrix.toFn_swapCols]
      have h_j'_val : (Fin.castLE (Nat.succ_le_of_lt (show start - 1 < n by omega)) j').val =
          j'.val := rfl
      have h_j'_lt_start : (Fin.castLE (Nat.succ_le_of_lt (show start - 1 < n by omega)) j' : Fin n).val < start := by
        rw [h_j'_val]; have := j'.isLt; omega
      have h_neq_kp : Fin.castLE (Nat.succ_le_of_lt (show start - 1 < n by omega)) j' ≠ kp := by
        intro h_eq
        have : (Fin.castLE _ j').val = start := congrArg Fin.val h_eq
        omega
      have h_neq_j : Fin.castLE (Nat.succ_le_of_lt (show start - 1 < n by omega)) j' ≠ j := by
        intro h_eq
        have : (Fin.castLE _ j').val = j.val := congrArg Fin.val h_eq
        omega
      rw [if_neg h_neq_kp, if_neg h_neq_j]
    · simp only [dif_neg hs]
      have h_bp := h_inv.b_prev_eq
      simp only [dif_neg hs] at h_bp
      exact h_bp
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · exact M'.bareissEliminate_preservesPartialZero start (by omega) b_prev h_pz_M'
  · intro i j' hi hj'
    exact M_ref'.bareissEliminate_advances_level M' start h_lt b_prev
      h_bareiss_new h_b_prev_M_ref'
      (fun ℓ hℓ h => by
        rcases lt_or_eq_of_le hℓ with hℓ_lt | hℓ_eq
        · exact h_old_pms_M_ref' ℓ hℓ_lt h
        · subst hℓ_eq; exact h_pp_minor_nz)
      i j' hi hj'
  · simp only [show 0 < start + 1 from by omega, dite_true]
    show M'.toFn _ _ = M_ref'.principalMinor (start + 1 - 1) _
    rw [h_new_pivot_eq_pm]
    show M_ref'.bareissMinor start _ _ _ = M_ref'.principalMinor _ _
    rfl
  · intro ℓ hℓ h
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hℓ) with hℓ_lt | hℓ_eq
    · exact h_old_pms_M_ref' ℓ hℓ_lt h
    · subst hℓ_eq; exact h_pp_minor_nz

/-! ### Abort-case helper: row of zeros forces `det M_ref = 0` -/

/-- If the algorithm aborts at step `start` (`findPivot` returns `none`), and
    the invariant relates `M_curr` to `M_ref`, then `det(M_ref) = 0`.

    Reason: `findPivot = none` means row `start` of `M_curr` is zero from
    column `start` onward; combined with `PartialZero` (zeros below diagonal
    in earlier columns), the whole row `start` is zero. Via (8.5),
    `gaussSteps M_ref start` then has a zero row at row `start`, so its
    determinant is zero, and `det M_ref = det (gaussSteps M_ref start)`
    via `det_gaussSteps`. -/
theorem AzMatrix.BareissInv.det_eq_zero_of_findPivot_none
    {M_curr M_ref : AzMatrix D n n} {start : Nat} {b_prev : D}
    (h_inv : M_curr.BareissInv M_ref start b_prev)
    (h_lt : start + 1 < n)
    (h_find : M_curr.findPivot ⟨start, by omega⟩ = none) :
    Matrix.det M_ref.toFn = 0 := by
  classical
  let K := FractionRing D
  let f : D →+* K := algebraMap D K
  have h_inj : Function.Injective f := IsFractionRing.injective D K
  apply h_inj
  show f ((Matrix.of M_ref.toFn).det) = f 0
  rw [map_zero, RingHom.map_det]
  -- Work in K (a field). Lift the algorithm's hypotheses.
  have h_start_lt : start < n := by omega
  -- Row `start` of `M_curr` is zero from column `start` onward.
  have h_zero_high : ∀ j' : Fin n, start ≤ j'.val →
      M_curr.toFn ⟨start, h_start_lt⟩ j' = 0 :=
    fun j' h_ge => M_curr.findPivot_eq_none ⟨start, h_start_lt⟩ h_find j' h_ge
  -- Lift principalMinors_nz to K and convert to Gauss pivots nonzero in K.
  have h_pms_K : ∀ ℓ : Nat, ℓ < start → (h : ℓ < n) →
      (M_ref.map f).principalMinor ℓ h ≠ 0 := by
    intro ℓ hℓ h
    rw [← M_ref.algebraMap_principalMinor f ℓ h]
    intro h_eq
    have : M_ref.principalMinor ℓ h = 0 := h_inj (by rw [h_eq, map_zero])
    exact h_inv.principalMinors_nz ℓ hℓ h this
  have h_piv_K : ∀ ℓ : Nat, ℓ < start → (h : ℓ < n) →
      ((M_ref.map f).gaussSteps ℓ).toFn ⟨ℓ, h⟩ ⟨ℓ, h⟩ ≠ 0 := by
    intro ℓ hℓ h
    -- principalMinors_nz at ℓ ≤ start - 1, so apply at k = start - 1.
    rcases Nat.eq_zero_or_pos start with hs | hs
    · subst hs; exact absurd hℓ (Nat.not_lt_zero _)
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hs)
      exact (M_ref.map f).gauss_pivots_nz_of_principalMinors_nz k'
        (fun ℓ' hℓ' h' => h_pms_K ℓ' (by omega) h') ℓ (by omega) h
  -- Row `start` of `gaussSteps (M_ref.map f) start` is zero from column `start` on.
  have h_gauss_row_high_K : ∀ j' : Fin n, start ≤ j'.val →
      ((M_ref.map f).gaussSteps start).toFn ⟨start, h_start_lt⟩ j' = 0 := by
    intro j' h_ge
    -- Lift: bareissMinor (M_ref.map f) start ⟨start⟩ j' = 0 (from M_curr row zero).
    have h_bm_D := h_inv.bareiss ⟨start, h_start_lt⟩ j' (le_refl _) h_ge
    rw [h_zero_high j' h_ge] at h_bm_D
    have h_bm_K : (M_ref.map f).bareissMinor start (by omega)
        ⟨start, h_start_lt⟩ j' = 0 := by
      rw [← M_ref.algebraMap_bareissMinor f, ← h_bm_D, map_zero]
    -- Apply (8.5) factoring in K.
    have h_factor := (M_ref.map f).bareissMinor_eq_pivotProd_mul_gaussSteps
      start h_start_lt ⟨start, h_start_lt⟩ j' (Nat.le_refl _) h_ge h_piv_K
    rw [h_bm_K] at h_factor
    have h_pp_nz : (M_ref.map f).pivotProd start (by omega) ≠ 0 := by
      unfold AzMatrix.pivotProd
      apply Finset.prod_ne_zero_iff.mpr
      intro ℓ _
      exact h_piv_K ℓ.val (by have := ℓ.isLt; omega)
        (by have := ℓ.isLt; omega)
    exact (mul_eq_zero.mp h_factor.symm).resolve_left h_pp_nz
  -- Combined with partialZero of gaussSteps, entire row `start` is zero in K.
  have h_gauss_row_all_K : ∀ j' : Fin n,
      ((M_ref.map f).gaussSteps start).toFn ⟨start, h_start_lt⟩ j' = 0 := by
    intro j'
    by_cases h : start ≤ j'.val
    · exact h_gauss_row_high_K j' h
    · have h_j'_lt : j'.val < start := by omega
      exact (M_ref.map f).gaussSteps_partialZero start ⟨start, h_start_lt⟩ j'
        h_j'_lt h_j'_lt
  have h_det_K_gauss_zero :
      Matrix.det ((M_ref.map f).gaussSteps start).toFn = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero ⟨start, h_start_lt⟩ h_gauss_row_all_K
  rw [(M_ref.map f).det_gaussSteps start
      (fun ℓ hℓ h => h_piv_K ℓ hℓ h)] at h_det_K_gauss_zero
  -- f.mapMatrix M_ref.toFn = (M_ref.map f).toFn
  show Matrix.det (f.mapMatrix M_ref.toFn) = 0
  have h_eq : f.mapMatrix M_ref.toFn = (M_ref.map f).toFn := by
    funext i j
    rw [AzMatrix.toFn_map]
    rfl
  rw [h_eq]
  exact h_det_K_gauss_zero

/-! ### Base-case helper: M_curr[n-1][n-1] = det(M_ref) -/

omit [DecidableEq D] in
theorem AzMatrix.BareissInv.last_entry_eq_det
    {M_curr M_ref : AzMatrix D n n} {start : Nat} {b_prev : D}
    (h_inv : M_curr.BareissInv M_ref start b_prev)
    (h_no_step : ¬ start + 1 < n) (h_n_pos : 0 < n) :
    M_curr.toFn ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = Matrix.det M_ref.toFn := by
  -- The invariant `start_le_pred` gives `start ≤ n - 1`, and `¬ start + 1 < n`
  -- gives `start ≥ n - 1`, so `start = n - 1`.
  have h_start_eq : start = n - 1 := by
    have := h_inv.start_le_pred; omega
  subst h_start_eq
  -- M_curr[n-1][n-1] = bareissMinor M_ref (n-1) ⟨n-1,_⟩ ⟨n-1,_⟩.
  rw [h_inv.bareiss ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ (le_refl _) (le_refl _)]
  -- This equals det(M_ref) by `bareissMinor_last`.
  exact M_ref.bareissMinor_last h_n_pos

/-! ### Main inductive theorem -/

/-- **Inductive correctness of `bareissAux`.** Whenever the Bareiss invariant
    holds between `M_curr` and a reference matrix `M_ref`, then

      `M_curr.bareissAux start s b_prev = (-1)^s · det(M_ref)`.

    The reference matrix carries the cumulative column swaps, so its
    determinant differs from the original `M` by `(-1)^s`. -/
theorem AzMatrix.bareissAux_eq_det
    (M_curr M_ref : AzMatrix D n n) (start s : Nat) (b_prev : D)
    (h_n_pos : 0 < n)
    (h_inv : M_curr.BareissInv M_ref start b_prev) :
    M_curr.bareissAux start s b_prev = (-1 : D) ^ s * Matrix.det M_ref.toFn := by
  revert h_inv h_n_pos M_ref
  induction M_curr, start, s, b_prev using AzMatrix.bareissAux.induct with
  | case1 M start s b_prev h_lt _kp h_find =>
    intro M_ref h_n_pos h_inv
    -- Abort: bareissAux returns 0; det(M_ref) = 0 by the invariant.
    have h_det_zero : Matrix.det M_ref.toFn = 0 :=
      h_inv.det_eq_zero_of_findPivot_none h_lt h_find
    rw [AzMatrix.bareissAux.eq_def]
    simp only [dif_pos h_lt]
    rw [show M.findPivot ⟨start, by omega⟩ = none from h_find]
    rw [h_det_zero, mul_zero]
  | case2 M start s b_prev h_lt _kp h_find ih =>
    intro M_ref h_n_pos h_inv
    -- No swap: invariant transitions to start + 1.
    have h_inv_next : (M.bareissEliminate ⟨start, by omega⟩ b_prev).BareissInv
        M_ref (start + 1) (M.get ⟨start, by omega⟩ ⟨start, by omega⟩) :=
      h_inv.step_no_swap h_lt h_find
    rw [AzMatrix.bareissAux.eq_def]
    simp only [dif_pos h_lt]
    rw [show M.findPivot ⟨start, by omega⟩ = some ⟨start, by omega⟩ from h_find]
    simp only [if_true]
    exact ih M_ref h_n_pos h_inv_next
  | case3 M start s b_prev h_lt _kp j h_find h_neq _M' ih =>
    intro M_ref h_n_pos h_inv
    -- Swap then eliminate: invariant transitions to (swapCols M_ref ⟨start,_⟩ j),
    -- with new s = s + 1.
    have h_inv_next := h_inv.step_swap h_lt j h_find h_neq
    rw [AzMatrix.bareissAux.eq_def]
    simp only [dif_pos h_lt]
    rw [show M.findPivot ⟨start, by omega⟩ = some j from h_find]
    show (if j = ⟨start, _⟩ then _ else _) = _
    rw [if_neg h_neq]
    -- The IH applied at the swapped M_ref gives the result; then det flips sign.
    have h_ih := ih (M_ref.swapCols ⟨start, by omega⟩ j) h_n_pos h_inv_next
    rw [h_ih]
    -- det (swapCols M_ref ⟨start⟩ j) = -det M_ref.
    have h_kp_neq_j : (⟨start, by omega⟩ : Fin n) ≠ j := fun h => h_neq h.symm
    rw [M_ref.det_swapCols_domain ⟨start, by omega⟩ j h_kp_neq_j]
    ring
  | case4 M start s b_prev h_no_step h_n_pos' =>
    intro M_ref _ h_inv
    -- Base case n ≥ 1: M_curr[n-1][n-1] = det(M_ref).
    rw [AzMatrix.bareissAux.eq_def]
    simp only [dif_neg h_no_step, dif_pos h_n_pos']
    show (-1 : D) ^ s * M.toFn ⟨n - 1, _⟩ ⟨n - 1, _⟩ = _
    rw [h_inv.last_entry_eq_det h_no_step h_n_pos']
  | case5 _ _ _ _ _ h_n_zero =>
    intro _ h_n_pos _
    exact absurd h_n_pos h_n_zero

/-! ### Main theorem -/

/-- **Correctness of `AzMatrix.bareissDet`.** The fraction-free Dodgson-
    Jordan-Bareiss algorithm computes the same determinant as Mathlib's
    `Matrix.det`. -/
theorem AzMatrix.bareissDet_eq_Matrix_det (M : AzMatrix D n n) :
    M.bareissDet = Matrix.det M.toFn := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- n = 0: both sides are 1.
    subst hn
    unfold AzMatrix.bareissDet
    rw [AzMatrix.bareissAux.eq_def]
    rw [dif_neg (show ¬ (0 + 1 < 0) from by omega)]
    rw [dif_neg (show ¬ (0 < 0) from by omega)]
    show (1 : D) = (Matrix.of M.toFn).det
    rw [Matrix.det_isEmpty]
  · -- n ≥ 1: apply the inductive theorem at start = 0, s = 0, b_prev = 1,
    -- with M_ref = M (the initial reference matrix).
    have h_inv : M.BareissInv M 0 1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · omega
      · intro _ _ _ h_bnd; exact absurd h_bnd (Nat.not_lt_zero _)
      · intro i j _ _; rw [M.bareissMinor_zero (by omega) i j]
      · simp only [show ¬ (0 < 0) from by omega, dite_false]
      · intro _ hℓ _; exact absurd hℓ (Nat.not_lt_zero _)
    have h := M.bareissAux_eq_det M 0 0 1 hn h_inv
    show M.bareissAux 0 0 1 = _
    rw [h, pow_zero, one_mul]

end Azurite
