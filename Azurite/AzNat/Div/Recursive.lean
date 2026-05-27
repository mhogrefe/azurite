import Azurite.AzNat.Div.Schoolbook
import Azurite.AzNat.Mul
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.UInt64.LeadingZeros

namespace Azurite.AzNat

/-!
## Slice-style limb-level recursive divrem (MCA Algorithm 1.8) — in-place

API matches `schoolbookDivModLimbs`.  The body is decomposed into
two non-recursive helpers (`afterFirstRec`, `afterSecondRec`) plus
the main recursive function, dodging the kernel `whnf` timeout we
hit when writing the body monolithically.
-/

/-! ### Helpers -/

/-- Zero out positions `[lo, hi)` of `a`. -/
def zeroFill (a : Array UInt64) (lo hi : Nat) : Array UInt64 :=
  if h : lo < hi then
    if hlt : lo < a.size then
      zeroFill (a.set lo 0) (lo + 1) hi
    else a
  else a
  termination_by hi - lo

theorem zeroFill_size (a : Array UInt64) (lo hi : Nat) :
    (zeroFill a lo hi).size = a.size := by
  induction h_sub : hi - lo generalizing a lo with
  | zero =>
    have : ¬ lo < hi := by omega
    rw [zeroFill]; simp [this]
  | succ n ih =>
    have h_lt : lo < hi := by omega
    rw [zeroFill]
    simp only [h_lt, ↓reduceDIte]
    by_cases h_in : lo < a.size
    · simp only [h_in, ↓reduceDIte]
      rw [ih _ _ (by omega), Array.size_set]
    · simp only [h_in, ↓reduceDIte]

/-- `zeroFill` preserves positions outside `[lo, hi)`. -/
theorem zeroFill_get_outside (a : Array UInt64) (lo hi j : Nat)
    (h_j : j < lo ∨ hi ≤ j) (h_j_size : j < a.size) :
    (zeroFill a lo hi)[j]'(by rw [zeroFill_size]; exact h_j_size) = a[j] := by
  induction h_sub : hi - lo generalizing a lo with
  | zero =>
    have : ¬ lo < hi := by omega
    unfold zeroFill; simp [this]
  | succ n ih =>
    have h_lt : lo < hi := by omega
    unfold zeroFill
    simp only [h_lt, ↓reduceDIte]
    by_cases h_in : lo < a.size
    · simp only [h_in, ↓reduceDIte]
      have h_j' : j < lo + 1 ∨ hi ≤ j := by
        rcases h_j with h | h
        · left; omega
        · right; exact h
      rw [ih (a.set lo 0) (lo + 1) h_j'
        (by rw [Array.size_set]; exact h_j_size) (by omega)]
      rw [Array.getElem_set]
      have h_ne : lo ≠ j := by
        rcases h_j with h | h
        · omega
        · omega
      simp [h_ne]
    · simp only [h_in, ↓reduceDIte]

/-- `zeroFill` zeros out the targeted range: positions in `[lo, hi)`
    become `0`. -/
theorem zeroFill_get_inside (a : Array UInt64) (lo hi j : Nat)
    (h_j_lo : lo ≤ j) (h_j_hi : j < hi) (h_j_size : j < a.size) :
    (zeroFill a lo hi)[j]'(by rw [zeroFill_size]; exact h_j_size) = 0 := by
  induction h_sub : hi - lo generalizing a lo with
  | zero => omega
  | succ n ih =>
    have h_lt : lo < hi := by omega
    unfold zeroFill
    simp only [h_lt, ↓reduceDIte]
    have h_in : lo < a.size := Nat.lt_of_le_of_lt h_j_lo h_j_size
    simp only [h_in, ↓reduceDIte]
    by_cases h_eq : lo = j
    · -- This position was just set to 0; subsequent recursion preserves it.
      have h_set : (a.set lo 0)[j]'(by rw [Array.size_set]; exact h_j_size) = 0 := by
        rw [Array.getElem_set]; simp [h_eq]
      have h_below : j < lo + 1 := by omega
      have h_preserve := zeroFill_get_outside (a.set lo 0) (lo + 1) hi j
        (Or.inl h_below) (by rw [Array.size_set]; exact h_j_size)
      rw [h_preserve]; exact h_set
    · have h_j_lo' : lo + 1 ≤ j := by omega
      exact ih (a.set lo 0) (lo + 1) h_j_lo'
        (by rw [Array.size_set]; exact h_j_size) (by omega)

/-- `toNatLimbsList` of an all-zero limb list is `0`. -/
private theorem toNatLimbsList_replicate_zero (n : Nat) :
    toNatLimbsList (List.replicate n (0 : UInt64)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show toNatLimbsList ((0 : UInt64) :: List.replicate k (0 : UInt64)) = 0
    rw [toNatLimbsList_cons, ih]; simp

/-- `zeroFill`'s `sliceVal` over the zeroed range is `0`. -/
theorem zeroFill_sliceVal_zero (a : Array UInt64) (lo len : Nat)
    (h_bound : lo + len ≤ a.size) :
    toNatLimbsList (((zeroFill a lo (lo + len)).toList.drop lo).take len) = 0 := by
  have h_eq : ((zeroFill a lo (lo + len)).toList.drop lo).take len
      = List.replicate len (0 : UInt64) := by
    apply List.ext_getElem
    · simp [List.length_take, List.length_drop, Array.length_toList,
        zeroFill_size, List.length_replicate]
      omega
    · intro i h1 _
      have h_i : i < len := by
        simp [List.length_take, List.length_drop, Array.length_toList,
          zeroFill_size] at h1
        omega
      rw [List.getElem_take, List.getElem_drop, List.getElem_replicate,
        Array.getElem_toList]
      exact zeroFill_get_inside a lo (lo + len) (lo + i) (by omega) (by omega)
        (by omega)
  rw [h_eq]; exact toNatLimbsList_replicate_zero len

/-- Copy `src[loS, loS + len)` into `a[loA, loA + len)`. -/
def writeSlice (a src : Array UInt64) (loA loS len k : Nat)
    (hA : loA + len ≤ a.size) (hS : loS + len ≤ src.size) : Array UInt64 :=
  if h : k < len then
    have hAk : loA + k < a.size := by omega
    have hSk : loS + k < src.size := by omega
    writeSlice (a.set (loA + k) (src[loS + k]'hSk)) src loA loS len (k + 1)
      (by rw [Array.size_set]; exact hA) hS
  else a
  termination_by len - k

theorem writeSlice_size (a src : Array UInt64) (loA loS len k : Nat)
    (hA : loA + len ≤ a.size) (hS : loS + len ≤ src.size) :
    (writeSlice a src loA loS len k hA hS).size = a.size := by
  induction h_sub : len - k generalizing a k hA with
  | zero =>
    have : ¬ k < len := by omega
    rw [writeSlice]; simp [this]
  | succ n ih =>
    have h_lt : k < len := by omega
    rw [writeSlice]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ (by omega), Array.size_set]

/-- `writeSlice` preserves positions outside `[loA + k, loA + len)`. -/
theorem writeSlice_get_outside (a src : Array UInt64) (loA loS len k : Nat)
    (hA : loA + len ≤ a.size) (hS : loS + len ≤ src.size) (j : Nat)
    (h_j : j < loA + k ∨ loA + len ≤ j) (h_j_size : j < a.size) :
    (writeSlice a src loA loS len k hA hS)[j]'(by
      rw [writeSlice_size]; exact h_j_size) = a[j] := by
  induction h_sub : len - k generalizing a k hA with
  | zero =>
    have : ¬ k < len := by omega
    unfold writeSlice; simp [this]
  | succ n ih =>
    have h_lt : k < len := by omega
    unfold writeSlice
    simp only [h_lt, ↓reduceDIte]
    have hAk : loA + k < a.size := by omega
    have hSk : loS + k < src.size := by omega
    have h_j' : j < loA + (k + 1) ∨ loA + len ≤ j := by
      rcases h_j with h | h
      · left; omega
      · right; exact h
    rw [ih (a.set (loA + k) (src[loS + k]'hSk)) (k + 1)
      (by rw [Array.size_set]; exact hA)
      h_j' (by rw [Array.size_set]; exact h_j_size) (by omega)]
    rw [Array.getElem_set]
    have h_ne : loA + k ≠ j := by
      rcases h_j with h | h
      · omega
      · omega
    simp [h_ne]

/-- `writeSlice` copies `src[loS + k + i]` into position `loA + k + i`
    for `i ∈ [0, len - k)`.  For positions in `[loA + k, loA + len)`,
    the output equals the corresponding source element. -/
theorem writeSlice_get_inside (a src : Array UInt64) (loA loS len k : Nat)
    (hA : loA + len ≤ a.size) (hS : loS + len ≤ src.size) (j : Nat)
    (h_j_lo : loA + k ≤ j) (h_j_hi : j < loA + len) (h_j_size : j < a.size) :
    (writeSlice a src loA loS len k hA hS)[j]'(by
      rw [writeSlice_size]; exact h_j_size)
      = src[loS + (j - loA)]'(by omega) := by
  induction h_sub : len - k generalizing a k hA with
  | zero => omega
  | succ n ih =>
    have h_lt : k < len := by omega
    unfold writeSlice
    simp only [h_lt, ↓reduceDIte]
    have hAk : loA + k < a.size := by omega
    have hSk : loS + k < src.size := by omega
    by_cases h_eq : loA + k = j
    · -- This position was just set; subsequent recursion preserves it.
      have h_set :
          (a.set (loA + k) (src[loS + k]'hSk))[j]'(by
            rw [Array.size_set]; exact h_j_size) = src[loS + k]'hSk := by
        rw [Array.getElem_set]; simp [h_eq]
      have h_below : j < loA + (k + 1) := by omega
      have h_preserve :=
        writeSlice_get_outside (a.set (loA + k) (src[loS + k]'hSk)) src loA loS
          len (k + 1) (by rw [Array.size_set]; exact hA) hS j
          (Or.inl h_below) (by rw [Array.size_set]; exact h_j_size)
      rw [h_preserve, h_set]
      congr 1; omega
    · have h_j_lo' : loA + (k + 1) ≤ j := by omega
      exact ih (a.set (loA + k) (src[loS + k]'hSk)) (k + 1)
        (by rw [Array.size_set]; exact hA)
        h_j_lo' (by rw [Array.size_set]; exact h_j_size) (by omega)

/-- Adjustment loop: while `borrow`, add `B[loB, loB + n)` to
    `a[loA + k, loA + k + highLen)` (carry propagated through the full
    `highLen` length via `addGeqLimbs`). -/
def addbackLoop (a b : Array UInt64) (loA loB n k highLen : Nat)
    (borrow : Bool) (fuel : Nat)
    (hA : loA + k + highLen ≤ a.size) (hB : loB + n ≤ b.size)
    (h_n_le : n ≤ highLen) (h_n_pos : 0 < n) (h_high_pos : 0 < highLen) :
    Array UInt64 × Nat :=
  match fuel with
  | 0 => (a, 0)
  | fuel' + 1 =>
    if borrow then
      have h_addGeq_size : (addGeqLimbs a b (loA + k) highLen loB n
          (by omega) hB h_n_le h_high_pos h_n_pos).1.size = a.size :=
        addGeqLimbs_size a b (loA + k) highLen loB n
          (by omega) hB h_n_le h_high_pos h_n_pos
      let r := addGeqLimbs a b (loA + k) highLen loB n
        (by omega) hB h_n_le h_high_pos h_n_pos
      let (a', cnt) := addbackLoop r.1 b loA loB n k highLen (!r.2) fuel'
        (by show loA + k + highLen ≤ r.1.size
            rw [show r.1.size = a.size from h_addGeq_size]; omega)
        hB h_n_le h_n_pos h_high_pos
      (a', cnt + 1)
    else
      (a, 0)

theorem addbackLoop_size (a b : Array UInt64) (loA loB n k highLen : Nat)
    (borrow : Bool) (fuel : Nat)
    (hA : loA + k + highLen ≤ a.size) (hB : loB + n ≤ b.size)
    (h_n_le : n ≤ highLen) (h_n_pos : 0 < n) (h_high_pos : 0 < highLen) :
    (addbackLoop a b loA loB n k highLen borrow fuel
      hA hB h_n_le h_n_pos h_high_pos).1.size = a.size := by
  induction fuel generalizing a borrow with
  | zero => rw [addbackLoop]
  | succ fuel' ih =>
    rw [addbackLoop]
    by_cases h_b : borrow
    · simp only [h_b, ↓reduceIte]
      rw [ih _ _]
      exact addGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _
    · simp [h_b]

/-- `addbackLoop` preserves positions outside `[loA + k, loA + k + highLen)`. -/
theorem addbackLoop_get_outside (a b : Array UInt64) (loA loB n k highLen : Nat)
    (borrow : Bool) (fuel : Nat)
    (hA : loA + k + highLen ≤ a.size) (hB : loB + n ≤ b.size)
    (h_n_le : n ≤ highLen) (h_n_pos : 0 < n) (h_high_pos : 0 < highLen) (j : Nat)
    (h_j : j < loA + k ∨ loA + k + highLen ≤ j) (h_j_size : j < a.size) :
    (addbackLoop a b loA loB n k highLen borrow fuel
      hA hB h_n_le h_n_pos h_high_pos).1[j]'(by
      rw [addbackLoop_size]; exact h_j_size) = a[j] := by
  induction fuel generalizing a borrow with
  | zero => unfold addbackLoop; simp
  | succ fuel' ih =>
    unfold addbackLoop
    by_cases h_b : borrow
    · simp only [h_b, ↓reduceIte]
      rw [ih _ _
        (by rw [addGeqLimbs_size]; exact hA)
        (by rw [addGeqLimbs_size]; exact h_j_size)]
      exact addGeqLimbs_get_outside a b (loA + k) highLen loB n hA hB
        h_n_le h_high_pos h_n_pos j h_j h_j_size
    · simp [h_b]

/-- Decrement `a[lo, a.size)` by a Nat amount. -/
def decrementSlice (a : Array UInt64) (lo : Nat) (d : Nat)
    (hlo : lo ≤ a.size) : Array UInt64 :=
  (subLimb a lo a.size (UInt64.ofNat d) hlo (Nat.le_refl _)).1

theorem decrementSlice_size (a : Array UInt64) (lo : Nat) (d : Nat)
    (hlo : lo ≤ a.size) :
    (decrementSlice a lo d hlo).size = a.size := by
  unfold decrementSlice; exact subLimb_size _ _ _ _ _ _

/-! ### Stage helpers (non-recursive, elaborated separately) -/

/-- After the first recursive call has overwritten `a` with R₁ at
    `[loA + 2k, loA + n + k)` and Q₁ low limbs at
    `[loA + n + k, loA + n + m)`, with `q_top_1` as the top of Q₁:
      - Save Q₁ to scratch (length `m - k + 1`).
      - Zero out the Q₁ region in `a`.
      - Compute `Q₁ · B₀` via `mulLimbs` (length `m + 1`).
      - Subtract from `a` at offset `loA + k` via `subGeqLimbs`.
      - Adjust via `addbackLoop` while borrow.
      - Decrement Q₁ by the adjustment count.
    Returns `(modified a, decremented Q₁, adjustment count)`. -/
def recursiveDivModLimbs.afterFirstRec
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m) :
    Array UInt64 × Array UInt64 × Nat :=
  let k := m / 2
  have h_k_pos : 0 < k := by omega
  have h_2k_le_n : 2 * k ≤ n := by omega
  let q1_low := a.extract (loA + n + k) (loA + n + m)
  let q1_arr := q1_low.push q_top_1
  have h_q1_low_size : q1_low.size = m - k := by
    show (a.extract (loA + n + k) (loA + n + m)).size = m - k
    rw [Array.size_extract]; omega
  have h_q1_size : q1_arr.size = m - k + 1 := by
    show (q1_low.push q_top_1).size = m - k + 1
    rw [Array.size_push, h_q1_low_size]
  let a2 := zeroFill a (loA + n + k) (loA + n + m)
  have h_a2_size : a2.size = a.size := zeroFill_size _ _ _
  let q1_b0 := mulLimbs q1_arr b 0 (m - k + 1) loB k
    (by rw [h_q1_size]; omega) (by omega)
  have h_q1_b0_size_ge : m + 1 ≤ q1_b0.size := by
    show m + 1 ≤ (mulLimbs q1_arr b 0 (m - k + 1) loB k
      (by rw [h_q1_size]; omega) (by omega)).size
    have h := mulLimbs_size_ge q1_arr b 0 (m - k + 1) loB k
      (by rw [h_q1_size]; omega) (by omega)
    omega
  let subRes := subGeqLimbs a2 q1_b0 (loA + k) (n + m - k) 0 (m + 1)
    (by rw [h_a2_size]; omega) (by omega)
    (by omega) (by omega) (by omega)
  let a3 := subRes.1
  let borrow1 := subRes.2
  have h_a3_size : a3.size = a.size :=
    (subGeqLimbs_size a2 q1_b0 (loA + k) (n + m - k) 0 (m + 1)
      (by rw [h_a2_size]; omega) (by omega)
      (by omega) (by omega) (by omega)).trans h_a2_size
  let adj := addbackLoop a3 b loA loB n k (n + m - k) borrow1 5
    (by rw [h_a3_size]; omega) hB (by omega) h_n_pos (by omega)
  let a4 := adj.1
  let delta1 := adj.2
  let q1_arr' := decrementSlice q1_arr 0 delta1 (Nat.zero_le _)
  (a4, q1_arr', delta1)

theorem recursiveDivModLimbs.afterFirstRec_size
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m) :
    (recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2).1.size = a.size := by
  unfold recursiveDivModLimbs.afterFirstRec
  simp only
  set k := m / 2
  set a2 := zeroFill a (loA + n + k) (loA + n + m)
  have h_a2 : a2.size = a.size := zeroFill_size a (loA + n + k) (loA + n + m)
  rw [addbackLoop_size, subGeqLimbs_size]; exact h_a2

/-- `afterFirstRec` preserves positions outside `[loA, loA + n + m)`. -/
theorem recursiveDivModLimbs.afterFirstRec_get_outside
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m) (j : Nat)
    (h_j : j < loA ∨ loA + n + m ≤ j) (h_j_size : j < a.size) :
    (recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2).1[j]'(by
      rw [recursiveDivModLimbs.afterFirstRec_size]; exact h_j_size) = a[j] := by
  unfold recursiveDivModLimbs.afterFirstRec
  simp only
  set k := m / 2
  set a2 := zeroFill a (loA + n + k) (loA + n + m) with h_a2_def
  set q1_b0 := mulLimbs (a.extract (loA + n + k) (loA + n + m) |>.push q_top_1)
    b 0 (m - k + 1) loB k (by simp [Array.size_push, Array.size_extract]; omega)
    (by omega) with h_q1_b0_def
  have h_a2_size : a2.size = a.size := zeroFill_size _ _ _
  have h_j_k : j < loA + k ∨ loA + k + (n + m - k) ≤ j := by
    rcases h_j with h | h
    · left; omega
    · right; omega
  have h_j_k2 : j < loA + k ∨ loA + k + (n + m - k) ≤ j := h_j_k
  rw [addbackLoop_get_outside _ _ _ _ _ _ _ _ _ _ _ _ _ _ j h_j_k
    (by rw [subGeqLimbs_size, h_a2_size]; exact h_j_size)]
  rw [subGeqLimbs_get_outside _ _ _ _ _ _ _ _ _ _ _ j h_j_k2
    (by rw [h_a2_size]; exact h_j_size)]
  have h_j_zf : j < loA + n + k ∨ loA + n + m ≤ j := by
    rcases h_j with h | h
    · left; omega
    · right; exact h
  exact zeroFill_get_outside a (loA + n + k) (loA + n + m) j h_j_zf h_j_size

theorem recursiveDivModLimbs.afterFirstRec_q1size
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m) :
    (recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2).2.1.size = m - m / 2 + 1 := by
  unfold recursiveDivModLimbs.afterFirstRec
  simp only
  rw [decrementSlice_size, Array.size_push, Array.size_extract]
  omega

/-- After the second recursive call: save Q₀, zero Q₀ region, compute
    Q₀ B₀, subtract, addback, assemble Q = Q₁' beta^k + Q₀'. -/
def recursiveDivModLimbs.afterSecondRec
    (a b q1_arr' : Array UInt64) (q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (h_q1_arr'_size : q1_arr'.size = m - m / 2 + 1) :
    Array UInt64 × UInt64 :=
  let k := m / 2
  have h_k_pos : 0 < k := by omega
  have h_2k_le_n : 2 * k ≤ n := by omega
  let q0_low := a.extract (loA + n) (loA + n + k)
  let q0_arr := q0_low.push q_top_0
  have h_q0_low_size : q0_low.size = k := by
    show (a.extract (loA + n) (loA + n + k)).size = k
    rw [Array.size_extract]; omega
  have h_q0_size : q0_arr.size = k + 1 := by
    show (q0_low.push q_top_0).size = k + 1
    rw [Array.size_push, h_q0_low_size]
  let a6 := zeroFill a (loA + n) (loA + n + k)
  have h_a6_size : a6.size = a.size := zeroFill_size _ _ _
  let q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k
    (by rw [h_q0_size]; omega) (by omega)
  have h_q0_b0_size_ge : 2 * k + 1 ≤ q0_b0.size := by
    show 2 * k + 1 ≤ (mulLimbs q0_arr b 0 (k + 1) loB k
      (by rw [h_q0_size]; omega) (by omega)).size
    have h := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k
      (by rw [h_q0_size]; omega) (by omega)
    omega
  let subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
    (by rw [h_a6_size]; omega) (by omega)
    (by omega) (by omega) (by omega)
  let a7 := subRes2.1
  let borrow0 := subRes2.2
  have h_a7_size : a7.size = a.size :=
    (subGeqLimbs_size a6 q0_b0 loA (n + m) 0 (2 * k + 1)
      (by rw [h_a6_size]; omega) (by omega)
      (by omega) (by omega) (by omega)).trans h_a6_size
  let adj2 := addbackLoop a7 b loA loB n 0 (n + m) borrow0 5
    (by rw [h_a7_size]; omega) hB (by omega) h_n_pos (by omega)
  let a8 := adj2.1
  let delta0 := adj2.2
  have h_a8_size : a8.size = a.size :=
    (addbackLoop_size a7 b loA loB n 0 (n + m) borrow0 5
      (by rw [h_a7_size]; omega) hB (by omega) h_n_pos (by omega)).trans h_a7_size
  let q0_arr' := decrementSlice q0_arr 0 delta0 (Nat.zero_le _)
  have h_q0_arr'_size : q0_arr'.size = k + 1 := by
    rw [decrementSlice_size]; exact h_q0_size
  let tempQ : Array UInt64 := Array.replicate (m + 1) 0
  have h_tempQ_size : tempQ.size = m + 1 := Array.size_replicate
  let tempQ1 := writeSlice tempQ q0_arr' 0 0 (k + 1) 0
    (by rw [h_tempQ_size]; omega) (by rw [h_q0_arr'_size]; omega)
  have h_tempQ1_size : tempQ1.size = m + 1 := by
    rw [writeSlice_size]; exact h_tempQ_size
  let addRes := addSameLengthLimbs tempQ1 q1_arr' k 0 (m - k + 1)
    (by rw [h_tempQ1_size]; omega) (by rw [h_q1_arr'_size]; omega)
  let tempQ2 := addRes.1
  have h_tempQ2_size : tempQ2.size = m + 1 :=
    (addSameLengthLimbs_size tempQ1 q1_arr' k 0 (m - k + 1)
      (by rw [h_tempQ1_size]; omega) (by rw [h_q1_arr'_size]; omega)).trans h_tempQ1_size
  let a9 := writeSlice a8 tempQ2 (loA + n) 0 m 0
    (by rw [h_a8_size]; omega) (by rw [h_tempQ2_size]; omega)
  have h_top_idx : m < tempQ2.size := by rw [h_tempQ2_size]; omega
  (a9, tempQ2[m]'h_top_idx)

theorem recursiveDivModLimbs.afterSecondRec_size
    (a b q1_arr' : Array UInt64) (q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (h_q1_arr'_size : q1_arr'.size = m - m / 2 + 1) :
    (recursiveDivModLimbs.afterSecondRec a b q1_arr' q_top_0 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2 h_q1_arr'_size).1.size = a.size := by
  unfold recursiveDivModLimbs.afterSecondRec
  simp only
  set k := m / 2
  set a6 := zeroFill a (loA + n) (loA + n + k)
  have h_a6 : a6.size = a.size := zeroFill_size a (loA + n) (loA + n + k)
  rw [writeSlice_size, addbackLoop_size, subGeqLimbs_size]; exact h_a6

/-- `afterSecondRec` preserves positions outside `[loA, loA + n + m)`. -/
theorem recursiveDivModLimbs.afterSecondRec_get_outside
    (a b q1_arr' : Array UInt64) (q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (h_q1_arr'_size : q1_arr'.size = m - m / 2 + 1) (j : Nat)
    (h_j : j < loA ∨ loA + n + m ≤ j) (h_j_size : j < a.size) :
    (recursiveDivModLimbs.afterSecondRec a b q1_arr' q_top_0 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2 h_q1_arr'_size).1[j]'(by
      rw [recursiveDivModLimbs.afterSecondRec_size]; exact h_j_size) = a[j] := by
  unfold recursiveDivModLimbs.afterSecondRec
  simp only
  set k := m / 2
  set a6 := zeroFill a (loA + n) (loA + n + k) with h_a6_def
  have h_a6_size : a6.size = a.size := zeroFill_size _ _ _
  have h_j_writeSlice : j < loA + n ∨ loA + n + m ≤ j := by
    rcases h_j with h | h
    · left; omega
    · right; exact h
  have h_j_addback : j < loA + 0 ∨ loA + 0 + (n + m) ≤ j := by
    rcases h_j with h | h
    · left; omega
    · right; omega
  have h_j_subGeq : j < loA ∨ loA + (n + m) ≤ j := by
    rcases h_j with h | h
    · left; exact h
    · right; omega
  have h_j_zeroFill : j < loA + n ∨ loA + n + k ≤ j := by
    rcases h_j with h | h
    · left; omega
    · right; omega
  rw [writeSlice_get_outside _ _ _ _ _ _ _ _ j h_j_writeSlice
    (by rw [addbackLoop_size, subGeqLimbs_size, h_a6_size]; exact h_j_size)]
  rw [addbackLoop_get_outside _ _ _ _ _ _ _ _ _ _ _ _ _ _ j h_j_addback
    (by rw [subGeqLimbs_size, h_a6_size]; exact h_j_size)]
  rw [subGeqLimbs_get_outside _ _ _ _ _ _ _ _ _ _ _ j h_j_subGeq
    (by rw [h_a6_size]; exact h_j_size)]
  exact zeroFill_get_outside a (loA + n) (loA + n + k) j h_j_zeroFill h_j_size

/-! ### Main slice-level recursive divrem -/

/-- Slice-style limb-level recursive divrem.  In-place convention
    matches `schoolbookDivModLimbs`.  Returns `(array, top_limb)`
    paired with a proof that the array's size is preserved. -/
def recursiveDivModLimbsAux (threshold : Nat) (a b : Array UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat) :
    { p : Array UInt64 × UInt64 // p.1.size = a.size } :=
  if h_unbal : n < m then
    have h_n_le_m : n ≤ m := Nat.le_of_lt h_unbal
    have hA_chunk : (loA + (m - n)) + n + n ≤ a.size := by omega
    let ⟨⟨a_chunk, q_top_chunk⟩, h_chunk_size⟩ :=
      recursiveDivModLimbsAux threshold a b
        (loA + (m - n)) loB n n h_n_pos hA_chunk hB hbn1
    have hA_rest : loA + n + (m - n) ≤ a_chunk.size := by
      rw [h_chunk_size]; omega
    let ⟨⟨a_rest, q_top_rest⟩, h_rest_size⟩ :=
      recursiveDivModLimbsAux threshold a_chunk b
        loA loB n (m - n) h_n_pos hA_rest hB hbn1
    have hAdd_end : loA + m + n ≤ a_rest.size := by
      rw [h_rest_size, h_chunk_size]; omega
    let addRes := addLimb a_rest (loA + m) (loA + m + n) q_top_rest
      (by omega) hAdd_end
    let carryOut : UInt64 := if addRes.2 then 1 else 0
    ⟨(addRes.1, q_top_chunk + carryOut), by
      rw [addLimb_size]; exact h_rest_size.trans h_chunk_size⟩
  else if h : m < max threshold 2 then
    ⟨schoolbookDivModLimbs a b loA loB n m h_n_pos hA hB hbn1,
     schoolbookDivModLimbs_size a b loA loB n m h_n_pos hA hB hbn1⟩
  else
    have h_m_le_n : m ≤ n := by omega
    have h_m_ge_2 : 2 ≤ m := by have := le_max_right threshold 2; omega
    have h_k_pos : 0 < m / 2 := by omega
    have h_2k_le_n : 2 * (m / 2) ≤ n := by omega
    have h_k_lt_n : m / 2 < n := by omega
    have h_n_minus_k_pos : 0 < n - m / 2 := by omega
    have hA_top : (loA + 2 * (m / 2)) + (n - m / 2) + (m - m / 2) ≤ a.size := by omega
    have hB_top : (loB + m / 2) + (n - m / 2) ≤ b.size := by omega
    have hbn1_top : 2 ^ 63 ≤ (b[(loB + m / 2) + (n - m / 2) - 1]'(by omega)).toNat := by
      have h_eq : b[(loB + m / 2) + (n - m / 2) - 1]'(by omega)
          = b[loB + n - 1]'(by omega) := by congr 1; omega
      rw [h_eq]; exact hbn1
    let ⟨⟨a1, q_top_1⟩, h_a1_size⟩ := recursiveDivModLimbsAux threshold a b
      (loA + 2 * (m / 2)) (loB + m / 2) (n - m / 2) (m - m / 2)
      h_n_minus_k_pos hA_top hB_top hbn1_top
    let res_after1 := recursiveDivModLimbs.afterFirstRec a1 b q_top_1 loA loB n m
      h_n_pos (by rw [h_a1_size]; exact hA) hB h_m_le_n h_m_ge_2
    let a4 := res_after1.1
    let q1_arr' := res_after1.2.1
    have h_a4_size : a4.size = a.size :=
      (recursiveDivModLimbs.afterFirstRec_size a1 b q_top_1 loA loB n m
        h_n_pos (by rw [h_a1_size]; exact hA) hB h_m_le_n h_m_ge_2).trans h_a1_size
    have h_q1_size : q1_arr'.size = m - m / 2 + 1 :=
      recursiveDivModLimbs.afterFirstRec_q1size a1 b q_top_1 loA loB n m
        h_n_pos (by rw [h_a1_size]; exact hA) hB h_m_le_n h_m_ge_2
    have hA_mid : (loA + m / 2) + (n - m / 2) + (m / 2) ≤ a4.size := by
      rw [h_a4_size]; omega
    let ⟨⟨a5, q_top_0⟩, h_a5_size_local⟩ := recursiveDivModLimbsAux threshold a4 b
      (loA + m / 2) (loB + m / 2) (n - m / 2) (m / 2)
      h_n_minus_k_pos hA_mid hB_top hbn1_top
    have h_a5_size : a5.size = a.size := h_a5_size_local.trans h_a4_size
    let res_final := recursiveDivModLimbs.afterSecondRec a5 b q1_arr' q_top_0 loA loB n m
      h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_q1_size
    ⟨res_final,
     (recursiveDivModLimbs.afterSecondRec_size a5 b q1_arr' q_top_0 loA loB n m
        h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_q1_size).trans h_a5_size⟩
  termination_by n + m
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-- Thin Array-typed wrapper: returns just the `(Array, UInt64)` pair. -/
@[inline] def recursiveDivModLimbsArr (threshold : Nat) (a b : Array UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat) :
    Array UInt64 × UInt64 :=
  (recursiveDivModLimbsAux threshold a b loA loB n m h_n_pos hA hB hbn1).1

/-- Size preservation: immediate from the Sigma-typed `Aux`. -/
theorem recursiveDivModLimbsArr_size (threshold : Nat) (a b : Array UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat) :
    (recursiveDivModLimbsArr threshold a b loA loB n m
      h_n_pos hA hB hbn1).1.size = a.size :=
  (recursiveDivModLimbsAux threshold a b loA loB n m h_n_pos hA hB hbn1).2

end Azurite.AzNat
