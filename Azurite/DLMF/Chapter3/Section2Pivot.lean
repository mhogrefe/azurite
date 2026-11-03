/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter3.Section2

/-!
# DLMF §3.2(i): Gaussian elimination with partial pivoting

"The rows are interchanged at each elimination step in such a way that the absolute value of the
element that is used as a divisor, the pivot element, is not less than that of the other
available elements in its column."

* The algorithm, over an ordered field, works in compact storage, keeping the multipliers below
  the diagonal and interchanging whole rows.
  * `pivotRow` gives the first row of maximal `|c_{pk}|` (`pivotRow_spec`).
  * `ppSwap`, `ppElim`, `ppStep`, `ppRun` and `gaussPP` carry out the steps.
  * The result is the factors `ppL`, `ppU` and the permuted matrix `ppPA`.
* **`PA = LU`** (`gaussPP_factorization`), for every square matrix, singular or not.
  * The invariant (`ppRun_invariant`, `ppR`) says that row `σ(i)` of `A` is
    `∑_{m < min(i,k)} ℓ_{im}(row m of U)` plus the active part of row `i`.
  * It is preserved by the interchange (`ppR_swap`) and by the elimination (`ppR_elim`); a zero
    pivot column is consistent because the pivot is maximal.
* **"Then `|ℓ_{jk}| ≤ 1` in all cases"** (`ppRun_mult_le_one`, `ppL_le_one`): the multipliers
  stay bounded through all later interchanges.
-/

namespace Azurite.DLMF

open Azurite

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-! ### The algorithm (compact storage: multipliers below the diagonal) -/

/-- The pivot row: the first row `p ≥ k` maximizing `|c_{pk}|`. -/
def pivotRow (C : AzMatrix K n n) (k : Fin n) : Fin n :=
  (List.finRange n).foldl (fun r i => if k ≤ i ∧ |C.toFn r k| < |C.toFn i k| then i else r) k

omit [IsStrictOrderedRing K] in
theorem pivotRow_foldl (C : AzMatrix K n n) (k : Fin n) :
    ∀ (l : List (Fin n)) (r : Fin n), k ≤ r →
      let r' := l.foldl (fun r i => if k ≤ i ∧ |C.toFn r k| < |C.toFn i k| then i else r) r
      k ≤ r' ∧ |C.toFn r k| ≤ |C.toFn r' k| ∧ ∀ i ∈ l, k ≤ i → |C.toFn i k| ≤ |C.toFn r' k| := by
  intro l
  induction l with
  | nil => intro r hr; exact ⟨hr, le_rfl, fun i hi => absurd hi (List.not_mem_nil)⟩
  | cons a l ih =>
    intro r hr
    simp only [List.foldl_cons]
    by_cases h : k ≤ a ∧ |C.toFn r k| < |C.toFn a k|
    · simp only [h, and_self, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := ih a h.1
      refine ⟨h1, h.2.le.trans h2, fun i hi hki => ?_⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact h2
      · exact h3 i hi hki
    · simp only [h, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := ih r hr
      refine ⟨h1, h2, fun i hi hki => ?_⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact (not_lt.mp fun h' => h ⟨hki, h'⟩).trans h2
      · exact h3 i hi hki

omit [IsStrictOrderedRing K] in
theorem pivotRow_spec (C : AzMatrix K n n) (k : Fin n) :
    k ≤ pivotRow C k ∧ ∀ i : Fin n, k ≤ i → |C.toFn i k| ≤ |C.toFn (pivotRow C k) k| := by
  obtain ⟨h1, -, h3⟩ := pivotRow_foldl C k (List.finRange n) k le_rfl
  exact ⟨h1, fun i hi => h3 i (List.mem_finRange i) hi⟩

/-- Interchange rows `k` and `p`. -/
def ppSwap (C : AzMatrix K n n) (k p : Fin n) : AzMatrix K n n :=
  AzMatrix.ofFn fun i j => C.toFn (Equiv.swap k p i) j

/-- Eliminate below the pivot `(k, k)`, storing the multipliers `ℓ_{ik} = c_{ik}/c_{kk}` in
column `k`. -/
def ppElim (C : AzMatrix K n n) (k : Fin n) : AzMatrix K n n :=
  AzMatrix.ofFn fun i j =>
    if i.val ≤ k.val then C.toFn i j
    else if j.val < k.val then C.toFn i j
    else if j = k then C.toFn i k / C.toFn k k
    else C.toFn i j - C.toFn i k / C.toFn k k * C.toFn k j

/-- One step: choose the pivot, interchange, eliminate; `σ` records the original row of each
current row. -/
def ppStep (s : AzMatrix K n n × (Fin n → Fin n)) (k : Fin n) :
    AzMatrix K n n × (Fin n → Fin n) :=
  (ppElim (ppSwap s.1 k (pivotRow s.1 k)) k, s.2 ∘ Equiv.swap k (pivotRow s.1 k))

/-- The first `m` steps of Gaussian elimination with partial pivoting. -/
def ppRun (A : AzMatrix K n n) : ℕ → AzMatrix K n n × (Fin n → Fin n)
  | 0 => (A, id)
  | m + 1 => if h : m < n then ppStep (ppRun A m) ⟨m, h⟩ else ppRun A m

/-- The final compact matrix and row order. -/
def gaussPP (A : AzMatrix K n n) : AzMatrix K n n × (Fin n → Fin n) := ppRun A n

/-- `L`: unit lower triangular, the stored multipliers below the diagonal. -/
def ppL (A : AzMatrix K n n) : AzMatrix K n n :=
  AzMatrix.ofFn fun i k =>
    if k.val < i.val then (gaussPP A).1.toFn i k else if k = i then 1 else 0

/-- `U`: the upper triangle. -/
def ppU (A : AzMatrix K n n) : AzMatrix K n n :=
  AzMatrix.ofFn fun i j => if i.val ≤ j.val then (gaussPP A).1.toFn i j else 0

/-- `PA`: the rows of `A` in the final order. -/
def ppPA (A : AzMatrix K n n) : AzMatrix K n n :=
  AzMatrix.ofFn fun i j => A.toFn ((gaussPP A).2 i) j

/-! ### The invariant -/

/-- After `k` steps, row `i` of `PA` is `∑_{m < min(i,k)} ℓ_{im} (row m of U)` plus the active
part of row `i` (columns `≥ k`), or the frozen row of `U` when `i < k`. -/
def ppR (C : AzMatrix K n n) (k : ℕ) (i j : Fin n) : K :=
  (∑ m : Fin n, if m.val < i.val ∧ m.val < k then
      C.toFn i m * (if m.val ≤ j.val then C.toFn m j else 0) else 0) +
    if i.val < k then (if i.val ≤ j.val then C.toFn i j else 0)
    else if k ≤ j.val then C.toFn i j else 0

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem ppR_swap (C : AzMatrix K n n) (k p : Fin n) (hkp : k ≤ p) (i j : Fin n) :
    ppR (ppSwap C k p) k.val i j = ppR C k.val (Equiv.swap k p i) j := by
  have hsw : ∀ m : Fin n, m.val < k.val → Equiv.swap k p m = m := fun m hm =>
    Equiv.swap_apply_of_ne_of_ne (fun h => by rw [h] at hm; exact lt_irrefl _ hm)
      (fun h => by rw [h] at hm; exact absurd hkp (not_le.mpr hm))
  have hrow : ∀ m j : Fin n, m.val < k.val → (ppSwap C k p).toFn m j = C.toFn m j :=
    fun m j hm => by rw [ppSwap, AzMatrix.toFn_ofFn, hsw m hm]
  unfold ppR
  rcases lt_or_ge i.val k.val with hi | hi
  · have hi' : Equiv.swap k p i = i := hsw i hi
    rw [hi']
    congr 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hm : m.val < i.val
      · simp only [hm, show m.val < k.val by omega, and_self, ↓reduceIte, hrow i m hi,
          hrow m j (by omega)]
      · simp only [hm, false_and, ↓reduceIte]
    · simp only [hi, ↓reduceIte, hrow i j hi]
  · set i' := Equiv.swap k p i
    have hi' : k.val ≤ i'.val := by
      simp only [i', Equiv.swap_apply_def]
      split_ifs with h1 h2
      · exact hkp
      · exact le_rfl
      · exact hi
    have hval : ∀ m : Fin n, (ppSwap C k p).toFn i m = C.toFn i' m := fun m => by
      rw [ppSwap, AzMatrix.toFn_ofFn]
    congr 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hm : m.val < k.val
      · simp only [show m.val < i.val by omega, show m.val < i'.val by omega, hm, and_self,
          ↓reduceIte, hval, hrow m j hm]
      · simp only [hm, and_false, ↓reduceIte]
    · simp only [show ¬ i.val < k.val by omega, show ¬ i'.val < k.val by omega, ↓reduceIte, hval]

theorem ppR_elim (C : AzMatrix K n n) (k : Fin n)
    (hmax : ∀ i : Fin n, k ≤ i → |C.toFn i k| ≤ |C.toFn k k|) (i j : Fin n) :
    ppR (ppElim C k) (k.val + 1) i j = ppR C k.val i j := by
  have hE : ∀ i j : Fin n, (ppElim C k).toFn i j =
      if i.val ≤ k.val then C.toFn i j
      else if j.val < k.val then C.toFn i j
      else if j = k then C.toFn i k / C.toFn k k
      else C.toFn i j - C.toFn i k / C.toFn k k * C.toFn k j := fun i j => by
    rw [ppElim, AzMatrix.toFn_ofFn]
  have hrowle : ∀ m j : Fin n, m.val ≤ k.val → (ppElim C k).toFn m j = C.toFn m j :=
    fun m j hm => by rw [hE]; simp [hm]
  unfold ppR
  rcases lt_trichotomy i.val k.val with hi | hi | hi
  · congr 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hm : m.val < i.val
      · simp only [hm, show m.val < k.val + 1 by omega, show m.val < k.val by omega, and_self,
          ↓reduceIte, hrowle i m (by omega), hrowle m j (by omega)]
      · simp only [hm, false_and, ↓reduceIte]
    · simp only [show i.val < k.val + 1 by omega, hi, ↓reduceIte, hrowle i j hi.le]
  · have hik : i = k := Fin.ext hi
    subst hik
    congr 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hm : m.val < i.val
      · simp only [hm, show m.val < i.val + 1 by omega, and_self, ↓reduceIte,
          hrowle i m le_rfl, hrowle m j hm.le]
      · simp only [hm, false_and, ↓reduceIte]
    · simp only [lt_add_one, lt_irrefl, ↓reduceIte, hrowle i j le_rfl]
  · -- a row below the pivot
    have hsplit : ∀ m : Fin n, (if m.val < i.val ∧ m.val < k.val + 1 then
          (ppElim C k).toFn i m * (if m.val ≤ j.val then (ppElim C k).toFn m j else 0) else 0) =
        (if m.val < i.val ∧ m.val < k.val then
          C.toFn i m * (if m.val ≤ j.val then C.toFn m j else 0) else 0) +
        if m = k then C.toFn i k / C.toFn k k * (if k.val ≤ j.val then C.toFn k j else 0)
          else 0 := by
      intro m
      by_cases hmk : m = k
      · subst hmk
        simp only [hi, lt_add_one, and_self, ↓reduceIte, lt_irrefl, and_false, zero_add]
        rw [hE, hrowle m j le_rfl]
        simp [show ¬ i.val ≤ m.val by omega]
      · have hmk' : m.val ≠ k.val := fun h => hmk (Fin.ext h)
        simp only [hmk, ↓reduceIte, add_zero]
        by_cases hm : m.val < k.val
        · simp only [show m.val < i.val by omega, show m.val < k.val + 1 by omega, hm, and_self,
            ↓reduceIte, hE i m, hrowle m j hm.le, show ¬ i.val ≤ k.val by omega]
        · simp only [show ¬ m.val < k.val + 1 by omega, hm, and_false, ↓reduceIte]
    rw [Finset.sum_congr rfl fun m _ => hsplit m, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte, show ¬ i.val < k.val + 1 by omega,
      show ¬ i.val < k.val by omega]
    rw [add_assoc]
    congr 1
    rw [hE i j]
    simp only [show ¬ i.val ≤ k.val by omega, ↓reduceIte]
    rcases lt_trichotomy j.val k.val with hj | hj | hj
    · simp [show ¬ k.val ≤ j.val by omega, show ¬ k.val + 1 ≤ j.val by omega]
    · have hjk : j = k := Fin.ext hj
      subst hjk
      simp only [le_refl, ↓reduceIte, show ¬ j.val + 1 ≤ j.val by omega, add_zero]
      by_cases h0 : C.toFn j j = 0
      · have := hmax i (by rw [Fin.le_def]; omega)
        rw [h0, abs_zero] at this
        rw [abs_nonpos_iff.mp this, h0]; simp
      · field_simp
    · have hjk : j ≠ k := fun h => by rw [h] at hj; exact lt_irrefl _ hj
      simp only [show k.val ≤ j.val by omega, show k.val + 1 ≤ j.val by omega, ↓reduceIte,
        show ¬ j.val < k.val by omega, hjk]
      ring

/-- **The invariant**: after `m` steps, `a_{σ(i), j} = R_m(C)_{ij}`. -/
theorem ppRun_invariant (A : AzMatrix K n n) :
    ∀ m : ℕ, m ≤ n → ∀ i j : Fin n,
      A.toFn ((ppRun A m).2 i) j = ppR (ppRun A m).1 m i j := by
  intro m
  induction m with
  | zero =>
    intro _ i j
    simp [ppRun, ppR]
  | succ m ih =>
    intro hm i j
    have hmn : m < n := by omega
    set k : Fin n := ⟨m, hmn⟩
    simp only [ppRun, hmn, ↓reduceDIte, ppStep]
    obtain ⟨hkp, hmax⟩ := pivotRow_spec (ppRun A m).1 k
    set C := (ppRun A m).1
    set p := pivotRow C k
    have hmax' : ∀ i : Fin n, k ≤ i → |(ppSwap C k p).toFn i k| ≤ |(ppSwap C k p).toFn k k| := by
      intro i hi
      rw [ppSwap, AzMatrix.toFn_ofFn, AzMatrix.toFn_ofFn, Equiv.swap_apply_left]
      apply hmax
      simp only [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · exact hkp
      · exact le_rfl
      · exact hi
    rw [show m + 1 = k.val + 1 from rfl, ppR_elim _ k hmax' i j, ppR_swap C k p hkp i j]
    exact ih (by omega) _ j

/-- **Partial pivoting: `PA = LU`** (for every square matrix, singular or not). -/
theorem gaussPP_factorization (A : AzMatrix K n n) : ppPA A = ppL A * ppU A := by
  apply AzMatrix.toFn_injective
  funext i j
  have hinv : A.toFn ((gaussPP A).2 i) j = ppR (gaussPP A).1 n i j :=
    ppRun_invariant A n le_rfl i j
  rw [ppPA, AzMatrix.toFn_ofFn, AzMatrix.toFn_mul, hinv]
  unfold ppR
  have e : ∀ m : Fin n, (ppL A).toFn i m * (ppU A).toFn m j =
      (if m.val < i.val ∧ m.val < n then
        (gaussPP A).1.toFn i m * (if m.val ≤ j.val then (gaussPP A).1.toFn m j else 0) else 0) +
      if m = i then (if i.val ≤ j.val then (gaussPP A).1.toFn i j else 0) else 0 := by
    intro m
    rw [ppL, ppU, AzMatrix.toFn_ofFn, AzMatrix.toFn_ofFn]
    by_cases h1 : m.val < i.val
    · have : m ≠ i := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      simp [h1, this, m.isLt]
    · by_cases h2 : m = i
      · subst h2; simp
      · simp [h1, h2]
  rw [Finset.sum_congr rfl fun m _ => e m, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte, i.isLt]

/-- **"Then `|ℓ_{jk}| ≤ 1` in all cases"**: the stored multipliers never exceed `1` in modulus,
through all later interchanges. -/
theorem ppRun_mult_le_one (A : AzMatrix K n n) :
    ∀ k : ℕ, ∀ i m : Fin n, m.val < i.val → m.val < k → |(ppRun A k).1.toFn i m| ≤ 1 := by
  intro k
  induction k with
  | zero => intro i m _ h; omega
  | succ k ih =>
    intro i m hmi hmk
    by_cases hkn : k < n
    · set kk : Fin n := ⟨k, hkn⟩
      simp only [ppRun, hkn, ↓reduceDIte, ppStep]
      obtain ⟨hkp, hmax⟩ := pivotRow_spec (ppRun A k).1 kk
      set C := (ppRun A k).1
      set p := pivotRow C kk
      have hsw : ∀ r : Fin n, r.val < k → Equiv.swap kk p r = r := fun r hr =>
        Equiv.swap_apply_of_ne_of_ne (fun h => by rw [h] at hr; exact lt_irrefl _ hr)
          (fun h => by rw [h] at hr; exact absurd hkp (not_le.mpr hr))
      rw [ppElim, AzMatrix.toFn_ofFn]
      by_cases hik : i.val ≤ k
      · simp only [hik, ↓reduceIte]
        rw [ppSwap, AzMatrix.toFn_ofFn]
        rcases lt_or_eq_of_le hik with h | h
        · rw [hsw i h]; exact ih i m hmi (by omega)
        · -- row `k` after the interchange is the old pivot row `p`, with `m < k`
          have hi : i = kk := Fin.ext h
          rw [hi, Equiv.swap_apply_left]
          have h1 : m.val < kk.val := hi ▸ hmi
          exact ih p m (lt_of_lt_of_le h1 hkp) (by omega)
      · simp only [hik, ↓reduceIte]
        by_cases hm : m.val < k
        · simp only [hm, ↓reduceIte]
          rw [ppSwap, AzMatrix.toFn_ofFn]
          have hi' : k ≤ (Equiv.swap kk p i).val := by
            simp only [Equiv.swap_apply_def]
            split_ifs with h1 h2
            · exact hkp
            · exact le_rfl
            · omega
          exact ih _ m (lt_of_lt_of_le hm hi') hm
        · obtain rfl : m = kk := Fin.ext (show m.val = k by omega)
          simp only [hm, ↓reduceIte]
          split_ifs with hc
          swap; · exact absurd rfl hc
          rw [ppSwap, AzMatrix.toFn_ofFn, AzMatrix.toFn_ofFn, Equiv.swap_apply_left, abs_div]
          by_cases h0 : |C.toFn p kk| = 0
          · rw [h0, div_zero]; exact zero_le_one
          · rw [div_le_one (lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0))]
            apply hmax
            simp only [Equiv.swap_apply_def]
            split_ifs with h1 h2
            · exact hkp
            · exact le_rfl
            · rw [Fin.le_def]; simp [kk]; omega
    · simp only [ppRun, hkn, ↓reduceDIte]
      exact ih i m hmi (by omega)

/-- `|ℓ_{jk}| ≤ 1` for the factor `L` of `PA = LU`. -/
theorem ppL_le_one (A : AzMatrix K n n) (i m : Fin n) : |(ppL A).toFn i m| ≤ 1 := by
  rw [ppL, AzMatrix.toFn_ofFn]
  split_ifs with h1 h2
  · exact ppRun_mult_le_one A n i m h1 m.isLt
  · simp
  · simp

end Azurite.DLMF
