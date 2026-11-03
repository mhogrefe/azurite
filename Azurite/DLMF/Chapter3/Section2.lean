/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.AzMatrix.Equiv.Bareiss
import Azurite.AzMatrix.Equiv.Mul
import Azurite.AzMatrix.Equiv.MulVec

/-!
# DLMF §3.2(i): Gaussian elimination

Gaussian elimination is Azurite's `AzMatrix.gaussSteps` (BPR Algorithm 8.15 without pivoting,
over any field), with its lemmas on triangularity and stable rows.

* **3.2.3–3.2.4**: `U` (`luU`, upper triangular by `luU_upper`) and `L` (`luL`, unit lower
  triangular, the stored multipliers `ℓ_{ik}` = `luMult`).
* **3.2.5** (`dlmf_3_2_5`): `A = LU` when the pivots `u_{11}, …, u_{n−1,n−1}` are nonzero.
  * Each step is the row operation `row_i ← row_i − ℓ_{ik} row_k` (`gaussSteps_succ_row`).
  * The invariant `a_{ij} = ∑_{k<min(ℓ,i)} ℓ_{ik} u_{kj} + g^{(ℓ)}_{ij}` holds throughout
    (`gaussSteps_invariant`).
* **Solution of 3.2.1** (`gauss_solve`): forward elimination `Ly = b` (`forwardSubst`,
  `forwardSubst_spec`), then back substitution `Ux = y` (`backSubst`, `backSubst_spec`), gives
  `Ax = b` whenever all pivots are nonzero.
* **Example 3.2.6** (`dlmf_3_2_6`): the triangular decomposition, computed in the kernel.
  `dlmf_3_2_i_example_solve` gives `y = [1, −1, 3]ᵀ` and `x = [1/6, 1/6, 1/6]ᵀ`.
* **Iterative refinement** (`iterative_refinement`): exactly, `A(x + δx) = b` when `A δx = r`,
  `r = b − Ax`.

Partial pivoting is in `Section2Pivot.lean`. The remarks on instability and on rounding errors
are not formalized.
-/

namespace Azurite.DLMF

open Azurite

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The triangular decomposition 3.2.3–3.2.5 -/

/-- The multiplier `ℓ_{ik}` used in column `k` to eliminate row `i`: the `(i, k)` entry divided
by the pivot, after `k` elimination steps. -/
def luMult (M : AzMatrix K n n) (k i : Fin n) : K :=
  (M.gaussSteps k).toFn i k / (M.gaussSteps k).toFn k k

/-- **DLMF 3.2.4**: `L`, unit lower triangular with the multipliers below the diagonal. -/
def luL (M : AzMatrix K n n) : AzMatrix K n n :=
  AzMatrix.ofFn fun i k => if k.val < i.val then luMult M k i else if k = i then 1 else 0

/-- **DLMF 3.2.3**: `U`, the upper triangular matrix left by forward elimination. -/
def luU (M : AzMatrix K n n) : AzMatrix K n n := M.gaussSteps n

/-- `U` is upper triangular. -/
theorem luU_upper (M : AzMatrix K n n) (i j : Fin n) (h : j.val < i.val) :
    (luU M).toFn i j = 0 :=
  M.gaussSteps_partialZero n i j h j.isLt

/-- One elimination step is the row operation `row_i ← row_i − ℓ_{ik} row_k` (all columns), for
`i > k`, when the pivot is nonzero. -/
theorem gaussSteps_succ_row (M : AzMatrix K n n) {k : ℕ} (hk : k < n)
    (hpiv : (M.gaussSteps k).toFn ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0) (i j : Fin n) (hi : k < i.val) :
    (M.gaussSteps (k + 1)).toFn i j =
      (M.gaussSteps k).toFn i j - luMult M ⟨k, hk⟩ i * (M.gaussSteps k).toFn ⟨k, hk⟩ j := by
  unfold luMult
  rcases lt_trichotomy j.val k with hj | hj | hj
  · rw [AzMatrix.gaussSteps_succ _ _ hk, AzMatrix.toFn_eliminateBelow]
    simp only [show ¬ i.val ≤ k by omega, hj, ↓reduceIte]
    rw [M.gaussSteps_partialZero k ⟨k, hk⟩ j hj hj, mul_zero, sub_zero]
  · have hjk : j = ⟨k, hk⟩ := Fin.ext hj
    subst hjk
    rw [AzMatrix.gaussSteps_succ _ _ hk, AzMatrix.toFn_eliminateBelow]
    simp only [show ¬ i.val ≤ k by omega, lt_irrefl, ↓reduceIte]
    field_simp
    ring
  · exact M.gaussSteps_succ_apply k hk i j hi hj

/-- The elimination invariant: `a_{ij} = ∑_{k < min(ℓ, i)} ℓ_{ik} g^{(k)}_{kj} + g^{(ℓ)}_{ij}`. -/
theorem gaussSteps_invariant (M : AzMatrix K n n)
    (hpiv : ∀ k : ℕ, (hk : k + 1 < n) →
      (M.gaussSteps k).toFn ⟨k, by omega⟩ ⟨k, by omega⟩ ≠ 0) :
    ∀ ℓ : ℕ, ℓ ≤ n → ∀ i j : Fin n, M.toFn i j =
      (∑ k : Fin n, if k.val < ℓ ∧ k.val < i.val then
        luMult M k i * (M.gaussSteps k).toFn k j else 0) + (M.gaussSteps ℓ).toFn i j := by
  intro ℓ
  induction ℓ with
  | zero => intro _ i j; simp
  | succ ℓ ih =>
    intro hℓ i j
    have hℓn : ℓ < n := by omega
    rw [ih (by omega) i j]
    by_cases hi : ℓ < i.val
    · have hp := hpiv ℓ (by omega)
      rw [gaussSteps_succ_row M hℓn hp i j hi]
      have hsplit : ∀ k : Fin n, (if k.val < ℓ + 1 ∧ k.val < i.val then
            luMult M k i * (M.gaussSteps k).toFn k j else 0) =
          (if k.val < ℓ ∧ k.val < i.val then luMult M k i * (M.gaussSteps k).toFn k j else 0) +
            if k = ⟨ℓ, hℓn⟩ then luMult M ⟨ℓ, hℓn⟩ i *
              (M.gaussSteps ℓ).toFn ⟨ℓ, hℓn⟩ j else 0 := by
        intro k
        by_cases hk : k = ⟨ℓ, hℓn⟩
        · subst hk; simp [hi]
        · have hk' : k.val ≠ ℓ := fun h => hk (Fin.ext h)
          simp only [hk, ↓reduceIte, add_zero]
          by_cases h1 : k.val < ℓ ∧ k.val < i.val
          · simp only [h1, show k.val < ℓ + 1 by omega, and_self, ↓reduceIte]
          · simp only [h1, ↓reduceIte]
            exact ite_eq_right_iff.mpr fun h => absurd ⟨by omega, h.2⟩ h1
      rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
      ring
    · have hst : (M.gaussSteps (ℓ + 1)).toFn i j = (M.gaussSteps ℓ).toFn i j := by
        rw [AzMatrix.gaussSteps_succ _ _ hℓn, AzMatrix.toFn_eliminateBelow]
        simp only [show i.val ≤ ℓ by omega, ↓reduceIte]
      rw [hst]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      exact propext ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩

/-- **DLMF 3.2.5**: `A = LU`, when the pivots `u_{11}, …, u_{n−1,n−1}` are nonzero (the
elimination does not break down). -/
theorem dlmf_3_2_5 (M : AzMatrix K n n)
    (hpiv : ∀ k : ℕ, (hk : k + 1 < n) →
      (M.gaussSteps k).toFn ⟨k, by omega⟩ ⟨k, by omega⟩ ≠ 0) :
    luL M * luU M = M := by
  apply AzMatrix.toFn_injective
  funext i j
  rw [AzMatrix.toFn_mul, gaussSteps_invariant M hpiv n le_rfl i j]
  have hrow : ∀ k : Fin n, (M.gaussSteps k).toFn k j = (luU M).toFn k j := fun k =>
    (M.gaussSteps_row_unchanged k k.isLt n k.isLt.le j).symm
  have e : ∀ k : Fin n, (luL M).toFn i k * (luU M).toFn k j =
      (if k.val < n ∧ k.val < i.val then luMult M k i * (M.gaussSteps k).toFn k j else 0) +
        if k = i then (luU M).toFn i j else 0 := by
    intro k
    rw [luL, AzMatrix.toFn_ofFn, hrow]
    by_cases h1 : k.val < i.val
    · have : k ≠ i := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      simp [h1, this, k.isLt]
    · by_cases h2 : k = i
      · subst h2; simp
      · simp [h1, h2]
  rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte, luU]

/-! ### Forward elimination and back substitution -/

/-- The first `m` unknowns of `Ly = b` (`y_i = b_i − ∑_{j<i} ℓ_{ij} y_j`). -/
def fwdSubAux (L : AzMatrix K n n) (b : AzVector K n) : ℕ → Fin n → K
  | 0 => fun _ => 0
  | m + 1 =>
    if h : m < n then
      Function.update (fwdSubAux L b m) ⟨m, h⟩
        (b.get ⟨m, h⟩ - ∑ j : Fin n, if j.val < m then L.get ⟨m, h⟩ j * fwdSubAux L b m j else 0)
    else fwdSubAux L b m

/-- **Forward elimination**: the solution of `Ly = b` for unit lower triangular `L`. -/
def forwardSubst (L : AzMatrix K n n) (b : AzVector K n) : AzVector K n :=
  AzVector.ofFn (fwdSubAux L b n)

/-- The last `m` unknowns of `Ux = y`, computed from `x_n` downwards
(`x_i = (y_i − ∑_{j>i} u_{ij} x_j)/u_{ii}`). -/
def bwdSubAux (U : AzMatrix K n n) (y : AzVector K n) : ℕ → Fin n → K
  | 0 => fun _ => 0
  | m + 1 =>
    if h : m < n then
      Function.update (bwdSubAux U y m) ⟨n - 1 - m, by omega⟩
        ((y.get ⟨n - 1 - m, by omega⟩ - ∑ j : Fin n, if n - 1 - m < j.val then
          U.get ⟨n - 1 - m, by omega⟩ j * bwdSubAux U y m j else 0) /
          U.get ⟨n - 1 - m, by omega⟩ ⟨n - 1 - m, by omega⟩)
    else bwdSubAux U y m

/-- **Back substitution**: the solution of `Ux = y` for upper triangular `U` with nonzero
diagonal. -/
def backSubst (U : AzMatrix K n n) (y : AzVector K n) : AzVector K n :=
  AzVector.ofFn (bwdSubAux U y n)

theorem fwdSubAux_succ (L : AzMatrix K n n) (b : AzVector K n) {m : ℕ} (hm : m < n) :
    fwdSubAux L b (m + 1) = Function.update (fwdSubAux L b m) ⟨m, hm⟩
      (b.get ⟨m, hm⟩ - ∑ j : Fin n, if j.val < m then L.get ⟨m, hm⟩ j * fwdSubAux L b m j
        else 0) := by
  simp only [fwdSubAux, hm, ↓reduceDIte]

theorem bwdSubAux_succ (U : AzMatrix K n n) (y : AzVector K n) {m : ℕ} (hm : m < n) :
    bwdSubAux U y (m + 1) = Function.update (bwdSubAux U y m) ⟨n - 1 - m, by omega⟩
      ((y.get ⟨n - 1 - m, by omega⟩ - ∑ j : Fin n, if n - 1 - m < j.val then
        U.get ⟨n - 1 - m, by omega⟩ j * bwdSubAux U y m j else 0) /
        U.get ⟨n - 1 - m, by omega⟩ ⟨n - 1 - m, by omega⟩) := by
  simp only [bwdSubAux, hm, ↓reduceDIte]

theorem fwdSubAux_stable (L : AzMatrix K n n) (b : AzVector K n) :
    ∀ m : ℕ, ∀ i : Fin n, i.val < m → fwdSubAux L b m i = fwdSubAux L b (i.val + 1) i := by
  intro m
  induction m with
  | zero => intro i h; omega
  | succ m ih =>
    intro i hi
    by_cases him : i.val = m
    · rw [← him]
    · by_cases hm : m < n
      · rw [fwdSubAux_succ L b hm, Function.update_of_ne
          (fun h => him (by have := congrArg Fin.val h; simpa using this)), ih i (by omega)]
      · rw [show fwdSubAux L b (m + 1) = fwdSubAux L b m by simp [fwdSubAux, hm], ih i (by omega)]

theorem fwdSubAux_eq (L : AzMatrix K n n) (b : AzVector K n) (i : Fin n) :
    fwdSubAux L b n i = b.get i - ∑ j : Fin n, if j.val < i.val then
      L.get i j * fwdSubAux L b n j else 0 := by
  rw [fwdSubAux_stable L b n i i.isLt, fwdSubAux_succ L b i.isLt, Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rw [fwdSubAux_stable L b n j j.isLt, fwdSubAux_stable L b i.val j hj]
  · rfl

/-- `Ly = b` for unit lower triangular `L` (forward elimination). -/
theorem forwardSubst_spec (L : AzMatrix K n n)
    (hL : ∀ i j : Fin n, L.toFn i j = if j.val < i.val then L.toFn i j else if j = i then 1 else 0)
    (b : AzVector K n) : L.mulVec (forwardSubst L b) = b := by
  apply AzVector.toFn_injective
  funext i
  rw [AzMatrix.toFn_mulVec, dotProduct]
  have e : ∀ j : Fin n, L.toFn i j * (forwardSubst L b).toFn j =
      (if j.val < i.val then L.get i j * fwdSubAux L b n j else 0) +
        if j = i then fwdSubAux L b n i else 0 := by
    intro j
    rw [hL i j, forwardSubst, AzVector.toFn_ofFn]
    by_cases h1 : j.val < i.val
    · have : j ≠ i := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      simp only [h1, this, ↓reduceIte, add_zero]; rfl
    · by_cases h2 : j = i
      · subst h2; simp
      · simp [h1, h2]
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [fwdSubAux_eq, add_sub_cancel]
  rfl

theorem bwdSubAux_stable (U : AzMatrix K n n) (y : AzVector K n) :
    ∀ m : ℕ, ∀ i : Fin n, n - 1 - i.val < m →
      bwdSubAux U y m i = bwdSubAux U y (n - i.val) i := by
  intro m
  induction m with
  | zero => intro i h; omega
  | succ m ih =>
    intro i hi
    by_cases him : n - 1 - i.val = m
    · rw [show n - i.val = m + 1 by omega]
    · by_cases hm : m < n
      · rw [bwdSubAux_succ U y hm, Function.update_of_ne
          (fun h => him (by have := congrArg Fin.val h; simp at this; omega)), ih i (by omega)]
      · rw [show bwdSubAux U y (m + 1) = bwdSubAux U y m by simp [bwdSubAux, hm], ih i (by omega)]

theorem bwdSubAux_eq (U : AzMatrix K n n) (y : AzVector K n) (i : Fin n) :
    bwdSubAux U y n i = (y.get i - ∑ j : Fin n, if i.val < j.val then
      U.get i j * bwdSubAux U y n j else 0) / U.get i i := by
  rw [bwdSubAux_stable U y n i (by omega)]
  have hm : n - 1 - i.val < n := by omega
  rw [show n - i.val = (n - 1 - i.val) + 1 by omega, bwdSubAux_succ U y hm]
  simp only [show n - 1 - (n - 1 - i.val) = i.val by omega, Function.update_self]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rw [bwdSubAux_stable U y n j (by omega), bwdSubAux_stable U y (n - 1 - i.val) j (by omega)]
  · rfl

/-- `Ux = y` for upper triangular `U` with nonzero diagonal (back substitution). -/
theorem backSubst_spec (U : AzMatrix K n n) (hU : ∀ i j : Fin n, j.val < i.val → U.toFn i j = 0)
    (hd : ∀ i : Fin n, U.toFn i i ≠ 0) (y : AzVector K n) : U.mulVec (backSubst U y) = y := by
  apply AzVector.toFn_injective
  funext i
  rw [AzMatrix.toFn_mulVec, dotProduct]
  have e : ∀ j : Fin n, U.toFn i j * (backSubst U y).toFn j =
      (if i.val < j.val then U.get i j * bwdSubAux U y n j else 0) +
        if j = i then U.toFn i i * bwdSubAux U y n i else 0 := by
    intro j
    rw [backSubst, AzVector.toFn_ofFn]
    rcases lt_trichotomy i.val j.val with h | h | h
    · have : j ≠ i := fun h' => by rw [h'] at h; exact lt_irrefl _ h
      simp only [h, this, ↓reduceIte, add_zero]; rfl
    · have : j = i := Fin.ext h.symm
      subst this; simp
    · have : j ≠ i := fun h' => by rw [h'] at h; exact lt_irrefl _ h
      simp [show ¬ i.val < j.val by omega, this, hU i j h]
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [bwdSubAux_eq]
  have hdi : U.get i i ≠ 0 := hd i
  change _ + U.get i i * _ = y.get i
  field_simp
  ring

theorem mulVec_mul (A B : AzMatrix K n n) (v : AzVector K n) :
    (A * B).mulVec v = A.mulVec (B.mulVec v) := by
  apply AzVector.toFn_injective
  funext i
  simp only [AzMatrix.toFn_mulVec, AzMatrix.toFn_mul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The solution of 3.2.1 by Gaussian elimination**: with all pivots nonzero (`A`
nonsingular, no breakdown), forward elimination `Ly = b` followed by back substitution `Ux = y`
solves `Ax = b`. -/
theorem gauss_solve (M : AzMatrix K n n)
    (hpiv : ∀ k : ℕ, (hk : k < n) → (M.gaussSteps k).toFn ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0)
    (b : AzVector K n) :
    M.mulVec (backSubst (luU M) (forwardSubst (luL M) b)) = b := by
  have hLU := dlmf_3_2_5 M fun k hk => hpiv k (by omega)
  have hL : ∀ i j : Fin n, (luL M).toFn i j =
      if j.val < i.val then (luL M).toFn i j else if j = i then 1 else 0 := by
    intro i j
    rw [luL, AzMatrix.toFn_ofFn]
    split_ifs <;> simp_all
  have hd : ∀ i : Fin n, (luU M).toFn i i ≠ 0 := fun i => by
    rw [luU, M.gaussSteps_diag_stable i n i.isLt.le i.isLt]; exact hpiv i i.isLt
  calc M.mulVec (backSubst (luU M) (forwardSubst (luL M) b))
      = (luL M * luU M).mulVec (backSubst (luU M) (forwardSubst (luL M) b)) := by rw [hLU]
    _ = (luL M).mulVec ((luU M).mulVec (backSubst (luU M) (forwardSubst (luL M) b))) :=
        mulVec_mul _ _ _
    _ = b := by rw [backSubst_spec (luU M) (luU_upper M) hd, forwardSubst_spec (luL M) hL]

/-- **Iterative refinement with the existing decomposition**: for any approximation `x` (for
example one spoiled by rounding errors), the residual `r = b − Ax`, the correction `δx` solved
from `LU δx = r` by forward elimination and back substitution, and `x + δx` solves `Ax = b`
exactly (in exact arithmetic one step suffices). -/
theorem iterative_refinement_lu (M : AzMatrix K n n)
    (hpiv : ∀ k : ℕ, (hk : k < n) → (M.gaussSteps k).toFn ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0)
    (b x : AzVector K n) :
    let r := AzVector.ofFn (b.toFn - (M.mulVec x).toFn)
    let dx := backSubst (luU M) (forwardSubst (luL M) r)
    M.mulVec (AzVector.ofFn (x.toFn + dx.toFn)) = b := by
  intro r dx
  have h := gauss_solve M hpiv r
  apply AzVector.toFn_injective
  funext i
  have hi := congrArg (fun v => AzVector.toFn v i) h
  have hof : ∀ f : Fin n → K, (AzVector.ofFn f).toFn = f := fun f =>
    funext (AzVector.toFn_ofFn f)
  simp only [AzMatrix.toFn_mulVec] at hi ⊢
  rw [hof, dotProduct_add]
  change _ + M.toFn i ⬝ᵥ (backSubst (luU M) (forwardSubst (luL M) r)).toFn = _
  rw [hi, hof]
  simp [AzMatrix.toFn_mulVec]

/-- **Iterative refinement**, exactly: if `r = b − Ax` and `A δx = r`, then `A(x + δx) = b`. -/
theorem iterative_refinement (A : Matrix (Fin n) (Fin n) K) (b x dx : Fin n → K)
    (h : A.mulVec dx = b - A.mulVec x) : A.mulVec (x + dx) = b := by
  rw [Matrix.mulVec_add, h]; abel

/-! ### The Example 3.2.6 -/

/-- The matrix of 3.2.6. -/
def gaussExampleA : AzMatrix ℚ 3 3 := AzMatrix.ofFn ![![1, 2, 3], ![2, 3, 1], ![3, 1, 2]]

set_option maxRecDepth 100000 in
/-- **DLMF 3.2.6**: the triangular decomposition of the example, computed by the elimination. -/
theorem dlmf_3_2_6 :
    luL gaussExampleA = AzMatrix.ofFn ![![1, 0, 0], ![2, 1, 0], ![3, 5, 1]] ∧
      luU gaussExampleA = AzMatrix.ofFn ![![1, 2, 3], ![0, -1, -5], ![0, 0, 18]] ∧
      luL gaussExampleA * luU gaussExampleA = gaussExampleA := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- "In solving `Ax = [1, 1, 1]ᵀ`, we obtain by forward elimination `y = [1, −1, 3]ᵀ`, and by
back substitution `x = [1/6, 1/6, 1/6]ᵀ`." -/
theorem dlmf_3_2_i_example_solve :
    (forwardSubst (luL gaussExampleA) (AzVector.ofFn ![1, 1, 1])).toFn = ![1, -1, 3] ∧
      (backSubst (luU gaussExampleA) (AzVector.ofFn ![1, -1, 3])).toFn = ![1 / 6, 1 / 6, 1 / 6] ∧
      (gaussExampleA.mulVec (AzVector.ofFn ![1 / 6, 1 / 6, 1 / 6])).toFn = ![1, 1, 1] := by
  decide +kernel

end Azurite.DLMF
