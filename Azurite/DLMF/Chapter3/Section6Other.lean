/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section6Inhom

/-!
# DLMF §3.6(vii): linear difference equations of other orders

* The first-order equation 3.6.17 `aₙ w_{n+1} − bₙ wₙ = dₙ`: the homogeneous solutions are the
  multiples of `hₙ = ∏ bⱼ/aⱼ` (`rec1H`); when the wanted solution satisfies `wₙ/hₙ → 0`, forward
  recursion is unstable (`dlmf_3_6_17_forward_unstable`) and backward recursion from
  `w_N^{(N)} = 0` converges (`dlmf_3_6_17_backward`) — "it may sometimes be necessary to recur
  backwards to achieve stability"; such a solution is unique (`dlmf_3_6_17_unique`).
* The equation of order `k`, 3.6.18 (`IsRecK`), with 3.6.1 as the case `k = 2`
  (`isRecK_two_iff`), and its equivalence with a system of `k` first-order inhomogeneous equations
  for the state `(wₙ, …, w_{n+k−1})` (`dlmf_3_6_18_system`).
* Boundary-value problems with `k − ℓ` conditions at the beginning and `ℓ` at the end (`IsBVk`):
  forward recursion is `ℓ = 0` (`dlmf_3_6_vii_ell_zero`, from `dlmf_3_6_18_forward`), backward
  recursion is `ℓ = k` (`dlmf_3_6_vii_ell_k`, from `dlmf_3_6_18_backward`, built by reversing the
  index).

The choice of `ℓ` "depends on the asymptotic behavior of the wanted solution" — that is prose;
the references (Gautschi 1997b, Wimp 1984, Cash–Zahar 1994, Lozier 1980) are not formalized.
-/

open Filter Topology Finset

namespace Azurite.DLMF

/-! ### The first-order equation 3.6.17 -/

/-- `w` solves **DLMF 3.6.17** `aₙ w_{n+1} − bₙ wₙ = dₙ`. -/
def IsRec1 (a b d w : ℕ → ℂ) : Prop := ∀ n, a n * w (n + 1) - b n * w n = d n

/-- The solution `hₙ = ∏_{j<n} bⱼ/aⱼ` of the homogeneous equation, `h₀ = 1`. -/
noncomputable def rec1H (a b : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => b n / a n * rec1H a b n

theorem rec1H_isRec1 {a b : ℕ → ℂ} (ha : ∀ n, a n ≠ 0) : IsRec1 a b 0 (rec1H a b) := fun n => by
  simp only [rec1H, Pi.zero_apply]
  rw [← mul_assoc, mul_div_cancel₀ _ (ha n), sub_self]

theorem rec1H_ne_zero {a b : ℕ → ℂ} (ha : ∀ n, a n ≠ 0) (hb : ∀ n, b n ≠ 0) (n : ℕ) :
    rec1H a b n ≠ 0 := by
  induction n with
  | zero => simp [rec1H]
  | succ n ih => simp only [rec1H]; exact mul_ne_zero (div_ne_zero (hb n) (ha n)) ih

/-- The solutions of the homogeneous form of 3.6.17 are the multiples of `h`. -/
theorem IsRec1.eq_mul_rec1H {a b u : ℕ → ℂ} (ha : ∀ n, a n ≠ 0) (hu : IsRec1 a b 0 u) (n : ℕ) :
    u n = u 0 * rec1H a b n := by
  induction n with
  | zero => simp [rec1H]
  | succ n ih =>
    have e := hu n
    simp only [Pi.zero_apply] at e
    simp only [rec1H]
    have := ha n
    field_simp
    linear_combination e + b n * ih

theorem IsRec1.sub {a b d v w : ℕ → ℂ} (hv : IsRec1 a b d v) (hw : IsRec1 a b d w) :
    IsRec1 a b 0 (fun n => v n - w n) := fun n => by
  simp only [Pi.zero_apply]; linear_combination hv n - hw n

/-- Backward recursion `wₙ = (aₙ w_{n+1} − dₙ)/bₙ` for 3.6.17 from `w_N = x`: after `k` steps, the
value at `N − k`. -/
noncomputable def rec1BackAux (a b d : ℕ → ℂ) (N : ℕ) (x : ℂ) : ℕ → ℂ
  | 0 => x
  | k + 1 => (a (N - (k + 1)) * rec1BackAux a b d N x k - d (N - (k + 1))) / b (N - (k + 1))

/-- The values `w_N = x, w_{N−1}, …, w₀` of backward recursion for 3.6.17. -/
noncomputable def rec1Back (a b d : ℕ → ℂ) (N : ℕ) (x : ℂ) (n : ℕ) : ℂ :=
  rec1BackAux a b d N x (N - n)

theorem rec1Back_spec {a b d : ℕ → ℂ} (hb : ∀ n, b n ≠ 0) (N : ℕ) (x : ℂ) :
    rec1Back a b d N x N = x ∧
      ∀ n, n < N → a n * rec1Back a b d N x (n + 1) - b n * rec1Back a b d N x n = d n := by
  refine ⟨by simp [rec1Back, rec1BackAux], fun n hn => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, N - n = k + 1 := ⟨N - n - 1, by omega⟩
  have hk' : N - (n + 1) = k := by omega
  simp only [rec1Back, hk, hk', rec1BackAux, show N - (k + 1) = n by omega]
  have := hb n
  field_simp
  ring

/-- Uniqueness for backward recursion: two solutions of 3.6.17 on `0, …, N` with the same `w_N`
agree there. -/
theorem rec1_eq_of_end {a b d u v : ℕ → ℂ} (hb : ∀ n, b n ≠ 0) {N : ℕ}
    (hu : ∀ n, n < N → a n * u (n + 1) - b n * u n = d n)
    (hv : ∀ n, n < N → a n * v (n + 1) - b n * v n = d n) (hN : u N = v N) :
    ∀ n, n ≤ N → u n = v n := by
  intro n hn
  obtain ⟨k, hk, rfl⟩ : ∃ k, k ≤ N ∧ n = N - k := ⟨N - n, by omega, by omega⟩
  clear hn
  induction k with
  | zero => simpa using hN
  | succ k ih =>
    have ih := ih (by omega)
    have e1 := hu (N - (k + 1)) (by omega)
    have e2 := hv (N - (k + 1)) (by omega)
    rw [show N - (k + 1) + 1 = N - k by omega, ih] at e1
    rw [show N - (k + 1) + 1 = N - k by omega] at e2
    apply mul_left_cancel₀ (hb (N - (k + 1)))
    linear_combination e2 - e1

/-- Backward recursion from `w_N^{(N)} = 0` gives `wₙ − (w_N/h_N) hₙ`, `n ≤ N`, for every solution
`w` of 3.6.17. -/
theorem rec1Back_eq {a b d w : ℕ → ℂ} (ha : ∀ n, a n ≠ 0) (hb : ∀ n, b n ≠ 0)
    (hw : IsRec1 a b d w) {N n : ℕ} (hn : n ≤ N) :
    rec1Back a b d N 0 n = w n - w N / rec1H a b N * rec1H a b n := by
  have hh := rec1H_isRec1 (b := b) ha
  have hHN := rec1H_ne_zero ha hb N
  refine rec1_eq_of_end (a := a) (d := d) (v := fun n => w n - w N / rec1H a b N * rec1H a b n)
    hb (rec1Back_spec hb N 0).2 (fun k _ => ?_) ?_ n hn
  · have := hh k
    simp only [Pi.zero_apply] at this
    linear_combination hw k - w N / rec1H a b N * this
  · rw [(rec1Back_spec hb N 0).1]; field_simp; ring

/-- **DLMF §3.6(vii)**, 3.6.17: "in the inhomogeneous case it may sometimes be necessary to recur
backwards to achieve stability". If the wanted solution satisfies `wₙ/hₙ → 0`, forward
recursion is unstable (a perturbation `εh` has relative error `→ ∞`), whereas backward recursion
from `w_N^{(N)} = 0` converges to `wₙ` for every fixed `n`. -/
theorem dlmf_3_6_17_backward {a b d w : ℕ → ℂ} (ha : ∀ n, a n ≠ 0) (hb : ∀ n, b n ≠ 0)
    (hw : IsRec1 a b d w) (hwh : Tendsto (fun n => w n / rec1H a b n) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun N => rec1Back a b d N 0 n) atTop (𝓝 (w n)) := by
  have h := tendsto_const_nhds (x := w n) |>.sub (hwh.mul_const (rec1H a b n))
  rw [zero_mul, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop n] with N hN
  rw [rec1Back_eq ha hb hw hN]

theorem dlmf_3_6_17_forward_unstable {a b d w : ℕ → ℂ} (ha : ∀ n, a n ≠ 0) (hb : ∀ n, b n ≠ 0)
    (hw : IsRec1 a b d w) (hwh : Tendsto (fun n => w n / rec1H a b n) atTop (𝓝 0))
    (hwN : ∀ᶠ n in atTop, w n ≠ 0) {ε : ℂ} (hε : ε ≠ 0) :
    IsRec1 a b d (fun n => w n + ε * rec1H a b n) ∧
      Tendsto (fun n => ‖((w n + ε * rec1H a b n) - w n) / w n‖) atTop atTop := by
  refine ⟨fun n => ?_, dlmf_3_6_ii_forward_unstable
    ⟨Eventually.of_forall (rec1H_ne_zero ha hb), hwh⟩ hwN hε⟩
  have := rec1H_isRec1 (b := b) ha n
  simp only [Pi.zero_apply] at this
  linear_combination hw n + ε * this

/-- The wanted solution of 3.6.17 with `wₙ/hₙ → 0` is unique (no normalizing condition is
needed: `ℓ = k = 1`). -/
theorem dlmf_3_6_17_unique {a b d w w' : ℕ → ℂ} (ha : ∀ n, a n ≠ 0) (hb : ∀ n, b n ≠ 0)
    (hw : IsRec1 a b d w) (hw' : IsRec1 a b d w')
    (hwh : Tendsto (fun n => w n / rec1H a b n) atTop (𝓝 0))
    (hw'h : Tendsto (fun n => w' n / rec1H a b n) atTop (𝓝 0)) : w = w' := by
  have hd := hw.sub hw'
  have hC : ∀ n, w n - w' n = (w 0 - w' 0) * rec1H a b n := hd.eq_mul_rec1H ha
  have hlim : Tendsto (fun n => (w n - w' n) / rec1H a b n) atTop (𝓝 (w 0 - w' 0)) :=
    tendsto_const_nhds.congr fun n => by rw [hC n, mul_div_cancel_right₀ _ (rec1H_ne_zero ha hb n)]
  have h2 : Tendsto (fun n => (w n - w' n) / rec1H a b n) atTop (𝓝 (0 - 0)) :=
    (hwh.sub hw'h).congr fun n => by rw [sub_div]
  have := tendsto_nhds_unique hlim h2
  funext n
  have := hC n
  rw [show w 0 - w' 0 = 0 by simpa using ‹w 0 - w' 0 = 0 - 0›, zero_mul] at this
  exact sub_eq_zero.mp this

/-! ### The equation of order `k`, 3.6.18 -/

/-- `w` solves **DLMF 3.6.18** `a_{n,k} w_{n+k} + a_{n,k−1} w_{n+k−1} + ⋯ + a_{n,0} wₙ = dₙ` for all
`n` (`A n j = a_{n,j}`). -/
def IsRecK (k : ℕ) (A : ℕ → Fin (k + 1) → ℂ) (d w : ℕ → ℂ) : Prop :=
  ∀ n, ∑ j : Fin (k + 1), A n j * w (n + j) = d n

/-- The same equation on a finite range: for all `n` with `n + k ≤ M`. -/
def IsRecKUpTo (k : ℕ) (A : ℕ → Fin (k + 1) → ℂ) (d w : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ n, n + k ≤ M → ∑ j : Fin (k + 1), A n j * w (n + j) = d n

/-- The second-order case `k = 2` is 3.6.1 (shifted by one): `a_{n,2} = a_{n+1}`,
`a_{n,1} = −b_{n+1}`, `a_{n,0} = c_{n+1}`. -/
theorem isRecK_two_iff (a b c d w : ℕ → ℂ) :
    IsRec3Inh a b c d w ↔
      IsRecK 2 (fun n => ![c (n + 1), -b (n + 1), a (n + 1)]) (fun n => d (n + 1)) w := by
  constructor
  · intro h n
    have := h (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    simp [Fin.sum_univ_succ]
    ring_nf at this ⊢
    linear_combination this
  · intro h n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := h m
    simp [Fin.sum_univ_succ] at this
    simp only [Nat.add_sub_cancel]
    ring_nf at this ⊢
    linear_combination this

/-- One step of the equivalent first-order system: the state `Wₙ = (wₙ, …, w_{n+k−1})` is mapped
to `W_{n+1}` (shift, and `w_{n+k}` from 3.6.18). -/
noncomputable def companionStep (k : ℕ) (A : ℕ → Fin (k + 1) → ℂ) (d : ℕ → ℂ) (n : ℕ)
    (W : Fin k → ℂ) : Fin k → ℂ := fun i =>
  if h : i.val + 1 < k then W ⟨i.val + 1, h⟩ else
    (d n - ∑ j : Fin k, A n (Fin.castSucc j) * W j) / A n (Fin.last k)

/-- **DLMF §3.6(vii)**: 3.6.18 (with `a_{n,k} ≠ 0`, `k ≥ 1`) is equivalent to the system of `k`
first-order equations `W_{n+1} = companionStep Wₙ` for `Wₙ = (wₙ, …, w_{n+k−1})`. -/
theorem dlmf_3_6_18_system {k : ℕ} (hk : 1 ≤ k) {A : ℕ → Fin (k + 1) → ℂ} {d : ℕ → ℂ}
    (hA : ∀ n, A n (Fin.last k) ≠ 0) (w : ℕ → ℂ) :
    IsRecK k A d w ↔
      ∀ n, (fun i : Fin k => w (n + 1 + i)) = companionStep k A d n (fun i => w (n + i)) := by
  constructor
  · intro h n
    funext i
    simp only [companionStep]
    split_ifs with hi
    · congr 1; omega
    · have hik : i.val = k - 1 := by omega
      have e := h n
      rw [Fin.sum_univ_castSucc] at e
      simp only [Fin.val_castSucc, Fin.val_last] at e
      rw [eq_div_iff (hA n), hik, show n + 1 + (k - 1) = n + k by omega]
      linear_combination e
  · intro h n
    have e := congrFun (h n) ⟨k - 1, by omega⟩
    simp only [companionStep, show ¬ (k - 1 + 1 < k) by omega, dite_false] at e
    rw [show n + 1 + (k - 1) = n + k by omega, eq_div_iff (hA n)] at e
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    linear_combination e

/-! ### Forward recursion (`ℓ = 0`) -/

/-- The states of forward recursion from the initial values `v = (w₀, …, w_{k−1})`. -/
noncomputable def recKState (k : ℕ) (A : ℕ → Fin (k + 1) → ℂ) (d : ℕ → ℂ) (v : Fin k → ℂ) :
    ℕ → Fin k → ℂ
  | 0 => v
  | n + 1 => companionStep k A d n (recKState k A d v n)

/-- Forward recursion for 3.6.18. -/
noncomputable def recKFwd (k : ℕ) (hk : 0 < k) (A : ℕ → Fin (k + 1) → ℂ) (d : ℕ → ℂ)
    (v : Fin k → ℂ) (n : ℕ) : ℂ :=
  recKState k A d v n ⟨0, hk⟩

theorem recKState_eq {k : ℕ} (hk : 0 < k) (A : ℕ → Fin (k + 1) → ℂ) (d : ℕ → ℂ) (v : Fin k → ℂ)
    (n : ℕ) (i : Fin k) : recKState k A d v n i = recKFwd k hk A d v (n + i) := by
  obtain ⟨m, hm⟩ := i
  induction m generalizing n with
  | zero => simp [recKFwd]
  | succ m ih =>
    have := ih (n + 1) (by omega)
    simp only [recKState, companionStep, show m + 1 < k from hm, dite_true] at this
    rw [show n + (m + 1) = n + 1 + m by ring]
    exact this

/-- **DLMF §3.6(vii)**, forward recursion (`ℓ = 0`): with `a_{n,k} ≠ 0`, the solution of 3.6.18 with
given `w₀, …, w_{k−1}` exists (`recKFwd`) and is unique. -/
theorem dlmf_3_6_18_forward {k : ℕ} (hk : 0 < k) {A : ℕ → Fin (k + 1) → ℂ} {d : ℕ → ℂ}
    (hA : ∀ n, A n (Fin.last k) ≠ 0) (v : Fin k → ℂ) :
    IsRecK k A d (recKFwd k hk A d v) ∧ (∀ i : Fin k, recKFwd k hk A d v i = v i) ∧
      ∀ u, IsRecK k A d u → (∀ i : Fin k, u i = v i) → u = recKFwd k hk A d v := by
  have hshift := recKState_eq hk A d v
  refine ⟨fun n => ?_, fun i => ?_, fun u hu hv => ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have h1 := hshift (n + 1) ⟨k - 1, by omega⟩
    simp only [recKState, companionStep, show ¬ (k - 1 + 1 < k) by omega, dite_false] at h1
    rw [show n + 1 + (k - 1) = n + k by omega] at h1
    rw [← h1]
    simp only [← hshift n]
    have := hA n
    field_simp
    ring
  · rw [← show recKState k A d v 0 i = recKFwd k hk A d v i by rw [hshift]; simp]
    rfl
  · funext m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm : m < k
      · rw [hv ⟨m, hm⟩]
        have := hshift 0 ⟨m, hm⟩
        simp only [recKState, zero_add] at this
        exact this
      · -- the equation at `n = m − k` determines `w_m`
        obtain ⟨n, rfl⟩ : ∃ n, m = n + k := ⟨m - k, by omega⟩
        have e1 := hu n
        have e2 : ∑ j : Fin (k + 1), A n j * recKFwd k hk A d v (n + j) = d n := by
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last]
          have h1 := hshift (n + 1) ⟨k - 1, by omega⟩
          simp only [recKState, companionStep, show ¬ (k - 1 + 1 < k) by omega, dite_false] at h1
          rw [show n + 1 + (k - 1) = n + k by omega] at h1
          rw [← h1]
          simp only [← hshift n]
          have := hA n
          field_simp
          ring
        rw [Fin.sum_univ_castSucc] at e1 e2
        simp only [Fin.val_castSucc, Fin.val_last] at e1 e2
        have hlow : ∀ j : Fin k, u (n + j) = recKFwd k hk A d v (n + j) := fun j =>
          ih _ (by omega)
        simp only [hlow] at e1
        apply mul_left_cancel₀ (hA n)
        linear_combination e1 - e2

/-- Finite-range forward uniqueness: two solutions of 3.6.18 on `0, …, M` (equations for
`n + k ≤ M`) with the same `w₀, …, w_{k−1}` agree on `0, …, M`. -/
theorem recK_eq_of_init {k : ℕ} {A : ℕ → Fin (k + 1) → ℂ} {d u v : ℕ → ℂ}
    (hA : ∀ n, A n (Fin.last k) ≠ 0) {M : ℕ} (hu : IsRecKUpTo k A d u M)
    (hv : IsRecKUpTo k A d v M) (h0 : ∀ i, i < k → u i = v i) : ∀ m, m ≤ M → u m = v m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hmk : m < k
    · exact h0 m hmk
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + k := ⟨m - k, by omega⟩
      have e1 := hu n hm
      have e2 := hv n hm
      rw [Fin.sum_univ_castSucc] at e1 e2
      simp only [Fin.val_castSucc, Fin.val_last] at e1 e2
      have hlow : ∀ j : Fin k, u (n + j) = v (n + j) := fun j => ih _ (by omega) (by omega)
      simp only [hlow] at e1
      apply mul_left_cancel₀ (hA n)
      linear_combination e1 - e2

/-- Finite-range backward uniqueness: two solutions of 3.6.18 for `n < N` with the same
`w_N, …, w_{N+k−1}` agree on `0, …, N + k − 1` (`a_{n,0} ≠ 0`). -/
theorem recK_eq_of_end {k : ℕ} {A : ℕ → Fin (k + 1) → ℂ} {d u v : ℕ → ℂ}
    (hA0 : ∀ n, A n 0 ≠ 0) {N : ℕ} (hu : IsRecKUpTo k A d u (N + k - 1))
    (hv : IsRecKUpTo k A d v (N + k - 1)) (hk : 0 < k)
    (h0 : ∀ i, i < k → u (N + i) = v (N + i)) : ∀ n, n ≤ N + k - 1 → u n = v n := by
  have key : ∀ t, ∀ n, n + t = N + k - 1 → u n = v n := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro n hn
      by_cases hnN : N ≤ n
      · obtain ⟨i, rfl⟩ : ∃ i, n = N + i := ⟨n - N, by omega⟩
        exact h0 i (by omega)
      · have e1 := hu n (by omega)
        have e2 := hv n (by omega)
        rw [Fin.sum_univ_succ] at e1 e2
        simp only [Fin.val_zero, add_zero, Fin.val_succ] at e1 e2
        have hhigh : ∀ j : Fin k, u (n + (j + 1)) = v (n + (j + 1)) := fun j =>
          ih (t - (j + 1)) (by omega) _ (by omega)
        simp only [hhigh] at e1
        apply mul_left_cancel₀ (hA0 n)
        linear_combination e1 - e2
  intro n hn
  exact key (N + k - 1 - n) n (by omega)

/-! ### Backward recursion (`ℓ = k`) -/

/-- The reversed coefficients `a_{N−1−m, k−j}` (for `m < N`) of the backward problem. -/
noncomputable def revA (k N : ℕ) (A : ℕ → Fin (k + 1) → ℂ) : ℕ → Fin (k + 1) → ℂ :=
  fun m j => if m < N then A (N - 1 - m) (Fin.rev j) else if j = Fin.last k then 1 else 0

noncomputable def revD (N : ℕ) (d : ℕ → ℂ) : ℕ → ℂ := fun m => if m < N then d (N - 1 - m) else 0

/-- Backward recursion for 3.6.18 from `w_N, …, w_{N+k−1}` (`e`): forward recursion for the
reversed sequence `w_{N+k−1−m}`. -/
noncomputable def recKBwd (k : ℕ) (hk : 0 < k) (A : ℕ → Fin (k + 1) → ℂ) (d : ℕ → ℂ) (N : ℕ)
    (e : Fin k → ℂ) (n : ℕ) : ℂ :=
  recKFwd k hk (revA k N A) (revD N d) (fun i => e (Fin.rev i)) (N + k - 1 - n)

/-- **DLMF §3.6(vii)**, backward recursion (`ℓ = k`): with `a_{n,0} ≠ 0`, given
`w_N, …, w_{N+k−1}`, 3.6.18 for `n = 0, …, N − 1` determines `w_{N−1}, …, w₀` (`recKBwd`),
uniquely. -/
theorem dlmf_3_6_18_backward {k : ℕ} (hk : 0 < k) {A : ℕ → Fin (k + 1) → ℂ} {d : ℕ → ℂ}
    (hA0 : ∀ n, A n 0 ≠ 0) (N : ℕ) (e : Fin k → ℂ) :
    (∀ i : Fin k, recKBwd k hk A d N e (N + i) = e i) ∧
      IsRecKUpTo k A d (recKBwd k hk A d N e) (N + k - 1) ∧
      ∀ u, IsRecKUpTo k A d u (N + k - 1) → (∀ i : Fin k, u (N + i) = e i) →
        ∀ n, n ≤ N + k - 1 → u n = recKBwd k hk A d N e n := by
  have hlead : ∀ m, revA k N A m (Fin.last k) ≠ 0 := fun m => by
    simp only [revA, Fin.rev_last]
    split_ifs
    · exact hA0 _
    · exact one_ne_zero
  obtain ⟨hF, hFv, -⟩ := dlmf_3_6_18_forward hk hlead (fun i => e (Fin.rev i))
  have hend : ∀ i : Fin k, recKBwd k hk A d N e (N + i) = e i := fun i => by
    simp only [recKBwd]
    rw [show N + k - 1 - (N + i) = (Fin.rev i : ℕ) by simp [Fin.val_rev]; omega, hFv, Fin.rev_rev]
  have heq : IsRecKUpTo k A d (recKBwd k hk A d N e) (N + k - 1) := fun n hn => by
    have hnN : n < N := by omega
    have h := hF (N - 1 - n)
    simp only [revA, revD, show N - 1 - n < N by omega, ite_true,
      show N - 1 - (N - 1 - n) = n by omega] at h
    rw [← h, ← Equiv.sum_comp Fin.revPerm]
    refine sum_congr rfl fun j _ => ?_
    simp only [Fin.revPerm_apply, recKBwd]
    congr 2
    simp only [Fin.val_rev]
    omega
  refine ⟨hend, heq, fun u hu hue n hn => ?_⟩
  exact recK_eq_of_end hA0 hu heq hk (fun i hi => by
    rw [hue ⟨i, hi⟩, ← hend ⟨i, hi⟩]) n hn

/-! ### Boundary-value methods: `k − ℓ` conditions at the beginning, `ℓ` at the end -/

/-- The boundary-value problem for 3.6.18 on `0, …, N + ℓ − 1`: `k − ℓ` conditions at the
beginning (`wᵢ = sᵢ`, `i < k − ℓ`), `ℓ` at the end (`w_{N+i} = eᵢ`, `i < ℓ`), and 3.6.18 whenever
all its indices lie in the range. -/
def IsBVk (k ℓ N : ℕ) (A : ℕ → Fin (k + 1) → ℂ) (d s e w : ℕ → ℂ) : Prop :=
  (∀ i, i < k - ℓ → w i = s i) ∧ (∀ i, i < ℓ → w (N + i) = e i) ∧
    IsRecKUpTo k A d w (N + ℓ - 1)

/-- **DLMF §3.6(vii)**: forward recursion is the case `ℓ = 0` — the problem with `k` conditions
at the beginning has a unique solution on `0, …, N − 1` (`N ≥ k`, `a_{n,k} ≠ 0`). -/
theorem dlmf_3_6_vii_ell_zero {k : ℕ} (hk : 0 < k) {A : ℕ → Fin (k + 1) → ℂ} {d : ℕ → ℂ}
    (hA : ∀ n, A n (Fin.last k) ≠ 0) (N : ℕ) (s e : ℕ → ℂ) :
    ∃ w, IsBVk k 0 N A d s e w ∧
      ∀ w', IsBVk k 0 N A d s e w' → ∀ n, n ≤ N - 1 → w' n = w n := by
  obtain ⟨hF, hFv, -⟩ := dlmf_3_6_18_forward hk hA (fun i : Fin k => s i)
  refine ⟨recKFwd k hk A d (fun i : Fin k => s i), ⟨fun i hi => ?_, fun i hi => absurd hi
    (Nat.not_lt_zero _), fun n _ => hF n⟩, fun w' hw' n hn => ?_⟩
  · simpa using hFv ⟨i, by omega⟩
  · refine recK_eq_of_init hA hw'.2.2 (fun n _ => hF n) (fun i hi => ?_) n (by simpa using hn)
    rw [hw'.1 i (by omega)]
    simpa using (hFv ⟨i, hi⟩).symm

/-- **DLMF §3.6(vii)**: backward recursion is the case `ℓ = k` — the problem with `k` conditions
at the end has a unique solution on `0, …, N + k − 1` (`a_{n,0} ≠ 0`). -/
theorem dlmf_3_6_vii_ell_k {k : ℕ} (hk : 0 < k) {A : ℕ → Fin (k + 1) → ℂ} {d : ℕ → ℂ}
    (hA0 : ∀ n, A n 0 ≠ 0) (N : ℕ) (s e : ℕ → ℂ) :
    ∃ w, IsBVk k k N A d s e w ∧
      ∀ w', IsBVk k k N A d s e w' → ∀ n, n ≤ N + k - 1 → w' n = w n := by
  obtain ⟨hend, heq, huniq⟩ := dlmf_3_6_18_backward hk hA0 N (fun i : Fin k => e i)
  refine ⟨recKBwd k hk A d N (fun i : Fin k => e i), ⟨fun i hi => absurd hi (by omega),
    fun i hi => hend ⟨i, hi⟩, heq⟩, fun w' hw' n hn => huniq w' hw'.2.2
      (fun i => hw'.2.1 i i.isLt) n hn⟩

end Azurite.DLMF
