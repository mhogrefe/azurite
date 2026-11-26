/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div.Schoolbook2
import Azurite.AzNat.Equiv.Div.Schoolbook
import Azurite.UInt64.Equiv.Div3By2
import Azurite.UInt64.Equiv.MulAddWithCarry
import Azurite.UInt64.Equiv.MulWithCarry

/-!
# Schoolbook division with two quotient limbs per pass: correctness

* `subMul2Limbs_toNat`: the value identity of the double subtract-multiply row.
* `trialQuot2_spec`: the trial digit is `min (2^128 − 1) ⌊T / D⌋`.
* `trial_bounds`: such a digit is at least the true one and overshoots the window by less
  than `γ W` (pure arithmetic).
* `schoolbookDivModLimbs.step2_spec`: one step leaves the remainder and two true quotient
  limbs.
* `schoolbookDivModLimbs.goFast_eq_go`, **`schoolbookDivModLimbs_eq_fast`** (`@[csimp]`):
  `schoolbookDivModLimbs` and `schoolbookDivModLimbsFast` are the same function.
-/

namespace Azurite.AzNat

/-- The value of the slice `a[lo : lo + len)`. -/
local macro "sl(" a:term ", " lo:term ", " len:term ")" : term =>
  `(toNatLimbsList (List.take $len (List.drop $lo (Array.toList $a))))

/-! ### The borrow of one limb -/

theorem subBorrowLimb_spec (a l bw : UInt64) (hbw : bw.toNat ≤ 1) :
    (subBorrowLimb a l bw).1.toNat + l.toNat + bw.toNat
        = a.toNat + (subBorrowLimb a l bw).2.toNat * 2 ^ 64 ∧
      (subBorrowLimb a l bw).2.toNat ≤ 1 := by
  unfold subBorrowLimb
  simp only
  have ha := a.toNat_lt
  have hl := l.toNat_lt
  have h1 : (a - l).toNat = (2 ^ 64 - l.toNat + a.toNat) % 2 ^ 64 := UInt64.toNat_sub a l
  have h2 : (a - l - bw).toNat = (2 ^ 64 - bw.toNat + (a - l).toNat) % 2 ^ 64 :=
    UInt64.toNat_sub _ _
  have h3 : (a < l) ↔ a.toNat < l.toNat := UInt64.lt_iff_toNat_lt
  have h4 : (a - l < bw) ↔ (a - l).toNat < bw.toNat := UInt64.lt_iff_toNat_lt
  have one : (1 : UInt64).toNat = 1 := rfl
  have zero : (0 : UInt64).toNat = 0 := rfl
  by_cases c1 : a.toNat < l.toNat <;> by_cases c2 : (a - l).toNat < bw.toNat
  · simp only [h3.mpr c1, h4.mpr c2, ↓reduceIte, UInt64.toNat_add, one]; omega
  · simp only [h3.mpr c1, h4.not.mpr c2, ↓reduceIte, UInt64.toNat_add, one, zero]; omega
  · simp only [h3.not.mpr c1, h4.mpr c2, ↓reduceIte, UInt64.toNat_add, one, zero]; omega
  · simp only [h3.not.mpr c1, h4.not.mpr c2, ↓reduceIte, UInt64.toNat_add, zero]; omega

/-! ### The double subtract-multiply row -/

private theorem getElem_of_take_eq (x y : Array UInt64) (i m : ℕ) (hi : i < m)
    (hx : i < x.size) (hy : i < y.size) (h : x.toList.take m = y.toList.take m) :
    x[i] = y[i] := by
  have h1 := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_take, hi, ↓reduceIte] at h1
  rw [List.getElem?_eq_getElem (by simpa using hx),
    List.getElem?_eq_getElem (by simpa using hy)] at h1
  simpa using h1

private theorem toNat_bne_zero (u : UInt64) (h : u.toNat ≤ 1) : (u != 0).toNat = u.toNat := by
  have h0 : (0 : UInt64).toNat = 0 := rfl
  by_cases hu : u = 0
  · subst hu; rfl
  · have : u.toNat ≠ 0 := fun h' => hu (UInt64.toNat_inj.mp (h'.trans h0.symm))
    have hb : (u != 0) = true := by simpa using hu
    rw [hb]; simp only [Bool.toNat_true]; omega

/-- `subMul2Limbs.go` preserves any prefix up to `loA + k`. -/
theorem subMul2Limbs.go_toList_take_le (b : Array UInt64) (loB n : Nat) (q₀ q₁ : UInt64)
    (a : Array UInt64) (loA k : Nat) (c₀ c₁ bw : UInt64)
    (hA : loA + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) (m : Nat) (hm : m ≤ loA + k) :
    (subMul2Limbs.go b loB n q₀ q₁ a loA k c₀ c₁ bw hA hB).1.toList.take m
      = a.toList.take m := by
  induction h_sub : n - k generalizing a k c₀ c₁ bw with
  | zero =>
    have h_ge : n ≤ k := by omega
    rw [subMul2Limbs.go]
    simp [Nat.not_lt.mpr h_ge]
  | succ p ih =>
    have h_lt : k < n := by omega
    rw [subMul2Limbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ _ _ (by omega) (by omega)]
    rw [Array.toList_set, List.take_set_of_le (by omega)]

/-- `subMul2Limbs.go` preserves the suffix of `a` from `loA + n`. -/
theorem subMul2Limbs.go_toList_drop (b : Array UInt64) (loB n : Nat) (q₀ q₁ : UInt64)
    (a : Array UInt64) (loA k : Nat) (c₀ c₁ bw : UInt64)
    (hA : loA + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) :
    (subMul2Limbs.go b loB n q₀ q₁ a loA k c₀ c₁ bw hA hB).1.toList.drop (loA + n)
      = a.toList.drop (loA + n) := by
  induction h_sub : n - k generalizing a k c₀ c₁ bw with
  | zero =>
    have h_ge : n ≤ k := by omega
    rw [subMul2Limbs.go]
    simp [Nat.not_lt.mpr h_ge]
  | succ p ih =>
    have h_lt : k < n := by omega
    rw [subMul2Limbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ _ _ (by omega)]
    rw [Array.toList_set, List.drop_set]
    simp
    omega

private theorem slice_cons (A : Array UInt64) (i m : Nat) (hi : i < A.size) :
    sl(A, i, m + 1) = A[i].toNat + sl(A, i + 1, m) * 2 ^ 64 := by
  have h_lt_list : i < A.toList.length := hi
  rw [List.drop_eq_getElem_cons h_lt_list, List.take_succ_cons, toNatLimbsList_cons]
  rw [show A.toList[i] = A[i] from (Array.getElem_toList hi).symm]
  ring

/-- Invariant of `subMul2Limbs.go`: with `τ` the two limbs above the slice after the
(unwritten) subtraction of the final carry. -/
private theorem subMul2Limbs.go_correct (b : Array UInt64) (loB n : Nat) (q₀ q₁ : UInt64) :
    ∀ (p : ℕ) (a : Array UInt64) (loA k : Nat) (c₀ c₁ bw : UInt64)
      (hA : loA + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) (h0 : loA + n < a.size)
      (h1 : loA + n + 1 < a.size), n - k = p → k ≤ n → bw.toNat ≤ 1 →
      ∃ τ, τ < 2 ^ 128 ∧
        sl(a, loA + k, p)
            + 2 ^ (64 * p) * ((a[loA + n]'h0).toNat + 2 ^ 64 * (a[loA + n + 1]'h1).toNat)
            + (subMul2Limbs.go b loB n q₀ q₁ a loA k c₀ c₁ bw hA hB).2.toNat
              * (2 ^ (64 * p) * 2 ^ 128)
          = sl((subMul2Limbs.go b loB n q₀ q₁ a loA k c₀ c₁ bw hA hB).1, loA + k, p)
            + 2 ^ (64 * p) * τ
            + (q₀.toNat + q₁.toNat * 2 ^ 64) * sl(b, loB + k, p)
            + (c₀.toNat + c₁.toNat * 2 ^ 64 + bw.toNat) := by
  intro p
  induction p with
  | zero =>
    intro a loA k c₀ c₁ bw hA hB h0 h1 hp hk hbw
    have h_ge : ¬ k < n := by omega
    have s0 := subBorrowLimb_spec (a[loA + n]'h0) c₀ bw hbw
    have s1 := subBorrowLimb_spec (a[loA + n + 1]'h1) c₁
      (subBorrowLimb (a[loA + n]'h0) c₀ bw).2 s0.2
    have h_eq : subMul2Limbs.go b loB n q₀ q₁ a loA k c₀ c₁ bw hA hB
        = (a, (subBorrowLimb (a[loA + n + 1]'h1) c₁
            (subBorrowLimb (a[loA + n]'h0) c₀ bw).2).2 != 0) := by
      rw [subMul2Limbs.go]; simp only [h_ge, ↓reduceDIte]
    rw [h_eq]
    simp only [toNat_bne_zero _ s1.2]
    refine ⟨(subBorrowLimb (a[loA + n]'h0) c₀ bw).1.toNat
      + 2 ^ 64 * (subBorrowLimb (a[loA + n + 1]'h1) c₁
          (subBorrowLimb (a[loA + n]'h0) c₀ bw).2).1.toNat, ?_, ?_⟩
    · have := (subBorrowLimb (a[loA + n]'h0) c₀ bw).1.toNat_lt
      have := (subBorrowLimb (a[loA + n + 1]'h1) c₁
          (subBorrowLimb (a[loA + n]'h0) c₀ bw).2).1.toNat_lt
      omega
    · simp only [List.take_zero, toNatLimbsList, List.foldr_nil, Nat.mul_zero, pow_zero,
        Nat.one_mul, Nat.zero_add, Nat.add_zero]
      have e0 := s0.1
      have e1 := s1.1
      linear_combination -e0 - (2 ^ 64) * e1
  | succ p ih =>
    intro a loA k c₀ c₁ bw hA hB h0 h1 hp hk hbw
    have h_lt : k < n := by omega
    have h_iA : loA + k < a.size := by omega
    have h_iB : loB + k < b.size := by omega
    set m₁ := UInt64.mulWithCarry b[loB + k] q₀ c₀ with hm₁
    set m₂ := UInt64.mulAddWithCarry b[loB + k] q₁ m₁.1 c₁ with hm₂
    set s := subBorrowLimb a[loA + k] m₁.2 bw with hs
    set a' := a.set (loA + k) s.1 with ha'
    have hA' : loA + n + 2 ≤ a'.size := by rw [ha', Array.size_set]; exact hA
    have h_eq : subMul2Limbs.go b loB n q₀ q₁ a loA k c₀ c₁ bw hA hB
        = subMul2Limbs.go b loB n q₀ q₁ a' loA (k + 1) m₂.2 m₂.1 s.2 hA' hB := by
      conv_lhs => rw [subMul2Limbs.go]
      simp only [h_lt, ↓reduceDIte]
      rfl
    have hs_spec := subBorrowLimb_spec a[loA + k] m₁.2 bw hbw
    rw [← hs] at hs_spec
    obtain ⟨τ, hτ, h_ih⟩ := ih a' loA (k + 1) m₂.2 m₂.1 s.2 hA' hB (by omega) (by omega)
      (by omega) (by omega) hs_spec.2
    have h_mc1 := UInt64.mulWithCarry_eq b[loB + k] q₀ c₀
    rw [← hm₁] at h_mc1
    have h_mc2 := UInt64.mulAddWithCarry_eq b[loB + k] q₁ m₁.1 c₁
    rw [← hm₂] at h_mc2
    have h_res_size : (subMul2Limbs.go b loB n q₀ q₁ a' loA (k + 1) m₂.2 m₂.1 s.2
        hA' hB).1.size = a.size := by
      rw [subMul2Limbs.go_size, ha', Array.size_set]
    have h_res_lt : loA + k < (subMul2Limbs.go b loB n q₀ q₁ a' loA (k + 1) m₂.2 m₂.1 s.2
        hA' hB).1.size := by rw [h_res_size]; exact h_iA
    have h_a'_lt : loA + k < a'.size := by rw [ha', Array.size_set]; exact h_iA
    have h_res_i : (subMul2Limbs.go b loB n q₀ q₁ a' loA (k + 1) m₂.2 m₂.1 s.2
        hA' hB).1[loA + k]'h_res_lt = s.1 := by
      rw [getElem_of_take_eq _ a' (loA + k) (loA + (k + 1)) (by omega) h_res_lt h_a'_lt
        (subMul2Limbs.go_toList_take_le b loB n q₀ q₁ a' loA (k + 1) m₂.2 m₂.1 s.2 hA' hB
          _ (Nat.le_refl _))]
      simp [ha']
    have h_drop_eq : a'.toList.drop (loA + (k + 1)) = a.toList.drop (loA + (k + 1)) := by
      rw [ha', Array.toList_set, List.drop_set]; simp
    have h_top0 : a'[loA + n]'(by omega) = a[loA + n]'(by omega) := by
      simp only [ha']; rw [Array.getElem_set_ne]; omega
    have h_top1 : a'[loA + n + 1]'(by omega) = a[loA + n + 1]'(by omega) := by
      simp only [ha']; rw [Array.getElem_set_ne]; omega
    rw [h_top0, h_top1, h_drop_eq] at h_ih
    refine ⟨τ, hτ, ?_⟩
    rw [h_eq, slice_cons _ (loA + k) p h_res_lt, h_res_i,
      slice_cons a (loA + k) p h_iA, slice_cons b (loB + k) p h_iB,
      show 64 * (p + 1) = 64 * p + 64 by ring, pow_add,
      show loA + k + 1 = loA + (k + 1) by ring, show loB + k + 1 = loB + (k + 1) by ring]
    have e := hs_spec.1
    linear_combination (2 ^ 64) * h_ih + h_mc1 + (2 ^ 64) * h_mc2 - e

/-- **The double row**: with `X` the `n + 2` limbs of the window and `B` the divisor,
`X + borrow · 2^(64 (n + 2)) = L' + 2^(64 n) τ + (q₀ + q₁ 2^64) B`, where `L'` is the new low
`n` limbs and `τ < 2^128` the (unwritten) top two limbs of the difference. -/
theorem subMul2Limbs_toNat (a b : Array UInt64) (loA loB n : Nat) (q₀ q₁ : UInt64)
    (hA : loA + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) (h0 : loA + n < a.size)
    (h1 : loA + n + 1 < a.size) :
    ∃ τ, τ < 2 ^ 128 ∧
      sl(a, loA, n) + 2 ^ (64 * n) * ((a[loA + n]'h0).toNat + 2 ^ 64 * (a[loA + n + 1]'h1).toNat)
          + (subMul2Limbs a b loA loB n q₀ q₁ hA hB).2.toNat * (2 ^ (64 * n) * 2 ^ 128)
        = sl((subMul2Limbs a b loA loB n q₀ q₁ hA hB).1, loA, n) + 2 ^ (64 * n) * τ
          + (q₀.toNat + q₁.toNat * 2 ^ 64) * sl(b, loB, n) := by
  have z : (0 : UInt64).toNat = 0 := rfl
  unfold subMul2Limbs
  obtain ⟨τ, hτ, h⟩ := subMul2Limbs.go_correct b loB n q₀ q₁ n a loA 0 0 0 0 hA hB h0 h1
    (Nat.sub_zero n) (Nat.zero_le _) (by rw [z]; exact Nat.zero_le _)
  refine ⟨τ, hτ, ?_⟩
  -- (`Nat.add_zero` only while no `_ + 0` stands at the top of a side: as a `rfl` lemma it
  -- leaves the kernel a definitional check, which runs away on `Y + 0 ≡ Y` for a large `Y`)
  simp only [Nat.add_zero] at h
  rw [z, Nat.zero_mul] at h
  linear_combination h

/-! ### The trial digit -/

/-- **The trial digit is `min (2^128 − 1) ⌊T / D⌋`**, for the four limbs `T` and the
normalized two limbs `D`. -/
theorem trialQuot2_spec (a₃ a₂ a₁ a₀ d₁ d₀ v : UInt64) (hd : 2 ^ 63 ≤ d₁.toNat)
    (hv : v = UInt64.reciprocal3By2 d₁ d₀ hd) (D T : ℕ)
    (hD : D = d₁.toNat * 2 ^ 64 + d₀.toNat)
    (hT : T = (a₃.toNat * 2 ^ 64 + a₂.toNat) * 2 ^ 128 + (a₁.toNat * 2 ^ 64 + a₀.toNat)) :
    ((trialQuot2 a₃ a₂ a₁ a₀ d₁ d₀ v).1.toNat * 2 ^ 64
          + (trialQuot2 a₃ a₂ a₁ a₀ d₁ d₀ v).2.toNat) * D ≤ T ∧
      ∀ x, x * D ≤ T → x < 2 ^ 128 →
        x ≤ (trialQuot2 a₃ a₂ a₁ a₀ d₁ d₀ v).1.toNat * 2 ^ 64
          + (trialQuot2 a₃ a₂ a₁ a₀ d₁ d₀ v).2.toNat := by
  have h3 := a₃.toNat_lt
  have h2 := a₂.toNat_lt
  have h1 := a₁.toNat_lt
  have h0 := a₀.toNat_lt
  have hd0 := d₀.toNat_lt
  have hd1 := d₁.toNat_lt
  unfold trialQuot2
  by_cases hc : a₃ > d₁ ∨ (a₃ = d₁ ∧ a₂ ≥ d₀)
  · simp only [hc, ↓reduceIte]
    have hm : ((0 : UInt64) - 1).toNat = 2 ^ 64 - 1 := rfl
    rw [hm]
    have hge : D ≤ a₃.toNat * 2 ^ 64 + a₂.toNat := by
      rw [hD]
      rcases hc with h | ⟨h, h'⟩
      · have := UInt64.lt_iff_toNat_lt.mp h
        omega
      · have := UInt64.le_iff_toNat_le.mp h'
        rw [h]; omega
    refine ⟨?_, fun x _ hx => by omega⟩
    have e : ((2 ^ 64 - 1) * 2 ^ 64 + (2 ^ 64 - 1)) * D
        ≤ 2 ^ 128 * (a₃.toNat * 2 ^ 64 + a₂.toNat) :=
      Nat.mul_le_mul (by decide) hge
    have e' : 2 ^ 128 * (a₃.toNat * 2 ^ 64 + a₂.toNat)
        = (a₃.toNat * 2 ^ 64 + a₂.toNat) * 2 ^ 128 := Nat.mul_comm _ _
    omega
  · simp only [hc, ↓reduceIte]
    have hlt : a₃.toNat * 2 ^ 64 + a₂.toNat < d₁.toNat * 2 ^ 64 + d₀.toNat := by
      by_contra hge
      apply hc
      by_cases h : d₁.toNat < a₃.toNat
      · exact Or.inl (UInt64.lt_iff_toNat_lt.mpr h)
      · have he : a₃ = d₁ := UInt64.toNat_inj.mp (by omega)
        exact Or.inr ⟨he, UInt64.le_iff_toNat_le.mpr (by rw [he] at hge; omega)⟩
    obtain ⟨e1, r1⟩ := UInt64.toNat_div3By2 a₃ a₂ a₁ d₁ d₀ v hd hlt hv
    obtain ⟨e2, r2⟩ := UInt64.toNat_div3By2 (UInt64.div3By2 a₃ a₂ a₁ d₁ d₀ v).2.1
      (UInt64.div3By2 a₃ a₂ a₁ d₁ d₀ v).2.2 a₀ d₁ d₀ v hd r1 hv
    generalize (UInt64.div3By2 (UInt64.div3By2 a₃ a₂ a₁ d₁ d₀ v).2.1
      (UInt64.div3By2 a₃ a₂ a₁ d₁ d₀ v).2.2 a₀ d₁ d₀ v) = s at e2 r2 ⊢
    generalize UInt64.div3By2 a₃ a₂ a₁ d₁ d₀ v = r at e1 r1 e2 ⊢
    have e1' : r.1.toNat * D + (r.2.1.toNat * 2 ^ 64 + r.2.2.toNat)
        = a₃.toNat * 2 ^ 128 + a₂.toNat * 2 ^ 64 + a₁.toNat := by rw [hD]; exact e1
    have e2' : s.1.toNat * D + (s.2.1.toNat * 2 ^ 64 + s.2.2.toNat)
        = r.2.1.toNat * 2 ^ 128 + r.2.2.toNat * 2 ^ 64 + a₀.toNat := by rw [hD]; exact e2
    have r2' : s.2.1.toNat * 2 ^ 64 + s.2.2.toNat < D := by rw [hD]; exact r2
    have key : (r.1.toNat * 2 ^ 64 + s.1.toNat) * D + (s.2.1.toNat * 2 ^ 64 + s.2.2.toNat)
        = T := by
      rw [hT]
      linear_combination (2 ^ 64) * e1' + e2'
    refine ⟨by omega, fun x hx _ => ?_⟩
    by_contra hcon
    have : (r.1.toNat * 2 ^ 64 + s.1.toNat + 1) * D ≤ x * D :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

/-- **The arithmetic of a trial digit** (any base `γ`, any place value `W`): a digit `q̂` with
`q̂ D ≤ T`, largest below `γ` with that property, is at least the true digit `⌊X / B⌋` of
`X = T W + Aᵣ`, `B = D W + Bᵣ`, and `q̂ B` exceeds `X` by less than `γ W`. -/
theorem trial_bounds {W D T Ar Br qh γ X B : ℕ} (hX : X = T * W + Ar) (hB : B = D * W + Br)
    (hAr : Ar < W) (hBr : Br < W) (hq : qh * D ≤ T) (hqγ : qh < γ)
    (hmax : ∀ x, x * D ≤ T → x < γ → x ≤ qh) (hXB : X < γ * B) :
    X / B ≤ qh ∧ qh * B < X + γ * W := by
  have hW : 0 < W := by omega
  have hBpos : 0 < B := Nat.pos_of_ne_zero (by rintro rfl; simp at hXB)
  constructor
  · apply hmax
    · have h1 : X / B * B ≤ X := Nat.div_mul_le_self X B
      have h2 : X / B * (D * W) ≤ X / B * B := Nat.mul_le_mul_left _ (by omega)
      have h3 : X / B * D * W < (T + 1) * W := by
        rw [Nat.mul_assoc]
        have : (T + 1) * W = T * W + W := by ring
        omega
      have := Nat.lt_of_mul_lt_mul_right h3
      omega
    · exact (Nat.div_lt_iff_lt_mul hBpos).mpr hXB
  · have h1 : qh * B = qh * D * W + qh * Br := by rw [hB]; ring
    have h2 : qh * D * W ≤ T * W := Nat.mul_le_mul_right _ hq
    have h3 : qh * Br < γ * W := by
      calc qh * Br ≤ qh * W := Nat.mul_le_mul_left _ hBr.le
        _ < γ * W := Nat.mul_lt_mul_of_pos_right hqγ hW
    omega

/-! ### The arithmetic of one step -/

/-- After the row, without a borrow: the low limbs are the remainder and the digit is right. -/
private theorem step_arith_pos {X B Nn Q L τ : ℕ} (hrow : X = L + Nn * τ + Q * B)
    (hBpos : 0 < B) (hB1 : B < Nn) (hq1 : X / B ≤ Q) : L < B ∧ X = Q * B + L := by
  have h1 := Nat.lt_mul_div_succ X hBpos
  have h2 : B * (X / B + 1) ≤ B * (Q + 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : B * (Q + 1) = Q * B + B := by ring
  rcases Nat.eq_zero_or_pos τ with h | h
  · subst h
    rw [Nat.mul_zero] at hrow
    omega
  · have := Nat.le_mul_of_pos_right Nn h
    omega

/-- After the row, with a borrow: the top two limbs are all ones, and the low limbs are
`X − q̂ B + 2^(64 n)`. -/
private theorem step_arith_neg {X B Nn Q L τ : ℕ}
    (hrow : X + Nn * 2 ^ 128 = L + Nn * τ + Q * B) (hτ : τ < 2 ^ 128) (hL : L < Nn)
    (hq2 : Q * B < X + Nn) : L + Q * B = X + Nn := by
  have hτ' : 2 ^ 128 ≤ τ + 1 := by
    by_contra hc
    have h1 : Nn * (τ + 2) ≤ Nn * 2 ^ 128 := Nat.mul_le_mul_left _ (by omega)
    have h2 : Nn * (τ + 2) = Nn * τ + 2 * Nn := by ring
    omega
  have h3 : Nn * 2 ^ 128 = Nn * τ + Nn := by
    rw [show (2 : ℕ) ^ 128 = τ + 1 by omega]; ring
  omega

/-- One addition of the divisor that carries out ends the correction. -/
private theorem step_arith_add1 {X B Nn Q L S : ℕ} (hb : L + Q * B = X + Nn)
    (hadd : S + Nn = L + B) (hL : L < Nn) :
    1 ≤ Q ∧ S < B ∧ X = (Q - 1) * B + S := by
  have hQ : 1 ≤ Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · subst h; rw [Nat.zero_mul] at hb; omega
    · exact h
  have h1 : (Q - 1) * B = Q * B - B := by rw [Nat.sub_mul, Nat.one_mul]
  have h2 : B ≤ Q * B := Nat.le_mul_of_pos_left B hQ
  omega

/-- A second addition always carries out (the divisor is normalized). -/
private theorem step_arith_add2 {X B Nn Q L S₁ S₂ c : ℕ} (hb : L + Q * B = X + Nn)
    (hadd1 : S₁ = L + B) (hS1 : S₁ < Nn) (hadd2 : S₂ + c * Nn = S₁ + B) (hS2 : S₂ < Nn)
    (hc : c ≤ 1) (hB2 : Nn ≤ 2 * B) :
    2 ≤ Q ∧ S₂ < B ∧ X = (Q - 2) * B + S₂ := by
  have hc1 : c = 1 := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; rw [Nat.zero_mul] at hadd2; omega
    · omega
  subst hc1
  rw [Nat.one_mul] at hadd2
  have hQ : 2 ≤ Q := by
    by_contra hlt
    have : Q * B ≤ 1 * B := Nat.mul_le_mul_right _ (by omega)
    omega
  have h1 : (Q - 2) * B = Q * B - 2 * B := by rw [Nat.sub_mul]
  have h2 : 2 * B ≤ Q * B := Nat.mul_le_mul_right _ hQ
  omega

/-! ### Storing the digits -/

private theorem slice_snoc2 (A : Array UInt64) (i m : ℕ) (h : i + m + 1 < A.size) :
    sl(A, i, m + 2) = sl(A, i, m)
      + 2 ^ (64 * m) * ((A[i + m]'(by omega)).toNat + 2 ^ 64 * (A[i + m + 1]'h).toNat) := by
  have h1 := toNatLimbsList_drop_take_succ A i m (by omega)
  have h2 := toNatLimbsList_drop_take_succ A i (m + 1) (by omega)
  simp only [← Nat.add_assoc] at h2
  rw [h2, h1, show 64 * (m + 1) = 64 * m + 64 by ring, pow_add]
  ring

private theorem slice_set_outside (A : Array UInt64) (p n i : ℕ) (v : UInt64)
    (hi : i < A.size) (h : p + n ≤ i) : sl(A.set i v hi, p, n) = sl(A, p, n) := by
  rw [Array.toList_set, List.drop_set]
  simp only [show ¬ i < p by omega, ↓reduceIte]
  rw [List.take_set_of_le (by omega)]

private theorem slice_two (A : Array UInt64) (i : ℕ) (h : i + 1 < A.size) :
    sl(A, i, 2) = (A[i]'(by omega)).toNat + 2 ^ 64 * (A[i + 1]'h).toNat := by
  have e0 : sl(A, i + 1 + 1, 0) = 0 := rfl
  rw [slice_cons A i 1 (by omega), slice_cons A (i + 1) 0 h, e0]
  ring

private theorem digits_sub (q₁ q₀ k : UInt64) (hk : k.toNat ≤ q₁.toNat * 2 ^ 64 + q₀.toNat)
    (hk2 : k.toNat ≤ 2) :
    (q₀ - k).toNat + 2 ^ 64 * (q₁ - (if q₀ < k then 1 else 0)).toNat
      = q₁.toNat * 2 ^ 64 + q₀.toNat - k.toNat := by
  have h0 := q₀.toNat_lt
  have h1 := q₁.toNat_lt
  have e0 : (q₀ - k).toNat = (2 ^ 64 - k.toNat + q₀.toNat) % 2 ^ 64 := UInt64.toNat_sub _ _
  have one : (1 : UInt64).toNat = 1 := rfl
  have zero : (0 : UInt64).toNat = 0 := rfl
  by_cases c : q₀.toNat < k.toNat
  · simp only [UInt64.lt_iff_toNat_lt.mpr c, ↓reduceIte]
    have e1 : (q₁ - 1).toNat = (2 ^ 64 - (1 : UInt64).toNat + q₁.toNat) % 2 ^ 64 :=
      UInt64.toNat_sub _ _
    rw [one] at e1
    omega
  · simp only [UInt64.lt_iff_toNat_lt.not.mpr c, ↓reduceIte]
    have e1 : (q₁ - 0).toNat = (2 ^ 64 - (0 : UInt64).toNat + q₁.toNat) % 2 ^ 64 :=
      UInt64.toNat_sub _ _
    rw [zero] at e1
    omega

private theorem storeDigits_spec (arr : Array UInt64) (p n : ℕ) (q₁ q₀ k : UInt64)
    (h : p + n + 1 < arr.size) (hk : k.toNat ≤ q₁.toNat * 2 ^ 64 + q₀.toNat)
    (hk2 : k.toNat ≤ 2) :
    sl(schoolbookDivModLimbs.storeDigits arr (p + n) q₁ q₀ k h, p, n) = sl(arr, p, n) ∧
      sl(schoolbookDivModLimbs.storeDigits arr (p + n) q₁ q₀ k h, p + n, 2)
        = q₁.toNat * 2 ^ 64 + q₀.toNat - k.toNat ∧
      (schoolbookDivModLimbs.storeDigits arr (p + n) q₁ q₀ k h).toList.take p
        = arr.toList.take p ∧
      (schoolbookDivModLimbs.storeDigits arr (p + n) q₁ q₀ k h).toList.drop (p + n + 2)
        = arr.toList.drop (p + n + 2) := by
  unfold schoolbookDivModLimbs.storeDigits
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [slice_set_outside _ p n _ _ _ (by omega), slice_set_outside _ p n _ _ _ (by omega)]
  · rw [slice_two _ (p + n) (by simp only [Array.size_set]; omega)]
    have g0 : ((arr.set (p + n) (q₀ - k) (by omega)).set (p + n + 1)
        (q₁ - (if q₀ < k then 1 else 0)) (by rw [Array.size_set]; exact h))[p + n]'(by
          simp only [Array.size_set]; omega) = q₀ - k := by
      rw [Array.getElem_set_ne _ (by rw [Array.size_set]; omega) (by omega),
        Array.getElem_set_self]
    have g1 : ((arr.set (p + n) (q₀ - k) (by omega)).set (p + n + 1)
        (q₁ - (if q₀ < k then 1 else 0)) (by rw [Array.size_set]; exact h))[p + n + 1]'(by
          simp only [Array.size_set]; omega) = q₁ - (if q₀ < k then 1 else 0) :=
      Array.getElem_set_self _
    rw [g0, g1]
    exact digits_sub q₁ q₀ k hk hk2
  · rw [Array.toList_set, List.take_set_of_le (by omega), Array.toList_set,
      List.take_set_of_le (by omega)]
  · rw [Array.toList_set, List.drop_set]
    simp only [show p + n + 1 < p + n + 2 by omega, ↓reduceIte]
    rw [Array.toList_set, List.drop_set]
    simp only [show p + n < p + n + 2 by omega, ↓reduceIte]

/-! ### One step -/

private theorem slice_lt (A : Array UInt64) (i m : ℕ) : sl(A, i, m) < 2 ^ (64 * m) :=
  lt_of_lt_of_le (toNatLimbsList_lt_pow _)
    (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (List.length_take_le _ _)))

private theorem drop_add_of_drop (x y : List UInt64) (m k : ℕ) (h : x.drop m = y.drop m) :
    x.drop (m + k) = y.drop (m + k) := by
  rw [← List.drop_drop, ← List.drop_drop, h]

private theorem subMul2Limbs_frames (a b : Array UInt64) (loA loB n : Nat) (q₀ q₁ : UInt64)
    (hA : loA + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) :
    (subMul2Limbs a b loA loB n q₀ q₁ hA hB).1.toList.take loA = a.toList.take loA ∧
      (subMul2Limbs a b loA loB n q₀ q₁ hA hB).1.toList.drop (loA + n)
        = a.toList.drop (loA + n) :=
  ⟨subMul2Limbs.go_toList_take_le b loB n q₀ q₁ a loA 0 0 0 0 hA hB loA (Nat.le_add_right _ _),
    subMul2Limbs.go_toList_drop b loB n q₀ q₁ a loA 0 0 0 0 hA hB⟩

private theorem addSame_frames (a b : Array UInt64) (loA loB n : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    (addSameLengthLimbs a b loA loB n hA hB).1.toList.take loA = a.toList.take loA ∧
      (addSameLengthLimbs a b loA loB n hA hB).1.toList.drop (loA + n)
        = a.toList.drop (loA + n) :=
  ⟨addSameLengthLimbs.go_toList_take_le b loA loB n a 0 false hA hB loA
      (Nat.le_add_right _ _),
    addSameLengthLimbs.go_toList_drop b loA loB n a 0 false hA hB⟩

private theorem addSame_spec (a b : Array UInt64) (loA loB n : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    sl((addSameLengthLimbs a b loA loB n hA hB).1, loA, n)
        + (addSameLengthLimbs a b loA loB n hA hB).2.toNat * 2 ^ (64 * n)
      = sl(a, loA, n) + sl(b, loB, n) := by
  have h := addSameLengthLimbs_toNat a b loA loB n hA hB
  generalize addSameLengthLimbs a b loA loB n hA hB = y at h ⊢
  obtain ⟨a', c⟩ := y
  exact h

/-- The end of a step: the corrected digits stored above a remainder. -/
private theorem step_close (a arr : Array UInt64) (p n : ℕ) (q₁ q₀ k : UInt64) (B X Q : ℕ)
    (h : p + n + 1 < arr.size) (hQ : Q = q₁.toNat * 2 ^ 64 + q₀.toNat) (hk2 : k.toNat ≤ 2)
    (hk : k.toNat ≤ Q) (hR : sl(arr, p, n) < B) (hXe : X = (Q - k.toNat) * B + sl(arr, p, n))
    (ht : arr.toList.take p = a.toList.take p)
    (hdr : arr.toList.drop (p + n) = a.toList.drop (p + n)) :
    sl(schoolbookDivModLimbs.storeDigits arr (p + n) q₁ q₀ k h, p, n) < B ∧
      X = sl(schoolbookDivModLimbs.storeDigits arr (p + n) q₁ q₀ k h, p + n, 2) * B
        + sl(schoolbookDivModLimbs.storeDigits arr (p + n) q₁ q₀ k h, p, n) ∧
      (schoolbookDivModLimbs.storeDigits arr (p + n) q₁ q₀ k h).toList.take p
        = a.toList.take p ∧
      (schoolbookDivModLimbs.storeDigits arr (p + n) q₁ q₀ k h).toList.drop (p + n + 2)
        = a.toList.drop (p + n + 2) := by
  obtain ⟨e1, e2, e3, e4⟩ := storeDigits_spec arr p n q₁ q₀ k h (hQ ▸ hk) hk2
  rw [e1, e2, e3, e4, ← hQ]
  exact ⟨hR, hXe, ht, drop_add_of_drop _ _ _ 2 hdr⟩

/-- The correction is right: from the value identity of the row and the two properties of
the trial digit. -/
private theorem correct2_spec (a arr b : Array UInt64) (neg : Bool) (loA loB n j : ℕ)
    (q₁ q₀ : UInt64) (hA : loA + j + n + 2 ≤ arr.size) (hB : loB + n ≤ b.size)
    (X Q τ : ℕ) (hQ : Q = q₁.toNat * 2 ^ 64 + q₀.toNat)
    (hrow : X + neg.toNat * (2 ^ (64 * n) * 2 ^ 128)
      = sl(arr, loA + j, n) + 2 ^ (64 * n) * τ + Q * sl(b, loB, n))
    (hτ : τ < 2 ^ 128) (hBpos : 0 < sl(b, loB, n)) (hB2 : 2 ^ (64 * n) ≤ 2 * sl(b, loB, n))
    (hq1 : X / sl(b, loB, n) ≤ Q) (hq2 : Q * sl(b, loB, n) < X + 2 ^ (64 * n))
    (ht : arr.toList.take (loA + j) = a.toList.take (loA + j))
    (hdr : arr.toList.drop (loA + j + n) = a.toList.drop (loA + j + n)) :
    sl(schoolbookDivModLimbs.correct2 arr b neg loA loB n j q₁ q₀ hA hB, loA + j, n)
        < sl(b, loB, n) ∧
      X = sl(schoolbookDivModLimbs.correct2 arr b neg loA loB n j q₁ q₀ hA hB, loA + j + n, 2)
            * sl(b, loB, n)
          + sl(schoolbookDivModLimbs.correct2 arr b neg loA loB n j q₁ q₀ hA hB, loA + j, n) ∧
      (schoolbookDivModLimbs.correct2 arr b neg loA loB n j q₁ q₀ hA hB).toList.take (loA + j)
        = a.toList.take (loA + j) ∧
      (schoolbookDivModLimbs.correct2 arr b neg loA loB n j q₁ q₀ hA hB).toList.drop
          (loA + j + n + 2) = a.toList.drop (loA + j + n + 2) := by
  obtain ⟨Nn, hNn⟩ : ∃ Nn, Nn = 2 ^ (64 * n) := ⟨_, rfl⟩
  have hB1 : sl(b, loB, n) < Nn := by rw [hNn]; exact slice_lt b loB n
  have hLlt : sl(arr, loA + j, n) < Nn := by rw [hNn]; exact slice_lt arr (loA + j) n
  rw [← hNn] at hrow hB2 hq2
  have zero : (0 : UInt64).toNat = 0 := rfl
  have one : (1 : UInt64).toNat = 1 := rfl
  have two : (2 : UInt64).toNat = 2 := rfl
  unfold schoolbookDivModLimbs.correct2
  cases neg with
  | true =>
    simp only [↓reduceIte]
    rw [Bool.toNat_true, Nat.one_mul] at hrow
    have hbq := step_arith_neg hrow hτ hLlt hq2
    have hadd := addSame_spec arr b (loA + j) loB n (by omega) hB
    obtain ⟨fs1, fs2⟩ := addSame_frames arr b (loA + j) loB n (by omega) hB
    have hSlt := slice_lt (addSameLengthLimbs arr b (loA + j) loB n (by omega) hB).1
      (loA + j) n
    have hss := addSameLengthLimbs_size arr b (loA + j) loB n (by omega) hB
    rw [← hNn] at hadd hSlt
    by_cases hc : (addSameLengthLimbs arr b (loA + j) loB n (by omega) hB).2 = true
    · simp only [hc, ↓reduceIte]
      rw [hc, Bool.toNat_true, Nat.one_mul] at hadd
      obtain ⟨hQ1, hSB, hXe⟩ := step_arith_add1 hbq hadd hLlt
      exact step_close a _ (loA + j) n q₁ q₀ 1 _ _ Q (by omega) hQ (by rw [one]; omega)
        (by rw [one]; exact hQ1) hSB (by rw [one]; exact hXe) (fs1.trans ht)
        (fs2.trans hdr)
    · have hc' : (addSameLengthLimbs arr b (loA + j) loB n (by omega) hB).2 = false := by
        simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte]
      rw [hc', Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hadd
      have hadd2 := addSame_spec (addSameLengthLimbs arr b (loA + j) loB n (by omega) hB).1 b
        (loA + j) loB n (by omega) hB
      obtain ⟨ft1, ft2⟩ := addSame_frames
        (addSameLengthLimbs arr b (loA + j) loB n (by omega) hB).1 b (loA + j) loB n
        (by omega) hB
      have hS2lt := slice_lt (addSameLengthLimbs
        (addSameLengthLimbs arr b (loA + j) loB n (by omega) hB).1 b (loA + j) loB n
        (by omega) hB).1 (loA + j) n
      rw [← hNn] at hadd2 hS2lt
      obtain ⟨hQ2, hSB, hXe⟩ := step_arith_add2 hbq hadd hSlt hadd2
        hS2lt (Bool.toNat_le _) hB2
      exact step_close a _ (loA + j) n q₁ q₀ 2 _ _ Q
        (by rw [addSameLengthLimbs_size]; omega) hQ (by rw [two]) (by rw [two]; exact hQ2)
        hSB (by rw [two]; exact hXe) (ft1.trans (fs1.trans ht)) (ft2.trans (fs2.trans hdr))
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hrow
    obtain ⟨hLB, hXe⟩ := step_arith_pos hrow hBpos hB1 hq1
    exact step_close a arr (loA + j) n q₁ q₀ 0 _ _ Q (by omega) hQ (by rw [zero]; omega)
      (by rw [zero]; omega) hLB (by rw [zero, Nat.sub_zero]; exact hXe) ht hdr

/-- A step with a given trial digit is right when the digit has the two properties of
`trial_bounds`. -/
private theorem finish2_spec (a b : Array UInt64) (loA loB n j : ℕ) (q₁ q₀ : UInt64)
    (hA : loA + j + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) (Q : ℕ)
    (hQ : Q = q₁.toNat * 2 ^ 64 + q₀.toNat) (hBpos : 0 < sl(b, loB, n))
    (hB2 : 2 ^ (64 * n) ≤ 2 * sl(b, loB, n))
    (hq1 : sl(a, loA + j, n + 2) / sl(b, loB, n) ≤ Q)
    (hq2 : Q * sl(b, loB, n) < sl(a, loA + j, n + 2) + 2 ^ (64 * n)) :
    sl(schoolbookDivModLimbs.finish2 a b loA loB n j q₁ q₀ hA hB, loA + j, n)
        < sl(b, loB, n) ∧
      sl(a, loA + j, n + 2)
        = sl(schoolbookDivModLimbs.finish2 a b loA loB n j q₁ q₀ hA hB, loA + j + n, 2)
            * sl(b, loB, n)
          + sl(schoolbookDivModLimbs.finish2 a b loA loB n j q₁ q₀ hA hB, loA + j, n) ∧
      (schoolbookDivModLimbs.finish2 a b loA loB n j q₁ q₀ hA hB).toList.take (loA + j)
        = a.toList.take (loA + j) ∧
      (schoolbookDivModLimbs.finish2 a b loA loB n j q₁ q₀ hA hB).toList.drop
          (loA + j + n + 2) = a.toList.drop (loA + j + n + 2) := by
  obtain ⟨τ, hτ, hrow⟩ := subMul2Limbs_toNat a b (loA + j) loB n q₀ q₁ hA hB (by omega)
    (by omega)
  obtain ⟨fr1, fr2⟩ := subMul2Limbs_frames a b (loA + j) loB n q₀ q₁ hA hB
  have hXdec := slice_snoc2 a (loA + j) n (by omega)
  rw [← hXdec, show q₀.toNat + q₁.toNat * 2 ^ 64 = Q by omega] at hrow
  unfold schoolbookDivModLimbs.finish2
  exact correct2_spec a _ b _ loA loB n j q₁ q₀ (by rw [subMul2Limbs_size]; exact hA) hB _ Q τ
    hQ hrow hτ hBpos hB2 hq1 hq2 fr1 fr2

/-- **One step is right**: for a normalized divisor `B` of `n ≥ 2` limbs and a window of
`n + 2` limbs below `2^128 B`, `step2` leaves the remainder in the low `n` limbs and the two
quotient limbs above, and changes nothing outside the window. -/
theorem schoolbookDivModLimbs.step2_spec (a b : Array UInt64) (loA loB n j : ℕ)
    (d₁ d₀ v : UInt64) (hA : loA + j + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) (hn : 2 ≤ n)
    (hd1 : d₁ = b[loB + (n - 2) + 1]'(by omega)) (hd0 : d₀ = b[loB + (n - 2)]'(by omega))
    (hd : 2 ^ 63 ≤ d₁.toNat) (hv : v = UInt64.reciprocal3By2 d₁ d₀ hd)
    (hX : sl(a, loA + j, n + 2) < 2 ^ 128 * sl(b, loB, n)) :
    sl(schoolbookDivModLimbs.step2 a b loA loB n j d₁ d₀ v hA hB hn, loA + j, n)
        < sl(b, loB, n) ∧
      sl(a, loA + j, n + 2)
        = sl(schoolbookDivModLimbs.step2 a b loA loB n j d₁ d₀ v hA hB hn, loA + j + n, 2)
            * sl(b, loB, n)
          + sl(schoolbookDivModLimbs.step2 a b loA loB n j d₁ d₀ v hA hB hn, loA + j, n) ∧
      (schoolbookDivModLimbs.step2 a b loA loB n j d₁ d₀ v hA hB hn).toList.take (loA + j)
        = a.toList.take (loA + j) ∧
      (schoolbookDivModLimbs.step2 a b loA loB n j d₁ d₀ v hA hB hn).toList.drop
          (loA + j + n + 2) = a.toList.drop (loA + j + n + 2) := by
  -- the place values
  obtain ⟨W, hW⟩ : ∃ W, W = 2 ^ (64 * (n - 2)) := ⟨_, rfl⟩
  have hNW : 2 ^ (64 * n) = W * 2 ^ 128 := by
    rw [hW, ← pow_add]; congr 1; omega
  -- the divisor
  obtain ⟨D, hD⟩ : ∃ D, D = d₁.toNat * 2 ^ 64 + d₀.toNat := ⟨_, rfl⟩
  have hBdec : sl(b, loB, n) = D * W + sl(b, loB, n - 2) := by
    have h := slice_snoc2 b loB (n - 2) (by omega)
    rw [Nat.sub_add_cancel hn] at h
    rw [h, ← hd0, ← hd1, hD, hW]; ring
  have hBr : sl(b, loB, n - 2) < W := by rw [hW]; exact slice_lt b loB (n - 2)
  have hD127 : 2 ^ 127 ≤ D := by rw [hD]; omega
  have hB2 : 2 ^ (64 * n) ≤ 2 * sl(b, loB, n) := by
    have := Nat.mul_le_mul_right W hD127
    rw [hNW]
    omega
  have hWpos : 0 < W := by rw [hW]; positivity
  have hBpos : 0 < sl(b, loB, n) := by
    have := Nat.mul_le_mul_right W hD127
    omega
  -- the window
  obtain ⟨T, hT⟩ : ∃ T, T = ((a[loA + j + n + 1]'(by omega)).toNat * 2 ^ 64
      + (a[loA + j + n]'(by omega)).toNat) * 2 ^ 128
      + ((a[loA + j + (n - 2) + 1]'(by omega)).toNat * 2 ^ 64
        + (a[loA + j + (n - 2)]'(by omega)).toNat) := ⟨_, rfl⟩
  have hXdec1 := slice_snoc2 a (loA + j) n (by omega)
  have hXdec2 : sl(a, loA + j, n) = sl(a, loA + j, n - 2)
      + W * ((a[loA + j + (n - 2)]'(by omega)).toNat
        + 2 ^ 64 * (a[loA + j + (n - 2) + 1]'(by omega)).toNat) := by
    have h := slice_snoc2 a (loA + j) (n - 2) (by omega)
    rw [Nat.sub_add_cancel hn] at h
    rw [h, hW]
  have hXeq : sl(a, loA + j, n + 2) = T * W + sl(a, loA + j, n - 2) := by
    rw [hXdec1, hXdec2, hT, hNW]; ring
  have hAr : sl(a, loA + j, n - 2) < W := by rw [hW]; exact slice_lt a (loA + j) (n - 2)
  -- the trial digit
  obtain ⟨hq, hmax⟩ := trialQuot2_spec (a[loA + j + n + 1]'(by omega))
    (a[loA + j + n]'(by omega)) (a[loA + j + (n - 2) + 1]'(by omega))
    (a[loA + j + (n - 2)]'(by omega)) d₁ d₀ v hd hv D T hD hT
  have hQlt : (trialQuot2 (a[loA + j + n + 1]'(by omega)) (a[loA + j + n]'(by omega))
      (a[loA + j + (n - 2) + 1]'(by omega)) (a[loA + j + (n - 2)]'(by omega)) d₁ d₀ v).1.toNat
        * 2 ^ 64
      + (trialQuot2 (a[loA + j + n + 1]'(by omega)) (a[loA + j + n]'(by omega))
      (a[loA + j + (n - 2) + 1]'(by omega)) (a[loA + j + (n - 2)]'(by omega)) d₁ d₀ v).2.toNat
      < 2 ^ 128 := by
    have := (trialQuot2 (a[loA + j + n + 1]'(by omega)) (a[loA + j + n]'(by omega))
      (a[loA + j + (n - 2) + 1]'(by omega)) (a[loA + j + (n - 2)]'(by omega))
      d₁ d₀ v).1.toNat_lt
    have := (trialQuot2 (a[loA + j + n + 1]'(by omega)) (a[loA + j + n]'(by omega))
      (a[loA + j + (n - 2) + 1]'(by omega)) (a[loA + j + (n - 2)]'(by omega))
      d₁ d₀ v).2.toNat_lt
    omega
  obtain ⟨hq1, hq2⟩ := trial_bounds hXeq hBdec hAr hBr hq hQlt hmax hX
  rw [Nat.mul_comm (2 ^ 128) W, ← hNW] at hq2
  exact finish2_spec a b loA loB n j _ _ hA hB _ rfl hBpos hB2 hq1 hq2

/-! ### The loop -/

private theorem slice_split (A : Array UInt64) (lo k m : ℕ) (h : lo + (m + k) ≤ A.size) :
    sl(A, lo, m + k) = sl(A, lo, k) + sl(A, lo + k, m) * 2 ^ (64 * k) := by
  have h1 := toNatLimbsList_drop_take_split A lo (m + k) k (by omega) h
  rw [Nat.add_sub_cancel] at h1
  exact h1

private theorem take_of_take (x y : List UInt64) (k m : ℕ) (h : x.take m = y.take m)
    (hk : k ≤ m) : x.take k = y.take k := by
  have h1 := congrArg (List.take k) h
  rwa [List.take_take, List.take_take, Nat.min_eq_left hk] at h1

private theorem slice_of_take (x y : Array UInt64) (lo k : ℕ)
    (h : x.toList.take (lo + k) = y.toList.take (lo + k)) : sl(x, lo, k) = sl(y, lo, k) := by
  rw [List.take_drop, List.take_drop, h]

private theorem slice_of_drop (x y : Array UInt64) (lo k : ℕ)
    (h : x.toList.drop lo = y.toList.drop lo) : sl(x, lo, k) = sl(y, lo, k) := by
  rw [h]

/-- **The loop is right**: `goFast` leaves the remainder and the true quotient limbs, as
`schoolbookDivModLimbs.go` does. -/
theorem schoolbookDivModLimbs.goFast_spec (b : Array UInt64) (loA loB n : ℕ) (d₁ d₀ v : UInt64)
    (hd : 2 ^ 63 ≤ d₁.toNat) (hB : loB + n ≤ b.size) (hn : 2 ≤ n)
    (hd1 : d₁ = b[loB + (n - 2) + 1]'(by omega)) (hd0 : d₀ = b[loB + (n - 2)]'(by omega))
    (hv : v = UInt64.reciprocal3By2 d₁ d₀ hd) (hBpos : 0 < sl(b, loB, n)) :
    ∀ (j : ℕ) (a : Array UInt64) (hA : loA + n + j ≤ a.size),
      sl(a, loA, n + j) < 2 ^ (64 * j) * sl(b, loB, n) →
      sl(schoolbookDivModLimbs.goFast a b loA loB n j d₁ d₀ v hd hA hB hn, loA, n)
          < sl(b, loB, n) ∧
        sl(a, loA, n + j)
          = sl(schoolbookDivModLimbs.goFast a b loA loB n j d₁ d₀ v hd hA hB hn, loA + n, j)
              * sl(b, loB, n)
            + sl(schoolbookDivModLimbs.goFast a b loA loB n j d₁ d₀ v hd hA hB hn, loA, n) ∧
        (schoolbookDivModLimbs.goFast a b loA loB n j d₁ d₀ v hd hA hB hn).toList.take loA
          = a.toList.take loA ∧
        (schoolbookDivModLimbs.goFast a b loA loB n j d₁ d₀ v hd hA hB hn).toList.drop
          (loA + n + j) = a.toList.drop (loA + n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro a hA hinv
    match j with
    | 0 =>
      rw [schoolbookDivModLimbs.goFast]
      have e0 : sl(a, loA + n, 0) = 0 := rfl
      rw [e0, Nat.zero_mul, Nat.zero_add]
      rw [Nat.mul_zero, pow_zero, Nat.one_mul] at hinv
      exact ⟨hinv, rfl, rfl, rfl⟩
    | 1 =>
      rw [schoolbookDivModLimbs.goFast]
      have h := schoolbookDivModLimbs.go_toNat a b loA loB n 1 d₁ (UInt64.reciprocal d₁ hd)
        hA hB (by omega) ⟨by omega, hd1.trans (by congr 1; omega)⟩ hd ⟨hd, rfl⟩ hBpos hinv
      exact ⟨h.1, h.2, schoolbookDivModLimbs.go_toList_take a b loA loB n 1 _ _ hA hB _,
        schoolbookDivModLimbs.go_toList_drop a b loA loB n 1 _ _ hA hB _⟩
    | j + 2 =>
      rw [schoolbookDivModLimbs.goFast]
      have hA' : loA + j + n + 2 ≤ a.size := by omega
      -- the window of the step
      have hsp := slice_split a loA j (n + 2) (by omega)
      rw [show n + 2 + j = n + (j + 2) by omega] at hsp
      have hXw : sl(a, loA + j, n + 2) < 2 ^ 128 * sl(b, loB, n) := by
        have h1 : sl(a, loA + j, n + 2) * 2 ^ (64 * j)
            < 2 ^ (64 * j) * (2 ^ 128 * sl(b, loB, n)) := by
          have e : (2 : ℕ) ^ (64 * (j + 2)) = 2 ^ (64 * j) * 2 ^ 128 := by
            rw [← pow_add]; congr 1
          rw [e, Nat.mul_assoc] at hinv
          omega
        rw [Nat.mul_comm] at h1
        exact Nat.lt_of_mul_lt_mul_left h1
      obtain ⟨s1, s2, s3, s4⟩ := schoolbookDivModLimbs.step2_spec a b loA loB n j d₁ d₀ v hA'
        hB hn hd1 hd0 hd hv hXw
      suffices key : ∀ (a₁ : Array UInt64) (hA₁ : loA + n + j ≤ a₁.size),
          a₁.size = a.size → sl(a₁, loA + j, n) < sl(b, loB, n) →
          sl(a, loA + j, n + 2) = sl(a₁, loA + j + n, 2) * sl(b, loB, n) + sl(a₁, loA + j, n) →
          a₁.toList.take (loA + j) = a.toList.take (loA + j) →
          a₁.toList.drop (loA + j + n + 2) = a.toList.drop (loA + j + n + 2) →
          sl(schoolbookDivModLimbs.goFast a₁ b loA loB n j d₁ d₀ v hd hA₁ hB hn, loA, n)
              < sl(b, loB, n) ∧
            sl(a, loA, n + (j + 2))
              = sl(schoolbookDivModLimbs.goFast a₁ b loA loB n j d₁ d₀ v hd hA₁ hB hn,
                    loA + n, j + 2) * sl(b, loB, n)
                + sl(schoolbookDivModLimbs.goFast a₁ b loA loB n j d₁ d₀ v hd hA₁ hB hn,
                    loA, n) ∧
            (schoolbookDivModLimbs.goFast a₁ b loA loB n j d₁ d₀ v hd hA₁ hB hn).toList.take loA
              = a.toList.take loA ∧
            (schoolbookDivModLimbs.goFast a₁ b loA loB n j d₁ d₀ v hd hA₁ hB hn).toList.drop
              (loA + n + (j + 2)) = a.toList.drop (loA + n + (j + 2)) from
        key _ _ (schoolbookDivModLimbs.step2_size a b loA loB n j d₁ d₀ v hA' hB hn) s1 s2 s3 s4
      clear s1 s2 s3 s4
      intro a₁ hA₁ hsz s1 s2 s3 s4
      -- the invariant after the step
      have hsp1 := slice_split a₁ loA j n (by omega)
      have hpre : sl(a₁, loA, j) = sl(a, loA, j) := slice_of_take a₁ a loA j s3
      have hprelt := slice_lt a loA j
      have hinv1 : sl(a₁, loA, n + j) < 2 ^ (64 * j) * sl(b, loB, n) := by
        rw [hsp1, hpre]
        have h1 : (sl(a₁, loA + j, n) + 1) * 2 ^ (64 * j)
            ≤ sl(b, loB, n) * 2 ^ (64 * j) := Nat.mul_le_mul_right _ s1
        rw [Nat.add_mul, Nat.one_mul] at h1
        rw [Nat.mul_comm (2 ^ (64 * j))]
        omega
      obtain ⟨t1, t2, t3, t4⟩ := ih j (by omega) a₁ hA₁ hinv1
      have hsz2 := schoolbookDivModLimbs.goFast_size a₁ b loA loB n j d₁ d₀ v hd hA₁ hB hn
      generalize schoolbookDivModLimbs.goFast a₁ b loA loB n j d₁ d₀ v hd hA₁ hB hn = a₂
        at t1 t2 t3 t4 hsz2 ⊢
      refine ⟨t1, ?_, t3.trans (take_of_take _ _ loA (loA + j) s3 (by omega)), ?_⟩
      · -- the quotient limbs of the step are still there
        have hq2 : sl(a₂, loA + n + j, 2) = sl(a₁, loA + j + n, 2) := by
          rw [show loA + j + n = loA + n + j by omega]
          exact slice_of_drop a₂ a₁ _ 2 t4
        have hspq := slice_split a₂ (loA + n) j 2 (by omega)
        rw [show 2 + j = j + 2 by omega] at hspq
        rw [hspq, hq2, hsp, s2]
        rw [hsp1, hpre] at t2
        linear_combination t2
      · have h1 := drop_add_of_drop _ _ _ 2 t4
        rw [show loA + n + (j + 2) = loA + n + j + 2 by omega, h1,
          show loA + n + j + 2 = loA + j + n + 2 by omega, s4]

/-! ### The two functions are the same -/

private theorem eq_of_toNatLimbsList_eq : ∀ (l₁ l₂ : List UInt64), l₁.length = l₂.length →
    toNatLimbsList l₁ = toNatLimbsList l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, hl, h => by
    rw [toNatLimbsList_cons, toNatLimbsList_cons] at h
    have hx := x.toNat_lt
    have hy := y.toNat_lt
    have h1 : x.toNat = y.toNat := by omega
    have h2 : toNatLimbsList xs = toNatLimbsList ys := by omega
    rw [UInt64.toNat_inj.mp h1,
      eq_of_toNatLimbsList_eq xs ys (by simpa using hl) h2]

private theorem list_split3 (l : List UInt64) (p n m : ℕ) :
    l = l.take p ++ ((l.drop p).take n ++ ((l.drop (p + n)).take m ++ l.drop (p + n + m))) := by
  have e1 : l.drop (p + n) = (l.drop p).drop n := by rw [List.drop_drop]
  have e2 : l.drop (p + n + m) = ((l.drop p).drop n).drop m := by
    rw [List.drop_drop, List.drop_drop, Nat.add_assoc]
  rw [e2, e1, List.take_append_drop, List.take_append_drop, List.take_append_drop]

private theorem divMod_unique {B q₁ r₁ q₂ r₂ : ℕ} (hB : 0 < B) (h : q₁ * B + r₁ = q₂ * B + r₂)
    (h1 : r₁ < B) (h2 : r₂ < B) : q₁ = q₂ ∧ r₁ = r₂ := by
  have e1 : (q₁ * B + r₁) / B = q₁ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt h1, Nat.zero_add]
  have e2 : (q₂ * B + r₂) / B = q₂ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt h2, Nat.zero_add]
  have hq : q₁ = q₂ := by rw [← e1, ← e2, h]
  subst hq
  exact ⟨rfl, by omega⟩

/-- **The fast loop computes the same array** as `schoolbookDivModLimbs.go`, under the
invariant of the division. -/
theorem schoolbookDivModLimbs.goFast_eq_go (a b : Array UInt64) (loA loB n m : ℕ)
    (d₁ d₀ v : UInt64) (hd : 2 ^ 63 ≤ d₁.toNat) (hA : loA + n + m ≤ a.size)
    (hB : loB + n ≤ b.size) (hn : 2 ≤ n)
    (hd1 : d₁ = b[loB + (n - 2) + 1]'(by omega)) (hd0 : d₀ = b[loB + (n - 2)]'(by omega))
    (hv : v = UInt64.reciprocal3By2 d₁ d₀ hd) (hBpos : 0 < sl(b, loB, n))
    (hinv : sl(a, loA, n + m) < 2 ^ (64 * m) * sl(b, loB, n)) :
    schoolbookDivModLimbs.goFast a b loA loB n m d₁ d₀ v hd hA hB hn
      = schoolbookDivModLimbs.go a b loA loB n m d₁ (UInt64.reciprocal d₁ hd) hA hB
          (by omega) := by
  obtain ⟨f1, f2, f3, f4⟩ := schoolbookDivModLimbs.goFast_spec b loA loB n d₁ d₀ v hd hB hn
    hd1 hd0 hv hBpos m a hA hinv
  have g := schoolbookDivModLimbs.go_toNat a b loA loB n m d₁ (UInt64.reciprocal d₁ hd)
    hA hB (by omega) ⟨by omega, hd1.trans (by congr 1; omega)⟩ hd ⟨hd, rfl⟩ hBpos hinv
  have g3 := schoolbookDivModLimbs.go_toList_take a b loA loB n m d₁
    (UInt64.reciprocal d₁ hd) hA hB (by omega)
  have g4 := schoolbookDivModLimbs.go_toList_drop a b loA loB n m d₁
    (UInt64.reciprocal d₁ hd) hA hB (by omega)
  have hfs := schoolbookDivModLimbs.goFast_size a b loA loB n m d₁ d₀ v hd hA hB hn
  have hgs := schoolbookDivModLimbs.go_size a b loA loB n m d₁ (UInt64.reciprocal d₁ hd)
    hA hB (by omega)
  obtain ⟨g1, g2⟩ := g
  generalize schoolbookDivModLimbs.goFast a b loA loB n m d₁ d₀ v hd hA hB hn = x
    at f1 f2 f3 f4 hfs ⊢
  generalize schoolbookDivModLimbs.go a b loA loB n m d₁ (UInt64.reciprocal d₁ hd) hA hB
    (by omega) = y at g1 g2 g3 g4 hgs ⊢
  obtain ⟨hq, hr⟩ := divMod_unique hBpos (f2.symm.trans g2) f1 g1
  apply Array.ext'
  rw [list_split3 x.toList loA n m, list_split3 y.toList loA n m, f3, g3, f4, g4,
    eq_of_toNatLimbsList_eq _ _ (by
      rw [List.length_take, List.length_take, List.length_drop, List.length_drop,
        Array.length_toList, Array.length_toList, hfs, hgs]) hr,
    eq_of_toNatLimbsList_eq _ _ (by
      rw [List.length_take, List.length_take, List.length_drop, List.length_drop,
        Array.length_toList, Array.length_toList, hfs, hgs]) hq]

private theorem subSame_spec (a b : Array UInt64) (loA loB n : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    sl(a, loA, n) + (subSameLengthLimbs a b loA loB n hA hB).2.toNat * 2 ^ (64 * n)
      = sl((subSameLengthLimbs a b loA loB n hA hB).1, loA, n) + sl(b, loB, n) := by
  have h := subSameLengthLimbs_toNat a b loA loB n hA hB
  generalize subSameLengthLimbs a b loA loB n hA hB = y at h ⊢
  obtain ⟨a', c⟩ := y
  exact h

/-- **`schoolbookDivModLimbs` is `schoolbookDivModLimbsFast`**: the compiled division takes
two quotient limbs per pass. -/
@[csimp] theorem schoolbookDivModLimbs_eq_fast :
    @schoolbookDivModLimbs = @schoolbookDivModLimbsFast := by
  funext a b loA loB n m h_n_pos hA hB hbn1
  unfold schoolbookDivModLimbsFast
  by_cases hn : n < 2
  · simp only [hn, ↓reduceDIte]
  · simp only [hn, ↓reduceDIte]
    unfold schoolbookDivModLimbs
    simp only
    have hn2 : 2 ≤ n := by omega
    have hlb := schoolbookDivModLimbs.divisor_bound b loB n h_n_pos hB hbn1
    have hpow : (2 : ℕ) ^ (64 * n) = 2 * 2 ^ (64 * n - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hBpos : 0 < sl(b, loB, n) := lt_of_lt_of_le (by positivity) hlb
    have hd1 : b[loB + n - 1]'(by omega) = b[loB + (n - 2) + 1]'(by omega) := by
      congr 1; omega
    have hd0 : b[loB + n - 2]'(by omega) = b[loB + (n - 2)]'(by omega) := by
      congr 1; omega
    have hcmp := compareLimbs_eq_compare_slice a b (loA + m) loB n (by omega) hB
    have hsp := slice_split a loA m n (by omega)
    have hprelt := slice_lt a loA m
    by_cases hc : compareLimbs a b (loA + m) loB n (by omega) hB = Ordering.lt
    · simp only [hc, ↓reduceIte]
      congr 1
      rw [hcmp] at hc
      have hlt := Nat.compare_eq_lt.mp hc
      refine (schoolbookDivModLimbs.goFast_eq_go a b loA loB n m _ _ _ hbn1 (by omega) hB hn2
        hd1 hd0 rfl hBpos ?_).symm
      rw [hsp]
      have h1 : (sl(a, loA + m, n) + 1) * 2 ^ (64 * m) ≤ sl(b, loB, n) * 2 ^ (64 * m) :=
        Nat.mul_le_mul_right _ hlt
      rw [Nat.add_mul, Nat.one_mul] at h1
      rw [Nat.mul_comm (2 ^ (64 * m))]
      omega
    · simp only [hc, ↓reduceIte]
      congr 1
      rw [hcmp] at hc
      have hge : sl(b, loB, n) ≤ sl(a, loA + m, n) := by
        by_contra hlt
        exact hc (Nat.compare_eq_lt.mpr (by omega))
      have hsub := subSame_spec a b (loA + m) loB n (by omega) hB
      have htoplt := slice_lt a (loA + m) n
      have hreslt := slice_lt (subSameLengthLimbs a b (loA + m) loB n (by omega) hB).1
        (loA + m) n
      have hrs := subSameLengthLimbs_size a b (loA + m) loB n (by omega) hB
      have hfr := subSameLengthLimbs.go_toList_take_le b (loA + m) loB n a 0 false
        (by omega) hB (loA + m) (Nat.le_add_right _ _)
      have hc0 : (subSameLengthLimbs a b (loA + m) loB n (by omega) hB).2 = false := by
        by_contra hne
        have : (subSameLengthLimbs a b (loA + m) loB n (by omega) hB).2 = true := by
          simpa using hne
        rw [this, Bool.toNat_true, Nat.one_mul] at hsub
        omega
      rw [hc0, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hsub
      refine (schoolbookDivModLimbs.goFast_eq_go _ b loA loB n m _ _ _ hbn1
        (by rw [hrs]; omega) hB hn2 hd1 hd0 rfl hBpos ?_).symm
      have hsp' := slice_split (subSameLengthLimbs a b (loA + m) loB n (by omega) hB).1
        loA m n (by rw [hrs]; omega)
      have hpre := slice_of_take (subSameLengthLimbs a b (loA + m) loB n (by omega) hB).1 a
        loA m hfr
      rw [hsp', hpre]
      have h1 : (sl((subSameLengthLimbs a b (loA + m) loB n (by omega) hB).1, loA + m, n) + 1)
          * 2 ^ (64 * m) ≤ sl(b, loB, n) * 2 ^ (64 * m) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1
      rw [Nat.mul_comm (2 ^ (64 * m))]
      omega

end Azurite.AzNat
