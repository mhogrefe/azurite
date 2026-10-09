/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sum
import Azurite.AzFloat.Equiv.Add
import Azurite.AzFloat.Equiv.AddSubRat
import Azurite.AzFloat.Equiv.Compare
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzFloat.Equiv.Shift
import Azurite.AzFloat.Equiv.Ziv

/-!
## Correctness of `AzFloat.sumPrecRound`

`sumPrecRound_eq`: the sum is the correct rounding of `Spec.sum`, the fold of the two-operand
specification `Spec.add` over the values.  The proof follows the algorithm: the window sums are
exact (`toVal_exactSum`), the tail is bounded (`abs_realSum_lt_tailBound`), the sign procedure
is exact (`signSum_eq`), and in the main branch either the Ziv bracket decides
(`roundingPossible_eq`) or the unique `(p + 1)`-bit float in the bracket (`boundary_unique`) is
compared with the sum through the sign of the remainder.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The specification -/

namespace Spec

/-- The specification of a sum: the fold of `add` over the values, `NaN` propagating. -/
noncomputable def sum (xs : List AzFloat) : Option EReal :=
  xs.foldr (fun x acc => x.toVal.bind fun a => acc.bind fun b => add a b) (some 0)

theorem add_top_top : add ⊤ ⊤ = some ⊤ := by unfold add; simp
theorem add_bot_bot : add ⊥ ⊥ = some ⊥ := by unfold add; simp
theorem add_top_bot : add ⊤ ⊥ = none := by unfold add; simp
theorem add_bot_top : add ⊥ ⊤ = none := by unfold add; simp
theorem add_top_coe (r : ℝ) : add ⊤ r = some ⊤ := by unfold add; simp
theorem add_coe_top (r : ℝ) : add r ⊤ = some ⊤ := by unfold add; simp
theorem add_bot_coe (r : ℝ) : add ⊥ r = some ⊥ := by unfold add; simp
theorem add_coe_bot (r : ℝ) : add r ⊥ = some ⊥ := by unfold add; simp

end Spec

/-- The real value of a float: the value of a finite one, `0` for the others. -/
noncomputable def fval : AzFloat → ℝ
  | finite s e _ m _ => finiteVal s e m
  | _ => 0

/-- The real sum of the finite values of a list. -/
noncomputable def realSum (l : List AzFloat) : ℝ := (l.map fval).sum

@[simp] theorem realSum_nil : realSum [] = 0 := rfl

theorem realSum_cons (x : AzFloat) (l : List AzFloat) : realSum (x :: l) = fval x + realSum l := by
  simp [realSum]

theorem toVal_of_isFinite {x : AzFloat} (hx : x.isFinite = true) :
    x.toVal = some ((fval x : ℝ) : EReal) := by
  cases x <;> simp_all [isFinite, fval, toVal]

theorem isFinite_of_toVal_coe {x : AzFloat} {r : ℝ} (h : x.toVal = some (r : EReal)) :
    x.isFinite = true := by
  cases x with
  | nan => simp at h
  | infinity s => cases s <;> simp at h
  | zero => rfl
  | finite _ _ _ _ _ => rfl

theorem fval_of_toVal_coe {x : AzFloat} {r : ℝ} (h : x.toVal = some (r : EReal)) :
    fval x = r := by
  have := toVal_of_isFinite (isFinite_of_toVal_coe h)
  rw [this, Option.some.injEq, EReal.coe_eq_coe_iff] at h
  exact h

theorem isNormal_iff_isFinite_ne_zero (x : AzFloat) :
    x.isNormal = true ↔ x.isFinite = true ∧ x ≠ zero := by
  cases x <;> simp [isNormal, isFinite]

/-- The specification, by cases: `NaN` or both infinities give `NaN`, one infinity gives
itself, and otherwise the real sum. -/
theorem Spec.sum_eq (xs : List AzFloat) :
    Spec.sum xs =
      if xs.any isNaN = true then none
      else if (xs.any fun x => x == infinity true) = true ∧
          (xs.any fun x => x == infinity false) = true then none
      else if (xs.any fun x => x == infinity true) = true then some ⊤
      else if (xs.any fun x => x == infinity false) = true then some ⊥
      else some ((realSum xs : ℝ) : EReal) := by
  induction xs with
  | nil => simp [Spec.sum]
  | cons x xs ih =>
    rw [Spec.sum, List.foldr_cons, ← Spec.sum, ih]
    simp only [List.any_cons, Bool.or_eq_true, realSum_cons]
    cases x with
    | nan => simp [isNaN]
    | infinity s =>
      cases s <;> simp only [isNaN, toVal_infinity, Option.bind_some, beq_iff_eq,
        reduceCtorEq, false_or, true_or] <;> split_ifs <;>
        simp_all [Spec.add_top_top, Spec.add_bot_bot, Spec.add_top_bot, Spec.add_bot_top,
          Spec.add_top_coe, Spec.add_bot_coe]
    | zero =>
      simp only [isNaN, toVal_zero, Option.bind_some, beq_iff_eq, reduceCtorEq, false_or]
      split_ifs <;> simp [Spec.add_zero_left, fval]
    | finite s e p m hv =>
      simp only [isNaN, toVal_finite, Option.bind_some, beq_iff_eq, reduceCtorEq, false_or]
      split_ifs <;> simp [Spec.add_coe_top, Spec.add_coe_bot, Spec.add_coe_coe, fval]

/-! ### Exact window sums -/

private theorem toInt_max' (a b : AzInt) : (max a b).toInt = max a.toInt b.toInt := by
  show (if a ≤ b then b else a).toInt = _
  split_ifs with h
  · rw [max_eq_right ((AzInt.le_iff_toInt_le a b).mp h)]
  · rw [max_eq_left (le_of_lt (not_le.mp (fun h' => h ((AzInt.le_iff_toInt_le a b).mpr h'))))]

private theorem toInt_min' (a b : AzInt) : (min a b).toInt = min a.toInt b.toInt := by
  show (if a ≤ b then a else b).toInt = _
  split_ifs with h
  · rw [min_eq_left ((AzInt.le_iff_toInt_le a b).mp h)]
  · rw [min_eq_right (le_of_lt (not_le.mp (fun h' => h ((AzInt.le_iff_toInt_le a b).mpr h'))))]

/-- A finite value is an integer multiple of `2^(e − p)` with the integer below `2^p`. -/
theorem finiteVal_eq_int_mul_prec (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat}
    (hv : FiniteValid p m) :
    ∃ k : ℤ, finiteVal s e m = (k : ℝ) * (2 : ℝ) ^ (e.toInt - p) ∧ |k| < 2 ^ p := by
  obtain ⟨c, hc⟩ := hv.dvd
  have hB := hv.size_eq
  obtain ⟨_, hhi⟩ := toNat_bounds_of_valid hv
  have hpB := le_alignedBits p
  refine ⟨if s then (c : ℤ) else -(c : ℤ), ?_, ?_⟩
  · rw [finiteVal_eq_int_mul, hB, hc]
    push_cast
    have : (2 : ℝ) ^ (e.toInt - (alignedBits p : ℕ)) * (2 : ℝ) ^ (alignedBits p - p)
        = (2 : ℝ) ^ (e.toInt - p) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      omega
    rw [← this]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  · have hc' : c < 2 ^ p := by
      have h1 : 2 ^ (alignedBits p - p) * c < 2 ^ (alignedBits p - p) * 2 ^ p := by
        rw [← pow_add, Nat.sub_add_cancel hpB, ← hc]; exact hhi
      exact Nat.lt_of_mul_lt_mul_left h1
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, abs_neg, abs_of_nonneg (Int.natCast_nonneg c)]
      exact_mod_cast hc'
    · simp only [↓reduceIte, abs_of_nonneg (Int.natCast_nonneg c)]
      exact_mod_cast hc'

theorem exactSumPrec_pos_toInt (s₁ : Bool) (e₁ : AzInt) (p₁ : ℕ) (m₁ : AzNat)
    (h₁ : FiniteValid p₁ m₁) (s₂ : Bool) (e₂ : AzInt) (p₂ : ℕ) (m₂ : AzNat)
    (h₂ : FiniteValid p₂ m₂) :
    ((exactSumPrec (finite s₁ e₁ p₁ m₁ h₁) (finite s₂ e₂ p₂ m₂ h₂) : ℕ) : ℤ)
      = (max e₁.toInt e₂.toInt + 1) - min (e₁.toInt - p₁) (e₂.toInt - p₂) ∧
    0 < exactSumPrec (finite s₁ e₁ p₁ m₁ h₁) (finite s₂ e₂ p₂ m₂ h₂) := by
  have hpos :
      0 < (max e₁.toInt e₂.toInt + 1) - min (e₁.toInt - p₁) (e₂.toInt - p₂) := by
    have := min_le_left (e₁.toInt - p₁) (e₂.toInt - p₂)
    have := le_max_left e₁.toInt e₂.toInt
    omega
  have hval :
      ((exactSumPrec (finite s₁ e₁ p₁ m₁ h₁) (finite s₂ e₂ p₂ m₂ h₂) : ℕ) : ℤ)
        = (max e₁.toInt e₂.toInt + 1) - min (e₁.toInt - p₁) (e₂.toInt - p₂) := by
    show (((max e₁ e₂ + 1)
      - min (e₁ - (AzNat.ofNat p₁).toAzInt) (e₂ - (AzNat.ofNat p₂).toAzInt)).abs.toNat : ℤ) = _
    rw [← AzInt.abs_toInt, AzInt.toInt_sub, AzInt.toInt_add, toInt_max', toInt_min',
      AzInt.toInt_sub, AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toInt_toAzInt,
      AzNat.toNat_ofNat, AzNat.toNat_ofNat, AzInt.toInt_one]
    exact abs_of_pos hpos
  exact ⟨hval, by exact_mod_cast (hval ▸ hpos)⟩

/-- Rounding a value representable at precision `p` returns it exactly. -/
theorem roundVal_of_mem (p : ℕ) [NeZero p] (mode : RoundingMode) (r : ℝ)
    (h : ((r : ℝ) : EReal) ∈ floatSet p) :
    (roundVal p mode (some (r : EReal))).1.toVal = some (r : EReal) ∧
      (roundVal p mode (some (r : EReal))).2 = .eq := by
  obtain ⟨h1, h2⟩ := roundVal_coe p mode r
  rw [RoundingTarget.val_round_of_mem _ mode h] at h1 h2
  exact ⟨h1, by rw [h2]; exact compare_eq_iff_eq.mpr rfl⟩

/-- **The exact sum of two finite floats**: `exactAdd` loses nothing. -/
theorem toVal_exactAdd {x y : AzFloat} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (exactAdd x y).toVal = some ((fval x + fval y : ℝ) : EReal) := by
  unfold exactAdd
  cases x with
  | nan => simp [isFinite] at hx
  | infinity s => simp [isFinite] at hx
  | zero =>
    cases y with
    | nan => simp [isFinite] at hy
    | infinity t => simp [isFinite] at hy
    | zero =>
      show (setPrecRound zero 1 .Floor).1.toVal = _
      simp [setPrecRound, fval]
    | finite t e q m hv =>
      show (setPrecRound (finite t e q m hv) q .Floor).1.toVal = _
      have : NeZero q := ⟨hv.pos.ne'⟩
      rw [setPrecRound_eq_liftE]
      unfold liftE liftVal
      rw [toVal_finite, Option.bind_some]
      simp only [id_eq]
      rw [roundVal_of_toVal q .Floor (finite t e q m hv) _ (Or.inl rfl) rfl]
      simp [fval]
  | finite s e₁ p₁ m₁ h₁ =>
    cases y with
    | nan => simp [isFinite] at hy
    | infinity t => simp [isFinite] at hy
    | zero =>
      show (setPrecRound (finite s e₁ p₁ m₁ h₁) p₁ .Floor).1.toVal = _
      have : NeZero p₁ := ⟨h₁.pos.ne'⟩
      rw [setPrecRound_eq_liftE]
      unfold liftE liftVal
      rw [toVal_finite, Option.bind_some]
      simp only [id_eq]
      rw [roundVal_of_toVal p₁ .Floor (finite s e₁ p₁ m₁ h₁) _ (Or.inl rfl) rfl]
      simp [fval]
    | finite t e₂ p₂ m₂ h₂ =>
      obtain ⟨hq, hqpos⟩ := exactSumPrec_pos_toInt s e₁ p₁ m₁ h₁ t e₂ p₂ m₂ h₂
      set q := exactSumPrec (finite s e₁ p₁ m₁ h₁) (finite t e₂ p₂ m₂ h₂) with hqdef
      have : NeZero q := ⟨hqpos.ne'⟩
      rw [addPrecRound_eq_liftVal₂]
      unfold liftVal₂
      rw [toVal_finite, toVal_finite, Option.bind_some, Option.bind_some, Spec.add_coe_coe]
      simp only [fval]
      apply (roundVal_of_mem q .Floor _ _).1
      -- the sum is an integer multiple of `2^bot` with the integer at most `2^q`
      obtain ⟨k₁, hk₁, hk₁b⟩ := finiteVal_eq_int_mul_prec s e₁ h₁
      obtain ⟨k₂, hk₂, hk₂b⟩ := finiteVal_eq_int_mul_prec t e₂ h₂
      set bot := min (e₁.toInt - p₁) (e₂.toInt - p₂) with hbot
      set top := max e₁.toInt e₂.toInt + 1 with htop
      have hb₁ : bot ≤ e₁.toInt - p₁ := min_le_left _ _
      have hb₂ : bot ≤ e₂.toInt - p₂ := min_le_right _ _
      set K : ℤ := k₁ * 2 ^ (e₁.toInt - p₁ - bot).toNat
        + k₂ * 2 ^ (e₂.toInt - p₂ - bot).toNat with hK
      have hsum : finiteVal s e₁ m₁ + finiteVal t e₂ m₂ = (K : ℝ) * (2 : ℝ) ^ bot := by
        rw [hk₁, hk₂, hK]
        push_cast
        have h1 : (2 : ℝ) ^ ((e₁.toInt - p₁ - bot).toNat : ℕ) * (2 : ℝ) ^ bot
            = (2 : ℝ) ^ (e₁.toInt - p₁) := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num), Int.toNat_of_nonneg (by omega)]
          congr 1; ring
        have h2 : (2 : ℝ) ^ ((e₂.toInt - p₂ - bot).toNat : ℕ) * (2 : ℝ) ^ bot
            = (2 : ℝ) ^ (e₂.toInt - p₂) := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num), Int.toNat_of_nonneg (by omega)]
          congr 1; ring
        rw [add_mul, mul_assoc, mul_assoc, h1, h2]
      rw [hsum]
      apply mem_floatSet_mul_zpow
      -- `|K| ≤ 2^q`
      have hq' : (q : ℤ) = top - bot := hq
      have hpow : ∀ (k : ℤ) (e : ℤ) (p : ℕ), |k| < 2 ^ p → bot ≤ e - p →
          |k * 2 ^ (e - p - bot).toNat| ≤ 2 ^ (e - bot).toNat := by
        intro k e p hk hle
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ (e - p - bot).toNat)]
        calc |k| * 2 ^ (e - p - bot).toNat ≤ 2 ^ p * 2 ^ (e - p - bot).toNat :=
              mul_le_mul_of_nonneg_right hk.le (by positivity)
          _ = 2 ^ (e - bot).toNat := by
              rw [← pow_add]; congr 1; omega
      have hK1 := hpow k₁ e₁.toInt p₁ hk₁b hb₁
      have hK2 := hpow k₂ e₂.toInt p₂ hk₂b hb₂
      have htb : (e₁.toInt - bot).toNat ≤ (top - bot).toNat - 1 ∧
          (e₂.toInt - bot).toNat ≤ (top - bot).toNat - 1 := by
        have := le_max_left e₁.toInt e₂.toInt
        have := le_max_right e₁.toInt e₂.toInt
        constructor <;> omega
      have hq2 : (2 : ℤ) ^ q = 2 ^ ((top - bot).toNat - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        congr 1
        omega
      calc |K|
          ≤ |k₁ * 2 ^ (e₁.toInt - p₁ - bot).toNat| + |k₂ * 2 ^ (e₂.toInt - p₂ - bot).toNat| :=
            abs_add_le _ _
        _ ≤ 2 ^ ((top - bot).toNat - 1) + 2 ^ ((top - bot).toNat - 1) := by
            have h1 : (2 : ℤ) ^ (e₁.toInt - bot).toNat ≤ 2 ^ ((top - bot).toNat - 1) :=
              pow_le_pow_right₀ (by norm_num) htb.1
            have h2 : (2 : ℤ) ^ (e₂.toInt - bot).toNat ≤ 2 ^ ((top - bot).toNat - 1) :=
              pow_le_pow_right₀ (by norm_num) htb.2
            linarith
        _ = 2 ^ q := by rw [hq2]; ring

theorem isFinite_exactAdd {x y : AzFloat} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (exactAdd x y).isFinite = true :=
  isFinite_of_toVal_coe (toVal_exactAdd hx hy)

theorem fval_exactAdd {x y : AzFloat} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    fval (exactAdd x y) = fval x + fval y :=
  fval_of_toVal_coe (toVal_exactAdd hx hy)

/-- A list of finite floats. -/
def IsFiniteList (l : List AzFloat) : Prop := ∀ x ∈ l, x.isFinite = true

theorem foldl_exactAdd_spec (l : List AzFloat) (hl : IsFiniteList l) : ∀ acc : AzFloat,
    acc.isFinite = true → (l.foldl exactAdd acc).isFinite = true ∧
      fval (l.foldl exactAdd acc) = fval acc + realSum l := by
  induction l with
  | nil => intro acc hacc; simp [hacc]
  | cons x xs ih =>
    intro acc hacc
    have hx : x.isFinite = true := hl x (List.mem_cons_self ..)
    have hxs : IsFiniteList xs := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih hxs (exactAdd acc x) (isFinite_exactAdd hacc hx)
    refine ⟨h1, ?_⟩
    rw [h2, fval_exactAdd hacc hx, realSum_cons]
    ring

/-- **The window sum is exact.** -/
theorem exactSum_spec (l : List AzFloat) (hl : IsFiniteList l) :
    (exactSum l).isFinite = true ∧ fval (exactSum l) = realSum l := by
  obtain ⟨h1, h2⟩ := foldl_exactAdd_spec l hl zero rfl
  unfold exactSum
  exact ⟨h1, by rw [h2]; simp [fval]⟩

/-! ### Lists of normal floats, windows and the tail bound -/

/-- A list of finite nonzero floats. -/
def IsNormalList (l : List AzFloat) : Prop := ∀ x ∈ l, x.isNormal = true

theorem IsNormalList.isFiniteList {l : List AzFloat} (h : IsNormalList l) : IsFiniteList l :=
  fun x hx => ((isNormal_iff_isFinite_ne_zero x).mp (h x hx)).1

theorem IsNormalList.filter {l : List AzFloat} (h : IsNormalList l) (q : AzFloat → Bool) :
    IsNormalList (l.filter q) :=
  fun x hx => h x (List.mem_of_mem_filter hx)

theorem realSum_filter (l : List AzFloat) (q : AzFloat → Bool) :
    realSum l = realSum (l.filter q) + realSum (l.filter fun x => !q x) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [realSum_cons, ih]
    by_cases h : q x = true
    · rw [List.filter_cons_of_pos h, List.filter_cons_of_neg (by simp [h]), realSum_cons]; ring
    · rw [List.filter_cons_of_neg h, List.filter_cons_of_pos (by simp [h]), realSum_cons]; ring

/-- The magnitude of a normal float against its exponent `e`: in `[2^(e−1), 2^e)`. -/
theorem abs_fval_bounds {x : AzFloat} (hx : x.isNormal = true) :
    (2 : ℝ) ^ ((expOf x).toInt - 1) ≤ |fval x| ∧ |fval x| < (2 : ℝ) ^ (expOf x).toInt := by
  cases x with
  | finite s e p m hv =>
    simp only [fval, expOf, exponent?, Option.getD_some]
    exact abs_finiteVal_bounds s e hv
  | _ => simp [isNormal] at hx

theorem le_foldMax (a : AzInt) :
    ∀ xs : List AzFloat, a ≤ xs.foldl (fun b y => max b (expOf y)) a
  | [] => le_rfl
  | x :: xs => by
    rw [List.foldl_cons]
    exact (le_max_left _ _).trans (le_foldMax _ xs)

theorem expOf_le_foldMax (a : AzInt) : ∀ (xs : List AzFloat), ∀ y ∈ xs,
    expOf y ≤ xs.foldl (fun b y => max b (expOf y)) a
  | [], _, hy => by simp at hy
  | x :: xs, y, hy => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (le_max_right _ _).trans (le_foldMax _ xs)
    · exact expOf_le_foldMax _ xs y hy

theorem foldMax_mem (a : AzInt) : ∀ xs : List AzFloat,
    xs.foldl (fun b y => max b (expOf y)) a = a ∨
      ∃ y ∈ xs, xs.foldl (fun b y => max b (expOf y)) a = expOf y
  | [] => Or.inl rfl
  | x :: xs => by
    rw [List.foldl_cons]
    rcases foldMax_mem (max a (expOf x)) xs with h | ⟨y, hy, h⟩
    · rcases max_choice a (expOf x) with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨x, List.mem_cons_self .., h.trans h'⟩
    · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h⟩

theorem expOf_le_maxExponent {l : List AzFloat} : ∀ y ∈ l, expOf y ≤ maxExponent l := by
  intro y hy
  cases l with
  | nil => simp at hy
  | cons x xs =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_foldMax _ xs
    · exact expOf_le_foldMax _ xs y hy

theorem exists_expOf_eq_maxExponent {l : List AzFloat} (hne : l ≠ []) :
    ∃ y ∈ l, expOf y = maxExponent l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x xs =>
    rcases foldMax_mem (expOf x) xs with h | ⟨y, hy, h⟩
    · exact ⟨x, List.mem_cons_self .., h.symm⟩
    · exact ⟨y, List.mem_cons_of_mem _ hy, h.symm⟩

theorem lengthBits_eq (l : List AzFloat) : lengthBits l = l.length.size := by
  unfold lengthBits
  rw [← AzNat.size_toNat, AzNat.toNat_ofNat]

/-- `|Σ| < n · 2^E` when every term has exponent at most `E` (`n ≥ 1`). -/
theorem abs_realSum_le (E : ℤ) : ∀ (l : List AzFloat), IsNormalList l →
    (∀ x ∈ l, (expOf x).toInt ≤ E) → |realSum l| ≤ l.length * (2 : ℝ) ^ E
  | [], _, _ => by simp
  | x :: xs, hl, hE => by
    have hx := hl x (List.mem_cons_self ..)
    have hxs : IsNormalList xs := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hExs : ∀ y ∈ xs, (expOf y).toInt ≤ E := fun y hy => hE y (List.mem_cons_of_mem _ hy)
    have h1 := abs_realSum_le E xs hxs hExs
    have h2 : |fval x| < (2 : ℝ) ^ E :=
      lt_of_lt_of_le (abs_fval_bounds hx).2
        (zpow_le_zpow_right₀ (by norm_num) (hE x (List.mem_cons_self ..)))
    rw [realSum_cons, List.length_cons]
    push_cast
    calc |fval x + realSum xs| ≤ |fval x| + |realSum xs| := abs_add_le _ _
      _ ≤ (2 : ℝ) ^ E + xs.length * 2 ^ E := by linarith
      _ = (xs.length + 1) * 2 ^ E := by ring

theorem abs_realSum_lt (E : ℤ) (l : List AzFloat) (hl : IsNormalList l) (hne : l ≠ [])
    (hE : ∀ x ∈ l, (expOf x).toInt ≤ E) : |realSum l| < l.length * (2 : ℝ) ^ E := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x xs =>
    have hx := hl x (List.mem_cons_self ..)
    have hxs : IsNormalList xs := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hExs : ∀ y ∈ xs, (expOf y).toInt ≤ E := fun y hy => hE y (List.mem_cons_of_mem _ hy)
    have h1 := abs_realSum_le E xs hxs hExs
    have h2 : |fval x| < (2 : ℝ) ^ E :=
      lt_of_lt_of_le (abs_fval_bounds hx).2
        (zpow_le_zpow_right₀ (by norm_num) (hE x (List.mem_cons_self ..)))
    rw [realSum_cons, List.length_cons]
    push_cast
    calc |fval x + realSum xs| ≤ |fval x| + |realSum xs| := abs_add_le _ _
      _ < (2 : ℝ) ^ E + xs.length * 2 ^ E := by linarith
      _ = (xs.length + 1) * 2 ^ E := by ring

theorem toVal_powerOf2 (e : AzInt) :
    toVal (powerOf2 e) = some (((2 : ℝ) ^ e.toInt : ℝ) : EReal) := by
  unfold powerOf2
  rw [toVal_mkFinite _ _ _ _ one_ne_zero]
  congr 2
  unfold finiteVal
  rw [AzNat.toNat_one, show (1 : AzNat).size = 1 by rw [← AzNat.size_toNat, AzNat.toNat_one]; rfl,
    AzInt.toInt_add, AzInt.toInt_one]
  simp only [↓reduceIte, Nat.cast_one, one_mul]
  congr 1
  ring

/-- The tail bound: `tailBound rest` is `2^(e_R + k)` and exceeds `|Σ rest|`. -/
theorem tailBound_spec (rest : List AzFloat) (hrest : IsNormalList rest) (hne : rest ≠ []) :
    (tailBound rest).toVal
      = some (((2 : ℝ) ^ ((maxExponent rest).toInt + lengthBits rest) : ℝ) : EReal) ∧
    (tailBound rest).isNormal = true ∧
    |realSum rest| < (2 : ℝ) ^ ((maxExponent rest).toInt + lengthBits rest) := by
  have hval : (tailBound rest).toVal
      = some (((2 : ℝ) ^ ((maxExponent rest).toInt + lengthBits rest) : ℝ) : EReal) := by
    unfold tailBound
    rw [toVal_powerOf2, AzInt.toInt_add, AzNat.toInt_toAzInt, AzNat.toNat_ofNat]
  refine ⟨hval, ?_, ?_⟩
  · unfold tailBound powerOf2 mkFinite
    rw [dite_eq_right one_ne_zero]; rfl
  · have h1 := abs_realSum_lt (maxExponent rest).toInt rest hrest hne
      (fun x hx => (AzInt.le_iff_toInt_le _ _).mp (expOf_le_maxExponent x hx))
    have h2 : (rest.length : ℝ) ≤ (2 : ℝ) ^ (lengthBits rest : ℕ) := by
      rw [lengthBits_eq]
      exact_mod_cast (Nat.lt_size_self rest.length).le
    calc |realSum rest| < rest.length * (2 : ℝ) ^ (maxExponent rest).toInt := h1
      _ ≤ (2 : ℝ) ^ (lengthBits rest : ℕ) * (2 : ℝ) ^ (maxExponent rest).toInt :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (2 : ℝ) ^ ((maxExponent rest).toInt + lengthBits rest) := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num), add_comm]

/-- The facts about a window split. -/
theorem splitWindow_spec (l : List AzFloat) (W : ℕ) (hl : IsNormalList l) (hne : l ≠ []) :
    IsNormalList (splitWindow l W).1 ∧ IsNormalList (splitWindow l W).2 ∧
    realSum l = realSum (splitWindow l W).1 + realSum (splitWindow l W).2 ∧
    l.length = (splitWindow l W).1.length + (splitWindow l W).2.length ∧
    (splitWindow l W).1 ≠ [] ∧
    (∀ x ∈ (splitWindow l W).2, (expOf x).toInt + W < (maxExponent l).toInt) ∧
    ((splitWindow l W).1.length = 1 →
      ∃ y, (splitWindow l W).1 = [y] ∧ (expOf y).toInt = (maxExponent l).toInt) := by
  unfold splitWindow
  simp only [List.partition_eq_filter_filter]
  set q : AzFloat → Bool := fun x => decide (maxExponent l - expOf x ≤ (AzNat.ofNat W).toAzInt)
    with hq
  have hnot : (not ∘ q) = fun x => !q x := rfl
  rw [hnot]
  obtain ⟨y₀, hy₀, hy₀e⟩ := exists_expOf_eq_maxExponent hne
  have hy₀q : q y₀ = true := by
    rw [hq]; simp only [decide_eq_true_eq]
    rw [hy₀e]
    exact (AzInt.le_iff_toInt_le _ _).mpr
      (by rw [AzInt.toInt_sub, sub_self, AzNat.toInt_toAzInt]; exact Int.natCast_nonneg _)
  have hy₀mem : y₀ ∈ l.filter q := List.mem_filter.mpr ⟨hy₀, hy₀q⟩
  refine ⟨hl.filter q, hl.filter _, realSum_filter l q, List.length_eq_length_filter_add q,
    List.ne_nil_of_mem hy₀mem, ?_, ?_⟩
  · intro x hx
    have := (List.mem_filter.mp hx).2
    rw [hq] at this
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
    have := not_le.mp this
    rw [AzInt.lt_iff_toInt_lt, AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toNat_ofNat] at this
    linarith
  · intro hlen
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
    refine ⟨a, ha, ?_⟩
    have hya : y₀ = a := List.mem_singleton.mp (ha ▸ hy₀mem)
    rw [← hya, hy₀e]

theorem toVal_abs_of_isFinite {x : AzFloat} (hx : x.isFinite = true) :
    x.abs.toVal = some ((|fval x| : ℝ) : EReal) := by
  rw [toVal_abs, toVal_of_isFinite hx, Option.map_some]
  congr 2

theorem absLt_iff {x y : AzFloat} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    absLt x y = true ↔ |fval x| < fval y := by
  unfold absLt
  rw [partialCompare_eq, toVal_abs_of_isFinite hx, toVal_of_isFinite hy]
  simp only [compare_coe_coe, beq_iff_eq, Option.some.injEq]
  exact compare_lt_iff_lt

theorem absGt_iff {x y : AzFloat} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    absGt x y = true ↔ fval y < |fval x| := by
  unfold absGt
  rw [partialCompare_eq, toVal_abs_of_isFinite hx, toVal_of_isFinite hy]
  simp only [compare_coe_coe, beq_iff_eq, Option.some.injEq]
  exact compare_gt_iff_gt

theorem signOf_eq {x : AzFloat} (hx : x.isFinite = true) : signOf x = compare (fval x) 0 := by
  unfold signOf
  rw [partialCompare_eq, toVal_of_isFinite hx, toVal_zero]
  simp only [Option.getD_some]
  rw [← EReal.coe_zero, compare_coe_coe]

theorem compare_add_of_abs_lt (a b : ℝ) (h : |b| < |a|) : compare (a + b) 0 = compare a 0 := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [abs_of_neg ha, abs_lt] at h
    rw [compare_lt_iff_lt.mpr ha, compare_lt_iff_lt.mpr (by linarith)]
  · subst ha; simp at h; exact absurd h (not_lt.mpr (abs_nonneg b))
  · rw [abs_of_pos ha, abs_lt] at h
    rw [compare_gt_iff_gt.mpr ha, compare_gt_iff_gt.mpr (by linarith)]

/-- The exact sum of a nonzero finite float is normal, so it may rejoin a list. -/
theorem isNormal_of_isFinite_ne_zero {x : AzFloat} (hx : x.isFinite = true) (h0 : x ≠ zero) :
    x.isNormal = true :=
  (isNormal_iff_isFinite_ne_zero x).mpr ⟨hx, h0⟩

theorem fval_zero : fval zero = 0 := rfl

/-! ### The sign of a sum -/

/-- **`signSum` is exact** once the fuel exceeds the length. -/
theorem signSum_eq : ∀ (fuel : ℕ) (l : List AzFloat), IsNormalList l → l.length < fuel →
    signSum fuel l = compare (realSum l) 0 := by
  intro fuel
  induction fuel with
  | zero => intro l _ h; omega
  | succ fuel ih =>
    intro l hl hlen
    cases l with
    | nil => simp [signSum]
    | cons x xs =>
      have hne : x :: xs ≠ [] := List.cons_ne_nil x xs
      obtain ⟨hwinN, hrestN, hsum, hlenW, hwinne, hrestexp, hsingle⟩ :=
        splitWindow_spec (x :: xs) (lengthBits (x :: xs) + 2) hl hne
      have hsplit : splitWindow (x :: xs) (lengthBits (x :: xs) + 2)
          = ((splitWindow (x :: xs) (lengthBits (x :: xs) + 2)).1,
             (splitWindow (x :: xs) (lengthBits (x :: xs) + 2)).2) := Prod.ext rfl rfl
      obtain ⟨hs₁fin, hs₁val⟩ := exactSum_spec _ hwinN.isFiniteList
      rw [signSum.eq_def]
      dsimp only
      rw [hsplit]
      dsimp only
      set W := lengthBits (x :: xs) + 2 with hW
      set win := (splitWindow (x :: xs) W).1 with hwin
      set rest := (splitWindow (x :: xs) W).2 with hrest
      set s₁ := exactSum win with hs₁
      clear_value win rest s₁
      rw [hsum, ← hs₁val]
      cases rest with
      | nil =>
        dsimp only
        rw [realSum_nil, add_zero]
        exact signOf_eq hs₁fin
      | cons r rs =>
        dsimp only
        have hrne : r :: rs ≠ [] := List.cons_ne_nil r rs
        obtain ⟨hTval, hTnorm, hTbound⟩ := tailBound_spec (r :: rs) hrestN hrne
        have hTfin : (tailBound (r :: rs)).isFinite = true :=
          ((isNormal_iff_isFinite_ne_zero _).mp hTnorm).1
        have hTf : fval (tailBound (r :: rs))
            = (2 : ℝ) ^ ((maxExponent (r :: rs)).toInt + lengthBits (r :: rs)) :=
          fval_of_toVal_coe hTval
        by_cases hgt : absGt s₁ (tailBound (r :: rs)) = true
        · rw [ite_eq_left hgt, signOf_eq hs₁fin]
          rw [absGt_iff hs₁fin hTfin, hTf] at hgt
          exact (compare_add_of_abs_lt _ _ (hTbound.trans hgt)).symm
        · rw [ite_eq_right hgt]
          rw [absGt_iff hs₁fin hTfin, hTf] at hgt
          have hnotle :
              |fval s₁| ≤ (2 : ℝ) ^ ((maxExponent (r :: rs)).toInt + lengthBits (r :: rs)) :=
            not_lt.mp hgt
          -- the window has at least two terms
          have hwin2 : 2 ≤ win.length := by
            by_contra hlt
            have h1 : win.length = 1 := by
              have := List.length_pos_of_ne_nil hwinne; omega
            obtain ⟨y, hy, hye⟩ := hsingle h1
            have hyN : y.isNormal = true := hwinN y (by rw [hy]; exact List.mem_singleton_self y)
            have hs₁y : fval s₁ = fval y := by
              rw [hs₁val, hy, realSum_cons, realSum_nil, add_zero]
            have hlow := (abs_fval_bounds hyN).1
            rw [hye] at hlow
            obtain ⟨r₀, hr₀, hr₀e⟩ := exists_expOf_eq_maxExponent hrne
            have hr₀ := hrestexp r₀ hr₀
            rw [hr₀e] at hr₀
            have hk : lengthBits (r :: rs) ≤ lengthBits (x :: xs) := by
              rw [lengthBits_eq, lengthBits_eq]
              exact Nat.size_le_size (by rw [hlenW]; omega)
            have hT : (2 : ℝ) ^ ((maxExponent (r :: rs)).toInt + lengthBits (r :: rs))
                ≤ (2 : ℝ) ^ ((maxExponent (x :: xs)).toInt - 3) :=
              zpow_le_zpow_right₀ (by norm_num)
                (by rw [hW] at hr₀; push_cast at hr₀ ⊢; omega)
            have : (2 : ℝ) ^ ((maxExponent (x :: xs)).toInt - 3)
                < (2 : ℝ) ^ ((maxExponent (x :: xs)).toInt - 1) :=
              zpow_lt_zpow_right₀ (by norm_num) (by omega)
            rw [hs₁y] at hnotle
            linarith
          -- recurse on the shorter list
          have hlen' : (if s₁ = zero then r :: rs else s₁ :: r :: rs).length < fuel := by
            split_ifs <;> simp only [List.length_cons] at hlenW hlen ⊢ <;> omega
          have hN' : IsNormalList (if s₁ = zero then r :: rs else s₁ :: r :: rs) := by
            split_ifs with h0
            · exact hrestN
            · intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact isNormal_of_isFinite_ne_zero hs₁fin h0
              · exact hrestN y hy
          rw [ih _ hN' hlen']
          split_ifs with h0
          · rw [h0, fval_zero, zero_add]
          · rw [realSum_cons]

/-! ### The main branch: brackets and the unique boundary -/

/-- Two `(p+1)`-bit floats of magnitude at least `2^(E−2)` coincide or differ by at least
`2^(E−2−p)`. -/
theorem boundary_dist (p : ℕ) [NeZero p] (E : ℤ) (b c : ℝ)
    (hb : ((b : ℝ) : EReal) ∈ floatSet (p + 1)) (hc : ((c : ℝ) : EReal) ∈ floatSet (p + 1))
    (hbE : (2 : ℝ) ^ (E - 2) ≤ |b|) (hcE : (2 : ℝ) ^ (E - 2) ≤ |c|) (hne : b ≠ c) :
    (2 : ℝ) ^ (E - 2 - p) ≤ |b - c| := by
  have : NeZero (p + 1) := ⟨Nat.succ_ne_zero p⟩
  have hb0 : b ≠ 0 := by
    intro h; rw [h, abs_zero] at hbE; exact absurd hbE (not_le.mpr (zpow_pos (by norm_num) _))
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hcE; exact absurd hcE (not_le.mpr (zpow_pos (by norm_num) _))
  obtain ⟨Mb, kb, hMb, hkb⟩ := boundary_repr p b hb hb0
  obtain ⟨Mc, kc, hMc, hkc⟩ := boundary_repr p c hc hc0
  have hlogb : E - 2 ≤ Int.log 2 |b| :=
    (Int.zpow_le_iff_le_log (by norm_num) (abs_pos.mpr hb0)).mp (by exact_mod_cast hbE)
  have hlogc : E - 2 ≤ Int.log 2 |c| :=
    (Int.zpow_le_iff_le_log (by norm_num) (abs_pos.mpr hc0)).mp (by exact_mod_cast hcE)
  set K := E - 2 - p with hK
  have hkbK : K ≤ kb := by omega
  have hkcK : K ≤ kc := by omega
  have hrepr :
      b - c = ((Mb * 2 ^ (kb - K).toNat - Mc * 2 ^ (kc - K).toNat : ℤ) : ℝ) * 2 ^ K := by
    rw [hMb, hMc]
    push_cast
    rw [sub_mul, mul_assoc, mul_assoc, ← zpow_natCast, ← zpow_natCast,
      ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num), Int.toNat_of_nonneg (by omega),
      Int.toNat_of_nonneg (by omega), sub_add_cancel, sub_add_cancel]
  set N : ℤ := Mb * 2 ^ (kb - K).toNat - Mc * 2 ^ (kc - K).toNat with hN
  have hN0 : N ≠ 0 := by
    intro h
    apply hne
    have := hrepr
    rw [h] at this
    push_cast at this
    linarith
  rw [hrepr, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) K)]
  have h1 : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hN0
  have h2 : (0 : ℝ) < 2 ^ K := zpow_pos (by norm_num) K
  nlinarith

/-- The truncation at `w` bits of a value below `2^(E+1)` in magnitude is within `2^(E+3−w)`. -/
theorem floor_err_le (w : ℕ) [NeZero w] (hw : 2 ≤ w) (x : ℝ) (E : ℤ)
    (hx : |x| ≤ (2 : ℝ) ^ (E + 1)) :
    ∃ yv : ℝ, (roundVal w .Floor (some (x : EReal))).1.toVal = some (yv : EReal) ∧
      yv ≤ x ∧ x ≤ yv + (2 : ℝ) ^ (E + 3 - w) := by
  obtain ⟨yv, εv, hy, _, hle, hxle, _, hε0, hε, _⟩ := truncError_spec w x
  refine ⟨yv, hy, hle, ?_⟩
  have hδ : (0 : ℝ) < (2 : ℝ) ^ (E + 3 - w) := zpow_pos (by norm_num) _
  by_cases hεz : εv = 0
  · linarith
  obtain ⟨e, he, hlow, _⟩ := hε hεz
  have habs : |yv| ≤ |x| + εv := by
    rw [abs_le]
    constructor <;> cases abs_le.mp (le_refl |x|) <;> linarith [neg_abs_le x, le_abs_self x]
  have hew : (2 : ℝ) ^ (e - w) ≤ (2 : ℝ) ^ (e - 2) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (e - 1) = 2 * (2 : ℝ) ^ (e - 2) := by
    rw [show e - 1 = (e - 2) + 1 by ring, zpow_add_one₀ (by norm_num)]; ring
  have hle' : (2 : ℝ) ^ (e - 2) ≤ (2 : ℝ) ^ (E + 1) := by
    rw [he] at habs
    linarith
  have heE : e - 2 ≤ E + 1 := (zpow_le_zpow_iff_right₀ (by norm_num)).mp hle'
  have : εv ≤ (2 : ℝ) ^ (E + 3 - w) := by
    rw [he]; exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  linarith

theorem toVal_neg_of_isFinite {x : AzFloat} (hx : x.isFinite = true) :
    (-x).toVal = some ((-fval x : ℝ) : EReal) := by
  rw [toVal_neg, toVal_of_isFinite hx, Option.map_some, EReal.coe_neg]

theorem isFinite_neg {x : AzFloat} (hx : x.isFinite = true) : (-x).isFinite = true :=
  isFinite_of_toVal_coe (toVal_neg_of_isFinite hx)

theorem toVal_shiftLeft_nat {x : AzFloat} (hx : x.isFinite = true) (k : ℕ) :
    (x <<< k).toVal = some ((fval x * (2 : ℝ) ^ (k : ℤ) : ℝ) : EReal) := by
  show (shiftLeft x (AzNat.ofNat k).toAzInt).toVal = _
  rw [toVal_shiftLeft, toVal_of_isFinite hx, Option.map_some, AzNat.toInt_toAzInt,
    AzNat.toNat_ofNat]
  rfl

theorem toVal_shiftRight_one {x : AzFloat} (hx : x.isFinite = true) :
    (x >>> (1 : ℕ)).toVal = some ((fval x / 2 : ℝ) : EReal) := by
  show (shiftRight x (AzNat.ofNat 1).toAzInt).toVal = _
  rw [toVal_shiftRight, toVal_of_isFinite hx, Option.map_some, AzNat.toInt_toAzInt,
    AzNat.toNat_ofNat]
  rw [← EReal.coe_mul]
  congr 2
  ring

theorem fval_neg {x : AzFloat} (hx : x.isFinite = true) : fval (-x) = -fval x :=
  fval_of_toVal_coe (toVal_neg_of_isFinite hx)

theorem toVal_exactSub {x y : AzFloat} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (exactSub x y).toVal = some ((fval x - fval y : ℝ) : EReal) := by
  unfold exactSub
  rw [toVal_exactAdd hx (isFinite_neg hy), fval_neg hy, sub_eq_add_neg]

/-- Changing the precision of a float of value `xv` rounds `xv`. -/
theorem setPrecRound_eq_roundVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (q : ℕ) [NeZero q] (m : RoundingMode) :
    setPrecRound x q m = roundVal q m (some (xv : EReal)) := by
  rw [setPrecRound_eq_liftE]
  unfold liftE liftVal
  rw [hx, Option.bind_some]
  simp only [id_eq]

/-- `setPrecRound x q m` is the rounding procedure of the value of a finite `x`. -/
theorem rounds_setPrecRound {x : AzFloat} (hx : x.isFinite = true) :
    Rounds (fun q m => setPrecRound x q m) (fval x) := fun q _ m =>
  setPrecRound_eq_roundVal (toVal_of_isFinite hx) q m

/-- The `(p+1)`-bit truncation of a float of value `xv`: the greatest `(p+1)`-bit float not
exceeding `xv`. -/
theorem setPrecRound_floor_spec (p : ℕ) [NeZero p] {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) :
    ∃ bv : ℝ, (setPrecRound x (p + 1) .Floor).1.toVal = some (bv : EReal) ∧
      ((bv : ℝ) : EReal) ∈ floatSet (p + 1) ∧ bv ≤ xv ∧
      ∀ c : ℝ, ((c : ℝ) : EReal) ∈ floatSet (p + 1) → c ≤ xv → c ≤ bv := by
  have : NeZero (p + 1) := ⟨Nat.succ_ne_zero p⟩
  rw [setPrecRound_eq_roundVal hx]
  obtain ⟨bv, hbv⟩ :
      ∃ r : ℝ, ((r : ℝ) : EReal) = (roundFloor (floatSet (p + 1)) xv).val := by
    rw [val_roundFloor_floatSet]; exact precisionSet_exists_real _
  refine ⟨bv, ?_, hbv ▸ (roundFloor _ _).property, ?_, ?_⟩
  · rw [(roundVal_coe (p + 1) .Floor xv).1]
    exact congrArg some hbv.symm
  · have := (isGreatest_roundFloor (floatSet (p + 1)) xv).1.2
    rw [← hbv] at this
    exact EReal.coe_le_coe_iff.mp this
  · intro c hc hcx
    have := (isGreatest_roundFloor (floatSet (p + 1)) xv).2 ⟨hc, EReal.coe_le_coe_iff.mpr hcx⟩
    rw [← hbv] at this
    exact EReal.coe_le_coe_iff.mp this

/-- Two reals in an open interval free of `(p+1)`-bit floats round alike. -/
theorem roundVal_congr_of_no_boundary_Ioo (p : ℕ) [NeZero p] (mode : RoundingMode)
    (a b lo hi : ℝ) (ha : lo < a) (ha' : a < hi) (hb : lo < b) (hb' : b < hi)
    (h : ∀ c : ℝ, ((c : ℝ) : EReal) ∈ floatSet (p + 1) → ¬ (lo < c ∧ c < hi)) :
    roundVal p mode (some (a : EReal)) = roundVal p mode (some (b : EReal)) := by
  rcases le_total a b with hab | hab
  · exact roundVal_congr_of_no_boundary p mode a b hab
      (fun c hc ⟨h1, h2⟩ => h c hc ⟨by linarith, by linarith⟩)
  · exact (roundVal_congr_of_no_boundary p mode b a hab
      (fun c hc ⟨h1, h2⟩ => h c hc ⟨by linarith, by linarith⟩)).symm

theorem toVal_addPrecRound_floor {x y : AzFloat} {xv yv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hy : y.toVal = some (yv : EReal)) (w : ℕ) [NeZero w] :
    (addPrecRound x y w .Floor).1 = (roundVal w .Floor (some ((xv + yv : ℝ) : EReal))).1 := by
  rw [addPrecRound_eq_liftVal₂]
  unfold liftVal₂
  rw [hx, hy, Option.bind_some, Option.bind_some, Spec.add_coe_coe]

/-- **`sumFinite` is the correct rounding** once the fuel exceeds the length. -/
theorem sumFinite_eq (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ∀ (fuel : ℕ) (l : List AzFloat), IsNormalList l → l.length < fuel →
      sumFinite p mode fuel l = roundVal p mode (some ((realSum l : ℝ) : EReal)) := by
  have hp : 1 ≤ p := Nat.pos_of_ne_zero (NeZero.ne p)
  intro fuel
  induction fuel with
  | zero => intro l _ h; omega
  | succ fuel ih =>
    intro l hl hlen
    cases l with
    | nil =>
      show (zero, Ordering.eq) = _
      rw [realSum_nil, EReal.coe_zero]
      exact (roundVal_of_toVal p mode zero 0 (Or.inr rfl) rfl).symm
    | cons x xs =>
      have hne : x :: xs ≠ [] := List.cons_ne_nil x xs
      set W := p + lengthBits (x :: xs) + 3 + zivGuardBits with hW
      obtain ⟨hwinN, hrestN, hsum, hlenW, hwinne, hrestexp, hsingle⟩ :=
        splitWindow_spec (x :: xs) W hl hne
      have hsplit : splitWindow (x :: xs) W
          = ((splitWindow (x :: xs) W).1, (splitWindow (x :: xs) W).2) := Prod.ext rfl rfl
      obtain ⟨hs₁fin, hs₁val⟩ := exactSum_spec _ hwinN.isFiniteList
      rw [sumFinite.eq_def]
      dsimp only
      rw [hsplit]
      dsimp only
      set win := (splitWindow (x :: xs) W).1 with hwin
      set rest := (splitWindow (x :: xs) W).2 with hrest
      set s₁ := exactSum win with hs₁
      clear_value win rest s₁
      rw [hsum, ← hs₁val]
      cases rest with
      | nil =>
        dsimp only
        rw [realSum_nil, add_zero, setPrecRound_eq_liftE]
        unfold liftE liftVal
        rw [toVal_of_isFinite hs₁fin, Option.bind_some]
        simp only [id_eq]
      | cons r rs =>
        dsimp only
        have hrne : r :: rs ≠ [] := List.cons_ne_nil r rs
        obtain ⟨hTval, hTnorm, hTbound⟩ := tailBound_spec (r :: rs) hrestN hrne
        have hTfin : (tailBound (r :: rs)).isFinite = true :=
          ((isNormal_iff_isFinite_ne_zero _).mp hTnorm).1
        set Tv : ℝ := (2 : ℝ) ^ ((maxExponent (r :: rs)).toInt + lengthBits (r :: rs)) with hTv
        have hTf : fval (tailBound (r :: rs)) = Tv := fval_of_toVal_coe hTval
        have hTpos : 0 < Tv := zpow_pos (by norm_num) _
        set Rv := realSum (r :: rs) with hRv
        -- the shifted bound
        have hTsfin : (tailBound (r :: rs) <<< (p + 4)).isFinite = true :=
          isFinite_of_toVal_coe (toVal_shiftLeft_nat hTfin (p + 4))
        have hTsf :
            fval (tailBound (r :: rs) <<< (p + 4)) = Tv * (2 : ℝ) ^ ((p + 4 : ℕ) : ℤ) := by
          rw [fval_of_toVal_coe (toVal_shiftLeft_nat hTfin (p + 4)), hTf]
        by_cases hlt : absLt s₁ (tailBound (r :: rs) <<< (p + 4)) = true
        · -- cancellation: restart on the shorter list
          rw [ite_eq_left hlt]
          rw [absLt_iff hs₁fin hTsfin, hTsf] at hlt
          have hwin2 : 2 ≤ win.length := by
            by_contra hlt2
            have h1 : win.length = 1 := by
              have := List.length_pos_of_ne_nil hwinne; omega
            obtain ⟨y, hy, hye⟩ := hsingle h1
            have hyN : y.isNormal = true := hwinN y (by rw [hy]; exact List.mem_singleton_self y)
            have hs₁y : fval s₁ = fval y := by
              rw [hs₁val, hy, realSum_cons, realSum_nil, add_zero]
            have hlow := (abs_fval_bounds hyN).1
            rw [hye] at hlow
            obtain ⟨r₀, hr₀, hr₀e⟩ := exists_expOf_eq_maxExponent hrne
            have hr₀ := hrestexp r₀ hr₀
            rw [hr₀e] at hr₀
            have hk : lengthBits (r :: rs) ≤ lengthBits (x :: xs) := by
              rw [lengthBits_eq, lengthBits_eq]
              exact Nat.size_le_size (by rw [hlenW]; omega)
            have hT : Tv * (2 : ℝ) ^ ((p + 4 : ℕ) : ℤ)
                ≤ (2 : ℝ) ^ ((maxExponent (x :: xs)).toInt - 64) := by
              rw [hTv, ← zpow_add₀ (by norm_num)]
              apply zpow_le_zpow_right₀ (by norm_num)
              rw [hW] at hr₀
              simp only [zivGuardBits] at hr₀
              push_cast at hr₀ ⊢
              omega
            have : (2 : ℝ) ^ ((maxExponent (x :: xs)).toInt - 64)
                < (2 : ℝ) ^ ((maxExponent (x :: xs)).toInt - 1) :=
              zpow_lt_zpow_right₀ (by norm_num) (by omega)
            rw [hs₁y] at hlt
            linarith
          have hlen' : (if s₁ = zero then r :: rs else s₁ :: r :: rs).length < fuel := by
            split_ifs <;> simp only [List.length_cons] at hlenW hlen ⊢ <;> omega
          have hN' : IsNormalList (if s₁ = zero then r :: rs else s₁ :: r :: rs) := by
            split_ifs with h0
            · exact hrestN
            · intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact isNormal_of_isFinite_ne_zero hs₁fin h0
              · exact hrestN y hy
          rw [ih _ hN' hlen']
          split_ifs with h0
          · rw [h0, fval_zero, zero_add]
          · rw [realSum_cons]
        · -- the main branch
          rw [ite_eq_right hlt]
          rw [absLt_iff hs₁fin hTsfin, hTsf] at hlt
          have hge : Tv * (2 : ℝ) ^ ((p + 4 : ℕ) : ℤ) ≤ |fval s₁| := not_lt.mp hlt
          have hs₁ne : s₁ ≠ zero := by
            intro h0
            rw [h0, fval_zero, abs_zero] at hge
            have : 0 < Tv * (2 : ℝ) ^ ((p + 4 : ℕ) : ℤ) := by positivity
            linarith
          have hs₁N : s₁.isNormal = true := isNormal_of_isFinite_ne_zero hs₁fin hs₁ne
          have hs₁tv : s₁.toVal = some ((fval s₁ : ℝ) : EReal) := toVal_of_isFinite hs₁fin
          have hs₁negtv : (-s₁).toVal = some ((-fval s₁ : ℝ) : EReal) :=
            toVal_neg_of_isFinite hs₁fin
          have hTnegtv : (-(tailBound (r :: rs))).toVal = some ((-Tv : ℝ) : EReal) := by
            rw [toVal_neg_of_isFinite hTfin, hTf]
          set s₁v := fval s₁ with hs₁v
          set E := (expOf s₁).toInt with hE
          obtain ⟨hElow, hEhigh⟩ := abs_fval_bounds hs₁N
          rw [← hs₁v, ← hE] at hElow hEhigh
          -- the scales
          set B : ℝ := (2 : ℝ) ^ (E - p - 4) with hB
          have hBpos : 0 < B := zpow_pos (by norm_num) _
          have hTB : Tv < B := by
            have h2 : (2 : ℝ) ^ ((p + 4 : ℕ) : ℤ) * B = (2 : ℝ) ^ E := by
              rw [hB, ← zpow_add₀ (by norm_num)]; congr 1; push_cast; ring
            have h3 : Tv * (2 : ℝ) ^ ((p + 4 : ℕ) : ℤ) < 2 ^ E := lt_of_le_of_lt hge hEhigh
            rw [← h2] at h3
            have hpow : (0 : ℝ) < (2 : ℝ) ^ ((p + 4 : ℕ) : ℤ) := by positivity
            nlinarith
          have hB5 : B ≤ (2 : ℝ) ^ (E - 5) := zpow_le_zpow_right₀ (by norm_num) (by omega)
          have hE2 : (2 : ℝ) ^ (E - 2) = 8 * (2 : ℝ) ^ (E - 5) := by
            rw [show E - 2 = (E - 5) + 3 by ring, zpow_add₀ (by norm_num)]; norm_num; ring
          have hE1 : (2 : ℝ) ^ (E - 1) = 16 * (2 : ℝ) ^ (E - 5) := by
            rw [show E - 1 = (E - 5) + 4 by ring, zpow_add₀ (by norm_num)]; norm_num; ring
          have h4B : (2 : ℝ) ^ (E - 2 - p) = 4 * B := by
            rw [hB, show E - 2 - p = (E - p - 4) + 2 by ring, zpow_add₀ (by norm_num)]
            norm_num; ring
          have hw2 : 2 ≤ W := by rw [hW, zivGuardBits]; omega
          have : NeZero W := ⟨by omega⟩
          set δ : ℝ := (2 : ℝ) ^ (E + 3 - W) with hδ
          have hδpos : 0 < δ := zpow_pos (by norm_num) _
          have hδB : 4 * δ ≤ B := by
            have : (2 : ℝ) ^ (E + 3 - W) * 4 ≤ (2 : ℝ) ^ (E - p - 4) := by
              rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℤ) by norm_num, ← zpow_add₀ (by norm_num)]
              apply zpow_le_zpow_right₀ (by norm_num)
              rw [hW, zivGuardBits]; push_cast; omega
            linarith
          -- the bracket ends
          have hxbound : ∀ t : ℝ, |t| ≤ Tv → |s₁v + t| ≤ (2 : ℝ) ^ (E + 1) := by
            intro t ht
            have : (2 : ℝ) ^ (E + 1) = 2 * 2 ^ E := by rw [zpow_add_one₀ (by norm_num)]; ring
            calc |s₁v + t| ≤ |s₁v| + |t| := abs_add_le _ _
              _ ≤ 2 ^ E + Tv := by linarith
              _ ≤ 2 * 2 ^ E := by linarith [hTB, hB5, hE2, hE1]
              _ = _ := this.symm
          obtain ⟨lov, hlo, hlo1, hlo2⟩ := floor_err_le W hw2 (s₁v + -Tv) E
            (hxbound (-Tv) (by rw [abs_neg, abs_of_pos hTpos]))
          rw [← toVal_addPrecRound_floor hs₁tv hTnegtv W] at hlo
          obtain ⟨yv, hyv, hyv1, hyv2⟩ := floor_err_le W hw2 (-s₁v + -Tv) E
            (by rw [show -s₁v + -Tv = -(s₁v + Tv) by ring, abs_neg]
                exact hxbound Tv (by rw [abs_of_pos hTpos]))
          rw [← toVal_addPrecRound_floor hs₁negtv hTnegtv W] at hyv
          set lo := (addPrecRound s₁ (-(tailBound (r :: rs))) W .Floor).1 with hlodef
          set hi := -(addPrecRound (-s₁) (-(tailBound (r :: rs))) W .Floor).1 with hhidef
          have hhi : hi.toVal = some ((-yv : ℝ) : EReal) := by
            rw [hhidef, toVal_neg, hyv, Option.map_some, EReal.coe_neg]
          set hiv := -yv with hhiv
          have hlofin : lo.isFinite = true := isFinite_of_toVal_coe hlo
          have hhifin : hi.isFinite = true := isFinite_of_toVal_coe hhi
          have hlof : fval lo = lov := fval_of_toVal_coe hlo
          have hhif : fval hi = hiv := fval_of_toVal_coe hhi
          -- the exact sum lies strictly inside the bracket
          set v := s₁v + Rv with hv
          have hRlt : -Tv < Rv ∧ Rv < Tv := abs_lt.mp hTbound
          have hlov : lov < v := by linarith
          have hvhi : v < hiv := by linarith
          have hwidth : hiv - lov < 4 * B := by linarith
          -- every boundary in the bracket has magnitude at least `2^(E−2)`
          have hmag : ∀ c : ℝ, lov < c → c ≤ hiv → (2 : ℝ) ^ (E - 2) ≤ |c| := by
            intro c hc1 hc2
            have h1 : |c - s₁v| ≤ Tv + δ := by rw [abs_le]; constructor <;> linarith
            have h2 : |s₁v| - |c| ≤ |s₁v - c| := abs_sub_abs_le_abs_sub _ _
            rw [abs_sub_comm] at h2
            linarith
          have huniq : ∀ b c : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) →
              ((c : ℝ) : EReal) ∈ floatSet (p + 1) →
              lov < b → b ≤ hiv → lov < c → c ≤ hiv → b = c := by
            intro b c hb hc hb1 hb2 hc1 hc2
            by_contra hne
            have := boundary_dist p E b c hb hc (hmag b hb1 hb2) (hmag c hc1 hc2) hne
            rw [h4B] at this
            have : |b - c| < 4 * B := by rw [abs_lt]; constructor <;> linarith
            linarith
          have hRl : Rounds (fun q m => setPrecRound lo q m) lov :=
            hlof ▸ rounds_setPrecRound hlofin
          have hRh : Rounds (fun q m => setPrecRound hi q m) hiv :=
            hhif ▸ rounds_setPrecRound hhifin
          split
          · rename_i res hres
            exact roundingPossible_eq p mode hRl hRh hlov.le hvhi.le
              (fun h => absurd h hlov.ne) hres
          · -- the bracket straddles a boundary: locate it and decide the side exactly
            obtain ⟨bv, hbtv, hbmem, hbhi, hbgreatest⟩ := setPrecRound_floor_spec p hhi
            set b := (setPrecRound hi (p + 1) .Floor).1 with hbdef
            have hbfin : b.isFinite = true := isFinite_of_toVal_coe hbtv
            have hbf : fval b = bv := fval_of_toVal_coe hbtv
            have hdtv : (exactSub s₁ b).toVal = some ((s₁v - bv : ℝ) : EReal) := by
              rw [toVal_exactSub hs₁fin hbfin, hbf]
            have hdfin : (exactSub s₁ b).isFinite = true := isFinite_of_toVal_coe hdtv
            have hdf : fval (exactSub s₁ b) = s₁v - bv := fval_of_toVal_coe hdtv
            set d := exactSub s₁ b with hddef
            have hL : ∃ L : List AzFloat, (if d = zero then r :: rs else d :: r :: rs) = L ∧
                IsNormalList L ∧ L.length < (r :: rs).length + 2 ∧ realSum L = v - bv := by
              by_cases h0 : d = zero
              · refine ⟨r :: rs, ite_eq_left h0, hrestN,
                  by simp only [List.length_cons]; omega, ?_⟩
                have : fval d = 0 := by rw [h0, fval_zero]
                rw [hdf] at this
                rw [hv]; linarith
              · refine ⟨d :: r :: rs, ite_eq_right h0, ?_,
                  by simp only [List.length_cons]; omega, ?_⟩
                · intro y hy
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact isNormal_of_isFinite_ne_zero hdfin h0
                  · exact hrestN y hy
                · rw [realSum_cons, hdf, hv]; ring
            obtain ⟨L, hLeq, hLN, hLlen, hLsum⟩ := hL
            rw [hLeq, signSum_eq _ L hLN hLlen, hLsum]
            rcases lt_trichotomy v bv with hvb | hvb | hvb
            · -- the sum lies below the boundary: round the lower midpoint
              rw [compare_lt_iff_lt.mpr (by linarith : v - bv < 0)]
              dsimp only
              have hmfin := isFinite_exactAdd hlofin hbfin
              have hmtv : (exactAdd lo b >>> (1 : ℕ)).toVal
                  = some (((lov + bv) / 2 : ℝ) : EReal) := by
                rw [toVal_shiftRight_one hmfin, fval_exactAdd hlofin hbfin, hlof, hbf]
              rw [setPrecRound_eq_roundVal hmtv]
              apply roundVal_congr_of_no_boundary_Ioo p mode _ _ lov bv (by linarith) (by linarith)
                hlov hvb
              intro c hc ⟨h1, h2⟩
              have := huniq c bv hc hbmem h1 (by linarith) (by linarith) hbhi
              linarith
            · -- the sum is the boundary itself
              rw [hvb, sub_self, compare_eq_iff_eq.mpr rfl]
              dsimp only
              rw [setPrecRound_eq_roundVal hbtv]
            · -- the sum lies above the boundary: round the upper midpoint
              rw [compare_gt_iff_gt.mpr (by linarith : v - bv > 0)]
              dsimp only
              have hmfin := isFinite_exactAdd hbfin hhifin
              have hmtv : (exactAdd b hi >>> (1 : ℕ)).toVal
                  = some (((bv + hiv) / 2 : ℝ) : EReal) := by
                rw [toVal_shiftRight_one hmfin, fval_exactAdd hbfin hhifin, hbf, hhif]
              rw [setPrecRound_eq_roundVal hmtv]
              apply roundVal_congr_of_no_boundary_Ioo p mode _ _ bv hiv (by linarith) (by linarith)
                hvb hvhi
              intro c hc ⟨h1, h2⟩
              have := hbgreatest c hc h2.le
              linarith

/-! ### The main theorem -/

theorem fval_of_not_isNormal {x : AzFloat} (h : x.isNormal = false) : fval x = 0 := by
  cases x <;> simp_all [isNormal, fval]

/-- Dropping the non-normal floats (`NaN`, infinities and zero) does not change the real sum. -/
theorem realSum_filter_isNormal (xs : List AzFloat) :
    realSum (xs.filter isNormal) = realSum xs := by
  rw [realSum_filter xs isNormal]
  have : realSum (xs.filter fun x => !isNormal x) = 0 := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      rw [List.filter_cons]
      split_ifs with h
      · rw [realSum_cons, ih, fval_of_not_isNormal (by simpa using h), add_zero]
      · exact ih
  rw [this, add_zero]

/-- **`sumPrecRound` is the correct rounding of the sum**: `NaN` for a `NaN` term or two
infinities of opposite sign, the infinity for one infinity, and otherwise the rounding of the
exact real sum, with the tag comparing the result to it. -/
theorem sumPrecRound_eq (xs : List AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sumPrecRound xs p mode = roundVal p mode (Spec.sum xs) := by
  rw [Spec.sum_eq]
  unfold sumPrecRound
  dsimp only
  simp only [Bool.and_eq_true]
  split_ifs
  · exact (roundVal_none p mode).symm
  · exact (roundVal_none p mode).symm
  · exact (roundVal_of_toVal p mode (infinity true) ⊤ (Or.inr rfl) rfl).symm
  · exact (roundVal_of_toVal p mode (infinity false) ⊥ (Or.inr rfl) rfl).symm
  · rw [sumFinite_eq p mode _ _ (fun x hx => (List.mem_filter.mp hx).2) (Nat.lt_succ_self _),
      realSum_filter_isNormal]

end Azurite.AzFloat
