/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ZivPair
import Azurite.AzFloat.Equiv.Ziv

/-!
# Equivalence: Ziv's strategy for a pair of values

* `roundingPossible₂_eq`: when the joint test answers, it answers with the two roundings.
* `zivLoopCertified₂_eq`: the certified joint loop returns the two correctly rounded values.
* `eventually_isSome_of_not_mem_threshold`: for a non-boundary value and brackets whose width
  tends to zero, `roundingPossible` answers at **every** sufficiently large level `w₀ · 2^f`
  (the form needed to find a common level for two values), and
  `exists_isSome₂_of_irrational_threshold`: the joint certificate for two irrational values.
-/

namespace Azurite.AzFloat

theorem roundingPossible₂_isSome {a : (Roundable × Roundable) × (Roundable × Roundable)}
    {p : ℕ} {mode : RoundingMode} (h₁ : (roundingPossible a.1.1 a.1.2 p mode).isSome = true)
    (h₂ : (roundingPossible a.2.1 a.2.2 p mode).isSome = true) :
    (roundingPossible₂ a p mode).isSome = true := by
  obtain ⟨r₁, hr₁⟩ := Option.isSome_iff_exists.mp h₁
  obtain ⟨r₂, hr₂⟩ := Option.isSome_iff_exists.mp h₂
  unfold roundingPossible₂
  rw [hr₁, hr₂]
  rfl

theorem roundingPossible₂_eq_some {a : (Roundable × Roundable) × (Roundable × Roundable)}
    {p : ℕ} {mode : RoundingMode} {r : (AzFloat × Ordering) × (AzFloat × Ordering)}
    (h : roundingPossible₂ a p mode = some r) :
    roundingPossible a.1.1 a.1.2 p mode = some r.1 ∧
      roundingPossible a.2.1 a.2.2 p mode = some r.2 := by
  unfold roundingPossible₂ at h
  split at h
  · next r₁ r₂ h₁ h₂ =>
    rw [Option.some.injEq] at h
    subst h
    exact ⟨h₁, h₂⟩
  · exact absurd h (by simp)

/-- When the joint test answers, it answers with the roundings of the two exact values. -/
theorem roundingPossible₂_eq (p : ℕ) [NeZero p] (mode : RoundingMode)
    {a : (Roundable × Roundable) × (Roundable × Roundable)} {l₁ h₁ v₁ l₂ h₂ v₂ : ℝ}
    (hl₁ : Rounds a.1.1 l₁) (hh₁ : Rounds a.1.2 h₁) (hv₁ : l₁ ≤ v₁) (hv₁' : v₁ ≤ h₁)
    (hB₁ : ((v₁ : ℝ) : EReal) ∉ floatSet (p + 1))
    (hl₂ : Rounds a.2.1 l₂) (hh₂ : Rounds a.2.2 h₂) (hv₂ : l₂ ≤ v₂) (hv₂' : v₂ ≤ h₂)
    (hB₂ : ((v₂ : ℝ) : EReal) ∉ floatSet (p + 1))
    {r : (AzFloat × Ordering) × (AzFloat × Ordering)}
    (hr : roundingPossible₂ a p mode = some r) :
    r = (roundVal p mode (some (v₁ : EReal)), roundVal p mode (some (v₂ : EReal))) := by
  obtain ⟨hr₁, hr₂⟩ := roundingPossible₂_eq_some hr
  exact Prod.ext (roundingPossible_eq' p mode hl₁ hh₁ hv₁ hv₁' (Or.inr hB₁) hr₁)
    (roundingPossible_eq' p mode hl₂ hh₂ hv₂ hv₂' (Or.inr hB₂) hr₂)

/-- The certified joint loop returns the roundings of the two exact values, at every stage. -/
theorem zivLoopCertified₂_go_eq (p : ℕ) [NeZero p] (mode : RoundingMode)
    (approx : Nat → (Roundable × Roundable) × (Roundable × Roundable)) (v₁ v₂ : ℝ)
    (hB₁ : ((v₁ : ℝ) : EReal) ∉ floatSet (p + 1)) (hB₂ : ((v₂ : ℝ) : EReal) ∉ floatSet (p + 1))
    (w₀ : ℕ)
    (happrox : ∀ w, w₀ ≤ w → ∃ l₁ h₁ l₂ h₂ : ℝ, Rounds (approx w).1.1 l₁ ∧
      Rounds (approx w).1.2 h₁ ∧ l₁ ≤ v₁ ∧ v₁ ≤ h₁ ∧ Rounds (approx w).2.1 l₂ ∧
      Rounds (approx w).2.2 h₂ ∧ l₂ ≤ v₂ ∧ v₂ ≤ h₂)
    (hw₀ : 0 < w₀)
    (h : ∃ f : Nat, (roundingPossible₂ (approx (w₀ * 2 ^ f)) p mode).isSome = true) :
    ∀ (n f : ℕ) (hf : ∀ g < f, (roundingPossible₂ (approx (w₀ * 2 ^ g)) p mode).isSome = false),
      Nat.find h - f = n →
      zivLoopCertified₂.go approx p mode w₀ h f hf
        = (roundVal p mode (some (v₁ : EReal)), roundVal p mode (some (v₂ : EReal)))
  | n, f, hf, hn => by
    have hw : w₀ ≤ w₀ * 2 ^ f := Nat.le_mul_of_pos_right _ (by positivity)
    obtain ⟨l₁, h₁, l₂, h₂, hl₁, hh₁, a₁, b₁, hl₂, hh₂, a₂, b₂⟩ := happrox _ hw
    rw [zivLoopCertified₂.go.eq_def]
    split
    · rename_i r hr
      exact roundingPossible₂_eq p mode hl₁ hh₁ a₁ b₁ hB₁ hl₂ hh₂ a₂ b₂ hB₂ hr
    · rename_i hr
      have hlt : f < Nat.find h := by
        by_contra hcon
        push Not at hcon
        have hspec := Nat.find_spec h
        rcases Nat.lt_or_eq_of_le hcon with hlt' | heq
        · rw [hf _ hlt'] at hspec; exact Bool.false_ne_true hspec
        · rw [heq, hr] at hspec; exact Bool.false_ne_true hspec
      cases n with
      | zero => omega
      | succ m =>
        exact zivLoopCertified₂_go_eq p mode approx v₁ v₂ hB₁ hB₂ w₀ happrox hw₀ h m (f + 1) _
          (by omega)

/-- **The certified joint Ziv loop returns the two correctly rounded values**, for brackets that
are valid from the starting precision `w₀` on and values that are not rounding boundaries. -/
theorem zivLoopCertified₂_eq (p : ℕ) [NeZero p] (mode : RoundingMode)
    (approx : Nat → (Roundable × Roundable) × (Roundable × Roundable)) (v₁ v₂ : ℝ)
    (hB₁ : ((v₁ : ℝ) : EReal) ∉ floatSet (p + 1)) (hB₂ : ((v₂ : ℝ) : EReal) ∉ floatSet (p + 1))
    (w₀ : ℕ) (hw₀ : 0 < w₀)
    (happrox : ∀ w, w₀ ≤ w → ∃ l₁ h₁ l₂ h₂ : ℝ, Rounds (approx w).1.1 l₁ ∧
      Rounds (approx w).1.2 h₁ ∧ l₁ ≤ v₁ ∧ v₁ ≤ h₁ ∧ Rounds (approx w).2.1 l₂ ∧
      Rounds (approx w).2.2 h₂ ∧ l₂ ≤ v₂ ∧ v₂ ≤ h₂)
    (h : ∃ f : Nat, (roundingPossible₂ (approx (w₀ * 2 ^ f)) p mode).isSome = true) :
    zivLoopCertified₂ approx p mode w₀ h
      = (roundVal p mode (some (v₁ : EReal)), roundVal p mode (some (v₂ : EReal))) :=
  zivLoopCertified₂_go_eq p mode approx v₁ v₂ hB₁ hB₂ w₀ happrox hw₀ h _ 0 _ rfl

/-- For a nonzero value that is not a boundary and brackets valid above a threshold `W₀` whose
width `ε w` tends to zero, rounding is possible at **every** level `w₀ · 2^f` from some `f` on. -/
theorem eventually_isSome_of_not_mem_threshold (p : ℕ) [NeZero p] (mode : RoundingMode)
    (approx : Nat → Roundable × Roundable) {v : ℝ} (hv0 : v ≠ 0)
    (hvB : ((v : ℝ) : EReal) ∉ floatSet (p + 1)) (ε : ℕ → ℝ)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) (W₀ : ℕ)
    (happrox : ∀ w, W₀ ≤ w → ∃ lv hv' : ℝ, Rounds (approx w).1 lv ∧ Rounds (approx w).2 hv' ∧
      lv ≤ v ∧ v ≤ hv' ∧ hv' - lv ≤ ε w)
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ F : ℕ, ∀ f, F ≤ f →
      (roundingPossible (approx (w₀ * 2 ^ f)).1 (approx (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  obtain ⟨bm, bp, hbm, hbp, hbmv, hvbp, hgreatest, hleast, -, -⟩ :=
    adjacent_boundaries p v hv0 hvB
  set D := min (v - bm) (bp - v) with hD
  have hD0 : 0 < D := lt_min (by linarith) (by linarith)
  obtain ⟨W₁, hW₁⟩ := (hε.eventually (gt_mem_nhds hD0)).exists_forall_of_atTop
  refine ⟨W₀ + W₁, fun f hFf => ?_⟩
  have hf : W₀ + W₁ ≤ w₀ * 2 ^ f :=
    calc W₀ + W₁ ≤ f := hFf
      _ ≤ 2 ^ f := Nat.lt_two_pow_self.le
      _ ≤ w₀ * 2 ^ f := Nat.le_mul_of_pos_left _ hw₀
  obtain ⟨lv, hv', hl, hh, hlo, hhi, hwidth⟩ := happrox (w₀ * 2 ^ f) (by omega)
  have hεw : ε (w₀ * 2 ^ f) < D := hW₁ _ (by omega)
  apply roundingPossible_isSome_of_no_boundary p mode hl hh (by linarith)
  refine no_boundary_of_dist p v _ _ D hv0 hvB hlo hhi ?_ (by linarith)
  intro b hb hbne _
  rcases le_or_gt b v with hble | hbgt
  · have := hgreatest b hb hble
    rw [abs_of_nonneg (by linarith)]
    calc D ≤ v - bm := min_le_left _ _
      _ ≤ v - b := by linarith
  · have := hleast b hb hbgt.le
    rw [abs_of_neg (by linarith)]
    calc D ≤ bp - v := min_le_right _ _
      _ ≤ -(v - b) := by linarith

/-- **The joint certificate for two irrational values**: brackets valid above a threshold `W₀`
with widths tending to zero reach a level where both roundings are possible. -/
theorem exists_isSome₂_of_irrational_threshold (p : ℕ) [NeZero p] (mode : RoundingMode)
    (approx : Nat → (Roundable × Roundable) × (Roundable × Roundable)) {v₁ v₂ : ℝ}
    (hv₁ : Irrational v₁) (hv₂ : Irrational v₂) (ε₁ ε₂ : ℕ → ℝ)
    (hε₁ : Filter.Tendsto ε₁ Filter.atTop (nhds 0))
    (hε₂ : Filter.Tendsto ε₂ Filter.atTop (nhds 0)) (W₀ : ℕ)
    (happrox₁ : ∀ w, W₀ ≤ w → ∃ lv hv' : ℝ, Rounds (approx w).1.1 lv ∧
      Rounds (approx w).1.2 hv' ∧ lv ≤ v₁ ∧ v₁ ≤ hv' ∧ hv' - lv ≤ ε₁ w)
    (happrox₂ : ∀ w, W₀ ≤ w → ∃ lv hv' : ℝ, Rounds (approx w).2.1 lv ∧
      Rounds (approx w).2.2 hv' ∧ lv ≤ v₂ ∧ v₂ ≤ hv' ∧ hv' - lv ≤ ε₂ w)
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible₂ (approx (w₀ * 2 ^ f)) p mode).isSome = true := by
  obtain ⟨F₁, hF₁⟩ := eventually_isSome_of_not_mem_threshold p mode (fun w => (approx w).1)
    hv₁.ne_zero (not_mem_floatSet_of_irrational p hv₁) ε₁ hε₁ W₀ happrox₁ w₀ hw₀
  obtain ⟨F₂, hF₂⟩ := eventually_isSome_of_not_mem_threshold p mode (fun w => (approx w).2)
    hv₂.ne_zero (not_mem_floatSet_of_irrational p hv₂) ε₂ hε₂ W₀ happrox₂ w₀ hw₀
  exact ⟨max F₁ F₂, roundingPossible₂_isSome (hF₁ _ (le_max_left _ _))
    (hF₂ _ (le_max_right _ _))⟩

end Azurite.AzFloat
