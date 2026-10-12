/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.CompareProduct
import Azurite.AzRat.Equiv.Unary
import Azurite.AzNat.Equiv.CompareProducts
import Azurite.AzInt.Equiv.CompareProducts

/-!
## Correctness of `AzRat.compareProduct`

`compareProduct_eq : compareProduct x y z = compare (toRat x * toRat y) (toRat z)`.  The
factorwise screens are monotonicity of products of three positive numbers (`screen3_spec`), the
bit-length screen is `2^(s₁+s₂+s₃−3) ≤ a₁ a₂ a₃ < 2^(s₁+s₂+s₃)`, and the rational layer reduces
the comparison of `(±P)/B` with `(±N)/D` to the comparison of the integers `±P·D` and `±N·B`
(`compare_div`), which `AzInt.compare_signed` turns into the shape of the function.
-/

namespace Azurite.AzRat

open Azurite.AzNat (compare_Nat_lt_iff compare_Nat_eq_iff compare_Nat_gt_iff
  two_pow_size_sub_one_le)

/-! ### The factorwise screens -/

/-- Three factors at most their partners, one strictly: the product is strictly smaller. -/
theorem mul3_lt_of_le {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (hs : a₁ < b₁ ∨ a₂ < b₂ ∨ a₃ < b₃) :
    a₁ * a₂ * a₃ < b₁ * b₂ * b₃ := by
  rcases hs with h | h | h
  · calc a₁ * a₂ * a₃ < b₁ * a₂ * a₃ :=
          Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right h ha₂) ha₃
      _ ≤ b₁ * b₂ * b₃ := Nat.mul_le_mul (Nat.mul_le_mul le_rfl h₂) h₃
  · calc a₁ * a₂ * a₃ < a₁ * b₂ * a₃ :=
          Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left h ha₁) ha₃
      _ ≤ b₁ * b₂ * b₃ := Nat.mul_le_mul (Nat.mul_le_mul h₁ le_rfl) h₃
  · calc a₁ * a₂ * a₃ < a₁ * a₂ * b₃ := Nat.mul_lt_mul_of_pos_left h (Nat.mul_pos ha₁ ha₂)
      _ ≤ b₁ * b₂ * b₃ := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) le_rfl

/-- **The screen is sound**: when it answers, it answers the comparison of the products. -/
theorem screen3_spec {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃) {o : Ordering}
    (h : screen3 (Ord.compare a₁ b₁) (Ord.compare a₂ b₂) (Ord.compare a₃ b₃) = some o) :
    Ord.compare (a₁ * a₂ * a₃) (b₁ * b₂ * b₃) = o := by
  unfold screen3 at h
  split_ifs at h with hle hall hge
  · obtain ⟨e₁, e₂, e₃⟩ := hall
    rw [compare_Nat_eq_iff] at e₁ e₂ e₃
    rw [Option.some.injEq] at h
    rw [← h, e₁, e₂, e₃, compare_Nat_eq_iff]
  · obtain ⟨l₁, l₂, l₃⟩ := hle
    rw [Option.some.injEq] at h
    rw [← h, compare_Nat_lt_iff]
    have h₁ : a₁ ≤ b₁ := not_lt.mp (fun hlt => l₁ ((compare_Nat_gt_iff _ _).mpr hlt))
    have h₂ : a₂ ≤ b₂ := not_lt.mp (fun hlt => l₂ ((compare_Nat_gt_iff _ _).mpr hlt))
    have h₃ : a₃ ≤ b₃ := not_lt.mp (fun hlt => l₃ ((compare_Nat_gt_iff _ _).mpr hlt))
    apply mul3_lt_of_le ha₁ ha₂ ha₃ h₁ h₂ h₃
    by_contra hns
    push Not at hns
    apply hall
    refine ⟨?_, ?_, ?_⟩ <;> rw [compare_Nat_eq_iff] <;> omega
  · obtain ⟨g₁, g₂, g₃⟩ := hge
    rw [Option.some.injEq] at h
    rw [← h, compare_Nat_gt_iff]
    have h₁ : b₁ ≤ a₁ := not_lt.mp (fun hlt => g₁ ((compare_Nat_lt_iff _ _).mpr hlt))
    have h₂ : b₂ ≤ a₂ := not_lt.mp (fun hlt => g₂ ((compare_Nat_lt_iff _ _).mpr hlt))
    have h₃ : b₃ ≤ a₃ := not_lt.mp (fun hlt => g₃ ((compare_Nat_lt_iff _ _).mpr hlt))
    apply mul3_lt_of_le hb₁ hb₂ hb₃ h₁ h₂ h₃
    by_contra hns
    push Not at hns
    apply hle
    refine ⟨?_, ?_, ?_⟩ <;> intro hg <;> rw [compare_Nat_gt_iff] at hg <;> omega

/-! ### The bit-length screen -/

theorem mul3_lt_of_size {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃)
    (h : a₁.size + a₂.size + a₃.size + 3 ≤ b₁.size + b₂.size + b₃.size) :
    a₁ * a₂ * a₃ < b₁ * b₂ * b₃ := by
  have hs₁ := Nat.size_pos.mpr hb₁
  have hs₂ := Nat.size_pos.mpr hb₂
  have hs₃ := Nat.size_pos.mpr hb₃
  calc a₁ * a₂ * a₃ < 2 ^ a₁.size * 2 ^ a₂.size * 2 ^ a₃.size := by
        apply Nat.mul_lt_mul_of_lt_of_le _ (Nat.lt_size_self a₃).le (Nat.two_pow_pos _)
        exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self a₁) (Nat.lt_size_self a₂).le
          (Nat.two_pow_pos _)
    _ = 2 ^ (a₁.size + a₂.size + a₃.size) := by rw [pow_add, pow_add]
    _ ≤ 2 ^ (b₁.size - 1 + (b₂.size - 1) + (b₃.size - 1)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ (b₁.size - 1) * 2 ^ (b₂.size - 1) * 2 ^ (b₃.size - 1) := by rw [pow_add, pow_add]
    _ ≤ b₁ * b₂ * b₃ :=
        Nat.mul_le_mul (Nat.mul_le_mul (two_pow_size_sub_one_le hb₁) (two_pow_size_sub_one_le hb₂))
          (two_pow_size_sub_one_le hb₃)

/-! ### The magnitude comparison -/

/-- **Correctness of `compareProductMag`**: `nx · ny · dz` against `nz · dx · dy`. -/
theorem compareProductMag_eq (nx dx ny dy nz dz : AzNat) (hnx : 0 < nx.toNat)
    (hdx : 0 < dx.toNat) (hny : 0 < ny.toNat) (hdy : 0 < dy.toNat) (hnz : 0 < nz.toNat)
    (hdz : 0 < dz.toNat) :
    compareProductMag nx dx ny dy nz dz
      = Ord.compare (nx.toNat * ny.toNat * dz.toNat) (nz.toNat * (dx.toNat * dy.toNat)) := by
  unfold compareProductMag
  simp only [AzNat.compare_eq_compare_toNat, ← AzNat.size_toNat]
  split_ifs with hs hs'
  · symm; rw [compare_Nat_gt_iff]
    have := mul3_lt_of_size (a₁ := nz.toNat) (a₂ := dx.toNat) (a₃ := dy.toNat)
      hnx hny hdz (by omega)
    rw [mul_assoc nz.toNat] at this
    exact this
  · symm; rw [compare_Nat_lt_iff]
    have := mul3_lt_of_size (a₁ := nx.toNat) (a₂ := ny.toNat) (a₃ := dz.toNat)
      hnz hdx hdy (by omega)
    rw [mul_assoc nz.toNat] at this
    exact this
  split
  · rename_i o h
    rw [← screen3_spec hnx hny hdz hdx hdy hnz h]
    congr 1
    ring
  · split
    · rename_i o h
      rw [← screen3_spec hnx hny hdz hnz hdy hdx h]
      congr 1
      ring
    · split
      · rename_i o h
        rw [← screen3_spec hnx hny hdz hdx hnz hdy h]
        congr 1
        ring
      · rw [AzNat.compareProducts_eq, AzNat.toNat_mul, AzNat.toNat_mul,
          mul_comm (dx.toNat * dy.toNat)]

/-! ### The rational layer -/

/-- Comparing two fractions with positive denominators is comparing the cross products. -/
theorem compare_div (A C B D : ℤ) (hB : 0 < B) (hD : 0 < D) :
    Ord.compare ((A : ℚ) / (B : ℚ)) ((C : ℚ) / (D : ℚ)) = Ord.compare (A * D) (C * B) := by
  have hB' : (0 : ℚ) < B := by exact_mod_cast hB
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  rcases h : Ord.compare (A * D) (C * B) with _ | _ | _
  · rw [compare_lt_iff_lt] at h
    rw [compare_lt_iff_lt, div_lt_iff₀ hB', div_mul_eq_mul_div, lt_div_iff₀ hD']
    exact_mod_cast h
  · rw [compare_eq_iff_eq] at h
    rw [compare_eq_iff_eq, div_eq_div_iff hB'.ne' hD'.ne']
    exact_mod_cast h
  · rw [compare_gt_iff_gt] at h
    rw [compare_gt_iff_gt, div_lt_iff₀ hD', div_mul_eq_mul_div, lt_div_iff₀ hB']
    exact_mod_cast h

theorem signed_mul_natCast (s : Bool) (P E : ℕ) :
    (if s then (P : ℤ) else -(P : ℤ)) * (E : ℤ)
      = if s then ((P * E : ℕ) : ℤ) else -((P * E : ℕ) : ℤ) := by
  cases s <;> simp [Nat.cast_mul]

/-- **Correctness of `compareProduct`.** -/
theorem compareProduct_eq (x y z : AzRat) :
    compareProduct x y z = Ord.compare (toRat x * toRat y) (toRat z) := by
  rcases x with ⟨xs, nx, dx, hdx, _, _⟩
  rcases y with ⟨ys, ny, dy, hdy, _, _⟩
  rcases z with ⟨zs, nz, dz, hdz, _, _⟩
  have hdx' : 0 < dx.toNat := Nat.pos_of_ne_zero (fun h => hdx ((AzNat.eq_zero_iff_toNat dx).mpr h))
  have hdy' : 0 < dy.toNat := Nat.pos_of_ne_zero (fun h => hdy ((AzNat.eq_zero_iff_toNat dy).mpr h))
  have hdz' : 0 < dz.toNat := Nat.pos_of_ne_zero (fun h => hdz ((AzNat.eq_zero_iff_toNat dz).mpr h))
  unfold compareProduct
  dsimp only
  rw [toRat_eq_divInt, toRat_eq_divInt, toRat_eq_divInt]
  dsimp only
  rw [Rat.divInt_mul_divInt, Rat.divInt_eq_div, Rat.divInt_eq_div, ← Nat.cast_mul,
    compare_div _ _ _ _ (by exact_mod_cast Nat.mul_pos hdx' hdy') (by exact_mod_cast hdz'),
    AzInt.toInt_mul_signed, signed_mul_natCast, signed_mul_natCast, AzInt.compare_signed]
  simp only [AzNat.eq_zero_iff_toNat, Nat.mul_eq_zero, hdx'.ne', hdy'.ne', hdz'.ne', or_false]
  split_ifs
  all_goals first
    | rfl
    | rw [compareProductMag_eq _ _ _ _ _ _ (by omega) hdx' (by omega) hdy' (by omega) hdz']

end Azurite.AzRat
