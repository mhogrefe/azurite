/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.CompareProducts
import Azurite.AzRat.Equiv.CompareProduct

/-!
## Correctness of `AzRat.compareProducts`

`compareProducts_eq : compareProducts w x y z = compare (toRat w * toRat x) (toRat y * toRat z)`,
by the four-factor versions of the screens of `compareProduct` (`screen4_spec`,
`mul4_lt_of_size`), the cross-product reduction `compare_div`, and the sign dispatch of
`AzInt.compare_signed`.
-/

namespace Azurite.AzRat

open Azurite.AzNat (compare_Nat_lt_iff compare_Nat_eq_iff compare_Nat_gt_iff
  two_pow_size_sub_one_le)

/-! ### The factorwise screens -/

theorem mul4_lt_of_le {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) (h₄ : a₄ ≤ b₄)
    (hs : a₁ < b₁ ∨ a₂ < b₂ ∨ a₃ < b₃ ∨ a₄ < b₄) :
    a₁ * a₂ * a₃ * a₄ < b₁ * b₂ * b₃ * b₄ := by
  have hle : ∀ {c₁ c₂ c₃ c₄ : ℕ}, c₁ ≤ b₁ → c₂ ≤ b₂ → c₃ ≤ b₃ → c₄ ≤ b₄ →
      c₁ * c₂ * c₃ * c₄ ≤ b₁ * b₂ * b₃ * b₄ := fun g₁ g₂ g₃ g₄ =>
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul g₁ g₂) g₃) g₄
  rcases hs with h | h | h | h
  · calc a₁ * a₂ * a₃ * a₄ < b₁ * a₂ * a₃ * a₄ :=
          Nat.mul_lt_mul_of_pos_right
            (Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right h ha₂) ha₃) ha₄
      _ ≤ b₁ * b₂ * b₃ * b₄ := hle le_rfl h₂ h₃ h₄
  · calc a₁ * a₂ * a₃ * a₄ < a₁ * b₂ * a₃ * a₄ :=
          Nat.mul_lt_mul_of_pos_right
            (Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left h ha₁) ha₃) ha₄
      _ ≤ b₁ * b₂ * b₃ * b₄ := hle h₁ le_rfl h₃ h₄
  · calc a₁ * a₂ * a₃ * a₄ < a₁ * a₂ * b₃ * a₄ :=
          Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left h (Nat.mul_pos ha₁ ha₂)) ha₄
      _ ≤ b₁ * b₂ * b₃ * b₄ := hle h₁ h₂ le_rfl h₄
  · calc a₁ * a₂ * a₃ * a₄ < a₁ * a₂ * a₃ * b₄ :=
          Nat.mul_lt_mul_of_pos_left h (Nat.mul_pos (Nat.mul_pos ha₁ ha₂) ha₃)
      _ ≤ b₁ * b₂ * b₃ * b₄ := hle h₁ h₂ h₃ le_rfl

/-- **The screen is sound.** -/
theorem screen4_spec {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (ha₄ : 0 < a₄) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃) (hb₄ : 0 < b₄) {o : Ordering}
    (h : screen4 (Ord.compare a₁ b₁) (Ord.compare a₂ b₂) (Ord.compare a₃ b₃) (Ord.compare a₄ b₄)
      = some o) :
    Ord.compare (a₁ * a₂ * a₃ * a₄) (b₁ * b₂ * b₃ * b₄) = o := by
  unfold screen4 at h
  split_ifs at h with hle hall hge
  · obtain ⟨e₁, e₂, e₃, e₄⟩ := hall
    rw [compare_Nat_eq_iff] at e₁ e₂ e₃ e₄
    rw [Option.some.injEq] at h
    rw [← h, e₁, e₂, e₃, e₄, compare_Nat_eq_iff]
  · obtain ⟨l₁, l₂, l₃, l₄⟩ := hle
    rw [Option.some.injEq] at h
    rw [← h, compare_Nat_lt_iff]
    have h₁ : a₁ ≤ b₁ := not_lt.mp (fun hlt => l₁ ((compare_Nat_gt_iff _ _).mpr hlt))
    have h₂ : a₂ ≤ b₂ := not_lt.mp (fun hlt => l₂ ((compare_Nat_gt_iff _ _).mpr hlt))
    have h₃ : a₃ ≤ b₃ := not_lt.mp (fun hlt => l₃ ((compare_Nat_gt_iff _ _).mpr hlt))
    have h₄ : a₄ ≤ b₄ := not_lt.mp (fun hlt => l₄ ((compare_Nat_gt_iff _ _).mpr hlt))
    apply mul4_lt_of_le ha₁ ha₂ ha₃ ha₄ h₁ h₂ h₃ h₄
    by_contra hns
    push Not at hns
    apply hall
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [compare_Nat_eq_iff] <;> omega
  · obtain ⟨g₁, g₂, g₃, g₄⟩ := hge
    rw [Option.some.injEq] at h
    rw [← h, compare_Nat_gt_iff]
    have h₁ : b₁ ≤ a₁ := not_lt.mp (fun hlt => g₁ ((compare_Nat_lt_iff _ _).mpr hlt))
    have h₂ : b₂ ≤ a₂ := not_lt.mp (fun hlt => g₂ ((compare_Nat_lt_iff _ _).mpr hlt))
    have h₃ : b₃ ≤ a₃ := not_lt.mp (fun hlt => g₃ ((compare_Nat_lt_iff _ _).mpr hlt))
    have h₄ : b₄ ≤ a₄ := not_lt.mp (fun hlt => g₄ ((compare_Nat_lt_iff _ _).mpr hlt))
    apply mul4_lt_of_le hb₁ hb₂ hb₃ hb₄ h₁ h₂ h₃ h₄
    by_contra hns
    push Not at hns
    apply hle
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hg <;> rw [compare_Nat_gt_iff] at hg <;> omega

/-! ### The bit-length screen -/

theorem mul4_lt_of_size {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℕ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hb₃ : 0 < b₃) (hb₄ : 0 < b₄)
    (h : a₁.size + a₂.size + a₃.size + a₄.size + 4 ≤ b₁.size + b₂.size + b₃.size + b₄.size) :
    a₁ * a₂ * a₃ * a₄ < b₁ * b₂ * b₃ * b₄ := by
  have hs₁ := Nat.size_pos.mpr hb₁
  have hs₂ := Nat.size_pos.mpr hb₂
  have hs₃ := Nat.size_pos.mpr hb₃
  have hs₄ := Nat.size_pos.mpr hb₄
  calc a₁ * a₂ * a₃ * a₄ < 2 ^ a₁.size * 2 ^ a₂.size * 2 ^ a₃.size * 2 ^ a₄.size := by
        apply Nat.mul_lt_mul_of_lt_of_le _ (Nat.lt_size_self a₄).le (Nat.two_pow_pos _)
        apply Nat.mul_lt_mul_of_lt_of_le _ (Nat.lt_size_self a₃).le (Nat.two_pow_pos _)
        exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self a₁) (Nat.lt_size_self a₂).le
          (Nat.two_pow_pos _)
    _ = 2 ^ (a₁.size + a₂.size + a₃.size + a₄.size) := by rw [pow_add, pow_add, pow_add]
    _ ≤ 2 ^ (b₁.size - 1 + (b₂.size - 1) + (b₃.size - 1) + (b₄.size - 1)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ (b₁.size - 1) * 2 ^ (b₂.size - 1) * 2 ^ (b₃.size - 1) * 2 ^ (b₄.size - 1) := by
        rw [pow_add, pow_add, pow_add]
    _ ≤ b₁ * b₂ * b₃ * b₄ :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (two_pow_size_sub_one_le hb₁)
          (two_pow_size_sub_one_le hb₂)) (two_pow_size_sub_one_le hb₃))
          (two_pow_size_sub_one_le hb₄)

/-! ### The magnitude comparison -/

/-- **Correctness of `compareProductsMag`**: `nw · nx · dy · dz` against `ny · nz · dw · dx`. -/
theorem compareProductsMag_eq (nw dw nx dx ny dy nz dz : AzNat) (hnw : 0 < nw.toNat)
    (hdw : 0 < dw.toNat) (hnx : 0 < nx.toNat) (hdx : 0 < dx.toNat) (hny : 0 < ny.toNat)
    (hdy : 0 < dy.toNat) (hnz : 0 < nz.toNat) (hdz : 0 < dz.toNat) :
    compareProductsMag nw dw nx dx ny dy nz dz
      = Ord.compare (nw.toNat * nx.toNat * (dy.toNat * dz.toNat))
          (ny.toNat * nz.toNat * (dw.toNat * dx.toNat)) := by
  unfold compareProductsMag
  simp only [AzNat.compare_eq_compare_toNat, ← AzNat.size_toNat]
  split_ifs with hs hs'
  · symm; rw [compare_Nat_gt_iff]
    have := mul4_lt_of_size (a₁ := ny.toNat) (a₂ := nz.toNat) (a₃ := dw.toNat)
      (a₄ := dx.toNat) hnw hnx hdy hdz (by omega)
    rw [mul_assoc (ny.toNat * nz.toNat), mul_assoc (nw.toNat * nx.toNat)] at this
    exact this
  · symm; rw [compare_Nat_lt_iff]
    have := mul4_lt_of_size (a₁ := nw.toNat) (a₂ := nx.toNat) (a₃ := dy.toNat)
      (a₄ := dz.toNat) hny hnz hdw hdx (by omega)
    rw [mul_assoc (ny.toNat * nz.toNat), mul_assoc (nw.toNat * nx.toNat)] at this
    exact this
  split
  · rename_i o h
    rw [← screen4_spec hnw hnx hdy hdz hdw hdx hny hnz h]
    congr 1 <;> ring
  · split
    · rename_i o h
      rw [← screen4_spec hnw hnx hdy hdz hny hnz hdw hdx h]
      congr 1 <;> ring
    · split
      · rename_i o h
        rw [← screen4_spec hnw hnx hdy hdz hnz hny hdx hdw h]
        congr 1 <;> ring
      · rw [AzNat.compareProducts_eq, AzNat.toNat_mul, AzNat.toNat_mul, AzNat.toNat_mul,
          AzNat.toNat_mul]

/-- **Correctness of `compareProducts`.** -/
theorem compareProducts_eq (w x y z : AzRat) :
    compareProducts w x y z = Ord.compare (toRat w * toRat x) (toRat y * toRat z) := by
  rcases w with ⟨ws, nw, dw, hdw, _, _⟩
  rcases x with ⟨xs, nx, dx, hdx, _, _⟩
  rcases y with ⟨ys, ny, dy, hdy, _, _⟩
  rcases z with ⟨zs, nz, dz, hdz, _, _⟩
  have hdw' : 0 < dw.toNat :=
    Nat.pos_of_ne_zero (fun h => hdw ((AzNat.eq_zero_iff_toNat dw).mpr h))
  have hdx' : 0 < dx.toNat :=
    Nat.pos_of_ne_zero (fun h => hdx ((AzNat.eq_zero_iff_toNat dx).mpr h))
  have hdy' : 0 < dy.toNat :=
    Nat.pos_of_ne_zero (fun h => hdy ((AzNat.eq_zero_iff_toNat dy).mpr h))
  have hdz' : 0 < dz.toNat :=
    Nat.pos_of_ne_zero (fun h => hdz ((AzNat.eq_zero_iff_toNat dz).mpr h))
  unfold compareProducts
  dsimp only
  rw [toRat_eq_divInt, toRat_eq_divInt, toRat_eq_divInt, toRat_eq_divInt]
  dsimp only
  rw [Rat.divInt_mul_divInt, Rat.divInt_mul_divInt, Rat.divInt_eq_div, Rat.divInt_eq_div,
    ← Nat.cast_mul, ← Nat.cast_mul,
    compare_div _ _ _ _ (by exact_mod_cast Nat.mul_pos hdw' hdx')
      (by exact_mod_cast Nat.mul_pos hdy' hdz'),
    AzInt.toInt_mul_signed, AzInt.toInt_mul_signed, signed_mul_natCast, signed_mul_natCast,
    AzInt.compare_signed]
  simp only [AzNat.eq_zero_iff_toNat, Nat.mul_eq_zero, hdw'.ne', hdx'.ne', hdy'.ne', hdz'.ne',
    or_false, or_self]
  split_ifs
  all_goals first
    | rfl
    | rw [compareProductsMag_eq _ _ _ _ _ _ _ _ (by omega) hdw' (by omega) hdx' (by omega) hdy'
        (by omega) hdz']

end Azurite.AzRat
