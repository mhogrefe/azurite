/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Div.Classic
import Azurite.AzNat.Equiv.Div.Newton

/-!
# Correctness of division

`divModWith_toNat`: the dispatcher between the classical path (`divModClassic_toNat`) and
Newton–Barrett division (`divModNewton_toNat`) returns `(Q, R)` with `Q V + R = U` and `R < V`;
hence `divModWith_eq_divMod` (the threshold does not change the result), `toNat_div`,
`toNat_mod`, `ofNat_div`, `ofNat_mod`.
-/

namespace Azurite.AzNat

/-- **Top-level correctness of `divModWith`**: `Q V + R = U`, and `R < V` for `V ≠ 0`. -/
theorem divModWith_toNat (threshold : Nat) (U V : AzNat) :
    (divModWith threshold U V).1.toNat * V.toNat + (divModWith threshold U V).2.toNat = U.toNat
    ∧ (V.toNat ≠ 0 → (divModWith threshold U V).2.toNat < V.toNat) := by
  unfold divModWith
  split_ifs with h
  · exact divModNewton_toNat reciprocalBaseThreshold newtonFFTThreshold shortProductBase (by decide)
      (by decide) U V
  · exact divModClassic_toNat threshold U V

/-- The Newton path is never taken for a zero divisor. -/
theorem useNewtonDiv_of_size_zero (U V : AzNat) (h : V.limbs.size = 0) :
    useNewtonDiv U V = false := by
  unfold useNewtonDiv
  simp only [h]
  have : ¬ divNewtonThreshold ≤ 0 := by unfold divNewtonThreshold; omega
  simp [this]

theorem divModWith_of_size_zero (threshold : Nat) (U V : AzNat) (h : V.limbs.size = 0) :
    divModWith threshold U V = (0, U) := by
  unfold divModWith
  rw [useNewtonDiv_of_size_zero U V h]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold divModClassic
  simp only [h, ↓reduceDIte]

/-- Correctness of `divMod` (the default threshold). -/
theorem divMod_toNat (U V : AzNat) :
    (divMod U V).1.toNat * V.toNat + (divMod U V).2.toNat = U.toNat
    ∧ (V.toNat ≠ 0 → (divMod U V).2.toNat < V.toNat) :=
  divModWith_toNat divDispatchThreshold U V

/-- The threshold only affects the recursion schedule, not the result. -/
theorem divModWith_eq_divMod (threshold : Nat) (U V : AzNat) :
    divModWith threshold U V = divMod U V := by
  obtain ⟨h1, h2⟩ := divModWith_toNat threshold U V
  obtain ⟨h1', h2'⟩ := divMod_toNat U V
  by_cases hV : V.toNat = 0
  · have h_size : V.limbs.size = 0 := (toNat_eq_zero_iff V).mp hV
    unfold divMod
    rw [divModWith_of_size_zero _ _ _ h_size, divModWith_of_size_zero _ _ _ h_size]
  · have hpos : 0 < V.toNat := Nat.pos_of_ne_zero hV
    have hdiv : ∀ Q R : AzNat, Q.toNat * V.toNat + R.toNat = U.toNat → R.toNat < V.toNat →
        Q.toNat = U.toNat / V.toNat ∧ R.toNat = U.toNat % V.toNat := by
      intro Q R h hlt
      have h_eq : U.toNat = R.toNat + Q.toNat * V.toNat := by omega
      constructor
      · rw [h_eq, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
      · rw [h_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    obtain ⟨hq1, hr1⟩ := hdiv _ _ h1 (h2 hV)
    obtain ⟨hq2, hr2⟩ := hdiv _ _ h1' (h2' hV)
    exact Prod.ext (toNat_injective (hq1.trans hq2.symm)) (toNat_injective (hr1.trans hr2.symm))

/-! ### Correctness of `div` and `mod` -/

/-- When the divisor is zero, `divMod` returns `(0, U)`. -/
private lemma divMod_of_toNat_zero (U V : AzNat) (hV : V.toNat = 0) :
    divMod U V = (0, U) := by
  have h_size : V.limbs.size = 0 := (toNat_eq_zero_iff V).mp hV
  unfold divMod
  exact divModWith_of_size_zero _ _ _ h_size

theorem divWith_eq_divModWith_fst (threshold : Nat) (U V : AzNat) :
    divWith threshold U V = (divModWith threshold U V).1 := by
  unfold divWith divModWith
  split_ifs
  · rfl
  · exact divClassic_eq_divModClassic_fst threshold U V

theorem modWith_eq_divModWith_snd (threshold : Nat) (U V : AzNat) :
    modWith threshold U V = (divModWith threshold U V).2 := by
  unfold modWith divModWith
  split_ifs
  · rfl
  · exact modClassic_eq_divModClassic_snd threshold U V

theorem div_eq_divMod_fst (U V : AzNat) : div U V = (divMod U V).1 :=
  divWith_eq_divModWith_fst divDispatchThreshold U V

theorem mod_eq_divMod_snd (U V : AzNat) : mod U V = (divMod U V).2 :=
  modWith_eq_divModWith_snd divDispatchThreshold U V

/-- `(U / V).toNat = U.toNat / V.toNat`. -/
@[simp] theorem toNat_div (U V : AzNat) : (U / V).toNat = U.toNat / V.toNat := by
  show (div U V).toNat = _
  rw [div_eq_divMod_fst]
  by_cases hV : V.toNat = 0
  · rw [divMod_of_toNat_zero U V hV, hV, Nat.div_zero, toNat_zero]
  · obtain ⟨h_id, h_lt⟩ := divMod_toNat U V
    have h_lt' := h_lt hV
    have h_pos : 0 < V.toNat := Nat.pos_of_ne_zero hV
    have h_eq : U.toNat
        = (divMod U V).2.toNat + (divMod U V).1.toNat * V.toNat := by omega
    rw [h_eq, Nat.add_mul_div_right _ _ h_pos, Nat.div_eq_of_lt h_lt', Nat.zero_add]

/-- `(U % V).toNat = U.toNat % V.toNat`. -/
@[simp] theorem toNat_mod (U V : AzNat) : (U % V).toNat = U.toNat % V.toNat := by
  show (mod U V).toNat = _
  rw [mod_eq_divMod_snd]
  by_cases hV : V.toNat = 0
  · rw [divMod_of_toNat_zero U V hV, hV, Nat.mod_zero]
  · obtain ⟨h_id, h_lt⟩ := divMod_toNat U V
    have h_lt' := h_lt hV
    have h_pos : 0 < V.toNat := Nat.pos_of_ne_zero hV
    have h_eq : U.toNat
        = (divMod U V).2.toNat + (divMod U V).1.toNat * V.toNat := by omega
    rw [h_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_lt']

/-- `ofNat`-version of `toNat_div`. -/
theorem ofNat_div (m n : Nat) : ofNat (m / n) = ofNat m / ofNat n := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_div, toNat_ofNat, toNat_ofNat]

/-- `ofNat`-version of `toNat_mod`. -/
theorem ofNat_mod (m n : Nat) : ofNat (m % n) = ofNat m % ofNat n := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_mod, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat
