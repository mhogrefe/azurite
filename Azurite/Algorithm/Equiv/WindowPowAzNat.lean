/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Correctness of the fixed-window `AzNat` exponentiation**:
  `windowPowAzNat a e = a ^ e.toNat` in any monoid with a lawful `Square`.
-/
import Azurite.Algorithm.WindowPowAzNat
import Azurite.AzNat.Equiv.GetBits
import Azurite.AzNat.Equiv.Size

namespace Azurite

variable {M : Type _} [Monoid M] [Square M]

omit [Square M] in
theorem powTable_foldl (a : M) :
    ∀ t : ℕ, (List.range t).foldl (fun (st : Array M × M) _ => (st.1.push st.2, st.2 * a)) (#[], 1)
      = (((List.range t).map fun i => a ^ i).toArray, a ^ t)
  | 0 => by simp
  | t + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, powTable_foldl a t]
    simp [pow_succ]

omit [Square M] in
theorem powTable_getD (a : M) (w : ℕ) {i : ℕ} (hi : i < 2 ^ w) : (powTable a w).getD i 1 = a ^ i := by
  rw [powTable, powTable_foldl]
  simp [hi]

theorem windowPowAux_eq (a : M) (e : AzNat) :
    ∀ (j : ℕ) (r : M), r = a ^ (e.toNat / 2 ^ (j * windowW)) →
      windowPowAux (powTable a windowW) e j r = a ^ e.toNat
  | 0, r, hr => by
    rw [windowPowAux, hr]
    simp
  | j + 1, r, hr => by
    rw [windowPowAux]
    refine windowPowAux_eq a e j _ ?_
    rw [squareN_eq, hr, powTable_getD a windowW (by
      rw [AzNat.toNat_getBitsAsLimb, Nat.add_sub_cancel_left]
      exact Nat.mod_lt _ (pow_pos two_pos _)), AzNat.toNat_getBitsAsLimb, Nat.add_sub_cancel_left,
      ← pow_mul, ← pow_add]
    congr 1
    have h1 : e.toNat / 2 ^ ((j + 1) * windowW) = e.toNat / 2 ^ (j * windowW) / 2 ^ windowW := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, add_mul, one_mul]
    rw [h1, mul_comm, Nat.div_add_mod]

/-- **`windowPowAzNat` is the monoid power.** -/
theorem windowPowAzNat_eq_pow (a : M) (e : AzNat) : windowPowAzNat a e = a ^ e.toNat := by
  rw [windowPowAzNat]
  refine windowPowAux_eq a e _ 1 ?_
  have hsize : e.size ≤ (e.size + windowW - 1) / windowW * windowW := by
    have := Nat.div_add_mod (e.size + windowW - 1) windowW
    have := Nat.mod_lt (e.size + windowW - 1) (by decide : 0 < windowW)
    simp only [windowW] at *
    omega
  have hlt : e.toNat < 2 ^ ((e.size + windowW - 1) / windowW * windowW) := by
    calc e.toNat < 2 ^ e.toNat.size := Nat.lt_size_self _
      _ = 2 ^ e.size := by rw [AzNat.size_toNat]
      _ ≤ 2 ^ ((e.size + windowW - 1) / windowW * windowW) := Nat.pow_le_pow_right two_pos hsize
  rw [Nat.div_eq_of_lt hlt, pow_zero]

end Azurite
