/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.Core

/-!
# Existence of the parameters

`exists_params`: for all constants `cst`, `γ` there is a system of parameters `Params cst γ`:
with `s₀ = 100 + cst + γ`, `J = 2^(16 s₀)`, `Lc = 2^(13 s₀)`, `ζ = 2^(16 s₀ + 8) s₀`,
`T(s) = 2^(16 s + 9) s`.  Everything is bounded by powers of two and the exponents are
compared; the margins are `2^(3 s₀)` at the start and `2^s` in the steps.
-/

namespace Azurite.Chudnovsky

/-- `T(s) = 2^(16 s + 9) s`. -/
def pT (s : ℕ) : ℕ := 2 ^ (16 * s + 9) * s

/-- The exponent of the measure at stage `s`. -/
def pMu (cst s : ℕ) : ℕ := cst * pT s ^ 2 * Nat.size (pT s) ^ 3

theorem pow_four_le_two_pow {s : ℕ} (hs : 16 ≤ s) : s ^ 4 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    have h1 : 16 * s ^ 3 ≤ s ^ 4 := by
      have := Nat.mul_le_mul_right (s ^ 3) hs
      calc 16 * s ^ 3 ≤ s * s ^ 3 := this
        _ = s ^ 4 := by ring
    have hs1 : 1 ≤ s := by omega
    have h2 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right hs1 (by norm_num)
    have h3 : s ≤ s ^ 3 := Nat.le_self_pow (by norm_num) s
    have h4 : 1 ≤ s ^ 3 := Nat.one_le_pow _ _ hs1
    calc (s + 1) ^ 4 = s ^ 4 + 4 * s ^ 3 + 6 * s ^ 2 + 4 * s + 1 := by ring
      _ ≤ 2 * s ^ 4 := by linarith
      _ ≤ 2 * 2 ^ s := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (s + 1) := by ring

theorem mul_two_pow_hundred_le {c s : ℕ} (h : 100 + c ≤ s) : c * 2 ^ 100 ≤ 2 ^ s := by
  calc c * 2 ^ 100 ≤ 2 ^ c * 2 ^ 100 := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = 2 ^ (c + 100) := by rw [pow_add]
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem size_pT_le {s : ℕ} (hs : 1 ≤ s) : Nat.size (pT s) ≤ 27 * s := by
  have h1 := size_mul_le (2 ^ (16 * s + 9)) s
  have h2 : Nat.size (2 ^ (16 * s + 9)) = 16 * s + 9 + 1 := Nat.size_pow
  have h3 : Nat.size s ≤ s := Nat.size_le.mpr Nat.lt_two_pow_self
  unfold pT
  omega

/-- The exponent of the measure is small compared with `2^(35 s)`. -/
theorem pMu_le {cst s : ℕ} (hs : 100 + cst ≤ s) : pMu cst s ≤ s * 2 ^ (35 * s) := by
  have hs1 : 1 ≤ s := by omega
  have h1 := mul_two_pow_hundred_le hs
  have h2 : s ^ 4 ≤ 2 ^ s := pow_four_le_two_pow (by omega)
  have hcoef : cst * 19683 * 2 ^ 18 * s ^ 4 ≤ 2 ^ (3 * s) := by
    calc cst * 19683 * 2 ^ 18 * s ^ 4 = cst * (19683 * 2 ^ 18) * s ^ 4 := by ring
      _ ≤ cst * 2 ^ 100 * s ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by norm_num))
      _ ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul h1 h2
      _ = 2 ^ (2 * s) := by rw [← pow_add]; congr 1; ring
      _ ≤ 2 ^ (3 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold pMu
  calc cst * pT s ^ 2 * Nat.size (pT s) ^ 3 ≤ cst * pT s ^ 2 * (27 * s) ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (size_pT_le hs1) 3)
    _ = cst * 19683 * 2 ^ 18 * s ^ 4 * (s * 2 ^ (32 * s)) := by
        unfold pT
        ring
    _ ≤ 2 ^ (3 * s) * (s * 2 ^ (32 * s)) := Nat.mul_le_mul_right _ hcoef
    _ = s * 2 ^ (35 * s) := by ring

/-- `ζ = 2^(16 s₀ + 8) s₀`. -/
def pZeta (s₀ : ℕ) : ℕ := 2 ^ (16 * s₀ + 8) * s₀

/-- The exponent of the box principle. -/
def pNu (cst γ s₀ : ℕ) : ℕ :=
  3 + 55 * s₀ + pZeta s₀ + (16 * s₀ + 5) * 2 ^ (16 * s₀) + (10 * s₀ + 3 + γ) * 2 ^ (16 * s₀ + 2)
    + pMu cst s₀

theorem deg_le {s₀ s : ℕ} (h1 : 1 ≤ s₀) (hs : s₀ ≤ s) :
    3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s ≤ 2 ^ (16 * s + 2) := by
  rw [Nst_def]
  have a1 : 2 ^ (13 * s₀ + 2) ≤ 2 ^ (16 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have a2 : 2 ^ (16 * s₀) ≤ 2 ^ (16 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : 2 ^ (13 * s₀ + 2) = 4 * 2 ^ (13 * s₀) := by ring
  have e2 : 2 ^ (16 * s + 2) = 4 * 2 ^ (16 * s) := by ring
  rw [e1] at a1
  rw [e2]
  generalize 2 ^ (13 * s₀) = a at *
  generalize 2 ^ (16 * s₀) = b at *
  generalize 2 ^ (16 * s) = c at *
  omega

theorem hTd_ok {s₀ s : ℕ} (h1 : 1 ≤ s₀) (hs : s₀ ≤ s) :
    3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s ≤ pT s := by
  refine (deg_le h1 hs).trans ?_
  unfold pT
  have e : 2 ^ (16 * s + 9) = 128 * 2 ^ (16 * s + 2) := by ring
  have hs1 : 1 ≤ s := by omega
  calc 2 ^ (16 * s + 2) ≤ 2 ^ (16 * s + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 2 ^ (16 * s + 9) * s := Nat.le_mul_of_pos_right _ hs1

theorem lc_pow_eq (s₀ ζ : ℕ) :
    (2 ^ (13 * s₀)) ^ 3 * 2 ^ (16 * s₀) * 2 ^ ζ = 2 ^ (55 * s₀ + ζ) := by
  rw [← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

theorem eight_deg_pow_le {s₀ s : ℕ} (h1 : 1 ≤ s₀) (hs : s₀ ≤ s) :
    (8 * (3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s)) ^ Nst s
      ≤ 2 ^ ((16 * s + 5) * 2 ^ (16 * s)) := by
  have hd := deg_le h1 hs
  have hb : 8 * (3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s) ≤ 2 ^ (16 * s + 5) := by
    have e : 2 ^ (16 * s + 5) = 8 * 2 ^ (16 * s + 2) := by ring
    rw [e]
    exact Nat.mul_le_mul_left 8 hd
  calc _ ≤ (2 ^ (16 * s + 5)) ^ Nst s := Nat.pow_le_pow_left hb _
    _ = 2 ^ ((16 * s + 5) * 2 ^ (16 * s)) := by rw [Nst_def, ← pow_mul]

theorem hTB_ok {s₀ s : ℕ} (h1 : 1 ≤ s₀) (hs : s₀ ≤ s) :
    (8 * (3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s)) ^ Nst s
      * ((2 ^ (13 * s₀)) ^ 3 * 2 ^ (16 * s₀) * 2 ^ pZeta s₀)
      * (3 * (1 + 4 * Hst s)) ^ (3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s) ≤ 2 ^ pT s := by
  have hd := deg_le h1 hs
  have hA := eight_deg_pow_le h1 hs
  have hC : (3 * (1 + 4 * Hst s)) ^ (3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s)
      ≤ 2 ^ ((10 * s + 4) * 2 ^ (16 * s + 2)) := by
    have hb : 3 * (1 + 4 * Hst s) ≤ 2 ^ (10 * s + 4) := by
      rw [Hst_def]
      have : 1 ≤ 2 ^ (10 * s) := Nat.one_le_two_pow
      have e : 2 ^ (10 * s + 4) = 16 * 2 ^ (10 * s) := by ring
      omega
    calc _ ≤ (2 ^ (10 * s + 4)) ^ (3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s) :=
          Nat.pow_le_pow_left hb _
      _ ≤ (2 ^ (10 * s + 4)) ^ 2 ^ (16 * s + 2) := Nat.pow_le_pow_right (by positivity) hd
      _ = _ := by rw [← pow_mul]
  rw [lc_pow_eq]
  calc _ ≤ 2 ^ ((16 * s + 5) * 2 ^ (16 * s)) * 2 ^ (55 * s₀ + pZeta s₀)
        * 2 ^ ((10 * s + 4) * 2 ^ (16 * s + 2)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hA) hC
    _ = 2 ^ ((16 * s + 5) * 2 ^ (16 * s) + (55 * s₀ + pZeta s₀)
        + (10 * s + 4) * 2 ^ (16 * s + 2)) := by rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ pT s := Nat.pow_le_pow_right (by norm_num) ?_
  -- the exponents
  unfold pZeta pT
  set X := 2 ^ (16 * s) with hX
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have e2 : 2 ^ (16 * s + 2) = 4 * X := by rw [hX]; ring
  have e9 : 2 ^ (16 * s + 9) = 512 * X := by rw [hX]; ring
  have e8 : 2 ^ (16 * s₀ + 8) = 256 * 2 ^ (16 * s₀) := by ring
  have hmono : 2 ^ (16 * s₀) * s₀ ≤ X * s :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) hs
  have hsX : s ≤ X * s := Nat.le_mul_of_pos_left _ hX1
  have hXs : X ≤ X * s := Nat.le_mul_of_pos_right _ (by omega)
  rw [e2, e9, e8]
  have e3 : 256 * 2 ^ (16 * s₀) * s₀ = 256 * (2 ^ (16 * s₀) * s₀) := by ring
  rw [e3]
  generalize 2 ^ (16 * s₀) * s₀ = z at *
  have h5 : (16 * s + 5) * X = 16 * (X * s) + 5 * X := by ring
  have h6 : (10 * s + 4) * (4 * X) = 40 * (X * s) + 16 * X := by ring
  have h7 : 512 * X * s = 512 * (X * s) := by ring
  rw [h5, h6, h7]
  generalize X * s = y at *
  omega

theorem hstart_ok {cst γ s₀ : ℕ} (h1 : 1 ≤ s₀) :
    4 * ((2 ^ (13 * s₀)) ^ 3 * 2 ^ (16 * s₀) * 2 ^ pZeta s₀
      * ((8 * (3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s₀)) ^ Nst s₀
        * (7 * Hst s₀ * 2 ^ γ) ^ (3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s₀)))
      * 2 ^ (cst * pT s₀ ^ 2 * Nat.size (pT s₀) ^ 3) < 2 ^ pNu cst γ s₀ := by
  have hd := deg_le h1 (le_refl s₀)
  have hA := eight_deg_pow_le h1 (le_refl s₀)
  have hC : (7 * Hst s₀ * 2 ^ γ) ^ (3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s₀)
      ≤ 2 ^ ((10 * s₀ + 3 + γ) * 2 ^ (16 * s₀ + 2)) := by
    have hb : 7 * Hst s₀ * 2 ^ γ ≤ 2 ^ (10 * s₀ + 3 + γ) := by
      rw [Hst_def]
      have e : 2 ^ (10 * s₀ + 3 + γ) = 8 * 2 ^ (10 * s₀) * 2 ^ γ := by ring
      rw [e]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
    calc _ ≤ (2 ^ (10 * s₀ + 3 + γ)) ^ (3 * 2 ^ (13 * s₀) + 2 ^ (16 * s₀) + Nst s₀) :=
          Nat.pow_le_pow_left hb _
      _ ≤ (2 ^ (10 * s₀ + 3 + γ)) ^ 2 ^ (16 * s₀ + 2) :=
          Nat.pow_le_pow_right (by positivity) hd
      _ = _ := by rw [← pow_mul]
  rw [lc_pow_eq]
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  calc _ ≤ 2 ^ 2 * (2 ^ (55 * s₀ + pZeta s₀) * (2 ^ ((16 * s₀ + 5) * 2 ^ (16 * s₀))
        * 2 ^ ((10 * s₀ + 3 + γ) * 2 ^ (16 * s₀ + 2))))
        * 2 ^ (cst * pT s₀ ^ 2 * Nat.size (pT s₀) ^ 3) := by
        rw [h4]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul hA hC)))
    _ = 2 ^ (2 + (55 * s₀ + pZeta s₀ + ((16 * s₀ + 5) * 2 ^ (16 * s₀)
        + (10 * s₀ + 3 + γ) * 2 ^ (16 * s₀ + 2))) + cst * pT s₀ ^ 2 * Nat.size (pT s₀) ^ 3) := by
        rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ < 2 ^ pNu cst γ s₀ := Nat.pow_lt_pow_right (by norm_num) (by unfold pNu pMu; omega)

theorem hcount_ok {cst γ s₀ : ℕ} (h0 : 100 + cst + γ ≤ s₀) :
    pNu cst γ s₀ * (Nst s₀ * (Hst s₀ * Hst s₀) * 2)
      < pZeta s₀ * ((2 ^ (13 * s₀)) ^ 3 * 2 ^ (16 * s₀)) := by
  have e1 : Nst s₀ * (Hst s₀ * Hst s₀) * 2 = 2 ^ (36 * s₀ + 1) := by
    rw [Nst_def, Hst_def]
    ring
  have e2 : pZeta s₀ * ((2 ^ (13 * s₀)) ^ 3 * 2 ^ (16 * s₀))
      = 2 ^ (35 * s₀ + 7) * s₀ * 2 ^ (36 * s₀ + 1) := by
    unfold pZeta
    ring
  rw [e1, e2]
  refine Nat.mul_lt_mul_of_pos_right ?_ (by positivity)
  have hμ : pMu cst s₀ ≤ s₀ * 2 ^ (35 * s₀) := pMu_le (by omega)
  unfold pNu pZeta
  set X := 2 ^ (16 * s₀) with hX
  set W := 2 ^ (35 * s₀) with hW
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have hXW : 1024 * X ≤ W := by
    have e : 1024 * X = 2 ^ (16 * s₀ + 10) := by rw [hX]; ring
    rw [e]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2' : 2 ^ (16 * s₀ + 2) = 4 * X := by rw [hX]; ring
  have e8 : 2 ^ (16 * s₀ + 8) = 256 * X := by rw [hX]; ring
  have e7 : 2 ^ (35 * s₀ + 7) = 128 * W := by rw [hW]; ring
  rw [e2', e8, e7]
  have hγX : γ * X ≤ s₀ * X := Nat.mul_le_mul_right _ (by omega)
  have hsX : s₀ ≤ s₀ * X := Nat.le_mul_of_pos_right _ hX1
  have hXs : 100 * X ≤ s₀ * X := Nat.mul_le_mul_right _ (by omega)
  have hsXW : 1024 * (s₀ * X) ≤ s₀ * W := by
    calc 1024 * (s₀ * X) = s₀ * (1024 * X) := by ring
      _ ≤ s₀ * W := Nat.mul_le_mul_left _ hXW
  have a1 : 256 * X * s₀ = 256 * (s₀ * X) := by ring
  have a2 : (16 * s₀ + 5) * X = 16 * (s₀ * X) + 5 * X := by ring
  have a3 : (10 * s₀ + 3 + γ) * (4 * X) = 40 * (s₀ * X) + 12 * X + 4 * (γ * X) := by ring
  have a4 : 128 * W * s₀ = 128 * (s₀ * W) := by ring
  rw [a1, a2, a3, a4]
  generalize s₀ * X = p at *
  generalize s₀ * W = r at *
  generalize γ * X = g at *
  generalize pMu cst s₀ = μ at *
  omega

theorem Ghat_le (γ s₀ s : ℕ) :
    Ghat γ (2 ^ (13 * s₀)) (2 ^ (16 * s₀)) (pZeta s₀) s
      ≤ 2 ^ ((11 * s + 19) * (2 ^ (22 * s + 34) * 2 ^ (13 * s₀))
        + (55 * s₀ + pZeta s₀ + γ * 2 ^ (16 * s₀)) + (22 * s + 32 + 2 * γ) * 2 ^ (13 * s₀)) := by
  rw [Ghat_def]
  have hK : Kst s = 2 ^ (11 * s + 14) := by
    rw [Kst_def, Hst_def]
    ring
  rw [hK]
  set K := 2 ^ (11 * s + 14) with hKdef
  set Lc := 2 ^ (13 * s₀) with hLc
  have hK1 : 1 ≤ K := Nat.one_le_two_pow
  have hL1 : 1 ≤ Lc := Nat.one_le_two_pow
  have f1 : 16 * K + 4 ≤ 2 ^ (11 * s + 19) := by
    have e : 2 ^ (11 * s + 19) = 32 * K := by rw [hKdef]; ring
    omega
  have f2 : (2 * K + 1) ^ 2 * (3 * Lc) ≤ 2 ^ (22 * s + 34) * Lc := by
    calc (2 * K + 1) ^ 2 * (3 * Lc) ≤ (4 * K) ^ 2 * (4 * Lc) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (by omega)
      _ = 2 ^ (22 * s + 34) * Lc := by rw [hKdef]; ring
  have hfirst : (16 * K + 4) ^ ((2 * K + 1) ^ 2 * (3 * Lc))
      ≤ 2 ^ ((11 * s + 19) * (2 ^ (22 * s + 34) * Lc)) := by
    calc _ ≤ (2 ^ (11 * s + 19)) ^ ((2 * K + 1) ^ 2 * (3 * Lc)) := Nat.pow_le_pow_left f1 _
      _ ≤ (2 ^ (11 * s + 19)) ^ (2 ^ (22 * s + 34) * Lc) :=
          Nat.pow_le_pow_right (by positivity) f2
      _ = _ := by rw [← pow_mul]
  have f3 : Lc ^ 3 * (2 ^ (16 * s₀) * (2 ^ pZeta s₀ * (2 ^ γ) ^ 2 ^ (16 * s₀)))
      = 2 ^ (55 * s₀ + pZeta s₀ + γ * 2 ^ (16 * s₀)) := by
    have hJ : (2 ^ γ) ^ 2 ^ (16 * s₀) = 2 ^ (γ * 2 ^ (16 * s₀)) := (pow_mul 2 γ _).symm
    rw [hJ, hLc, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  have f4 : ((4 * K + 2) * 2 ^ γ * (2 ^ γ * (K + 1))) ^ Lc
      ≤ 2 ^ ((22 * s + 32 + 2 * γ) * Lc) := by
    have hb : (4 * K + 2) * 2 ^ γ * (2 ^ γ * (K + 1)) ≤ 2 ^ (22 * s + 32 + 2 * γ) := by
      calc (4 * K + 2) * 2 ^ γ * (2 ^ γ * (K + 1)) ≤ (8 * K) * 2 ^ γ * (2 ^ γ * (2 * K)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega))
              (Nat.mul_le_mul_left _ (by omega))
        _ = 2 ^ (22 * s + 32 + 2 * γ) := by rw [hKdef]; ring
    calc _ ≤ (2 ^ (22 * s + 32 + 2 * γ)) ^ Lc := Nat.pow_le_pow_left hb _
      _ = _ := by rw [← pow_mul]
  calc (16 * K + 4) ^ ((2 * K + 1) ^ 2 * (3 * Lc))
        * (Lc ^ 3 * (2 ^ (16 * s₀) * (2 ^ pZeta s₀ * (2 ^ γ) ^ 2 ^ (16 * s₀))
          * ((4 * K + 2) * 2 ^ γ * (2 ^ γ * (K + 1))) ^ Lc))
      = (16 * K + 4) ^ ((2 * K + 1) ^ 2 * (3 * Lc))
        * (Lc ^ 3 * (2 ^ (16 * s₀) * (2 ^ pZeta s₀ * (2 ^ γ) ^ 2 ^ (16 * s₀))))
          * ((4 * K + 2) * 2 ^ γ * (2 ^ γ * (K + 1))) ^ Lc := by ring
    _ ≤ 2 ^ ((11 * s + 19) * (2 ^ (22 * s + 34) * Lc))
        * 2 ^ (55 * s₀ + pZeta s₀ + γ * 2 ^ (16 * s₀)) * 2 ^ ((22 * s + 32 + 2 * γ) * Lc) :=
        Nat.mul_le_mul (Nat.mul_le_mul hfirst (le_of_eq f3)) f4
    _ = _ := by rw [← pow_add, ← pow_add]

theorem two_pow_pow_mul_eight_pow (a n : ℕ) : (2 ^ a) ^ n * 8 ^ n = 2 ^ ((a + 3) * n) := by
  have h8 : (8 : ℕ) ^ n = 2 ^ (3 * n) := by
    rw [pow_mul]
    norm_num
  rw [h8, ← pow_mul, ← pow_add]
  congr 1
  ring

theorem hstep_ok {cst γ s₀ s : ℕ} (h0 : 100 + cst + γ ≤ s₀) (hs : s₀ ≤ s) :
    Nst (s + 1) ^ Nst (s + 1) * 8 ^ Nst (s + 1)
      * Ghat γ (2 ^ (13 * s₀)) (2 ^ (16 * s₀)) (pZeta s₀) s
      * 2 ^ (cst * pT (s + 1) ^ 2 * Nat.size (pT (s + 1)) ^ 3)
      < 2 ^ (s * (Nst s * Hst s ^ 2)) := by
  have hN : Nst (s + 1) ^ Nst (s + 1) * 8 ^ Nst (s + 1)
      = 2 ^ ((16 * (s + 1) + 3) * 2 ^ (16 * (s + 1))) := by
    rw [Nst_def]
    exact two_pow_pow_mul_eight_pow _ _
  rw [hN]
  have hG := Ghat_le γ s₀ s
  have hT : Nst s * Hst s ^ 2 = 2 ^ s * 2 ^ (35 * s) := by
    rw [Nst_def, Hst_def]
    ring
  rw [hT]
  calc _ ≤ 2 ^ ((16 * (s + 1) + 3) * 2 ^ (16 * (s + 1)))
        * 2 ^ ((11 * s + 19) * (2 ^ (22 * s + 34) * 2 ^ (13 * s₀))
          + (55 * s₀ + pZeta s₀ + γ * 2 ^ (16 * s₀)) + (22 * s + 32 + 2 * γ) * 2 ^ (13 * s₀))
        * 2 ^ (cst * pT (s + 1) ^ 2 * Nat.size (pT (s + 1)) ^ 3) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hG)
    _ = 2 ^ ((16 * (s + 1) + 3) * 2 ^ (16 * (s + 1))
        + ((11 * s + 19) * (2 ^ (22 * s + 34) * 2 ^ (13 * s₀))
          + (55 * s₀ + pZeta s₀ + γ * 2 ^ (16 * s₀)) + (22 * s + 32 + 2 * γ) * 2 ^ (13 * s₀))
        + cst * pT (s + 1) ^ 2 * Nat.size (pT (s + 1)) ^ 3) := by rw [← pow_add, ← pow_add]
    _ < 2 ^ (s * (2 ^ s * 2 ^ (35 * s))) := Nat.pow_lt_pow_right (by norm_num) ?_
  -- the exponents
  set W := 2 ^ (35 * s) with hW
  set E := 2 ^ s with hE
  have hW1 : 1 ≤ W := Nat.one_le_two_pow
  have hn' : 2 ^ (16 * (s + 1)) ≤ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLW : 2 ^ (22 * s + 34) * 2 ^ (13 * s₀) ≤ 17179869184 * W := by
    have e : (17179869184 : ℕ) * W = 2 ^ (34 + 35 * s) := by rw [hW, pow_add]; norm_num
    rw [e, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hJ : 2 ^ (16 * s₀) ≤ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hL : 2 ^ (13 * s₀) ≤ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hζ : pZeta s₀ ≤ s * W := by
    unfold pZeta
    rw [mul_comm]
    exact Nat.mul_le_mul hs (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hμ : cst * pT (s + 1) ^ 2 * Nat.size (pT (s + 1)) ^ 3 ≤ 68719476736 * (s * W) := by
    have h := pMu_le (cst := cst) (s := s + 1) (by omega)
    unfold pMu at h
    refine h.trans ?_
    have e : 2 ^ (35 * (s + 1)) = 34359738368 * W := by rw [hW]; ring
    rw [e]
    have hs1 : s + 1 ≤ 2 * s := by omega
    calc (s + 1) * (34359738368 * W) ≤ 2 * s * (34359738368 * W) := Nat.mul_le_mul_right _ hs1
      _ = 68719476736 * (s * W) := by ring
  have hE40 : 1099511627776 ≤ E := by
    have : (1099511627776 : ℕ) = 2 ^ 40 := by norm_num
    rw [this]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have t1 : (16 * (s + 1) + 3) * 2 ^ (16 * (s + 1)) ≤ 16 * (s * W) + 19 * W := by
    calc _ ≤ (16 * (s + 1) + 3) * W := Nat.mul_le_mul_left _ hn'
      _ = 16 * (s * W) + 19 * W := by ring
  have t2 : (11 * s + 19) * (2 ^ (22 * s + 34) * 2 ^ (13 * s₀))
      ≤ 188978561024 * (s * W) + 326417514496 * W := by
    calc _ ≤ (11 * s + 19) * (17179869184 * W) := Nat.mul_le_mul_left _ hLW
      _ = 188978561024 * (s * W) + 326417514496 * W := by ring
  have hγW : γ * W ≤ s * W := Nat.mul_le_mul_right _ (by omega)
  have t5 : γ * 2 ^ (16 * s₀) ≤ s * W := Nat.mul_le_mul (by omega) hJ
  have t6 : (22 * s + 32 + 2 * γ) * 2 ^ (13 * s₀) ≤ 24 * (s * W) + 32 * W := by
    calc _ ≤ (22 * s + 32 + 2 * γ) * W := Nat.mul_le_mul_left _ hL
      _ = 22 * (s * W) + 32 * W + 2 * (γ * W) := by ring
      _ ≤ 24 * (s * W) + 32 * W := by omega
  have hWs : W ≤ s * W := Nat.le_mul_of_pos_left _ (by omega)
  have hsW : s ≤ s * W := Nat.le_mul_of_pos_right _ hW1
  have hfin : 1099511627776 * (s * W) ≤ s * (E * W) := by
    calc 1099511627776 * (s * W) ≤ E * (s * W) := Nat.mul_le_mul_right _ hE40
      _ = s * (E * W) := by ring
  generalize s * W = p at *
  generalize s * (E * W) = tgt at *
  generalize 2 ^ (16 * (s + 1)) = n' at *
  generalize 2 ^ (22 * s + 34) * 2 ^ (13 * s₀) = q at *
  generalize 2 ^ (16 * s₀) = j at *
  generalize 2 ^ (13 * s₀) = l at *
  generalize cst * pT (s + 1) ^ 2 * Nat.size (pT (s + 1)) ^ 3 = μ at *
  generalize pZeta s₀ = z at *
  generalize (16 * (s + 1) + 3) * n' = a1 at *
  generalize (11 * s + 19) * q = a2 at *
  generalize (22 * s + 32 + 2 * γ) * l = a6 at *
  generalize γ * j = a5 at *
  omega

/-- **The parameters exist.** -/
theorem exists_params (cst γ : ℕ) : Nonempty (Params cst γ) := by
  set s₀ := 100 + cst + γ with hs₀
  have h1 : 1 ≤ s₀ := by omega
  exact ⟨{
    s₀ := s₀
    Lc := 2 ^ (13 * s₀)
    J := 2 ^ (16 * s₀)
    ζ := pZeta s₀
    ν := pNu cst γ s₀
    T := pT
    hcount := hcount_ok le_rfl
    hstart := hstart_ok h1
    hTd := fun s hs => hTd_ok h1 hs
    hTB := fun s hs => hTB_ok h1 hs
    hstep := fun s hs => hstep_ok le_rfl hs }⟩

end Azurite.Chudnovsky
