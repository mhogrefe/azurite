/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# DLMF §3.11(iii), Example: exact rational data

Rational data and kernel-checked (`decide +kernel`) inequalities for the certification of
Table 3.11.1 in `Section11RationalExample.lean`: the coefficients of `R₃,₃`, the truncated `J₀`
series (`aL`, degree `≤ 26`), the numerator `S = P − QA` (`sL`), a cubic competitor (`cQ`, `gL`),
values of polynomials and their derivatives at rational points (`evQ`), coefficient bounds for
third derivatives (`absSumQ`), and the cell checks.
-/

namespace Azurite.DLMF

/-- Table 3.11.1: `p_j`. -/
def pR33 : ℕ → ℚ
  | 0 => 99999998917854 / 10 ^ 14
  | 1 => -34038938209347 / 10 ^ 14
  | 2 => -18915483763222 / 10 ^ 14
  | 3 => 6658319420166 / 10 ^ 14
  | _ => 0

/-- Table 3.11.1: `q_j` (`q₀ = 1`). -/
def qQ : ℕ → ℚ
  | 0 => 1
  | 1 => -34039052338838 / 10 ^ 14
  | 2 => 6086501629812 / 10 ^ 14
  | 3 => -1864476809090 / 10 ^ 14
  | _ => 0

/-- A cubic competitor on `[0, 2.41]`. -/
def cQ : ℕ → ℚ
  | 0 => 9975 / 10 ^ 4
  | 1 => 336 / 10 ^ 4
  | 2 => -3249 / 10 ^ 4
  | 3 => 575 / 10 ^ 4
  | _ => 0

/-- Coefficients of `∑_{j<14} (−1)^j (x/2)^{2j}/(j!)²` (literal). -/
def aL : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | 2 => -1 / 4
  | 3 => 0
  | 4 => 1 / 64
  | 5 => 0
  | 6 => -1 / 2304
  | 7 => 0
  | 8 => 1 / 147456
  | 9 => 0
  | 10 => -1 / 14745600
  | 11 => 0
  | 12 => 1 / 2123366400
  | 13 => 0
  | 14 => -1 / 416179814400
  | 15 => 0
  | 16 => 1 / 106542032486400
  | 17 => 0
  | 18 => -1 / 34519618525593600
  | 19 => 0
  | 20 => 1 / 13807847410237440000
  | 21 => 0
  | 22 => -1 / 6682998146554920960000
  | 23 => 0
  | 24 => 1 / 3849406932415634472960000
  | 25 => 0
  | 26 => -1 / 2602199086312968903720960000
  | 27 => 0
  | _ => 0

/-- Coefficients of `S = P − QA` (literal). -/
def sL : ℕ → ℚ
  | 0 => -541073 / 50000000000000
  | 1 => 114129491 / 100000000000000
  | 2 => -992696517 / 50000000000000
  | 3 => 26066289093 / 200000000000000
  | 4 => -40874592547 / 100000000000000
  | 5 => 2103711696699 / 3200000000000000
  | 6 => -7444628667077 / 14400000000000000
  | 7 => 16541056394201 / 115200000000000000
  | 8 => 1131000407453 / 57600000000000000
  | 9 => -14214577240487 / 2457600000000000000
  | 10 => -1271625407453 / 3686400000000000000
  | 11 => 25401438095027 / 245760000000000000000
  | 12 => 12132128667077 / 3317760000000000000000
  | 13 => -117222804085061 / 106168320000000000000000
  | 14 => -68309644965197 / 2601123840000000000000000
  | 15 => 55233067040467 / 6936330240000000000000000
  | 16 => 1423969157453 / 10404495360000000000000000
  | 17 => -24625945043789 / 591900180480000000000000000
  | 18 => -117001658003693 / 215747615784960000000000000000
  | 19 => 285025716903161 / 1725980926279680000000000000000
  | 20 => 208446486779 / 123284351877120000000000000000
  | 21 => -13180586505503 / 25570087796736000000000000000000
  | 22 => -25409524900259 / 5966962630852608000000000000000000
  | 23 => 144727953876787 / 111383302442582016000000000000000000
  | 24 => 13304003667077 / 1503674582974857216000000000000000000
  | 25 => -519949794848501 / 192470346620781723648000000000000000000
  | 26 => -250904693859557 / 16263744289456055648256000000000000000000
  | 27 => 204391211767667 / 43369984771882815062016000000000000000000
  | 28 => 169069489717 / 7228330795313802510336000000000000000000
  | 29 => -26635382987 / 3717427266161384148172800000000000000000
  | _ => 0

/-- Coefficients of `competitor − A` (literal). -/
def gL : ℕ → ℚ
  | 0 => -1 / 400
  | 1 => 21 / 625
  | 2 => -749 / 10000
  | 3 => 23 / 400
  | 4 => -1 / 64
  | 5 => 0
  | 6 => 1 / 2304
  | 7 => 0
  | 8 => -1 / 147456
  | 9 => 0
  | 10 => 1 / 14745600
  | 11 => 0
  | 12 => -1 / 2123366400
  | 13 => 0
  | 14 => 1 / 416179814400
  | 15 => 0
  | 16 => -1 / 106542032486400
  | 17 => 0
  | 18 => 1 / 34519618525593600
  | 19 => 0
  | 20 => -1 / 13807847410237440000
  | 21 => 0
  | 22 => 1 / 6682998146554920960000
  | 23 => 0
  | 24 => -1 / 3849406932415634472960000
  | 25 => 0
  | 26 => 1 / 2602199086312968903720960000
  | 27 => 0
  | _ => 0

/-- The coefficients of the `k`th derivative of `∑_{n<N} c_n x^n`. -/
def dcoeffQ (c : ℕ → ℚ) (N k m : ℕ) : ℚ :=
  if m + k < N then ((m + k).descFactorial k : ℚ) * c (m + k) else 0

/-- The `k`th derivative at `x` of `∑_{n<N} c_n x^n`. -/
def evQ (c : ℕ → ℚ) (N k : ℕ) (x : ℚ) : ℚ :=
  ∑ m ∈ Finset.range N, dcoeffQ c N k m * x ^ m

theorem evQ_eq (c : ℕ → ℚ) (N k : ℕ) (x : ℚ) :
    evQ c N k x = ∑ m ∈ Finset.range N, dcoeffQ c N k m * x ^ m := rfl

/-- `∑_m |coefficient of the kth derivative| R^m`. -/
def absSumQ (c : ℕ → ℚ) (N k : ℕ) (R : ℚ) : ℚ :=
  ∑ m ∈ Finset.range N, |dcoeffQ c N k m| * R ^ m

/-- The tables agree with their definitions. -/
theorem aL_eq : (List.range 14).all (fun j => decide (aL (2 * j) = (-1) ^ j /
    (4 ^ j * ((j.factorial ^ 2 : ℕ) : ℚ)) ∧ aL (2 * j + 1) = 0)) = true := by decide +kernel

theorem sL_eq : (List.range 31).all (fun n => decide (sL n = (if n < 4 then pR33 n else 0) -
    ∑ k ∈ Finset.range (n + 1), (if k < 4 then qQ k else 0) *
      (if n - k < 28 then aL (n - k) else 0))) = true := by decide +kernel

theorem gL_eq : (List.range 28).all (fun n => decide (gL n = (if n < 4 then cQ n else 0) - aL n)) =
    true := by decide +kernel

/-- The second-order cell bound `|G(c)| + δ(|G′(c)| + δ(|G″(c)| + δL₃))`. -/
def cellBoundQ (c : ℕ → ℚ) (N : ℕ) (L3 x δ : ℚ) : ℚ :=
  |evQ c N 0 x| + δ * (|evQ c N 1 x| + δ * (|evQ c N 2 x| + δ * L3))

/-- The truncation bound for `J₀`. -/
def tauQ : ℚ := 1 / 10 ^ 17

/-- The right end of the interval, `0.89357…`. -/
def b0Q : ℚ := 8935769663 / 10 ^ 10

def L3S : ℚ := absSumQ sL 31 3 1

theorem L3S_le : L3S ≤ 16 / 100 := by decide +kernel

/-- The upper-bound cells for `S` on `[0, 0.893]`. -/
def cellS (i : ℕ) : Bool :=
  decide (cellBoundQ sL 31 (16 / 100) ((2 * i + 1) / 2000) (1 / 2000) ≤
    (109 / 10 ^ 10 - tauQ) * evQ qQ 4 0 ((2 * i + 1) / 2000 + 1 / 2000))

theorem cellS_all : (List.range 893).all cellS = true := by decide +kernel

/-- The last cell `[0.893, b₀]`. -/
theorem cellS_last : cellBoundQ sL 31 (16 / 100) ((893 / 1000 + b0Q) / 2) ((b0Q - 893 / 1000) / 2) ≤
    (109 / 10 ^ 10 - tauQ) * evQ qQ 4 0 b0Q := by decide +kernel

/-- The error `R − A` at a rational point. -/
def errR33 (x : ℚ) : ℚ := evQ pR33 4 0 x / evQ qQ 4 0 x - evQ aL 28 0 x

/-- The alternation points. -/
def altPt : ℕ → ℚ
  | 0 => 0
  | 1 => 461 / 10 ^ 4
  | 2 => 174 / 10 ^ 3
  | 3 => 3561 / 10 ^ 4
  | 4 => 5547 / 10 ^ 4
  | 5 => 7307 / 10 ^ 4
  | 6 => 851 / 10 ^ 3
  | _ => b0Q

theorem altPt_check : (List.range 8).all (fun j =>
    decide (10821 / 10 ^ 12 + tauQ ≤ -((-1) ^ j * errR33 (altPt j)))) = true := by decide +kernel

theorem altPt_mono : (List.range 7).all (fun j => decide (altPt j < altPt (j + 1))) = true := by
  decide +kernel

theorem altPt_mem : (List.range 8).all (fun j => decide (0 ≤ altPt j ∧ altPt j ≤ b0Q)) = true := by
  decide +kernel

def L3A : ℚ := absSumQ aL 28 3 (12 / 5)

theorem L3A_le : L3A ≤ 2 := by decide +kernel

/-- `J₀ > 0` on `[0, 2.4]`: lower bounds on cells. -/
def cellA (i : ℕ) : Bool :=
  decide (tauQ < evQ aL 28 0 ((2 * i + 1) / 500) -
    (1 / 500) * (|evQ aL 28 1 ((2 * i + 1) / 500)| + (1 / 500) *
      (|evQ aL 28 2 ((2 * i + 1) / 500)| + (1 / 500) * 2)))

theorem cellA_all : (List.range 600).all cellA = true := by decide +kernel

theorem A_241_neg : evQ aL 28 0 (241 / 100) + tauQ < 0 := by decide +kernel

theorem err_24 : 1 / 25 + tauQ ≤ errR33 (12 / 5) := by decide +kernel

def L3G : ℚ := absSumQ gL 28 3 (5 / 2)

theorem L3G_le : L3G ≤ 5 / 2 := by decide +kernel

/-- The competitor is within `0.01` of `J₀` on `[0, 2.41]`. -/
def cellG (i : ℕ) : Bool :=
  decide (cellBoundQ gL 28 (5 / 2) ((2 * i + 1) / 200) (1 / 200) ≤ 1 / 100 - tauQ)

theorem cellG_all : (List.range 241).all cellG = true := by decide +kernel

end Azurite.DLMF
