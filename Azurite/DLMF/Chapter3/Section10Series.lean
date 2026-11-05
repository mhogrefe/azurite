/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section10
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# DLMF §3.10(ii): Relations to power series

* 3.10.3–3.10.5 (`eulerA`, `eulerB`, `dlmf_3_10_4`): if no `uₙ` vanishes, the continued fraction
  with `b₀ = u₀`, `b₁ = 1`, `a₁ = u₁`, `bₙ = 1 + uₙ/u_{n−1}`, `aₙ = −uₙ/u_{n−1}` has
  `Bₙ = 1` and `Aₙ = u₀ + ⋯ + uₙ`, so `Cₙ = Aₙ/Bₙ` is the `n`th partial sum.
* **Erratum** ("Every convergent, asymptotic, or formal series … can be converted into a
  continued fraction … with `Aₙ/Bₙ = u₀ + ⋯ + uₙ`"): impossible when some `uₙ` (`n ≥ 1`)
  vanishes, because consecutive convergents of a continued fraction with `aₙ ≠ 0` differ
  (determinant formula 1.12.7) (`dlmf_3_10_ii_erratum`).
* 3.10.6 (`sfA`, `sfB`, `sNum`, `sDen`): Stieltjes fractions `a₀/(1 − a₁z/(1 − a₂z/(1 − ⋯)))`,
  with the numerator and denominator polynomials of their convergents.
* 3.10.7 (`SCorresponds`): correspondence with a formal power series `f`: the expansion of `Cₙ`
  agrees with `f` up to `z^{n−1}`.
* 3.10.8–3.10.10 (`qdTable`, `qdE`, `qdQ`, `qdCoeff`): the quotient-difference algorithm, the
  rhombus rules (`dlmf_3_10_8`, `dlmf_3_10_9`), and the coefficients 3.10.10.
* 3.10.11 (`jfA`, `jfB`, `jNum`, `jDen`, `JAssociated`): Jacobi fractions and association.
* "For the same function `f(z)`, the convergent `Cₙ` of the Jacobi fraction equals the convergent
  `C_{2n}` of the Stieltjes fraction" (`dlmf_3_10_11_contraction`, `sCorresponds_jAssociated`):
  with `β₀ = a₀`, `α₀ = a₁`, `αₙ = a_{2n} + a_{2n+1}`, `βₙ = a_{2n−1}a_{2n}` (even contraction),
  the numerator and denominator polynomials coincide, so an `S`-fraction corresponding to `f`
  gives a `J`-fraction associated with `f`.
-/

open Filter Topology Finset Polynomial

namespace Azurite.DLMF

/-! ### 3.10.4–3.10.5 -/

section Euler

variable {K : Type*} [Field K]

/-- **DLMF 3.10.5**: `b₀ = u₀`, `b₁ = 1`, `bₙ = 1 + uₙ/u_{n−1}` (`n ≥ 2`). -/
def eulerB (u : ℕ → K) : ℕ → K
  | 0 => u 0
  | 1 => 1
  | n + 2 => 1 + u (n + 2) / u (n + 1)

/-- **DLMF 3.10.5**: `a₁ = u₁`, `aₙ = −uₙ/u_{n−1}` (`n ≥ 2`). -/
def eulerA (u : ℕ → K) : ℕ → K
  | 0 => 0
  | 1 => u 1
  | n + 2 => -(u (n + 2) / u (n + 1))

theorem eulerA_ne_zero {u : ℕ → K} (hu : ∀ n, 1 ≤ n → u n ≠ 0) : IsCF (eulerA u) := by
  intro n hn
  rcases n with _ | _ | n
  · omega
  · exact hu 1 le_rfl
  · simp only [eulerA, neg_ne_zero]
    exact div_ne_zero (hu _ (by omega)) (hu _ (by omega))

/-- **DLMF 3.10.4**: with 3.10.5, `Bₙ = 1` and `Aₙ = u₀ + u₁ + ⋯ + uₙ`; hence
`Aₙ/Bₙ = u₀ + ⋯ + uₙ`. -/
theorem dlmf_3_10_4 {u : ℕ → K} (hu : ∀ n, 1 ≤ n → u n ≠ 0) (n : ℕ) :
    cfB (eulerA u) (eulerB u) n = 1 ∧
      cfA (eulerA u) (eulerB u) n = ∑ k ∈ range (n + 1), u k ∧
      cfA (eulerA u) (eulerB u) n / cfB (eulerA u) (eulerB u) n = ∑ k ∈ range (n + 1), u k := by
  have key : ∀ n, cfP (eulerA u) (eulerB u) (n + 2) = ∑ k ∈ range (n + 2), u k ∧
      cfP (eulerA u) (eulerB u) (n + 1) = ∑ k ∈ range (n + 1), u k ∧
      cfQ (eulerA u) (eulerB u) (n + 2) = 1 ∧ cfQ (eulerA u) (eulerB u) (n + 1) = 1 := by
    intro n
    induction n with
    | zero => simp [cfP, cfQ, eulerA, eulerB, sum_range_succ]
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have hn : u (n + 1) ≠ 0 := hu _ (by omega)
      refine ⟨?_, h1, ?_, h3⟩
      · rw [show n + 1 + 2 = (n + 1) + 2 from rfl, cfP, h1, h2]
        simp only [eulerA, eulerB]
        rw [sum_range_succ _ (n + 2), sum_range_succ _ (n + 1)]
        field_simp
        ring
      · rw [show n + 1 + 2 = (n + 1) + 2 from rfl, cfQ, h3, h4]
        simp only [eulerA, eulerB]
        ring
  obtain ⟨-, hA, -, hB⟩ := key n
  refine ⟨hB, hA, ?_⟩
  rw [show cfA (eulerA u) (eulerB u) n = cfP (eulerA u) (eulerB u) (n + 1) from rfl,
    show cfB (eulerA u) (eulerB u) n = cfQ (eulerA u) (eulerB u) (n + 1) from rfl, hA, hB,
    div_one]

/-- **Erratum**: if `u_{n+1} = 0`, no continued fraction with `aₖ ≠ 0` has convergents
`Aₙ/Bₙ`, `A_{n+1}/B_{n+1}` (with `Bₙ, B_{n+1} ≠ 0`) equal to the partial sums
`u₀ + ⋯ + uₙ`, `u₀ + ⋯ + u_{n+1}`: by 1.12.7, `A_{n+1}Bₙ − B_{n+1}Aₙ = ±a₁⋯a_{n+1} ≠ 0`. -/
theorem dlmf_3_10_ii_erratum {u : ℕ → K} {n : ℕ} (hu : u (n + 1) = 0) :
    ¬ ∃ a b : ℕ → K, IsCF a ∧ cfB a b n ≠ 0 ∧ cfB a b (n + 1) ≠ 0 ∧
      cfA a b n / cfB a b n = ∑ k ∈ range (n + 1), u k ∧
      cfA a b (n + 1) / cfB a b (n + 1) = ∑ k ∈ range (n + 2), u k := by
  rintro ⟨a, b, ha, hB0, hB1, h0, h1⟩
  rw [sum_range_succ, hu, add_zero, ← h0] at h1
  have hdet := dlmf_1_12_7 a b (n + 1)
  have hprod : ∏ k ∈ Icc 1 (n + 1), a k ≠ 0 :=
    prod_ne_zero_iff.mpr fun k hk => ha k (mem_Icc.mp hk).1
  rw [div_eq_div_iff hB1 hB0] at h1
  have : cfA a b (n + 1) * cfQ a b (n + 1) - cfB a b (n + 1) * cfP a b (n + 1) = 0 := by
    show cfA a b (n + 1) * cfB a b n - cfB a b (n + 1) * cfA a b n = 0
    linear_combination h1
  rw [this] at hdet
  exact hprod (by
    have := hdet.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h)

end Euler

/-! ### Continued fractions of polynomials -/

section Poly

variable {R : Type*} [CommRing R]

/-- `pcfP a b k = A_{k−1}` (1.12.5–1.12.6) over a commutative ring. -/
def pcfP (a b : ℕ → R) : ℕ → R
  | 0 => 1
  | 1 => b 0
  | k + 2 => b (k + 1) * pcfP a b (k + 1) + a (k + 1) * pcfP a b k

/-- `pcfQ a b k = B_{k−1}` over a commutative ring. -/
def pcfQ (a b : ℕ → R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | k + 2 => b (k + 1) * pcfQ a b (k + 1) + a (k + 1) * pcfQ a b k

theorem pcfP_eq_cfP {K : Type*} [Field K] (a b : ℕ → K) (k : ℕ) : pcfP a b k = cfP a b k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · rfl
    · rfl
    · rw [pcfP, cfP, ih _ (by omega), ih _ (by omega)]

theorem pcfQ_eq_cfQ {K : Type*} [Field K] (a b : ℕ → K) (k : ℕ) : pcfQ a b k = cfQ a b k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · rfl
    · rfl
    · rw [pcfQ, cfQ, ih _ (by omega), ih _ (by omega)]

end Poly

/-! ### Stieltjes fractions -/

section SFrac

variable {𝕜 : Type*} [Field 𝕜]

/-- **DLMF 3.10.6**: the partial numerators of `a₀/(1 − a₁z/(1 − a₂z/(1 − ⋯)))`:
`a₀` and then `−a_m z`. -/
noncomputable def sfA (a : ℕ → 𝕜) : ℕ → 𝕜[X]
  | 0 => 0
  | 1 => C (a 0)
  | m + 2 => -(C (a (m + 1)) * X)

/-- The partial denominators `b₀ = 0`, `b_m = 1`. -/
noncomputable def sfB : ℕ → 𝕜[X]
  | 0 => 0
  | _ + 1 => 1

/-- The numerator `Aₙ(z)` of the `n`th convergent of 3.10.6. -/
noncomputable def sNum (a : ℕ → 𝕜) (n : ℕ) : 𝕜[X] := pcfP (sfA a) sfB (n + 1)

/-- The denominator `Bₙ(z)` of the `n`th convergent of 3.10.6. -/
noncomputable def sDen (a : ℕ → 𝕜) (n : ℕ) : 𝕜[X] := pcfQ (sfA a) sfB (n + 1)

theorem sDen_coeff_zero (a : ℕ → 𝕜) (n : ℕ) : (sDen a n).coeff 0 = 1 := by
  have : ∀ k, (pcfQ (sfA a) sfB (k + 1)).coeff 0 = 1 ∧
      (pcfQ (sfA a) sfB (k + 2)).coeff 0 = 1 := by
    intro k
    induction k with
    | zero => simp [pcfQ, sfA, sfB]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 2 = (k + 1) + 2 from rfl, pcfQ]
      simp [sfA, sfB, ih.2, coeff_add, coeff_neg]
  exact (this n).1

/-- **DLMF 3.10.7**: the `S`-fraction corresponds to the formal power series `f` if the expansion
of `Cₙ = Aₙ/Bₙ` in ascending powers of `z` agrees with `f` up to and including `z^{n−1}`. -/
def SCorresponds (a : ℕ → 𝕜) (f : PowerSeries 𝕜) : Prop :=
  ∀ n, 1 ≤ n → ∀ i < n,
    PowerSeries.coeff i ((sNum a n : PowerSeries 𝕜) * (sDen a n : PowerSeries 𝕜)⁻¹) =
      PowerSeries.coeff i f

end SFrac

/-! ### The quotient-difference algorithm -/

section QD

variable {𝕜 : Type*} [Field 𝕜]

/-- The `j`th column pair of Table 3.10.1: `(k ↦ e_j^k, k ↦ q_{j+1}^k)`, built by 3.10.8 and the
rhombus rules 3.10.9. -/
def qdTable (c : ℕ → 𝕜) : ℕ → (ℕ → 𝕜) × (ℕ → 𝕜)
  | 0 => (fun _ => 0, fun k => c (k + 1) / c k)
  | j + 1 =>
    let e : ℕ → 𝕜 := fun k => (qdTable c j).1 (k + 1) + (qdTable c j).2 (k + 1) -
      (qdTable c j).2 k
    (e, fun k => (qdTable c j).2 (k + 1) * e (k + 1) / e k)

/-- `e_j^k`. -/
def qdE (c : ℕ → 𝕜) (j k : ℕ) : 𝕜 := (qdTable c j).1 k

/-- `q_j^k` (`j ≥ 1`). -/
def qdQ (c : ℕ → 𝕜) (j k : ℕ) : 𝕜 := (qdTable c (j - 1)).2 k

/-- **DLMF 3.10.8**: `e_0^n = 0`, `q_1^n = c_{n+1}/c_n`. -/
theorem dlmf_3_10_8 (c : ℕ → 𝕜) (n : ℕ) : qdE c 0 n = 0 ∧ qdQ c 1 n = c (n + 1) / c n :=
  ⟨rfl, rfl⟩

/-- **DLMF 3.10.9**: the rhombus rules `e_j^k = e_{j−1}^{k+1} + q_j^{k+1} − q_j^k`,
`q_{j+1}^k = q_j^{k+1} e_j^{k+1}/e_j^k` (`j ≥ 1`). -/
theorem dlmf_3_10_9 (c : ℕ → 𝕜) (j k : ℕ) :
    qdE c (j + 1) k = qdE c j (k + 1) + qdQ c (j + 1) (k + 1) - qdQ c (j + 1) k ∧
      qdQ c (j + 2) k = qdQ c (j + 1) (k + 1) * qdE c (j + 1) (k + 1) / qdE c (j + 1) k :=
  ⟨rfl, rfl⟩

/-- **DLMF 3.10.10**: `a₀ = c₀`, `a_{2j−1} = q_j^0`, `a_{2j} = e_j^0`. -/
def qdCoeff (c : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => c 0
  | m + 1 => if m % 2 = 0 then qdQ c (m / 2 + 1) 0 else qdE c (m / 2 + 1) 0

theorem dlmf_3_10_10 (c : ℕ → 𝕜) (j : ℕ) :
    qdCoeff c 0 = c 0 ∧ qdCoeff c (2 * j + 1) = qdQ c (j + 1) 0 ∧
      qdCoeff c (2 * j + 2) = qdE c (j + 1) 0 := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [qdCoeff, Nat.mul_mod_right]
  · simp only [qdCoeff]
    rw [ite_eq_right (by omega), show (2 * j + 1) / 2 = j by omega]

end QD

/-! ### Jacobi fractions -/

section JFrac

variable {𝕜 : Type*} [Field 𝕜]

/-- **DLMF 3.10.11**: the partial numerators of
`β₀/(1 − α₀z − β₁z²/(1 − α₁z − β₂z²/(1 − α₂z − ⋯)))`: `β₀`, then `−β_m z²`. -/
noncomputable def jfA (β : ℕ → 𝕜) : ℕ → 𝕜[X]
  | 0 => 0
  | 1 => C (β 0)
  | m + 2 => -(C (β (m + 1)) * X ^ 2)

/-- The partial denominators `0`, then `1 − α_m z`. -/
noncomputable def jfB (α : ℕ → 𝕜) : ℕ → 𝕜[X]
  | 0 => 0
  | m + 1 => 1 - C (α m) * X

/-- The numerator of the `n`th convergent of 3.10.11. -/
noncomputable def jNum (α β : ℕ → 𝕜) (n : ℕ) : 𝕜[X] := pcfP (jfA β) (jfB α) (n + 1)

/-- The denominator of the `n`th convergent of 3.10.11. -/
noncomputable def jDen (α β : ℕ → 𝕜) (n : ℕ) : 𝕜[X] := pcfQ (jfA β) (jfB α) (n + 1)

/-- **DLMF §3.10(ii)**: the `J`-fraction is associated with `f` if the expansion of `Cₙ` agrees
with `f` up to and including `z^{2n−1}`. -/
def JAssociated (α β : ℕ → 𝕜) (f : PowerSeries 𝕜) : Prop :=
  ∀ n, 1 ≤ n → ∀ i < 2 * n,
    PowerSeries.coeff i ((jNum α β n : PowerSeries 𝕜) * (jDen α β n : PowerSeries 𝕜)⁻¹) =
      PowerSeries.coeff i f

/-- The even contraction of the `S`-fraction: `β₀ = a₀`, `α₀ = a₁`, `αₙ = a_{2n} + a_{2n+1}`,
`βₙ = a_{2n−1}a_{2n}`. -/
def contrAlpha (a : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => a 1
  | n + 1 => a (2 * n + 2) + a (2 * n + 3)

def contrBeta (a : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => a 0
  | n + 1 => a (2 * n + 1) * a (2 * n + 2)

/-- The contraction identity on any sequence satisfying the `S`- and `J`-recurrences. -/
theorem contraction_seq (a : ℕ → 𝕜) (P : ℕ → 𝕜[X]) (Q : ℕ → 𝕜[X])
    (hP : ∀ k, P (k + 2) = sfB (k + 1) * P (k + 1) + sfA a (k + 1) * P k)
    (hQ : ∀ k, Q (k + 2) = jfB (contrAlpha a) (k + 1) * Q (k + 1) +
      jfA (contrBeta a) (k + 1) * Q k)
    (h1 : Q 1 = P 1) (h2 : Q 2 = P 3) :
    ∀ n, Q (n + 1) = P (2 * n + 1) := by
  have hb : ∀ m, 1 ≤ m → sfB (𝕜 := 𝕜) m = 1 := fun m hm => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hm; rw [add_comm]; rfl
  -- `P_{2n+3} = (1 − α_{n+1} z) P_{2n+1} − β_{n+1} z² P_{2n−1}` for `n ≥ 1`
  have hstep : ∀ n, P (2 * n + 5) = jfB (contrAlpha a) (n + 2) * P (2 * n + 3) +
      jfA (contrBeta a) (n + 2) * P (2 * n + 1) := by
    intro n
    have e1 := hP (2 * n + 3)
    have e2 := hP (2 * n + 2)
    have e3 := hP (2 * n + 1)
    rw [hb _ (by omega)] at e1 e2 e3
    simp only [sfA, jfA, jfB, contrAlpha, contrBeta, map_add, map_mul] at e1 e2 e3 ⊢
    rw [show 2 * n + 3 + 2 = 2 * n + 5 by ring, show 2 * n + 3 + 1 = 2 * n + 4 by ring] at e1
    rw [show 2 * n + 2 + 2 = 2 * n + 4 by ring, show 2 * n + 2 + 1 = 2 * n + 3 by ring] at e2
    rw [show 2 * n + 1 + 2 = 2 * n + 3 by ring, show 2 * n + 1 + 1 = 2 * n + 2 by ring] at e3
    simp only [show 2 * n + 2 + 1 = 2 * n + 3 by ring, show 2 * n + 1 + 1 = 2 * n + 2 by ring]
      at e1 e2
    linear_combination e1 + e2 + C (a (2 * n + 2)) * X * e3
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simpa using h1
    · simpa using h2
    · rw [show n + 2 + 1 = n + 1 + 2 from rfl, hQ, ih (n + 1) (by omega), ih n (by omega),
        show 2 * (n + 2) + 1 = 2 * n + 5 by ring, hstep n]
      congr 2

/-- **DLMF §3.10(ii)**: "the convergent `Cₙ` of the Jacobi fraction (3.10.11) equals the
convergent `C_{2n}` of the Stieltjes fraction (3.10.6)": with the contracted coefficients the
numerator and denominator polynomials coincide. -/
theorem dlmf_3_10_11_contraction (a : ℕ → 𝕜) (n : ℕ) :
    jNum (contrAlpha a) (contrBeta a) n = sNum a (2 * n) ∧
      jDen (contrAlpha a) (contrBeta a) n = sDen a (2 * n) := by
  constructor
  · exact contraction_seq a (pcfP (sfA a) sfB) (pcfP (jfA (contrBeta a)) (jfB (contrAlpha a)))
      (fun k => rfl) (fun k => rfl) (by simp [pcfP, sfB, jfB])
      (by simp [pcfP, sfA, sfB, jfA, jfB, contrAlpha, contrBeta]) n
  · exact contraction_seq a (pcfQ (sfA a) sfB) (pcfQ (jfA (contrBeta a)) (jfB (contrAlpha a)))
      (fun k => rfl) (fun k => rfl) rfl
      (by simp [pcfQ, sfA, sfB, jfA, jfB, contrAlpha, contrBeta]; ring) n

/-- An `S`-fraction corresponding to `f` contracts to a `J`-fraction associated with `f`. -/
theorem sCorresponds_jAssociated {a : ℕ → 𝕜} {f : PowerSeries 𝕜} (h : SCorresponds a f) :
    JAssociated (contrAlpha a) (contrBeta a) f := by
  intro n hn i hi
  obtain ⟨hN, hD⟩ := dlmf_3_10_11_contraction a n
  rw [hN, hD]
  exact h (2 * n) (by omega) i hi

end JFrac

end Azurite.DLMF
