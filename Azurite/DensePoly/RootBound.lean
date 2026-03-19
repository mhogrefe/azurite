import Azurite.DensePoly.Basic
import Azurite.DensePoly.Parse

/-!
# Computable Root Bound for DensePoly

Implements the Cauchy bound on polynomial roots:
for `p = aₙ xⁿ + … + a₀` with `aₙ ≠ 0`,

  all roots r satisfy  `|r| < 1 + max(|aᵢ/aₙ|)` for `0 ≤ i < n`.

The bound is computed in `ℚ` given an embedding `R →+* ℚ`.
For zero or constant polynomials, returns 0.

The function returns a `ℚ` such that all real roots of the polynomial
lie in the interval `(-rootBound, rootBound)`.
-/

namespace Azurite.DensePoly

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Compute the maximum absolute value of `|f(aᵢ)/f(aₙ)|` for `0 ≤ i < n`,
    where `f` is the embedding into `ℚ` and `aₙ` is the leading coefficient.
    Returns the max ratio as a `ℚ`. -/
def maxCoeffRatio (f : R →+* ℚ) (coeffs : Array R) : ℚ :=
  if h : coeffs.size ≤ 1 then 0
  else
    have hpos : 0 < coeffs.size := by omega
    let lead := f (coeffs[coeffs.size - 1]'(by omega))
    if lead == 0 then 0  -- shouldn't happen for well-formed DensePoly
    else
      let n := coeffs.size - 1
      Fin.foldl n (init := (0 : ℚ)) fun acc i =>
        let ratio := |f (coeffs[i.val]'(by omega))| / |lead|
        max acc ratio

-- ── Key properties of maxCoeffRatio ────────────────────────────────────────

/-- Helper: the `Fin.foldl max 0` accumulator is always ≥ 0. -/
private lemma fin_foldl_max_nonneg {n : Nat} {g : Fin n → ℚ} (hg : ∀ i, 0 ≤ g i) :
    0 ≤ Fin.foldl n (init := (0 : ℚ)) (fun acc i => max acc (g i)) := by
  induction n with
  | zero => rw [Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last]
    exact le_max_of_le_left (ih (fun i => hg i.castSucc))

/-- Helper: each value is ≤ the `Fin.foldl max 0` accumulator. -/
private lemma le_fin_foldl_max {n : Nat} {g : Fin n → ℚ} (i : Fin n) :
    g i ≤ Fin.foldl n (init := (0 : ℚ)) (fun acc j => max acc (g j)) := by
  induction n with
  | zero => exact i.elim0
  | succ k ih =>
    rw [Fin.foldl_succ_last]
    by_cases hi : i.val < k
    · exact le_max_of_le_left (ih (g := fun j => g j.castSucc) ⟨i.val, hi⟩)
    · have hik : i = Fin.last k := by ext; simp [Fin.last]; omega
      rw [hik]
      exact le_max_right _ _

/-- `maxCoeffRatio` is non-negative. -/
lemma maxCoeffRatio_nonneg (f : R →+* ℚ) (coeffs : Array R) :
    0 ≤ maxCoeffRatio f coeffs := by
  unfold maxCoeffRatio
  split
  · rfl
  · next h =>
    simp only
    by_cases hlead : f (coeffs[coeffs.size - 1]'(by omega)) == 0
    · simp [hlead]
    · simp [hlead]
      apply fin_foldl_max_nonneg
      intro i
      exact Rat.div_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Each coefficient ratio is ≤ `maxCoeffRatio`. -/
lemma le_maxCoeffRatio (f : R →+* ℚ) (coeffs : Array R)
    (hsize : ¬ coeffs.size ≤ 1)
    (hlead : f (coeffs[coeffs.size - 1]'(by omega)) ≠ 0)
    (i : Fin (coeffs.size - 1)) :
    |f (coeffs[i.val]'(by omega))| / |f (coeffs[coeffs.size - 1]'(by omega))|
    ≤ maxCoeffRatio f coeffs := by
  unfold maxCoeffRatio
  simp only [show ¬ coeffs.size ≤ 1 from hsize, dite_false]
  simp only [show ¬ (f (coeffs[coeffs.size - 1]'(by omega)) == 0) from by
    simp [beq_iff_eq]; exact hlead]
  exact le_fin_foldl_max i

/-- Cauchy bound on the roots of a `DensePoly R`.

    Given an embedding `f : R →+* ℚ`, returns a rational `b ≥ 0` such that
    every real root `r` of `p` satisfies `|r| < b`.

    For a polynomial `aₙ xⁿ + … + a₀`, the bound is
    `1 + max(|a₀/aₙ|, …, |aₙ₋₁/aₙ|)`.

    Returns `0` for the zero polynomial and for constant polynomials
    (which have no roots or roots are trivially bounded). -/
def rootBound (f : R →+* ℚ) (p : DensePoly R) : ℚ :=
  if p.coeffs.size ≤ 1 then 0
  else 1 + maxCoeffRatio f p.coeffs

/-- Returns the interval `(-rootBound, rootBound)` containing all real roots.
    For zero/constant polynomials, returns `(0, 0)`. -/
def rootInterval (f : R →+* ℚ) (p : DensePoly R) : ℚ × ℚ :=
  let b := rootBound f p
  (-b, b)

-- ── Convenience wrappers ───────────────────────────────────────────────────

/-- Root bound for `DensePoly ℤ` using the canonical embedding `ℤ ↪ ℚ`. -/
def rootBoundInt (p : DensePoly ℤ) : ℚ :=
  rootBound (Int.castRingHom ℚ) p

/-- Root bound for `DensePoly ℚ`. -/
def rootBoundRat (p : DensePoly ℚ) : ℚ :=
  rootBound (RingHom.id ℚ) p

-- ── Tests ──────────────────────────────────────────────────────────────────

-- x^2 - 4 : roots are ±2, bound should be 1 + |(-4)/1| = 5
#eval rootBoundInt (parseDensePoly (R := ℤ) "x^2-4").get!  -- expect 5
#guard rootBoundInt (parseDensePoly (R := ℤ) "x^2-4").get! == 5

-- x^2 + 1 : no real roots, but bound is still 1 + |1/1| = 2
#eval rootBoundInt (parseDensePoly (R := ℤ) "x^2+1").get!  -- expect 2
#guard rootBoundInt (parseDensePoly (R := ℤ) "x^2+1").get! == 2

-- 2x^3 - 3x + 1 : roots are 1, 1/2, -1; bound = 1 + max(|1/2|, |3/2|, |0|) = 5/2
#eval rootBoundInt (parseDensePoly (R := ℤ) "2*x^3-3*x+1").get!  -- expect 5/2

-- 3 (constant polynomial) : no roots, bound = 0
#eval rootBoundInt (parseDensePoly (R := ℤ) "3").get!  -- expect 0
#guard rootBoundInt (parseDensePoly (R := ℤ) "3").get! == 0

-- 0 (zero polynomial) : bound = 0
#guard rootBoundInt (0 : DensePoly ℤ) == 0

-- x - 5 : root is 5, bound = 1 + |(-5)/1| = 6
#eval rootBoundInt (parseDensePoly (R := ℤ) "x-5").get!  -- expect 6
#guard rootBoundInt (parseDensePoly (R := ℤ) "x-5").get! == 6

-- rootInterval test: x^2 - 4 should give (-5, 5)
#eval rootInterval (Int.castRingHom ℚ) (parseDensePoly (R := ℤ) "x^2-4").get!

end Azurite.DensePoly
