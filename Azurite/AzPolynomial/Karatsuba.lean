import Azurite.AzPolynomial.Mul
import Azurite.AzInt.Instances
import Azurite.AzRat.Instances
import Azurite.AzZMod.Instances

/-!
# Karatsuba Multiplication for AzPolynomial

Implements the Karatsuba algorithm for polynomial multiplication,
achieving O(n^log₂3) ≈ O(n^1.585) complexity instead of O(n²).

The algorithm:
  Given polynomials p, q, split each at midpoint m:
    p = p_low + x^m · p_high
    q = q_low + x^m · q_high

  Compute three products (instead of four):
    z0 = p_low · q_low
    z2 = p_high · q_high
    z1 = (p_low + p_high) · (q_low + q_high) - z0 - z2

  Result: z0 + x^m · z1 + x^(2m) · z2

All intermediate operations use raw coefficient arrays to avoid
redundant normalization. Only the final result is normalized.

Requires `Ring R` for the subtraction step in z1.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Ring R] [DecidableEq R]

-- ── Raw coefficient array operations ────────────────────────────────────────
-- These operate on raw Array R, avoiding AzPolynomial normalization overhead.

/-- Add two coefficient arrays elementwise, zero-padding the shorter one. -/
def rawAdd (a b : Array R) : Array R :=
  let n := max a.size b.size
  Array.ofFn (fun (i : Fin n) =>
    let ai := (a[i.val]?).getD 0
    let bi := (b[i.val]?).getD 0
    ai + bi)

/-- Subtract two coefficient arrays elementwise (a - b), zero-padding shorter. -/
def rawSub (a b : Array R) : Array R :=
  let n := max a.size b.size
  Array.ofFn (fun (i : Fin n) =>
    let ai := (a[i.val]?).getD 0
    let bi := (b[i.val]?).getD 0
    ai - bi)

/-- Prepend `m` zeros — equivalent to multiplying by x^m. -/
def rawShift (a : Array R) (m : Nat) : Array R :=
  (Array.replicate m (0 : R)) ++ a


-- ── Karatsuba algorithm ─────────────────────────────────────────────────────

/-- Threshold below which we fall back to basecase multiplication.
    Karatsuba's overhead (extra additions, array splits) isn't worth it
    for small polynomials. -/
def karatsubaThreshold : Nat := 32

/-- Karatsuba multiplication on raw coefficient arrays.
    Falls back to basecase for small inputs.
    Uses explicit fuel for clean termination. -/
def rawKaratsuba (a b : Array R) : Array R :=
  go (max a.size b.size) a b (Nat.le_refl _)
where
  go (fuel : Nat) (a b : Array R) (hfuel : max a.size b.size ≤ fuel) : Array R :=
    if a.size == 0 || b.size == 0 then #[]
    else if hlt : fuel < karatsubaThreshold then
      mulBasecaseCoeffs a b
    else
      let m := fuel / 2
      -- Split: p = p_low + x^m · p_high
      let a0 := a.take m
      let a1 := a.drop m
      let b0 := b.take m
      let b1 := b.drop m
      -- Size bounds for recursive calls
      have hfuel_pos : 0 < fuel := by unfold karatsubaThreshold at hlt; omega
      have hm_lt : m < fuel := Nat.div_lt_self hfuel_pos (by omega)
      have ha0 : a0.size ≤ m := by simp [a0]
      have hb0 : b0.size ≤ m := by simp [b0]
      have ha1 : a1.size ≤ fuel - m := by simp [a1]; omega
      have hb1 : b1.size ≤ fuel - m := by simp [b1]; omega
      -- z0 = a_low * b_low (max size ≤ m)
      let z0 := go m a0 b0 (by omega)
      -- z2 = a_high * b_high (max size ≤ fuel - m)
      let z2 := go (fuel - m) a1 b1 (by omega)
      -- z1 = (a_low + a_high) * (b_low + b_high) - z0 - z2
      -- rawAdd produces size = max(a0.size, a1.size) ≤ fuel - m
      let sum_a := rawAdd a0 a1
      let sum_b := rawAdd b0 b1
      have hsa : sum_a.size ≤ fuel - m := by
        simp [sum_a, rawAdd]; omega
      have hsb : sum_b.size ≤ fuel - m := by
        simp [sum_b, rawAdd]; omega
      let z1_raw := go (fuel - m) sum_a sum_b (by omega)
      let z1 := rawSub (rawSub z1_raw z0) z2
      -- Combine: z0 + x^m · z1 + x^(2m) · z2
      rawAdd (rawAdd z0 (rawShift z1 m)) (rawShift z2 (2 * m))
  termination_by fuel
  decreasing_by all_goals (unfold karatsubaThreshold at *; simp_all; omega)

/-- Karatsuba polynomial multiplication.
    Uses the Karatsuba algorithm for O(n^1.585) complexity.
    Falls back to O(n²) basecase for small polynomials.
    Requires `Ring R` for the intermediate subtraction step. -/
def mulKaratsuba (p q : AzPolynomial R) : AzPolynomial R :=
  normalize (rawKaratsuba p.coeffs q.coeffs)

-- ── Parameterized version (for threshold tuning) ────────────────────────────

/-- Karatsuba multiplication on raw coefficient arrays with a configurable
    threshold. Same algorithm as `rawKaratsuba` but the cutoff is a runtime
    parameter instead of the compile-time `karatsubaThreshold`.
    Requires `threshold ≥ 2` so that `fuel / 2 < fuel` in recursive calls. -/
def rawKaratsubaWithThreshold (threshold : Nat) (a b : Array R) : Array R :=
  go (max a.size b.size) a b (Nat.le_refl _)
where
  go (fuel : Nat) (a b : Array R) (hfuel : max a.size b.size ≤ fuel) : Array R :=
    if a.size == 0 || b.size == 0 then #[]
    else if fuel < threshold then
      mulBasecaseCoeffs a b
    else if _ : fuel < 2 then
      mulBasecaseCoeffs a b
    else
      let m := fuel / 2
      let a0 := a.take m; let a1 := a.drop m
      let b0 := b.take m; let b1 := b.drop m
      have hfuel_pos : 0 < fuel := by omega
      have hm_lt : m < fuel := Nat.div_lt_self hfuel_pos (by omega)
      have ha0 : a0.size ≤ m := by simp [a0]
      have hb0 : b0.size ≤ m := by simp [b0]
      have ha1 : a1.size ≤ fuel - m := by simp [a1]; omega
      have hb1 : b1.size ≤ fuel - m := by simp [b1]; omega
      let z0 := go m a0 b0 (by omega)
      let z2 := go (fuel - m) a1 b1 (by omega)
      let sum_a := rawAdd a0 a1
      let sum_b := rawAdd b0 b1
      have hsa : sum_a.size ≤ fuel - m := by simp [sum_a, rawAdd]; omega
      have hsb : sum_b.size ≤ fuel - m := by simp [sum_b, rawAdd]; omega
      let z1_raw := go (fuel - m) sum_a sum_b (by omega)
      let z1 := rawSub (rawSub z1_raw z0) z2
      rawAdd (rawAdd z0 (rawShift z1 m)) (rawShift z2 (2 * m))
  termination_by fuel

/-- Karatsuba multiplication with a configurable threshold.
    Use `mulKaratsuba` for the default threshold, or this version
    to experiment with different cutoffs (e.g. for auto-tuning). -/
def mulKaratsubaWithThreshold (threshold : Nat) (p q : AzPolynomial R) : AzPolynomial R :=
  normalize (rawKaratsubaWithThreshold threshold p.coeffs q.coeffs)

-- ── Karatsuba-based MulConfig instances ──────────────────────────────────────

/-- Karatsuba multiplication for any `CommRing` with default threshold.
    Overrides the basecase instance from `Mul.lean`. -/
instance (priority := 200) instAzPolynomialMulConfigKaratsuba
    {R : Type _} [CommRing R] [DecidableEq R] : AzPolynomialMulConfig R where
  dmul p q := mulKaratsubaWithThreshold karatsubaThreshold p q

/-- Karatsuba multiplication for `AzInt`, threshold tuned to 29. -/
instance (priority := 300) : AzPolynomialMulConfig AzInt where
  dmul p q := mulKaratsubaWithThreshold 29 p q

/-- Karatsuba multiplication for `AzRat`, threshold tuned to 14. -/
instance (priority := 300) : AzPolynomialMulConfig AzRat where
  dmul p q := mulKaratsubaWithThreshold 14 p q

/-- Karatsuba multiplication for `AzZMod m`, threshold tuned to 8. -/
instance (priority := 300) {m : AzNat} [NeZero m.toNat] : AzPolynomialMulConfig (AzZMod m) where
  dmul p q := mulKaratsubaWithThreshold 8 p q

-- ── Tests ───────────────────────────────────────────────────────────────────

-- Basic correctness tests
#guard mulKaratsuba (parseAzPolynomial (R := AzInt) "x+1").get! (parseAzPolynomial (R := AzInt) "x+2").get!
    == (parseAzPolynomial (R := AzInt) "x^2+3*x+2").get!

#guard mulKaratsuba (parseAzPolynomial (R := AzInt) "2*x^2+x").get! (parseAzPolynomial (R := AzInt) "x-1").get!
    == (parseAzPolynomial (R := AzInt) "2*x^3-x^2-x").get!

#guard mulKaratsuba (0 : AzPolynomial AzInt) (parseAzPolynomial (R := AzInt) "x^2+1").get! == 0

#guard mulKaratsuba (parseAzPolynomial (R := AzInt) "3").get! (parseAzPolynomial (R := AzInt) "4").get!
    == (parseAzPolynomial (R := AzInt) "12").get!

-- Consistency with mulBasecaseFold
#guard mulKaratsuba (parseAzPolynomial (R := AzInt) "x+1").get! (parseAzPolynomial (R := AzInt) "x+2").get!
    == mulBasecaseFold (parseAzPolynomial (R := AzInt) "x+1").get! (parseAzPolynomial (R := AzInt) "x+2").get!

#guard mulKaratsuba (parseAzPolynomial (R := AzInt) "2*x^2+x").get! (parseAzPolynomial (R := AzInt) "x-1").get!
    == mulBasecaseFold (parseAzPolynomial (R := AzInt) "2*x^2+x").get! (parseAzPolynomial (R := AzInt) "x-1").get!

-- Verify that * uses Karatsuba for AzInt (threshold 29)
#guard (parseAzPolynomial (R := AzInt) "x+1").get! * (parseAzPolynomial (R := AzInt) "x+2").get!
    == mulKaratsuba (parseAzPolynomial (R := AzInt) "x+1").get! (parseAzPolynomial (R := AzInt) "x+2").get!

end Azurite.AzPolynomial
