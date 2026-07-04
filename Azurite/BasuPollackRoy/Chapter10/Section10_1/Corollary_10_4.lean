import Azurite.BasuPollackRoy.Chapter10.Section10_1.Lemma_10_2
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Order.Field.Basic

/-!
# BPR Corollary 10.4: the Cauchy bound for integer polynomials, in bitsizes

`corollary_10_4`: if `P ∈ ℤ[X]` has degree at most `p` and coefficients of
bitsize at most `τ`, then the absolute values of the roots of `P` in `R` are
bounded by `2^(τ + bit(p))`. Follows from Lemma 10.2: the leading coefficient
is a nonzero integer, so each normalized coefficient satisfies
`|aᵢ/aₚ| ≤ |aᵢ| < 2^τ`, and the sum has `deg P + 1 ≤ p + 1 ≤ 2^{bit(p)}`
terms (`Nat.lt_size_self`).

Bitsize conventions follow Chapter 8: the bitsize of `a : ℤ` is
`a.natAbs.size` (BPR Definition 8.4) and `bit(p)` is `Nat.size p`.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **BPR Corollary 10.4.** If `P ∈ ℤ[X]` has degree at most `p` and
coefficients of bitsize at most `τ`, then the absolute value of any root of
`P` in `R` is bounded by `2^(τ + bit(p))`. -/
theorem corollary_10_4 {P : ℤ[X]} (hP : P ≠ 0) {p τ : ℕ} (hdeg : P.natDegree ≤ p)
    (hτ : ∀ i, (P.coeff i).natAbs.size ≤ τ)
    {x : K} (hx : (P.map (Int.castRingHom K)).IsRoot x) :
    |x| < 2 ^ (τ + Nat.size p) := by
  have hcast : Function.Injective (Int.castRingHom K) := fun a b h => by simpa using h
  have hPK : P.map (Int.castRingHom K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hcast).mpr hP
  have hd : (P.map (Int.castRingHom K)).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hcast P
  -- Lemma 10.2 for the mapped polynomial; it remains to bound its Cauchy bound
  have h102 := lemma_10_2 hPK hx
  refine lt_trans h102 ?_
  -- the leading coefficient is a nonzero integer, so its image has `|·| ≥ 1`
  have hlcK : (P.map (Int.castRingHom K)).leadingCoeff = ((P.leadingCoeff : ℤ) : K) := by
    rw [Polynomial.leadingCoeff, hd, Polynomial.coeff_map]
    rfl
  have hlc1 : (1 : K) ≤ |(P.map (Int.castRingHom K)).leadingCoeff| := by
    rw [hlcK, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (by
      exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hP)
  -- each normalized coefficient is strictly below `2^τ`
  have hterm : ∀ i, |(P.map (Int.castRingHom K)).coeff i
      / (P.map (Int.castRingHom K)).leadingCoeff| < 2 ^ τ := by
    intro i
    have h1 : |(P.map (Int.castRingHom K)).coeff i
        / (P.map (Int.castRingHom K)).leadingCoeff|
        ≤ |(P.map (Int.castRingHom K)).coeff i| := by
      rw [abs_div]
      exact div_le_self (abs_nonneg _) hlc1
    refine lt_of_le_of_lt h1 ?_
    rw [Polynomial.coeff_map, show (Int.castRingHom K) (P.coeff i) = ((P.coeff i : ℤ) : K)
      from rfl, ← Int.cast_abs, Int.abs_eq_natAbs]
    have h2 : (P.coeff i).natAbs < 2 ^ τ := Nat.size_le.mp (hτ i)
    exact_mod_cast h2
  -- sum the bounds; there are `deg P + 1 ≤ p + 1 ≤ 2^{bit(p)}` terms
  calc cauchyBound (P.map (Int.castRingHom K))
      < ∑ _i ∈ Finset.range ((P.map (Int.castRingHom K)).natDegree + 1), (2 : K) ^ τ := by
        rw [cauchyBound]
        exact Finset.sum_lt_sum_of_nonempty Finset.nonempty_range_add_one (fun i _ => hterm i)
    _ = (((P.map (Int.castRingHom K)).natDegree + 1 : ℕ) : K) * (2 : K) ^ τ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((2 : K) ^ Nat.size p) * (2 : K) ^ τ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hd]
        calc ((P.natDegree + 1 : ℕ) : K) ≤ ((2 ^ Nat.size p : ℕ) : K) := by
              apply Nat.cast_le.mpr
              have := Nat.lt_size_self p
              omega
          _ = (2 : K) ^ Nat.size p := by push_cast; ring
    _ = 2 ^ (τ + Nat.size p) := by
        rw [← pow_add, Nat.add_comm]

end Azurite.BPR
