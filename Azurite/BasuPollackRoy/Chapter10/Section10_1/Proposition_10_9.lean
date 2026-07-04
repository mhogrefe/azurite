import Azurite.BasuPollackRoy.Chapter10.Section10_1.Lemma_10_10

/-!
# BPR Proposition 10.9 (Landau's inequality): the measure is bounded by the norm

`proposition_10_9`: `Mea(P) ≤ ∥P∥`. BPR's proof: exchange each root `zᵢ`
outside the unit disk for the factor `(z̄ᵢ x − 1)`, obtaining a polynomial `R`
with `∥R∥ = ∥P∥` (Lemma 10.10, applied `k` times) whose leading coefficient
has modulus `Mea(P)`; then `Mea(P)² = |bₚ|² ≤ ∥R∥² = ∥P∥²`.

The formalization runs the same exchange as an induction on the number of
roots outside the unit disk: if `α` is such a root, factor `P = (X − α)·Q`
and pass to `P' = (ᾱX − 1)·Q`, which has equal norm (Lemma 10.10), equal
measure (the factor exchange trades the root `α` for `ᾱ⁻¹` inside the disk
while multiplying the leading coefficient by `ᾱ`), and one fewer root outside
the disk. The base case is the coefficient bound `|aₚ| ≤ ∥P∥`.

The measure lemmas proved on the way: multiplicativity of `polyMeasure` and
its values on the linear factors `x − α` and `αx − 1`.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The measure is multiplicative (roots and leading coefficients both are). -/
theorem polyMeasure_mul {P Q : Polynomial (Ri R)} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    polyMeasure (P * Q) = polyMeasure P * polyMeasure Q := by
  rw [polyMeasure, polyMeasure, polyMeasure, Polynomial.leadingCoeff_mul, Ri.abs_mul,
    Polynomial.roots_mul (mul_ne_zero hP hQ), Multiset.map_add, Multiset.prod_add]
  ring

theorem polyMeasure_X_sub_C (α : Ri R) :
    polyMeasure (X - C α) = max 1 (Ri.abs α) := by
  rw [polyMeasure, Polynomial.roots_X_sub_C,
    show (X - C α : (Ri R)[X]).leadingCoeff = 1 from (Polynomial.monic_X_sub_C α),
    Ri.abs_one, one_mul, Multiset.map_singleton, Multiset.prod_singleton]

theorem polyMeasure_C_mul_X_sub_one {α : Ri R} (hα : α ≠ 0) :
    polyMeasure (C α * X - 1) = Ri.abs α * max 1 (Ri.abs α⁻¹) := by
  have hfact : (C α * X - 1 : (Ri R)[X]) = C α * (X - C α⁻¹) := by
    rw [mul_sub, ← Polynomial.C_mul, mul_inv_cancel₀ hα, Polynomial.C_1]
  rw [hfact, polyMeasure, Polynomial.roots_C_mul _ hα, Polynomial.roots_X_sub_C,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    show (X - C α⁻¹ : (Ri R)[X]).leadingCoeff = 1 from (Polynomial.monic_X_sub_C α⁻¹),
    mul_one, Multiset.map_singleton, Multiset.prod_singleton]

/-- The exchange induction: `Mea(P) ≤ ∥P∥`, by the number of roots of `P`
outside the unit disk. -/
theorem landau_aux : ∀ (k : ℕ) (P : Polynomial (Ri R)), P ≠ 0 →
    (P.roots.filter (fun z => 1 < Ri.abs z)).card = k →
    polyMeasure P ≤ polyNorm P := by
  intro k
  induction k with
  | zero =>
    intro P hP hcard
    -- no roots outside the disk: the max-product is `1` and `Mea = |aₚ| ≤ ∥P∥`
    have hall : ∀ z ∈ P.roots, Ri.abs z ≤ 1 := by
      intro z hz
      by_contra hgt
      push Not at hgt
      have hmem : z ∈ P.roots.filter (fun z => 1 < Ri.abs z) :=
        Multiset.mem_filter.mpr ⟨hz, hgt⟩
      have := Multiset.card_pos_iff_exists_mem.mpr ⟨z, hmem⟩
      omega
    have hprod : (P.roots.map (fun z => max 1 (Ri.abs z))).prod = 1 := by
      apply Multiset.prod_eq_one
      intro a ha
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ha
      exact max_eq_left (hall z hz)
    rw [polyMeasure, hprod, mul_one]
    exact abs_leadingCoeff_le_polyNorm P
  | succ n ih =>
    intro P hP hcard
    classical
    -- pick a root `α` outside the disk and factor `P = (X − α)·Q`
    have hne : P.roots.filter (fun z => 1 < Ri.abs z) ≠ 0 := by
      intro h
      rw [h] at hcard
      simp at hcard
    obtain ⟨α, hαf⟩ := Multiset.exists_mem_of_ne_zero hne
    obtain ⟨hαroot, hα1⟩ := Multiset.mem_filter.mp hαf
    have hα0 : α ≠ 0 := by
      intro h
      rw [h, Ri.abs_zero] at hα1
      linarith
    have hαc0 : Ri.conj R α ≠ 0 := by
      intro h
      have h2 := congrArg (Ri.conj R) h
      rw [Ri.conj_conj, map_zero] at h2
      exact hα0 h2
    obtain ⟨Q, hPQ⟩ := (Polynomial.dvd_iff_isRoot.mpr
      (Polynomial.isRoot_of_mem_roots hαroot))
    have hQ0 : Q ≠ 0 := by
      intro h
      rw [h, mul_zero] at hPQ
      exact hP hPQ
    have hX0 : (X - C α : (Ri R)[X]) ≠ 0 := (Polynomial.monic_X_sub_C α).ne_zero
    have hL0 : (C (Ri.conj R α) * X - 1 : (Ri R)[X]) ≠ 0 := by
      intro h
      have h1 := congrArg (fun q => Polynomial.coeff q 1) h
      simp [Polynomial.coeff_one] at h1
      exact hα0 h1
    set P' := (C (Ri.conj R α) * X - 1) * Q with hP'
    have hP'0 : P' ≠ 0 := mul_ne_zero hL0 hQ0
    -- Lemma 10.10: the norms agree
    have hnorm : polyNorm P = polyNorm P' := by
      rw [hPQ, hP']
      exact lemma_10_10 α Q
    have habsα : (0 : R) < Ri.abs α := by linarith
    -- the measures agree: the exchange trades `α` for `ᾱ⁻¹` inside the disk
    have hmea : polyMeasure P = polyMeasure P' := by
      rw [hPQ, hP', polyMeasure_mul hX0 hQ0, polyMeasure_mul hL0 hQ0,
        polyMeasure_X_sub_C, polyMeasure_C_mul_X_sub_one hαc0,
        max_eq_right (le_of_lt hα1), Ri.abs_inv, Ri.abs_conj,
        max_eq_left (by rw [inv_le_one₀ habsα]; linarith)]
      ring
    -- one fewer root outside the disk
    have hcard' : (P'.roots.filter (fun z => 1 < Ri.abs z)).card = n := by
      have hrootsP : P.roots = {α} + Q.roots := by
        rw [hPQ, Polynomial.roots_mul (hPQ ▸ hP), Polynomial.roots_X_sub_C]
      have hfact : (C (Ri.conj R α) * X - 1 : (Ri R)[X])
          = C (Ri.conj R α) * (X - C (Ri.conj R α)⁻¹) := by
        rw [mul_sub, ← Polynomial.C_mul, mul_inv_cancel₀ hαc0, Polynomial.C_1]
      have hrootsP' : P'.roots = {(Ri.conj R α)⁻¹} + Q.roots := by
        rw [hP', Polynomial.roots_mul hP'0, hfact, Polynomial.roots_C_mul _ hαc0,
          Polynomial.roots_X_sub_C]
      have habsinv : Ri.abs ((Ri.conj R α)⁻¹) ≤ 1 := by
        rw [Ri.abs_inv, Ri.abs_conj, inv_le_one₀ habsα]
        linarith
      have h1 : (P.roots.filter (fun z => 1 < Ri.abs z)).card
          = 1 + (Q.roots.filter (fun z => 1 < Ri.abs z)).card := by
        rw [hrootsP, Multiset.filter_add, Multiset.card_add,
          Multiset.filter_singleton, if_pos hα1]
        simp
      have h2 : (P'.roots.filter (fun z => 1 < Ri.abs z)).card
          = (Q.roots.filter (fun z => 1 < Ri.abs z)).card := by
        rw [hrootsP', Multiset.filter_add, Multiset.card_add,
          Multiset.filter_singleton, if_neg (by
            push Not
            exact habsinv)]
        simp
      omega
    rw [hmea, hnorm]
    exact ih P' hP'0 hcard'

/-- **BPR Proposition 10.9 (Landau's inequality).** `Mea(P) ≤ ∥P∥`. -/
theorem proposition_10_9 (P : Polynomial (Ri R)) : polyMeasure P ≤ polyNorm P := by
  rcases eq_or_ne P 0 with rfl | hP
  · rw [polyMeasure, Polynomial.roots_zero, Polynomial.leadingCoeff_zero, Ri.abs_zero,
      zero_mul]
    exact polyNorm_nonneg 0
  · exact landau_aux _ P hP rfl

end Azurite.BPR
