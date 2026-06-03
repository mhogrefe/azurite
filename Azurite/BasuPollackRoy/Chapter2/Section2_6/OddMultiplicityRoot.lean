import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-! # Over a real closed field, an odd-degree polynomial has a root of odd multiplicity

`IsRealClosed.exists_isRoot_of_odd_natDegree` gives *a* root of an odd-degree polynomial; for the
Puiseux root construction we need a root of *odd multiplicity* (`exists_odd_rootMultiplicity`).

By strong induction on the degree: an odd-degree `g` has a root `r` of multiplicity `m`. If `m` is
odd we are done; otherwise factor `g = (X − r)^m h` with `h(r) ≠ 0`, so `deg h = deg g − m` is
again odd and smaller, and a root `s` of odd multiplicity of `h` (which is `≠ r`, since
`h(r) ≠ 0`) has the same multiplicity in `g`. This is the parity-of-factorization argument: real
closed fields factor into linear and irreducible-quadratic factors, the latter contributing even
degree, so an odd degree forces an odd total multiplicity of real roots. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [IsRealClosed R]

/-- **An odd-degree polynomial over a real closed field has a root of odd multiplicity.** -/
theorem exists_odd_rootMultiplicity : ∀ (n : ℕ) (g : R[X]), g.natDegree = n → Odd n →
    ∃ x, Odd (g.rootMultiplicity x) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro g hgn hodd
    have hg0 : g ≠ 0 := by
      rintro rfl
      rw [natDegree_zero] at hgn; subst hgn; simp at hodd
    obtain ⟨r, hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (f := g) (by rw [hgn]; exact hodd)
    set m := g.rootMultiplicity r with hm
    by_cases hmo : Odd m
    · exact ⟨r, hmo⟩
    · rw [Nat.not_odd_iff_even] at hmo
      have hm1 : 1 ≤ m := (rootMultiplicity_pos hg0).mpr hr
      have hmonic : ((X - C r) ^ m).Monic := (monic_X_sub_C r).pow m
      set h := g /ₘ (X - C r) ^ m with hhdef
      have hfact : g = (X - C r) ^ m * h := by
        conv_lhs => rw [← modByMonic_add_div g ((X - C r) ^ m),
          (modByMonic_eq_zero_iff_dvd hmonic).mpr (pow_rootMultiplicity_dvd g r), zero_add]
      have hhne : h ≠ 0 := fun h0 => hg0 (by rw [hfact, h0, mul_zero])
      have hhr : h.eval r ≠ 0 := by
        rw [hhdef, hm]; exact eval_divByMonic_pow_rootMultiplicity_ne_zero r hg0
      have hnm : n = m + h.natDegree := by
        have := natDegree_mul (pow_ne_zero m (X_sub_C_ne_zero r)) hhne
        rw [← hfact, hgn, natDegree_pow, natDegree_X_sub_C, mul_one] at this
        exact this
      have hoddh : Odd h.natDegree := by
        rw [Nat.odd_iff] at hodd ⊢; rw [Nat.even_iff] at hmo; omega
      obtain ⟨s, hs⟩ := IH h.natDegree (by omega) h rfl hoddh
      have hsr : s ≠ r := by
        rintro rfl
        rw [rootMultiplicity_eq_zero hhr] at hs
        simp at hs
      refine ⟨s, ?_⟩
      have hpq : (X - C r) ^ m * h ≠ 0 := by rw [← hfact]; exact hg0
      have hnotroot : ¬ ((X - C r) ^ m).IsRoot s := by
        rw [IsRoot, eval_pow, eval_sub, eval_X, eval_C]
        exact pow_ne_zero m (sub_ne_zero.mpr hsr)
      rw [hfact, rootMultiplicity_mul hpq, rootMultiplicity_eq_zero hnotroot, zero_add]
      exact hs

/-- **An odd-degree polynomial with nonzero constant term has a *nonzero* root of odd
multiplicity.** -/
theorem exists_ne_zero_odd_rootMultiplicity {g : R[X]} (hodd : Odd g.natDegree)
    (h0 : g.coeff 0 ≠ 0) : ∃ x, x ≠ 0 ∧ Odd (g.rootMultiplicity x) := by
  obtain ⟨x, hx⟩ := exists_odd_rootMultiplicity g.natDegree g rfl hodd
  have hg0 : g ≠ 0 := fun h => h0 (by rw [h, coeff_zero])
  have hroot : g.IsRoot x := (rootMultiplicity_pos hg0).mp (by obtain ⟨k, hk⟩ := hx; omega)
  refine ⟨x, ?_, hx⟩
  rintro rfl
  have he : g.eval 0 = 0 := hroot
  rw [← coeff_zero_eq_eval_zero] at he
  exact h0 he

/-- **A nonzero root of odd multiplicity from an odd-length span.** If `g ≠ 0` and the span
`deg g − natTrailingDegree g` (the degree after stripping the `X^t` factor) is odd, then `g` has a
nonzero root of odd multiplicity. Applied to a characteristic polynomial `Q = X^{A.1}·φ(X^q)`,
whose span is the edge length `B.1 − A.1`. -/
theorem exists_ne_zero_odd_rootMultiplicity_of_span {g : R[X]} (hg : g ≠ 0)
    (hodd : Odd (g.natDegree - g.natTrailingDegree)) :
    ∃ x, x ≠ 0 ∧ Odd (g.rootMultiplicity x) := by
  set t := g.natTrailingDegree with ht
  have hdvd : (X : R[X]) ^ t ∣ g :=
    X_pow_dvd_iff.mpr (fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd)
  obtain ⟨h, hgh⟩ := hdvd
  have hhne : h ≠ 0 := by rintro rfl; rw [mul_zero] at hgh; exact hg hgh
  have hXt_ne : (X : R[X]) ^ t ≠ 0 := pow_ne_zero t X_ne_zero
  have hh0 : h.coeff 0 ≠ 0 := by
    have hc : g.coeff t = h.coeff 0 := by
      have hcm := coeff_X_pow_mul h t 0
      rw [zero_add, ← hgh] at hcm; exact hcm
    rw [← hc]; exact trailingCoeff_nonzero_iff_nonzero.mpr hg
  have hdeg : h.natDegree = g.natDegree - t := by
    have hnd := natDegree_mul hXt_ne hhne
    rw [← hgh, natDegree_X_pow] at hnd; omega
  obtain ⟨x, hx0, hxodd⟩ := exists_ne_zero_odd_rootMultiplicity (by rw [hdeg]; exact hodd) hh0
  refine ⟨x, hx0, ?_⟩
  rw [hgh, rootMultiplicity_mul (by rw [← hgh]; exact hg),
    rootMultiplicity_eq_zero (by rw [IsRoot, eval_pow, eval_X]; exact pow_ne_zero t hx0), zero_add]
  exact hxodd

end Azurite.BPR
