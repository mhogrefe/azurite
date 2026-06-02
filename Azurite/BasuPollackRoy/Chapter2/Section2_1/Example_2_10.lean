import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # BPR Section 2.1 — Example 2.10: ℝ and ℝ_alg are real closed

> The field ℝ of real numbers is of course real closed. The real
> algebraic numbers, i.e. those real numbers that satisfy an equation
> with integer coefficients, form a real closed field denoted Ralg
> (see Exercise 2.11).

The first claim, `IsRealClosed ℝ`, is proven here: `ℝ` has square roots of
nonnegative elements (`Real.sqrt`), and every odd-degree real polynomial has a
root (real irreducibles have degree `≤ 2` by the fundamental theorem of algebra).
The second is Exercise 2.11, formalised in
`Azurite.BasuPollackRoy.Chapter2.Exercise_2_11`. This file also defines the
underlying set `realAlgebraicNumbers` (with notation `ℝ_alg`) and a few
trivial closure lemmas.
-/

open Polynomial

namespace Azurite.BPR

/-- A nonzero real polynomial that is not a unit has positive degree. -/
private lemma natDegree_pos_of_not_isUnit {f : ℝ[X]} (hf : f ≠ 0) (hu : ¬IsUnit f) :
    0 < f.natDegree := by
  rcases Nat.eq_zero_or_pos f.natDegree with h | h
  · exfalso; apply hu
    rw [Polynomial.isUnit_iff]
    have hc : f.coeff 0 ≠ 0 := fun hc => hf (by rw [eq_C_of_natDegree_eq_zero h, hc, map_zero])
    exact ⟨f.coeff 0, Ne.isUnit hc, (eq_C_of_natDegree_eq_zero h).symm⟩
  · exact h

/-- **Over `ℝ`, every odd-degree polynomial has a root.** Standard proof: a real
irreducible has degree `≤ 2` (fundamental theorem of algebra), so by strong induction on
the degree an odd-degree polynomial factors off a degree-one piece, which has a root. -/
theorem exists_isRoot_real_of_odd_natDegree {f : ℝ[X]} (hodd : Odd f.natDegree) :
    ∃ r : ℝ, f.IsRoot r := by
  have hf : f ≠ 0 := by rintro rfl; simp at hodd
  suffices ∀ n, ∀ g : ℝ[X], g ≠ 0 → g.natDegree = n → Odd n → ∃ r, g.IsRoot r from
    this _ f hf rfl hodd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hg0 hgn hodd_n
    have hnu : ¬IsUnit g := fun hu => by
      have := natDegree_eq_zero_of_isUnit hu
      rw [hgn] at this; exact Nat.not_odd_zero (this ▸ hodd_n)
    rcases irreducible_or_factor hnu with hirr | ⟨a, b, ha, hb, hab⟩
    · have hle2 := hirr.natDegree_le_two
      obtain ⟨k, hk⟩ := hodd_n
      have h1 : n = 1 := by omega
      exact exists_root_of_degree_eq_one (by
        rw [degree_eq_natDegree hg0, hgn, h1]; norm_cast)
    · have ha0 : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hg0)
      have hb0 : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hg0)
      have hdeg : n = a.natDegree + b.natDegree := by
        rw [← hgn, hab, natDegree_mul ha0 hb0]
      have ha_pos := natDegree_pos_of_not_isUnit ha0 ha
      have hb_pos := natDegree_pos_of_not_isUnit hb0 hb
      by_cases hoa : Odd a.natDegree
      · have hlt : a.natDegree < n := by omega
        obtain ⟨r, hr⟩ := ih _ hlt a ha0 rfl hoa
        exact ⟨r, hab ▸ root_mul_right_of_isRoot b hr⟩
      · have hob : Odd b.natDegree := by
          rw [hdeg, Nat.odd_add] at hodd_n
          exact Nat.not_even_iff_odd.mp (fun heb => hoa (hodd_n.mpr heb))
        have hlt : b.natDegree < n := by omega
        obtain ⟨r, hr⟩ := ih _ hlt b hb0 rfl hob
        exact ⟨r, hab ▸ root_mul_left_of_isRoot a hr⟩

/-- **BPR Example 2.10 (first claim): `ℝ` is real closed.** -/
instance : IsRealClosed ℝ :=
  IsRealClosed.of_linearOrderedField
    (fun {x} hx => ⟨Real.sqrt x, (Real.mul_self_sqrt hx).symm⟩)
    (fun {_} hodd => exists_isRoot_real_of_odd_natDegree hodd)

/-- **BPR p.38.** The set of *real algebraic numbers* `R_alg`:
    those `x : ℝ` satisfying some nonzero polynomial with integer coefficients.

    Formally: `IsAlgebraic ℤ x`, i.e., `∃ p : ℤ[X], p ≠ 0 ∧ aeval x p = 0`. -/
def realAlgebraicNumbers : Set ℝ :=
  {x : ℝ | IsAlgebraic ℤ x}

scoped notation "ℝ_alg" => realAlgebraicNumbers

/-- The zero element 0 is real algebraic, witnessed by the polynomial `X`. -/
theorem zero_mem_realAlgebraicNumbers : (0 : ℝ) ∈ realAlgebraicNumbers :=
  isAlgebraic_zero

/-- The element 1 is real algebraic, witnessed by the polynomial `X - 1`. -/
theorem one_mem_realAlgebraicNumbers : (1 : ℝ) ∈ realAlgebraicNumbers :=
  isAlgebraic_one

/-- Every integer is a real algebraic number. -/
theorem intCast_mem_realAlgebraicNumbers (n : ℤ) : (n : ℝ) ∈ realAlgebraicNumbers :=
  isAlgebraic_algebraMap n

end Azurite.BPR
