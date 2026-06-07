import Azurite.BasuPollackRoy.Chapter2.Section2_1.IntermediateValueProperty
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd
import Mathlib.FieldTheory.Separable

/-! # BPR §3.3, Lemma 3.12 — the intermediate value property reduces to separable polynomials

The intermediate value property `I(P, a, b)` — `P(a)·P(b) < 0 ⇒ ∃ x ∈ (a, b), P(x) = 0` — holds for
every `P ∈ R[X]` if and only if it holds for every *separable* `P ∈ R[X]`.

One direction is trivial. For the other, given `P` with `P(a)·P(b) < 0`: if `P` is separable we are
done; otherwise `P₁ = gcd(P, P')` is a non-unit, so `P = P₁ · P₂` with both factors of strictly
smaller degree, and `P(a)P(b) = (P₁(a)P₁(b))·(P₂(a)P₂(b)) < 0` forces a sign change in one factor.
Strong induction on the degree produces a root. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The intermediate value property restricted to **separable** polynomials. -/
def HasSeparableIntermediateValueProperty (R : Type*) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] : Prop :=
  ∀ (P : Polynomial R), P.Separable → ∀ (a b : R), a < b →
    Polynomial.eval a P * Polynomial.eval b P < 0 →
    ∃ x : R, a < x ∧ x < b ∧ Polynomial.eval x P = 0

/-- **BPR Lemma 3.12.** The intermediate value property holds for every polynomial in `R[X]` if and
only if it holds for every separable polynomial in `R[X]`. -/
theorem lemma_3_12 :
    HasIntermediateValueProperty R ↔ HasSeparableIntermediateValueProperty R := by
  constructor
  · intro h P _ a b hab hsign; exact h P a b hab hsign
  · intro h
    suffices H : ∀ n, ∀ (P : Polynomial R), P.natDegree = n → ∀ a b : R, a < b →
        eval a P * eval b P < 0 → ∃ x : R, a < x ∧ x < b ∧ eval x P = 0 by
      intro P a b hab hsign; exact H P.natDegree P rfl a b hab hsign
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro P hPdeg a b hab hsign
      -- `P` is nonzero and non-constant
      have hP0 : P ≠ 0 := by rintro rfl; simp at hsign
      have hPnc : P.natDegree ≠ 0 := by
        intro h0
        obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp h0
        rw [eval_C, eval_C] at hsign
        nlinarith [hsign]
      by_cases hsep : P.Separable
      · exact h P hsep a b hab hsign
      · -- `P₁ = gcd(P, P')` is a proper factor
        set g := gcd P (derivative P) with hg
        have hgU : ¬ IsUnit g := by rw [hg, gcd_isUnit_iff]; exact hsep
        have hg0 : g ≠ 0 := fun hgz =>
          hP0 ((gcd_eq_zero_iff P (derivative P)).mp hgz).1
        have hP'0 : derivative P ≠ 0 := fun hd =>
          hPnc (Polynomial.natDegree_eq_zero_of_derivative_eq_zero hd)
        have hgP : g ∣ P := gcd_dvd_left P (derivative P)
        have hgP' : g ∣ derivative P := gcd_dvd_right P (derivative P)
        obtain ⟨P₂, hP2⟩ := hgP
        have hP2_0 : P₂ ≠ 0 := by rintro rfl; rw [mul_zero] at hP2; exact hP0 hP2
        -- degree bounds: both factors have strictly smaller degree
        have hdeg_g_lt : g.natDegree < P.natDegree :=
          lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hgP' hP'0)
            (Polynomial.natDegree_derivative_lt hPnc)
        have hg_deg_pos : g.natDegree ≠ 0 := by
          intro h0
          obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp h0
          apply hgU
          rw [← hc]
          exact (Polynomial.isUnit_C).mpr
            (isUnit_iff_ne_zero.mpr (fun hc0 => hg0 (by rw [← hc, hc0, map_zero])))
        have hdeg_sum : P.natDegree = g.natDegree + P₂.natDegree := by
          rw [hP2, Polynomial.natDegree_mul hg0 hP2_0]
        have hdeg_P2_lt : P₂.natDegree < P.natDegree := by omega
        -- the sign of `P(a)P(b)` factors through the two divisors
        have hfact : eval a P * eval b P
            = (eval a g * eval b g) * (eval a P₂ * eval b P₂) := by
          rw [hP2]; simp only [eval_mul]; ring
        rw [hfact] at hsign
        rcases mul_neg_iff.mp hsign with ⟨_, hneg2⟩ | ⟨hneg1, _⟩
        · obtain ⟨x, hax, hxb, hx0⟩ :=
            ih P₂.natDegree (hPdeg ▸ hdeg_P2_lt) P₂ rfl a b hab hneg2
          exact ⟨x, hax, hxb, by rw [hP2, eval_mul, hx0, mul_zero]⟩
        · obtain ⟨x, hax, hxb, hx0⟩ :=
            ih g.natDegree (hPdeg ▸ hdeg_g_lt) g rfl a b hab hneg1
          exact ⟨x, hax, hxb, by rw [hP2, eval_mul, hx0, zero_mul]⟩

end Azurite.BPR
