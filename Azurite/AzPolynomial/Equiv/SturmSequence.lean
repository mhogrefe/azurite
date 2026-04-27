import Azurite.AzPolynomial.SturmSequence
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Neg
import Azurite.AzPolynomial.Equiv.QuoRem
import Azurite.AzPolynomial.Equiv.Derivative
import Azurite.BasuPollackRoy.Chapter2.SturmSequence

/-!
# Equivalence: AzPolynomial Sturm sequence ↔ Polynomial Sturm sequence

`toPoly (sturmSequence P n) = Azurite.BPR.sturmSequence (toPoly P) n`.
-/

open Polynomial

namespace Azurite.AzPolynomial

variable {K : Type _} [Field K] [DecidableEq K] [PolynomialDerivative K]

/-- The two-argument signed-remainder sequence on `AzPolynomial`, with the
    same shape as `Azurite.BPR.SRemS`. We expose this as a building block
    so `sturmSequence` matches `SRemS P P.derivative` term-by-term. -/
private def sRemS (P Q : AzPolynomial K) : ℕ → AzPolynomial K
  | 0 => P
  | 1 => Q
  | n + 2 =>
      let prev := sRemS P Q (n + 1)
      if prev = 0 then 0
      else -((sRemS P Q n).rem prev)

private theorem sturmSequence_eq_sRemS (P : AzPolynomial K) (n : ℕ) :
    sturmSequence P n = sRemS P (derivative P) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 =>
      simp only [sturmSequence, sRemS]
      rw [ih (n + 1) (by omega), ih n (by omega)]

omit [PolynomialDerivative K] in
open Classical in
private theorem toPoly_sRemS (P Q : AzPolynomial K) (n : ℕ) :
    AzPolynomial.toPoly (sRemS P Q n) =
      Azurite.BPR.SRemS (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 =>
      have h_succ := ih (n + 1) (by omega)
      have h_n := ih n (by omega)
      simp only [sRemS, Azurite.BPR.SRemS]
      by_cases hprev : sRemS P Q (n + 1) = 0
      · -- The AzPolynomial side reduces to 0.
        rw [if_pos hprev]
        rw [hprev] at h_succ
        rw [toPoly_zero] at h_succ ⊢
        rw [if_pos h_succ.symm]
      · -- The AzPolynomial side reduces to `-((sRemS P Q n).rem prev)`.
        rw [if_neg hprev]
        have hprev_poly : AzPolynomial.toPoly (sRemS P Q (n + 1)) ≠ 0 := by
          rw [Ne, ← toPoly_zero (R := K), toPoly_inj]
          exact hprev
        rw [h_succ] at hprev_poly
        rw [if_neg hprev_poly]
        rw [toPoly_neg, toPoly_rem _ _ (by rw [h_succ]; exact hprev_poly), h_succ, h_n]

theorem toPoly_sturmSequence (P : AzPolynomial K) (n : ℕ) :
    AzPolynomial.toPoly (sturmSequence P n) =
      Azurite.BPR.sturmSequence (AzPolynomial.toPoly P) n := by
  rw [sturmSequence_eq_sRemS, toPoly_sRemS, toPoly_derivative]
  rfl

end Azurite.AzPolynomial
