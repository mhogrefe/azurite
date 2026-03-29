import Azurite.AzPolynomial.Eval
import Azurite.AzPolynomial.Equiv.Basic
import Batteries.Data.Array.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree

open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [DecidableEq R]

omit [DecidableEq R] in
lemma eval_list_toPoly [CommSemiring R] (l : List R) (x : R) :
  l.foldr (init := 0) (fun a acc => a + acc * x) = (List.toPoly l).eval x := by
  induction l with
  | nil =>
    simp [List.toPoly]
  | cons a as ih =>
    simp [List.toPoly, ih]
    have ht : as.toPoly.eval x * x = x * as.toPoly.eval x := mul_comm _ _
    rw [ht]

omit [DecidableEq R] in
@[simp] lemma eval_toPoly [CommSemiring R] (p : Azurite.AzPolynomial R) (x : R) :
  (AzPolynomial.toPoly p).eval x = p.eval x := by
  dsimp [AzPolynomial.toPoly, Azurite.AzPolynomial.eval]
  apply Eq.symm
  have ht : (p.coeffs.foldr (init := 0) (fun a acc => a + acc * x)) =
    (p.coeffs.toList.foldr (init := 0) (fun a acc => a + acc * x)) := Array.foldr_toList (f := fun a acc => a + acc * x) (init := 0) (xs := p.coeffs) |>.symm
  rw [ht]
  exact eval_list_toPoly p.coeffs.toList x

@[simp] lemma eval_ofPoly [CommSemiring R] (p : Polynomial R) (x : R) :
  (AzPolynomial.ofPoly p).eval x = p.eval x := by
  have h := eval_toPoly (AzPolynomial.ofPoly p) x
  rw [toPoly_ofPoly] at h
  exact h.symm

lemma funext [CommRing R] [IsDomain R] [Infinite R] {p q : AzPolynomial R} (ext : ∀ r : R, p.eval r = q.eval r) : p = q := by
  have heq : AzPolynomial.toPoly p = AzPolynomial.toPoly q := Polynomial.funext (fun r => by
    rw [eval_toPoly, eval_toPoly, ext r])
  exact Equiv.injective equivPolynomial heq

end Azurite.AzPolynomial

/-! ### Special Evaluation (BPR Algorithm 8.8) -/

open Finset

private def evalSpecialStep {R : Type _} [Mul R] [Add R] (b c : R) :
    R → R × R → R × R :=
  fun a ⟨acc, d⟩ => (a * d + acc * b, d * c)

private lemma evalSpecialStep_snd {R : Type _} [CommRing R]
    (l : List R) (b c : R) :
    (l.foldr (evalSpecialStep b c) (0, 1)).2 = c ^ l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, evalSpecialStep]
    rw [ih, List.length_cons, pow_succ]

private lemma evalSpecial_list_eq {R : Type _} [CommRing R]
    (l : List R) (b c : R) :
    (l.foldr (evalSpecialStep b c) (0, 1)).1 =
    ∑ k ∈ Finset.range l.length,
      l.getCoeff k * b ^ k * c ^ (l.length - 1 - k) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, evalSpecialStep]
    rw [evalSpecialStep_snd, ih]
    rw [show (a :: as).length = as.length + 1 from rfl, Finset.sum_range_succ']
    simp only [List.getCoeff_cons_zero, List.getCoeff_cons_succ,
               pow_zero, mul_one, Nat.sub_zero,
               show as.length + 1 - 1 = as.length from by omega]
    rw [add_comm]; congr 1
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k hk; rw [Finset.mem_range] at hk
    rw [show as.length - 1 - k = as.length - (k + 1) from by omega]; ring

namespace Azurite.AzPolynomial

open Polynomial

variable {R : Type _} [CommRing R]

/-- `evalSpecial p b c` computes `∑ a_k · b^k · c^{natDegree − k}`,
    which equals `c^(natDegree) · P(b/c)` when `c` is invertible. -/
theorem evalSpecial_eq_sum (p : AzPolynomial R) (b c : R) :
    p.evalSpecial b c =
      ∑ k ∈ Finset.range p.coeffs.size,
        p.coeff k * b ^ k * c ^ (p.natDegree - k) := by
  simp only [evalSpecial, AzPolynomial.coeff, AzPolynomial.natDegree]
  rw [show p.coeffs.foldr (fun a x => (a * x.2 + x.1 * b, x.2 * c)) (0, 1) =
    p.coeffs.toList.foldr (evalSpecialStep b c) (0, 1) from by
      rw [Array.foldr_toList]; rfl]
  rw [evalSpecial_list_eq]
  apply Finset.sum_congr (by simp)
  intro k hk; simp [List.getCoeff, Array.getElem?_toList]

/-- **BPR Algorithm 8.8 (correctness).**
    Over a field with `c ≠ 0`:
    `evalSpecial p b c = c ^ natDegree · (toPoly p).eval(b · c⁻¹)`. -/
theorem evalSpecial_eq_eval {K : Type _} [Field K] [DecidableEq K]
    (p : AzPolynomial K) (b c : K) (hc : c ≠ 0) :
    p.evalSpecial b c =
      c ^ p.natDegree * (AzPolynomial.toPoly p).eval (b * c⁻¹) := by
  rw [evalSpecial_eq_sum, eval_eq_sum_range, Finset.mul_sum]
  simp only [AzPolynomial.natDegree_toPoly, coeff_toPoly_eq]
  by_cases hp : p.coeffs.size = 0
  · -- Zero polynomial: empty sum on LHS, natDegree = 0 on RHS
    have hnd : p.natDegree = 0 := by simp [AzPolynomial.natDegree, hp]
    rw [hp, hnd, Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [AzPolynomial.coeff, hp]
  · -- Nonzero: size = natDegree + 1
    have hsize : p.coeffs.size = p.natDegree + 1 := by
      simp [AzPolynomial.natDegree]; omega
    rw [← hsize]
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mem_range] at hk
    rw [mul_pow, inv_pow]
    have hkle : k ≤ p.natDegree := by omega
    calc p.coeff k * b ^ k * c ^ (p.natDegree - k)
        = p.coeff k * (b ^ k * c ^ (p.natDegree - k)) := by ring
      _ = p.coeff k * (c ^ p.natDegree * (b ^ k * (c ^ k)⁻¹)) := by
          congr 1; rw [pow_sub₀ c hc hkle]; ring
      _ = c ^ p.natDegree * (p.coeff k * (b ^ k * (c ^ k)⁻¹)) := by ring

end Azurite.AzPolynomial
