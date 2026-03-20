import Azurite.AzPolynomial.Eval
import Azurite.AzPolynomial.Equiv.Basic
import Batteries.Data.Array.Lemmas
import Mathlib.Algebra.Polynomial.Roots

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
