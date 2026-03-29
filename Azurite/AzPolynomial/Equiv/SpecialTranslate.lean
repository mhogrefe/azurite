import Azurite.AzPolynomial.SpecialTranslate
import Azurite.AzPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.Equiv.Monomial
import Azurite.AzPolynomial.Equiv.Eval
import Azurite.AzPolynomial.Equiv.Map

/-! # Equivalence: AzPolynomial.specialTranslate ↔ Polynomial identities

Proves correctness of `AzPolynomial.specialTranslate` (BPR Algorithm 8.10).

## Main results

- `toPoly_cXSubB` — `toPoly (cXSubB b c) = C c * X - C b`
- `eval_specialTranslate` — integral evaluation identity
- `eval_specialTranslate_field` — field identity: `= c^deg · eval(z − b/c) P`
- `isRoot_specialTranslate_iff` — root iff root of original at shifted point
- `isRoot_specialTranslate_map_iff` — same across a ring homomorphism `f : R →+* K`

## References

* Basu, Pollack, Roy – *Algorithms in Real Algebraic Geometry*, Algorithm 8.10.
-/

set_option autoImplicit false

open Azurite Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-! ### toPoly_cXSubB -/

/-- `toPoly (cXSubB b c) = C c * X - C b`. -/
@[simp] theorem toPoly_cXSubB (b c : R) :
    AzPolynomial.toPoly (cXSubB b c) = Polynomial.C c * Polynomial.X - Polynomial.C b := by
  unfold cXSubB
  split
  · next hc =>
    subst hc
    split
    · next hb => subst hb; simp [AzPolynomial.toPoly, List.toPoly]
    · next hb =>
      show AzPolynomial.toPoly ⟨#[-b], _⟩ = _
      simp [AzPolynomial.toPoly, List.toPoly, sub_eq_add_neg, Polynomial.C_neg]
  · next hc =>
    show AzPolynomial.toPoly ⟨#[-b, c], _⟩ = _
    simp [AzPolynomial.toPoly, List.toPoly, sub_eq_add_neg, Polynomial.C_neg]; ring

/-! ### Integral evaluation identity -/

/-- **Integral evaluation identity.**
    `eval z (toPoly (specialTranslate p b c)) = evalSpecial p (c·z − b) c`. -/
theorem eval_specialTranslate (p : AzPolynomial R) (b c z : R) :
    Polynomial.eval z (AzPolynomial.toPoly (p.specialTranslate b c)) =
    p.evalSpecial (c * z - b) c := by
  simp only [specialTranslate, evalSpecial, ← Array.foldr_toList]
  set l := p.coeffs.toList
  suffices h : ∀ l : List R,
    let az := l.foldr (fun a x => (C (a * x.2) + x.1 * cXSubB b c, x.2 * c))
      ((0 : AzPolynomial R), (1 : R))
    let sc := l.foldr (fun a x => (a * x.2 + x.1 * (c * z - b), x.2 * c)) ((0 : R), (1 : R))
    (AzPolynomial.toPoly az.1).eval z = sc.1 ∧ az.2 = sc.2 by exact (h l).1
  intro l; induction l with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [List.foldr_cons]
    exact ⟨by simp only [toPoly_add, toPoly_mul, toPoly_C, toPoly_cXSubB,
                          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
                          Polynomial.eval_sub, Polynomial.eval_X]; rw [ih1, ih2],
           by rw [ih2]⟩

/-! ### Field evaluation identity -/

theorem eval_specialTranslate_field {K : Type _} [Field K] [DecidableEq K]
    (p : AzPolynomial K) (b c : K) (hc : c ≠ 0) (z : K) :
    Polynomial.eval z (AzPolynomial.toPoly (p.specialTranslate b c)) =
    c ^ p.natDegree * Polynomial.eval (z - b * c⁻¹) (AzPolynomial.toPoly p) := by
  rw [eval_specialTranslate, evalSpecial_eq_eval p _ c hc]
  congr 1
  rw [sub_mul, mul_comm c z, mul_assoc, mul_inv_cancel₀ hc, mul_one]

/-! ### Root translation (field) -/

theorem isRoot_specialTranslate_iff {K : Type _} [Field K] [DecidableEq K]
    (p : AzPolynomial K) (b c : K) (hc : c ≠ 0) (z : K) :
    Polynomial.IsRoot (AzPolynomial.toPoly (p.specialTranslate b c)) z ↔
    Polynomial.IsRoot (AzPolynomial.toPoly p) (z - b * c⁻¹) := by
  simp only [Polynomial.IsRoot, eval_specialTranslate_field p b c hc z]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hpow | heval
    · exact absurd hpow (pow_ne_zero _ hc)
    · exact heval
  · intro h; rw [h, mul_zero]

/-! ### Mapped root theorem -/

private theorem toPoly_foldr_st_both (l : List R) (b c : R) :
    let cxb := cXSubB b c
    let az := l.foldr (fun a x => (C (a * x.2) + x.1 * cxb, x.2 * c))
      ((0 : AzPolynomial R), (1 : R))
    let pf := l.foldr (fun a x =>
      (Polynomial.C (a * x.2) + x.1 * (Polynomial.C c * Polynomial.X - Polynomial.C b), x.2 * c))
      ((0 : Polynomial R), (1 : R))
    AzPolynomial.toPoly az.1 = pf.1 ∧ az.2 = pf.2 := by
  induction l with
  | nil => exact ⟨toPoly_zero, rfl⟩
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    obtain ⟨ih1, ih2⟩ := ih
    exact ⟨by rw [toPoly_add, toPoly_mul, toPoly_C, toPoly_cXSubB, ih1, ih2],
           by rw [ih2]⟩

omit [DecidableEq R] in
private theorem map_poly_foldr_both {S : Type _} [CommRing S] [DecidableEq S]
    (f : R →+* S) (l : List R) (b c : R) :
    let lhs := l.foldr (fun a x =>
      (Polynomial.C (a * x.2) + x.1 * (Polynomial.C c * Polynomial.X - Polynomial.C b), x.2 * c))
      ((0 : Polynomial R), (1 : R))
    let rhs := (l.map f).foldr (fun a x =>
      (Polynomial.C (a * x.2) + x.1 * (Polynomial.C (f c) * Polynomial.X - Polynomial.C (f b)),
       x.2 * (f c)))
      ((0 : Polynomial S), (1 : S))
    Polynomial.map f lhs.1 = rhs.1 ∧ f lhs.2 = rhs.2 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr_cons, List.map_cons]
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
                 Polynomial.map_sub, Polynomial.map_X]
      rw [map_mul, ih2, ih1]
    · rw [map_mul, ih2]

private theorem eval_poly_foldr_both {S : Type _} [CommRing S]
    (l : List S) (b' c' z : S) :
    let pf := l.foldr (fun a x =>
      (Polynomial.C (a * x.2) + x.1 * (Polynomial.C c' * Polynomial.X - Polynomial.C b'), x.2 * c'))
      ((0 : Polynomial S), (1 : S))
    let sf := l.foldr (evalSpecialStep (c' * z - b') c') ((0 : S), (1 : S))
    pf.1.eval z = sf.1 ∧ pf.2 = sf.2 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr_cons, evalSpecialStep]
    obtain ⟨ih1, ih2⟩ := ih
    exact ⟨by simp only [Polynomial.eval_add, Polynomial.eval_mul,
                          Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
              rw [ih1, ih2],
           by rw [ih2]⟩

private theorem evalSpecialStep_fold_eq {K : Type _} [Field K]
    (l : List K) (fc x : K) :
    (l.foldr (evalSpecialStep (fc * x) fc) ((0 : K), (1 : K))).1 =
     fc ^ (l.length - 1) * l.foldr (fun a acc => a + acc * x) (0 : K) ∧
    (l.foldr (evalSpecialStep (fc * x) fc) ((0 : K), (1 : K))).2 = fc ^ l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · simp only [List.foldr_cons, List.length_cons, evalSpecialStep]
      rw [ih1, ih2]
      cases tl with
      | nil => simp
      | cons h t =>
        simp only [List.length_cons]
        have h1 : t.length + 1 - 1 = t.length := by omega
        have h2 : t.length + 1 + 1 - 1 = t.length + 1 := by omega
        rw [h1, h2]; ring
    · simp only [List.foldr_cons, List.length_cons, evalSpecialStep]
      rw [ih2]; ring

omit [DecidableEq R] in
private theorem horner_fold_eq_eval₂ {K : Type _} [Field K]
    (f : R →+* K) (l : List R) (x : K) :
    (l.map f).foldr (fun a acc => a + acc * x) (0 : K) =
    l.toPoly.eval₂ f x := by
  induction l with
  | nil => simp [List.toPoly]
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldr_cons, List.toPoly,
               Polynomial.eval₂_add, Polynomial.eval₂_C,
               Polynomial.eval₂_mul, Polynomial.eval₂_X]
    rw [ih]; ring


/-- **Root translation across a ring homomorphism.**

    If `f : R →+* K` maps into a field with `f c ≠ 0`, then
    `z` is a root of `map f (toPoly (specialTranslate p b c))` iff
    `z − f(b) · (f c)⁻¹` is a root of `map f (toPoly p)`. -/
theorem isRoot_specialTranslate_map_iff {K : Type _} [Field K] [DecidableEq K]
    (f : R →+* K) (p : AzPolynomial R) (b c : R) (hfc : f c ≠ 0) (z : K) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (p.specialTranslate b c))) z ↔
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly p)) (z - f b * (f c)⁻¹) := by
  simp only [Polynomial.IsRoot]
  have hst : AzPolynomial.toPoly (p.specialTranslate b c) =
    (p.coeffs.toList.foldr (fun a x =>
      (Polynomial.C (a * x.2) + x.1 * (Polynomial.C c * Polynomial.X - Polynomial.C b), x.2 * c))
      ((0 : Polynomial R), (1 : R))).1 := by
    simp only [specialTranslate, ← Array.foldr_toList]
    exact (toPoly_foldr_st_both p.coeffs.toList b c).1
  rw [hst, (map_poly_foldr_both f p.coeffs.toList b c).1,
      (eval_poly_foldr_both (p.coeffs.toList.map f) (f b) (f c) z).1]
  have halg : f c * z - f b = f c * (z - f b * (f c)⁻¹) := by
    rw [mul_sub, mul_comm (f c) (f b * (f c)⁻¹), mul_assoc, inv_mul_cancel₀ hfc, mul_one]
  rw [halg, (evalSpecialStep_fold_eq (p.coeffs.toList.map f) (f c) (z - f b * (f c)⁻¹)).1,
      horner_fold_eq_eval₂ f p.coeffs.toList (z - f b * (f c)⁻¹), ← Polynomial.eval_map]
  -- p.coeffs.toList.toPoly = AzPolynomial.toPoly p definitionally
  change _ * Polynomial.eval _ (Polynomial.map f (AzPolynomial.toPoly p)) = 0 ↔ _
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hpow | heval
    · exact absurd hpow (pow_ne_zero _ hfc)
    · exact heval
  · intro h; rw [h, mul_zero]
