import Azurite.AzPolynomial.SpecialTranslate
import Azurite.AzPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.Equiv.Monomial
import Azurite.AzPolynomial.Equiv.Eval
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! # Equivalence: AzPolynomial.specialTranslate ↔ Polynomial identities

Proves correctness of `AzPolynomial.specialTranslate` (BPR Algorithm 8.10).

The structural spec is `toPoly_specialTranslate`:

  `toPoly (specialTranslate p b c) = ((toPoly p).scaleRoots c).comp (C c * X - C b)`,

that is, the algorithm computes the composition of Mathlib's `Polynomial.scaleRoots`
with the linear substitution `X ↦ c·X − b`. Everything else — the coefficient sum
form, the evaluation identities, the root translation lemmas, and the degree and
leading-coefficient facts — is derived from it (or from the sum form
`toPoly_specialTranslate_sum`, which is the same identity with the composition
expanded).

## Main results

- `toPoly_cXSubB` — `toPoly (cXSubB b c) = C c * X - C b`
- `toPoly_specialTranslate` — structural spec via `scaleRoots` and `comp`
- `toPoly_specialTranslate_sum` — expanded sum form (used for mapped statements)
- `eval_specialTranslate` — integral evaluation identity (via `evalSpecial`)
- `eval_specialTranslate_field` — field identity: `= c^deg · eval (z − b/c) P`
- `isRoot_specialTranslate_iff` — root iff root of original at shifted point
- `isRoot_specialTranslate_map_iff` — same across a ring homomorphism `f : R →+* K`
- `natDegree_specialTranslate`, `leadingCoeff_specialTranslate`,
  `specialTranslate_ne_zero` — degree data over an integral domain, for `c ≠ 0`

## References

* Basu, Pollack, Roy – *Algorithms in Real Algebraic Geometry*, Algorithm 8.10.
-/

set_option autoImplicit false

open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-! ### The linear polynomial `c·X − b` -/

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

/-! ### Structural spec -/

/-- The Horner fold of `specialTranslate`, as a coefficient sum (with the second
component of the state being the running power of `c`). -/
private theorem toPoly_specialTranslate_foldr (b c : R) : ∀ l : List R,
    AzPolynomial.toPoly
        (l.foldr (fun a x => (C (a * x.2) + x.1 * cXSubB b c, x.2 * c))
          ((0 : AzPolynomial R), (1 : R))).1
      = ∑ i ∈ Finset.range l.length,
          Polynomial.C (l.getD i 0 * c ^ (l.length - 1 - i))
            * (Polynomial.C c * Polynomial.X - Polynomial.C b) ^ i
    ∧ (l.foldr (fun a x => (C (a * x.2) + x.1 * cXSubB b c, x.2 * c))
          ((0 : AzPolynomial R), (1 : R))).2 = c ^ l.length
  | [] => by simp
  | hd :: tl => by
    obtain ⟨ih1, ih2⟩ := toPoly_specialTranslate_foldr b c tl
    refine ⟨?_, by simp only [List.foldr_cons]; rw [ih2, List.length_cons, pow_succ]⟩
    simp only [List.foldr_cons, toPoly_add, toPoly_mul, toPoly_C, toPoly_cXSubB, ih1, ih2,
      List.length_cons]
    rw [Finset.sum_range_succ', Finset.sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, Nat.add_sub_cancel]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hexp : tl.length - (i + 1) = tl.length - 1 - i := by omega
    rw [hexp, mul_assoc, ← pow_succ]

omit [DecidableEq R] in
/-- A nonzero polynomial's coefficient array has size `deg + 1`. -/
private theorem coeffs_size_of_ne_zero {p : AzPolynomial R} (hp : p ≠ 0) :
    p.coeffs.size = p.natDegree + 1 := by
  have hsz : p.coeffs.size ≠ 0 :=
    fun h => hp (AzPolynomial.ext (by rw [Array.size_eq_zero_iff.mp h]; rfl))
  show _ = p.coeffs.size - 1 + 1
  omega

/-- **Sum form of the structural spec.**
`toPoly (specialTranslate p b c) = ∑ᵢ aᵢ · c^(deg P − i) · (c·X − b)^i`. This is the
form that pushes through coefficient maps and evaluations termwise. -/
theorem toPoly_specialTranslate_sum (p : AzPolynomial R) (b c : R) :
    AzPolynomial.toPoly (p.specialTranslate b c)
      = ∑ i ∈ Finset.range p.coeffs.size,
          Polynomial.C (p.coeff i * c ^ (p.natDegree - i))
            * (Polynomial.C c * Polynomial.X - Polynomial.C b) ^ i := by
  simp only [specialTranslate, ← Array.foldr_toList]
  rw [(toPoly_specialTranslate_foldr b c p.coeffs.toList).1]
  apply Finset.sum_congr (by rw [Array.length_toList])
  intro i hi
  have h1 : p.coeffs.toList.getD i 0 = p.coeff i := by
    rw [show p.coeff i = (p.coeffs[i]?).getD 0 from rfl, List.getD_eq_getElem?_getD,
      Array.getElem?_toList]
  have h2 : p.coeffs.toList.length - 1 - i = p.natDegree - i := by
    rw [Array.length_toList]; rfl
  rw [h1, h2]

/-- **Structural spec of `specialTranslate` (BPR Algorithm 8.10).** The algorithm
computes `scaleRoots` followed by the linear substitution `X ↦ c·X − b`:
`toPoly (specialTranslate p b c) = ((toPoly p).scaleRoots c).comp (C c * X − C b)`.
Mathlib's `scaleRoots`/`comp` lemmas therefore apply directly. -/
theorem toPoly_specialTranslate (p : AzPolynomial R) (b c : R) :
    AzPolynomial.toPoly (p.specialTranslate b c)
      = ((AzPolynomial.toPoly p).scaleRoots c).comp
          (Polynomial.C c * Polynomial.X - Polynomial.C b) := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [toPoly_specialTranslate_sum]
    simp [toPoly_zero]
  · rw [toPoly_specialTranslate_sum, Polynomial.comp, Polynomial.eval₂_eq_sum_range,
      Polynomial.natDegree_scaleRoots, AzPolynomial.natDegree_toPoly,
      ← coeffs_size_of_ne_zero hp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.coeff_scaleRoots, AzPolynomial.coeff_toPoly, AzPolynomial.natDegree_toPoly,
      map_mul, map_pow]

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

/-- **Field evaluation identity.** For `c ≠ 0`,
`eval z (toPoly (specialTranslate p b c)) = c^(deg P) · eval (z − b/c) (toPoly p)`. -/
theorem eval_specialTranslate_field {K : Type _} [Field K] [DecidableEq K]
    (p : AzPolynomial K) (b c : K) (hc : c ≠ 0) (z : K) :
    Polynomial.eval z (AzPolynomial.toPoly (p.specialTranslate b c)) =
    c ^ p.natDegree * Polynomial.eval (z - b / c) (AzPolynomial.toPoly p) := by
  rw [toPoly_specialTranslate, Polynomial.eval_comp]
  have h1 : Polynomial.eval z (Polynomial.C c * Polynomial.X - Polynomial.C b)
      = c * (z - b / c) := by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [mul_sub, mul_div_cancel₀ _ hc]
  rw [h1]
  have hs := Polynomial.scaleRoots_eval₂_mul (p := AzPolynomial.toPoly p)
    (RingHom.id K) (z - b / c) c
  simp only [Polynomial.eval₂_id, RingHom.id_apply] at hs
  rw [hs, AzPolynomial.natDegree_toPoly]

/-! ### Root translation (field) -/

/-- **Root translation.** For `c ≠ 0`, `z` is a root of `c^(deg P)·P(X − b/c)` iff
`z − b/c` is a root of `P`: the roots of `specialTranslate p b c` are the roots of
`p`, each shifted by `+ b/c`. -/
theorem isRoot_specialTranslate_iff {K : Type _} [Field K] [DecidableEq K]
    (p : AzPolynomial K) (b c : K) (hc : c ≠ 0) (z : K) :
    Polynomial.IsRoot (AzPolynomial.toPoly (p.specialTranslate b c)) z ↔
    Polynomial.IsRoot (AzPolynomial.toPoly p) (z - b / c) := by
  simp only [Polynomial.IsRoot, eval_specialTranslate_field p b c hc z]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hpow | heval
    · exact absurd hpow (pow_ne_zero _ hc)
    · exact heval
  · intro h; rw [h, mul_zero]

/-- **Root translation across a ring homomorphism.**

    If `f : R →+* K` maps into a field with `f c ≠ 0` (no injectivity needed), then
    `z` is a root of `map f (toPoly (specialTranslate p b c))` iff
    `z − f(b) / f(c)` is a root of `map f (toPoly p)`.

    **Application:** if `P ∈ ℤ[X]` is a minimal polynomial of an algebraic number
    `α`, the complex roots of `specialTranslate P b c` are exactly the complex
    roots of `P` shifted by `b/c`, giving a defining polynomial for `α + b/c`. -/
theorem isRoot_specialTranslate_map_iff {K : Type _} [Field K] [DecidableEq K]
    (f : R →+* K) (p : AzPolynomial R) (b c : R) (hfc : f c ≠ 0) (z : K) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (p.specialTranslate b c))) z ↔
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly p)) (z - f b / f c) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [Polynomial.IsRoot, toPoly_specialTranslate_sum, toPoly_zero]
  · have hsz := coeffs_size_of_ne_zero hp
    simp only [Polynomial.IsRoot, toPoly_specialTranslate_sum, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_C,
      Polynomial.map_X, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, map_mul, map_pow]
    have hterm : ∀ i ∈ Finset.range p.coeffs.size,
        f (p.coeff i) * f c ^ (p.natDegree - i) * (f c * z - f b) ^ i
          = f c ^ p.natDegree * (f (p.coeff i) * (z - f b / f c) ^ i) := by
      intro i hi
      rw [Finset.mem_range, hsz] at hi
      have hcz : f c * z - f b = f c * (z - f b / f c) := by
        rw [mul_sub, mul_div_cancel₀ _ hfc]
      have hexp : p.natDegree - i + i = p.natDegree := by omega
      calc f (p.coeff i) * f c ^ (p.natDegree - i) * (f c * z - f b) ^ i
          = f c ^ (p.natDegree - i + i) * (f (p.coeff i) * (z - f b / f c) ^ i) := by
            rw [hcz, mul_pow, pow_add]; ring
        _ = _ := by rw [hexp]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hrhs : Polynomial.eval (z - f b / f c) (Polynomial.map f (AzPolynomial.toPoly p))
        = ∑ i ∈ Finset.range p.coeffs.size, f (p.coeff i) * (z - f b / f c) ^ i := by
      rw [Polynomial.eval_eq_sum_range' (n := p.coeffs.size)
        (lt_of_le_of_lt Polynomial.natDegree_map_le
          (by rw [AzPolynomial.natDegree_toPoly, hsz]; omega))]
      apply Finset.sum_congr rfl; intro i _
      rw [Polynomial.coeff_map, AzPolynomial.coeff_toPoly]
    rw [← hrhs]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h1 | h2
      · exact absurd h1 (pow_ne_zero _ hfc)
      · exact h2
    · intro h; rw [h, mul_zero]

/-! ### Degree data over an integral domain -/

section Domain

variable {D : Type _} [CommRing D] [IsDomain D] [DecidableEq D]

/-- For `c ≠ 0` over a domain, `specialTranslate` preserves the degree. -/
theorem natDegree_specialTranslate (p : AzPolynomial D) (b c : D) (hc : c ≠ 0) :
    (p.specialTranslate b c).natDegree = p.natDegree := by
  have hlin : (Polynomial.C c * Polynomial.X - Polynomial.C b).natDegree = 1 := by
    rw [sub_eq_add_neg, ← Polynomial.C_neg]
    exact Polynomial.natDegree_linear hc
  rw [← AzPolynomial.natDegree_toPoly, toPoly_specialTranslate, Polynomial.natDegree_comp,
    Polynomial.natDegree_scaleRoots, AzPolynomial.natDegree_toPoly, hlin, mul_one]

/-- For `c ≠ 0` over a domain, the leading coefficient of `specialTranslate p b c`
is `lcof(P) · c^(deg P)`. -/
theorem leadingCoeff_specialTranslate (p : AzPolynomial D) (b c : D) (hc : c ≠ 0) :
    (p.specialTranslate b c).leadingCoeff = p.leadingCoeff * c ^ p.natDegree := by
  have hlin : (Polynomial.C c * Polynomial.X - Polynomial.C b).natDegree = 1 := by
    rw [sub_eq_add_neg, ← Polynomial.C_neg]
    exact Polynomial.natDegree_linear hc
  have hlc : (Polynomial.C c * Polynomial.X - Polynomial.C b).leadingCoeff = c := by
    rw [sub_eq_add_neg, ← Polynomial.C_neg]
    exact Polynomial.leadingCoeff_linear hc
  rw [← leadingCoeff_toPoly, toPoly_specialTranslate,
    Polynomial.leadingCoeff_comp (by rw [hlin]; exact one_ne_zero),
    Polynomial.leadingCoeff_scaleRoots, Polynomial.natDegree_scaleRoots, hlc,
    leadingCoeff_toPoly, AzPolynomial.natDegree_toPoly]

/-- For `p ≠ 0` and `c ≠ 0` over a domain, `specialTranslate p b c ≠ 0`. -/
theorem specialTranslate_ne_zero {p : AzPolynomial D} (hp : p ≠ 0) (b : D) {c : D} (hc : c ≠ 0) :
    p.specialTranslate b c ≠ 0 := by
  intro h
  have hlc := leadingCoeff_specialTranslate p b c hc
  rw [h] at hlc
  have hlp : p.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_toPoly]
    exact Polynomial.leadingCoeff_ne_zero.mpr
      (fun hz => hp (toPoly_inj.mp (hz.trans toPoly_zero.symm)))
  exact mul_ne_zero hlp (pow_ne_zero _ hc)
    (by rw [← hlc]; rw [show (0 : AzPolynomial D).leadingCoeff = 0 from rfl])

end Domain

end Azurite.AzPolynomial
