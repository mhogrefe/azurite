import Azurite.AzPolynomial.ScaleRoots
import Azurite.AzPolynomial.Equiv.Add
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Equivalence: AzPolynomial.scaleRoots ↔ Polynomial identities

Proves correctness of `AzPolynomial.scaleRoots` (root scaling by `b / c`).

The structural spec is `toPoly_scaleRoots`:

  `toPoly (scaleRoots p b c) = ((toPoly p).scaleRoots b).comp (C c * X)`,

that is, Mathlib's `Polynomial.scaleRoots` (roots × `b`) followed by the
substitution `X ↦ c·X` (roots ÷ `c`). Everything else — the sum form, the field
evaluation identity, the root scaling lemmas, and the degree data — is derived
from it, mirroring `Equiv/SpecialTranslate.lean`.

Note the hypothesis asymmetry (the mirror image of `specialTranslate`): the
evaluation and root lemmas clear denominators through `b`, so they assume
`b ≠ 0` (resp. `f b ≠ 0`); the degree and leading-coefficient lemmas depend on
the leading coefficient `aₚ·c^p`, so they assume `c ≠ 0` (over a domain) while
`b` may be anything — scaling roots by `0/c` collapses all roots to `0` with the
degree preserved.

## Main results

- `Polynomial.coeff_comp_C_mul_X` — `(q.comp (C c * X)).coeff n = q.coeff n * c^n`
- `toPoly_scaleRoots` — structural spec via Mathlib's `scaleRoots` and `comp`
- `toPoly_scaleRoots_sum` — expanded sum form (used for mapped statements)
- `ofPoly_scaleRoots` — `ofPoly` version
- `eval_scaleRoots_field` — `eval z = b^(deg P) · eval (c·z/b) P` for `b ≠ 0`
- `isRoot_scaleRoots_iff` — root at `z` ↔ root of `P` at `c·z/b`
- `isRoot_scaleRoots_map_iff` — same across a ring homomorphism `f : R →+* K`
- `natDegree_scaleRoots`, `leadingCoeff_scaleRoots`, `scaleRoots_ne_zero` —
  degree data over an integral domain, for `c ≠ 0`
-/

set_option autoImplicit false

open Polynomial

/-- The coefficient of `X^n` in `q(c·X)` is `c^n` times that of `q`. -/
theorem Polynomial.coeff_comp_C_mul_X {R : Type _} [CommRing R] (q : R[X]) (c : R) (n : ℕ) :
    (q.comp (Polynomial.C c * Polynomial.X)).coeff n = q.coeff n * c ^ n := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, add_mul]
  | monomial e a =>
    rw [monomial_comp, mul_pow, ← Polynomial.C_pow, coeff_monomial,
      show Polynomial.C a * (Polynomial.C (c ^ e) * Polynomial.X ^ e)
          = Polynomial.C (a * c ^ e) * Polynomial.X ^ e by rw [map_mul]; ring,
      coeff_C_mul_X_pow]
    by_cases h : n = e
    · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right h, ite_eq_right (fun he : e = n => h he.symm), zero_mul]

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

omit [DecidableEq R] in
/-- A nonzero polynomial's coefficient array has size `deg + 1`. -/
private theorem coeffs_size_of_ne_zero {p : AzPolynomial R} (hp : p ≠ 0) :
    p.coeffs.size = p.natDegree + 1 := by
  have hsz : p.coeffs.size ≠ 0 :=
    fun h => hp (AzPolynomial.ext (by rw [Array.size_eq_zero_iff.mp h]; rfl))
  show _ = p.coeffs.size - 1 + 1
  omega

/-- **Structural spec of `scaleRoots`.** The operation is Mathlib's
`Polynomial.scaleRoots` (roots × `b`) followed by the substitution `X ↦ c·X`
(roots ÷ `c`):
`toPoly (scaleRoots p b c) = ((toPoly p).scaleRoots b).comp (C c * X)`. -/
theorem toPoly_scaleRoots (p : AzPolynomial R) (b c : R) :
    AzPolynomial.toPoly (p.scaleRoots b c)
      = ((AzPolynomial.toPoly p).scaleRoots b).comp (Polynomial.C c * Polynomial.X) := by
  ext n
  rw [AzPolynomial.coeff_toPoly, coeff_scaleRoots, Polynomial.coeff_comp_C_mul_X,
    Polynomial.coeff_scaleRoots, AzPolynomial.coeff_toPoly, AzPolynomial.natDegree_toPoly,
    mul_right_comm]

/-- **Sum form of the structural spec.**
`toPoly (scaleRoots p b c) = ∑ᵢ aᵢ · c^i · b^(deg P − i) · X^i`. -/
theorem toPoly_scaleRoots_sum (p : AzPolynomial R) (b c : R) :
    AzPolynomial.toPoly (p.scaleRoots b c)
      = ∑ i ∈ Finset.range p.coeffs.size,
          Polynomial.C (p.coeff i * c ^ i * b ^ (p.natDegree - i)) * Polynomial.X ^ i := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [scaleRoots_zero, toPoly_zero, show (0 : AzPolynomial R).coeffs = #[] from rfl]
    simp
  · rw [toPoly_scaleRoots, Polynomial.comp, Polynomial.eval₂_eq_sum_range,
      Polynomial.natDegree_scaleRoots, AzPolynomial.natDegree_toPoly,
      ← coeffs_size_of_ne_zero hp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.coeff_scaleRoots, AzPolynomial.coeff_toPoly, AzPolynomial.natDegree_toPoly,
      mul_pow, ← Polynomial.C_pow]
    simp only [map_mul]
    ring

/-- **`ofPoly` version.** -/
theorem ofPoly_scaleRoots (q : Polynomial R) (b c : R) :
    (AzPolynomial.ofPoly q).scaleRoots b c
      = AzPolynomial.ofPoly ((q.scaleRoots b).comp (Polynomial.C c * Polynomial.X)) := by
  rw [← toPoly_inj, toPoly_scaleRoots, toPoly_ofPoly, toPoly_ofPoly]

/-- **Field evaluation identity.** For `b ≠ 0`,
`eval z (toPoly (scaleRoots p b c)) = b^(deg P) · eval (c·z/b) (toPoly p)`. -/
theorem eval_scaleRoots_field {K : Type _} [Field K] [DecidableEq K]
    (p : AzPolynomial K) (b c : K) (hb : b ≠ 0) (z : K) :
    Polynomial.eval z (AzPolynomial.toPoly (p.scaleRoots b c)) =
      b ^ p.natDegree * Polynomial.eval (c * z / b) (AzPolynomial.toPoly p) := by
  rw [toPoly_scaleRoots, Polynomial.eval_comp]
  have h1 : Polynomial.eval z (Polynomial.C c * Polynomial.X) = b * (c * z / b) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [mul_comm b, div_mul_cancel₀ _ hb]
  rw [h1]
  have hs := Polynomial.scaleRoots_eval₂_mul (p := AzPolynomial.toPoly p)
    (RingHom.id K) (c * z / b) b
  simp only [Polynomial.eval₂_id, RingHom.id_apply] at hs
  rw [hs, AzPolynomial.natDegree_toPoly]

/-- **Root scaling.** For `b ≠ 0`, `z` is a root of `scaleRoots p b c` iff
`c·z/b` is a root of `P`: the roots of `scaleRoots p b c` are the roots of `p`,
each multiplied by `b/c`. -/
theorem isRoot_scaleRoots_iff {K : Type _} [Field K] [DecidableEq K]
    (p : AzPolynomial K) (b c : K) (hb : b ≠ 0) (z : K) :
    Polynomial.IsRoot (AzPolynomial.toPoly (p.scaleRoots b c)) z ↔
    Polynomial.IsRoot (AzPolynomial.toPoly p) (c * z / b) := by
  simp only [Polynomial.IsRoot, eval_scaleRoots_field p b c hb z]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hpow | heval
    · exact absurd hpow (pow_ne_zero _ hb)
    · exact heval
  · intro h; rw [h, mul_zero]

/-- **Root scaling across a ring homomorphism.**

    If `f : R →+* K` maps into a field with `f b ≠ 0` (no injectivity needed),
    then `z` is a root of `map f (toPoly (scaleRoots p b c))` iff
    `f(c)·z / f(b)` is a root of `map f (toPoly p)`.

    **Application:** if `P ∈ ℤ[X]` is a defining polynomial of an algebraic
    number `α`, then `scaleRoots P b c` is a defining polynomial of `(b/c)·α`. -/
theorem isRoot_scaleRoots_map_iff {K : Type _} [Field K] [DecidableEq K]
    (f : R →+* K) (p : AzPolynomial R) (b c : R) (hfb : f b ≠ 0) (z : K) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (p.scaleRoots b c))) z ↔
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly p)) (f c * z / f b) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [Polynomial.IsRoot, toPoly_zero]
  · have hsz := coeffs_size_of_ne_zero hp
    simp only [Polynomial.IsRoot, toPoly_scaleRoots_sum, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, map_mul, map_pow]
    have hterm : ∀ i ∈ Finset.range p.coeffs.size,
        f (p.coeff i) * f c ^ i * f b ^ (p.natDegree - i) * z ^ i
          = f b ^ p.natDegree * (f (p.coeff i) * (f c * z / f b) ^ i) := by
      intro i hi
      rw [Finset.mem_range, hsz] at hi
      have hcz : (f c * z / f b) ^ i = f c ^ i * z ^ i / f b ^ i := by
        rw [div_pow, mul_pow]
      have hexp : p.natDegree - i + i = p.natDegree := by omega
      rw [hcz]
      field_simp
      calc f (p.coeff i) * f c ^ i * f b ^ (p.natDegree - i) * z ^ i * f b ^ i
          = f b ^ (p.natDegree - i + i) * (f (p.coeff i) * (f c ^ i * z ^ i)) := by
            rw [pow_add]; ring
        _ = _ := by rw [hexp]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hrhs : Polynomial.eval (f c * z / f b) (Polynomial.map f (AzPolynomial.toPoly p))
        = ∑ i ∈ Finset.range p.coeffs.size, f (p.coeff i) * (f c * z / f b) ^ i := by
      rw [Polynomial.eval_eq_sum_range' (n := p.coeffs.size)
        (lt_of_le_of_lt Polynomial.natDegree_map_le
          (by rw [AzPolynomial.natDegree_toPoly, hsz]; omega))]
      apply Finset.sum_congr rfl; intro i _
      rw [Polynomial.coeff_map, AzPolynomial.coeff_toPoly]
    rw [← hrhs]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h1 | h2
      · exact absurd h1 (pow_ne_zero _ hfb)
      · exact h2
    · intro h; rw [h, mul_zero]

/-! ### Degree data over an integral domain -/

section Domain

variable {D : Type _} [CommRing D] [IsDomain D] [DecidableEq D]

/-- For `c ≠ 0` over a domain, `scaleRoots` preserves the degree (`b` may be
anything, including `0`). -/
theorem natDegree_scaleRoots (p : AzPolynomial D) (b : D) {c : D} (hc : c ≠ 0) :
    (p.scaleRoots b c).natDegree = p.natDegree := by
  rw [← AzPolynomial.natDegree_toPoly, toPoly_scaleRoots, Polynomial.natDegree_comp,
    Polynomial.natDegree_scaleRoots, AzPolynomial.natDegree_toPoly,
    Polynomial.natDegree_C_mul_X c hc, mul_one]

/-- For `c ≠ 0` over a domain, the leading coefficient of `scaleRoots p b c` is
`lcof(P) · c^(deg P)`. -/
theorem leadingCoeff_scaleRoots (p : AzPolynomial D) (b : D) {c : D} (hc : c ≠ 0) :
    (p.scaleRoots b c).leadingCoeff = p.leadingCoeff * c ^ p.natDegree := by
  rw [← leadingCoeff_toPoly, toPoly_scaleRoots,
    Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_C_mul_X c hc]; exact one_ne_zero),
    Polynomial.leadingCoeff_scaleRoots, Polynomial.leadingCoeff_C_mul_X,
    Polynomial.natDegree_scaleRoots, leadingCoeff_toPoly, AzPolynomial.natDegree_toPoly]

/-- For `p ≠ 0` and `c ≠ 0` over a domain, `scaleRoots p b c ≠ 0`. -/
theorem scaleRoots_ne_zero {p : AzPolynomial D} (hp : p ≠ 0) (b : D) {c : D} (hc : c ≠ 0) :
    p.scaleRoots b c ≠ 0 := by
  intro h
  have hlc := leadingCoeff_scaleRoots p b hc
  rw [h] at hlc
  have hlp : p.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_toPoly]
    exact Polynomial.leadingCoeff_ne_zero.mpr
      (fun hz => hp (toPoly_inj.mp (hz.trans toPoly_zero.symm)))
  exact mul_ne_zero hlp (pow_ne_zero _ hc)
    (by rw [← hlc]; rw [show (0 : AzPolynomial D).leadingCoeff = 0 from rfl])

end Domain

end Azurite.AzPolynomial
