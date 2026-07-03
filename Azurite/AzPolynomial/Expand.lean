import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Eval
import Azurite.AzPolynomial.Parse

/-!
# nth-Root Substitution (Expansion)

Computes `P(X^n)` for a univariate polynomial `P ∈ R[X]` — Mathlib's
`Polynomial.expand`. The roots of the result are the `n`-th roots of the roots
of `P`: `z` is a root of `P(X^n)` iff `z^n` is a root of `P`.

Implemented directly on the coefficient array: coefficient `aᵢ` moves to index
`n·i` and all other entries are `0`, an `O(n · deg P)` construction (linear in
the size of the output). The leading coefficient moves to the last position, so
the trailing-nonzero invariant is preserved without renormalizing. The
degenerate case `n = 0` follows Mathlib's convention `P(X^0) = C (P(1))`.

## Main definitions

- `AzPolynomial.expand p n` — computes `P(X^n)`

The coefficient formula is proved here; the `toPoly` bridge (to Mathlib's
`Polynomial.expand`), the root property, and the degree data live in
`Equiv/Expand.lean`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

omit [DecidableEq R] in
/-- The last coefficient of a nonempty coefficient array is nonzero. -/
private theorem coeff_last_ne_zero (p : AzPolynomial R) (hp : p.coeffs.size ≠ 0) :
    p.coeff (p.coeffs.size - 1) ≠ 0 := by
  intro h
  apply p.last_ne_zero
  show p.coeffs[p.coeffs.size - 1]? = some 0
  rw [Array.getElem?_eq_getElem (by omega)]
  congr 1
  rw [show p.coeff (p.coeffs.size - 1) = (p.coeffs[p.coeffs.size - 1]?).getD 0 from rfl,
    Array.getElem?_eq_getElem (by omega)] at h
  exact h

/-- **nth-root substitution.** Computes `P(X^n)` by spreading the coefficients:
`aᵢ` moves to index `n·i`. The roots of the result are the `n`-th roots of the
roots of `P`. For `n = 0` this is `C (P(1))`, matching `Polynomial.expand`. -/
def expand (p : AzPolynomial R) (n : ℕ) : AzPolynomial R :=
  if hp : p.coeffs.size = 0 then 0
  else if hn : n = 0 then C (p.eval 1)
  else ⟨Array.ofFn (fun j : Fin ((p.coeffs.size - 1) * n + 1) =>
      if n ∣ j.val then p.coeff (j.val / n) else 0), by
    intro h
    unfold Array.back? at h
    rw [Array.size_ofFn, Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; omega)] at h
    have h' := Option.some.inj h
    rw [Array.getElem_ofFn] at h'
    simp only [Nat.add_sub_cancel] at h'
    rw [if_pos (dvd_mul_left n _), Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn)] at h'
    exact coeff_last_ne_zero p hp h'⟩

@[simp] theorem zero_expand (n : ℕ) : (0 : AzPolynomial R).expand n = 0 := rfl

/-- The degenerate case: `P(X^0) = C (P(1))`, as in `Polynomial.expand`. -/
theorem expand_zero (p : AzPolynomial R) (hp : p ≠ 0) : p.expand 0 = C (p.eval 1) := by
  have hsz : p.coeffs.size ≠ 0 :=
    fun h => hp (AzPolynomial.ext (by rw [Array.size_eq_zero_iff.mp h]; rfl))
  rw [expand, dif_neg hsz, dif_pos rfl]

/-- The coefficient formula, matching Mathlib's `Polynomial.coeff_expand`:
`(expand p n).coeff j` is `p.coeff (j / n)` when `n ∣ j`, and `0` otherwise. -/
theorem coeff_expand (p : AzPolynomial R) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    (p.expand n).coeff j = if n ∣ j then p.coeff (j / n) else 0 := by
  rcases Nat.eq_zero_or_pos p.coeffs.size with hsz | hsz
  · rw [expand, dif_pos hsz]
    have hpc : ∀ m, p.coeff m = 0 := fun m => by
      show (p.coeffs[m]?).getD 0 = 0
      rw [Array.getElem?_eq_none (by omega)]; rfl
    rw [show (0 : AzPolynomial R).coeff j = 0 from rfl, hpc]
    split <;> rfl
  · rw [expand, dif_neg (by omega), dif_neg (by omega)]
    show ((Array.ofFn _)[j]?).getD 0 = _
    by_cases hj : j < (p.coeffs.size - 1) * n + 1
    · rw [Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
      simp only [Option.getD_some]
    · rw [Array.getElem?_eq_none (by rw [Array.size_ofFn]; omega)]
      show (0 : R) = _
      split
      · next hdvd =>
        obtain ⟨k, rfl⟩ := hdvd
        rw [Nat.mul_div_cancel_left k hn]
        have hk : p.coeffs.size ≤ k := by
          by_contra hlt
          have h2 : n * k ≤ (p.coeffs.size - 1) * n := by
            rw [Nat.mul_comm n k]
            exact Nat.mul_le_mul_right n (by omega)
          omega
        show _ = (p.coeffs[k]?).getD 0
        rw [Array.getElem?_eq_none (by omega)]
        rfl
      · rfl

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- x − 2 (root 2) expanded by 2: x² − 2 (roots ±√2)
#guard (parseAzPolynomial (R := AzInt) "x-2").get!.expand 2
    == (parseAzPolynomial (R := AzInt) "x^2-2").get!

-- (x−1)(x−2) expanded by 3: roots are the cube roots of 1 and 2
#guard (parseAzPolynomial (R := AzInt) "x^2-3*x+2").get!.expand 3
    == (parseAzPolynomial (R := AzInt) "x^6-3*x^3+2").get!

-- n = 1 is the identity
#guard (parseAzPolynomial (R := AzInt) "x^2+x+1").get!.expand 1
    == (parseAzPolynomial (R := AzInt) "x^2+x+1").get!

-- Constants unchanged
#guard (parseAzPolynomial (R := AzInt) "7").get!.expand 5
    == (parseAzPolynomial (R := AzInt) "7").get!

-- Zero unchanged
#guard (0 : AzPolynomial AzInt).expand 3 == 0

-- n = 0 degenerates to C (P(1)) — here P(1) = 0 and P(1) = 3 respectively
#guard (parseAzPolynomial (R := AzInt) "x^2-3*x+2").get!.expand 0 == 0
#guard (parseAzPolynomial (R := AzInt) "x^2-3*x+5").get!.expand 0
    == (parseAzPolynomial (R := AzInt) "3").get!

end Tests

end Azurite.AzPolynomial
