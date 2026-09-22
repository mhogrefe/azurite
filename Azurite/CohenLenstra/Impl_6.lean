/-
  **Implementation paper, §6 opening: pseudoprime tests with Jacobi
  sums — the arithmetic of `ℤ[ζ_{p^k}]/nℤ[ζ_{p^k}]`.**

  For a prime `q ∣ s₂`, a prime `p ∣ q − 1`, `k = v_p(q − 1)` (step
  (1.3)(i)) or `k = 1` (steps (j), (k)), and `m = (p − 1)p^(k−1)`, all
  computations of (1.3)(i) take place in `ℤ[ζ_{p^k}]/nℤ[ζ_{p^k}]`;
  when `flag_{p^k}` is true, (i2a) works in `ℤ/nℤ` after `λ` (end of
  §6).  An element `Σ_{i<m} a_i ζ^i` is the vector `(a_i)_{i<m}` with
  `a_i ∈ {0, …, n−1}`; addition/subtraction is componentwise mod `n`;
  multiplication is multiplication of polynomials of degree `< m`
  over `ℤ/nℤ` followed by reduction modulo the `p^k`-th cyclotomic
  polynomial `Σ_{i<p} X^(i·p^(k−1))`.

  Formalized here:

  * **The computation ring is `(ℤ/nℤ)[X]/(Φ_m)`** (`CycModN m n`),
    and it *is* the reduction of our abstract model:
    `cycM_quot_equiv : CycM m ⧸ (n) ≃+* CycModN m n` — so every
    congruence of the soundness chain, stated in `ℤ[ζ_m]` modulo an
    ideal containing `n`, is checked by equality in `CycModN m n`.
  * **Vectors of length `m`**: `CycModN (p^k) n` has the power basis
    `1, ζ, …, ζ^(m−1)` with `m = (p−1)p^(k−1)` (`cycModN_dim`, from
    Mathlib's `AdjoinRoot.powerBasis'` for the monic `Φ_{p^k}`) — the
    unique-representation claim behind the vector encoding.
  * **Multiplication = polynomial product mod `Φ`**
    (`mk_mul_modByMonic`, for any monic modulus), with `Φ_{p^k}` in
    the paper's shape `Σ_{i<p} X^(i·p^(k−1))`
    (`cyclotomic_prime_pow_eq_sum`); the coefficient-level reduction
    rule is `zeta_pow_eq_neg_sum` of `Impl_1_1.lean`.

  Cost notes (prose, for the rail): the schoolbook product needs `m²`
  integer multiplications; Winograd [4, p. 495] achieves `2m − 1` but
  with heavy overhead and was not implemented; instead hand-tuned
  per-`p^k` formulae for `p^k = 3, 4, 5, 7, 8, 9, 11, 16` (Appendix,
  awaited) improve on `m²` without reaching `2m − 1`.  The authors
  note a further saving: in auxiliary routine 3 the second call of
  routine 1 recomputes `a₂·b₂`, so three multiplications can be saved
  in the `p = 11` product and one in its squaring.  Our rail's options
  here are the `AzPolynomial` Karatsuba/Toom kernels over `AzZMod`
  with a dedicated `Φ_{p^k}`-reduction, to be compared against the
  Appendix formulae at benchmark time.
-/
import Azurite.CohenLenstra.Impl_5_6
import Azurite.CrandallPomerance.Chapter4.CycM
import Mathlib.Data.ZMod.QuotientRing

namespace Azurite

namespace CL

open Polynomial

/-- **The computation ring** `(ℤ/nℤ)[X]/(Φ_m)` of §6. -/
abbrev CycModN (m n : ℕ) := AdjoinRoot (cyclotomic m (ZMod n))

/-- **`ℤ[ζ_m]/nℤ[ζ_m] ≃ (ℤ/nℤ)[X]/(Φ_m)`**: the computation ring is the
reduction of the abstract model `CycM m` modulo `n`. -/
noncomputable def cycM_quot_equiv (m n : ℕ) :
    (CP.CycM m ⧸ Ideal.span {(n : CP.CycM m)}) ≃+* CycModN m n := by
  have hI : Ideal.span {(n : CP.CycM m)}
      = (Ideal.span {(n : ℤ)}).map (AdjoinRoot.of (cyclotomic m ℤ)) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  refine (Ideal.quotEquivOfEq hI).trans ?_
  refine (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot _ _).trans ?_
  refine Ideal.quotientEquiv _ _
    (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod n)) ?_
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  simp only [RingEquiv.coe_toRingHom, Polynomial.mapEquiv_apply,
    map_cyclotomic]

/-- **Vectors of length `m = (p−1)p^(k−1)`**: the power basis
`1, ζ, …, ζ^(m−1)` of `CycModN (p^k) n`. -/
theorem cycModN_dim {p k n : ℕ} [Fact (1 < n)] (hp : p.Prime) (hk : 0 < k) :
    (AdjoinRoot.powerBasis' (cyclotomic.monic (p ^ k) (ZMod n))).dim
      = (p - 1) * p ^ (k - 1) := by
  show (cyclotomic (p ^ k) (ZMod n)).natDegree = _
  rw [natDegree_cyclotomic, Nat.totient_prime_pow hp hk, mul_comm]

/-- **Multiplication is the polynomial product reduced modulo the
modulus**: `mk g · mk h = mk ((g·h) %ₘ f)` (for the monic `Φ_{p^k}`,
`%ₘ` is genuine polynomial remainder). -/
theorem mk_mul_modByMonic {R : Type _} [CommRing R] (f g h : Polynomial R) :
    AdjoinRoot.mk f g * AdjoinRoot.mk f h
      = AdjoinRoot.mk f ((g * h) %ₘ f) := by
  rw [← map_mul, AdjoinRoot.mk_eq_mk]
  have hdiv := Polynomial.modByMonic_add_div (g * h) f
  exact ⟨(g * h) /ₘ f, by linear_combination (-1 : Polynomial R) * hdiv⟩

/-- **The modulus in the paper's shape**: `Φ_{p^k} = Σ_{i<p} X^(i·p^(k−1))`. -/
theorem cyclotomic_prime_pow_eq_sum {R : Type _} [CommRing R] {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    cyclotomic (p ^ k) R = ∑ i ∈ Finset.range p, X ^ (i * p ^ (k - 1)) := by
  have h := cyclotomic_prime_pow_eq_geom_sum (R := R) (n := k - 1) hp
  rw [show k - 1 + 1 = k by omega] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul, mul_comm]

end CL

end Azurite
