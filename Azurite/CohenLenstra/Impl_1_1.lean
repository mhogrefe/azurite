/-
  **Implementation paper, (1.1): preparation of tables — the
  improved version.**

  Deltas against the 1984 paper's (12.1) Step 1:

  (a) `t` is required *even*, and `e(t)` is given directly as
      `2·∏_{q−1∣t} q^(v_q(t)+1)` — our computable `e` (whose odd
      case never arises here).  The primes dividing `e(t)` are the
      "`q`-primes".  For `t = 55440` (Fortran): `e(t) = 4.920·10^106`
      rounded down (our guard in `Implementation_13.lean`), 44 odd
      `q`-primes, 213 digits; the unimplemented `e(t) > N^(1/3)`
      refinement would reach 320 digits.

  (b1) The same index table `f` with `1 − g^x ≡ g^(f(x))`, built
      from a discrete-log table (generator-side; certified by the
      defining property, as in our `jacobiSum_eq_sum_gen_pow`).

  (b2) **The tables now store only the raw Jacobi sums** — the
      `θ`/`α(v)`-powered tables of the 1984 version are gone (the
      powering moves into the per-`n` test, mod `n`).  Moreover the
      `p = 2, k ≥ 3` quantities are redefined:
      `j*_{2,q} = Σ ζ^(2x+f(x))` alone (so that
      `j*_(1987)·j_{2,q} = j*_(1984) = j(χ,χ,χ)`) and
      `j#_{2,q} = Σ ζ^(2^(k−3)(3x+f(x)))` unsquared (so
      `(j#_(1987))² = j#_(1984) = j(φ,φ³)²`).  All three sums are
      instances of our `jacobiSum_eq_sum_gen_pow`:
      `(a,b) = (1,1)` gives `j_{p,q} = j(χ,χ)`; `(2,1)` gives
      `j* = j(χ²,χ)`; `(3·2^(k−3), 2^(k−3))` gives `j# = j(φ³,φ)`.

  The incremental computation: represent `Σ aᵢζ^i` as the vector
  `(aᵢ)_{i<(p−1)p^(k−1)}` (our `cycMBasis`), and for each `x` add
  `ζ^(ax+bf(x))` reduced mod `Φ_{p^k}`: with
  `l = (ax + bf(x)) mod p^k`, either `l < (p−1)p^(k−1)` and
  `a_l += 1`, or `a_(l−i·p^(k−1)) −= 1` for `i = 1,…,p−1`.  The
  correctness core, proved here (`zeta_pow_eq_neg_sum`): for any
  root `z` of `Φ_{p^k}` in any commutative ring and any
  `l ≥ (p−1)p^(k−1)`,

    `z^l = −Σ_{i=1}^{p−1} z^(l − i·p^(k−1))`

  — the reduction rule of the vector algorithm, and the spec for
  the computable `Φ_{p^k}`-reduction kernel of the implementation
  phase.
-/
import Azurite.CohenLenstra.Method_10_3

namespace Azurite

namespace CL

open Polynomial

/-- **The cyclotomic reduction rule of (1.1)(b2)**: for a root `z`
of `Φ_(P^k)` and `l ≥ (P−1)P^(k−1)`,
`z^l = −Σ_{i=1}^{P−1} z^(l − i·P^(k−1))` — adding `ζ^l` to the
coefficient vector means decrementing the `P − 1` positions
`l − i·P^(k−1)`. -/
theorem zeta_pow_eq_neg_sum {R : Type _} [CommRing R] {P k : ℕ}
    (hp : P.Prime) (hk : 0 < k) {z : R}
    (hz : Polynomial.eval₂ (Int.castRingHom R) z
      (cyclotomic (P ^ k) ℤ) = 0)
    {l : ℕ} (hl : (P - 1) * P ^ (k - 1) ≤ l) :
    z ^ l = - ∑ i ∈ Finset.Icc 1 (P - 1), z ^ (l - i * P ^ (k - 1)) := by
  have hP1 : 1 < P := hp.one_lt
  -- the geometric-sum form of `Φ_(P^k)` evaluated at `z`
  have hcyc : cyclotomic (P ^ k) ℤ
      = ∑ i ∈ Finset.range P, (X ^ P ^ (k - 1)) ^ i := by
    have hgs := cyclotomic_prime_pow_eq_geom_sum (R := ℤ)
      (n := k - 1) hp
    rwa [show k - 1 + 1 = k from by omega] at hgs
  rw [hcyc, Polynomial.eval₂_finsetSum] at hz
  have hterm : ∀ i, Polynomial.eval₂ (Int.castRingHom R) z
      ((X ^ P ^ (k - 1)) ^ i) = z ^ (P ^ (k - 1) * i) := by
    intro i
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X_pow, ← pow_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i] at hz
  -- multiply by `z^(l − (P−1)P^(k−1))`
  have hmul : ∑ i ∈ Finset.range P,
      z ^ (l - (P - 1) * P ^ (k - 1) + P ^ (k - 1) * i) = 0 := by
    have h0 := congrArg (fun w => z ^ (l - (P - 1) * P ^ (k - 1)) * w) hz
    simp only [mul_zero, Finset.mul_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_add]
  -- split off the `i = P − 1` term, whose exponent is `l`
  have hsplit := Finset.sum_range_succ
    (fun i => z ^ (l - (P - 1) * P ^ (k - 1) + P ^ (k - 1) * i)) (P - 1)
  rw [show P - 1 + 1 = P from by omega] at hsplit
  rw [hsplit] at hmul
  have hlast : l - (P - 1) * P ^ (k - 1) + P ^ (k - 1) * (P - 1)
      = l := by
    have hcomm : P ^ (k - 1) * (P - 1) = (P - 1) * P ^ (k - 1) :=
      mul_comm _ _
    omega
  rw [hlast] at hmul
  have hmain : z ^ l
      = - ∑ i ∈ Finset.range (P - 1),
          z ^ (l - (P - 1) * P ^ (k - 1) + P ^ (k - 1) * i) := by
    linear_combination hmul
  rw [hmain]
  congr 1
  -- reindex `i ↦ P − 1 − i` onto `Icc 1 (P − 1)`
  refine Finset.sum_nbij' (fun i => P - 1 - i) (fun j => P - 1 - j)
    ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc]
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_range]
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    congr 1
    have hle : (P - 1 - i) * P ^ (k - 1) ≤ (P - 1) * P ^ (k - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have hexp : (P - 1) * P ^ (k - 1)
        = (P - 1 - i) * P ^ (k - 1) + i * P ^ (k - 1) := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have hswap : P ^ (k - 1) * i = i * P ^ (k - 1) := mul_comm _ _
    omega

end CL

end Azurite
