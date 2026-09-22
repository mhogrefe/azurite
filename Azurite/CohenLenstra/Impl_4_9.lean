/-
  **Implementation paper, Remarks (4.9)–(4.12): arithmetic in the
  quadratic ring, norm-one elements, and the `n ∓ 1`-only bounds.**

  **(4.9)** — the multiplication and squaring routines of
  `A = (ℤ/nℤ)[T]/(T² − uT − a)`, our rail's specs.  Writing
  `quadElt u a x₀ x₁ = x₀ + x₁α`:

  * the general product (`quadElt_mul`):
    `(x₀ + x₁α)(y₀ + y₁α) = (x₀y₀ + a·x₁y₁) + (x₀y₁ + x₁y₀ + u·x₁y₁)α`;
  * `n ≡ 1 (mod 4)`, `u = 0`: three multiplications instead of
    four (`quadElt_mul_c1`): `p₀ = x₀y₀`, `p₁ = x₁y₁`,
    `s₀ = x₀ + x₁`, `s₁ = y₀ + y₁`, `z₀ = p₀ + a·p₁`,
    `z₁ = s₀s₁ − p₀ − p₁` (Karatsuba);
  * `n ≡ 3 (mod 4)`, `a = 1` (`quadElt_mul_c2`): the same `p`'s
    and `s`'s, `z₀ = p₀ + p₁`, `z₁ = s₀s₁ + (u − 1)p₁ − p₀`;
  * the norm is multiplicative on coordinates
    (`quadNorm_mul_coords`) — so norm-one is preserved along an
    exponentiation, which is what licenses the next item;
  * *combined squaring for norm-one elements*
    (`quadElt_sq_of_quadNorm_one`): if `N(x₀ + x₁α) = 1` then
    `(x₀ + x₁α)² = (x₀x₁u + 2x₀² − 1) + (x₁²u + 2x₀x₁)α`, computed
    as `s = u·x₁ + 2x₀`, `z₀ = x₀s − 1`, `z₁ = x₁s` — two
    multiplications;
  * `α^(n+1)` in (4.4)(c2): `α` has norm `−1`, but
    `α² = uα + 1 = quadElt u 1 1 u` has norm one
    (`quadNorm_root_sq_c2`), and `α^(n+1) = (α²)^((n+1)/2)`
    (`root_pow_succ_eq_sq_pow`), so the norm-one routines apply.

  ("Multiple" = multiprecision integer; Section 7 awaited.)

  **(4.10)** — norm-one elements for Test (4.3): try
  `(α + m)/(ᾱ + m)` for `m ∈ {1, …, 50}`, with `ᾱ = u − α` (`−α`
  when `u = 0`).  Since `(α + m)(ᾱ + m) = N(m + α) = m(m + u) − a`
  (`quadNorm_m_one`), the quotient is
  `((m² + a) + (2m + u)α) / (m(m + u) − a)` —
  `norm_one_candidate_spec` is the cleared-denominator identity
  `(ᾱ + m)·((m² + a) + (2m + u)α) = (m(m + u) − a)·(α + m)`, and
  `quadNorm_norm_one_candidate` verifies norm one given an inverse
  `d` of the denominator.  The inverse "can be computed unless `n`
  is composite": for prime `n` the denominator is a unit
  (`norm_one_denominator_isUnit`), since `m(m + u) − a = 0` would
  make `u² + 4a = (2m + u)²` a square, against
  `((u² + 4a)/n) = −1` (`not_isSquare_disc`).  A non-unit
  denominator is thus a composite verdict (and a nonzero one yields
  a factor by gcd).

  **(4.11)** (prose): the trial cap `50` in (4.2), (4.3), (4.4)(c)
  is arbitrary but sufficient in practice ([2] before (10.4) and
  (11.6)) — the give-up branches of our `Option Bool` design.

  **(4.12)** (prose): `n ∓ 1`-only bounds.  If `f⁻ ≥ n^(1/2)`,
  step (4.4)(a) alone proves primality — our C&P Pocklington
  certificate `corollary_4_1_4` (`n ≤ F²`); if `f⁻ < n^(1/2) ≤ f⁻·B`,
  Test (4.2) with `p = r⁻` is also needed — the BLS-style
  `r⁻`-test of C&P §4.1.  The `n + 1` analogues are Morrison's
  `morrison_test` (`n < (F − 1)²`) and the cube-root test 4.2.8.
-/
import Azurite.CohenLenstra.Impl_4_5

namespace Azurite

namespace CL

open Polynomial

/-- **The coordinate element** `x₀ + x₁α ∈ A = R[T]/(T² − uT − a)`. -/
noncomputable def quadElt {R : Type _} [CommRing R] (u a x₀ x₁ : R) : QuadRing R u a :=
  algebraMap R (QuadRing R u a) x₀
    + algebraMap R (QuadRing R u a) x₁
      * AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial R)

/-- **The general product formula** of (4.9). -/
theorem quadElt_mul {R : Type _} [CommRing R] (u a x₀ x₁ y₀ y₁ : R) :
    quadElt u a x₀ x₁ * quadElt u a y₀ y₁
      = quadElt u a (x₀ * y₀ + a * (x₁ * y₁))
          (x₀ * y₁ + x₁ * y₀ + u * (x₁ * y₁)) := by
  have hrel := quadRing_root_sq u a
  simp only [quadElt, map_add, map_mul]
  linear_combination (algebraMap R (QuadRing R u a) x₁
    * algebraMap R (QuadRing R u a) y₁) * hrel

/-- **(4.9), `n ≡ 1 (mod 4)`, `u = 0`**: the three-multiplication
scheme `p₀ = x₀y₀`, `p₁ = x₁y₁`, `s₀ = x₀ + x₁`, `s₁ = y₀ + y₁`,
`z₀ = p₀ + a·p₁`, `z₁ = s₀s₁ − p₀ − p₁`. -/
theorem quadElt_mul_c1 {R : Type _} [CommRing R] (a x₀ x₁ y₀ y₁ : R) :
    quadElt 0 a x₀ x₁ * quadElt 0 a y₀ y₁
      = quadElt 0 a (x₀ * y₀ + a * (x₁ * y₁))
          ((x₀ + x₁) * (y₀ + y₁) - x₀ * y₀ - x₁ * y₁) := by
  rw [quadElt_mul]
  congr 1
  ring

/-- **(4.9), `n ≡ 3 (mod 4)`, `a = 1`**: `z₀ = p₀ + p₁`,
`z₁ = s₀s₁ + (u − 1)p₁ − p₀`. -/
theorem quadElt_mul_c2 {R : Type _} [CommRing R] (u x₀ x₁ y₀ y₁ : R) :
    quadElt u 1 x₀ x₁ * quadElt u 1 y₀ y₁
      = quadElt u 1 (x₀ * y₀ + x₁ * y₁)
          ((x₀ + x₁) * (y₀ + y₁) + (u - 1) * (x₁ * y₁) - x₀ * y₀) := by
  rw [quadElt_mul]
  congr 1 <;> ring

/-- **The norm is multiplicative** on coordinates — so norm-one
elements stay norm-one along an exponentiation. -/
theorem quadNorm_mul_coords {R : Type _} [CommRing R] (u a x₀ x₁ y₀ y₁ : R) :
    quadNorm u a (x₀ * y₀ + a * (x₁ * y₁))
        (x₀ * y₁ + x₁ * y₀ + u * (x₁ * y₁))
      = quadNorm u a x₀ x₁ * quadNorm u a y₀ y₁ := by
  simp only [quadNorm]
  ring

/-- **(4.9) combined squaring for norm-one elements**: with
`s = u·x₁ + 2x₀`, `(x₀ + x₁α)² = (x₀s − 1) + (x₁s)α`. -/
theorem quadElt_sq_of_quadNorm_one {R : Type _} [CommRing R]
    {u a x₀ x₁ : R} (h : quadNorm u a x₀ x₁ = 1) :
    quadElt u a x₀ x₁ ^ 2
      = quadElt u a (x₀ * (u * x₁ + 2 * x₀) - 1)
          (x₁ * (u * x₁ + 2 * x₀)) := by
  rw [quadNorm] at h
  rw [sq, quadElt_mul]
  congr 1
  · linear_combination -h
  · ring

/-- **(4.9), `α^(n+1)` in (4.4)(c2)**: `α² = uα + 1` has norm one. -/
theorem quadNorm_root_sq_c2 {R : Type _} [CommRing R] (u : R) :
    quadNorm u 1 1 u = 1 := by
  simp only [quadNorm]
  ring

/-- `α² = a + uα` as a coordinate element. -/
theorem root_sq_eq_quadElt {R : Type _} [CommRing R] (u a : R) :
    (AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial R)) ^ 2
      = quadElt u a a u := by
  rw [quadRing_root_sq, quadElt, add_comm]

/-- **(4.9)**: for odd `n`, `α^(n+1) = (α²)^((n+1)/2)`. -/
theorem root_pow_succ_eq_sq_pow {R : Type _} [CommRing R] (u a : R)
    {n : ℕ} (hodd : n % 2 = 1) :
    (AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial R)) ^ (n + 1)
      = ((AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial R)) ^ 2)
          ^ ((n + 1) / 2) := by
  rw [← pow_mul, Nat.mul_div_cancel' (by omega : 2 ∣ n + 1)]

/-- **(4.10)**: `N(m + α) = m(m + u) − a`, the denominator. -/
theorem quadNorm_m_one {R : Type _} [CommRing R] (u a m : R) :
    quadNorm u a m 1 = m * (m + u) - a := by
  simp only [quadNorm]
  ring

/-- **(4.10), the candidate identity** (denominators cleared):
`(ᾱ + m)·((m² + a) + (2m + u)α) = (m(m + u) − a)·(α + m)` with
`ᾱ = u − α`; so `(α + m)/(ᾱ + m) = ((m² + a) + (2m + u)α)/(m(m+u) − a)`. -/
theorem norm_one_candidate_spec {R : Type _} [CommRing R] (u a m : R) :
    (algebraMap R (QuadRing R u a) u
        - AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial R)
        + algebraMap R (QuadRing R u a) m)
      * quadElt u a (m ^ 2 + a) (2 * m + u)
      = algebraMap R (QuadRing R u a) (m * (m + u) - a)
        * (AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial R)
          + algebraMap R (QuadRing R u a) m) := by
  have hrel := quadRing_root_sq u a
  simp only [quadElt, map_add, map_sub, map_mul, map_pow, map_ofNat]
  linear_combination (-(2 * algebraMap R (QuadRing R u a) m
    + algebraMap R (QuadRing R u a) u)) * hrel

/-- **(4.10), norm one**: with `d` inverse to `m(m + u) − a`, the
element `(m² + a)d + (2m + u)d·α` has norm one. -/
theorem quadNorm_norm_one_candidate {R : Type _} [CommRing R]
    (u a m d : R) (hd : d * (m * (m + u) - a) = 1) :
    quadNorm u a ((m ^ 2 + a) * d) ((2 * m + u) * d) = 1 := by
  simp only [quadNorm]
  linear_combination (d * (m * (m + u) - a) + 1) * hd

/-- **(4.10), "unless `n` is composite"**: for prime `n` with a
nonsquare discriminant, the denominator `m(m + u) − a` is a unit of
`ℤ/nℤ` for every `m` — it vanishes only if `u² + 4a = (2m + u)²`
were a square.  Contrapositive: a non-unit denominator convicts `n`. -/
theorem norm_one_denominator_isUnit {n : ℕ} (hn : n.Prime) {u a : ZMod n}
    (hns : ¬ IsSquare (u ^ 2 + 4 * a)) (m : ZMod n) :
    IsUnit (m * (m + u) - a) := by
  haveI : Fact n.Prime := ⟨hn⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  apply hns
  refine ⟨2 * m + u, ?_⟩
  linear_combination (-4 : ZMod n) * h0

/-- **Injectivity of the coordinate representation** `x₀ + x₁α` in
`R[T]/(T² − uT − a)`: the power basis `1, α` of a monic quadratic. -/
theorem quadElt_injective {R : Type _} [CommRing R] [Nontrivial R] (u a : R)
    {x₀ x₁ y₀ y₁ : R} (h : quadElt u a x₀ x₁ = quadElt u a y₀ y₁) :
    x₀ = y₀ ∧ x₁ = y₁ := by
  have hmk : ∀ c d : R, quadElt u a c d
      = AdjoinRoot.mk (X ^ 2 - C u * X - C a) (C c + C d * X) := by
    intro c d
    rw [quadElt, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    rfl
  rw [hmk, hmk, AdjoinRoot.mk_eq_mk] at h
  have hfrw : (X ^ 2 - C u * X - C a : R[X]) = X ^ 2 - (C u * X + C a) := by ring
  have hfmonic : (X ^ 2 - C u * X - C a : R[X]).Monic := by
    rw [hfrw]
    exact monic_X_pow_sub (lt_of_le_of_lt degree_linear_le
      (by exact_mod_cast (by norm_num : (1 : ℕ) < 2)))
  have hfdeg : (X ^ 2 - C u * X - C a : R[X]).natDegree = 2 := by
    rw [hfrw, natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt natDegree_linear_le (by norm_num)
  have hg : (C x₀ + C x₁ * X - (C y₀ + C y₁ * X) : R[X])
      = C (x₁ - y₁) * X + C (x₀ - y₀) := by
    simp only [C_sub]
    ring
  rw [hg] at h
  by_cases hg0 : (C (x₁ - y₁) * X + C (x₀ - y₀) : R[X]) = 0
  · have h0 := congrArg (fun q : R[X] => q.coeff 0) hg0
    have h1 := congrArg (fun q : R[X] => q.coeff 1) hg0
    simp only [coeff_add, coeff_C_mul, coeff_X_zero, coeff_X_one, mul_zero, mul_one,
      coeff_C_zero, coeff_C_succ, zero_add, add_zero, coeff_zero] at h0 h1
    exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩
  · exfalso
    obtain ⟨c, hc⟩ := h
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact hg0 hc
    have hdeg := congrArg natDegree hc
    rw [hfmonic.natDegree_mul' hc0, hfdeg] at hdeg
    have hle : (C (x₁ - y₁) * X + C (x₀ - y₀) : R[X]).natDegree ≤ 1 := natDegree_linear_le
    omega

end CL

end Azurite
