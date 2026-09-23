/-
  **The exponent alignment: from Theorem (7.8)'s `χ(r) = ζ^(f·m_r)` to
  Theorem (6.3)'s `χ(r) = χ(n)^(m_r)`** — phase B3 (Jacobi side).

  Theorem (7.8) delivers, for a prime `r ∣ n`, `χ(r) = ζ^(f·m_r)` where
  `m_r` is *any* exponent with `r^(p−1) ≡ (n^(p−1))^(m_r) (mod p^D)` at a
  sufficient depth `D`, and `f` depends only on the test data.  Theorem
  (6.3) wants `χ(r) = χ(n)^(m_r)` with the *same* `m_r` as in (6.4).  The
  bridge (`chi_eq_chi_pow`): writing `n = ∏ r^(e_r)`,
  `χ(n) = ∏ χ(r)^(e_r) = ζ^(f·M)` with `M = Σ e_r m_r`, and
  `(n^(p−1))^M ≡ n^(p−1) (mod p^D)`, so `(n^(p−1))^(M−1) ≡ 1`; since the
  order of `n^(p−1)` modulo `p^D` is at least `p^k` once
  `D ≥ v_p(n^(p−1) − 1) + k` (lifting the exponent,
  `pow_dvd_of_pow_modEq_one_odd`; for `p = 2`, `D ≥ v₂(n² − 1) + k`,
  `pow_dvd_of_pow_modEq_one_two`), `p^k ∣ M − 1` and
  `χ(n)^(m_r) = ζ^(f·M·m_r) = ζ^(f·m_r) = χ(r)`.

  Because one `m_r` (chosen at depth `D`) serves every `q` with `p ∣ q − 1`
  simultaneously, this is exactly the per-`(r, p)` hypothesis of
  `theorem_6_3_LL`: the (6.4) exponent and the (6.5) exponent coincide.
-/
import Azurite.CohenLenstra.Theorem_6_3_LL
import Mathlib.NumberTheory.Multiplicity

namespace Azurite

namespace CL

open Finset

/-! ### The order of `x` modulo `p^D` is at least `p^k` -/

/-- **Odd `p`**: `x ≡ 1 (mod p)`, `D ≥ v_p(x − 1) + k`, `x^j ≡ 1 (mod p^D)` ⟹
`p^k ∣ j` (lifting the exponent). -/
theorem pow_dvd_of_pow_modEq_one_odd {p x j k D : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx1 : 1 < x)
    (hxp : x ≡ 1 [MOD p]) (hD : padicValNat p (x - 1) + k ≤ D) (hj : x ^ j ≡ 1 [MOD p ^ D]) :
    p ^ k ∣ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · rw [hj0]
    exact dvd_zero _
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hxy : p ∣ x - 1 := (Nat.modEq_iff_dvd' hx1.le).mp hxp.symm
  have hx : ¬ p ∣ x := by
    intro hd
    have h1 : p ∣ x - (x - 1) := Nat.dvd_sub hd hxy
    rw [show x - (x - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hlte := padicValNat.pow_sub_pow hodd hx1 hxy hx hj0.ne'
  rw [one_pow] at hlte
  have hxj1 : 1 ≤ x ^ j := Nat.one_le_pow _ _ (by omega)
  have hxj : x ^ j - 1 ≠ 0 := by
    have : 1 < x ^ j := Nat.one_lt_pow hj0.ne' hx1
    omega
  have hdvd : p ^ D ∣ x ^ j - 1 := (Nat.modEq_iff_dvd' hxj1).mp hj.symm
  have hle : D ≤ padicValNat p (x ^ j - 1) := (padicValNat_dvd_iff_le hxj).mp hdvd
  rw [hlte] at hle
  have hk : k ≤ padicValNat p j := by omega
  exact (pow_dvd_pow p hk).trans pow_padicValNat_dvd

/-- **`p = 2`**: `x` odd, `D ≥ v₂(x + 1) + v₂(x − 1) + k`, `x^j ≡ 1 (mod 2^D)` ⟹
`2^k ∣ j` (lifting the exponent applied to the even exponent `2j`). -/
theorem pow_dvd_of_pow_modEq_one_two {x j k D : ℕ} (hx1 : 1 < x) (hxodd : x % 2 = 1)
    (hD : padicValNat 2 (x + 1) + padicValNat 2 (x - 1) + k ≤ D) (hj : x ^ j ≡ 1 [MOD 2 ^ D]) :
    2 ^ k ∣ j := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · rw [hj0]
    exact dvd_zero _
  have hj2 : x ^ (j * 2) ≡ 1 [MOD 2 ^ D] := by
    have := hj.pow 2
    rwa [one_pow, ← pow_mul] at this
  have hxy : 2 ∣ x - 1 := by omega
  have hx : ¬ 2 ∣ x := by omega
  have hlte := padicValNat.pow_two_sub_pow hx1 hxy hx (by omega : j * 2 ≠ 0) ⟨j, by ring⟩
  rw [one_pow] at hlte
  have hj2v : padicValNat 2 (j * 2) = padicValNat 2 j + 1 := by
    rw [padicValNat.mul hj0.ne' (by norm_num), padicValNat_self]
  have hxj1 : 1 ≤ x ^ (j * 2) := Nat.one_le_pow _ _ (by omega)
  have hxj : x ^ (j * 2) - 1 ≠ 0 := by
    have : 1 < x ^ (j * 2) := Nat.one_lt_pow (by omega) hx1
    omega
  have hdvd : 2 ^ D ∣ x ^ (j * 2) - 1 := (Nat.modEq_iff_dvd' hxj1).mp hj2.symm
  have hle : D ≤ padicValNat 2 (x ^ (j * 2) - 1) := (padicValNat_dvd_iff_le hxj).mp hdvd
  rw [hj2v] at hlte
  have hk : k ≤ padicValNat 2 j := by omega
  exact (pow_dvd_pow 2 hk).trans pow_padicValNat_dvd

/-! ### The alignment -/

/-- **The alignment theorem.**  Suppose `χ : (ℤ/qℤ)ˣ → R` and a primitive
`p^k`-th root of unity `ζ`, with `n > 1`, `p ∤ n`, and depth `D` such that
`(n^(p−1))^j ≡ 1 (mod p^D)` forces `p^k ∣ j`.  If for every prime `r ∣ n`
the exponent `m_r` satisfies (6.4) at depth `D` and Theorem (7.8)'s output
`χ(r) = ζ^(f·m_r)`, then `χ(r) = χ(n)^(m_r)` for every prime `r ∣ n`. -/
theorem chi_eq_chi_pow {R : Type _} [CommRing R] {q p k n D : ℕ} [Fact q.Prime]
    (hk : 0 < k) (hn1 : 1 < n) (hpn : ¬ p ∣ n) (hp : p.Prime)
    {χ : MulChar (ZMod q) R} {ζ : R} (hζ : IsPrimitiveRoot ζ (p ^ k))
    (hord : ∀ j, (n ^ (p - 1)) ^ j ≡ 1 [MOD p ^ D] → p ^ k ∣ j)
    {f : ℕ} {m : ℕ → ℕ}
    (hm : ∀ r ∈ n.primeFactors, r ^ (p - 1) ≡ (n ^ (p - 1)) ^ m r [MOD p ^ D])
    (hχ : ∀ r ∈ n.primeFactors, χ ((r : ℕ) : ZMod q) = ζ ^ (f * m r)) :
    ∀ r ∈ n.primeFactors, χ ((r : ℕ) : ZMod q) = χ ((n : ℕ) : ZMod q) ^ m r := by
  classical
  intro r hr
  have hn0 : n ≠ 0 := by omega
  have hprod : ∏ r' ∈ n.primeFactors, r' ^ n.factorization r' = n := by
    rw [← Nat.support_factorization, ← Finsupp.prod]
    exact Nat.prod_factorization_pow_eq_self hn0
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ r' ∈ n.primeFactors, n.factorization r' * m r' := ⟨_, rfl⟩
  -- `χ(n) = ζ^(f·M)`
  have hχn : χ ((n : ℕ) : ZMod q) = ζ ^ (f * M) := by
    conv_lhs => rw [← hprod]
    rw [Nat.cast_prod, map_prod]
    have h1 : ∀ r' ∈ n.primeFactors,
        χ (((r' ^ n.factorization r' : ℕ) : ZMod q)) = ζ ^ (f * (n.factorization r' * m r')) :=
      fun r' hr' => by
        rw [Nat.cast_pow, map_pow, hχ r' hr', ← pow_mul]
        congr 1
        ring
    rw [Finset.prod_congr rfl h1, Finset.prod_pow_eq_pow_sum, hM, Finset.mul_sum]
  -- `(n^(p−1))^M ≡ n^(p−1) (mod p^D)`
  have hnM : (((n ^ (p - 1)) : ℕ) : ZMod (p ^ D)) ^ M = ((n ^ (p - 1) : ℕ) : ZMod (p ^ D)) := by
    have h2 : ((n ^ (p - 1) : ℕ) : ZMod (p ^ D))
        = ∏ r' ∈ n.primeFactors, (((r' ^ (p - 1) : ℕ) : ZMod (p ^ D))) ^ n.factorization r' := by
      conv_lhs => rw [← hprod]
      rw [← Finset.prod_pow, Nat.cast_prod]
      refine Finset.prod_congr rfl fun r' _ => ?_
      rw [← pow_mul, mul_comm, pow_mul, Nat.cast_pow, Nat.cast_pow]
    have h3 : ∀ r' ∈ n.primeFactors,
        (((r' ^ (p - 1) : ℕ) : ZMod (p ^ D))) ^ n.factorization r'
          = ((n ^ (p - 1) : ℕ) : ZMod (p ^ D)) ^ (n.factorization r' * m r') := fun r' hr' => by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr (hm r' hr'), Nat.cast_pow, ← pow_mul,
        mul_comm]
    conv_rhs => rw [h2]
    rw [Finset.prod_congr rfl h3, Finset.prod_pow_eq_pow_sum, ← hM]
  -- `n^(p−1)` is a unit mod `p^D`, so `(n^(p−1))^(M−1) ≡ 1` and `p^k ∣ M − 1`
  have hunit : IsUnit ((n ^ (p - 1) : ℕ) : ZMod (p ^ D)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm).pow_right _
  obtain ⟨M', hM'⟩ : ∃ M', M = M' + 1 := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hnM
      have h1 : (n ^ (p - 1)) ^ 1 ≡ 1 [MOD p ^ D] := by
        rw [pow_one]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [Nat.cast_one]; exact hnM.symm)
      have := Nat.le_of_dvd one_pos (hord 1 h1)
      have : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
      omega
    · exact ⟨M - 1, by omega⟩
  have hM'1 : (n ^ (p - 1)) ^ M' ≡ 1 [MOD p ^ D] := by
    rw [hM', pow_succ] at hnM
    have h1 : ((n ^ (p - 1) : ℕ) : ZMod (p ^ D)) ^ M' * ((n ^ (p - 1) : ℕ) : ZMod (p ^ D))
        = 1 * ((n ^ (p - 1) : ℕ) : ZMod (p ^ D)) := by
      rw [one_mul]
      exact hnM
    have := hunit.mul_right_cancel h1
    refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
    rw [Nat.cast_pow, Nat.cast_one]
    exact this
  obtain ⟨t, ht⟩ := hord M' hM'1
  -- conclude
  rw [hχ r hr, hχn, ← pow_mul, hM', ht]
  have : f * (p ^ k * t + 1) * m r = f * m r + p ^ k * (t * f * m r) := by ring
  rw [this, pow_add, pow_mul ζ (p ^ k), hζ.pow_eq_one, one_pow, mul_one]

end CL

end Azurite
