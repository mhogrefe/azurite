/-
  **Implementation paper, Remarks (5.6)–(5.9).**

  **(5.6)** Adding the test `r ≤ n^(1/2)` in step (l3) before `r ∣ n`
  (dividing only when it holds) is sound — `step5_prime_sqrt` below:
  the least prime factor of a composite `n` is `≤ n^(1/2) < s`, so it
  is met *as* a residue `n^j mod s` with `(n^j mod s)² ≤ n`, and the
  divisibility test at that `j` convicts.  The `t'·c_ftd` term of
  (5.5) may then be replaced by `t'·c_ftd·n^(1/2)/s` (only about a
  `n^(1/2)/s` fraction of the residues survive the size test), at a
  slight increase of `c_ftd` (prose; the spec-level `totalCost` keeps
  the paper's original term).

  **(5.7)** (5.5) may choose `t, s = s₁s₂` with an odd prime `p ∣ t`
  such that `p ∤ q − 1` for every prime `q ∣ s₂`.  Then `p ∣ s` with

    `v_p(s) = v_p(t) + v_p(n^(p−1) − 1)`

  — `remark_5_7` below, in both cases: `p ∣ F` (then
  `v_p(s₁) = v_p(t') + v_p(F)` by `padicValNat_s1`, and
  `v_p(F) = v_p(n² − 1) = v_p(n^(p−1) − 1)` by lifting the exponent,
  `padicValNat_pow_sub_one_eq_sq`) and `p ∣ s̄₂` (then
  `v_p(s₂) = v_p(n^(p−1) − 1) + v_p(t')` by `padicValNat_s2`), the
  other factor being coprime to `p`.  Removing `v_p(t)` factors `p`
  from both `s` and `t` does not change the set of residues that are
  powers of `n`, but the new `s` may fall below `n^(1/2)`, requiring
  (l3) to trial-divide all `r + i·s ≤ n^(1/2)` and the cost term to
  become `t'·c_ftd·n^(1/2)/s` again; not implemented by the authors
  (prose).

  **(5.8)** `t = 55440` covers `213` digits (our
  `Implementation_13.lean` guard); by (5.2) larger `n` are handled
  whenever enough prime divisors of `n² − 1` are found — the
  `s₁`-contribution (prose).

  **(5.9)** (H. W. Lenstra, not implemented): choose `s > n^(1/2)·t`
  (or `n^(1/2)` times any sufficiently large number); then one expects
  only one of the `t` candidate divisors in (l) to be `≤ n^(1/2)`, and
  at the cost of one size test per iteration most trial divisions are
  saved — the same soundness `step5_prime_sqrt` (prose; a rail option
  for our final trial division, likely important for larger `n`).
-/
import Azurite.CohenLenstra.Impl_5_2
import Azurite.CohenLenstra.Algorithm_12_1
import Mathlib.NumberTheory.Multiplicity

namespace Azurite

namespace CL

/-- **(5.6)/(5.9): the size-tested final trial division is sound.**
As `step5_prime`, but the sweep tests divisibility only for residues
`r = n^j mod s` with `r² ≤ n`: the least prime factor of a composite
`n` satisfies this, so it is still caught. -/
theorem step5_prime_sqrt {n s t : ℕ} (hn : 1 < n) (hs2 : n < s ^ 2)
    (h25 : ∀ r, r ∣ n → ∃ j < t, r ≡ n ^ j [MOD s])
    {i : ℕ} (hi1 : 1 ≤ i) (hri : n ^ i % s = 1)
    (hloop : ∀ j, 1 ≤ j → j < i → (n ^ j % s) ^ 2 ≤ n
      → ¬ (n ^ j % s ∣ n ∧ n ^ j % s < n)) :
    n.Prime := by
  have hs1 : 1 < s := by
    by_contra hc
    push Not at hc
    interval_cases s <;> simp_all
  by_contra hnp
  have hr := Nat.minFac_prime (by omega : n ≠ 1)
  have hrdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hrsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hrlt_s : n.minFac < s := by
    by_contra hc
    push Not at hc
    have := Nat.pow_le_pow_left hc 2
    omega
  have hrlt_n : n.minFac < n := by
    have h2 := hr.two_le
    have hsq : n.minFac ^ 2 = n.minFac * n.minFac := sq n.minFac
    nlinarith
  obtain ⟨j, hjt, hjcong⟩ := h25 n.minFac hrdvd
  have hni : n ^ i ≡ 1 [MOD s] := by
    unfold Nat.ModEq
    rw [hri, Nat.mod_eq_of_lt hs1]
  have hcyc : n.minFac ≡ n ^ (j % i) [MOD s] := by
    refine hjcong.trans ?_
    have hj' : j = i * (j / i) + j % i := (Nat.div_add_mod j i).symm
    calc n ^ j = (n ^ i) ^ (j / i) * n ^ (j % i) := by
          conv_lhs => rw [hj']
          rw [pow_add, pow_mul]
      _ ≡ 1 ^ (j / i) * n ^ (j % i) [MOD s] :=
          ((hni.pow _).mul_right _)
      _ = n ^ (j % i) := by rw [one_pow, one_mul]
  have hreq : n.minFac = n ^ (j % i) % s := by
    have hm := hcyc
    unfold Nat.ModEq at hm
    rwa [Nat.mod_eq_of_lt hrlt_s] at hm
  rcases Nat.eq_zero_or_pos (j % i) with h0 | h1
  · rw [h0, pow_zero, Nat.mod_eq_of_lt hs1] at hreq
    have := hr.one_lt
    omega
  · have hjmi : j % i < i := Nat.mod_lt _ (by omega)
    exact hloop (j % i) h1 hjmi (hreq ▸ hrsq) ⟨hreq ▸ hrdvd, hreq ▸ hrlt_n⟩

/-- The `p`-adic valuation of a product of distinct prime powers is
the exponent at `p`. -/
theorem padicValNat_prod_pow {p : ℕ} (hp : p.Prime) {S : Finset ℕ}
    (hS : ∀ q ∈ S, q.Prime) (e : ℕ → ℕ) (hpS : p ∈ S) :
    padicValNat p (∏ q ∈ S, q ^ e q) = e p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Finset.mul_prod_erase S _ hpS]
  have hrest0 : ∏ q ∈ S.erase p, q ^ e q ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq =>
      pow_ne_zero _ (hS q (Finset.mem_of_mem_erase hq)).ne_zero
  rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hrest0, padicValNat.prime_pow]
  have h0 : padicValNat p (∏ q ∈ S.erase p, q ^ e q) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hdvd
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
    have hq' := Finset.mem_erase.mp hq
    exact hq'.1 ((Nat.prime_dvd_prime_iff_eq hp (hS q hq'.2)).mp
      (hp.dvd_of_dvd_pow hpq)).symm
  omega

/-- `v_p(s₁) = v_p(t') + v_p(F) − [p = 2]` for `p ∣ F`. -/
theorem padicValNat_s1 {t' F p : ℕ} (hp : p ∈ F.primeFactors) :
    padicValNat p (s1 t' F) = s1Exp t' F p :=
  padicValNat_prod_pow (Nat.prime_of_mem_primeFactors hp)
    (fun _ hq => Nat.prime_of_mem_primeFactors hq) _ hp

/-- The `q`-part of `s₂` as a power of `q`. -/
theorem s2Part_eq_pow (t' n q : ℕ) :
    s2Part t' n q
      = q ^ (if q ∣ t' then padicValNat q (n ^ (q - 1) - 1) + padicValNat q t'
          else 1) := by
  unfold s2Part
  split_ifs <;> simp

/-- `v_q(s₂) = v_q(n^(q−1) − 1) + v_q(t')` if `q ∣ t'`, else `1`, for
`q ∣ s̄₂`. -/
theorem padicValNat_s2 {t' n s2bar q : ℕ} (hq : q ∈ s2bar.primeFactors) :
    padicValNat q (s2 t' n s2bar)
      = if q ∣ t' then padicValNat q (n ^ (q - 1) - 1) + padicValNat q t'
        else 1 := by
  simp only [s2, s2Part_eq_pow]
  exact padicValNat_prod_pow (Nat.prime_of_mem_primeFactors hq)
    (fun _ hr => Nat.prime_of_mem_primeFactors hr) _ hq

/-- **Lifting the exponent, equality form**: for an odd prime
`p ∣ n² − 1`, `v_p(n^(p−1) − 1) = v_p(n² − 1)` (the exponent
`(p−1)/2` is coprime to `p`). -/
theorem padicValNat_pow_sub_one_eq_sq {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 1 < n) (hpn : p ∣ n ^ 2 - 1) :
    padicValNat p (n ^ (p - 1) - 1) = padicValNat p (n ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hyx : 1 < n ^ 2 := by nlinarith
  have hx : ¬ p ∣ n ^ 2 := by
    intro h
    have h1 : p ∣ n ^ 2 - (n ^ 2 - 1) := Nat.dvd_sub h hpn
    rw [show n ^ 2 - (n ^ 2 - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hm0 : (p - 1) / 2 ≠ 0 := by omega
  have h2 : 2 ∣ p - 1 := by
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  have h := padicValNat.pow_sub_pow hodd hyx hpn hx hm0
  rw [one_pow, ← pow_mul, Nat.mul_div_cancel' h2] at h
  have h0 : padicValNat p ((p - 1) / 2) = 0 :=
    padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  rw [h, h0, add_zero]

/-- `s₁ ≠ 0`. -/
theorem s1_ne_zero {t' F : ℕ} : s1 t' F ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hq =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero

/-- `s₂ ≠ 0`. -/
theorem s2_ne_zero {t' n s2bar : ℕ} : s2 t' n s2bar ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun q hq => by
    rw [s2Part_eq_pow]
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero

/-- **Remark (5.7)**: for an odd prime `p ∣ t'` dividing `s = s₁s₂`
— either `p ∣ F` or `p ∣ s̄₂` — with the standing assumption
`v_p(F) = v_p(n² − 1)` and `F ∣ n² − 1`,

  `v_p(s) = v_p(t') + v_p(n^(p−1) − 1)`. -/
theorem remark_5_7 {n t' F s2bar p : ℕ} (hn : 1 < n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpt : p ∣ t') (hF0 : F ≠ 0) (hF : F ∣ n ^ 2 - 1)
    (hFp : padicValNat p F = padicValNat p (n ^ 2 - 1))
    (hs0 : s2bar ≠ 0) (hq : ∀ q ∈ s2bar.primeFactors, ¬ q ∣ F)
    (hcase : p ∣ F ∨ p ∣ s2bar) :
    padicValNat p (s1 t' F * s2 t' n s2bar)
      = padicValNat p t' + padicValNat p (n ^ (p - 1) - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.mul s1_ne_zero s2_ne_zero]
  rcases hcase with hpF | hps
  · have hmem : p ∈ F.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpF, hF0⟩
    have h1 := padicValNat_s1 (t' := t') hmem
    rw [s1Exp, ite_eq_right hp2, Nat.sub_zero, hFp,
      ← padicValNat_pow_sub_one_eq_sq hp hp2 hn (hpF.trans hF)] at h1
    have h2 : padicValNat p (s2 t' n s2bar) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      exact hq p (Nat.mem_primeFactors.mpr
        ⟨hp, prime_dvd_s2bar_of_dvd_s2 hp hd, hs0⟩) hpF
    omega
  · have hmem : p ∈ s2bar.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hps, hs0⟩
    have h2 := padicValNat_s2 (t' := t') (n := n) hmem
    rw [ite_eq_left hpt] at h2
    have h1 : padicValNat p (s1 t' F) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      exact hq p hmem (prime_dvd_F_of_dvd_s1 hp hd)
    omega

end CL

end Azurite
