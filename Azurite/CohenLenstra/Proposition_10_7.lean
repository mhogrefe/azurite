/-
  **Cohen–Lenstra Propositions (10.7) and (10.8): condition (6.4)
  from the second method — and the `n ≡ 7 (mod 8)` gap-filler.**

  (10.7): if the ring `F` of Method (10.3) exists with `β`
  satisfying the checks (10.4), then `p` satisfies condition (6.4).
  The paper's proof runs through [16, Theorem (8.4)] (Galois
  extensions of rank `f` of `ℤ/nℤ` with group `⟨ρ⟩`): with `s` the
  largest power of `p` dividing `n^f − 1` and `α = β^((n^f−1)/s)`,
  every divisor `r ∣ n` satisfies `r ≡ n^i (mod s)`; then
  `r·n^(−i) ∈ 1 + sℤ_p = (n^f)^(ℤ_p)` by (5.1), and (6.4) follows.

  In our architecture the [16, (8.4)]-role is played by the already
  formalized Crandall–Pomerance **Theorem 4.3.3** (Lenstra's
  divisor-confinement, `Azurite.CP.theorem_4_3_3`), which delivers
  exactly the confinement `r ≡ n^i (mod s)` for the concrete
  quotient models `F = (ℤ/n)[T]/(g)` that the algorithm uses.  We
  therefore formalize (10.7) as the *confinement-to-(6.4) bridge*
  (`proposition_10_7`): from `r ≡ n^i (mod s)` the finite (5.1)
  engine of Proposition (7.18) (`exists_pow_modEq_of_exact` and its
  2-adic variant — the latter needing `v_2(n^f−1) ≥ 2`, which is
  the formal content of the paper's "if `p = 2` and
  `n ≡ 3 mod 4`, suppose `k ≥ 2`") gives
  `r·n^(f−i) ≡ (n^f)^l (mod p^D)` at every depth, and an
  Euler-totient exponent shift removes the auxiliary factor without
  inverses.  The conclusion `∀ D, ∃ l, r ≡ n^l (mod p^D)` is the
  same (6.4)-shape as Propositions (7.24)/(7.25).  The fully
  abstract [16, (8.4)] (for a rank-`f` Galois ring extension given
  by cardinality) is not needed by the pipeline and is left
  unformalized.

  (10.8): for `n ≡ 3 (mod 4)`, `F = (ℤ/n)[T]/(T² − uT − 1)`,
  `ρ(ξ) = u − ξ = −ξ^(−1)`, the single check `ξ^(n+1) = −1`
  implies (6.4) at `p = 2` (`proposition_10_8`) — covering in
  particular `n ≡ 7 (mod 8)`, the residue that Propositions
  (7.24)/(7.25) leave open.  Following the paper this is (10.7) at
  `f = 2`, `β = ξ`, with the [16, (8.4)]-confinement supplied by
  Theorem 4.3.3 at `f₄.₃.₃ = T² − uT − 1`, `g = T`; the
  (10.4)-checks all *follow* from `ξ^(n+1) = −1` here:
  `ξ^(n²−1) = 1` since `n − 1` is even; `ξ^((n²−1)/2) = −1`
  since `(n−1)/2` is odd, so the half-power minus one is the unit
  `−2`; `ρ(ξ) = −ξ^(−1) = ξ^n`; and condition (3) holds because
  the symmetric functions of `{ξ, ξ^n}` are `ξ + ξ^n = u` and
  `ξ^(n+1) = −1`, both constants.  The hypothesis is stated
  polynomial-level as `(X² − uX − 1) ∣ X^(n+1) + 1` — no quotient
  ring is constructed.  The Lucas-function reading
  (`ξ^(n+1) = −1` ⟺ `V_((n+1)/2) ≡ 0 (mod n)`, cf. our
  Lucas–Lehmer arc) and the paper's closing exercises (deducing
  (10.8) from Lucas-function identities; the assumptions forcing
  `((u²+4)/n) = −1`) are prose-level remarks.
-/
import Azurite.CohenLenstra.Proposition_7_18
import Azurite.CrandallPomerance.Chapter4.Theorem_4_3_3

namespace Azurite

namespace CL

open Polynomial

/-- **Cohen–Lenstra Proposition (10.7)** (the confinement-to-(6.4)
bridge): if a divisor `r` of `n` is confined to `r ≡ n^i (mod s)`
with `s = p^(v_p(n^f−1))` the `p`-part of `n^f − 1` — as delivered
by the second method via Theorem 4.3.3 — then the finite (5.1)
engine yields the full condition (6.4) for `p`: `r` is a power of
`n` mod `p^D` for every depth `D`.  For `p = 2` the engine needs
`v_2(n^f − 1) ≥ 2` (the paper's `k ≥ 2` proviso for
`n ≡ 3 mod 4`). -/
theorem proposition_10_7 {p n f : ℕ} (hp : p.Prime) (hn1 : 1 < n)
    (hpn : ¬ p ∣ n) (hf : 0 < f) (hpd : p ∣ n ^ f - 1)
    (hc2 : p = 2 → 2 ≤ (n ^ f - 1).factorization p)
    {r : ℕ}
    (hconf : ∃ i < f, r ≡ n ^ i [MOD p ^ (n ^ f - 1).factorization p]) :
    ∀ D : ℕ, ∃ l : ℕ, r ≡ n ^ l [MOD p ^ D] := by
  set c := (n ^ f - 1).factorization p with hc
  have hnf1 : 1 < n ^ f := Nat.one_lt_pow hf.ne' hn1
  have hN0 : n ^ f - 1 ≠ 0 := by omega
  have hc1 : 1 ≤ c := hp.factorization_pos_of_dvd hN0 hpd
  have hpnf : ¬ p ∣ n ^ f := fun hd => hpn (hp.dvd_of_dvd_pow hd)
  -- exact valuation of `n^f − 1`
  have hdvdc : p ^ c ∣ n ^ f - 1 := Nat.ordProj_dvd _ p
  have hexact1 : (p : ℤ) ^ c ∣ (n ^ f : ℤ) - 1 := by
    have hd := Int.natCast_dvd_natCast.mpr hdvdc
    rwa [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_pow,
      Nat.cast_one] at hd
  have hexact2 : ¬ (p : ℤ) ^ (c + 1) ∣ (n ^ f : ℤ) - 1 := by
    intro hd
    refine Nat.pow_succ_factorization_not_dvd hN0 hp ?_
    have hd' : ((p ^ (c + 1) : ℕ) : ℤ) ∣ ((n ^ f - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_pow,
        Nat.cast_one]
      exact_mod_cast hd
    exact_mod_cast hd'
  obtain ⟨i, hif, hri⟩ := hconf
  -- `b = r·n^(f−i) ≡ 1 (mod p^c)`
  have hbmod : r * n ^ (f - i) ≡ 1 [MOD p ^ c] := by
    have h1 : r * n ^ (f - i) ≡ n ^ i * n ^ (f - i) [MOD p ^ c] :=
      hri.mul_right _
    rw [← pow_add, show i + (f - i) = f from by omega] at h1
    have h2 : n ^ f ≡ 1 [MOD p ^ c] :=
      ((Nat.modEq_iff_dvd' (by omega)).mpr hdvdc).symm
    exact h1.trans h2
  have hb : (p : ℤ) ^ c ∣ ((r * n ^ (f - i) : ℕ) : ℤ) - 1 := by
    have hd := Nat.ModEq.dvd hbmod.symm
    push_cast at hd ⊢
    exact hd
  -- the finite (5.1) engine
  have hengine : ∀ D, ∃ l,
      r * n ^ (f - i) ≡ (n ^ f) ^ l [MOD p ^ D] := by
    rcases eq_or_ne p 2 with rfl | hodd
    · exact exists_pow_modEq_of_exact_two (hc2 rfl) hpnf hexact1
        hexact2 hb
    · have hp3 : 2 < p := by
        have := hp.two_le
        omega
      exact exists_pow_modEq_of_exact hp hp3 hc1 hpnf hexact1
        hexact2 hb
  -- unwind the auxiliary factor with a totient shift
  intro D
  obtain ⟨l, hl⟩ := hengine D
  set T := (p ^ D).totient with hT
  have hTpos : 1 ≤ T := Nat.totient_pos.mpr (pow_pos hp.pos D)
  have hconp : Nat.Coprime n (p ^ D) :=
    Nat.Coprime.pow_right D ((hp.coprime_iff_not_dvd.mpr hpn).symm)
  have heuler : n ^ T ≡ 1 [MOD p ^ D] := Nat.ModEq.pow_totient hconp
  refine ⟨f * l + T * f - (f - i), ?_⟩
  have hexp : (f - i) + (f * l + T * f - (f - i)) = f * l + T * f := by
    have hle : f - i ≤ T * f :=
      le_trans (by omega) (Nat.le_mul_of_pos_left f hTpos)
    omega
  have hcanc : n ^ (f - i) * r
      ≡ n ^ (f - i) * n ^ (f * l + T * f - (f - i)) [MOD p ^ D] := by
    calc n ^ (f - i) * r
        = r * n ^ (f - i) := mul_comm _ _
      _ ≡ (n ^ f) ^ l [MOD p ^ D] := hl
      _ = n ^ (f * l) * 1 := by rw [← pow_mul, mul_one]
      _ ≡ n ^ (f * l) * (n ^ T) ^ f [MOD p ^ D] := by
          have hTf : (n ^ T) ^ f ≡ 1 ^ f [MOD p ^ D] := heuler.pow f
          rw [one_pow] at hTf
          exact hTf.symm.mul_left _
      _ = n ^ (f - i) * n ^ (f * l + T * f - (f - i)) := by
          rw [← pow_mul, ← pow_add, ← pow_add, hexp]
  have hcofn : Nat.Coprime (n ^ (f - i)) (p ^ D) :=
    Nat.Coprime.pow_left _ hconp
  exact Nat.ModEq.cancel_left_of_coprime
    (by rwa [Nat.Coprime, Nat.gcd_comm] at hcofn) hcanc

/-- **Cohen–Lenstra Proposition (10.8)**: for `n ≡ 3 (mod 4)` and
any `u`, if `ξ^(n+1) = −1` in `(ℤ/n)[T]/(T² − uT − 1)` — stated
polynomial-level as `(X² − uX − 1) ∣ X^(n+1) + 1` — then `p = 2`
satisfies condition (6.4): every prime `r ∣ n` is a power of `n`
mod `2^D` at every depth.  This covers `n ≡ 7 (mod 8)`, the
residue left open by Propositions (7.24)/(7.25). -/
theorem proposition_10_8 {n : ℕ} {u : ZMod n} (hn3 : n % 4 = 3)
    (hxi : (X ^ 2 - C u * X - 1 : Polynomial (ZMod n))
      ∣ X ^ (n + 1) + 1) :
    ∀ r : ℕ, r.Prime → r ∣ n → ∀ D : ℕ, ∃ l : ℕ,
      r ≡ n ^ l [MOD 2 ^ D] := by
  intro r hr hrn
  have hn1 : 1 < n := by omega
  have hnodd : ¬ 2 ∣ n := by omega
  have : Fact (1 < n) := ⟨hn1⟩
  have : NeZero n := ⟨by omega⟩
  obtain ⟨w, hw⟩ : ∃ w, n = 2 * w + 1 := ⟨n / 2, by omega⟩
  have hwodd : ¬ 2 ∣ w := by omega
  set fq : Polynomial (ZMod n) := X ^ 2 - C u * X - 1 with hfq
  set s := (n ^ 2 - 1).factorization 2 with hs
  have hnsq : 1 < n ^ 2 := Nat.one_lt_pow (by norm_num) hn1
  have hN0 : n ^ 2 - 1 ≠ 0 := by omega
  have hsqn : n ^ 2 = n * n := by ring
  have hnn : n * n = 4 * (w * w) + 4 * w + 1 := by
    rw [hw]
    ring
  -- `fq` is monic of degree 2
  have hfrw : fq = X ^ 2 - (C u * X + 1) := by
    rw [hfq]
    ring
  have hfmonic : fq.Monic := by
    rw [hfrw]
    have htail : degree (C u * X + (1 : Polynomial (ZMod n)))
        ≤ (1 : WithBot ℕ) := by
      rw [show (1 : Polynomial (ZMod n)) = C 1 from C_1.symm]
      exact degree_linear_le
    have hlt : (1 : WithBot ℕ) < ((2 : ℕ) : WithBot ℕ) := by
      exact_mod_cast (by norm_num : (1 : ℕ) < 2)
    exact monic_X_pow_sub (lt_of_le_of_lt htail hlt)
  have hfdeg : 0 < fq.natDegree := by
    have h2 : (2 : ℕ) ≤ fq.natDegree := by
      refine le_natDegree_of_ne_zero ?_
      have hc : fq.coeff 2 = 1 := by
        rw [hfq]
        simp [coeff_sub, coeff_X_pow, coeff_one]
      rw [hc]
      exact one_ne_zero
    omega
  -- (1): `ξ^(n²−1) = 1`
  have hsq2 : fq ∣ X ^ (2 * (n + 1)) - 1 := by
    refine hxi.trans ⟨X ^ (n + 1) - 1, ?_⟩
    have hpow : (X : Polynomial (ZMod n)) ^ (2 * (n + 1))
        = X ^ (n + 1) * X ^ (n + 1) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hpow]
    ring
  have hexpw : (2 * (n + 1)) * w = n ^ 2 - 1 := by
    have hh : (2 * (n + 1)) * w = 4 * (w * w) + 4 * w := by
      rw [hw]
      ring
    omega
  have h1 : fq ∣ X ^ (n ^ 2 - 1) - 1 := by
    refine hsq2.trans ?_
    have hchain := sub_dvd_pow_sub_pow
      ((X : Polynomial (ZMod n)) ^ (2 * (n + 1))) 1 w
    rw [one_pow, ← pow_mul, hexpw] at hchain
    exact hchain
  -- (2): `ξ^((n²−1)/2) − 1 = −2`, a unit
  have hhalfdvd : fq ∣ X ^ ((n ^ 2 - 1) / 2) + 1 := by
    have hoddw : Odd w := Nat.odd_iff.mpr (by omega)
    have hdvd2 := Odd.add_dvd_pow_add_pow
      ((X : Polynomial (ZMod n)) ^ (n + 1)) 1 hoddw
    rw [one_pow, ← pow_mul] at hdvd2
    have hexp2 : (n + 1) * w = (n ^ 2 - 1) / 2 := by
      have hh : (n + 1) * w = 2 * (w * w) + 2 * w := by
        rw [hw]
        ring
      omega
    rw [hexp2] at hdvd2
    exact hxi.trans hdvd2
  have hu2 : IsUnit (-2 : ZMod n) := by
    refine IsUnit.neg ?_
    have hco : Nat.Coprime 2 n :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnodd
    have hiu := (ZMod.isUnit_iff_coprime 2 n).mpr hco
    have hcast : ((2 : ℕ) : ZMod n) = (2 : ZMod n) := by norm_cast
    rwa [hcast] at hiu
  have hcop2 : IsCoprime (X ^ ((n ^ 2 - 1) / 2) - 1) fq := by
    obtain ⟨Q, hQ⟩ := hhalfdvd
    have heq : X ^ ((n ^ 2 - 1) / 2) - 1 = -2 + fq * Q := by
      linear_combination hQ
    rw [heq]
    refine IsCoprime.add_mul_left_left ?_ Q
    obtain ⟨vu, hvu⟩ := hu2.exists_left_inv
    refine ⟨C vu, 0, ?_⟩
    have hC2 : (-2 : Polynomial (ZMod n)) = C (-2) := by
      rw [map_neg, map_ofNat]
    rw [zero_mul, add_zero, hC2, ← C_mul, hvu, C_1]
  -- (3): the symmetric functions of `{ξ, ξ^n}` are constants
  have hXcop : IsCoprime (X : Polynomial (ZMod n)) fq :=
    ⟨X - C u, -1, by rw [hfq]; ring⟩
  have he1 : fq ∣ X ^ n + X - C u := by
    have hkey : X * (X ^ n + X - C u) = (X ^ (n + 1) + 1) + fq := by
      rw [hfq]
      ring
    have hd : fq ∣ X * (X ^ n + X - C u) := by
      rw [hkey]
      exact dvd_add hxi dvd_rfl
    exact hXcop.symm.dvd_of_dvd_mul_left hd
  have he2 : fq ∣ X ^ (n + 1) - C (-1 : ZMod n) := by
    have hC1 : (X ^ (n + 1) - C (-1 : ZMod n) : Polynomial (ZMod n))
        = X ^ (n + 1) + 1 := by
      rw [map_neg, C_1]
      ring
    rw [hC1]
    exact hxi
  have h3 : ∀ k : ℕ, 1 ≤ k → k ≤ 2 → ∃ c : ZMod n,
      fq ∣ ((Multiset.range 2).map
        fun j => (X : Polynomial (ZMod n)) ^ n ^ j).esymm k - C c := by
    intro k hk1 hk2
    interval_cases k
    · refine ⟨u, ?_⟩
      have hes : ((Multiset.range 2).map
          fun j => (X : Polynomial (ZMod n)) ^ n ^ j).esymm 1
          = X ^ n + X := by
        simp [Multiset.esymm, Multiset.powersetCard_one,
          Multiset.range_succ, Multiset.range_zero, pow_one, pow_zero]
        ring
      rw [hes]
      exact he1
    · refine ⟨-1, ?_⟩
      have hes : ((Multiset.range 2).map
          fun j => (X : Polynomial (ZMod n)) ^ n ^ j).esymm 2
          = X ^ (n + 1) := by
        simp [Multiset.esymm, Multiset.range_succ, Multiset.range_zero,
          Multiset.powersetCard_cons, Multiset.powersetCard_one,
          pow_one, pow_zero]
        exact (pow_succ X n).symm
      rw [hes]
      exact he2
  -- the confinement, via Theorem 4.3.3
  have hFdvd : 2 ^ s ∣ n ^ 2 - 1 := Nat.ordProj_dvd _ 2
  have h2cond : ∀ q : ℕ, q.Prime → q ∣ 2 ^ s →
      IsCoprime ((X : Polynomial (ZMod n)) ^ ((n ^ 2 - 1) / q) - 1)
        fq := by
    intro q hq hqs
    have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
        (hq.dvd_of_dvd_pow hqs)
    subst hq2
    exact hcop2
  have hconf := CP.theorem_4_3_3 hn1 (by norm_num) (pow_pos
    (by norm_num) s) hFdvd hfmonic hfdeg h1 h2cond h3 hr hrn
  -- assemble via (10.7)
  have hpd : 2 ∣ n ^ 2 - 1 := by omega
  have hc2 : (2 : ℕ) = 2 → 2 ≤ (n ^ 2 - 1).factorization 2 := by
    intro _
    obtain ⟨a, ha⟩ : ∃ a, w = 2 * a + 1 := ⟨w / 2, by omega⟩
    have hww : w * w = 2 * (2 * (a * a) + 2 * a) + 1 := by
      rw [ha]
      ring
    have h8 : 2 ^ 3 ∣ n ^ 2 - 1 := by
      refine ⟨2 * (a * a) + 2 * a + a + 1, ?_⟩
      omega
    have h3le := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      hN0).mp h8
    omega
  have hgconv : ∀ j, (fun j => (X : Polynomial (ZMod n)) ^ n ^ j) j
      = (X : Polynomial (ZMod n)) ^ n ^ j := fun j => rfl
  rw [hs] at hconf
  exact proposition_10_7 Nat.prime_two hn1 hnodd (by norm_num) hpd hc2
    hconf

end CL

end Azurite
