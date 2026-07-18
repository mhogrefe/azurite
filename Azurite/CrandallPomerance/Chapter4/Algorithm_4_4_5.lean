/-
  Crandall–Pomerance, Algorithm 4.4.5 (Gauss sums primality test) —
  the checker-semantics layer: the bridge lemmas by which COMPUTABLE
  checks discharge the hypotheses of
  `theorem_4_4_6_composite_tower` (and justify the algorithm's early
  "composite" verdicts).

  * `step2_composite_of_gcd` — the step-2 verdict: if
    `gcd(n, IF) > 1` and `n` is NOT a prime factor of `IF` (checked
    first), then `n` is composite.
  * `forall_mem_zpowers_of_pow_div_prime` — the primitive-root
    verification: `g^((q−1)/r) ≠ 1` for every prime `r ∣ q − 1`
    forces `ord g = q − 1`, so `g` generates `(Z_q)ˣ` — the `hgen`
    hypothesis from finitely many computable power checks.
  * `h5_of_forall_coprime_content` — the step-5 bridge: the
    algorithm's `p` gcd computations
    `gcd(n, c(H − ζ_p^j)) = 1` (`0 ≤ j < p`) yield the
    divisor-quantified NON-divisibility hypothesis `h5`, for ALL
    `j : ℕ` — the powers of `ζ_p` cycle with period `p`, and a
    common divisor `d` of `n` and the ring element would divide the
    content (Definition 4.4.4), hence the gcd.

  The step-3/4 checks bridge through
  `natCast_dvd_iff_dvd_content` directly (the congruence
  `G^(p^w u) ≡ ζ_p^l (mod n)` IS `n ∣ c(G^(p^w u) − ζ_p^l)`), and
  the step-6 table checks are decidable arithmetic.
-/
import Azurite.CrandallPomerance.Chapter4.Theorem_4_4_6_Tower

namespace Azurite

namespace CP

/-- **The step-2 composite verdict is sound**: `gcd(n, IF) > 1` for
`n` not a prime factor of `IF` (checked first) forces `n`
composite — a prime `n` with nontrivial gcd would divide `IF` and
so BE a prime factor. -/
theorem step2_composite_of_gcd {n I F : ℕ} (hIF : I * F ≠ 0)
    (hg : 1 < Nat.gcd n (I * F)) (hmem : n ∉ (I * F).primeFactors) :
    ¬n.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_left n (I * F)) with
    h1 | h1
  · omega
  · exact hmem (Nat.mem_primeFactors.mpr
      ⟨hp, h1 ▸ Nat.gcd_dvd_right n (I * F), hIF⟩)

/-- **The primitive-root verification is sound**: `g^((q−1)/r) ≠ 1`
for every prime `r ∣ q − 1` forces `ord g = q − 1 = #(Z_q)ˣ`, so `g`
generates — the `hgen` hypothesis of the correctness theorem from
finitely many computable power checks. -/
theorem forall_mem_zpowers_of_pow_div_prime {q : ℕ} [Fact q.Prime]
    {g : (ZMod q)ˣ}
    (h : ∀ r ∈ (q - 1).primeFactors, g ^ ((q - 1) / r) ≠ 1) :
    ∀ x, x ∈ Subgroup.zpowers g := by
  have hq := Fact.out (p := q.Prime)
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hq]
  have hpow : g ^ (q - 1) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one
  have hord : orderOf g = q - 1 := by
    refine orderOf_eq_of_pow_and_pow_div_prime
      (by have := hq.two_le; omega) hpow ?_
    intro r hr hdvd
    exact h r (Nat.mem_primeFactors.mpr
      ⟨hr, hdvd, by have := hq.two_le; omega⟩)
  have htop : Subgroup.zpowers g = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by
      rw [Nat.card_zpowers, hord, Nat.card_eq_fintype_card, hcard])
  intro x
  rw [htop]
  exact Subgroup.mem_top x

/-- **The step-5 bridge**: the algorithm's `p` computable gcd checks
`gcd(n, c(x − ζ_p^j)) = 1` (`0 ≤ j < p`) yield the
divisor-quantified non-divisibility hypothesis `h5` of the
correctness theorem, for ALL `j : ℕ` — the `ζ_p`-powers cycle with
period `p`, and a common divisor of `n` and the ring element would
divide the content. -/
theorem h5_of_forall_coprime_content {q p : ℕ} [Fact q.Prime]
    [Fact p.Prime] (hp : p ∈ (q - 1).primeFactors) {n : ℕ} (x : CycPQ p q)
    (h : ∀ j < p, Nat.Coprime n (content p q (x - zetaP p q ^ j))) :
    ∀ d, d ∣ n → 1 < d → ∀ j, ¬(d : CycPQ p q) ∣ x - zetaP p q ^ j := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpq : p ≠ q := by
    have hq2 := (Fact.out (p := q.Prime)).two_le
    have hle := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
    omega
  have hζ : IsPrimitiveRoot (zetaP p q) p := isPrimitiveRoot_zetaP p q hpq
  intro d hdn hd1 j hdvd
  have hper : zetaP p q ^ j = zetaP p q ^ (j % p) := by
    conv_lhs => rw [← Nat.div_add_mod j p, pow_add, pow_mul,
      hζ.pow_eq_one, one_pow, one_mul]
  rw [hper] at hdvd
  have hc : d ∣ content p q (x - zetaP p q ^ (j % p)) :=
    (natCast_dvd_iff_dvd_content p q d _).mp hdvd
  have hgcd : d ∣ Nat.gcd n (content p q (x - zetaP p q ^ (j % p))) :=
    Nat.dvd_gcd hdn hc
  rw [h (j % p) (Nat.mod_lt j hpp.pos)] at hgcd
  exact absurd (Nat.dvd_one.mp hgcd) (by omega)

end CP

end Azurite
