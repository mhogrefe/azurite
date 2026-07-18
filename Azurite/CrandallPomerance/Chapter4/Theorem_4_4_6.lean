/-
  Crandall–Pomerance, Theorem 4.4.6 (correctness of the Gauss sums
  primality test, Algorithm 4.4.5) — the step-6 arithmetic layer:
  what remains of the composite direction once (4.23) has produced
  `r ≡ l^a (mod F)` for the least prime factor `r` of a surviving
  composite `n`.

  * `exists_forall_modEq_primes` — the CRT choice of the combined
    exponent: an `a` with `a ≡ a_p (mod p)` for every prime
    `p ∣ I` exists (distinct primes are pairwise coprime; via
    Mathlib's `Nat.chineseRemainderOfList` — the constructive
    algorithm behind it is `CP.garner`, Algorithm 2.1.7).
  * `l_pow_I_modEq_one` — the step-6 residue `l` satisfies
    `l^I ≡ 1 (mod F)`: mod each prime `q ∣ F` the residue is a
    unit, whose order divides `#(Z_q)ˣ = q − 1 ∣ I`.
  * `step6_finds_factor` — **the catch**: for composite `n < F²`
    with `r = minFac n ≡ l^a (mod F)` and `l^I ≡ 1 (mod F)`, the
    exponent reduces to `j = a mod I`, and `l^j mod F` IS `r` — a
    nontrivial divisor of `n` with `1 ≤ j < I`, so the step-6 scan
    finds it and correctly declares `n` composite.  (`j = 0` is
    impossible: it would force the prime `r` to equal `1`.)
-/
import Azurite.CrandallPomerance.Chapter4.Equation_4_23
import Mathlib.Data.Nat.ChineseRemainder

namespace Azurite

namespace CP

/-- The combined exponent exists: CRT across a finset of distinct
primes. -/
theorem exists_forall_modEq_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (v : ℕ → ℕ) : ∃ a, ∀ p ∈ s, a ≡ v p [MOD p] := by
  have hpair : s.toList.Pairwise (Function.onFun Nat.Coprime id) := by
    refine List.Pairwise.imp_of_mem ?_ s.nodup_toList
    intro a b ha hb hne
    exact (Nat.coprime_primes (hs a (Finset.mem_toList.mp ha))
      (hs b (Finset.mem_toList.mp hb))).mpr hne
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfList v id s.toList hpair
  exact ⟨a, fun p hp => ha p (Finset.mem_toList.mpr hp)⟩

/-- The step-6 residue satisfies `l^I ≡ 1 (mod F)`: mod each prime
`q ∣ F` it is a unit, whose order divides `#(Z_q)ˣ = q − 1 ∣ I`. -/
theorem l_pow_I_modEq_one {F I l : ℕ} (hFsq : Squarefree F)
    (hqI : ∀ q ∈ F.primeFactors, (q - 1) ∣ I)
    (hunit : ∀ q ∈ F.primeFactors, IsUnit ((l : ℕ) : ZMod q)) :
    l ^ I ≡ 1 [MOD F] := by
  refine modEq_of_forall_primeFactor hFsq fun q hq => ?_
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  haveI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨u, hu⟩ := hunit q hq
  obtain ⟨t, ht⟩ := hqI q hq
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [← hu, ht, pow_mul, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
  have hcard : u ^ (q - 1) = 1 := by
    have h := pow_card_eq_one (G := (ZMod q)ˣ) (x := u)
    rwa [ZMod.card_units_eq_totient, Nat.totient_prime hqprime] at h
  rw [hcard, one_pow, Units.val_one]

/-- **The step-6 catch**: for composite `n < F²` whose least prime
factor is `≡ l^a (mod F)`, with `l^I ≡ 1 (mod F)`, the residue
`l^(a mod I) mod F` IS the least prime factor — a nontrivial divisor
of `n` found by the scan over `1 ≤ j < I`. -/
theorem step6_finds_factor {n I F l a : ℕ} (hn1 : 1 < n)
    (hncomp : ¬n.Prime) (hI : 0 < I) (hnF : n < F ^ 2)
    (hpow : l ^ I ≡ 1 [MOD F])
    (hmod : n.minFac ≡ l ^ a [MOD F]) :
    ∃ j, 0 < j ∧ j < I ∧ l ^ j % F ∣ n ∧ 1 < l ^ j % F ∧ l ^ j % F < n := by
  have hrprime : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hrdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hrsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hncomp
  have hrF : n.minFac < F :=
    lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le F) (lt_of_le_of_lt hrsq hnF)
  -- reduce the exponent mod `I`
  have hred : l ^ a ≡ l ^ (a % I) [MOD F] := by
    conv_lhs => rw [← Nat.div_add_mod a I, pow_add, pow_mul]
    calc (l ^ I) ^ (a / I) * l ^ (a % I)
        ≡ 1 ^ (a / I) * l ^ (a % I) [MOD F] :=
        (hpow.pow (a / I)).mul_right _
      _ = l ^ (a % I) := by rw [one_pow, one_mul]
  have hres : n.minFac = l ^ (a % I) % F := by
    have h := hmod.trans hred
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hrF] at h
  -- `j = 0` would force the prime `minFac n` to be `1`
  have hj0 : a % I ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Nat.mod_eq_of_lt (by
      have := hrprime.two_le
      omega : 1 < F)] at hres
    have := hrprime.one_lt
    omega
  have hrn : n.minFac < n := by
    have h2 := hrprime.two_le
    nlinarith [hrsq]
  exact ⟨a % I, Nat.pos_of_ne_zero hj0, Nat.mod_lt a hI,
    hres ▸ hrdvd, hres ▸ hrprime.one_lt, hres ▸ hrn⟩

/-- **The prime side of step 3**: for prime `n` the probable-prime
search always succeeds — `w = s_p` works, since
`G^(p^(s_p) u_p) = G^(n^(p−1)−1) ≡ χ(n) (mod n)` by Lemma 4.4.2 and
`χ(n)` is a `ζ_p`-power.  (Its contrapositive is the soundness of
the step-3 "composite" verdict.) -/
theorem step3_succeeds_of_prime {q p n s u : ℕ} [Fact q.Prime]
    (hp : p.Prime) (hn : n.Prime) (hgcd : Nat.Coprime (p * q) n)
    {R : Type _} [CommRing R] [IsDomain R]
    {ζp : Rˣ} (hζp : IsPrimitiveRoot ζp p)
    (hζmem : ζp ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {ζq : R} (hζq : IsPrimitiveRoot ζq q)
    (hfact : p ^ s * u = n ^ (p - 1) - 1) :
    ∃ j, (n : R) ∣ gaussSum (MulChar.ofRootOfUnity hζmem hg)
        (AddChar.zmodChar q hζq.pow_eq_one) ^ (p ^ s * u)
      - (ζp : R) ^ j := by
  rw [hfact]
  exact lemma_4_4_2_zeta_pow hp hn hgcd hζp hζmem hg hζq

/-- **Theorem 4.4.6, the composite direction**: a composite `n`
surviving steps 1–5 of Algorithm 4.4.5 is factored by the step-6
divisor search.  The certificate data enters per prime `q ∣ F`
through the ring `R q` (in practice `ℤ[ζ_(q−1), ζ_q]`): primitive
roots, the generator `g_q`, ℤ-faithfulness, the step-3/4
congruences at exponent `p^(w(p)) u_p`, the step-5 coprime check at
`q₀(p)`, and the step-6 tables `l(q)`, `l`.  The proof composes the
whole machinery against `r = minFac n`: per `p ∣ I` the (4.21)
engines and (4.22) produce `a_p, b_p` (at `q₀(p)`); the CRT picks
`a ≡ a_p (mod p)`; per pair the character value is pinned
(`eq_4_23_char`); per `q` the product-character engine gives
`r ≡ l^a (mod q)` (`eq_4_23_mod_q`); the congruences combine over
the squarefree `F`; and `step6_finds_factor` reports the factor. -/
theorem theorem_4_4_6_composite
    {n I F : ℕ} (hn1 : 1 < n) (hncomp : ¬n.Prime)
    (hI : Squarefree I) (hF : Squarefree F)
    (hqI : ∀ q ∈ F.primeFactors, (q - 1) ∣ I)
    (hgcd : Nat.Coprime (I * F) n) (hnF : n < F ^ 2)
    {w u : ℕ → ℕ}
    (hw : ∀ p ∈ I.primeFactors, 0 < w p)
    (hu : ∀ p ∈ I.primeFactors, ¬p ∣ u p)
    {lTab : ℕ → ℕ → ℕ} {lq : ℕ → ℕ} {l : ℕ} {q₀ : ℕ → ℕ}
    (hq₀ : ∀ p ∈ I.primeFactors, q₀ p ∈ F.primeFactors ∧ p ∣ q₀ p - 1)
    {R : ℕ → Type _} [∀ q, CommRing (R q)]
    (hdom : ∀ q ∈ F.primeFactors, IsDomain (R q))
    {ζP : (q : ℕ) → ℕ → (R q)ˣ} {ζQ : (q : ℕ) → R q}
    {g : (q : ℕ) → (ZMod q)ˣ}
    (hdata : ∀ q, q ∈ F.primeFactors → ∀ [Fact q.Prime],
      ∃ (hζq : IsPrimitiveRoot (ζQ q) q)
        (hmem : ∀ p, ζP q p ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) (R q))
        (hgen : ∀ x, x ∈ Subgroup.zpowers (g q)),
        (∀ p ∈ (q - 1).primeFactors, IsPrimitiveRoot (ζP q p) p) ∧
        (∀ x y : ℕ, ((x : R q) ∣ (y : R q)) ↔ x ∣ y) ∧
        (∀ p ∈ (q - 1).primeFactors,
          (n : R q) ∣ gaussSum (MulChar.ofRootOfUnity (hmem p) hgen)
              (AddChar.zmodChar q hζq.pow_eq_one) ^ (p ^ w p * u p)
            - (ζP q p : R q) ^ lTab p q) ∧
        (∀ p ∈ (q - 1).primeFactors, q₀ p = q →
          ∀ d, d ∣ n → 1 < d → ∀ j,
            ¬(d : R q) ∣ gaussSum (MulChar.ofRootOfUnity (hmem p) hgen)
                (AddChar.zmodChar q hζq.pow_eq_one) ^ (p ^ (w p - 1) * u p)
              - (ζP q p : R q) ^ j) ∧
        (∀ p ∈ (q - 1).primeFactors, lq q ≡ lTab p q [MOD p]) ∧
        ((l : ℕ) : ZMod q) = ((g q ^ lq q : (ZMod q)ˣ) : ZMod q)) :
    ∃ j, 0 < j ∧ j < I ∧ l ^ j % F ∣ n ∧ 1 < l ^ j % F ∧ l ^ j % F < n := by
  have hrprime : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hrdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hIpos : 0 < I := Nat.pos_of_ne_zero hI.ne_zero
  -- coprimality of the certificate primes to `r`
  have hpq_co : ∀ p q', p ∣ I → q' ∣ F → Nat.Coprime (p * q') n.minFac :=
    fun p q' hpI hqF =>
      (hgcd.coprime_dvd_left (mul_dvd_mul hpI hqF)).coprime_dvd_right hrdvd
  have hnotdvd : ∀ p q', p ∣ I → q' ∣ F → ¬n.minFac ∣ p := by
    intro p q' hpI hqF hdvd
    have hco := hpq_co p q' hpI hqF
    have h1 : n.minFac ∣ Nat.gcd (p * q') n.minFac :=
      Nat.dvd_gcd (dvd_mul_of_dvd_left hdvd q') dvd_rfl
    rw [hco] at h1
    exact absurd (Nat.dvd_one.mp h1) (by have := hrprime.one_lt; omega)
  -- per `p ∣ I`: the (4.22) data, from the `q₀(p)` checks
  have hab : ∀ p ∈ I.primeFactors, ∃ a b,
      (n.minFac ^ (p - 1) - 1) * b = p ^ w p * u p * a
        ∧ b ≡ 1 [MOD p] := by
    intro p hp
    obtain ⟨hq₀mem, hq₀dvd⟩ := hq₀ p hp
    have hq'prime : (q₀ p).Prime := Nat.prime_of_mem_primeFactors hq₀mem
    haveI : Fact (q₀ p).Prime := ⟨hq'prime⟩
    haveI : IsDomain (R (q₀ p)) := hdom (q₀ p) hq₀mem
    obtain ⟨hζq, hmem, hgen, hprim, hfaith, hstep, h5, -, -⟩ :=
      hdata (q₀ p) hq₀mem
    have hpmem : p ∈ (q₀ p - 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hq₀dvd,
        by have := hq'prime.two_le; omega⟩
    have hco : Nat.Coprime (p * q₀ p) n.minFac :=
      hpq_co p (q₀ p) (Nat.dvd_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hq₀mem)
    have hrp : ¬((n.minFac : R (q₀ p)) ∣ (p : R (q₀ p))) := by
      rw [hfaith]
      exact hnotdvd p (q₀ p) (Nat.dvd_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hq₀mem)
    have hstepr : (n.minFac : R (q₀ p))
        ∣ gaussSum (MulChar.ofRootOfUnity (hmem p) hgen)
            (AddChar.zmodChar (q₀ p) hζq.pow_eq_one) ^ (p ^ w p * u p)
          - (ζP (q₀ p) p : R (q₀ p)) ^ lTab p (q₀ p) :=
      (Nat.cast_dvd_cast hrdvd).trans (hstep p hpmem)
    exact exists_eq_4_22_data (Nat.prime_of_mem_primeFactors hp) hrprime
      hco (hprim p hpmem) (hmem p) hgen hζq hrp (hu p hp) (hw p hp) hstepr
      (fun _ => h5 p hpmem rfl n.minFac hrdvd hrprime.one_lt)
  choose! aTab bTab hab1 hab2 using hab
  -- the combined exponent
  obtain ⟨a, ha⟩ := exists_forall_modEq_primes
    (fun p hp => Nat.prime_of_mem_primeFactors hp) aTab
  -- per `q ∣ F`: `r ≡ l^a (mod q)`
  have hqmod : ∀ q ∈ F.primeFactors, n.minFac ≡ l ^ a [MOD q] := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    haveI : Fact q.Prime := ⟨hqprime⟩
    haveI : IsDomain (R q) := hdom q hq
    obtain ⟨hζq, hmem, hgen, hprim, hfaith, hstep, -, hlq, hl⟩ :=
      hdata q hq
    have hsqf : Squarefree (q - 1) :=
      Squarefree.squarefree_of_dvd (hqI q hq) hI
    refine eq_4_23_mod_q (r := n.minFac) (l := l) (a := a) (lq := lq q)
      (e := fun p => lTab p q * aTab p) hsqf hmem hprim hgen ?_ ?_ hl ?_
    · -- the character values, per pair
      intro p hpmem
      have hpI : p ∈ I.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpmem,
          (Nat.dvd_of_mem_primeFactors hpmem).trans (hqI q hq), hI.ne_zero⟩
      have hco : Nat.Coprime (p * q) n.minFac :=
        hpq_co p q (Nat.dvd_of_mem_primeFactors hpI)
          (Nat.dvd_of_mem_primeFactors hq)
      have hrp : ¬((n.minFac : R q) ∣ (p : R q)) := by
        rw [hfaith]
        exact hnotdvd p q (Nat.dvd_of_mem_primeFactors hpI)
          (Nat.dvd_of_mem_primeFactors hq)
      have hstepr : (n.minFac : R q)
          ∣ gaussSum (MulChar.ofRootOfUnity (hmem p) hgen)
              (AddChar.zmodChar q hζq.pow_eq_one) ^ (p ^ w p * u p)
            - (ζP q p : R q) ^ lTab p q :=
        (Nat.cast_dvd_cast hrdvd).trans (hstep p hpmem)
      exact eq_4_23_char (Nat.prime_of_mem_primeFactors hpmem) hrprime hco
        (hprim p hpmem) (hmem p) hgen hζq hrp (hab1 p hpI) (hab2 p hpI)
        hstepr
    · -- the exponent congruences
      intro p hpmem
      have hpI : p ∈ I.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpmem,
          (Nat.dvd_of_mem_primeFactors hpmem).trans (hqI q hq), hI.ne_zero⟩
      exact Nat.ModEq.mul (hlq p hpmem).symm (ha p hpI).symm
    · -- `r` is a unit mod `q`
      rw [ZMod.isUnit_iff_coprime]
      exact ((hgcd.coprime_dvd_left (dvd_mul_of_dvd_right
        (Nat.dvd_of_mem_primeFactors hq) I)).coprime_dvd_right hrdvd).symm
  -- combine over `F` and catch the factor
  have hlunit : ∀ q ∈ F.primeFactors, IsUnit ((l : ℕ) : ZMod q) := by
    intro q hq
    haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    obtain ⟨-, -, -, -, -, -, -, -, hl⟩ := hdata q hq
    rw [hl]
    exact (g q ^ lq q).isUnit
  exact step6_finds_factor hn1 hncomp hIpos hnF
    (l_pow_I_modEq_one hF hqI hlunit)
    (modEq_of_forall_primeFactor hF hqmod)

end CP

end Azurite
