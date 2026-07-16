/-
  Crandall–Pomerance, Theorem 4.2.3 (Morrison): the `n + 1` analogue of
  Pocklington.  Let `f, Δ` be as in (4.12), `n` positive with
  `gcd(n, 2b) = 1` and Jacobi symbol `(Δ/n) = −1`.  If `F ∣ n + 1` and

    `U_{n+1} ≡ 0 (mod n)`,  `gcd(U_{(n+1)/q}, n) = 1` for every prime
    `q ∣ F`,                                                    (4.14)

  then every prime `p ∣ n` satisfies `p ≡ (Δ/p) (mod F)`.  In
  particular, if `F > √n + 1`, then `n` is prime.

  Proof shape (the book's, expanded): for a prime `p ∣ n`, conditions
  (4.14) force `F ∣ r_f(p)` — the rank divides `n + 1` but no
  `(n+1)/q`, so each `q^{v_q(F)}` divides it (the same valuation climb
  as in Pocklington's proof, with the rank of appearance playing the
  role of the multiplicative order).  Theorem 4.2.2 gives
  `r_f(p) ∣ p − (Δ/p)`, whence `F ∣ p − (Δ/p)`.  For the primality
  claim: a composite `n` has a prime factor `p ≤ √n < F − 1`, but
  `p ≡ ±1 (mod F)` and `p ≥ 2` force `p ≥ F − 1`.

  The Jacobi hypothesis `(Δ/n) = −1` enters the *implication* only
  through `gcd(Δ, n) = 1` (it is what makes the test *complete* for
  prime `n`, since then `n + 1 = n − (Δ/n)` is where Theorem 3.6.3
  puts a guaranteed zero of `U`).
-/
import Azurite.CrandallPomerance.Chapter4.Theorem_4_2_2
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace Azurite

namespace CP

variable {a b : ℤ} {n F : ℕ}

/-- **Theorem 4.2.3 (Morrison), main implication**: under (4.14), every
prime `p ∣ n` satisfies `p ≡ (Δ/p) (mod F)`.  The symbol in the
conclusion is stated as a Jacobi symbol — which agrees with the
Legendre symbol at the prime `p` — so that the statement needs no
`Fact p.Prime` instance. -/
theorem theorem_4_2_3 (hn : 0 < n) (hcop : IsCoprime (n : ℤ) (2 * b))
    (hjac : jacobiSym (a ^ 2 - 4 * b) n = -1) (hF : F ∣ n + 1)
    (hU : (n : ℤ) ∣ lucasU a b (n + 1))
    (hq : ∀ q : ℕ, q.Prime → q ∣ F →
      IsCoprime (n : ℤ) (lucasU a b ((n + 1) / q))) :
    ∀ p : ℕ, p.Prime → p ∣ n →
      (F : ℤ) ∣ (p : ℤ) - jacobiSym (a ^ 2 - 4 * b) p := by
  intro p hp hpn
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hpz : ((p : ℕ) : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hpn
  -- `p ∤ 2b` and `p ∤ Δ`
  have hp2b : IsCoprime ((p : ℕ) : ℤ) (2 * b) :=
    IsCoprime.of_isCoprime_of_dvd_left hcop hpz
  have hpΔ : ¬((p : ℕ) : ℤ) ∣ (a ^ 2 - 4 * b) := by
    intro hd
    haveI : NeZero n := ⟨by omega⟩
    have hgcd : (a ^ 2 - 4 * b).gcd n = 1 := by
      by_contra hne
      have h0 : jacobiSym (a ^ 2 - 4 * b) n = 0 :=
        jacobiSym.eq_zero_iff_not_coprime.mpr hne
      omega
    have hdg := Int.dvd_gcd hd hpz
    rw [hgcd] at hdg
    have hp2 := hp.two_le
    have := Nat.dvd_one.mp hdg
    omega
  have hpb : IsCoprime ((p : ℕ) : ℤ) b :=
    IsCoprime.of_isCoprime_of_dvd_right hp2b (dvd_mul_left b 2)
  have hp2bΔ : ¬((p : ℕ) : ℤ) ∣ 2 * b * (a ^ 2 - 4 * b) := by
    intro hd
    have hpz' : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpz'.dvd_mul.mp hd with hd1 | hd1
    · exact hpz'.not_unit (hp2b.isUnit_of_dvd' dvd_rfl hd1)
    · exact hpΔ hd1
  -- the rank exists and divides `n + 1`
  have hpU : ((p : ℕ) : ℤ) ∣ lucasU a b (n + 1) := hpz.trans hU
  have hex : ∃ r : ℕ, 0 < r ∧ ((p : ℕ) : ℤ) ∣ lucasU a b r :=
    ⟨n + 1, by omega, hpU⟩
  obtain ⟨hrpos, -⟩ := rankApp_mem hex
  set r := rankApp a b p with hr
  have hrn1 : r ∣ n + 1 :=
    (dvd_lucasU_iff_rankApp_dvd hpb hex (n + 1)).mp hpU
  -- the valuation climb: `F ∣ r`
  have hFr : F ∣ r := by
    have hF0 : F ≠ 0 := by
      rintro rfl
      exact absurd (Nat.eq_zero_of_zero_dvd hF) (by omega)
    rw [← Nat.factorization_le_iff_dvd hF0 hrpos.ne', Finsupp.le_def]
    intro q
    set e := F.factorization q with he
    rcases Nat.eq_zero_or_pos e with he0 | hepos
    · omega
    have hqmem : q ∈ F.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr (by omega)
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hqF : q ∣ F := Nat.dvd_of_mem_primeFactors hqmem
    by_contra hlt
    -- then `r ∣ (n+1)/q`, so `p ∣ U_{(n+1)/q}`, contradicting (4.14)
    have hrdvd : r ∣ (n + 1) / q := by
      have hqn1 : q ∣ n + 1 := hqF.trans hF
      have hdiv0 : (n + 1) / q ≠ 0 := by
        have := Nat.one_le_div_iff hqprime.pos |>.mpr
          (Nat.le_of_dvd (by omega) hqn1)
        omega
      rw [← Nat.factorization_le_iff_dvd hrpos.ne' hdiv0, Finsupp.le_def]
      intro ℓ
      have hfdiv := Nat.factorization_div hqn1
      have hval : ((n + 1) / q).factorization ℓ
          = (n + 1).factorization ℓ - q.factorization ℓ := by
        rw [hfdiv, Finsupp.tsub_apply]
      have hrle : r.factorization ℓ ≤ (n + 1).factorization ℓ :=
        (Nat.factorization_le_iff_dvd hrpos.ne' (by omega)).mpr hrn1 ℓ
      rcases eq_or_ne ℓ q with rfl | hne
      · -- at `q`: strict room, since `v_q(r) < e ≤ v_q(F) ≤ v_q(n+1)`
        have hFn1 : F.factorization ℓ ≤ (n + 1).factorization ℓ :=
          (Nat.factorization_le_iff_dvd hF0 (by omega)).mpr hF ℓ
        have hqfact : Nat.factorization ℓ ℓ = 1 := by
          rw [hqprime.factorization]
          simp
        omega
      · have hqfact : Nat.factorization q ℓ = 0 := by
          rw [hqprime.factorization]
          exact Finsupp.single_eq_of_ne (by omega)
        omega
    have hUdvd : ((p : ℕ) : ℤ) ∣ lucasU a b ((n + 1) / q) :=
      (dvd_lucasU_iff_rankApp_dvd hpb hex _).mpr hrdvd
    have hcop' : IsCoprime ((p : ℕ) : ℤ) (lucasU a b ((n + 1) / q)) :=
      IsCoprime.of_isCoprime_of_dvd_left (hq q hqprime hqF) hpz
    have hpunit := hcop'.isUnit_of_dvd' dvd_rfl hUdvd
    exact (Nat.prime_iff_prime_int.mp hp).not_unit hpunit
  -- conclude via Theorem 4.2.2
  have h422 := theorem_4_2_2 (p := p) (a := a) (b := b) hp2bΔ
  exact (Int.natCast_dvd_natCast.mpr hFr : (F : ℤ) ∣ (r : ℤ)).trans h422

/-- **The Morrison `n + 1` primality test** (Crandall–Pomerance
Theorem 4.2.3, second part): if in addition `F > √n + 1` — stated in
integers as `n < (F − 1)²` — then `n` is prime. -/
theorem morrison_test (hn : 0 < n) (hcop : IsCoprime (n : ℤ) (2 * b))
    (hjac : jacobiSym (a ^ 2 - 4 * b) n = -1) (hF : F ∣ n + 1)
    (hU : (n : ℤ) ∣ lucasU a b (n + 1))
    (hq : ∀ q : ℕ, q.Prime → q ∣ F →
      IsCoprime (n : ℤ) (lucasU a b ((n + 1) / q)))
    (hbig : n < (F - 1) ^ 2) : n.Prime := by
  -- `n = 1` is impossible: `(Δ/1) = 1 ≠ −1`
  have hn1 : 1 < n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      rw [jacobiSym.one_right] at hjac
      omega
    · omega
  by_contra hcomp
  -- a composite `n` has a prime factor `p` with `p² ≤ n`
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  have hple : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hcomp
  -- but `p ≡ (Δ/p) (mod F)` forces `p ≥ F − 1`
  have hdvd := theorem_4_2_3 hn hcop hjac hF hU hq p hp (Nat.minFac_dvd n)
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hdvd
  have hleg := legendreSym.eq_one_or_neg_one (p := p)
    (a := a ^ 2 - 4 * b) (by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hd
      -- `p ∣ Δ` contradicts `gcd(Δ, n) = 1` (from the Jacobi symbol)
      haveI : NeZero n := ⟨by omega⟩
      have hgcd : (a ^ 2 - 4 * b).gcd n = 1 := by
        by_contra hne
        have h0 : jacobiSym (a ^ 2 - 4 * b) n = 0 :=
          jacobiSym.eq_zero_iff_not_coprime.mpr hne
        omega
      have hpn' : ((p : ℕ) : ℤ) ∣ (n : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd n)
      have hdg := Int.dvd_gcd hd hpn'
      rw [hgcd] at hdg
      have hp2 := hp.two_le
      have := Nat.dvd_one.mp hdg
      omega)
  have hp2 := hp.two_le
  have hplarge : F - 1 ≤ p := by
    by_contra hsmall
    -- `0 < p − (Δ/p) < F`, yet `F` divides it
    rcases hleg with h1 | h1 <;> rw [h1] at hdvd
    · have hpos : 0 < (p : ℤ) - 1 := by
        have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp2
        omega
      have := Int.le_of_dvd hpos hdvd
      omega
    · have hpos : 0 < (p : ℤ) - (-1) := by
        have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp2
        omega
      have := Int.le_of_dvd hpos hdvd
      omega
  -- `p² ≤ n < (F−1)² ≤ p²`, contradiction
  have hsq : (F - 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hplarge 2
  omega

end CP

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! Morrison in action: `13` is prime via the Fibonacci sequence
(`a = 1, b = −1`, `Δ = 5`): `(5/13) = −1`, `F = 7 ∣ 14`,
`U₁₄ = 377 = 13·29 ≡ 0 (mod 13)`, `U₂ = 1` coprime to `13`, and
`13 < (7 − 1)² = 36`. -/

example : Nat.Prime 13 := by
  refine Azurite.CP.morrison_test (a := 1) (b := -1) (F := 7)
    (by norm_num) ?_ ?_ (by norm_num) ?_ ?_ (by norm_num)
  · rw [Int.isCoprime_iff_gcd_eq_one]
    decide
  · norm_num
  · show (13 : ℤ) ∣ Azurite.CP.lucasU 1 (-1) 14
    decide
  · intro q hq hq7
    have : q = 7 :=
      (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp hq7
    subst this
    show IsCoprime (13 : ℤ) (Azurite.CP.lucasU 1 (-1) 2)
    rw [show Azurite.CP.lucasU 1 (-1) 2 = 1 by decide]
    exact isCoprime_one_right
