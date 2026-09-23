/-
  Crandall–Pomerance, Theorem 4.2.5: Morrison's `n + 1` test in
  `V`-sequence form — the version binary Lucas chains actually compute.
  Let `f, Δ` be as in (4.12), `n` positive with `gcd(n, 2b) = 1` and
  `(Δ/n) = −1`.  If `F` is an EVEN divisor of `n + 1` and

    `V_{F/2} ≡ 0 (mod n)`,  `gcd(V_{F/2q}, n) = 1` for every odd
    prime `q ∣ F`,                                          (4.15)

  then every prime `p ∣ n` satisfies `p ≡ (Δ/p) (mod F)`; and if
  moreover `F > √n + 1`, then `n` is prime.

  The book's proof, as formalized: a common prime divisor of `U_m` and
  `V_m` divides `4bᵐ` (from `V_m² − ΔU_m² = 4bᵐ`), hence is even or
  divides `b` — impossible for a divisor of `n`.  With the doubling
  formula `U_{2m} = U_m V_m`, condition (4.15) gives `U_F ≡ 0 (mod n)`
  with `gcd(U_{F/2}, n) = 1`, and `gcd(U_{F/q}, n) = 1` for odd primes
  `q ∣ F` (as `U_{F/q} = U_{F/2q}·V_{F/2q}` with `U_{F/2q} ∣ U_{F/2}`).
  So for every prime `p ∣ n` the rank `r_f(p)` divides `F` but no
  `F/q` — that is, `r_f(p) = F` exactly — and Theorem 4.2.2 gives
  `F ∣ p − (Δ/p)`.
-/
import Azurite.CrandallPomerance.Chapter4.Theorem_4_2_2
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace Azurite

namespace CP

variable {a b : ℤ} {n F : ℕ}

/-- **Theorem 4.2.5 (Morrison, `V`-form), main implication**: under
(4.15), every prime `p ∣ n` satisfies `p ≡ (Δ/p) (mod F)` (the symbol
in the conclusion is a Jacobi symbol, agreeing with Legendre at `p`). -/
theorem theorem_4_2_5 (hn : 0 < n) (hcop : IsCoprime (n : ℤ) (2 * b))
    (hjac : jacobiSym (a ^ 2 - 4 * b) n = -1) (hF : F ∣ n + 1)
    (hFeven : 2 ∣ F)
    (hV : (n : ℤ) ∣ lucasV a b (F / 2))
    (hq : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ F →
      IsCoprime (n : ℤ) (lucasV a b (F / (2 * q)))) :
    ∀ p : ℕ, p.Prime → p ∣ n →
      (F : ℤ) ∣ (p : ℤ) - jacobiSym (a ^ 2 - 4 * b) p := by
  intro p hp hpn
  have : Fact p.Prime := ⟨hp⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hF2 : 2 ≤ F := by
    have hF0 : F ≠ 0 := by
      rintro rfl
      exact absurd (Nat.eq_zero_of_zero_dvd hF) (by omega)
    omega
  have hpz : ((p : ℕ) : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hpn
  -- `p ∤ 2b` and `p ∤ Δ` (as in Theorem 4.2.3)
  have hp2b : IsCoprime ((p : ℕ) : ℤ) (2 * b) :=
    IsCoprime.of_isCoprime_of_dvd_left hcop hpz
  have hpΔ : ¬((p : ℕ) : ℤ) ∣ (a ^ 2 - 4 * b) := by
    intro hd
    have : NeZero n := ⟨by omega⟩
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
    · exact hpz'.not_isUnit (hp2b.isUnit_of_dvd' dvd_rfl hd1)
    · exact hpΔ hd1
  have hpprime : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
  -- `U_F = U_{F/2} · V_{F/2}`, so `n ∣ U_F`
  have hUdouble : lucasU a b F = lucasU a b (F / 2) * lucasV a b (F / 2) := by
    have := lucasU_two_mul a b (F / 2)
    rwa [Nat.mul_div_cancel' hFeven] at this
  have hnUF : (n : ℤ) ∣ lucasU a b F := by
    rw [hUdouble]
    exact hV.mul_left _
  have hpUF : ((p : ℕ) : ℤ) ∣ lucasU a b F := hpz.trans hnUF
  -- `p ∤ U_{F/2}`: a common divisor of `U_m, V_m` divides `4bᵐ`
  have hpUF2 : ¬((p : ℕ) : ℤ) ∣ lucasU a b (F / 2) := by
    intro hd
    have hpV : ((p : ℕ) : ℤ) ∣ lucasV a b (F / 2) := hpz.trans hV
    have hid := lucasV_sq_sub_disc_mul_sq a b (F / 2)
    have h4b : ((p : ℕ) : ℤ) ∣ 4 * b ^ (F / 2) := by
      rw [← hid]
      exact dvd_sub (dvd_pow hpV two_ne_zero)
        ((dvd_pow hd two_ne_zero).mul_left _)
    rcases hpprime.dvd_mul.mp h4b with h4 | hbm
    · -- `p ∣ 4` contradicts `p ∤ 2b` (i.e. `p` odd)
      have hp2 : ((p : ℕ) : ℤ) ∣ 2 := by
        have := hpprime.dvd_of_dvd_pow (n := 2)
          (by rwa [show (4 : ℤ) = 2 ^ 2 by norm_num] at h4)
        exact this
      exact hpprime.not_isUnit (hp2b.isUnit_of_dvd' dvd_rfl
        (hp2.mul_right b))
    · exact hpprime.not_isUnit (hpb.isUnit_of_dvd' dvd_rfl
        (hpprime.dvd_of_dvd_pow hbm))
  -- the rank equals `F`
  have hex : ∃ r : ℕ, 0 < r ∧ ((p : ℕ) : ℤ) ∣ lucasU a b r :=
    ⟨F, by omega, hpUF⟩
  obtain ⟨hrpos, -⟩ := rankApp_mem hex
  set r := rankApp a b p with hr
  have hrF : r ∣ F := (dvd_lucasU_iff_rankApp_dvd hpb hex F).mp hpUF
  have hrF2 : ¬r ∣ F / 2 := by
    intro hd
    exact hpUF2 ((dvd_lucasU_iff_rankApp_dvd hpb hex _).mpr hd)
  have hrFq : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ F → ¬r ∣ F / q := by
    intro q hqp hq2 hqF hd
    -- `2q ∣ F`, and `U_{F/q} = U_{F/2q} · V_{F/2q}`
    have h2q : 2 * q ∣ F :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (Nat.coprime_two_left.mpr (hqp.odd_of_ne_two hq2)) hFeven hqF
    have hq0 : 0 < q := hqp.pos
    have hdouble : lucasU a b (F / q)
        = lucasU a b (F / (2 * q)) * lucasV a b (F / (2 * q)) := by
      have := lucasU_two_mul a b (F / (2 * q))
      rwa [show 2 * (F / (2 * q)) = F / q by
        obtain ⟨t, rfl⟩ := h2q
        rw [Nat.mul_div_cancel_left _ (by omega : 0 < 2 * q),
          show 2 * q * t = q * (2 * t) by ring,
          Nat.mul_div_cancel_left _ hq0]] at this
    have hpUFq : ((p : ℕ) : ℤ) ∣ lucasU a b (F / q) :=
      (dvd_lucasU_iff_rankApp_dvd hpb hex _).mpr hd
    rw [hdouble] at hpUFq
    rcases hpprime.dvd_mul.mp hpUFq with hU | hVc
    · -- `U_{F/2q} ∣ U_{F/2}`, contradicting `p ∤ U_{F/2}`
      apply hpUF2
      refine hU.trans (lucasU_dvd_lucasU a b ?_)
      obtain ⟨t, rfl⟩ := h2q
      rw [Nat.mul_div_cancel_left _ (by omega : 0 < 2 * q),
        show 2 * q * t / 2 = q * t from by
          rw [show 2 * q * t = 2 * (q * t) by ring]
          exact Nat.mul_div_cancel_left _ (by norm_num)]
      exact ⟨q, by ring⟩
    · -- contradicts the second condition of (4.15)
      have hcop' := IsCoprime.of_isCoprime_of_dvd_left
        (hq q hqp hq2 hqF) hpz
      exact hpprime.not_isUnit (hcop'.isUnit_of_dvd' dvd_rfl hVc)
  have hrEq : r = F := by
    by_contra hne
    obtain ⟨s, hs⟩ := hrF
    have hs2 : 2 ≤ s := by
      rcases Nat.lt_or_ge s 2 with h | h
      · interval_cases s
        · rw [Nat.mul_zero] at hs
          omega
        · rw [Nat.mul_one] at hs
          exact (hne hs.symm).elim
      · exact h
    obtain ⟨q, hqp, hqs⟩ : ∃ q, q.Prime ∧ q ∣ s :=
      ⟨s.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd s⟩
    have hqF : q ∣ F := hqs.trans ⟨r, by rw [hs]; ring⟩
    have hrq : r ∣ F / q := by
      obtain ⟨t, ht⟩ := hqs
      refine ⟨t, ?_⟩
      rw [hs, ht, show r * (q * t) = q * (r * t) by ring,
        Nat.mul_div_cancel_left _ hqp.pos]
    rcases eq_or_ne q 2 with hq2 | hq2
    · rw [hq2] at hrq
      exact hrF2 hrq
    · exact hrFq q hqp hq2 hqF hrq
  -- conclude via Theorem 4.2.2
  have h422 := theorem_4_2_2 (p := p) (a := a) (b := b) hp2bΔ
  rw [← hr, hrEq] at h422
  exact h422

/-- **The Morrison `n + 1` test, `V`-form** (Crandall–Pomerance
Theorem 4.2.5, second part): if in addition `F > √n + 1` — in integers,
`n < (F − 1)²` — then `n` is prime. -/
theorem morrison_test_V (hn : 0 < n) (hcop : IsCoprime (n : ℤ) (2 * b))
    (hjac : jacobiSym (a ^ 2 - 4 * b) n = -1) (hF : F ∣ n + 1)
    (hFeven : 2 ∣ F)
    (hV : (n : ℤ) ∣ lucasV a b (F / 2))
    (hq : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ F →
      IsCoprime (n : ℤ) (lucasV a b (F / (2 * q))))
    (hbig : n < (F - 1) ^ 2) : n.Prime := by
  have hn1 : 1 < n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      rw [jacobiSym.one_right] at hjac
      omega
    · omega
  by_contra hcomp
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hple : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hcomp
  have hdvd := theorem_4_2_5 hn hcop hjac hF hFeven hV hq p hp
    (Nat.minFac_dvd n)
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hdvd
  have hleg := legendreSym.eq_one_or_neg_one (p := p)
    (a := a ^ 2 - 4 * b) (by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hd
      have : NeZero n := ⟨by omega⟩
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
  have hsq : (F - 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hplarge 2
  omega

end CP

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! Morrison's `V`-form in action: `13` is prime via `f = x² − x + 2`
(`Δ = −7`, a nonresidue mod 13) with the even divisor `F = 14` of
`n + 1`: `V₇ = −13 ≡ 0 (mod 13)`, and for the odd prime `7 ∣ F` the
value `V_{14/14} = V₁ = 1` is coprime to `13`. -/

example : Nat.Prime 13 := by
  refine Azurite.CP.morrison_test_V (a := 1) (b := 2) (F := 14)
    (by norm_num) ?_ ?_ (by norm_num) (by norm_num) ?_ ?_ (by norm_num)
  · rw [Int.isCoprime_iff_gcd_eq_one]
    decide
  · norm_num
  · show (13 : ℤ) ∣ Azurite.CP.lucasV 1 2 7
    decide
  · intro q hq hq2 hq14
    have hq7 : q = 7 := by
      have hle : q ≤ 14 := Nat.le_of_dvd (by norm_num) hq14
      interval_cases q <;> revert hq14 hq hq2 <;> decide
    subst hq7
    show IsCoprime (13 : ℤ) (Azurite.CP.lucasV 1 2 1)
    rw [show Azurite.CP.lucasV 1 2 1 = 1 by decide]
    exact isCoprime_one_right
