/-
  Crandall–Pomerance, Theorem 4.2.10 (Brillhart–Lehmer–Selfridge): the
  COMBINED `n − 1` / `n + 1` test.

  Suppose `F₁ ∣ n − 1` with the Pocklington conditions (4.3) holding
  for a witness `a₁` at `F = F₁`, and `F₂ ∣ n + 1` with the Morrison
  conditions (4.14) holding at `F = F₂` (for a Lucas pair with
  `gcd(n, 2b) = 1` and `(Δ/n) = −1`).  Let `F = lcm(F₁, F₂)`.  Then
  every prime factor of `n` is congruent to `1` or to `n (mod F)`.
  In particular, if `F > √n` and `n mod F` is not a nontrivial factor
  of `n`, then `n` is prime.

  The proof is exactly the book's: for a prime `p ∣ n`, Pocklington
  (Theorem 4.1.3) gives `p ≡ 1 (mod F₁)` and Morrison (Theorem 4.2.3)
  gives `p ≡ (Δ/p) (mod F₂)`.  If `(Δ/p) = 1` then `p ≡ 1` modulo both
  factors of the lcm; if `(Δ/p) = −1` then `p ≡ n` modulo both, since
  `n ≡ 1 (mod F₁)` and `n ≡ −1 (mod F₂)`.  For the test: a composite
  `n` has a prime factor `p ≤ √n < F`, so `p mod F = p`; the class of
  `1` would force `p = 1`, and the class of `n` exhibits
  `n mod F = p` as a nontrivial factor.

  (The book notes `F = F₁F₂/2` when both parts are even and `F₁F₂`
  otherwise — that is just the arithmetic of `lcm`, which we use
  directly.)

  This doubles the reach of partial factorizations: with
  `F₁ ≈ F₂ ≈ n^(1/4)`, the combination already exceeds `√n`.
-/
import Azurite.CrandallPomerance.Chapter4.Theorem_4_1_3
import Azurite.CrandallPomerance.Chapter4.Theorem_4_2_3

namespace Azurite

namespace CP

/-- **Crandall–Pomerance Theorem 4.2.10 (Brillhart–Lehmer–Selfridge),
congruence form**: under the Pocklington conditions at `F₁ ∣ n − 1`
and the Morrison conditions at `F₂ ∣ n + 1`, every prime factor of `n`
is `≡ 1` or `≡ n (mod lcm(F₁, F₂))`. -/
theorem theorem_4_2_10 {a b : ℤ} {n F₁ R₁ F₂ : ℕ} (hn : 0 < n)
    (hsplit : n - 1 = F₁ * R₁) (a₁ : ZMod n) (ha₁ : a₁ ^ (n - 1) = 1)
    (hunit : ∀ q : ℕ, q.Prime → q ∣ F₁ → IsUnit (a₁ ^ ((n - 1) / q) - 1))
    (hcop : IsCoprime (n : ℤ) (2 * b))
    (hjac : jacobiSym (a ^ 2 - 4 * b) n = -1)
    (hF₂ : F₂ ∣ n + 1)
    (hU : (n : ℤ) ∣ lucasU a b (n + 1))
    (hq : ∀ q : ℕ, q.Prime → q ∣ F₂ →
      IsCoprime (n : ℤ) (lucasU a b ((n + 1) / q))) :
    ∀ p : ℕ, p.Prime → p ∣ n →
      p ≡ 1 [MOD Nat.lcm F₁ F₂] ∨ p ≡ n [MOD Nat.lcm F₁ F₂] := by
  -- `n = 1` is impossible: `(Δ/1) = 1 ≠ −1`
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      rw [jacobiSym.one_right] at hjac
      omega
    · exact h
  intro p hp hpn
  haveI : NeZero n := ⟨by omega⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
  -- the two single-sided congruences
  have hp1 : p ≡ 1 [MOD F₁] :=
    pocklington (by omega) hsplit a₁ ha₁ hunit p hp hpn
  have h2 := theorem_4_2_3 hn hcop hjac hF₂ hU hq p hp hpn
  -- `(Δ/p) = ±1`
  have hΔn : Int.gcd (a ^ 2 - 4 * b) n = 1 := by
    by_contra h
    have h0 : jacobiSym (a ^ 2 - 4 * b) n = 0 :=
      jacobiSym.eq_zero_iff_not_coprime.mpr h
    rw [hjac] at h0
    norm_num at h0
  have hΔn' : Nat.Coprime (a ^ 2 - 4 * b).natAbs n := by
    rwa [Int.gcd, Int.natAbs_natCast] at hΔn
  have hJ : jacobiSym (a ^ 2 - 4 * b) p = 1 ∨
      jacobiSym (a ^ 2 - 4 * b) p = -1 :=
    jacobiSym.eq_one_or_neg_one (by
      rw [Int.gcd, Int.natAbs_natCast]
      exact hΔn'.coprime_dvd_right hpn)
  rcases hJ with hJ | hJ <;> rw [hJ] at h2
  · -- `(Δ/p) = 1`: `p ≡ 1` modulo both `F₁` and `F₂`
    left
    have hd1 : F₁ ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hp1.symm
    have hd2 : F₂ ∣ p - 1 := by
      have hz : ((F₂ : ℕ) : ℤ) ∣ ((p - 1 : ℕ) : ℤ) := by
        push_cast [show (1 : ℕ) ≤ p from by omega]
        exact h2
      exact_mod_cast hz
    exact ((Nat.modEq_iff_dvd' (by omega)).mpr (Nat.lcm_dvd hd1 hd2)).symm
  · -- `(Δ/p) = −1`: `p ≡ n` modulo both `F₁` and `F₂`
    right
    have hnF₁ : n ≡ 1 [MOD F₁] :=
      ((Nat.modEq_iff_dvd' (by omega)).mpr ⟨R₁, hsplit⟩).symm
    have hd1 : F₁ ∣ n - p :=
      (Nat.modEq_iff_dvd' hple).mp (hp1.trans hnF₁.symm)
    have hd2 : F₂ ∣ n - p := by
      have hpz : (F₂ : ℤ) ∣ (p : ℤ) + 1 := by
        rw [sub_neg_eq_add] at h2
        exact h2
      have hnz : (F₂ : ℤ) ∣ (n : ℤ) + 1 := by
        have h0 : ((F₂ : ℕ) : ℤ) ∣ ((n + 1 : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr hF₂
        push_cast at h0
        exact h0
      have hz : ((F₂ : ℕ) : ℤ) ∣ ((n - p : ℕ) : ℤ) := by
        have hsub := dvd_sub hnz hpz
        rw [show (n : ℤ) + 1 - ((p : ℤ) + 1) = (n : ℤ) - p by ring] at hsub
        push_cast [hple]
        exact hsub
      exact_mod_cast hz
    exact (Nat.modEq_iff_dvd' hple).mpr (Nat.lcm_dvd hd1 hd2)

/-- **The combined `n − 1` / `n + 1` primality test** (the final
assertion of Theorem 4.2.10): with the hypotheses above,
`lcm(F₁, F₂) > √n` (in integers, `n < lcm(F₁, F₂)²`), and
`n mod lcm(F₁, F₂)` not a nontrivial factor of `n`, the number `n` is
prime.  This doubles the reach of the one-sided √-tests: partial
factorizations of `n − 1` and `n + 1` past `n^(1/4)` each suffice. -/
theorem bls_combined_test {a b : ℤ} {n F₁ R₁ F₂ : ℕ} (hn : 0 < n)
    (hsplit : n - 1 = F₁ * R₁) (a₁ : ZMod n) (ha₁ : a₁ ^ (n - 1) = 1)
    (hunit : ∀ q : ℕ, q.Prime → q ∣ F₁ → IsUnit (a₁ ^ ((n - 1) / q) - 1))
    (hcop : IsCoprime (n : ℤ) (2 * b))
    (hjac : jacobiSym (a ^ 2 - 4 * b) n = -1)
    (hF₂ : F₂ ∣ n + 1)
    (hU : (n : ℤ) ∣ lucasU a b (n + 1))
    (hq : ∀ q : ℕ, q.Prime → q ∣ F₂ →
      IsCoprime (n : ℤ) (lucasU a b ((n + 1) / q)))
    (hbig : n < Nat.lcm F₁ F₂ ^ 2)
    (hmod : ¬(n % Nat.lcm F₁ F₂ ∣ n ∧ 1 < n % Nat.lcm F₁ F₂
        ∧ n % Nat.lcm F₁ F₂ < n)) : n.Prime := by
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      rw [jacobiSym.one_right] at hjac
      omega
    · exact h
  by_contra hcomp
  obtain ⟨p, hpdef⟩ : ∃ p, p = n.minFac := ⟨n.minFac, rfl⟩
  have hp : p.Prime := hpdef ▸ Nat.minFac_prime (by omega)
  have hpn : p ∣ n := hpdef ▸ n.minFac_dvd
  have hpsq : p ^ 2 ≤ n := hpdef ▸ Nat.minFac_sq_le_self (by omega) hcomp
  have hp2 : 2 ≤ p := hp.two_le
  have hpltF : p < Nat.lcm F₁ F₂ := by
    by_contra h
    push Not at h
    have hsq : Nat.lcm F₁ F₂ ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h 2
    omega
  have hpltn : p < n := by
    have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
    have hne : p ≠ n := by
      rintro rfl
      have hsq : p * p ≤ p := by
        have he : p ^ 2 = p * p := by ring
        omega
      nlinarith
    omega
  rcases theorem_4_2_10 hn hsplit a₁ ha₁ hunit hcop hjac hF₂ hU hq
      p hp hpn with h | h
  · -- `p ≡ 1 (mod F)` with `p < F` forces `p = 1`
    have hmodeq : p % Nat.lcm F₁ F₂ = 1 % Nat.lcm F₁ F₂ := h
    rw [Nat.mod_eq_of_lt hpltF, Nat.mod_eq_of_lt (by omega)] at hmodeq
    omega
  · -- `p ≡ n (mod F)` with `p < F` exhibits `n mod F = p` as a factor
    have hmodeq : p % Nat.lcm F₁ F₂ = n % Nat.lcm F₁ F₂ := h
    rw [Nat.mod_eq_of_lt hpltF] at hmodeq
    exact hmod ⟨by rw [← hmodeq]; exact hpn, by omega, by omega⟩

section Example

/-- `199` is prime by the combined test: `198 = 9 · 22` with
Pocklington witness `2` for `F₁ = 9`, `200 = 8 · 25` with the Lucas
pair `(a, b) = (2, −2)` (`Δ = 12`) for `F₂ = 8`, and
`lcm(9, 8) = 72 > √199` with `199 mod 72 = 55` not a factor of `199`.
Neither one-sided √-test applies: `9² = 81 < 199` and `8² = 64 < 199`. -/
example : Nat.Prime 199 := by
  refine bls_combined_test (a := 2) (b := -2) (F₁ := 9) (R₁ := 22)
    (F₂ := 8) (by norm_num) (by norm_num) (2 : ZMod 199)
    (by set_option maxRecDepth 4096 in decide) ?_
    (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
    (by norm_num)
    (by norm_num)
    (by set_option maxRecDepth 8192 in decide)
    ?_
    (by norm_num)
    (by norm_num)
  · -- Pocklington conditions at `F₁ = 9`: only `q = 3`
    intro q hq hqF
    have hq3 : q = 3 := by
      have hle : q ≤ 9 := Nat.le_of_dvd (by norm_num) hqF
      interval_cases q <;> revert hqF hq <;> decide
    subst hq3
    exact IsUnit.of_mul_eq_one (163 : ZMod 199)
      (by set_option maxRecDepth 4096 in decide)
  · -- Morrison conditions at `F₂ = 8`: only `q = 2`
    intro q hq hqF
    have hq2 : q = 2 := by
      have hle : q ≤ 8 := Nat.le_of_dvd (by norm_num) hqF
      interval_cases q <;> revert hqF hq <;> decide
    subst hq2
    rw [Int.isCoprime_iff_gcd_eq_one]
    set_option maxRecDepth 8192 in decide

end Example

end CP

end Azurite
