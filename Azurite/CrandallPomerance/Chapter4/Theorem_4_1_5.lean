/-
  Crandall–Pomerance, Theorem 4.1.5 (Brillhart–Lehmer–Selfridge): suppose
  `n − 1 = F·R` with `F` fully factored, the Pocklington conditions (4.3)
  hold for a witness `a`, and `n^(1/3) ≤ F < n^(1/2)`.  Write `n` in base
  `F`: `n = c₂F² + c₁F + 1` (the constant digit is `1` since
  `F ∣ n − 1`).  Then `n` is prime IF AND ONLY IF `c₁² − 4c₂` is not a
  square.

  The point: with only a CUBE-ROOT-sized factored part, primality is
  still decided — by one integer square test.  The two directions:

  * If `c₁² − 4c₂ = s²`, the quadratic `x² − c₁x + c₂` has roots
    `u, v = (c₁ ± s)/2` (integers, by parity; positive, since
    `uv = c₂ ≥ 1` — here `F < √n` enters), and
    `n = (uF + 1)(vF + 1)` is a nontrivial factorization.  This
    direction needs no Pocklington.

  * If `n` is composite, Pocklington confines every prime factor to
    `1 (mod F)`, so each exceeds `F`; from `n ≤ F³ < (F+1)³` there are
    EXACTLY two: `n = (aF+1)(bF+1)` with `a, b ≥ 1`.  Then
    `abF + (a+b) = c₂F + c₁`, and the base-`F` digits match: `ab < F`
    (from `abF² < n ≤ F³`) and `a + b ≤ ab + 1 ≤ F`, with the boundary
    `a + b = F` killed by `c₂ ≤ F − 1`.  So `c₁ = a + b`, `c₂ = ab`, and
    `c₁² − 4c₂ = (a − b)²` is a square.

  The range hypotheses are stated in natural numbers: `n^(1/3) ≤ F` as
  `n ≤ F³` and `F < n^(1/2)` as `F² < n` — the exact integer forms.
-/
import Azurite.CrandallPomerance.Chapter4.Theorem_4_1_3

namespace Azurite

namespace CP

/-- A composite `n ≤ F³` all of whose prime factors exceed `F` is a
product of exactly two primes. -/
private theorem two_prime_factors {n F : ℕ} (hn : 1 < n)
    (hcomp : ¬n.Prime) (hle : n ≤ F ^ 3)
    (hfac : ∀ p : ℕ, p.Prime → p ∣ n → F + 1 ≤ p) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q := by
  obtain ⟨p, hp, m, hm⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m :=
    ⟨n.minFac, Nat.minFac_prime (by omega), n / n.minFac,
      (Nat.mul_div_cancel' n.minFac_dvd).symm⟩
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hcomp (hm ▸ hp)
  obtain ⟨r, hr, k, hk⟩ : ∃ r, r.Prime ∧ ∃ k, m = r * k :=
    ⟨m.minFac, Nat.minFac_prime hm1, m / m.minFac,
      (Nat.mul_div_cancel' m.minFac_dvd).symm⟩
  rcases eq_or_ne k 1 with rfl | hk1
  · exact ⟨p, r, hp, hr, by rw [hm, hk, mul_one]⟩
  exfalso
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    rw [hk, mul_zero] at hm
    omega
  have ht : k.minFac.Prime := Nat.minFac_prime hk1
  -- all three pieces are at least `F + 1`
  have h1 : F + 1 ≤ p := hfac _ hp ⟨m, hm⟩
  have h2 : F + 1 ≤ r := hfac _ hr ⟨p * k, by rw [hm, hk]; ring⟩
  have h3 : F + 1 ≤ k.minFac :=
    hfac _ ht (k.minFac_dvd.trans ⟨p * r, by rw [hm, hk]; ring⟩)
  have h3' : F + 1 ≤ k := h3.trans (Nat.minFac_le (by omega))
  -- so `n ≥ (F+1)³ > F³`, contradiction
  have hbig : (F + 1) ^ 3 ≤ n := by
    calc (F + 1) ^ 3 = (F + 1) * ((F + 1) * (F + 1)) := by ring
    _ ≤ p * (r * k) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3')
    _ = n := by rw [hm, hk]
  have hlt : F ^ 3 < (F + 1) ^ 3 :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self F) three_ne_zero
  omega

/-- Base-`F` digit uniqueness for the situation at hand: if
`P·F + s = c₂·F + c₁` with `s ≤ P + 1`, `P < F`, and `c₁, c₂ < F`, then
the digits agree.  The boundary `s = F` would force `c₁ = 0` and
`c₂ = P + 1 ≥ F`, impossible. -/
private theorem digit_uniqueness {F P s c₁ c₂ : ℕ} (hF : 2 ≤ F)
    (heq : P * F + s = c₂ * F + c₁) (hs : s ≤ P + 1) (hP : P < F)
    (hc1 : c₁ < F) (hc2 : c₂ < F) : s = c₁ ∧ P = c₂ := by
  rcases Nat.lt_or_ge s F with hsF | hsF
  · have h1 : (P * F + s) % F = s := Nat.mul_add_mod_of_lt hsF
    have h2 : (c₂ * F + c₁) % F = c₁ := Nat.mul_add_mod_of_lt hc1
    have hsc : s = c₁ := by rw [← h1, heq, h2]
    refine ⟨hsc, ?_⟩
    rw [hsc] at heq
    exact Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel heq)
  · exfalso
    have hsF' : s = F := by omega
    rw [hsF'] at heq hs
    have heq' : (P + 1) * F + 0 = c₂ * F + c₁ := by
      have hx : (P + 1) * F + 0 = P * F + F := by ring
      rw [hx]
      exact heq
    have h1 : ((P + 1) * F + 0) % F = 0 := Nat.mul_add_mod_of_lt (by omega)
    have h2 : (c₂ * F + c₁) % F = c₁ := Nat.mul_add_mod_of_lt hc1
    have hc10 : c₁ = 0 := by rw [← h2, ← heq', h1]
    rw [hc10] at heq'
    have h4 : P + 1 = c₂ :=
      Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel heq')
    omega

/-- **The Brillhart–Lehmer–Selfridge test** (Crandall–Pomerance
Theorem 4.1.5): suppose `n − 1 = F·R`, the witness `a` satisfies the
Pocklington conditions, and `n^(1/3) ≤ F < n^(1/2)` (in integers:
`F² < n ≤ F³`).  Write `n = c₂F² + c₁F + 1` in base `F` (`c₁ < F`).
Then `n` is prime if and only if `c₁² − 4c₂` is not a square. -/
theorem theorem_4_1_5 {n F R c₁ c₂ : ℕ} (hn : 1 < n)
    (hsplit : n - 1 = F * R) (a : ZMod n) (ha : a ^ (n - 1) = 1)
    (hunit : ∀ q : ℕ, q.Prime → q ∣ F → IsUnit (a ^ ((n - 1) / q) - 1))
    (hlo : n ≤ F ^ 3) (hhi : F ^ 2 < n)
    (hc1 : c₁ < F) (hrep : n = c₂ * F ^ 2 + c₁ * F + 1) :
    n.Prime ↔ ¬IsSquare ((c₁ : ℤ) ^ 2 - 4 * (c₂ : ℤ)) := by
  -- `F ≥ 2`, since `F² < n ≤ F³`
  have hF2 : 2 ≤ F := by
    by_contra h
    have hF1 : F ≤ 1 := by omega
    have : F ^ 3 ≤ F ^ 2 := by
      calc F ^ 3 = F * F ^ 2 := by ring
      _ ≤ 1 * F ^ 2 := Nat.mul_le_mul_right _ hF1
      _ = F ^ 2 := one_mul _
    omega
  -- `c₂ ≥ 1`, since `n > F²`
  have hc2pos : 1 ≤ c₂ := by
    by_contra h
    have h0 : c₂ = 0 := by omega
    rw [h0, zero_mul, zero_add] at hrep
    have hlt : c₁ * F < F * F := mul_lt_mul_of_pos_right hc1 (by omega)
    have hFF : F * F = F ^ 2 := by ring
    omega
  -- `c₂ < F`, since `c₂F² < n ≤ F³`
  have hc2lt : c₂ < F := by
    have h0 : c₂ * F ^ 2 < c₂ * F ^ 2 + (c₁ * F + 1) :=
      Nat.lt_add_of_pos_right (Nat.succ_pos _)
    rw [← Nat.add_assoc, ← hrep] at h0
    have hF3 : F ^ 3 = F * F ^ 2 := by ring
    have h1 : c₂ * F ^ 2 < F * F ^ 2 := by omega
    exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
  constructor
  · -- prime ⟹ the discriminant is not a square
    intro hprime hsq
    obtain ⟨r, hr⟩ := hsq
    set s := r.natAbs with hsdef
    -- transfer the square identity to `ℕ`: `c₁² = s² + 4c₂`
    have hs2 : ((s : ℤ)) ^ 2 = r * r := by
      rw [sq]
      exact_mod_cast Int.natAbs_mul_self
    have hznat : c₁ ^ 2 = s ^ 2 + 4 * c₂ := by
      have hz : ((c₁ ^ 2 : ℕ) : ℤ) = ((s ^ 2 + 4 * c₂ : ℕ) : ℤ) := by
        push_cast
        rw [show ((s : ℤ)) ^ 2 = r * r from hs2]
        linarith
      exact_mod_cast hz
    have hsc1 : s ≤ c₁ := by
      have : s ^ 2 ≤ c₁ ^ 2 := by omega
      exact (Nat.pow_le_pow_iff_left two_ne_zero).mp this
    -- the two roots `u ≥ v ≥ 1` of `x² − c₁x + c₂`
    have hprodF : (c₁ + s) * (c₁ - s) = 4 * c₂ := by
      have h1 : c₁ ^ 2 - s ^ 2 = 4 * c₂ := by omega
      rw [Nat.sq_sub_sq] at h1
      exact h1
    have hpar : (c₁ + s) % 2 = 0 ∧ (c₁ - s) % 2 = 0 := by
      have hE : Even ((c₁ + s) * (c₁ - s)) := ⟨2 * c₂, by omega⟩
      rcases Nat.even_mul.mp hE with h | h <;> rw [Nat.even_iff] at h <;>
        constructor <;> omega
    obtain ⟨u, hu⟩ : ∃ u, c₁ + s = 2 * u := ⟨(c₁ + s) / 2, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, c₁ - s = 2 * v := ⟨(c₁ - s) / 2, by omega⟩
    have huv : u * v = c₂ := by
      have h4 : 4 * (u * v) = 4 * c₂ := by
        rw [← hprodF, hu, hv]
        ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) h4
    have hsum : u + v = c₁ := by omega
    have hvpos : 1 ≤ v := by
      rcases Nat.eq_zero_or_pos v with h0 | h
      · rw [h0, mul_zero] at huv
        omega
      · exact h
    have hupos : 1 ≤ u := by omega
    -- the factorization
    have hfact : n = (u * F + 1) * (v * F + 1) := by
      rw [hrep, ← huv, ← hsum]
      ring
    rw [hfact] at hprime
    have hx1 : u * F + 1 ≠ 1 := by
      intro h
      rcases Nat.mul_eq_zero.mp (by omega : u * F = 0) with h' | h' <;> omega
    have hy1 : v * F + 1 ≠ 1 := by
      intro h
      rcases Nat.mul_eq_zero.mp (by omega : v * F = 0) with h' | h' <;> omega
    exact Nat.not_prime_mul hx1 hy1 hprime
  · -- the discriminant is not a square ⟹ prime
    intro hnsq
    by_contra hcomp
    apply hnsq
    -- every prime factor is `wF + 1` with `w ≥ 1` (Pocklington)
    have hfacs : ∀ p : ℕ, p.Prime → p ∣ n →
        ∃ w : ℕ, 1 ≤ w ∧ p = w * F + 1 := by
      intro p hp hpd
      have hmod : p % F = 1 % F := pocklington hn hsplit a ha hunit p hp hpd
      rw [Nat.mod_eq_of_lt (by omega : 1 < F)] at hmod
      have hdm := Nat.div_add_mod p F
      rw [hmod] at hdm
      have hp1 := hp.one_lt
      refine ⟨p / F, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos (p / F) with h0 | h1
        · rw [h0, Nat.mul_zero, Nat.zero_add] at hdm
          omega
        · exact h1
      · rw [Nat.mul_comm] at hdm
        omega
    -- exactly two prime factors
    obtain ⟨p, q, hp, hq, hpq⟩ := two_prime_factors hn hcomp hlo
      (fun p hp hpd => by
        obtain ⟨w, hw1, hpw⟩ := hfacs p hp hpd
        have := Nat.le_mul_of_pos_left F hw1
        omega)
    obtain ⟨b₁, hb₁, hpb⟩ := hfacs p hp ⟨q, hpq⟩
    obtain ⟨b₂, hb₂, hqb⟩ := hfacs q hq ⟨p, by rw [hpq]; ring⟩
    -- the digits equation `b₁b₂·F + (b₁+b₂) = c₂·F + c₁`
    have hn' : n = (b₁ * b₂) * F ^ 2 + (b₁ + b₂) * F + 1 := by
      rw [hpq, hpb, hqb]
      ring
    have hEq : (b₁ * b₂) * F + (b₁ + b₂) = c₂ * F + c₁ := by
      have h1 : F * ((b₁ * b₂) * F + (b₁ + b₂)) + 1 =
          F * (c₂ * F + c₁) + 1 := by
        calc F * ((b₁ * b₂) * F + (b₁ + b₂)) + 1
            = (b₁ * b₂) * F ^ 2 + (b₁ + b₂) * F + 1 := by ring
        _ = n := hn'.symm
        _ = c₂ * F ^ 2 + c₁ * F + 1 := hrep
        _ = F * (c₂ * F + c₁) + 1 := by ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel h1)
    -- bounds for digit uniqueness
    have hPlt : b₁ * b₂ < F := by
      have h0 : (b₁ * b₂) * F ^ 2 < (b₁ * b₂) * F ^ 2 + ((b₁ + b₂) * F + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos _)
      rw [← Nat.add_assoc, ← hn'] at h0
      have hF3 : F ^ 3 = F * F ^ 2 := by ring
      have h1 : (b₁ * b₂) * F ^ 2 < F * F ^ 2 := by omega
      exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
    have hslt : b₁ + b₂ ≤ b₁ * b₂ + 1 := by
      zify at hb₁ hb₂ ⊢
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (b₁ : ℤ) - 1)
        (by linarith : (0 : ℤ) ≤ (b₂ : ℤ) - 1)]
    obtain ⟨hs_eq, hP_eq⟩ := digit_uniqueness hF2 hEq hslt hPlt hc1 hc2lt
    -- the discriminant is `(b₁ − b₂)²`
    refine ⟨(b₁ : ℤ) - (b₂ : ℤ), ?_⟩
    rw [← hs_eq, ← hP_eq]
    push_cast
    ring

end CP

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! A worked BLS certificate: `191` is prime via `190 = 10·19` — `F = 10`
is between `191^(1/3)` and `191^(1/2)`, so Pocklington's corollary does
NOT apply, but BLS does.  Witness `7` (`7^95 ≡ −1`, `7^38 ≡ 39`, with
explicit inverses `95` and `186` for the unit conditions); the base-10
digits of `191` give discriminant `9² − 4·1 = 77`, not a square. -/

set_option maxRecDepth 8192 in
example : Nat.Prime 191 := by
  refine (Azurite.CP.theorem_4_1_5 (F := 10) (R := 19) (c₁ := 9) (c₂ := 1)
    (by norm_num) (by norm_num) (7 : ZMod 191) (by decide) ?_ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).mpr ?_
  · intro q hq hqF
    have hq25 : q = 2 ∨ q = 5 := by
      have hle : q ≤ 10 := Nat.le_of_dvd (by norm_num) hqF
      interval_cases q <;> revert hqF hq <;> decide
    rcases hq25 with rfl | rfl
    · exact IsUnit.of_mul_eq_one (95 : ZMod 191) (by decide)
    · exact IsUnit.of_mul_eq_one (186 : ZMod 191) (by decide)
  · rintro ⟨r, hr⟩
    norm_num at hr
    have h1 : r ≤ 9 := by nlinarith [sq_nonneg (r - 9)]
    have h2 : -9 ≤ r := by nlinarith [sq_nonneg (r + 9)]
    interval_cases r <;> omega
