/-
  Crandall–Pomerance, Theorem 4.2.9: the Konyagin–Pomerance-style
  refinement of the `n + 1` test, reaching down to `F ≥ n^(3/10)`.
  The book states it and leaves the proof as an exercise ("completely
  analogous to Theorem 4.1.6"); the proof below is ours.

  Suppose `n ≥ 214`, the Morrison hypotheses (4.14) hold, and
  `n + 1 = c₄F² + c₁F` in base `F` (`c₁ < F`; `c₄ = c₃F + c₂` bundles
  the two high digits).  Let `u/v` approximate `c₁/F` with
  `v²n < F⁴` and `(uF − c₁v)²F² ≤ n` (the book's continued-fraction
  convergent qualifies), and let `d = ⌊c₄v/F + 1/2⌋`.  Then `n` is
  prime IF AND ONLY IF
  (1) `(c₁ + tF)² − 4t + 4c₄` is not a square for `|t| ≤ 5`, and
  (2) neither `vx³ − (uF − c₁v)x² − (c₄v − dF + u)x + d` has an
      integral root `x` with `xF + 1` a nontrivial factor of `n`, nor
      `vx³ + (uF − c₁v)x² + (dF − c₄v − u)x − d` an integral root `x`
      with `xF − 1` a nontrivial factor of `n`.

  TWO CORRECTIONS TO THE BOOK (both verified by explicit
  counterexample):

  * The book's band `n^(3/10) ≤ F ≤ n^(1/3) + 1` is too generous: for
    the PRIME `n = 223` with `F = 7` (inside that band) one has
    `c₄ = 4`, and at `t = c₄ = 4` the discriminant
    `(c₁ + tF)² − 4t + 4c₄ = 32²` is a square — the trivial split
    `1 · n` masquerades as a factorization, so condition (1) fails
    for a prime and the stated equivalence is FALSE.  The fix: the
    prime direction needs exactly `c₄ ≥ 6`, which we take as the
    hypothesis (when `F³ < n` — the interior of the band — it holds
    automatically, since then `c₄ ≥ F ≥ 6`).

  * The book's second cubic `vx³ + (uF − c₁v)x² − (c₄v + dF + u)x + d`
    has a sign typo: it does not vanish at the root it is meant to
    catch.  The correct polynomial (derived below, and confirmed
    numerically) is `vx³ + (uF − c₁v)x² + (dF − c₄v − u)x − d`.

  Proof shape (composite direction): every prime factor of `n` is
  `≡ ±1 (mod F)` (Theorem 4.2.3 + Jacobi), hence so is every DIVISOR;
  since `n ≡ −1`, splitting off the least prime factor gives
  `n = (xF + 1)(yF − 1)` with `x, y ≥ 1` — no two-prime-factor lemma
  needed.  Digit matching gives `xy = c₄ − t` and `y − x = c₁ + tF`
  for `t := c₄ − xy`.  If `|t| ≤ 5` the discriminant at `t` equals
  `(x + y)²`.  If `t ≥ 6` then `y ≥ 6F` forces `x` small
  (`5xF³ < n`), the integer `D := x(u + tv)` satisfies
  `DF − c₄v = x(uF − c₁v) − (x² + t)v` with `2|DF − c₄v| < F`
  (budget `6·(5xW) + 2·(15x²v) + 5·(6tv) ≤ 13(F−1)`), so `D = d` and
  `x` is a root of the first cubic.  If `t ≤ −6`, symmetrically
  `x ≥ 5F + 2` forces `y` small and `F ≥ 124` (whence
  `13824F⁴ ≤ (F−1)⁶` and `24x² ≤ n`), `D := y(sv − u)` (`s := −t`)
  pins to `d`, and `y` is a root of the second cubic.
-/
import Azurite.CrandallPomerance.Chapter4.Theorem_4_2_3
import Azurite.CrandallPomerance.Chapter4.Theorem_4_1_6

namespace Azurite

namespace CP

/-- Every positive divisor of `n` all of whose prime factors are
`≡ ±1 (mod F)` is itself `≡ ±1 (mod F)`. -/
private theorem dvd_pm_one {n F : ℕ}
    (hfac : ∀ p : ℕ, p.Prime → p ∣ n →
      (F : ℤ) ∣ (p : ℤ) - 1 ∨ (F : ℤ) ∣ (p : ℤ) + 1) :
    ∀ m : ℕ, 0 < m → m ∣ n →
      (F : ℤ) ∣ (m : ℤ) - 1 ∨ (F : ℤ) ∣ (m : ℤ) + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hmn
    rcases eq_or_ne m 1 with rfl | hm1
    · exact Or.inl (by simp)
    obtain ⟨m', hm'⟩ := m.minFac_dvd
    have hp : m.minFac.Prime := Nat.minFac_prime hm1
    set p := m.minFac with hpdef
    have hp2 : 2 ≤ p := hp.two_le
    have hm'pos : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with h0 | h
      · rw [h0, mul_zero] at hm'
        omega
      · exact h
    have hm'lt : m' < m := by
      have h1 : 1 * m' < p * m' := (Nat.mul_lt_mul_right hm'pos).mpr (by omega)
      rw [one_mul] at h1
      omega
    have hm'n : m' ∣ n := dvd_trans ⟨p, by rw [hm']; ring⟩ hmn
    have hpn : p ∣ n := dvd_trans ⟨m', hm'⟩ hmn
    have hmz : (m : ℤ) = p * m' := by exact_mod_cast hm'
    rcases hfac p hp hpn with hps | hps <;>
        rcases ih m' hm'lt hm'pos hm'n with hms | hms
    · exact Or.inl (by
        have : (F : ℤ) ∣ (m' : ℤ) * ((p : ℤ) - 1) + ((m' : ℤ) - 1) :=
          dvd_add (Dvd.dvd.mul_left hps _) hms
        have he : (m : ℤ) - 1
            = (m' : ℤ) * ((p : ℤ) - 1) + ((m' : ℤ) - 1) := by
          rw [hmz]
          ring
        rwa [← he] at this)
    · exact Or.inr (by
        have : (F : ℤ) ∣ (m' : ℤ) * ((p : ℤ) - 1) + ((m' : ℤ) + 1) :=
          dvd_add (Dvd.dvd.mul_left hps _) hms
        have he : (m : ℤ) + 1
            = (m' : ℤ) * ((p : ℤ) - 1) + ((m' : ℤ) + 1) := by
          rw [hmz]
          ring
        rwa [← he] at this)
    · exact Or.inr (by
        have : (F : ℤ) ∣ (m' : ℤ) * ((p : ℤ) + 1) - ((m' : ℤ) - 1) :=
          dvd_sub (Dvd.dvd.mul_left hps _) hms
        have he : (m : ℤ) + 1
            = (m' : ℤ) * ((p : ℤ) + 1) - ((m' : ℤ) - 1) := by
          rw [hmz]
          ring
        rwa [← he] at this)
    · exact Or.inl (by
        have : (F : ℤ) ∣ (m' : ℤ) * ((p : ℤ) + 1) - ((m' : ℤ) + 1) :=
          dvd_sub (Dvd.dvd.mul_left hps _) hms
        have he : (m : ℤ) - 1
            = (m' : ℤ) * ((p : ℤ) + 1) - ((m' : ℤ) + 1) := by
          rw [hmz]
          ring
        rwa [← he] at this)

/-- The nearest-integer pin: if `2|DF − A| < F` then
`D = ⌊A/F + 1/2⌋ = (2A + F)/(2F)` — over `ℤ`, so `D` may a priori be
negative. -/
private theorem nearest_pin {F A d : ℕ} {D : ℤ} (hF : 0 < F)
    (hd : d = (2 * A + F) / (2 * F))
    (hE : 2 * |D * F - (A : ℤ)| < F) : D = d := by
  have hdm := Nat.div_add_mod (2 * A + F) (2 * F)
  rw [← hd] at hdm
  set M := (2 * A + F) % (2 * F) with hM
  have hmodlt : M < 2 * F := Nat.mod_lt _ (by omega)
  -- `hdm : 2 * F * d + M = 2 * A + F`
  have habs1 : 2 * (D * F - (A : ℤ)) < F := by
    have := le_abs_self (D * F - (A : ℤ))
    omega
  have habs2 : -(F : ℤ) < 2 * (D * F - (A : ℤ)) := by
    have := neg_abs_le (D * F - (A : ℤ))
    omega
  have hdmz : 2 * (F : ℤ) * d + M = 2 * A + F := by exact_mod_cast hdm
  have hMz : (M : ℤ) < 2 * F := by exact_mod_cast hmodlt
  have hle : D ≤ d := by
    have h1 : D * (2 * F) < ((d : ℤ) + 1) * (2 * F) := by nlinarith
    have := lt_of_mul_lt_mul_right h1 (by positivity : (0 : ℤ) ≤ 2 * F)
    omega
  have hge : (d : ℤ) ≤ D := by
    have h1 : (d : ℤ) * (2 * F) < (D + 1) * (2 * F) := by nlinarith
    have := lt_of_mul_lt_mul_right h1 (by positivity : (0 : ℤ) ≤ 2 * F)
    omega
  omega

/-- A factorization `n = (xF + 1)(yF − 1)` with `x, y ≥ 1` and `F ≥ 6`
shows `n` composite. -/
private theorem not_prime_of_pm_factorization {n F : ℕ} (hF : 6 ≤ F)
    {x y : ℤ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hfact : ((x * F + 1) * (y * F - 1) : ℤ) = n) : ¬n.Prime := by
  lift x to ℕ using by omega with x'
  lift y to ℕ using by omega with y'
  have hx1 : 1 ≤ x' := by exact_mod_cast hx
  have hy1 : 1 ≤ y' := by exact_mod_cast hy
  have hgeB : 1 ≤ y' * F := Nat.mul_pos hy1 (by omega)
  have hfactN : (x' * F + 1) * (y' * F - 1) = n := by
    have hcast : (((x' * F + 1) * (y' * F - 1) : ℕ) : ℤ) = ((n : ℕ) : ℤ) := by
      push_cast [hgeB]
      linear_combination hfact
    exact_mod_cast hcast
  rw [← hfactN]
  have hxF : F ≤ x' * F := Nat.le_mul_of_pos_left F hx1
  have hyF : F ≤ y' * F := Nat.le_mul_of_pos_left F hy1
  exact Nat.not_prime_mul (by omega) (by omega)

/-- The prime side of condition (1): if `n = c₄F² + c₁F − 1` with
`c₄ ≥ 6` and the shifted discriminant at some `|t| ≤ 5` is a square,
then `n` factors as `(xF + 1)(yF − 1)` nontrivially — so `n` is
composite.  This is where `c₄ ≥ 6` earns its keep: it rules out the
trivial split `1 · n`, which the book's more generous band admits (see
the header for the `(n, F) = (223, 7)` counterexample). -/
private theorem not_prime_of_disc_square {n F c₁ c₄ : ℕ} {t : ℤ}
    (hF : 6 ≤ F) (hc4 : 6 ≤ c₄) (ht : t ≤ 5)
    (hdig : n + 1 = c₄ * F ^ 2 + c₁ * F)
    (hsq : IsSquare (((c₁ : ℤ) + t * F) ^ 2 - 4 * t + 4 * c₄)) :
    ¬n.Prime := by
  obtain ⟨r, hr⟩ := hsq
  set σ : ℤ := (c₁ : ℤ) + t * F with hσ
  set ρ : ℤ := (r.natAbs : ℤ) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ2 : ρ ^ 2 = σ ^ 2 - 4 * t + 4 * c₄ := by
    have : ρ ^ 2 = r * r := by
      rw [hρdef, sq]
      exact_mod_cast Int.natAbs_mul_self
    rw [this, ← hr]
  have hct : (1 : ℤ) ≤ (c₄ : ℤ) - t := by
    have : (6 : ℤ) ≤ c₄ := by exact_mod_cast hc4
    omega
  -- `ρ > |σ|`, and `ρ ∓ σ` are both even and at least 2
  have hρσ : σ ^ 2 < ρ ^ 2 := by nlinarith
  have hσρ : -ρ < σ ∧ σ < ρ := by
    constructor <;> nlinarith [sq_nonneg (σ + ρ), sq_nonneg (σ - ρ)]
  have heven : Even ((ρ - σ) * (ρ + σ)) := by
    refine ⟨2 * ((c₄ : ℤ) - t) - 2 * t * 0 + 0, ?_⟩
    nlinarith [hρ2]
  have hpar : Even (ρ - σ) := by
    rcases Int.even_mul.mp heven with h | h
    · exact h
    · obtain ⟨k, hk⟩ := h
      exact ⟨k - σ, by omega⟩
  obtain ⟨x, hx2⟩ : ∃ x : ℤ, ρ - σ = 2 * x := by
    obtain ⟨k, hk⟩ := hpar
    exact ⟨k, by omega⟩
  obtain ⟨y, hy2⟩ : ∃ y : ℤ, ρ + σ = 2 * y := by
    refine ⟨x + σ, by omega⟩
  have hx1 : 1 ≤ x := by omega
  have hy1 : 1 ≤ y := by omega
  have hxy : x * y = (c₄ : ℤ) - t := by nlinarith [hρ2]
  have hnz : ((n : ℤ)) + 1 = (c₄ : ℤ) * F ^ 2 + c₁ * F := by
    exact_mod_cast hdig
  have hfact : ((x * F + 1) * (y * F - 1) : ℤ) = n := by
    have hyx : y - x = σ := by omega
    linear_combination ((F : ℤ)) ^ 2 * hxy + (F : ℤ) * hyx - hnz
  exact not_prime_of_pm_factorization hF hx1 hy1 hfact


/-- **Crandall–Pomerance Theorem 4.2.9** (corrected; the book leaves
the proof as an exercise): the `n + 1` test at `F ≥ n^(3/10)`.
Suppose `n ≥ 214`, the Morrison hypotheses (4.14) hold,
`n + 1 = c₄F² + c₁F` with `c₁ < F` and `c₄ ≥ 6` (the corrected form of
the band's upper end — see the file header for the book's
`(n, F) = (223, 7)` counterexample), and `n³ ≤ F¹⁰`.  Let `u/v`
approximate `c₁/F` with `v²n < F⁴` and `(uF − c₁v)²F² ≤ n`, and let
`d = ⌊c₄v/F + 1/2⌋`.  Then `n` is prime iff (1) the eleven shifted
discriminants `(c₁ + tF)² − 4t + 4c₄` (`|t| ≤ 5`) are non-squares, and
(2) neither cubic has an integral root producing a nontrivial factor
`xF + 1` resp. `xF − 1` of `n`. -/
theorem theorem_4_2_9 {a b : ℤ} {n F c₁ c₄ u v d : ℕ} (hn : 214 ≤ n)
    (hcop : IsCoprime (n : ℤ) (2 * b))
    (hjac : jacobiSym (a ^ 2 - 4 * b) n = -1)
    (hdig : n + 1 = c₄ * F ^ 2 + c₁ * F) (hc1 : c₁ < F) (hc4 : 6 ≤ c₄)
    (hlo : n ^ 3 ≤ F ^ 10)
    (hU : (n : ℤ) ∣ lucasU a b (n + 1))
    (hq : ∀ q : ℕ, q.Prime → q ∣ F →
      IsCoprime (n : ℤ) (lucasU a b ((n + 1) / q)))
    (hv2 : v ^ 2 * n < F ^ 4)
    (happrox : ((u : ℤ) * F - c₁ * v) ^ 2 * F ^ 2 ≤ n)
    (hd : d = (2 * c₄ * v + F) / (2 * F)) :
    n.Prime ↔
      ((∀ t : ℤ, -5 ≤ t → t ≤ 5 →
          ¬IsSquare (((c₁ : ℤ) + t * F) ^ 2 - 4 * t + 4 * c₄)) ∧
        (¬∃ x : ℤ, (v : ℤ) * x ^ 3 - ((u : ℤ) * F - c₁ * v) * x ^ 2
              - ((c₄ : ℤ) * v - d * F + u) * x + d = 0
            ∧ (x * F + 1) ∣ (n : ℤ) ∧ 1 < x * F + 1 ∧ x * F + 1 < n) ∧
        (¬∃ x : ℤ, (v : ℤ) * x ^ 3 + ((u : ℤ) * F - c₁ * v) * x ^ 2
              + ((d : ℤ) * F - c₄ * v - u) * x - d = 0
            ∧ (x * F - 1) ∣ (n : ℤ) ∧ 1 < x * F - 1 ∧ x * F - 1 < n)) := by
  have hn1 : 1 < n := by omega
  have hF6 : 6 ≤ F := by
    by_contra h
    have hF5 : F ≤ 5 := by omega
    have h1 : F ^ 10 ≤ 5 ^ 10 := Nat.pow_le_pow_left hF5 10
    have h2 : 214 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
    norm_num at h1 h2
    omega
  have hFz : (6 : ℤ) ≤ F := by exact_mod_cast hF6
  have hFdvd : F ∣ n + 1 := ⟨c₄ * F + c₁, by rw [hdig]; ring⟩
  constructor
  · -- prime ⟹ (1) ∧ (2)
    intro hprime
    refine ⟨?_, ?_, ?_⟩
    · intro t _ h5b hsq
      exact not_prime_of_disc_square hF6 hc4 h5b hdig hsq hprime
    · -- a prime has no nontrivial factor `xF + 1`
      rintro ⟨x, _, hdvd, hgt, hlt⟩
      set z := x * (F : ℤ) + 1 with hz
      have hz0 : 0 ≤ z := by omega
      set m := z.toNat with hm
      have hzm : (m : ℤ) = z := Int.toNat_of_nonneg hz0
      have hmn : m ∣ n := by
        have : (m : ℤ) ∣ (n : ℤ) := hzm ▸ hdvd
        exact_mod_cast this
      rcases Nat.Prime.eq_one_or_self_of_dvd hprime m hmn with h1 | h1
      · rw [h1] at hzm
        omega
      · rw [h1] at hzm
        omega
    · -- nor a nontrivial factor `xF − 1`
      rintro ⟨x, _, hdvd, hgt, hlt⟩
      set z := x * (F : ℤ) - 1 with hz
      have hz0 : 0 ≤ z := by omega
      set m := z.toNat with hm
      have hzm : (m : ℤ) = z := Int.toNat_of_nonneg hz0
      have hmn : m ∣ n := by
        have : (m : ℤ) ∣ (n : ℤ) := hzm ▸ hdvd
        exact_mod_cast this
      rcases Nat.Prime.eq_one_or_self_of_dvd hprime m hmn with h1 | h1
      · rw [h1] at hzm
        omega
      · rw [h1] at hzm
        omega
  · -- (1) ∧ (2) ⟹ prime
    rintro ⟨h1, h2a, h2b⟩
    by_contra hcomp
    have : NeZero n := ⟨by omega⟩
    -- every prime factor is `≡ ±1 (mod F)` (Theorem 4.2.3 + Jacobi)
    have hΔn : Int.gcd (a ^ 2 - 4 * b) n = 1 := by
      by_contra h
      have h0 : jacobiSym (a ^ 2 - 4 * b) n = 0 :=
        jacobiSym.eq_zero_iff_not_coprime.mpr h
      rw [hjac] at h0
      norm_num at h0
    have hΔn' : Nat.Coprime (a ^ 2 - 4 * b).natAbs n := by
      rwa [Int.gcd, Int.natAbs_natCast] at hΔn
    have hJpm : ∀ p : ℕ, p.Prime → p ∣ n →
        jacobiSym (a ^ 2 - 4 * b) p = 1 ∨
          jacobiSym (a ^ 2 - 4 * b) p = -1 := by
      intro p hp hpn
      exact jacobiSym.eq_one_or_neg_one (by
        rw [Int.gcd, Int.natAbs_natCast]
        exact hΔn'.coprime_dvd_right hpn)
    have hp423 := theorem_4_2_3 (by omega) hcop hjac hFdvd hU hq
    have hpm : ∀ p : ℕ, p.Prime → p ∣ n →
        (F : ℤ) ∣ (p : ℤ) - 1 ∨ (F : ℤ) ∣ (p : ℤ) + 1 := by
      intro p hp hpn
      have hdvd := hp423 p hp hpn
      rcases hJpm p hp hpn with h | h <;> rw [h] at hdvd
      · exact Or.inl hdvd
      · rw [sub_neg_eq_add] at hdvd
        exact Or.inr hdvd
    have hnm1 : (F : ℤ) ∣ (n : ℤ) + 1 := by
      have h0 : ((F : ℕ) : ℤ) ∣ ((n + 1 : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr hFdvd
      push_cast at h0
      exact h0
    -- split `n = X·Y` with `X ≡ 1`, `Y ≡ −1 (mod F)`
    obtain ⟨X, Y, hXY, hX1, hY1, hXs, hYs⟩ :
        ∃ X Y : ℕ, n = X * Y ∧ 1 < X ∧ 1 < Y ∧
          (F : ℤ) ∣ (X : ℤ) - 1 ∧ (F : ℤ) ∣ (Y : ℤ) + 1 := by
      obtain ⟨m, hm⟩ := n.minFac_dvd
      have hP : n.minFac.Prime := Nat.minFac_prime (by omega)
      set P := n.minFac with hPdef
      have hP1 : 1 < P := hP.one_lt
      have hm1 : 1 < m := by
        rcases Nat.lt_or_ge m 2 with h | h
        · interval_cases m
          · omega
          · rw [mul_one] at hm
            exact absurd (hm ▸ hP) hcomp
        · exact h
      have hmn : m ∣ n := ⟨P, by rw [hm]; ring⟩
      have hnz2 : (n : ℤ) = P * m := by exact_mod_cast hm
      have hF2 : ¬(F : ℤ) ∣ 2 := by
        intro h
        have := Int.le_of_dvd (by norm_num) h
        omega
      rcases hpm P hP n.minFac_dvd with h | h <;>
          rcases dvd_pm_one hpm m (by omega) hmn with h' | h'
      · exfalso
        apply hF2
        have hd1 : (F : ℤ) ∣ (n : ℤ) - 1 := by
          have hdd : (F : ℤ) ∣ (m : ℤ) * ((P : ℤ) - 1) + ((m : ℤ) - 1) :=
            dvd_add (Dvd.dvd.mul_left h _) h'
          have he : (n : ℤ) - 1
              = (m : ℤ) * ((P : ℤ) - 1) + ((m : ℤ) - 1) := by
            rw [hnz2]
            ring
          rwa [← he] at hdd
        have hsub := dvd_sub hnm1 hd1
        have he2 : (n : ℤ) + 1 - ((n : ℤ) - 1) = 2 := by ring
        rwa [he2] at hsub
      · exact ⟨P, m, hm, hP1, hm1, h, h'⟩
      · exact ⟨m, P, by rw [hm]; ring, hm1, hP1, h', h⟩
      · exfalso
        apply hF2
        have hd1 : (F : ℤ) ∣ (n : ℤ) - 1 := by
          have hdd : (F : ℤ) ∣ (m : ℤ) * ((P : ℤ) + 1) - ((m : ℤ) + 1) :=
            dvd_sub (Dvd.dvd.mul_left h _) h'
          have he : (n : ℤ) - 1
              = (m : ℤ) * ((P : ℤ) + 1) - ((m : ℤ) + 1) := by
            rw [hnz2]
            ring
          rwa [← he] at hdd
        have hsub := dvd_sub hnm1 hd1
        have he2 : (n : ℤ) + 1 - ((n : ℤ) - 1) = 2 := by ring
        rwa [he2] at hsub
    -- coefficients: `X = xF + 1`, `Y = yF − 1` with `x, y ≥ 1`
    obtain ⟨xz, hxz⟩ := hXs
    obtain ⟨yz, hyz⟩ := hYs
    have hXz : (2 : ℤ) ≤ X := by exact_mod_cast hX1
    have hYz : (2 : ℤ) ≤ Y := by exact_mod_cast hY1
    have hx1 : 1 ≤ xz := by
      by_contra h
      push Not at h
      have : (F : ℤ) * xz ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
    have hy1 : 1 ≤ yz := by
      by_contra h
      push Not at h
      have : (F : ℤ) * yz ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
    lift xz to ℕ using (by omega) with x
    lift yz to ℕ using (by omega) with y
    have hx1' : 1 ≤ x := by exact_mod_cast hx1
    have hy1' : 1 ≤ y := by exact_mod_cast hy1
    have hXeq : X = x * F + 1 := by
      have hX' : (X : ℤ) = (x : ℤ) * F + 1 := by linear_combination hxz
      exact_mod_cast hX'
    have hYF : Y + 1 = y * F := by
      have hY' : ((Y : ℕ) : ℤ) + 1 = (y : ℤ) * F := by linear_combination hyz
      exact_mod_cast hY'
    have hYeq : Y = y * F - 1 := by omega
    have hfactN : n = (x * F + 1) * (y * F - 1) := by
      rw [hXY, hXeq, hYeq]
    have hnXY : n + (x * F + 1) = (x * F + 1) * (y * F) := by
      have h0 : n + X = X * (Y + 1) := by
        rw [hXY]
        ring
      rw [hXeq, hYF] at h0
      exact h0
    have hnfact : ((n : ℤ)) = ((x : ℤ) * F + 1) * ((y : ℤ) * F - 1) := by
      have hXz' : (X : ℤ) = (x : ℤ) * F + 1 := by exact_mod_cast hXeq
      have hYz' : (Y : ℤ) = (y : ℤ) * F - 1 := by
        have h0 : ((Y : ℕ) : ℤ) + 1 = (y : ℤ) * F := by exact_mod_cast hYF
        omega
      rw [show ((n : ℤ)) = (X : ℤ) * (Y : ℤ) from by exact_mod_cast hXY,
        hXz', hYz']
    -- digit matching
    have hnz1 : ((n : ℤ)) + 1 = (c₄ : ℤ) * F ^ 2 + c₁ * F := by
      exact_mod_cast hdig
    have hkey : (c₄ : ℤ) * F + c₁ = ((x : ℤ) * y) * F + ((y : ℤ) - x) := by
      have hcancel : ((c₄ : ℤ) * F + c₁) * F
          = (((x : ℤ) * y) * F + ((y : ℤ) - x)) * F := by
        have hexp : ((n : ℤ)) + 1
            = (((x : ℤ) * y) * F + ((y : ℤ) - x)) * F := by
          rw [hnfact]
          ring
        rw [← hexp, hnz1]
        ring
      exact mul_right_cancel₀ (by omega : (F : ℤ) ≠ 0) hcancel
    set t : ℤ := (c₄ : ℤ) - x * y with htdef
    have hyx : (y : ℤ) - x = c₁ + t * F := by
      linear_combination -hkey - (F : ℤ) * htdef
    have hxyprod : (x : ℤ) * y = c₄ - t := by
      linear_combination -htdef
    -- `W` and its bound (shared by both cubic cases)
    set W : ℕ := ((u : ℤ) * F - c₁ * v).natAbs with hW
    have hWn : W ^ 2 * F ^ 2 ≤ n := by
      have hcast : ((W : ℤ)) ^ 2 = ((u : ℤ) * F - c₁ * v) ^ 2 := by
        rw [hW, Int.natCast_natAbs, sq_abs]
      have hle : ((W : ℤ)) ^ 2 * (F : ℤ) ^ 2 ≤ (n : ℤ) := by
        rw [hcast]
        exact happrox
      exact_mod_cast hle
    have hd' : d = (2 * (c₄ * v) + F) / (2 * F) := by
      rw [hd, Nat.mul_assoc]
    by_cases ht6 : 6 ≤ t
    · -- CASE `t ≥ 6`: `x` is small; refute the first cubic condition
      set T := t.toNat with hTdef
      have hTz : (T : ℤ) = t := Int.toNat_of_nonneg (by omega)
      have hT6 : 6 ≤ T := by
        have h0 : (6 : ℤ) ≤ T := by omega
        exact_mod_cast h0
      have hyN : y = x + c₁ + T * F := by
        have hyz' : (y : ℤ) = x + c₁ + (T : ℤ) * F := by
          rw [hTz]
          linear_combination hyx
        exact_mod_cast hyz'
      have hTidz : (T : ℤ) * ((x : ℤ) * F + 1) = c₄ - x ^ 2 - x * c₁ := by
        rw [hTz]
        linear_combination (-(x : ℤ)) * hyx + hxyprod
      have hTidN : T * (x * F + 1) + x ^ 2 + x * c₁ = c₄ := by
        have hz2 : (T : ℤ) * ((x : ℤ) * F + 1) + (x : ℤ) ^ 2 + x * c₁ = c₄ := by
          linear_combination hTidz
        exact_mod_cast hz2
      -- `y ≥ 6F`, `5xF³ < n`, `TF³ < n`
      have hyF6 : 6 * F ≤ y := by
        have h6F : 6 * F ≤ T * F := Nat.mul_le_mul_right F hT6
        omega
      have hF2 : 36 ≤ F ^ 2 := by
        calc (36 : ℕ) = 6 ^ 2 := by norm_num
        _ ≤ F ^ 2 := Nat.pow_le_pow_left hF6 2
      have h5x : 5 * (x * F ^ 3) < n := by
        have hyFF : (6 * F) * F ≤ y * F := Nat.mul_le_mul_right F hyF6
        have hmul : (x * F + 1) * ((6 * F) * F) ≤ (x * F + 1) * (y * F) :=
          Nat.mul_le_mul_left _ hyFF
        rw [← hnXY] at hmul
        have hexp : (x * F + 1) * ((6 * F) * F)
            = 6 * (x * F ^ 3) + 6 * F ^ 2 := by ring
        have hxFle : x * F ≤ x * F ^ 3 := by
          have h0 : F ≤ F ^ 3 := by
            calc F = F ^ 1 := (pow_one F).symm
            _ ≤ F ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
          exact Nat.mul_le_mul_left x h0
        omega
      have hTF : T * F + 7 ≤ c₄ := by
        have hmul : T * (F + 1) ≤ T * (x * F + 1) :=
          Nat.mul_le_mul_left T (by
            have h0 : 1 * F ≤ x * F := Nat.mul_le_mul_right F hx1'
            omega)
        have hexp : T * (F + 1) = T * F + T := by ring
        have hx2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      have hTF3 : T * F ^ 3 < n := by
        have hmul : (T * F + 7) * F ^ 2 ≤ c₄ * F ^ 2 :=
          Nat.mul_le_mul_right _ hTF
        have hexp : (T * F + 7) * F ^ 2 = T * F ^ 3 + 7 * F ^ 2 := by ring
        omega
      -- budget chains: `5xW < F`, `15x²v < F`, `6Tv < F`
      have h5xW : 5 * (x * W) < F := by
        have hlt : (5 * (x * F ^ 3)) ^ 2 < n ^ 2 :=
          Nat.pow_lt_pow_left h5x two_ne_zero
        have hsq : (15 * (x * W)) ^ 2 * F ^ 8 < (3 * F) ^ 2 * F ^ 8 := by
          calc (15 * (x * W)) ^ 2 * F ^ 8
              = 9 * ((5 * (x * F ^ 3)) ^ 2 * (W ^ 2 * F ^ 2)) := by ring
          _ ≤ 9 * ((5 * (x * F ^ 3)) ^ 2 * n) :=
              Nat.mul_le_mul_left 9 (Nat.mul_le_mul_left _ hWn)
          _ < 9 * (n ^ 2 * n) := by
              have h9 := (Nat.mul_lt_mul_right (show 0 < n by omega)).mpr hlt
              omega
          _ = 9 * n ^ 3 := by ring
          _ ≤ 9 * F ^ 10 := Nat.mul_le_mul_left 9 hlo
          _ = (3 * F) ^ 2 * F ^ 8 := by ring
        have h2 : (15 * (x * W)) ^ 2 < (3 * F) ^ 2 :=
          lt_of_mul_lt_mul_right hsq (Nat.zero_le _)
        have h3 : 15 * (x * W) < 3 * F :=
          (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
        omega
      have h15x2v : 15 * (x ^ 2 * v) < F := by
        have hlt : (5 * (x * F ^ 3)) ^ 2 < n ^ 2 :=
          Nat.pow_lt_pow_left h5x two_ne_zero
        have h25 : 25 * (x ^ 2 * F ^ 6) < n ^ 2 := by
          have he : 25 * (x ^ 2 * F ^ 6) = (5 * (x * F ^ 3)) ^ 2 := by ring
          omega
        have h625 : 625 * (x ^ 4 * F ^ 2) < n := by
          have hlt2 : (25 * (x ^ 2 * F ^ 6)) ^ 2 < (n ^ 2) ^ 2 :=
            Nat.pow_lt_pow_left h25 two_ne_zero
          have hchain : (625 * (x ^ 4 * F ^ 2)) * F ^ 10 < n * F ^ 10 := by
            calc (625 * (x ^ 4 * F ^ 2)) * F ^ 10
                = (25 * (x ^ 2 * F ^ 6)) ^ 2 := by ring
            _ < (n ^ 2) ^ 2 := hlt2
            _ = n ^ 3 * n := by ring
            _ ≤ F ^ 10 * n := Nat.mul_le_mul_right n hlo
            _ = n * F ^ 10 := by ring
          exact lt_of_mul_lt_mul_right hchain (Nat.zero_le _)
        have hpos : 0 < 225 * x ^ 4 := by positivity
        have hchain2 : (15 * (x ^ 2 * v)) ^ 2 * n < F ^ 2 * n := by
          calc (15 * (x ^ 2 * v)) ^ 2 * n
              = 225 * x ^ 4 * (v ^ 2 * n) := by ring
          _ < 225 * x ^ 4 * F ^ 4 := (Nat.mul_lt_mul_left hpos).mpr hv2
          _ = (225 * (x ^ 4 * F ^ 2)) * F ^ 2 := by ring
          _ ≤ n * F ^ 2 := Nat.mul_le_mul_right _ (by omega)
          _ = F ^ 2 * n := by ring
        have h2 : (15 * (x ^ 2 * v)) ^ 2 < F ^ 2 :=
          lt_of_mul_lt_mul_right hchain2 (Nat.zero_le _)
        exact (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
      have h6Tv : 6 * (T * v) < F := by
        have hT2 : 6 * T ≤ T * T := Nat.mul_le_mul_right T hT6
        have hTF6 : (T * F ^ 3) ^ 2 < n ^ 2 :=
          Nat.pow_lt_pow_left hTF3 two_ne_zero
        have hbig : (6 * (T * v)) ^ 2 * (F ^ 12 * n)
            < F ^ 2 * (F ^ 12 * n) := by
          calc (6 * (T * v)) ^ 2 * (F ^ 12 * n)
              = ((6 * T) * (6 * T)) * (F ^ 12) * (v ^ 2 * n) := by ring
          _ ≤ ((T * T) * (T * T)) * (F ^ 12) * (v ^ 2 * n) := by
              have h0 := Nat.mul_le_mul hT2 hT2
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h0)
          _ = ((T * F ^ 3) ^ 2) ^ 2 * (v ^ 2 * n) := by ring
          _ ≤ (n ^ 2) ^ 2 * (v ^ 2 * n) :=
              Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hTF6.le 2)
          _ < (n ^ 2) ^ 2 * F ^ 4 :=
              (Nat.mul_lt_mul_left (by positivity)).mpr hv2
          _ = n ^ 3 * (n * F ^ 4) := by ring
          _ ≤ F ^ 10 * (n * F ^ 4) := Nat.mul_le_mul_right _ hlo
          _ = F ^ 2 * (F ^ 12 * n) := by ring
        have h2 : (6 * (T * v)) ^ 2 < F ^ 2 :=
          lt_of_mul_lt_mul_right hbig (Nat.zero_le _)
        exact (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
      -- pin `D = d`
      set D : ℕ := x * u + x * (T * v) with hDdef
      set E : ℤ := (D : ℤ) * F - (c₄ * v : ℕ) with hEdef
      have hEid : E = (x : ℤ) * ((u : ℤ) * F - c₁ * v)
          - ((x : ℤ) ^ 2 + T) * v := by
        rw [hEdef, hDdef]
        push_cast
        linear_combination (v : ℤ) * hTidz
      have hEabs : E.natAbs ≤ x * W + (x ^ 2 + T) * v := by
        have h0 : E = (x : ℤ) * ((u : ℤ) * F - c₁ * v)
            + -(((x : ℤ) ^ 2 + T) * v) := by
          rw [hEid]
          ring
        calc E.natAbs
            ≤ ((x : ℤ) * ((u : ℤ) * F - c₁ * v)).natAbs
              + (-(((x : ℤ) ^ 2 + T) * v)).natAbs := by
              rw [h0]
              exact Int.natAbs_add_le _ _
        _ = x * W + (x ^ 2 + T) * v := by
            rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_mul, ← hW]
            have hxa : ((x : ℤ)).natAbs = x := Int.natAbs_natCast x
            have hva : ((v : ℤ)).natAbs = v := Int.natAbs_natCast v
            have hxT : (((x : ℤ)) ^ 2 + T).natAbs = x ^ 2 + T := by
              have he : ((x : ℤ)) ^ 2 + T = ((x ^ 2 + T : ℕ) : ℤ) := by
                push_cast
                ring
              rw [he, Int.natAbs_natCast]
            rw [hxa, hva, hxT]
      have hsplitv : (x ^ 2 + T) * v = x ^ 2 * v + T * v := by ring
      have h2E : 2 * E.natAbs < F := by omega
      have hEpin : 2 * |E| < (F : ℤ) := by
        have hcast : ((2 * E.natAbs : ℕ) : ℤ) < ((F : ℕ) : ℤ) := by
          exact_mod_cast h2E
        rw [← Int.natCast_natAbs]
        push_cast at hcast ⊢
        linarith
      have hDd : ((D : ℕ) : ℤ) = d := by
        refine nearest_pin (by omega) hd' ?_
        rw [← hEdef]
        exact hEpin
      -- `x` roots the first cubic; `xF + 1` is a nontrivial factor
      apply h2a
      refine ⟨(x : ℤ), ?_, ⟨(y : ℤ) * F - 1, hnfact⟩, ?_, ?_⟩
      · have hdz : (d : ℤ) = (x : ℤ) * u + (x : ℤ) * (T * v) := by
          rw [← hDd, hDdef]
          push_cast
          ring
        linear_combination ((x : ℤ) * v) * hTidz + ((F : ℤ) * x + 1) * hdz
      · have h1x : (1 : ℤ) ≤ x := by exact_mod_cast hx1'
        have hxF : (1 : ℤ) * 6 ≤ (x : ℤ) * F :=
          mul_le_mul h1x hFz (by norm_num) (by omega)
        omega
      · have h1y : (1 : ℤ) ≤ y := by exact_mod_cast hy1'
        have hyFz : (1 : ℤ) * 6 ≤ (y : ℤ) * F :=
          mul_le_mul h1y hFz (by norm_num) (by omega)
        have h1x : (1 : ℤ) ≤ x := by exact_mod_cast hx1'
        have hxFz : (1 : ℤ) * 1 ≤ (x : ℤ) * F :=
          mul_le_mul h1x (by omega) (by norm_num) (by omega)
        have he : (n : ℤ) - ((x : ℤ) * F + 1)
            = ((x : ℤ) * F + 1) * ((y : ℤ) * F - 2) := by
          linear_combination hnfact
        have hpos : (0 : ℤ) < ((x : ℤ) * F + 1) * ((y : ℤ) * F - 2) :=
          mul_pos (by omega) (by omega)
        omega
    · by_cases htm6 : t ≤ -6
      · -- CASE `t ≤ −6`: `y` is small; refute the second cubic condition
        set S := (-t).toNat with hSdef
        have hSz : (S : ℤ) = -t := Int.toNat_of_nonneg (by omega)
        have hS6 : 6 ≤ S := by
          have h0 : (6 : ℤ) ≤ S := by omega
          exact_mod_cast h0
        have hxN : x + c₁ = y + S * F := by
          have hxz' : (x : ℤ) + c₁ = y + (S : ℤ) * F := by
            rw [hSz]
            linear_combination -hyx
          exact_mod_cast hxz'
        have hSidz : (S : ℤ) * ((y : ℤ) * F - 1) = c₄ + y * c₁ - y ^ 2 := by
          rw [hSz]
          linear_combination (y : ℤ) * hyx + hxyprod
        -- `x ≥ 5F + 2`, `4yF³ < n`, `F ≥ 124`, `16S²F² ≤ n`
        have hx5F : 5 * F + 2 ≤ x := by
          have h6F : 6 * F ≤ S * F := Nat.mul_le_mul_right F hS6
          omega
        have hyFge : F ≤ y * F := by
          have h0 : 1 * F ≤ y * F := Nat.mul_le_mul_right F hy1'
          omega
        have h4y : 4 * (y * F ^ 3) < n := by
          have hB : (x * F + 1) * (F - 1) ≤ n := by
            rw [hfactN]
            exact Nat.mul_le_mul_left _ (by omega)
          have hxF2 : (x * F + 1) * (F - 1) + (x * F + 1) = x * F ^ 2 + F := by
            have hF1 : F - 1 + 1 = F := by omega
            calc (x * F + 1) * (F - 1) + (x * F + 1)
                = (x * F + 1) * ((F - 1) + 1) := by ring
            _ = (x * F + 1) * F := by rw [hF1]
            _ = x * F ^ 2 + F := by ring
          have hA : 5 * (y * F ^ 3) ≤ n + (x * F + 1) := by
            have h5F2 : 5 * F ^ 2 ≤ x * F + 1 := by
              have h0 : (5 * F) * F ≤ x * F := Nat.mul_le_mul_right F (by omega)
              have hexp : (5 * F) * F = 5 * F ^ 2 := by ring
              omega
            have hmul : (5 * F ^ 2) * (y * F) ≤ (x * F + 1) * (y * F) :=
              Nat.mul_le_mul_right _ h5F2
            rw [← hnXY] at hmul
            have hexp : (5 * F ^ 2) * (y * F) = 5 * (y * F ^ 3) := by ring
            omega
          have hA12 : 6 * (x * F) ≤ x * F ^ 2 := by
            have h0 : (x * F) * 6 ≤ (x * F) * F := Nat.mul_le_mul_left _ hF6
            have hexp : (x * F) * F = x * F ^ 2 := by ring
            omega
          have hQ216 : 216 ≤ y * F ^ 3 := by
            have h63 : 216 ≤ F ^ 3 := by
              calc (216 : ℕ) = 6 ^ 3 := by norm_num
              _ ≤ F ^ 3 := Nat.pow_le_pow_left hF6 3
            have h0 : 1 * F ^ 3 ≤ y * F ^ 3 := Nat.mul_le_mul_right _ hy1'
            omega
          omega
        have hxFn : x * (F * (F - 1)) ≤ n := by
          have hB : (x * F) * (F - 1) ≤ n := by
            rw [hfactN]
            calc (x * F) * (F - 1)
                ≤ (x * F + 1) * (F - 1) := Nat.mul_le_mul_right _ (by omega)
            _ ≤ (x * F + 1) * (y * F - 1) := Nat.mul_le_mul_left _ (by omega)
          have hexp : x * (F * (F - 1)) = (x * F) * (F - 1) := by ring
          omega
        have hF124 : 124 ≤ F := by
          by_contra h
          push Not at h
          have hnlow : (5 * F ^ 2 + 2 * F + 1) * (F - 1) ≤ n := by
            rw [hfactN]
            refine Nat.mul_le_mul ?_ (by omega)
            have h0 : (5 * F + 2) * F ≤ x * F := Nat.mul_le_mul_right F hx5F
            have hexp : (5 * F + 2) * F = 5 * F ^ 2 + 2 * F := by ring
            omega
          have hn3 : ((5 * F ^ 2 + 2 * F + 1) * (F - 1)) ^ 3 ≤ n ^ 3 :=
            Nat.pow_le_pow_left hnlow 3
          have hFineq : ((5 * F ^ 2 + 2 * F + 1) * (F - 1)) ^ 3 ≤ F ^ 10 :=
            le_trans hn3 hlo
          have hforall : ∀ G ∈ Finset.Ico 6 124,
              (G : ℕ) ^ 10 < ((5 * G ^ 2 + 2 * G + 1) * (G - 1)) ^ 3 := by
            set_option maxRecDepth 8192 in decide
          have := hforall F (Finset.mem_Ico.mpr ⟨hF6, by omega⟩)
          omega
        have h13824 : 13824 * F ^ 4 ≤ (F - 1) ^ 6 := by
          have hstep : 123 * F ≤ 124 * (F - 1) := by omega
          have h4 : (123 * F) ^ 4 ≤ (124 * (F - 1)) ^ 4 :=
            Nat.pow_le_pow_left hstep 4
          have hnum : 13824 * 124 ^ 4 ≤ 123 ^ 6 := by norm_num
          have h123sq : 123 ^ 2 ≤ (F - 1) ^ 2 :=
            Nat.pow_le_pow_left (by omega) 2
          have hchain : 123 ^ 4 * (13824 * F ^ 4)
              ≤ 123 ^ 4 * ((F - 1) ^ 6) := by
            calc 123 ^ 4 * (13824 * F ^ 4)
                = 13824 * (123 * F) ^ 4 := by ring
            _ ≤ 13824 * (124 * (F - 1)) ^ 4 := Nat.mul_le_mul_left _ h4
            _ = (13824 * 124 ^ 4) * (F - 1) ^ 4 := by ring
            _ ≤ 123 ^ 6 * (F - 1) ^ 4 := Nat.mul_le_mul_right _ hnum
            _ = 123 ^ 4 * (123 ^ 2 * (F - 1) ^ 4) := by ring
            _ ≤ 123 ^ 4 * ((F - 1) ^ 2 * (F - 1) ^ 4) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h123sq)
            _ = 123 ^ 4 * ((F - 1) ^ 6) := by ring
          exact Nat.le_of_mul_le_mul_left hchain (by norm_num)
        have h24n : 24 * n ≤ (F * (F - 1)) ^ 2 := by
          have hcube : (24 * n) ^ 3 ≤ ((F * (F - 1)) ^ 2) ^ 3 := by
            calc (24 * n) ^ 3 = 13824 * n ^ 3 := by ring
            _ ≤ 13824 * F ^ 10 := Nat.mul_le_mul_left _ hlo
            _ = F ^ 6 * (13824 * F ^ 4) := by ring
            _ ≤ F ^ 6 * (F - 1) ^ 6 := Nat.mul_le_mul_left _ h13824
            _ = ((F * (F - 1)) ^ 2) ^ 3 := by ring
          exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hcube
        have h24x2 : 24 * x ^ 2 ≤ n := by
          have hpos : 0 < (F * (F - 1)) ^ 2 := by
            have h0 : 0 < F * (F - 1) := Nat.mul_pos (by omega) (by omega)
            positivity
          have hchain : (24 * x ^ 2) * (F * (F - 1)) ^ 2
              ≤ n * (F * (F - 1)) ^ 2 := by
            calc (24 * x ^ 2) * (F * (F - 1)) ^ 2
                = 24 * (x * (F * (F - 1))) ^ 2 := by ring
            _ ≤ 24 * n ^ 2 :=
                Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hxFn 2)
            _ = n * (24 * n) := by ring
            _ ≤ n * (F * (F - 1)) ^ 2 := Nat.mul_le_mul_left n h24n
          exact Nat.le_of_mul_le_mul_right hchain hpos
        have h16S : 16 * (S ^ 2 * F ^ 2) ≤ n := by
          have hSF : S * F ≤ x + F := by omega
          have h56 : 5 * (x + F) ≤ 6 * x := by omega
          have hsq1 : (5 * (S * F)) ^ 2 ≤ (6 * x) ^ 2 := by
            refine Nat.pow_le_pow_left ?_ 2
            calc 5 * (S * F) ≤ 5 * (x + F) := Nat.mul_le_mul_left 5 hSF
            _ ≤ 6 * x := h56
          have hchain : 25 * (16 * (S ^ 2 * F ^ 2)) ≤ 25 * n := by
            calc 25 * (16 * (S ^ 2 * F ^ 2)) = 16 * (5 * (S * F)) ^ 2 := by ring
            _ ≤ 16 * (6 * x) ^ 2 := Nat.mul_le_mul_left 16 hsq1
            _ = 24 * (24 * x ^ 2) := by ring
            _ ≤ 24 * n := Nat.mul_le_mul_left 24 h24x2
            _ ≤ 25 * n := Nat.mul_le_mul_right n (by norm_num)
          exact Nat.le_of_mul_le_mul_left hchain (by norm_num)
        -- budget chains: `4Sv < F`, `4y²v < F`, `4yW < F`
        have h4Sv : 4 * (S * v) < F := by
          have hS2 : 0 < 16 * S ^ 2 := by positivity
          have hchain : (4 * (S * v)) ^ 2 * n < F ^ 2 * n := by
            calc (4 * (S * v)) ^ 2 * n = 16 * S ^ 2 * (v ^ 2 * n) := by ring
            _ < 16 * S ^ 2 * F ^ 4 := (Nat.mul_lt_mul_left hS2).mpr hv2
            _ = (16 * (S ^ 2 * F ^ 2)) * F ^ 2 := by ring
            _ ≤ n * F ^ 2 := Nat.mul_le_mul_right _ h16S
            _ = F ^ 2 * n := by ring
          have h2 : (4 * (S * v)) ^ 2 < F ^ 2 :=
            lt_of_mul_lt_mul_right hchain (Nat.zero_le _)
          exact (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
        have h4y2v : 4 * (y ^ 2 * v) < F := by
          have h16y : (4 * (y * F ^ 3)) ^ 2 < n ^ 2 :=
            Nat.pow_lt_pow_left h4y two_ne_zero
          have h256 : 256 * (y ^ 4 * F ^ 2) < n := by
            have hlt : (16 * (y ^ 2 * F ^ 6)) ^ 2 < (n ^ 2) ^ 2 := by
              have he : 16 * (y ^ 2 * F ^ 6) = (4 * (y * F ^ 3)) ^ 2 := by ring
              rw [he]
              exact Nat.pow_lt_pow_left h16y two_ne_zero
            have hchain : (256 * (y ^ 4 * F ^ 2)) * F ^ 10 < n * F ^ 10 := by
              calc (256 * (y ^ 4 * F ^ 2)) * F ^ 10
                  = (16 * (y ^ 2 * F ^ 6)) ^ 2 := by ring
              _ < (n ^ 2) ^ 2 := hlt
              _ = n ^ 3 * n := by ring
              _ ≤ F ^ 10 * n := Nat.mul_le_mul_right n hlo
              _ = n * F ^ 10 := by ring
            exact lt_of_mul_lt_mul_right hchain (Nat.zero_le _)
          have hpos : 0 < 16 * y ^ 4 := by positivity
          have hchain2 : (4 * (y ^ 2 * v)) ^ 2 * n < F ^ 2 * n := by
            calc (4 * (y ^ 2 * v)) ^ 2 * n
                = 16 * y ^ 4 * (v ^ 2 * n) := by ring
            _ < 16 * y ^ 4 * F ^ 4 := (Nat.mul_lt_mul_left hpos).mpr hv2
            _ = (16 * (y ^ 4 * F ^ 2)) * F ^ 2 := by ring
            _ ≤ (256 * (y ^ 4 * F ^ 2)) * F ^ 2 :=
                Nat.mul_le_mul_right _ (by omega)
            _ ≤ n * F ^ 2 := Nat.mul_le_mul_right _ (by omega)
            _ = F ^ 2 * n := by ring
          have h2 : (4 * (y ^ 2 * v)) ^ 2 < F ^ 2 :=
            lt_of_mul_lt_mul_right hchain2 (Nat.zero_le _)
          exact (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
        have h4yW : 4 * (y * W) < F := by
          have hlt : (4 * (y * F ^ 3)) ^ 2 < n ^ 2 :=
            Nat.pow_lt_pow_left h4y two_ne_zero
          have hsq : (12 * (y * W)) ^ 2 * F ^ 8 < (3 * F) ^ 2 * F ^ 8 := by
            calc (12 * (y * W)) ^ 2 * F ^ 8
                = 9 * ((4 * (y * F ^ 3)) ^ 2 * (W ^ 2 * F ^ 2)) := by ring
            _ ≤ 9 * ((4 * (y * F ^ 3)) ^ 2 * n) :=
                Nat.mul_le_mul_left 9 (Nat.mul_le_mul_left _ hWn)
            _ < 9 * (n ^ 2 * n) := by
                have h9 := (Nat.mul_lt_mul_right (show 0 < n by omega)).mpr hlt
                omega
            _ = 9 * n ^ 3 := by ring
            _ ≤ 9 * F ^ 10 := Nat.mul_le_mul_left 9 hlo
            _ = (3 * F) ^ 2 * F ^ 8 := by ring
          have h2 : (12 * (y * W)) ^ 2 < (3 * F) ^ 2 :=
            lt_of_mul_lt_mul_right hsq (Nat.zero_le _)
          have h3 : 12 * (y * W) < 3 * F :=
            (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
          omega
        -- pin `D = d`
        set D : ℤ := (y : ℤ) * ((S : ℤ) * v) - y * u with hDdef
        set E : ℤ := D * F - (c₄ * v : ℕ) with hEdef
        have hEid : E = -((y : ℤ) * ((u : ℤ) * F - c₁ * v))
            + ((S : ℤ) - y ^ 2) * v := by
          rw [hEdef, hDdef]
          push_cast
          linear_combination (v : ℤ) * hSidz
        set Z : ℕ := ((S : ℤ) - y ^ 2).natAbs with hZ
        have hEabs : E.natAbs ≤ y * W + Z * v := by
          calc E.natAbs
              ≤ (-((y : ℤ) * ((u : ℤ) * F - c₁ * v))).natAbs
                + (((S : ℤ) - y ^ 2) * v).natAbs := by
                rw [hEid]
                exact Int.natAbs_add_le _ _
          _ = y * W + Z * v := by
              rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_mul, ← hW, ← hZ]
              rw [Int.natAbs_natCast, Int.natAbs_natCast]
        have hZv : 4 * (Z * v) < F := by
          rcases le_total ((y : ℤ) ^ 2) (S : ℤ) with hcase | hcase
          · have hZS : Z ≤ S := by
              have hz2 : ((Z : ℕ) : ℤ) = (S : ℤ) - y ^ 2 := by
                rw [hZ]
                exact Int.natAbs_of_nonneg (by omega)
              have h0 : ((Z : ℕ) : ℤ) ≤ ((S : ℕ) : ℤ) := by
                rw [hz2]
                have : (0 : ℤ) ≤ (y : ℤ) ^ 2 := by positivity
                omega
              exact_mod_cast h0
            have h0 : Z * v ≤ S * v := Nat.mul_le_mul_right v hZS
            omega
          · have hZy : Z ≤ y ^ 2 := by
              have hz2 : ((Z : ℕ) : ℤ) = (y : ℤ) ^ 2 - S := by
                rw [hZ, ← Int.natAbs_neg, neg_sub]
                exact Int.natAbs_of_nonneg (by omega)
              have hy2c : ((y ^ 2 : ℕ) : ℤ) = (y : ℤ) ^ 2 := by
                push_cast
                ring
              have h0 : ((Z : ℕ) : ℤ) ≤ ((y ^ 2 : ℕ) : ℤ) := by
                rw [hz2, hy2c]
                have : (0 : ℤ) ≤ (S : ℤ) := by positivity
                omega
              exact_mod_cast h0
            have h0 : Z * v ≤ y ^ 2 * v := Nat.mul_le_mul_right v hZy
            omega
        have h2E : 2 * E.natAbs < F := by omega
        have hEpin : 2 * |E| < (F : ℤ) := by
          have hcast : ((2 * E.natAbs : ℕ) : ℤ) < ((F : ℕ) : ℤ) := by
            exact_mod_cast h2E
          rw [← Int.natCast_natAbs]
          push_cast at hcast ⊢
          linarith
        have hDd : D = (d : ℤ) := by
          refine nearest_pin (by omega) hd' ?_
          rw [← hEdef]
          exact hEpin
        -- `y` roots the second cubic; `yF − 1` is a nontrivial factor
        apply h2b
        refine ⟨(y : ℤ), ?_, ⟨(x : ℤ) * F + 1, by rw [hnfact]; ring⟩, ?_, ?_⟩
        · have hdz : (d : ℤ) = (y : ℤ) * ((S : ℤ) * v) - y * u := by
            rw [← hDd, hDdef]
          linear_combination ((y : ℤ) * v) * hSidz + ((F : ℤ) * y - 1) * hdz
        · have h1y : (1 : ℤ) ≤ y := by exact_mod_cast hy1'
          have hyFz : (1 : ℤ) * 6 ≤ (y : ℤ) * F :=
            mul_le_mul h1y hFz (by norm_num) (by omega)
          omega
        · have h1y : (1 : ℤ) ≤ y := by exact_mod_cast hy1'
          have hyFz : (1 : ℤ) * 6 ≤ (y : ℤ) * F :=
            mul_le_mul h1y hFz (by norm_num) (by omega)
          have h5x : (5 : ℤ) ≤ (x : ℤ) := by
            exact_mod_cast (show 5 ≤ x by omega)
          have hxFz : (5 : ℤ) * 6 ≤ (x : ℤ) * F :=
            mul_le_mul h5x hFz (by norm_num) (by omega)
          have he : (n : ℤ) - ((y : ℤ) * F - 1)
              = ((y : ℤ) * F - 1) * ((x : ℤ) * F) := by
            linear_combination hnfact
          have hpos : (0 : ℤ) < ((y : ℤ) * F - 1) * ((x : ℤ) * F) :=
            mul_pos (by omega) (by omega)
          omega
      · -- CASE `|t| ≤ 5`: the discriminant at `t` is the square `(x + y)²`
        have h5a : -5 ≤ t := by omega
        have h5b : t ≤ 5 := by omega
        refine h1 t h5a h5b ⟨(x : ℤ) + y, ?_⟩
        linear_combination (-((y : ℤ) - x + c₁ + t * F)) * hyx - 4 * hxyprod

section Example

/-- `251` is prime by the corrected Theorem 4.2.9 with the Lucas pair
`(a, b) = (1, 2)` (`Δ = −7`), `F = 6`, `252 = 7·6² + 0·6`
(`c₄ = 7`, `c₁ = 0`), approximation `u/v = 0/1`, `d = 1`: the eleven
shifted discriminants `36t² − 4t + 28` (`|t| ≤ 5`) are all
non-squares, and the two cubics `x³ − x + 1` and `x³ − x − 1` have no
integral roots at all. -/
example : Nat.Prime 251 := by
  refine (theorem_4_2_9 (a := 1) (b := 2) (F := 6) (c₁ := 0) (c₄ := 7)
    (u := 0) (v := 1) (d := 1) (by norm_num)
    (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by set_option maxRecDepth 8192 in decide)
    ?_ (by norm_num) (by norm_num) (by norm_num)).mpr ⟨?_, ?_, ?_⟩
  · intro q hq hqF
    have hq23 : q = 2 ∨ q = 3 := by
      have hle : q ≤ 6 := Nat.le_of_dvd (by norm_num) hqF
      interval_cases q <;> revert hqF hq <;> decide
    rcases hq23 with rfl | rfl
    · rw [Int.isCoprime_iff_gcd_eq_one]
      set_option maxRecDepth 8192 in decide
    · rw [Int.isCoprime_iff_gcd_eq_one]
      set_option maxRecDepth 8192 in decide
  · intro t h5a h5b
    interval_cases t
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 30) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 24) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 19) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 13) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 8) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 5) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 7) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 12) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 18) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 24) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 30) (by norm_num)
        (by norm_num)
  · rintro ⟨x, hroot, hdvd, hgt, hlt⟩
    norm_num at hroot
    have hx1 : 1 ≤ x := by omega
    rcases eq_or_lt_of_le hx1 with rfl | hx2
    · norm_num at hroot
    · have hx2' : 2 ≤ x := hx2
      nlinarith [hroot, hx2', sq_nonneg (x - 2),
        mul_nonneg (by linarith : (0 : ℤ) ≤ x - 2) (sq_nonneg x)]
  · rintro ⟨x, hroot, hdvd, hgt, hlt⟩
    norm_num at hroot
    have hx1 : 1 ≤ x := by omega
    rcases eq_or_lt_of_le hx1 with rfl | hx2
    · norm_num at hroot
    · have hx2' : 2 ≤ x := hx2
      nlinarith [hroot, hx2', sq_nonneg (x - 2),
        mul_nonneg (by linarith : (0 : ℤ) ≤ x - 2) (sq_nonneg x)]

end Example

end CP

end Azurite
