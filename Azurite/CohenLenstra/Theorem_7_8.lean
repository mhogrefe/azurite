/-
  **Cohen–Lenstra Theorem (7.8): the converse — a verified Gauss-sum
  congruence forces the character condition (6.5).**

  Let `χ` be a character mod `q` of order `p^k`, and suppose the
  tested congruence (7.9) holds:

    `τ(χ)^((n−σ_n)β) ≡ ζ₀  (mod 𝔫)`,  `ζ₀ ∈ U_{p^k}`,

  for some `β ∈ ℤ[G]` satisfying (7.6) and some ideal `𝔫` satisfying
  (7.7).  If moreover the `p`-adic condition (6.4) holds, then `χ`
  satisfies (6.5): `χ(r) = χ(n)^(l_p(r))` for every divisor `r ∣ n`.

  Formal rendering (Galois-free, finite-level, per prime divisor):

  * the ambient ring is any domain `R` carrying a primitive `p^k`-th
    root `ζ` and the characters; the Galois element `σ_n` is an
    abstract ring endomorphism `σ` with `σ(χ(a)) = χ(a)^n`,
    `σ(ψ(a)) = ψ(a)`, `σ(ζ) = ζ^n` (concrete models provide it);
  * the ideal `𝔫` is an ideal `I` with `n ∈ I`, `σ[I] ⊆ I`, and
    `I ∩ ℤ ⊆ nℤ` — the paper's (7.7);
  * `β = Σ_{x ∈ S} ν(x)·σ_x` with `p ∤ x` on `S`, and (7.6) is
    `p ∤ Σ ν(x)·x`;
  * `ζ₀ = ζ^(e₀)`, and (7.9) is the unit-free
    `u^n ≡ ζ^(e₀)·σ(u) (mod I)` for `u = ∏_x τ(χ^x)^ν(x)`;
  * (6.4) for the prime `r ∣ n` enters at finite level: an exponent
    `m` with `p^(v_p(N)) ∣ r^(p−1) − n^((p−1)m)` in `ℤ`, where
    `N = n^((p−1)p^k) − 1` — the paper's (7.14)/(7.15);
  * `η` is encoded by an exponent `f` with `p^k ∣ e₀ + n·c(β)·f`
    (i.e. `ζ^(e₀) = η^(−nβ)` for `η = ζ^f`), and the conclusion is
    `χ(r) = ζ^(f·m)`, the paper's `χ(r) = η^(l_p(r))`.

  The proof follows the paper: telescoping the `σ`-twists of (7.9)
  gives `u^(n^i) ≡ ζ^(e₀·i·n^(i−1))·σ^i(u) (mod I)` (their (7.11)),
  with period (7.12) at `i = (p−1)p^k`; telescoping the instances of
  Lemma (7.3) at the prime `r` gives their (7.13) modulo `rR`; the
  two combine modulo `J = I + (r)` (their `𝔯`) via
  `σ_r^(p−1) = σ_n^((p−1)m)` (from (7.16)); raising to the `p`-free
  part `a` of `N` and cancelling the unit `u` (Gauss sums are units
  modulo `J` since `τ(χ')·τ(χ'⁻¹,ψ⁻¹) = q` and `q` is invertible mod
  `r`) leaves a root of unity congruent to `1` mod `J`, which is `1`
  by Lemma (7.17); the exponent arithmetic modulo `p^k` (where `p−1`,
  `c(β)`, `a`, `n`, `r` are all units) yields `χ(r) = ζ^(fm)`.
-/
import Azurite.CohenLenstra.Corollary_7_5
import Azurite.CohenLenstra.Lemma_7_17
import Azurite.CohenLenstra.Proposition_7_18
import Azurite.CohenLenstra.Theorem_6_3

namespace Azurite

namespace CL

open Finset

section Theorem78

variable {R : Type _} [CommRing R] {q n : ℕ} [Fact q.Prime]
variable {χ : MulChar (ZMod q) R} {ψ : AddChar (ZMod q) R}
variable {ζ : R} {σ : R →+* R} {I : Ideal R}
variable {S : Finset ℕ} {ν : ℕ → ℕ} {e₀ : ℕ}

/-- `σ` moves the Gauss sum of `χ^y` to that of `χ^(y·n)`. -/
theorem sigma_gaussSum
    (hσχ : ∀ a : ZMod q, σ (χ a) = χ a ^ n)
    (hσψ : ∀ a : ZMod q, σ (ψ a) = ψ a)
    (hn0 : n ≠ 0) {y : ℕ} (hy : y ≠ 0) :
    σ (gaussSum (χ ^ y) ψ) = gaussSum (χ ^ (y * n)) ψ := by
  rw [gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, hσψ a, MulChar.pow_apply' χ hy a,
    MulChar.pow_apply' χ (mul_ne_zero hy hn0) a, map_pow, hσχ a,
    ← pow_mul, mul_comm n y]

/-- Ideal-membership transfers along divisibility. -/
private theorem memdvd {J : Ideal R} {a b : R} (ha : a ∈ J)
    (hab : a ∣ b) : b ∈ J := by
  obtain ⟨d, rfl⟩ := hab
  exact J.mul_mem_right d ha

/-- Congruences chain. -/
private theorem memchain {J : Ideal R} {X Y Z : R} (h1 : X - Y ∈ J)
    (h2 : Y - Z ∈ J) : X - Z ∈ J := by
  have := J.add_mem h1 h2
  rwa [show X - Y + (Y - Z) = X - Z by ring] at this

/-- The paper's (7.11): telescoping the `σ`-twists of the tested
congruence (7.9). -/
private theorem tele_n
    (hσχ : ∀ a : ZMod q, σ (χ a) = χ a ^ n)
    (hσψ : ∀ a : ZMod q, σ (ψ a) = ψ a) (hσζ : σ ζ = ζ ^ n)
    (hσI : ∀ x ∈ I, σ x ∈ I) (hn0 : n ≠ 0)
    (hS0 : ∀ x ∈ S, x ≠ 0)
    (h79 : (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ n
      - ζ ^ e₀ * σ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ∈ I) :
    ∀ i, (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ n ^ i
      - ζ ^ (e₀ * i * n ^ (i - 1))
        * ∏ x ∈ S, gaussSum (χ ^ (x * n ^ i)) ψ ^ ν x ∈ I := by
  have hσuS : ∀ j, σ (∏ x ∈ S, gaussSum (χ ^ (x * n ^ j)) ψ ^ ν x)
      = ∏ x ∈ S, gaussSum (χ ^ (x * n ^ (j + 1))) ψ ^ ν x := by
    intro j
    rw [map_prod]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [map_pow, sigma_gaussSum hσχ hσψ hn0
      (mul_ne_zero (hS0 x hx) (pow_ne_zero _ hn0)),
      mul_assoc, ← pow_succ]
  have huS0 : (∏ x ∈ S, gaussSum (χ ^ (x * n ^ 0)) ψ ^ ν x)
      = ∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [pow_zero, mul_one]
  -- σ-iterates of (7.9)
  have hstepn : ∀ j,
      (∏ x ∈ S, gaussSum (χ ^ (x * n ^ j)) ψ ^ ν x) ^ n
        - ζ ^ (e₀ * n ^ j)
          * ∏ x ∈ S, gaussSum (χ ^ (x * n ^ (j + 1))) ψ ^ ν x ∈ I := by
    intro j
    induction j with
    | zero =>
      rw [huS0, ← hσuS 0, huS0, pow_zero, mul_one]
      exact h79
    | succ j ih =>
      have hσ := hσI _ ih
      rw [map_sub, map_pow, map_mul, map_pow, hσζ, hσuS, hσuS] at hσ
      rwa [← pow_mul, mul_comm n (e₀ * n ^ j), mul_assoc,
        ← pow_succ] at hσ
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := memdvd ih (sub_dvd_pow_sub_pow
      ((∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ n ^ i)
      (ζ ^ (e₀ * i * n ^ (i - 1))
        * ∏ x ∈ S, gaussSum (χ ^ (x * n ^ i)) ψ ^ ν x) n)
    rw [mul_pow, ← pow_mul (ζ) _ n, ← pow_mul, ← pow_succ] at h1
    -- h1 : u^(n^(i+1)) − ζ^(E_i·n)·P_i^n ∈ I
    have h2 : ζ ^ (e₀ * i * n ^ (i - 1) * n)
          * (∏ x ∈ S, gaussSum (χ ^ (x * n ^ i)) ψ ^ ν x) ^ n
        - ζ ^ (e₀ * i * n ^ (i - 1) * n)
          * (ζ ^ (e₀ * n ^ i)
            * ∏ x ∈ S, gaussSum (χ ^ (x * n ^ (i + 1))) ψ ^ ν x) ∈ I := by
      have hmm := I.mul_mem_left (ζ ^ (e₀ * i * n ^ (i - 1) * n))
        (hstepn i)
      rwa [mul_sub] at hmm
    have h3 := memchain h1 h2
    have hexp : e₀ * i * n ^ (i - 1) * n + e₀ * n ^ i
        = e₀ * (i + 1) * n ^ (i + 1 - 1) := by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [Nat.add_sub_cancel, Nat.add_sub_cancel, pow_succ]
        ring
    rwa [← mul_assoc, ← pow_add, hexp] at h3

/-- The paper's (7.13): telescoping the instances of Lemma (7.3) at
the prime `r`, modulo `(r)`. -/
private theorem tele_r
    {r : ℕ} (hr : r.Prime) (hqr : ¬ q ∣ r) (hS0 : ∀ x ∈ S, x ≠ 0) :
    ∀ i, (χ ((r : ℕ) : ZMod q)) ^ ((∑ x ∈ S, ν x * x) * i * r ^ i)
        * (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ r ^ i
      - ∏ x ∈ S, gaussSum (χ ^ (x * r ^ i)) ψ ^ ν x
      ∈ Ideal.span {(r : R)} := by
  set c := ∑ x ∈ S, ν x * x with hc
  set w := χ ((r : ℕ) : ZMod q) with hw
  have hAS0 : (∏ x ∈ S, gaussSum (χ ^ (x * r ^ 0)) ψ ^ ν x)
      = ∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [pow_zero, mul_one]
  -- the one-step congruence from Lemma (7.3)
  have hstep : ∀ j, w ^ (c * r ^ (j + 1))
        * (∏ x ∈ S, gaussSum (χ ^ (x * r ^ j)) ψ ^ ν x) ^ r
      - ∏ x ∈ S, gaussSum (χ ^ (x * r ^ (j + 1))) ψ ^ ν x
      ∈ Ideal.span {(r : R)} := by
    intro j
    refine Ideal.mem_span_singleton.mpr ?_
    have hper : ∀ x ∈ S, (r : R) ∣
        ((χ ^ (x * r ^ j)) ((r : ℕ) : ZMod q) ^ r
            * gaussSum (χ ^ (x * r ^ j)) ψ ^ r) ^ ν x
          - gaussSum (χ ^ (x * r ^ (j + 1))) ψ ^ ν x := by
      intro x hx
      have h73 := lemma_7_3 hr hqr (χ ^ (x * r ^ j)) ψ
      rw [show (χ ^ (x * r ^ j)) ^ r = χ ^ (x * r ^ (j + 1)) from by
        rw [← pow_mul, mul_assoc, ← pow_succ]] at h73
      exact h73.trans (sub_dvd_pow_sub_pow _ _ (ν x))
    have hprod := dvd_prod_sub_prod (c := (r : R)) hper
    have hL : ∏ x ∈ S,
        ((χ ^ (x * r ^ j)) ((r : ℕ) : ZMod q) ^ r
          * gaussSum (χ ^ (x * r ^ j)) ψ ^ r) ^ ν x
        = w ^ (c * r ^ (j + 1))
          * (∏ x ∈ S, gaussSum (χ ^ (x * r ^ j)) ψ ^ ν x) ^ r := by
      have hterm : ∀ x ∈ S,
          ((χ ^ (x * r ^ j)) ((r : ℕ) : ZMod q) ^ r
            * gaussSum (χ ^ (x * r ^ j)) ψ ^ r) ^ ν x
          = w ^ (ν x * x * r ^ (j + 1))
            * (gaussSum (χ ^ (x * r ^ j)) ψ ^ ν x) ^ r := by
        intro x hx
        rw [MulChar.pow_apply' χ
          (mul_ne_zero (hS0 x hx) (pow_ne_zero _ hr.pos.ne')) _, ← hw,
          mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 2
        · rw [pow_succ]; ring
        · ring
      rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow]
      congr 1
      rw [← Finset.sum_mul]
    rw [hL] at hprod
    exact hprod
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := memdvd ih (sub_dvd_pow_sub_pow
      (w ^ (c * i * r ^ i)
        * (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ r ^ i)
      (∏ x ∈ S, gaussSum (χ ^ (x * r ^ i)) ψ ^ ν x) r)
    rw [mul_pow, ← pow_mul (w) _ r, ← pow_mul, ← pow_succ] at h1
    -- h1 : w^(c·i·r^i·r)·u^(r^(i+1)) − P_i^r ∈ (r)
    have h1' : w ^ (c * r ^ (i + 1)) * (w ^ (c * i * r ^ i * r)
          * (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ r ^ (i + 1))
        - w ^ (c * r ^ (i + 1))
          * (∏ x ∈ S, gaussSum (χ ^ (x * r ^ i)) ψ ^ ν x) ^ r
        ∈ Ideal.span {(r : R)} := by
      have hmm := (Ideal.span {(r : R)}).mul_mem_left
        (w ^ (c * r ^ (i + 1))) h1
      rwa [mul_sub] at hmm
    have h3 := memchain h1' (hstep i)
    have hexp : c * r ^ (i + 1) + c * i * r ^ i * r
        = c * (i + 1) * r ^ (i + 1) := by
      rw [pow_succ]
      ring
    rwa [← mul_assoc, ← pow_add, hexp] at h3

/-- **Cohen–Lenstra Theorem (7.8)** (per prime divisor, finite
level): the verified congruence (7.9), together with the finite form
of (6.4) for a prime `r ∣ n`, forces `χ(r) = ζ^(f·m)` — the paper's
`χ(r) = η^(l_p(r))` with `η = ζ^f` determined by
`ζ^(e₀) = η^(−n·c(β))`. -/
theorem theorem_7_8 {R : Type _} [CommRing R] [IsDomain R]
    {q p k n : ℕ} [Fact q.Prime]
    (hp : p.Prime) (hk : 0 < k) (hn1 : 1 < n) (hpn : ¬ p ∣ n)
    (hqn : ¬ q ∣ n)
    {χ : MulChar (ZMod q) R} {ψ : AddChar (ZMod q) R}
    (hψ : ψ.IsPrimitive)
    {ζ : R} (hζ : IsPrimitiveRoot ζ (p ^ k))
    (hord : orderOf χ = p ^ k)
    (hχζ : ∀ a : (ZMod q)ˣ, ∃ j : ℕ, χ ↑a = ζ ^ j)
    {σ : R →+* R} (hσχ : ∀ a : ZMod q, σ (χ a) = χ a ^ n)
    (hσψ : ∀ a : ZMod q, σ (ψ a) = ψ a) (hσζ : σ ζ = ζ ^ n)
    {I : Ideal R} (hnI : (n : R) ∈ I) (hσI : ∀ x ∈ I, σ x ∈ I)
    (hIZ : ∀ a : ℕ, (a : R) ∈ I → n ∣ a)
    {S : Finset ℕ} {ν : ℕ → ℕ} (hSp : ∀ x ∈ S, ¬ p ∣ x)
    (hβ : ¬ p ∣ ∑ x ∈ S, ν x * x)
    {e₀ : ℕ}
    (h79 : (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ n
      - ζ ^ e₀ * σ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ∈ I)
    {r : ℕ} (hr : r.Prime) (hrn : r ∣ n) {m : ℕ}
    (hm : ((p : ℤ) ^ ((n ^ ((p - 1) * p ^ k) - 1).factorization p))
      ∣ (r : ℤ) ^ (p - 1) - (n : ℤ) ^ ((p - 1) * m))
    {f : ℕ} (hf : p ^ k ∣ e₀ + n * (∑ x ∈ S, ν x * x) * f) :
    χ ((r : ℕ) : ZMod q) = ζ ^ (f * m) := by
  classical
  have : NeZero q := ⟨(Fact.out (p := q.Prime)).pos.ne'⟩
  have hn0 : n ≠ 0 := by omega
  have hS0 : ∀ x ∈ S, x ≠ 0 := fun x hx h0 => hSp x hx (h0 ▸ dvd_zero p)
  have hrq : ¬ q ∣ r := fun hd => hqn (hd.trans hrn)
  have hrq' : r ≠ q := fun h => hrq (h ▸ dvd_refl r)
  have hpr : ¬ p ∣ r := by
    intro hd
    exact hpn (((Nat.prime_dvd_prime_iff_eq hp hr).mp hd) ▸ hrn)
  have hpc : p.Coprime n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
  -- the big numbers `N`, `v_p(N)`, and the `p`-free part `a`
  set N := n ^ ((p - 1) * p ^ k) - 1 with hN
  have hexp0 : (p - 1) * p ^ k ≠ 0 :=
    Nat.mul_ne_zero (by have := hp.one_lt; omega)
      (pow_ne_zero _ hp.pos.ne')
  have hNpos : 0 < N := by
    have h2 : 2 ≤ n ^ ((p - 1) * p ^ k) :=
      le_trans hn1 (Nat.le_self_pow hexp0 n)
    omega
  set vN := N.factorization p with hvN
  set a := N / p ^ vN with ha
  have hNa : p ^ vN * a = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hpa : ¬ p ∣ a := Nat.not_dvd_ordCompl hp hNpos.ne'
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hNa
    omega
  -- Fermat and the lower bound `v_p(N) ≥ k + 1`
  have hfermat : n ^ (p - 1) ≡ 1 [MOD p] := by
    have : Fact p.Prime := ⟨hp⟩
    have hz : ((n : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpn
    refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
    rw [Nat.cast_pow, Nat.cast_one, ZMod.pow_card_sub_one_eq_one hz]
  have hvNk : k + 1 ≤ vN := by
    have hh := pow_pow_modEq_one hfermat k
    have hpow : (n ^ (p - 1)) ^ p ^ k = n ^ ((p - 1) * p ^ k) := by
      rw [← pow_mul]
    have hone : 1 ≤ n ^ ((p - 1) * p ^ k) :=
      Nat.one_le_pow _ _ (by omega)
    have hdvd : p ^ (k + 1) ∣ N := by
      have hdd := (Nat.modEq_iff_dvd' hone).mp
        (by rw [← hpow]; exact hh.symm)
      rw [hN]
      exact hdd
    rw [hvN]
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hNpos.ne').mp hdvd
  -- (7.16): the congruence mod `p^k` and its character consequences
  have hkZ : ((p : ℤ)) ^ k ∣ (r : ℤ) ^ (p - 1) - (n : ℤ) ^ ((p - 1) * m) :=
    dvd_trans (pow_dvd_pow _ (by omega : k ≤ vN)) hm
  have hmodk : r ^ (p - 1) ≡ n ^ ((p - 1) * m) [MOD p ^ k] := by
    rw [Nat.modEq_iff_dvd]
    push_cast
    exact dvd_sub_comm.mp (by exact_mod_cast hkZ)
  have hEuler : n ^ ((p - 1) * p ^ k) ≡ 1 [MOD p ^ k] := by
    have hco : n.Coprime (p ^ k) := (hpc.symm).pow_right k
    have ht := Nat.ModEq.pow_totient hco
    have hφ : ((p ^ k).totient) * p = (p - 1) * p ^ k := by
      rw [Nat.totient_prime_pow hp hk]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]
      ring
    calc n ^ ((p - 1) * p ^ k) = (n ^ (p ^ k).totient) ^ p := by
          rw [← pow_mul, hφ]
      _ ≡ 1 ^ p [MOD p ^ k] := ht.pow p
      _ = 1 := one_pow p
  have hchpow : ∀ {A B : ℕ}, A ≡ B [MOD p ^ k] → χ ^ A = χ ^ B := by
    intro A B hAB
    exact pow_eq_pow_iff_modEq.mpr (hord ▸ hAB)
  have hcharN : ∀ x : ℕ, χ ^ (x * n ^ ((p - 1) * p ^ k)) = χ ^ x := by
    intro x
    refine hchpow ?_
    calc x * n ^ ((p - 1) * p ^ k) ≡ x * 1 [MOD p ^ k] :=
          hEuler.mul_left x
      _ = x := mul_one x
  have hcharR : ∀ x : ℕ,
      χ ^ (x * r ^ (p - 1)) = χ ^ (x * n ^ ((p - 1) * m)) :=
    fun x => hchpow (hmodk.mul_left x)
  -- the combination ideal `𝔯 = J` and its quotient
  set J := I ⊔ Ideal.span {(r : R)} with hJdef
  have hIJ : I ≤ J := le_sup_left
  have hrJ : (r : R) ∈ J :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self ((r : R) : R))
  set πJ := Ideal.Quotient.mk J with hπJ
  have hIeq : ∀ {A B : R}, A - B ∈ I → πJ A = πJ B := fun hAB =>
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hIJ hAB)
  have hReq : ∀ {A B : R}, A - B ∈ Ideal.span {(r : R)} → πJ A = πJ B :=
    fun hAB => (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_sup_right hAB)
  -- `q`, hence every Gauss sum of the family, is invertible mod `J`
  have hqrco : Nat.Coprime q r :=
    (Nat.coprime_primes (Fact.out (p := q.Prime)) hr).mpr
      fun h => hrq' h.symm
  have hqunit : IsUnit (πJ ((q : ℕ) : R)) := by
    have hb := Nat.gcd_eq_gcd_ab q r
    rw [Nat.Coprime.gcd_eq_one hqrco] at hb
    have hcast : (1 : R) = ((q : ℕ) : R) * ((Nat.gcdA q r : ℤ) : R)
        + ((r : ℕ) : R) * ((Nat.gcdB q r : ℤ) : R) := by
      have hbc := congrArg (fun z : ℤ => ((z : ℤ) : R)) hb
      push_cast at hbc
      simpa using hbc
    refine IsUnit.of_mul_eq_one (πJ ((Nat.gcdA q r : ℤ) : R)) ?_
    have hπc := congrArg πJ hcast
    rw [map_one, map_add, map_mul, map_mul,
      show πJ ((r : ℕ) : R) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr hrJ,
      zero_mul, add_zero] at hπc
    exact hπc.symm
  have hτunit : ∀ y : ℕ, ¬ p ∣ y →
      IsUnit (πJ (gaussSum (χ ^ y) ψ)) := by
    intro y hy
    have hχy : χ ^ y ≠ 1 := by
      intro h1
      have hd := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at hd
      exact hy (dvd_trans (dvd_pow_self p hk.ne') hd)
    have hprod := gaussSum_mul_gaussSum_eq_card hχy hψ
    have hcast : gaussSum (χ ^ y) ψ * gaussSum (χ ^ y)⁻¹ ψ⁻¹
        = ((q : ℕ) : R) := by
      rw [hprod, ZMod.card]
    refine isUnit_of_mul_isUnit_left
      (y := πJ (gaussSum (χ ^ y)⁻¹ ψ⁻¹)) ?_
    rw [← map_mul, hcast]
    exact hqunit
  have huunit : IsUnit (πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x)) := by
    rw [map_prod]
    refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul)
      isUnit_one ?_
    intro x hx
    rw [map_pow]
    exact (hτunit x (hSp x hx)).pow (ν x)
  -- the period (7.12)
  have hN1 : N + 1 = n ^ ((p - 1) * p ^ k) := by
    have h1 : 1 ≤ n ^ ((p - 1) * p ^ k) := Nat.one_le_pow _ _ (by omega)
    omega
  have hper1 : πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ (N + 1)
      = πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) := by
    have h0 := tele_n hσχ hσψ hσζ hσI hn0 hS0 h79 ((p - 1) * p ^ k)
    have hζE : ζ ^ (e₀ * ((p - 1) * p ^ k) * n ^ ((p - 1) * p ^ k - 1))
        = 1 := by
      refine (hζ.pow_eq_one_iff_dvd _).mpr ?_
      exact ⟨e₀ * (p - 1) * n ^ ((p - 1) * p ^ k - 1), by ring⟩
    have hprodEq :
        (∏ x ∈ S, gaussSum (χ ^ (x * n ^ ((p - 1) * p ^ k))) ψ ^ ν x)
        = ∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x :=
      Finset.prod_congr rfl fun x _ => by rw [hcharN x]
    rw [hζE, one_mul, hprodEq] at h0
    have hq0 := hIeq h0
    rw [map_pow] at hq0
    rwa [← hN1] at hq0
  have hper : ∀ w' s : ℕ, 1 ≤ s →
      πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ (N * w' + s)
        = πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ s := by
    intro w'
    induction w' with
    | zero => intro s _; rw [Nat.mul_zero, Nat.zero_add]
    | succ w' ih =>
      intro s hs
      have harith : N * (w' + 1) + s = N * w' + ((N + 1) + (s - 1)) := by
        rw [Nat.mul_succ]
        omega
      rw [harith, ih _ (by omega), pow_add, hper1, ← pow_succ']
      congr 1
      omega
  -- combine (7.11) at `i = (p−1)m` with (7.13) at `i = p−1` mod `J`
  have h_eqn := tele_n hσχ hσψ hσζ hσI hn0 hS0 h79 ((p - 1) * m)
  have h_eqr := tele_r (χ := χ) (ψ := ψ) (ν := ν) hr hrq hS0 (p - 1)
  have hAeq : (∏ x ∈ S, gaussSum (χ ^ (x * r ^ (p - 1))) ψ ^ ν x)
      = ∏ x ∈ S, gaussSum (χ ^ (x * n ^ ((p - 1) * m))) ψ ^ ν x :=
    Finset.prod_congr rfl fun x _ => by rw [hcharR x]
  rw [hAeq] at h_eqr
  have h_eqnJ := hIeq h_eqn
  have h_eqrJ := hReq h_eqr
  rw [map_pow, map_mul, map_pow] at h_eqnJ
  rw [map_mul, map_pow, map_pow] at h_eqrJ
  have hcomb : πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ n ^ ((p - 1) * m)
      = (πJ ζ ^ (e₀ * ((p - 1) * m) * n ^ ((p - 1) * m - 1))
          * πJ (χ ((r : ℕ) : ZMod q))
            ^ ((∑ x ∈ S, ν x * x) * (p - 1) * r ^ (p - 1)))
        * πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ r ^ (p - 1) := by
    rw [h_eqnJ, ← h_eqrJ]
    ring
  have hcombA : πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x)
        ^ (n ^ ((p - 1) * m) * a)
      = (πJ ζ ^ (e₀ * ((p - 1) * m) * n ^ ((p - 1) * m - 1))
          * πJ (χ ((r : ℕ) : ZMod q))
            ^ ((∑ x ∈ S, ν x * x) * (p - 1) * r ^ (p - 1))) ^ a
        * πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x)
            ^ (r ^ (p - 1) * a) := by
    calc πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x)
          ^ (n ^ ((p - 1) * m) * a)
        = (πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x)
            ^ n ^ ((p - 1) * m)) ^ a := by rw [pow_mul]
      _ = ((πJ ζ ^ (e₀ * ((p - 1) * m) * n ^ ((p - 1) * m - 1))
            * πJ (χ ((r : ℕ) : ZMod q))
              ^ ((∑ x ∈ S, ν x * x) * (p - 1) * r ^ (p - 1)))
          * πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x)
              ^ r ^ (p - 1)) ^ a := by rw [hcomb]
      _ = _ := by rw [mul_pow, ← pow_mul]
  -- hcombA : U^(n1·a) = ρ · U^(r1·a)
  -- `N` divides the exponent difference
  have hNd : (N : ℤ) ∣ ((r : ℤ) ^ (p - 1) - (n : ℤ) ^ ((p - 1) * m))
      * (a : ℤ) := by
    have hNz : (N : ℤ) = ((p : ℤ)) ^ vN * (a : ℤ) := by
      exact_mod_cast hNa.symm
    rw [hNz]
    exact mul_dvd_mul hm dvd_rfl
  -- cancel the unit `U` after using the period
  have hρ1 : (πJ ζ ^ (e₀ * ((p - 1) * m) * n ^ ((p - 1) * m - 1))
      * πJ (χ ((r : ℕ) : ZMod q))
        ^ ((∑ x ∈ S, ν x * x) * (p - 1) * r ^ (p - 1))) ^ a = 1 := by
    have hd1pos : 1 ≤ n ^ ((p - 1) * m) * a :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (pow_ne_zero _ hn0) ha0)
    have hd2pos : 1 ≤ r ^ (p - 1) * a :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (pow_ne_zero _ hr.pos.ne') ha0)
    rcases le_total (r ^ (p - 1) * a) (n ^ ((p - 1) * m) * a) with hle | hle
    · have hdiffdvd : N ∣ n ^ ((p - 1) * m) * a - r ^ (p - 1) * a := by
        rw [← Int.natCast_dvd_natCast]
        have hcast : ((n ^ ((p - 1) * m) * a - r ^ (p - 1) * a : ℕ) : ℤ)
            = -(((r : ℤ) ^ (p - 1) - (n : ℤ) ^ ((p - 1) * m))
                * (a : ℤ)) := by
          push_cast [hle]
          ring
        rw [hcast]
        exact dvd_neg.mpr hNd
      obtain ⟨w', hw'⟩ := hdiffdvd
      have harith : n ^ ((p - 1) * m) * a = N * w' + r ^ (p - 1) * a := by
        omega
      rw [harith, hper w' _ hd2pos] at hcombA
      have hU : IsUnit (πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x)
          ^ (r ^ (p - 1) * a)) := huunit.pow _
      exact (hU.mul_right_cancel (by rw [one_mul]; exact hcombA)).symm
    · have hdiffdvd : N ∣ r ^ (p - 1) * a - n ^ ((p - 1) * m) * a := by
        rw [← Int.natCast_dvd_natCast]
        have hcast : ((r ^ (p - 1) * a - n ^ ((p - 1) * m) * a : ℕ) : ℤ)
            = ((r : ℤ) ^ (p - 1) - (n : ℤ) ^ ((p - 1) * m)) * (a : ℤ) := by
          push_cast [hle]
          ring
        rw [hcast]
        exact hNd
      obtain ⟨w', hw'⟩ := hdiffdvd
      have harith : r ^ (p - 1) * a = N * w' + n ^ ((p - 1) * m) * a := by
        omega
      rw [harith, hper w' _ hd1pos] at hcombA
      have hU : IsUnit (πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x)
          ^ (n ^ ((p - 1) * m) * a)) := huunit.pow _
      exact (hU.mul_right_cancel (by rw [one_mul]; exact hcombA)).symm
  -- identify the root of unity and lift to `R` via (7.17)
  have hcoprq : r.Coprime q := (Nat.coprime_primes hr
    (Fact.out (p := q.Prime))).mpr hrq'
  obtain ⟨jr, hjr⟩ := hχζ (ZMod.unitOfCoprime r hcoprq)
  rw [ZMod.coe_unitOfCoprime] at hjr
  have hξ : πJ (ζ ^ (a * (e₀ * ((p - 1) * m) * n ^ ((p - 1) * m - 1)
      + jr * ((∑ x ∈ S, ν x * x) * (p - 1) * r ^ (p - 1))))) = 1 := by
    have hsplit : ζ ^ (a * (e₀ * ((p - 1) * m) * n ^ ((p - 1) * m - 1)
        + jr * ((∑ x ∈ S, ν x * x) * (p - 1) * r ^ (p - 1))))
        = (ζ ^ (e₀ * ((p - 1) * m) * n ^ ((p - 1) * m - 1))
          * (ζ ^ jr)
            ^ ((∑ x ∈ S, ν x * x) * (p - 1) * r ^ (p - 1))) ^ a := by
      rw [← pow_mul, ← pow_add, ← pow_mul]
      congr 1
      ring
    rw [hsplit, map_pow, map_mul, map_pow, map_pow, ← hjr]
    exact hρ1
  have hmem : ζ ^ (a * (e₀ * ((p - 1) * m) * n ^ ((p - 1) * m - 1)
      + jr * ((∑ x ∈ S, ν x * x) * (p - 1) * r ^ (p - 1)))) - 1 ∈ J := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := J), map_one]
    exact hξ
  have hrpk : ¬ r ∣ p ^ k := fun hd =>
    hpn (((Nat.prime_dvd_prime_iff_eq hr hp).mp
      (hr.dvd_of_dvd_pow hd)) ▸ hrn)
  have hζpow := lemma_7_17 hζ (pow_ne_zero k hp.pos.ne') hn0 hnI hIZ
    hrn hrpk (hJdef ▸ hmem)
  have hdvd_pk : p ^ k ∣ e₀ * ((p - 1) * m) * n ^ ((p - 1) * m - 1)
      + jr * ((∑ x ∈ S, ν x * x) * (p - 1) * r ^ (p - 1)) := by
    have hd := (hζ.pow_eq_one_iff_dvd _).mp hζpow
    have hcop : (p ^ k).Coprime a :=
      Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hpa)
    exact hcop.dvd_of_dvd_mul_left hd
  -- final exponent arithmetic, in ℤ
  rw [hjr]
  refine pow_eq_pow_of_modEq hζ.pow_eq_one ?_
  -- goal : jr ≡ f * m [MOD p ^ k]
  have hiZ : ((p : ℤ)) ^ k
      ∣ (e₀ : ℤ) * (((p - 1 : ℕ) : ℤ) * (m : ℤ)) * (n : ℤ) ^ ((p - 1) * m - 1)
        + (jr : ℤ) * (((∑ x ∈ S, ν x * x : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ)
            * (r : ℤ) ^ (p - 1)) := by
    exact_mod_cast hdvd_pk
  have hiiZ : ((p : ℤ)) ^ k
      ∣ (e₀ : ℤ) + (n : ℤ) * ((∑ x ∈ S, ν x * x : ℕ) : ℤ) * (f : ℤ) := by
    exact_mod_cast hf
  have hnnE : (n : ℤ) * ((e₀ : ℤ) * (((p - 1 : ℕ) : ℤ) * (m : ℤ))
        * (n : ℤ) ^ ((p - 1) * m - 1))
      = (e₀ : ℤ) * (((p - 1 : ℕ) : ℤ) * (m : ℤ)) * (n : ℤ) ^ ((p - 1) * m) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · simp
    · have hnn : (n : ℤ) * (n : ℤ) ^ ((p - 1) * m - 1)
          = (n : ℤ) ^ ((p - 1) * m) := by
        rw [← pow_succ']
        congr 1
        have h2p := hp.one_lt
        have hA1 : 1 ≤ (p - 1) * m :=
          Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by omega) hm1.ne')
        omega
      rw [← hnn]
      ring
  -- combine and cancel the coprime factor `n·c(β)·(p−1)`
  have hstepA : ((p : ℤ)) ^ k
      ∣ ((n : ℤ) * ((∑ x ∈ S, ν x * x : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ))
        * ((jr : ℤ) * (r : ℤ) ^ (p - 1)
          - (f : ℤ) * (m : ℤ) * (n : ℤ) ^ ((p - 1) * m)) := by
    have hA : ((p : ℤ)) ^ k
        ∣ (n : ℤ) * ((e₀ : ℤ) * (((p - 1 : ℕ) : ℤ) * (m : ℤ))
              * (n : ℤ) ^ ((p - 1) * m - 1)
            + (jr : ℤ) * (((∑ x ∈ S, ν x * x : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ)
                * (r : ℤ) ^ (p - 1))) :=
      Dvd.dvd.mul_left hiZ _
    have hB : ((p : ℤ)) ^ k
        ∣ ((e₀ : ℤ) + (n : ℤ) * ((∑ x ∈ S, ν x * x : ℕ) : ℤ) * (f : ℤ))
          * ((((p - 1 : ℕ) : ℤ) * (m : ℤ)) * (n : ℤ) ^ ((p - 1) * m)) :=
      Dvd.dvd.mul_right hiiZ _
    have hAB := dvd_sub hA hB
    have hring : (n : ℤ) * ((e₀ : ℤ) * (((p - 1 : ℕ) : ℤ) * (m : ℤ))
              * (n : ℤ) ^ ((p - 1) * m - 1)
            + (jr : ℤ) * (((∑ x ∈ S, ν x * x : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ)
                * (r : ℤ) ^ (p - 1)))
          - ((e₀ : ℤ) + (n : ℤ) * ((∑ x ∈ S, ν x * x : ℕ) : ℤ) * (f : ℤ))
            * ((((p - 1 : ℕ) : ℤ) * (m : ℤ)) * (n : ℤ) ^ ((p - 1) * m))
        = ((n : ℤ) * ((∑ x ∈ S, ν x * x : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ))
          * ((jr : ℤ) * (r : ℤ) ^ (p - 1)
            - (f : ℤ) * (m : ℤ) * (n : ℤ) ^ ((p - 1) * m)) := by
      linear_combination hnnE
    exact hring ▸ hAB
  have hcop3 : IsCoprime (((p : ℤ)) ^ k)
      ((n : ℤ) * ((∑ x ∈ S, ν x * x : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ)) := by
    have hp1 : ¬ p ∣ p - 1 := by
      intro hd
      have h1 := hp.one_lt
      have := Nat.le_of_dvd (by omega) hd
      omega
    have hnat : Nat.Coprime (p ^ k) (n * ((∑ x ∈ S, ν x * x) * (p - 1))) :=
      Nat.Coprime.pow_left k
        (Nat.Coprime.mul_right hpc
          (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hβ)
            (hp.coprime_iff_not_dvd.mpr hp1)))
    have hZ := Nat.isCoprime_iff_coprime.mpr hnat
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, ← mul_assoc] at hZ
    exact hZ
  have hstepB : ((p : ℤ)) ^ k ∣ (jr : ℤ) * (r : ℤ) ^ (p - 1)
      - (f : ℤ) * (m : ℤ) * (n : ℤ) ^ ((p - 1) * m) :=
    hcop3.dvd_of_dvd_mul_left hstepA
  -- use (7.16) and cancel `n^((p−1)m)`
  have hstepC : ((p : ℤ)) ^ k
      ∣ (n : ℤ) ^ ((p - 1) * m) * ((jr : ℤ) - (f : ℤ) * (m : ℤ)) := by
    have hring2 : (n : ℤ) ^ ((p - 1) * m) * ((jr : ℤ) - (f : ℤ) * (m : ℤ))
        = ((jr : ℤ) * (r : ℤ) ^ (p - 1)
            - (f : ℤ) * (m : ℤ) * (n : ℤ) ^ ((p - 1) * m))
          - (jr : ℤ) * ((r : ℤ) ^ (p - 1) - (n : ℤ) ^ ((p - 1) * m)) := by
      ring
    rw [hring2]
    exact dvd_sub hstepB (Dvd.dvd.mul_left hkZ _)
  have hcop4 : IsCoprime (((p : ℤ)) ^ k) ((n : ℤ) ^ ((p - 1) * m)) := by
    have hZ := Nat.isCoprime_iff_coprime.mpr
      (Nat.Coprime.pow k ((p - 1) * m) hpc)
    rw [Nat.cast_pow, Nat.cast_pow] at hZ
    exact hZ
  have hstepD := hcop4.dvd_of_dvd_mul_left hstepC
  -- conclude
  rw [Nat.modEq_iff_dvd]
  push_cast
  exact dvd_sub_comm.mp (by exact_mod_cast hstepD)


/-- **Cohen–Lenstra Theorem (7.19)**: if `p ≥ 3` and the tested
congruence (7.9) holds with a *primitive* `p^k`-th root of unity
(`ζ₀ = ζ^(e₀)` with `p ∤ e₀`), then `p` satisfies condition (6.4) —
at finite level: for every prime `r ∣ n` and every depth `D` there is
an exponent `l` with `r^(p−1) ≡ (n^(p−1))^l (mod p^D)`. -/
theorem theorem_7_19 {R : Type _} [CommRing R] [IsDomain R]
    {q p k n : ℕ} [Fact q.Prime]
    (hp : p.Prime) (hp3 : 2 < p) (hk : 0 < k) (hn1 : 1 < n)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n)
    {χ : MulChar (ZMod q) R} {ψ : AddChar (ZMod q) R}
    (hψ : ψ.IsPrimitive)
    {ζ : R} (hζ : IsPrimitiveRoot ζ (p ^ k))
    (hord : orderOf χ = p ^ k)
    {σ : R →+* R} (hσχ : ∀ a : ZMod q, σ (χ a) = χ a ^ n)
    (hσψ : ∀ a : ZMod q, σ (ψ a) = ψ a) (hσζ : σ ζ = ζ ^ n)
    {I : Ideal R} (hnI : (n : R) ∈ I) (hσI : ∀ x ∈ I, σ x ∈ I)
    (hIZ : ∀ a : ℕ, (a : R) ∈ I → n ∣ a)
    {S : Finset ℕ} {ν : ℕ → ℕ} (hSp : ∀ x ∈ S, ¬ p ∣ x)
    {e₀ : ℕ} (hpe₀ : ¬ p ∣ e₀)
    (h79 : (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ^ n
      - ζ ^ e₀ * σ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) ∈ I)
    {r : ℕ} (hr : r.Prime) (hrn : r ∣ n) :
    ∀ D, ∃ l, r ^ (p - 1) ≡ (n ^ (p - 1)) ^ l [MOD p ^ D] := by
  classical
  have : NeZero q := ⟨(Fact.out (p := q.Prime)).pos.ne'⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hn0 : n ≠ 0 := by omega
  have hS0 : ∀ x ∈ S, x ≠ 0 := fun x hx h0 => hSp x hx (h0 ▸ dvd_zero p)
  have hrq : ¬ q ∣ r := fun hd => hqn (hd.trans hrn)
  have hrq' : r ≠ q := fun h => hrq (h ▸ dvd_refl r)
  have hpr : ¬ p ∣ r := by
    intro hd
    exact hpn (((Nat.prime_dvd_prime_iff_eq hp hr).mp hd) ▸ hrn)
  have hpc : p.Coprime n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
  have hrpk : ¬ r ∣ p ^ (k' + 1) := fun hd =>
    hpn (((Nat.prime_dvd_prime_iff_eq hr hp).mp
      (hr.dvd_of_dvd_pow hd)) ▸ hrn)
  -- the exponent i₀ = φ(p^k) and the two Euler congruences
  have hEuler : ∀ {x : ℕ}, ¬ p ∣ x →
      x ^ ((p - 1) * p ^ k') ≡ 1 [MOD p ^ (k' + 1)] := by
    intro x hx
    have hco : x.Coprime (p ^ (k' + 1)) :=
      (((Nat.Prime.coprime_iff_not_dvd hp).mpr hx).symm).pow_right _
    have ht := Nat.ModEq.pow_totient hco
    rwa [Nat.totient_prime_pow hp (by omega), Nat.add_sub_cancel,
      mul_comm (p ^ k') (p - 1)] at ht
  have hchpow : ∀ {A B : ℕ}, A ≡ B [MOD p ^ (k' + 1)] → χ ^ A = χ ^ B := by
    intro A B hAB
    exact pow_eq_pow_iff_modEq.mpr (hord ▸ hAB)
  have hcharN : ∀ x : ℕ,
      χ ^ (x * n ^ ((p - 1) * p ^ k')) = χ ^ x := fun x =>
    hchpow (by calc x * n ^ ((p - 1) * p ^ k') ≡ x * 1 [MOD p ^ (k' + 1)] :=
        (hEuler hpn).mul_left x
      _ = x := mul_one x)
  have hcharR : ∀ x : ℕ,
      χ ^ (x * r ^ ((p - 1) * p ^ k')) = χ ^ x := fun x =>
    hchpow (by calc x * r ^ ((p - 1) * p ^ k') ≡ x * 1 [MOD p ^ (k' + 1)] :=
        (hEuler hpr).mul_left x
      _ = x := mul_one x)
  -- the ideal J = I + (r), its quotient, and unit-ness of the players
  set J := I ⊔ Ideal.span {(r : R)} with hJdef
  have hIJ : I ≤ J := le_sup_left
  have hrJ : (r : R) ∈ J :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self ((r : R) : R))
  set πJ := Ideal.Quotient.mk J with hπJ
  have hIeq : ∀ {A B : R}, A - B ∈ I → πJ A = πJ B := fun hAB =>
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hIJ hAB)
  have hReq : ∀ {A B : R}, A - B ∈ Ideal.span {(r : R)} → πJ A = πJ B :=
    fun hAB => (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_sup_right hAB)
  have hqrco : Nat.Coprime q r :=
    (Nat.coprime_primes (Fact.out (p := q.Prime)) hr).mpr
      fun h => hrq' h.symm
  have hqunit : IsUnit (πJ ((q : ℕ) : R)) := by
    have hb := Nat.gcd_eq_gcd_ab q r
    rw [Nat.Coprime.gcd_eq_one hqrco] at hb
    have hcast : (1 : R) = ((q : ℕ) : R) * ((Nat.gcdA q r : ℤ) : R)
        + ((r : ℕ) : R) * ((Nat.gcdB q r : ℤ) : R) := by
      have hbc := congrArg (fun z : ℤ => ((z : ℤ) : R)) hb
      push_cast at hbc
      simpa using hbc
    refine IsUnit.of_mul_eq_one (πJ ((Nat.gcdA q r : ℤ) : R)) ?_
    have hπc := congrArg πJ hcast
    rw [map_one, map_add, map_mul, map_mul,
      show πJ ((r : ℕ) : R) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr hrJ,
      zero_mul, add_zero] at hπc
    exact hπc.symm
  have hτunit : ∀ y : ℕ, ¬ p ∣ y →
      IsUnit (πJ (gaussSum (χ ^ y) ψ)) := by
    intro y hy
    have hχy : χ ^ y ≠ 1 := by
      intro h1
      have hd := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at hd
      exact hy (dvd_trans (dvd_pow_self p (by omega : k' + 1 ≠ 0)) hd)
    have hprod := gaussSum_mul_gaussSum_eq_card hχy hψ
    have hcast : gaussSum (χ ^ y) ψ * gaussSum (χ ^ y)⁻¹ ψ⁻¹
        = ((q : ℕ) : R) := by
      rw [hprod, ZMod.card]
    refine isUnit_of_mul_isUnit_left
      (y := πJ (gaussSum (χ ^ y)⁻¹ ψ⁻¹)) ?_
    rw [← map_mul, hcast]
    exact hqunit
  have huunit : IsUnit (πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x)) := by
    rw [map_prod]
    refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul)
      isUnit_one ?_
    intro x hx
    rw [map_pow]
    exact (hτunit x (hSp x hx)).pow (ν x)
  -- ζ and χ(r) are roots of unity, hence units mod J
  have hpk1 : p ^ (k' + 1) - 1 + 1 = p ^ (k' + 1) := by
    have := Nat.one_le_pow (k' + 1) p hp.pos
    omega
  have hζpkJ : πJ ζ ^ p ^ (k' + 1) = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  have hζunit : IsUnit (πJ ζ) :=
    IsUnit.of_mul_eq_one (πJ ζ ^ (p ^ (k' + 1) - 1))
      (by rw [← pow_succ', hpk1, hζpkJ])
  have hcoprq : r.Coprime q := (Nat.coprime_primes hr
    (Fact.out (p := q.Prime))).mpr hrq'
  have hwpk : (χ ((r : ℕ) : ZMod q)) ^ p ^ (k' + 1) = 1 := by
    rw [show ((r : ℕ) : ZMod q)
          = ((ZMod.unitOfCoprime r hcoprq : (ZMod q)ˣ) : ZMod q)
        from (ZMod.coe_unitOfCoprime r hcoprq).symm,
      ← MulChar.pow_apply_coe, ← hord, pow_orderOf_eq_one,
      MulChar.one_apply_coe]
  have hwpkJ : πJ (χ ((r : ℕ) : ZMod q)) ^ p ^ (k' + 1) = 1 := by
    rw [← map_pow, hwpk, map_one]
  have hwunit : IsUnit (πJ (χ ((r : ℕ) : ZMod q))) :=
    IsUnit.of_mul_eq_one (πJ (χ ((r : ℕ) : ZMod q)) ^ (p ^ (k' + 1) - 1))
      (by rw [← pow_succ', hpk1, hwpkJ])
  -- pass to the unit group of the quotient
  obtain ⟨U, hU⟩ := huunit
  obtain ⟨Z, hZ⟩ := hζunit
  obtain ⟨W, hW⟩ := hwunit
  -- (7.20): the n-side congruence at i₀, in unit form
  have h_eqn := tele_n hσχ hσψ hσζ hσI hn0 hS0 h79 ((p - 1) * p ^ k')
  have hprodN : (∏ x ∈ S,
        gaussSum (χ ^ (x * n ^ ((p - 1) * p ^ k'))) ψ ^ ν x)
      = ∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x :=
    Finset.prod_congr rfl fun x _ => by rw [hcharN x]
  rw [hprodN] at h_eqn
  have hUeq : U ^ (n ^ ((p - 1) * p ^ k')) = Z ^ (e₀ * ((p - 1) * p ^ k')
      * n ^ ((p - 1) * p ^ k' - 1)) * U := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, hU, hZ]
    calc (πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x))
          ^ n ^ ((p - 1) * p ^ k')
        = πJ ((∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x)
            ^ n ^ ((p - 1) * p ^ k')) := by rw [map_pow]
      _ = πJ (ζ ^ (e₀ * ((p - 1) * p ^ k') * n ^ ((p - 1) * p ^ k' - 1))
            * ∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) := hIeq h_eqn
      _ = πJ ζ ^ (e₀ * ((p - 1) * p ^ k') * n ^ ((p - 1) * p ^ k' - 1))
            * πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) := by
          rw [map_mul, map_pow]
  -- (7.21): the r-side congruence at i₀, in unit form
  have h_eqr := tele_r (χ := χ) (ψ := ψ) (ν := ν) hr hrq hS0
    ((p - 1) * p ^ k')
  have hprodR : (∏ x ∈ S,
        gaussSum (χ ^ (x * r ^ ((p - 1) * p ^ k'))) ψ ^ ν x)
      = ∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x :=
    Finset.prod_congr rfl fun x _ => by rw [hcharR x]
  rw [hprodR] at h_eqr
  have hWeq : W ^ ((∑ x ∈ S, ν x * x) * ((p - 1) * p ^ k')
        * r ^ ((p - 1) * p ^ k'))
      * U ^ (r ^ ((p - 1) * p ^ k')) = U := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, hU, hW]
    calc (πJ (χ ((r : ℕ) : ZMod q)))
          ^ ((∑ x ∈ S, ν x * x) * ((p - 1) * p ^ k')
            * r ^ ((p - 1) * p ^ k'))
        * (πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x))
            ^ r ^ ((p - 1) * p ^ k')
        = πJ ((χ ((r : ℕ) : ZMod q))
              ^ ((∑ x ∈ S, ν x * x) * ((p - 1) * p ^ k')
                * r ^ ((p - 1) * p ^ k'))
            * (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x)
              ^ r ^ ((p - 1) * p ^ k')) := by
          rw [map_mul, map_pow, map_pow]
      _ = πJ (∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x) := hReq h_eqr
  -- the order ω of U and its p-part
  set M := n ^ ((p - 1) * p ^ k') - 1 with hMdef
  set Mr := r ^ ((p - 1) * p ^ k') - 1 with hMrdef
  have hM1 : M + 1 = n ^ ((p - 1) * p ^ k') := by
    have := Nat.one_le_pow ((p - 1) * p ^ k') n (by omega)
    omega
  have hMr1 : Mr + 1 = r ^ ((p - 1) * p ^ k') := by
    have := Nat.one_le_pow ((p - 1) * p ^ k') r hr.pos
    omega
  have hexp0 : (p - 1) * p ^ k' ≠ 0 := by
    have := hp.one_lt
    exact Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hM0 : M ≠ 0 := by
    have h2 : 2 ≤ n ^ ((p - 1) * p ^ k') :=
      le_trans hn1 (Nat.le_self_pow hexp0 n)
    omega
  have hMr0 : Mr ≠ 0 := by
    have h2 : 2 ≤ r ^ ((p - 1) * p ^ k') :=
      le_trans hr.two_le (Nat.le_self_pow hexp0 r)
    omega
  -- U^M = Z^E
  have hUM : U ^ M = Z ^ (e₀ * ((p - 1) * p ^ k')
      * n ^ ((p - 1) * p ^ k' - 1)) := by
    have h1 : U ^ M * U = Z ^ (e₀ * ((p - 1) * p ^ k')
        * n ^ ((p - 1) * p ^ k' - 1)) * U := by
      rw [← pow_succ, hM1]
      exact hUeq
    exact mul_right_cancel h1
  -- Z^E has order exactly p; U has finite order
  have hZEp : (Z ^ (e₀ * ((p - 1) * p ^ k')
      * n ^ ((p - 1) * p ^ k' - 1))) ^ p = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hZ,
      Units.val_one, ← pow_mul, ← map_pow]
    rw [show e₀ * ((p - 1) * p ^ k') * n ^ ((p - 1) * p ^ k' - 1) * p
          = p ^ (k' + 1) * (e₀ * (p - 1) * n ^ ((p - 1) * p ^ k' - 1))
        from by rw [pow_succ]; ring]
    rw [pow_mul, hζ.pow_eq_one, one_pow, map_one]
  have hMp1 : U ^ (M * p) = 1 := by
    rw [pow_mul, hUM]
    exact hZEp
  have hfin : IsOfFinOrder U :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨M * p, Nat.pos_of_ne_zero (Nat.mul_ne_zero hM0 hp.pos.ne'), hMp1⟩
  have hω0 : orderOf U ≠ 0 := hfin.orderOf_pos.ne'
  -- ω ∤ M: else Z^E = 1, contradicting primitivity via (7.17)
  have hωM : ¬ orderOf U ∣ M := by
    intro hd
    have hUM1 : U ^ M = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
    have hZE1 : πJ (ζ ^ (e₀ * ((p - 1) * p ^ k')
        * n ^ ((p - 1) * p ^ k' - 1))) = 1 := by
      have hv := congrArg Units.val (hUM ▸ hUM1 :
        Z ^ (e₀ * ((p - 1) * p ^ k')
          * n ^ ((p - 1) * p ^ k' - 1)) = 1)
      rw [Units.val_pow_eq_pow_val, hZ, Units.val_one, ← map_pow] at hv
      exact hv
    have hmem : ζ ^ (e₀ * ((p - 1) * p ^ k')
        * n ^ ((p - 1) * p ^ k' - 1)) - 1 ∈ J := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := J), map_one]
      exact hZE1
    have hone := lemma_7_17 hζ (pow_ne_zero _ hp.pos.ne') hn0 hnI hIZ
      hrn hrpk (hJdef ▸ hmem)
    have hdvd := (hζ.pow_eq_one_iff_dvd _).mp hone
    rw [show e₀ * ((p - 1) * p ^ k') * n ^ ((p - 1) * p ^ k' - 1)
          = p ^ k' * (e₀ * (p - 1) * n ^ ((p - 1) * p ^ k' - 1))
        from by ring, pow_succ] at hdvd
    have hp1 : p ∣ e₀ * (p - 1) * n ^ ((p - 1) * p ^ k' - 1) :=
      (mul_dvd_mul_iff_left (a := (p : ℕ) ^ k')
        (pow_ne_zero k' hp.pos.ne')).mp hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hp1 with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · exact hpe₀ h'
      · have := Nat.le_of_dvd (by omega) h'
        have := hp.one_lt
        omega
    · exact hpn (hp.dvd_of_dvd_pow h)
  have hvpω : (orderOf U).factorization p = M.factorization p + 1 :=
    factorization_eq_succ_of_dvd_mul_prime hp hM0 hω0
      (orderOf_dvd_of_pow_eq_one hMp1) hωM
  -- the r-side: ω ∣ Mr·p
  have hWU1 : W ^ ((∑ x ∈ S, ν x * x) * ((p - 1) * p ^ k')
      * r ^ ((p - 1) * p ^ k')) * U ^ Mr = 1 := by
    have h1 : (W ^ ((∑ x ∈ S, ν x * x) * ((p - 1) * p ^ k')
        * r ^ ((p - 1) * p ^ k')) * U ^ Mr) * U = 1 * U := by
      rw [one_mul, mul_assoc, ← pow_succ, hMr1]
      exact hWeq
    exact mul_right_cancel h1
  have hWccp : (W ^ ((∑ x ∈ S, ν x * x) * ((p - 1) * p ^ k')
      * r ^ ((p - 1) * p ^ k'))) ^ p = 1 := by
    rw [← pow_mul]
    rw [show (∑ x ∈ S, ν x * x) * ((p - 1) * p ^ k')
          * r ^ ((p - 1) * p ^ k') * p
        = p ^ (k' + 1) * ((∑ x ∈ S, ν x * x) * (p - 1)
            * r ^ ((p - 1) * p ^ k'))
        from by rw [pow_succ]; ring]
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hW, Units.val_one, pow_mul, hwpkJ,
      one_pow]
  have hMrp1 : U ^ (Mr * p) = 1 := by
    have h1 := congrArg (· ^ p) hWU1
    simp only [mul_pow, one_pow] at h1
    rw [hWccp, one_mul, ← pow_mul] at h1
    exact h1
  have hvpω_le : (orderOf U).factorization p ≤ Mr.factorization p + 1 := by
    have hle := (Nat.factorization_le_iff_dvd hω0
      (Nat.mul_ne_zero hMr0 hp.pos.ne')).mpr
      (orderOf_dvd_of_pow_eq_one hMrp1)
    have h3 := Finsupp.le_def.mp hle p
    rw [Nat.factorization_mul hMr0 hp.pos.ne'] at h3
    simp only [Finsupp.coe_add, Pi.add_apply,
      Nat.Prime.factorization_self hp] at h3
    omega
  -- (7.22): v_p(n^(i₀) − 1) ≤ v_p(r^(i₀) − 1)
  have h722 : M.factorization p ≤ Mr.factorization p := by omega
  -- identify the valuations via LTE and conclude with the engine
  have hnp1 : 1 ≤ n ^ (p - 1) := Nat.one_le_pow _ _ (by omega)
  have hrp1 : 1 ≤ r ^ (p - 1) := Nat.one_le_pow _ _ hr.pos
  have hexp1 : 1 ≤ n ^ ((p - 1) * p ^ k') := Nat.one_le_pow _ _ (by omega)
  have hexp1r : 1 ≤ r ^ ((p - 1) * p ^ k') := Nat.one_le_pow _ _ hr.pos
  have hp10 : p - 1 ≠ 0 := by
    have := hp.one_lt
    omega
  have hnc0 : n ^ (p - 1) - 1 ≠ 0 := by
    have h3 : 2 ≤ n ^ (p - 1) := le_trans hn1 (Nat.le_self_pow hp10 n)
    omega
  have hrc0 : r ^ (p - 1) - 1 ≠ 0 := by
    have h3 : 2 ≤ r ^ (p - 1) := le_trans hr.two_le
      (Nat.le_self_pow hp10 r)
    omega
  set c₀ := (n ^ (p - 1) - 1).factorization p with hc₀
  set cr := (r ^ (p - 1) - 1).factorization p with hcr
  -- Fermat: c₀, cr ≥ 1
  have hfermatn : p ∣ n ^ (p - 1) - 1 := by
    have : Fact p.Prime := ⟨hp⟩
    have hz : ((n : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpn
    have h1 : ((n : ℕ) : ZMod p) ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hz
    have h2 : (n ^ (p - 1) : ℕ) ≡ 1 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [h1]
    exact (Nat.modEq_iff_dvd' hnp1).mp h2.symm
  have hfermatr : p ∣ r ^ (p - 1) - 1 := by
    have : Fact p.Prime := ⟨hp⟩
    have hz : ((r : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpr
    have h1 : ((r : ℕ) : ZMod p) ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hz
    have h2 : (r ^ (p - 1) : ℕ) ≡ 1 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [h1]
    exact (Nat.modEq_iff_dvd' hrp1).mp h2.symm
  have hc₀1 : 1 ≤ c₀ := by
    rw [hc₀]
    exact (Nat.Prime.factorization_pos_of_dvd hp hnc0 hfermatn)
  have hcr1 : 1 ≤ cr := by
    rw [hcr]
    exact (Nat.Prime.factorization_pos_of_dvd hp hrc0 hfermatr)
  -- exact ℤ-valuations of `n^(p−1) − 1` and `r^(p−1) − 1`
  have hnZ1 : (p : ℤ) ^ c₀ ∣ ((n : ℤ)) ^ (p - 1) - 1 := by
    have := Nat.ordProj_dvd (n ^ (p - 1) - 1) p
    rw [← hc₀] at this
    have h' : ((p ^ c₀ : ℕ) : ℤ) ∣ ((n ^ (p - 1) - 1 : ℕ) : ℤ) := by
      exact_mod_cast this
    push_cast [hnp1] at h'
    exact_mod_cast h'
  have hnZ2 : ¬ (p : ℤ) ^ (c₀ + 1) ∣ ((n : ℤ)) ^ (p - 1) - 1 := by
    intro hd
    have h' : (p : ℕ) ^ (c₀ + 1) ∣ n ^ (p - 1) - 1 := by
      have hd' : ((p ^ (c₀ + 1) : ℕ) : ℤ) ∣ ((n ^ (p - 1) - 1 : ℕ) : ℤ) := by
        push_cast [hnp1]
        exact_mod_cast hd
      exact_mod_cast hd'
    exact (Nat.pow_succ_factorization_not_dvd hnc0 hp) (hc₀ ▸ h')
  have hrZ1 : (p : ℤ) ^ cr ∣ ((r : ℤ)) ^ (p - 1) - 1 := by
    have := Nat.ordProj_dvd (r ^ (p - 1) - 1) p
    rw [← hcr] at this
    have h' : ((p ^ cr : ℕ) : ℤ) ∣ ((r ^ (p - 1) - 1 : ℕ) : ℤ) := by
      exact_mod_cast this
    push_cast [hrp1] at h'
    exact_mod_cast h'
  -- LTE: v_p(M) = c₀ + k', v_p(Mr) = cr + k'
  have hMfact : M.factorization p = c₀ + k' := by
    obtain ⟨hL1, hL2⟩ := dvd_pow_p_pow_sub_one hp hp3 hc₀1 hnZ1 hnZ2 k'
    refine factorization_eq_of_int_dvd hp hM0 ?_ ?_
    · have hcast : ((M : ℕ) : ℤ) = ((n : ℤ) ^ (p - 1)) ^ p ^ k' - 1 := by
        rw [hMdef]
        push_cast [hexp1]
        rw [← pow_mul]
      rw [hcast]
      exact hL1
    · have hcast : ((M : ℕ) : ℤ) = ((n : ℤ) ^ (p - 1)) ^ p ^ k' - 1 := by
        rw [hMdef]
        push_cast [hexp1]
        rw [← pow_mul]
      rw [hcast]
      rwa [show c₀ + k' + 1 = c₀ + k' + 1 from rfl] at hL2
  -- if v_p(r^(p−1)−1) < c₀, LTE on the r-side contradicts (7.22)
  have hcrge : c₀ ≤ cr := by
    by_contra hlt
    push Not at hlt
    obtain ⟨hR1, hR2⟩ := dvd_pow_p_pow_sub_one hp hp3 hcr1 hrZ1
      (by
        intro hd
        have h' : (p : ℕ) ^ (cr + 1) ∣ r ^ (p - 1) - 1 := by
          have hd' : ((p ^ (cr + 1) : ℕ) : ℤ)
              ∣ ((r ^ (p - 1) - 1 : ℕ) : ℤ) := by
            push_cast [hrp1]
            exact_mod_cast hd
          exact_mod_cast hd'
        exact (Nat.pow_succ_factorization_not_dvd hrc0 hp)
          (hcr ▸ h')) k'
    have hMrfact : Mr.factorization p = cr + k' := by
      refine factorization_eq_of_int_dvd hp hMr0 ?_ ?_
      · have hcast : ((Mr : ℕ) : ℤ) = ((r : ℤ) ^ (p - 1)) ^ p ^ k' - 1 := by
          rw [hMrdef]
          push_cast [hexp1r]
          rw [← pow_mul]
        rw [hcast]
        exact hR1
      · have hcast : ((Mr : ℕ) : ℤ) = ((r : ℤ) ^ (p - 1)) ^ p ^ k' - 1 := by
          rw [hMrdef]
          push_cast [hexp1r]
          rw [← pow_mul]
        rw [hcast]
        exact hR2
    omega
  -- the engine concludes
  have hpnp : ¬ p ∣ n ^ (p - 1) := fun hd => hpn (hp.dvd_of_dvd_pow hd)
  have hbZ : (p : ℤ) ^ c₀ ∣ ((r : ℤ)) ^ (p - 1) - 1 :=
    dvd_trans (pow_dvd_pow _ hcrge) hrZ1
  intro D
  obtain ⟨l, hl⟩ := exists_pow_modEq_of_exact hp hp3 hc₀1 hpnp
    (by push_cast; exact hnZ1) (by push_cast; exact hnZ2)
    hbZ D
  exact ⟨l, hl⟩

end Theorem78

end CL

end Azurite
