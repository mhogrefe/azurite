/-
  Crandall–Pomerance, Theorem 4.3.3 (Lenstra): the finite-field
  divisor-confinement theorem — the engine of the finite field
  primality test.

  Suppose `n > 1`, `I, F > 0`, `F ∣ n^I − 1`, and `f, g ∈ Z_n[x]` with
  (1) `f ∣ g^(n^I−1) − 1`,
  (2) `g^((n^I−1)/q) − 1` coprime to `f` for every prime `q ∣ F`,
  (3) each of the `I` elementary symmetric polynomials in
      `g, g^n, …, g^(n^(I−1))` congruent mod `f` to a constant.
  Then every prime factor `p` of `n` satisfies `p ≡ n^j (mod F)` for
  some `j < I`.  (So if additionally `n` has no proper divisor in the
  residue classes `n^j (mod F)`, `j < I`, then `n` is prime — the
  test built on this in the sequel.)

  STATEMENT GAP (implicit in the book): `f` must be monic of positive
  degree — the proof picks an irreducible factor `f₁` of `f mod p`,
  which requires `f mod p` to have positive degree for EVERY prime
  `p ∣ n`.  Without it the theorem is false: `f = 1`, `g = 1`
  satisfies (1)–(3) vacuously for any `F ∣ n − 1` at `I = 1`, yet a
  composite `n` has prime factors in no prescribed class.  Monic of
  positive degree is what Algorithm 4.3.2 supplies.

  Proof, as in the book: work in `K := Z_p[x]/(f₁)`, a field.  Let
  `ḡ` be the image of `g`.  Hypotheses (1), (2) force the order of
  `ḡ` in `K*` to be a multiple of `F` (the same valuation climb as
  Pocklington's theorem, here extracted as the reusable monoid lemma
  `dvd_orderOf_of_pow_eq_one`).  Hypothesis (3) makes
  `h(T) = ∏_(j<I) (T − ḡ^(n^j))` a polynomial with Frobenius-fixed
  coefficients (Vieta: the coefficients are `±` the elementary
  symmetric functions of the roots, which land in the prime field);
  since `h(ḡ) = 0`, applying Frobenius gives `h(ḡ^p) = 0`, and the
  factored form pins `ḡ^p = ḡ^(n^j)` for some `j < I`.  As `ord ḡ`
  is a multiple of `F`, exponents are determined mod `F`, whence
  `p ≡ n^j (mod F)`.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Factorization.Basic

namespace Azurite

namespace CP

open Polynomial

/-- **The Pocklington order climb, monoid form**: if `a^N = 1` but
`a^(N/q) ≠ 1` for every prime `q` dividing `F ∣ N`, then the order of
`a` is a multiple of `F`. -/
theorem dvd_orderOf_of_pow_eq_one {M : Type _} [Monoid M] {a : M} {N F : ℕ}
    (hN : 0 < N) (hF : 0 < F) (hFN : F ∣ N) (haN : a ^ N = 1)
    (hq : ∀ q : ℕ, q.Prime → q ∣ F → a ^ (N / q) ≠ 1) :
    F ∣ orderOf a := by
  have hfin : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr ⟨N, hN, haN⟩
  have hord0 : orderOf a ≠ 0 := hfin.orderOf_pos.ne'
  rw [← Nat.factorization_le_iff_dvd hF.ne' hord0, Finsupp.le_def]
  intro q
  by_cases hqp : q.Prime
  case neg => simp [Nat.factorization_eq_zero_of_not_prime _ hqp]
  by_cases hqF : q ∣ F
  case neg => simp [Nat.factorization_eq_zero_of_not_dvd hqF]
  have hqN : q ∣ N := hqF.trans hFN
  have he1 : 1 ≤ N.factorization q :=
    hqp.factorization_pos_of_dvd hN.ne' hqN
  obtain ⟨m, hm⟩ : q ^ N.factorization q ∣ N := Nat.ordProj_dvd N q
  -- `a^m` has order exactly `q^(v_q N)`
  have hc1 : (a ^ m) ^ q ^ N.factorization q = 1 := by
    rw [← pow_mul, mul_comm m, ← hm, haN]
  have hcord : orderOf (a ^ m) = q ^ N.factorization q := by
    obtain ⟨j, hj, hje⟩ :=
      (Nat.dvd_prime_pow hqp).mp (orderOf_dvd_of_pow_eq_one hc1)
    rcases Nat.lt_or_ge j (N.factorization q) with hlt | hge
    · exfalso
      apply hq q hqp hqF
      have key : ∀ e m' : ℕ, 1 ≤ e → N = q ^ e * m' →
          N / q = q ^ (e - 1) * m' := by
        intro e m' he hEq
        rw [hEq, show q ^ e = q * q ^ (e - 1) by
            conv_lhs => rw [show e = 1 + (e - 1) by omega]
            rw [pow_add, pow_one],
          mul_assoc, Nat.mul_div_cancel_left _ hqp.pos]
      have hNq : N / q = q ^ (N.factorization q - 1) * m := key _ m he1 hm
      rw [hNq, mul_comm, pow_mul]
      refine orderOf_dvd_iff_pow_eq_one.mp ?_
      rw [hje]
      exact pow_dvd_pow q (by omega)
    · rw [hje]
      congr 1
      omega
  calc F.factorization q
      ≤ N.factorization q :=
        Finsupp.le_def.mp
          ((Nat.factorization_le_iff_dvd hF.ne' hN.ne').mpr hFN) q
    _ ≤ (orderOf a).factorization q := by
        refine (Nat.Prime.pow_dvd_iff_le_factorization hqp hord0).mp ?_
        rw [← hcord]
        exact orderOf_pow_dvd m

/-- Elementary symmetric functions commute with ring homomorphisms. -/
theorem esymm_map {R S : Type _} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (s : Multiset R) (k : ℕ) :
    (s.map φ).esymm k = φ (s.esymm k) := by
  unfold Multiset.esymm
  rw [map_multiset_sum, Multiset.powersetCard_map, Multiset.map_map,
    Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun t _ => ?_
  exact (map_multiset_prod φ t).symm

/-- **Theorem 4.3.3 (Lenstra)**: with `F ∣ n^I − 1` and `f, g ∈ Z_n[x]`
(`f` monic of positive degree) such that (1) `f ∣ g^(n^I−1) − 1`,
(2) `g^((n^I−1)/q) − 1` is coprime to `f` for every prime `q ∣ F`, and
(3) each of the `I` elementary symmetric polynomials in
`g, g^n, …, g^(n^(I−1))` is congruent mod `f` to a constant, every
prime factor `p` of `n` satisfies `p ≡ n^j (mod F)` for some
`j < I`. -/
theorem theorem_4_3_3 {n I F : ℕ} (hn : 1 < n) (hI : 0 < I) (hF : 0 < F)
    (hFN : F ∣ n ^ I - 1) {f g : Polynomial (ZMod n)}
    (hf : f.Monic) (hfdeg : 0 < f.natDegree)
    (h1 : f ∣ g ^ (n ^ I - 1) - 1)
    (h2 : ∀ q : ℕ, q.Prime → q ∣ F →
      IsCoprime (g ^ ((n ^ I - 1) / q) - 1) f)
    (h3 : ∀ k : ℕ, 1 ≤ k → k ≤ I → ∃ c : ZMod n,
      f ∣ ((Multiset.range I).map fun j => g ^ n ^ j).esymm k - C c)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    ∃ j < I, p ≡ n ^ j [MOD F] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN0 : 0 < n ^ I - 1 := by
    have h2n : 2 ≤ n ^ I := le_trans hn (Nat.le_self_pow hI.ne' n)
    omega
  -- reduce mod `p` and pick an irreducible factor of `f mod p`
  set φ : ZMod n →+* ZMod p := ZMod.castHom hpn (ZMod p) with hφ
  have hfp : (f.map φ).Monic := hf.map φ
  have hfpnu : ¬IsUnit (f.map φ) := by
    intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    rw [hf.natDegree_map] at h0
    omega
  obtain ⟨f₁, hf₁irr, hf₁dvd⟩ :=
    WfDvdMonoid.exists_irreducible_factor hfpnu hfp.ne_zero
  haveI : Fact (Irreducible f₁) := ⟨hf₁irr⟩
  haveI : CharP (AdjoinRoot f₁) p :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod p) (AdjoinRoot f₁)).injective p
  -- the projection `Z_n[x] → K` and the image of `g`
  set π : Polynomial (ZMod n) →+* AdjoinRoot f₁ :=
    (AdjoinRoot.mk f₁).comp (mapRingHom φ) with hπdef
  have hπ : ∀ x : Polynomial (ZMod n),
      π x = AdjoinRoot.mk f₁ (x.map φ) := fun x => rfl
  have hπf : π f = 0 := by
    rw [hπ, AdjoinRoot.mk_eq_zero]
    exact hf₁dvd
  -- (1): `ḡ^(n^I−1) = 1`
  have hg1 : π g ^ (n ^ I - 1) = 1 := by
    have hd := map_dvd π h1
    rw [hπf, zero_dvd_iff, map_sub, map_pow, map_one, sub_eq_zero] at hd
    exact hd
  -- (2): `ḡ^((n^I−1)/q) ≠ 1` for primes `q ∣ F`
  have hg2 : ∀ q : ℕ, q.Prime → q ∣ F → π g ^ ((n ^ I - 1) / q) ≠ 1 := by
    intro q hqp hqF heq
    have hco := (h2 q hqp hqF).map π
    rw [hπf, isCoprime_zero_right, map_sub, map_pow, map_one, heq,
      sub_self] at hco
    exact not_isUnit_zero hco
  -- the order of `ḡ` is a multiple of `F`
  have hordF : F ∣ orderOf (π g) :=
    dvd_orderOf_of_pow_eq_one hN0 hF hFN hg1 hg2
  have hfin : IsOfFinOrder (π g) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n ^ I - 1, hN0, hg1⟩
  -- the conjugate multiset and the polynomial `h(T) = ∏ (T − ḡ^(n^j))`
  set S : Multiset (AdjoinRoot f₁) :=
    (Multiset.range I).map (fun j => π g ^ n ^ j) with hS
  have hScard : S.card = I := by
    rw [hS, Multiset.card_map, Multiset.card_range]
  have hSmap : S = ((Multiset.range I).map fun j => g ^ n ^ j).map π := by
    rw [hS, Multiset.map_map]
    exact Multiset.map_congr rfl fun j _ => (map_pow π g (n ^ j)).symm
  -- (3): the elementary symmetric functions of `S` are Frobenius-fixed
  have hesymm : ∀ k, k ≤ I →
      frobenius (AdjoinRoot f₁) p (S.esymm k) = S.esymm k := by
    intro k hkI
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have h0 : S.esymm 0 = 1 := by
        simp [Multiset.esymm, Multiset.powersetCard_zero_left]
      rw [h0, map_one]
    obtain ⟨c, hc⟩ := h3 k hk1 hkI
    have hd := map_dvd π hc
    rw [hπf, zero_dvd_iff, map_sub, sub_eq_zero] at hd
    rw [hSmap, esymm_map, hd, hπ, map_C, frobenius_def, ← map_pow,
      ← C_pow, ZMod.pow_card]
  set h : Polynomial (AdjoinRoot f₁) :=
    (S.map fun a => X - C a).prod with hh
  -- `h` has Frobenius-fixed coefficients
  have hdegh : h.natDegree ≤ I := by
    rw [hh]
    refine le_trans (natDegree_multiset_prod_le _) ?_
    rw [Multiset.map_map]
    have hone : ((S.map fun a => (X - C a).natDegree)).sum = I := by
      rw [Multiset.map_congr rfl fun a _ => natDegree_X_sub_C a]
      simp [hScard]
    exact le_of_eq hone
  have hfrob : h.map (frobenius (AdjoinRoot f₁) p) = h := by
    ext k
    rw [coeff_map]
    rcases Nat.lt_or_ge I k with hk | hk
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegh hk),
        map_zero]
    · have hcoeff := Multiset.prod_X_sub_C_coeff S
        (show k ≤ S.card by rw [hScard]; exact hk)
      rw [hScard] at hcoeff
      rw [hh, hcoeff, map_mul, map_pow, map_neg, map_one,
        hesymm (I - k) (by omega)]
  -- `h(ḡ) = 0`, hence `h(ḡ^p) = Frob (h(ḡ)) = 0`
  have hroot : h.eval (π g) = 0 := by
    rw [hh, eval_multiset_prod, Multiset.map_map]
    refine Multiset.prod_eq_zero (Multiset.mem_map.mpr
      ⟨π g ^ n ^ 0, Multiset.mem_map.mpr
        ⟨0, Multiset.mem_range.mpr hI, rfl⟩, ?_⟩)
    show eval (π g) (X - C (π g ^ n ^ 0)) = 0
    rw [eval_sub, eval_X, eval_C, pow_zero, pow_one, sub_self]
  have hrootp : h.eval (π g ^ p) = 0 := by
    have h0 : frobenius (AdjoinRoot f₁) p (h.eval (π g)) = 0 := by
      rw [hroot, map_zero]
    rw [← eval₂_at_apply, ← eval_map, hfrob, frobenius_def] at h0
    exact h0
  -- the factored form pins `ḡ^p` to a conjugate `ḡ^(n^j)`
  rw [hh, eval_multiset_prod, Multiset.map_map,
    Multiset.prod_eq_zero_iff] at hrootp
  obtain ⟨a, haS, ha0⟩ := Multiset.mem_map.mp hrootp
  obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp haS
  refine ⟨j, Multiset.mem_range.mp hj, ?_⟩
  have hpow : π g ^ p = π g ^ n ^ j := by
    have := ha0
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at this
    rwa [sub_eq_zero] at this
  -- exponents are determined mod the order, hence mod `F`
  exact (hfin.pow_eq_pow_iff_modEq.mp hpow).of_dvd hordF

end CP

end Azurite

/-! ### A worked instance

The degenerate band `I = 1` already exercises the statement: `n = 7`,
`F = 6 = 7^1 − 1`, `f = x`, `g = 3`.  Condition (1) is Fermat
(`3^6 ≡ 1 (mod 7)`), condition (2) holds since `3^3 − 1 ≡ 5` and
`3^2 − 1 ≡ 1` are units mod `7`, and condition (3) is trivial
(`g` itself is a constant).  The conclusion: every prime factor of `7`
is `≡ 1 (mod 6)`. -/

section Examples

open Polynomial Azurite.CP

example (p : ℕ) (hp : p.Prime) (hpn : p ∣ 7) : p % 6 = 1 := by
  have key := theorem_4_3_3 (n := 7) (I := 1) (F := 6)
    (by norm_num) one_pos (by norm_num) (by norm_num)
    (f := (X : Polynomial (ZMod 7))) (g := C 3)
    monic_X (by
      haveI : Fact (1 < 7) := ⟨by norm_num⟩
      rw [natDegree_X]
      exact one_pos)
    (by
      -- (1): `x ∣ C 3 ^ 6 − 1 = C (3^6 − 1) = 0`
      have h36 : (3 : ZMod 7) ^ 6 - 1 = 0 := by decide
      rw [show (7 : ℕ) ^ 1 - 1 = 6 by norm_num, ← C_pow, ← C_1, ← C_sub,
        h36, C_0]
      exact dvd_zero _)
    (by
      -- (2): the two subexponent values are units
      intro q hq hq6
      have hqle : q ≤ 6 := Nat.le_of_dvd (by norm_num) hq6
      have hq2 : 2 ≤ q := hq.two_le
      interval_cases q
      · -- `q = 2`: `3^3 − 1 ≡ 5`, inverse `3`
        refine ⟨C 3, 0, ?_⟩
        have h5 : (3 : ZMod 7) * ((3 : ZMod 7) ^ 3 - 1) = 1 := by decide
        rw [show ((7 : ℕ) ^ 1 - 1) / 2 = 3 by norm_num, ← C_pow, ← C_1,
          ← C_sub, ← C_mul, h5, C_1, zero_mul, add_zero]
      · -- `q = 3`: `3^2 − 1 ≡ 1`
        have h1 : (3 : ZMod 7) ^ 2 - 1 = 1 := by decide
        rw [show ((7 : ℕ) ^ 1 - 1) / 3 = 2 by norm_num, ← C_pow, ← C_1,
          ← C_sub, h1, C_1]
        exact isCoprime_one_left
      · exact absurd hq6 (by decide)
      · exact absurd hq6 (by decide)
      · exact absurd hq (by decide))
    (by
      -- (3): the only symmetric function of the singleton `{g}` is `g`
      intro k hk1 hkI
      obtain rfl : k = 1 := by omega
      refine ⟨3, ?_⟩
      have hsingle : ((Multiset.range 1).map
          fun j => (C (3 : ZMod 7)) ^ 7 ^ j).esymm 1 = C 3 := by
        simp [Multiset.esymm, Multiset.powersetCard_one]
      rw [hsingle, sub_self]
      exact dvd_zero _)
    hp hpn
  obtain ⟨j, hj, hmod⟩ := key
  interval_cases j
  simpa [Nat.ModEq] using hmod

end Examples
