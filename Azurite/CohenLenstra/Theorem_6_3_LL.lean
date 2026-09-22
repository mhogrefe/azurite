/-
  **The generalized Theorem (6.3) for `s = s₁·s₂`** — the assembly theorem
  of the 1987 algorithm (Section 5, (5.3)/(5.4)), phase B2 of the plan.

  In the 1984 Theorem (6.3) every prime `q ∣ s` is a `q`-prime
  (`q − 1 ∣ t`), and characters of `p`-power order generate the character
  group mod `q`.  In 1987 the modulus is `s = s₁·s₂`: the primes of `s₂`
  are still `q`-primes handled by Jacobi sums, but the primes of `s₁`
  divide `f⁻·f⁺` and are handled by the Lucas–Lehmer stage, which gives
  a *coherent* base congruence `r ≡ n^(ε(r)) (mod p)` (`ε(r) ∈ {0,1}`,
  Theorem `test_4_3_confinement` and the `f⁻`-side Pocklington fact) and
  condition (6.4) at all levels (via Proposition (10.7)), with the parity
  of the `2`-adic exponent equal to `ε(r)` (`c1_two_adic`, `c2_two_adic`).

  The proof is the 1984 one with the CRT exponent `l(r)` also forced to
  the parity `ε(r)`: for `p ∣ s₂` the character argument gives
  `r ≡ n^l (mod p)`; for `p ∣ s₁` the base congruence and `n² ≡ 1 (mod p)`
  give it; in both cases (6.4) at `p` and the unit-order endgame
  (`modEq_pow_of_modEq_of_pow_modEq`: a unit `≡ 1 (mod p)` with
  `a^(p−1) ≡ 1 (mod p^m)` is `1`) lift to `p^(v_p(s))`; primes of `s₁`
  not dividing `t'` need no lifting since `p^(v_p(s₁)) ∣ n² − 1`.
  Condition (2.3) is replaced by `n^(t') ≡ 1 (mod s)`
  (`pow_modEq_one_s1_mul_s2`).
-/
import Azurite.CohenLenstra.Theorem_6_3
import Azurite.CohenLenstra.Impl_5_2

namespace Azurite

namespace CL

open Finset

/-! ### The endgame, factored out of Theorem (6.3) -/

/-- **Transfer of the (6.4) exponent** along the CRT congruence: if
`n^(p−1) ≡ 1 (mod p)` and `l ≡ l' (mod p^H)` with `H ≥ m − 1`, then
`(n^(p−1))^l ≡ (n^(p−1))^l' (mod p^m)`. -/
theorem pow_sub_one_pow_modEq {n p m H l l' : ℕ} (hm : 1 ≤ m)
    (hfermat : n ^ (p - 1) ≡ 1 [MOD p]) (hH : m - 1 ≤ H) (hl : l ≡ l' [MOD p ^ H]) :
    (n ^ (p - 1)) ^ l ≡ (n ^ (p - 1)) ^ l' [MOD p ^ m] := by
  have hx1 : (((n ^ (p - 1) : ℕ)) : ZMod (p ^ m)) ^ p ^ (m - 1) = 1 := by
    have h2 := pow_pow_modEq_one hfermat (m - 1)
    rw [Nat.sub_add_cancel hm] at h2
    rw [← Nat.cast_pow, (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2, Nat.cast_one]
  have hxH : (((n ^ (p - 1) : ℕ)) : ZMod (p ^ m)) ^ p ^ H = 1 := by
    obtain ⟨c, hc⟩ := pow_dvd_pow p hH
    rw [hc, pow_mul, hx1, one_pow]
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  rw [Nat.cast_pow (n ^ (p - 1)) l, Nat.cast_pow (n ^ (p - 1)) l']
  exact pow_eq_pow_of_modEq hxH hl

/-- **The unit-order endgame**: if `r ≡ N (mod p)` and
`r^(p−1) ≡ N^(p−1) (mod p^m)` for units `r, N` mod `p^m`, then
`r ≡ N (mod p^m)` — the unit `r·N⁻¹` has order dividing
`gcd(p − 1, p^(m−1)) = 1`. -/
theorem modEq_pow_of_modEq_of_pow_modEq {r N p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hr : r.Coprime p) (hN : N.Coprime p) (hmod : r ≡ N [MOD p])
    (hc : r ^ (p - 1) ≡ N ^ (p - 1) [MOD p ^ m]) : r ≡ N [MOD p ^ m] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hrM : r.Coprime (p ^ m) := hr.pow_right m
  have hNM : N.Coprime (p ^ m) := hN.pow_right m
  set RU := ZMod.unitOfCoprime r hrM with hRU
  set NU := ZMod.unitOfCoprime N hNM with hNU
  have hA1 : (RU * NU⁻¹) ^ (p - 1) = 1 := by
    have hpow : RU ^ (p - 1) = NU ^ (p - 1) := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hRU, hNU,
        ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_pow]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc
    rw [mul_pow, inv_pow, hpow, mul_inv_cancel]
  have hAq : (RU * NU⁻¹) ^ p ^ (m - 1) = 1 := by
    refine units_pow_prime_pow_eq_one hp (by omega : m ≠ 0) _ ?_
    have hmapeq : Units.map (ZMod.castHom (dvd_pow_self p (by omega : m ≠ 0)) (ZMod p)).toMonoidHom RU
        = Units.map (ZMod.castHom (dvd_pow_self p (by omega : m ≠ 0)) (ZMod p)).toMonoidHom NU := by
      refine Units.ext ?_
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      rw [hRU, hNU, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, map_natCast, map_natCast]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    rw [map_mul, map_inv, hmapeq, mul_inv_cancel]
  have hAone : RU * NU⁻¹ = 1 := by
    have hd1 : orderOf (RU * NU⁻¹) ∣ p - 1 := orderOf_dvd_of_pow_eq_one hA1
    have hd2 : orderOf (RU * NU⁻¹) ∣ p ^ (m - 1) := orderOf_dvd_of_pow_eq_one hAq
    have hcop : Nat.Coprime (p - 1) (p ^ (m - 1)) := by
      refine Nat.Coprime.pow_right _ ?_
      have h1 := Nat.gcd_dvd_left (p - 1) p
      have h2 := Nat.gcd_dvd_right (p - 1) p
      have h3 := Nat.dvd_sub h2 h1
      rw [show p - (p - 1) = 1 from by have := hp.pos; omega, Nat.dvd_one] at h3
      exact h3
    rw [← orderOf_eq_one_iff]
    exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2)
  have hRUNU : RU = NU := mul_inv_eq_one.mp hAone
  have := congrArg (fun u : (ZMod (p ^ m))ˣ => (u : ZMod (p ^ m))) hRUNU
  rw [hRU, hNU] at this
  simp only [ZMod.coe_unitOfCoprime] at this
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this

/-- Fermat for `n` coprime to the prime `p`. -/
theorem pow_sub_one_modEq_one {n p : ℕ} (hp : p.Prime) (hco : n.Coprime p) :
    n ^ (p - 1) ≡ 1 [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz : ((n : ℕ) : ZMod p) ≠ 0 := fun h0 =>
    hp.one_lt.ne' (hco.symm.eq_one_of_dvd ((ZMod.natCast_eq_zero_iff n p).mp h0))
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  rw [Nat.cast_pow, Nat.cast_one, ZMod.pow_card_sub_one_eq_one hz]

/-- `n^l ≡ n^ε (mod M)` when `n² ≡ 1 (mod M)` and `l ≡ ε (mod 2)`. -/
theorem pow_modEq_pow_of_sq_modEq_one {n l ε M : ℕ} (hn2 : n ^ 2 ≡ 1 [MOD M])
    (hl : l % 2 = ε % 2) : n ^ l ≡ n ^ ε [MOD M] := by
  have key : ∀ j : ℕ, n ^ j ≡ n ^ (j % 2) [MOD M] := fun j => by
    conv_lhs => rw [← Nat.div_add_mod j 2, pow_add, pow_mul]
    calc (n ^ 2) ^ (j / 2) * n ^ (j % 2) ≡ 1 ^ (j / 2) * n ^ (j % 2) [MOD M] :=
          (hn2.pow _).mul_right _
      _ = n ^ (j % 2) := by rw [one_pow, one_mul]
  exact (key l).trans (by rw [hl]; exact (key ε).symm)

/-! ### The generalized Theorem (6.3), prime-divisor case -/

/-- **Generalized Theorem (6.3), prime-divisor case.**  `s = s₁·s₂` with
`s₁ ⊥ s₂`; the primes `q` of `s₂` are `q`-primes of `t'` (`q − 1 ∣ t'`,
and `q ∣ t'` whenever `q² ∣ s₂`), with characters `Y q p` of `p`-power
order as in Theorem (6.3); the primes of `s₁` divide `n² − 1`, and to the
full power of `s₁` when they do not divide `t'`.  For a divisor `r ∣ n`
(primality is not needed):
an `ε ∈ {0, 1}` with `r ≡ n^ε (mod p)` for every `p ∣ s₁`, to the full
power when `p ∤ t'`; and for every `p ∣ t'` an exponent `l_p` (`≡ ε mod 2`
for `p = 2`) satisfying (6.5) at the `s₂`-primes and (6.4) mod
`p^(v_p(s))`.  Then `r ≡ n^l (mod s)` for some `l`. -/
theorem theorem_6_3_LL_prime {n s₁ s₂ t' : ℕ} (hn1 : 1 < n) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (ht : 0 < t')
    (ht2 : 2 ∣ t') (hns : n.Coprime (s₁ * s₂)) (hcop : Nat.Coprime s₁ s₂)
    (hq : ∀ q ∈ s₂.primeFactors, (q - 1) ∣ t' ∧ (2 ≤ s₂.factorization q → q ∣ t'))
    (hF1 : ∀ p ∈ s₁.primeFactors, p ∣ n ^ 2 - 1)
    (hF2 : ∀ p ∈ s₁.primeFactors, ¬ p ∣ t' → p ^ s₁.factorization p ∣ n ^ 2 - 1)
    (Y : (q : ℕ) → (p : ℕ) → MulChar (ZMod q) ℂ)
    (hY : ∀ q ∈ s₂.primeFactors, ∀ p ∈ (q - 1).primeFactors,
      orderOf (Y q p) = p ^ (q - 1).factorization p)
    {r : ℕ} (hrn : r ∣ n) {ε : ℕ} (hε : ε < 2)
    (hbase : ∀ p ∈ s₁.primeFactors, r ≡ n ^ ε [MOD p])
    (hbase' : ∀ p ∈ s₁.primeFactors, ¬ p ∣ t' → r ≡ n ^ ε [MOD p ^ s₁.factorization p])
    (h : ∀ p ∈ t'.primeFactors, ∃ l : ℕ, (p = 2 → l % 2 = ε) ∧
      (∀ q ∈ s₂.primeFactors, p ∣ q - 1 →
        Y q p ((r : ℕ) : ZMod q) = Y q p ((n : ℕ) : ZMod q) ^ l) ∧
      r ^ (p - 1) ≡ (n ^ (p - 1)) ^ l [MOD p ^ (s₁ * s₂).factorization p]) :
    ∃ i : ℕ, r ≡ n ^ i [MOD s₁ * s₂] := by
  classical
  set s := s₁ * s₂ with hsdef
  have hs : 0 < s := Nat.mul_pos hs₁ hs₂
  have hrs : r.Coprime s := Nat.Coprime.coprime_dvd_left hrn hns
  -- the CRT modulus data (with a factor `2` so that `2 ∣ P`)
  set P := 2 * s * ∏ q ∈ s₂.primeFactors, (q - 1) with hPdef
  have hP0 : P ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hs.ne')
    (Finset.prod_ne_zero_iff.mpr fun q hq =>
      Nat.sub_ne_zero_of_lt (Nat.prime_of_mem_primeFactors hq).one_lt)
  -- select the exponents, totalized
  have h' : ∀ p : ℕ, ∃ l : ℕ, p ∈ t'.primeFactors →
      ((p = 2 → l % 2 = ε) ∧
       (∀ q ∈ s₂.primeFactors, p ∣ q - 1 →
        Y q p ((r : ℕ) : ZMod q) = Y q p ((n : ℕ) : ZMod q) ^ l) ∧
       r ^ (p - 1) ≡ (n ^ (p - 1)) ^ l [MOD p ^ s.factorization p]) := by
    intro p
    by_cases hp : p ∈ t'.primeFactors
    · obtain ⟨l, hl⟩ := h p hp
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun hcon => (hp hcon).elim⟩
  choose lp hlp using h'
  -- the common exponent, by CRT over the primes dividing t'
  obtain ⟨l, hl⟩ := Nat.chineseRemainderOfFinset lp
    (fun p => p ^ P.factorization p) t'.primeFactors
    (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).pos.ne')
    (fun p hp p' hp' hne => Nat.Coprime.pow _ _
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hp')).mpr hne))
  -- the parity of `l` is `ε`
  have h2t : 2 ∈ t'.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, ht2, ht.ne'⟩
  have hlpar : l % 2 = ε := by
    have h2P : 1 ≤ P.factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two hP0
        ((dvd_mul_right 2 s).trans (dvd_mul_right _ _))
    have hl2 := hl 2 h2t
    have : l ≡ lp 2 [MOD 2] := Nat.ModEq.of_dvd (dvd_pow_self 2 (by omega)) hl2
    rw [Nat.ModEq] at this
    rw [this]
    exact (hlp 2 h2t).1 rfl
  -- valuations of `s` at primes of `s₁` and of `s₂`
  have hfac₁ : ∀ p ∈ s₁.primeFactors, s.factorization p = s₁.factorization p := by
    intro p hp
    rw [hsdef, Nat.factorization_mul hs₁.ne' hs₂.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (n := s₂) (p := p) (fun hd => ?_), add_zero]
    have hp' := Nat.prime_of_mem_primeFactors hp
    exact hp'.one_lt.ne' (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hcop) hd)
  have hfac₂ : ∀ q ∈ s₂.primeFactors, s.factorization q = s₂.factorization q := by
    intro q hq'
    rw [hsdef, Nat.factorization_mul hs₁.ne' hs₂.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (n := s₁) (p := q) (fun hd => ?_), zero_add]
    have hq'' := Nat.prime_of_mem_primeFactors hq'
    exact hq''.one_lt.ne' (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hq') hcop.symm) hd)
  -- the congruence modulo each maximal prime power of s
  have key : ∀ p ∈ s.primeFactors, r ≡ n ^ l [MOD p ^ s.factorization p] := by
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hp'⟩
    have hps : p ∣ s := Nat.dvd_of_mem_primeFactors hp
    have hcopn : n.Coprime p := Nat.Coprime.coprime_dvd_right hps hns
    have hcopr : r.Coprime p := Nat.Coprime.coprime_dvd_right hps hrs
    have hfermat : n ^ (p - 1) ≡ 1 [MOD p] := pow_sub_one_modEq_one hp' hcopn
    set m := s.factorization p with hmdef
    have hm1 : 1 ≤ m := Nat.Prime.factorization_pos_of_dvd hp' hs.ne' hps
    have hmP : m - 1 ≤ P.factorization p :=
      le_trans (Nat.sub_le m 1)
        (Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hs.ne' hP0).mpr
          ((dvd_mul_left s 2).trans (dvd_mul_right _ _))) p)
    -- the lifting step, common to both kinds of primes
    have lift : r ≡ n ^ l [MOD p] → p ∈ t'.primeFactors → r ≡ n ^ l [MOD p ^ m] := by
      intro hqmod hpt
      have hB := (hlp p hpt).2.2
      have htr := pow_sub_one_pow_modEq hm1 hfermat hmP (hl p hpt)
      have hc : r ^ (p - 1) ≡ (n ^ l) ^ (p - 1) [MOD p ^ m] := by
        refine (hB.trans htr.symm).trans ?_
        rw [← pow_mul, mul_comm (p - 1) l, pow_mul]
      exact modEq_pow_of_modEq_of_pow_modEq hp' hm1 hcopr (hcopn.pow_left l) hqmod hc
    -- which factor does `p` divide?
    rcases (Nat.Prime.dvd_mul hp').mp hps with hp₁ | hp₂
    · -- `p ∣ s₁`: the Lucas–Lehmer base congruence and the parity of `l`
      have hp₁' : p ∈ s₁.primeFactors := Nat.mem_primeFactors.mpr ⟨hp', hp₁, hs₁.ne'⟩
      have hn2 : n ^ 2 ≡ 1 [MOD p] :=
        ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mpr (hF1 p hp₁')).symm
      have hqmod : r ≡ n ^ l [MOD p] :=
        (hbase p hp₁').trans (pow_modEq_pow_of_sq_modEq_one hn2 (by
          rw [hlpar, Nat.mod_eq_of_lt hε])).symm
      by_cases hpt : p ∣ t'
      · exact lift hqmod (Nat.mem_primeFactors.mpr ⟨hp', hpt, ht.ne'⟩)
      · rw [hmdef, hfac₁ p hp₁']
        have hn2' : n ^ 2 ≡ 1 [MOD p ^ s₁.factorization p] :=
          ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mpr (hF2 p hp₁' hpt)).symm
        exact (hbase' p hp₁' hpt).trans (pow_modEq_pow_of_sq_modEq_one hn2' (by
          rw [hlpar, Nat.mod_eq_of_lt hε])).symm
    · -- `p ∣ s₂`: the character argument of Theorem (6.3)
      have hp₂' : p ∈ s₂.primeFactors := Nat.mem_primeFactors.mpr ⟨hp', hp₂, hs₂.ne'⟩
      obtain ⟨hq1t, hq2t⟩ := hq p hp₂'
      -- Step A: χ(r) = χ(n^l) for every character mod p
      have hall : ∀ χ : MulChar (ZMod p) ℂ,
          χ ((r : ℕ) : ZMod p) = χ (((n : ℕ) : ZMod p) ^ l) := by
        have hgen : Subgroup.closure
            {χ : MulChar (ZMod p) ℂ | ∃ p' ∈ (p - 1).primeFactors, χ = Y p p'} = ⊤ :=
          closure_eq_top_of_forall_orderOf fun p' hp'' =>
            ⟨Y p p', ⟨p', hp'', rfl⟩, hY p hp₂' p' hp''⟩
        intro χ
        have hχmem : χ ∈ Subgroup.closure
            {χ : MulChar (ZMod p) ℂ | ∃ p' ∈ (p - 1).primeFactors, χ = Y p p'} := by
          rw [hgen]; exact Subgroup.mem_top χ
        induction hχmem using Subgroup.closure_induction with
        | mem χ' hχ' =>
          obtain ⟨p', hp'q1, rfl⟩ := hχ'
          have hp'' : p'.Prime := Nat.prime_of_mem_primeFactors hp'q1
          have hp'q1' : p' ∣ p - 1 := Nat.dvd_of_mem_primeFactors hp'q1
          have hp't : p' ∈ t'.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hp'', hp'q1'.trans hq1t, ht.ne'⟩
          have hA := (hlp p' hp't).2.1 p hp₂' hp'q1'
          have hxord : (Y p p' ((n : ℕ) : ZMod p)) ^ p' ^ P.factorization p' = 1 := by
            have hd : orderOf (Y p p') ∣ p' ^ P.factorization p' := by
              rw [hY p hp₂' p' hp'q1]
              refine pow_dvd_pow p' ?_
              have hq1P : (p - 1) ∣ P :=
                (Finset.dvd_prod_of_mem (fun q' => q' - 1) hp₂').trans (dvd_mul_left _ _)
              exact Finsupp.le_def.mp
                ((Nat.factorization_le_iff_dvd (Nat.sub_ne_zero_of_lt hp'.one_lt) hP0).mpr
                  hq1P) p'
            obtain ⟨c, hc⟩ := hd
            have hbase0 : (Y p p' ((n : ℕ) : ZMod p)) ^ orderOf (Y p p') = 1 := by
              rw [show ((n : ℕ) : ZMod p)
                    = ((ZMod.unitOfCoprime n hcopn : (ZMod p)ˣ) : ZMod p)
                  from (ZMod.coe_unitOfCoprime n hcopn).symm,
                ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
            rw [hc, pow_mul, hbase0, one_pow]
          rw [map_pow, hA, pow_eq_pow_of_modEq hxord ((hl p' hp't).symm)]
        | one =>
          rw [show ((r : ℕ) : ZMod p)
                = ((ZMod.unitOfCoprime r hcopr : (ZMod p)ˣ) : ZMod p)
              from (ZMod.coe_unitOfCoprime r hcopr).symm,
            show (((n : ℕ) : ZMod p) ^ l)
                = ((ZMod.unitOfCoprime n hcopn ^ l : (ZMod p)ˣ) : ZMod p)
              from by rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime],
            MulChar.one_apply_coe, MulChar.one_apply_coe]
        | mul χ₁ χ₂ _ _ h₁ h₂ =>
          rw [MulChar.mul_apply, MulChar.mul_apply, h₁, h₂]
        | inv χ' _ h' =>
          rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', h']
      -- Step B: separation gives the congruence mod p
      have hqmod : r ≡ n ^ l [MOD p] := by
        have hu := eq_6_1 (x := ZMod.unitOfCoprime r hcopr)
          (y := ZMod.unitOfCoprime n hcopn ^ l) fun χ => by
            rw [ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
            exact hall χ
        have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hu
        simp only [ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val] at this
        refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
        rw [Nat.cast_pow]
        exact this
      -- Step C: upgrade to the maximal power of p in s
      rcases eq_or_lt_of_le hm1 with hm | hm
      · rw [← hm, pow_one]
        exact hqmod
      · have hpt : p ∈ t'.primeFactors := by
          refine Nat.mem_primeFactors.mpr ⟨hp', hq2t ?_, ht.ne'⟩
          rw [← hfac₂ p hp₂']
          exact hm
        exact lift hqmod hpt
  -- assemble over the primes dividing s
  refine ⟨l, ?_⟩
  have hsprod : ∏ q ∈ s.primeFactors, q ^ s.factorization q = s := by
    rw [← Nat.support_factorization, ← Finsupp.prod]
    exact Nat.prod_factorization_pow_eq_self hs.ne'
  rw [← hsprod]
  refine modEq_prod_of_pairwise_coprime ?_ key
  intro q hq' q' hq'' hne
  exact Nat.Coprime.pow _ _
    ((Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq'))
      (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq''))).mpr hne)

/-- **Generalized Theorem (6.3)**: under the hypotheses of
`theorem_6_3_LL_prime` for every prime divisor of `n`, together with
`n^(t') ≡ 1 (mod s₁·s₂)`, every divisor `r` of `n` satisfies
`r ≡ n^i (mod s₁·s₂)` for some `i < t'` — condition (2.5) for the final
trial division. -/
theorem theorem_6_3_LL {n s₁ s₂ t' : ℕ} (hn : 1 < n) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (ht : 0 < t')
    (ht2 : 2 ∣ t') (hns : n.Coprime (s₁ * s₂)) (hcop : Nat.Coprime s₁ s₂)
    (hpow : n ^ t' ≡ 1 [MOD s₁ * s₂])
    (hq : ∀ q ∈ s₂.primeFactors, (q - 1) ∣ t' ∧ (2 ≤ s₂.factorization q → q ∣ t'))
    (hF1 : ∀ p ∈ s₁.primeFactors, p ∣ n ^ 2 - 1)
    (hF2 : ∀ p ∈ s₁.primeFactors, ¬ p ∣ t' → p ^ s₁.factorization p ∣ n ^ 2 - 1)
    (Y : (q : ℕ) → (p : ℕ) → MulChar (ZMod q) ℂ)
    (hY : ∀ q ∈ s₂.primeFactors, ∀ p ∈ (q - 1).primeFactors,
      orderOf (Y q p) = p ^ (q - 1).factorization p)
    (h : ∀ r ∈ n.primeFactors, ∃ ε < 2,
      (∀ p ∈ s₁.primeFactors, r ≡ n ^ ε [MOD p]) ∧
      (∀ p ∈ s₁.primeFactors, ¬ p ∣ t' → r ≡ n ^ ε [MOD p ^ s₁.factorization p]) ∧
      (∀ p ∈ t'.primeFactors, ∃ l : ℕ, (p = 2 → l % 2 = ε) ∧
        (∀ q ∈ s₂.primeFactors, p ∣ q - 1 →
          Y q p ((r : ℕ) : ZMod q) = Y q p ((n : ℕ) : ZMod q) ^ l) ∧
        r ^ (p - 1) ≡ (n ^ (p - 1)) ^ l [MOD p ^ (s₁ * s₂).factorization p])) :
    ∀ r, r ∣ n → ∃ i < t', r ≡ n ^ i [MOD s₁ * s₂] := by
  -- every divisor is congruent to SOME power of n mod s
  have hstep : ∀ r : ℕ, r ∣ n → ∃ i : ℕ, r ≡ n ^ i [MOD s₁ * s₂] := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hrn
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact (by omega : n ≠ 0) (Nat.eq_zero_of_zero_dvd hrn)
      rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hr0) with h1 | h1
      · exact ⟨0, by rw [← h1, pow_zero]⟩
      · have hrp : r.minFac.Prime := Nat.minFac_prime (by omega)
        have hmem : r.minFac ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hrp, (Nat.minFac_dvd r).trans hrn, by omega⟩
        obtain ⟨ε, hε, hb, hb', hpl⟩ := h r.minFac hmem
        obtain ⟨i₁, hi₁⟩ := theorem_6_3_LL_prime hn hs₁ hs₂ ht ht2 hns hcop hq hF1 hF2 Y hY
          ((Nat.minFac_dvd r).trans hrn) hε hb hb' hpl
        obtain ⟨i₂, hi₂⟩ := ih (r / r.minFac)
          (Nat.div_lt_self (by omega) hrp.one_lt)
          ((Nat.div_dvd_of_dvd (Nat.minFac_dvd r)).trans hrn)
        refine ⟨i₁ + i₂, ?_⟩
        calc r = r.minFac * (r / r.minFac) := (Nat.mul_div_cancel' (Nat.minFac_dvd r)).symm
          _ ≡ n ^ i₁ * n ^ i₂ [MOD s₁ * s₂] := hi₁.mul hi₂
          _ = n ^ (i₁ + i₂) := (pow_add n i₁ i₂).symm
  -- reduce the exponent modulo t', using n^t' ≡ 1 (mod s)
  intro r hrn
  obtain ⟨i, hi⟩ := hstep r hrn
  refine ⟨i % t', Nat.mod_lt _ ht, ?_⟩
  refine hi.trans ?_
  have hx : ((n : ℕ) : ZMod (s₁ * s₂)) ^ t' = 1 := by
    rw [← Nat.cast_pow, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hpow, Nat.cast_one]
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  rw [Nat.cast_pow, Nat.cast_pow]
  exact pow_eq_pow_of_modEq hx (Nat.mod_modEq i t').symm

end CL

end Azurite
