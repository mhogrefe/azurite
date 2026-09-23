/-
  **From a passed `(p, q)` test to the character equation `χ(r) = ζ^(f₀·m)`**
  (Theorems (8.5)/(9.1)/(9.3)/(9.5)/(9.10)/(9.19) followed by Theorem (7.8)).

  The 1984 theorems live in a domain containing both a primitive `p^k`-th
  and a primitive `q`-th root of unity.  We use the common ring
  `R = ℤ[ζ_{q·p^k}]` (`CycM (q * p^k)`), with `ζ_P = ζ^q`, `ζ_Q = ζ^{p^k}`,
  the additive character `ψ(a) = ζ_Q^a`, the character `χ_R` of order `p^k`
  with `χ_R(g) = ζ_P`, and the automorphism `σ = σ_c` with `c ≡ n (mod p^k)`,
  `c ≡ 1 (mod q)` (so `σ(ζ_P) = ζ_P^n`, `σ(ζ_Q) = ζ_Q`).  The ideal is `(n)`.
  The computed congruence in `ℤ[ζ_{p^k}]` is transported along the
  embedding `φ : ℤ[ζ_{p^k}] → R`, `ζ ↦ ζ_P`, under which the table character
  `chiT` becomes `χ_R` (`chiT_ringHomComp`).
-/
import Azurite.APRCL.Equiv.JacobiStage
import Azurite.CohenLenstra.Theorem_7_8
import Azurite.CohenLenstra.Theorem_8_5
import Azurite.CohenLenstra.Theorem_9_1
import Azurite.CohenLenstra.Theorem_9_19
import Azurite.CohenLenstra.Method_10_2
import Azurite.CohenLenstra.Algorithm_11_1

namespace Azurite

namespace APRCL

open CL CP Finset Polynomial

section CommonRing

variable {q p k : ℕ} [hqF : Fact q.Prime] (hp : p.Prime) (hk : 0 < k) (hpk : p ^ k ∣ q - 1)

/-- The common ring `R = ℤ[ζ_{q·p^k}]`. -/
abbrev CR (q p k : ℕ) := CycM (q * p ^ k)

include hp in
theorem cr_pos : 0 < q * p ^ k := Nat.mul_pos hqF.out.pos (pow_pos hp.pos k)

/-- `ζ_P = ζ^q`, a primitive `p^k`-th root of unity. -/
noncomputable def zP (q p k : ℕ) : CR q p k := zetaM (q * p ^ k) ^ q

/-- `ζ_Q = ζ^{p^k}`, a primitive `q`-th root of unity. -/
noncomputable def zQ (q p k : ℕ) : CR q p k := zetaM (q * p ^ k) ^ p ^ k

include hp in
theorem isPrimitiveRoot_zP : IsPrimitiveRoot (zP q p k) (p ^ k) :=
  (isPrimitiveRoot_zetaM (cr_pos hp)).pow (cr_pos hp) rfl

include hp in
theorem isPrimitiveRoot_zQ : IsPrimitiveRoot (zQ q p k) q :=
  (isPrimitiveRoot_zetaM (cr_pos hp)).pow (cr_pos hp) (mul_comm _ _)

include hp in
theorem zP_pow_eq_one : zP q p k ^ p ^ k = 1 := (isPrimitiveRoot_zP hp).pow_eq_one

/-- The additive character `ψ(a) = ζ_Q^a`. -/
noncomputable def psiR (q p k : ℕ) [Fact q.Prime] (hp : p.Prime) : AddChar (ZMod q) (CR q p k) :=
  AddChar.zmodChar q (isPrimitiveRoot_zQ (k := k) hp).pow_eq_one

include hp in
theorem psiR_primitive : (psiR q p k hp).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root q (isPrimitiveRoot_zQ hp)

include hp in
theorem psiR_apply (a : ZMod q) : psiR q p k hp a = zQ q p k ^ a.val :=
  AddChar.zmodChar_apply _ a

/-- `ζ_P` as a unit. -/
noncomputable def zPu (q p k : ℕ) [Fact q.Prime] (hp : p.Prime) : (CR q p k)ˣ :=
  ((isPrimitiveRoot_zP (k := k) hp).isUnit (pow_pos hp.pos k).ne').unit

include hp in
theorem val_zPu : ((zPu q p k hp : (CR q p k)ˣ) : CR q p k) = zP q p k := rfl

include hp in
theorem isPrimitiveRoot_zPu : IsPrimitiveRoot (zPu q p k hp) (p ^ k) :=
  (isPrimitiveRoot_zP hp).isUnit_unit (pow_pos hp.pos k).ne'

include hp hpk in
theorem zPu_mem : zPu q p k hp ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) (CR q p k) :=
  mem_rootsOfUnity_card_units_of_dvd (isPrimitiveRoot_zPu hp).pow_eq_one hpk

variable {gu : (ZMod q)ˣ} (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu)

/-- **The character `χ_R`** of order `p^k` with `χ_R(g) = ζ_P`. -/
noncomputable def chiR (hp : p.Prime) (hpk : p ^ k ∣ q - 1)
    (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu) : MulChar (ZMod q) (CR q p k) :=
  MulChar.ofRootOfUnity (zPu_mem hp hpk) hg

include hp hpk hg in
theorem chiR_gen : chiR hp hpk hg gu = zP q p k := by
  rw [chiR, MulChar.ofRootOfUnity_spec]
  rfl

include hp hpk hg in
theorem orderOf_chiR : orderOf (chiR hp hpk hg) = p ^ k :=
  orderOf_ofRootOfUnity_eq (isPrimitiveRoot_zPu hp) _ hg

include hp hpk hg in
/-- Values of `χ_R` at units are powers of `ζ_P`. -/
theorem chiR_values (a : (ZMod q)ˣ) : ∃ j : ℕ, chiR hp hpk hg a = zP q p k ^ j := by
  obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers.mpr (hg a))
  refine ⟨j, ?_⟩
  rw [← hj, Units.val_pow_eq_pow_val, map_pow, chiR_gen]

include hp in
/-- **The embedding `φ : ℤ[ζ_{p^k}] → R`**, `ζ ↦ ζ_P`. -/
noncomputable def phiR (hp : p.Prime) : CycM (p ^ k) →+* CR q p k :=
  AdjoinRoot.lift (Int.castRingHom (CR q p k)) (zP q p k) (by
    haveI := isDomain_cycM (cr_pos (q := q) (k := k) hp)
    haveI : NeZero ((p ^ k : ℕ) : CR q p k) :=
      ⟨natCast_ne_zero_cycM (cr_pos hp) (pow_pos hp.pos k).ne'⟩
    have hroot : IsRoot (cyclotomic (p ^ k) (CR q p k)) (zP q p k) :=
      isRoot_cyclotomic_iff.mpr (isPrimitiveRoot_zP hp)
    rw [eval₂_eq_eval_map, map_cyclotomic]
    exact hroot)

include hp in
theorem phiR_zetaM : phiR (q := q) hp (zetaM (p ^ k)) = zP q p k := AdjoinRoot.lift_root _

include hp hpk hg in
/-- **The table character becomes `χ_R` under `φ`.** -/
theorem chiT_ringHomComp : (chiT hp hpk hg).ringHomComp (phiR hp) = chiR hp hpk hg := by
  rw [MulChar.eq_iff hg, MulChar.ringHomComp_apply, chiT_gen, phiR_zetaM, chiR_gen]

/-! #### The automorphism `σ` -/

variable {N : ℕ} (hpn : ¬ p ∣ N)

include hp hk hpk in
theorem coprime_pk_q : Nat.Coprime (p ^ k) q :=
  Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hqF.out).mpr fun hpq => by
    subst hpq
    have h1 := Nat.le_of_dvd (by have := hqF.out.two_le; omega) (dvd_pow_self p hk.ne' |>.trans hpk)
    have := hp.two_le
    omega)

/-- The CRT exponent `c ≡ n (mod p^k)`, `c ≡ 1 (mod q)`. -/
noncomputable def cExp (hp : p.Prime) (hk : 0 < k) (hpk : p ^ k ∣ q - 1) (N : ℕ) : ℕ :=
  (Nat.chineseRemainder (coprime_pk_q hp hk hpk) N 1).1

include hp hk hpk in
theorem cExp_modEq_left : cExp hp hk hpk N ≡ N [MOD p ^ k] :=
  (Nat.chineseRemainder (coprime_pk_q hp hk hpk) N 1).2.1

include hp hk hpk in
theorem cExp_modEq_right : cExp hp hk hpk N ≡ 1 [MOD q] :=
  (Nat.chineseRemainder (coprime_pk_q hp hk hpk) N 1).2.2

include hp hk hpk hpn in
theorem cExp_coprime : Nat.Coprime (cExp hp hk hpk N) (q * p ^ k) := by
  refine Nat.Coprime.mul_right ?_ ?_
  · rw [Nat.Coprime, (cExp_modEq_right hp hk hpk).gcd_eq]
    exact Nat.gcd_one_left q
  · rw [Nat.Coprime, (cExp_modEq_left hp hk hpk).gcd_eq]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm

/-- **`σ = σ_c`** on the common ring. -/
noncomputable def sigR (hp : p.Prime) (hk : 0 < k) (hpk : p ^ k ∣ q - 1) (hpn : ¬ p ∣ N) :
    CR q p k →+* CR q p k :=
  sigmaN (cr_pos hp) (cExp_coprime hp hk hpk hpn)

include hp hk hpk hpn in
theorem sigR_zP : sigR hp hk hpk hpn (zP q p k) = zP q p k ^ N := by
  rw [sigR, zP, map_pow, sigmaN_zetaM, ← pow_mul, mul_comm (cExp hp hk hpk N) q, pow_mul]
  exact pow_eq_pow_of_modEq (zP_pow_eq_one hp) (cExp_modEq_left hp hk hpk)

include hp hk hpk hpn in
theorem sigR_zQ : sigR hp hk hpk hpn (zQ q p k) = zQ q p k := by
  rw [sigR, zQ, map_pow, sigmaN_zetaM, ← pow_mul, mul_comm (cExp hp hk hpk N) (p ^ k), pow_mul]
  exact (pow_eq_pow_of_modEq (isPrimitiveRoot_zQ hp).pow_eq_one
    (cExp_modEq_right hp hk hpk)).trans (pow_one _)

include hp hk hpk hpn in
theorem sigR_psiR (a : ZMod q) : sigR hp hk hpk hpn (psiR q p k hp a) = psiR q p k hp a := by
  rw [psiR_apply, map_pow, sigR_zQ]

include hp hk hpk hpn hg in
theorem sigR_chiR (hN0 : N ≠ 0) (a : ZMod q) :
    sigR hp hk hpk hpn (chiR hp hpk hg a) = chiR hp hpk hg a ^ N := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [MulChar.map_zero, map_zero, zero_pow hN0]
  · obtain ⟨j, hj⟩ := chiR_values hp hpk hg (Units.mk0 a ha)
    rw [Units.val_mk0] at hj
    rw [hj, map_pow, sigR_zP, ← pow_mul, ← pow_mul, mul_comm N j]

/-! #### The ideal `(n)` -/

omit hqF in
theorem natCast_mem_spanN : ((N : ℕ) : CR q p k) ∈ Ideal.span {((N : ℕ) : CR q p k)} :=
  Ideal.mem_span_singleton_self _

include hp hk hpk hpn in
theorem sigR_spanN_mem :
    ∀ x ∈ Ideal.span {((N : ℕ) : CR q p k)},
      sigR hp hk hpk hpn x ∈ Ideal.span {((N : ℕ) : CR q p k)} := by
  intro x hx
  rw [Ideal.mem_span_singleton] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨sigR hp hk hpk hpn y, by rw [map_mul, map_natCast]⟩

include hp in
theorem spanN_natCast_imp_dvd :
    ∀ a : ℕ, ((a : ℕ) : CR q p k) ∈ Ideal.span {((N : ℕ) : CR q p k)} → N ∣ a :=
  span_natCast_natCast_imp_dvd (cr_pos hp)

include hp in
theorem natCast_q_ne_zero : ((q : ℕ) : CR q p k) ≠ 0 :=
  natCast_ne_zero_cycM (cr_pos hp) hqF.out.pos.ne'

end CommonRing

section Chains

variable {q p k N : ℕ} [hqF : Fact q.Prime] (hp : p.Prime) (hk : 0 < k) (hpk : p ^ k ∣ q - 1)
  {gu : (ZMod q)ˣ} (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu)

include hp in
omit hk in
/-- The exponent `f₀` of Theorem (7.8): `p^k ∣ e₀ + x·f₀` for `p ∤ x`. -/
theorem exists_f_dvd {x : ℕ} (hx : ¬ p ∣ x) (e₀ : ℕ) : ∃ f₀ : ℕ, p ^ k ∣ e₀ + x * f₀ := by
  have hpk0 : 0 < p ^ k := pow_pos hp.pos k
  refine ⟨(p ^ k - e₀ % p ^ k) * minv p k x, ?_⟩
  have h1 : x * minv p k x ≡ 1 [MOD p ^ k] := minv_spec hp hx
  have h2 : e₀ + x * ((p ^ k - e₀ % p ^ k) * minv p k x)
      ≡ e₀ + (p ^ k - e₀ % p ^ k) * 1 [MOD p ^ k] := by
    rw [mul_left_comm]
    exact Nat.ModEq.add_left _ (Nat.ModEq.mul_left _ h1)
  have h3 : e₀ + (p ^ k - e₀ % p ^ k) * 1 = p ^ k * (e₀ / p ^ k) + p ^ k := by
    have := Nat.div_add_mod e₀ (p ^ k)
    have := Nat.mod_lt e₀ hpk0
    omega
  rw [h3] at h2
  exact (Nat.modEq_zero_iff_dvd).mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr ⟨e₀ / p ^ k + 1, by ring⟩))

include hp in
/-- Transport of the computed congruence into the common ring. -/
theorem spanN_of_dvd_cycM {W : CycM (p ^ k)} {h : ℕ}
    (hd : ((N : ℕ) : CycM (p ^ k)) ∣ W - zetaM (p ^ k) ^ h) :
    phiR (q := q) hp W - zP q p k ^ h ∈ Ideal.span {((N : ℕ) : CR q p k)} := by
  rw [Ideal.mem_span_singleton]
  have := map_dvd (phiR (q := q) hp) hd
  rwa [map_natCast, map_sub, map_pow, phiR_zetaM] at this

include hp hpk hg in
theorem phiR_jacobiSum (a b : ℕ) :
    phiR hp (jacobiSum (chiT hp hpk hg ^ a) (chiT hp hpk hg ^ b))
      = jacobiSum (chiR hp hpk hg ^ a) (chiR hp hpk hg ^ b) := by
  rw [← jacobiSum_ringHomComp, ← MulChar.ringHomComp_pow, ← MulChar.ringHomComp_pow,
    chiT_ringHomComp]

variable (hpn : ¬ p ∣ N)

include hp hk hpk hg hpn in
/-- **The odd-`p` chain**: a passed (i1a)+(i2b) test gives, for every prime `r ∣ n` and every
(6.4)-exponent `m` at the level of Theorem (7.8), `χ_R(r) = ζ_P^(f₀·m)`. -/
theorem chiR_eq_of_odd (hp3 : 2 < p) (hW : ¬ 2 ^ p ≡ 2 [MOD p ^ 2]) (hn1 : 1 < N) (hqn : ¬ q ∣ N)
    {h : ℕ} (h88 : ((N : ℕ) : CycM (p ^ k)) ∣ (∏ x ∈ Mset p k,
      jacobiSum (chiT hp hpk hg ^ minv p k x) (chiT hp hpk hg ^ minv p k x) ^ αc N p k x)
      - zetaM (p ^ k) ^ h) :
    ∃ f₀ : ℕ, ∀ r, r.Prime → r ∣ N → ∀ m : ℕ,
      ((p : ℤ) ^ ((N ^ ((p - 1) * p ^ k) - 1).factorization p)
        ∣ (r : ℤ) ^ (p - 1) - (N : ℤ) ^ ((p - 1) * m)) →
      chiR hp hpk hg r = zP q p k ^ (f₀ * m) := by
  haveI := isDomain_cycM (cr_pos (q := q) (k := k) hp)
  have hN0 : N ≠ 0 := by omega
  have h88' : (∏ x ∈ Mset p k, jacobiSum (chiR hp hpk hg ^ (1 * minv p k x))
      (chiR hp hpk hg ^ (1 * minv p k x)) ^ αc N p k x) - zP q p k ^ h
      ∈ Ideal.span {((N : ℕ) : CR q p k)} := by
    have := spanN_of_dvd_cycM (q := q) hp h88
    rw [map_prod] at this
    simp only [one_mul]
    simpa only [map_pow, phiR_jacobiSum] using this
  have hpa : ¬ p ∣ 1 := hp.not_dvd_one
  have hpab : ¬ p ∣ 1 + 1 := fun hd => by
    have := Nat.le_of_dvd two_pos hd
    omega
  have h79 := theorem_8_5 hp hk hN0 (orderOf_chiR hp hpk hg) (psiR_primitive hp)
    (natCast_q_ne_zero hp) hpa hpa hpab hpn (sigR_chiR hp hk hpk hg hpn hN0)
    (sigR_psiR hp hk hpk hpn) h88'
  have hβ : ¬ p ∣ ∑ y ∈ Mset p k, βc 1 1 p k (minv p k y) * y :=
    lemma_8_12 hp hp3 hk hpa hpa hpab (by simpa using hW)
  have hNS : ¬ p ∣ N * ∑ y ∈ Mset p k, βc 1 1 p k (minv p k y) * y := fun hd => by
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact hpn h
    · exact hβ h
  obtain ⟨f₀, hf⟩ := exists_f_dvd hp hNS h
  refine ⟨f₀, fun r hr hrn m hm => ?_⟩
  exact theorem_7_8 hp hk hn1 hpn hqn (psiR_primitive hp) (isPrimitiveRoot_zP hp)
    (orderOf_chiR hp hpk hg) (chiR_values hp hpk hg) (sigR_chiR hp hk hpk hg hpn hN0)
    (sigR_psiR hp hk hpk hpn) (sigR_zP hp hk hpk hpn) (natCast_mem_spanN)
    (sigR_spanN_mem hp hk hpk hpn) (spanN_natCast_imp_dvd hp)
    (fun x hx => (mem_Mset.mp hx).2) hβ h79 hr hrn hm hf

include hp hk hpk hg hpn in
/-- **(1.3)(i3), Theorem (7.19)**: a passed odd-`p` test whose exponent `h` is not
divisible by `p` is a (6.4) source. -/
theorem sixFour_of_odd (hp3 : 2 < p) (hn1 : 1 < N) (hqn : ¬ q ∣ N)
    {h : ℕ} (hph : ¬ p ∣ h)
    (h88 : ((N : ℕ) : CycM (p ^ k)) ∣ (∏ x ∈ Mset p k,
      jacobiSum (chiT hp hpk hg ^ minv p k x) (chiT hp hpk hg ^ minv p k x) ^ αc N p k x)
      - zetaM (p ^ k) ^ h) :
    ∀ r, r.Prime → r ∣ N → ∀ D, ∃ l, r ^ (p - 1) ≡ (N ^ (p - 1)) ^ l [MOD p ^ D] := by
  haveI := isDomain_cycM (cr_pos (q := q) (k := k) hp)
  have hN0 : N ≠ 0 := by omega
  have h88' : (∏ x ∈ Mset p k, jacobiSum (chiR hp hpk hg ^ (1 * minv p k x))
      (chiR hp hpk hg ^ (1 * minv p k x)) ^ αc N p k x) - zP q p k ^ h
      ∈ Ideal.span {((N : ℕ) : CR q p k)} := by
    have := spanN_of_dvd_cycM (q := q) hp h88
    rw [map_prod] at this
    simp only [one_mul]
    simpa only [map_pow, phiR_jacobiSum] using this
  have hpa : ¬ p ∣ 1 := hp.not_dvd_one
  have hpab : ¬ p ∣ 1 + 1 := fun hd => by
    have := Nat.le_of_dvd two_pos hd
    omega
  have h79 := theorem_8_5 hp hk hN0 (orderOf_chiR hp hpk hg) (psiR_primitive hp)
    (natCast_q_ne_zero hp) hpa hpa hpab hpn (sigR_chiR hp hk hpk hg hpn hN0)
    (sigR_psiR hp hk hpk hpn) h88'
  intro r hr hrn
  exact theorem_7_19 hp hp3 hk hn1 hpn hqn (psiR_primitive hp) (isPrimitiveRoot_zP hp)
    (orderOf_chiR hp hpk hg) (sigR_chiR hp hk hpk hg hpn hN0) (sigR_psiR hp hk hpk hpn)
    (sigR_zP hp hk hpk hpn) (natCast_mem_spanN) (sigR_spanN_mem hp hk hpk hpn)
    (spanN_natCast_imp_dvd hp) (fun x hx => (mem_Mset.mp hx).2) hph h79 hr hrn

/-! #### `p = 2` -/

include hp hpk hg in
/-- For `p = 2`, `χ_R(−1) = ±1` is a power of `ζ_P`. -/
theorem chiR_neg_one_eq_pow (hp2 : p = 2) (hk : 0 < k) :
    ∃ e : ℕ, chiR hp hpk hg (-1) = zP q p k ^ e := by
  haveI := isDomain_cycM (cr_pos (q := q) (k := k) hp)
  rcases mul_self_eq_one_iff.mp (chi_neg_one_sq (chiR hp hpk hg)) with h1 | h1
  · exact ⟨0, by rw [h1, pow_zero]⟩
  · refine ⟨p ^ (k - 1), ?_⟩
    rw [h1]
    have hζ := isPrimitiveRoot_zP (q := q) (k := k) hp
    subst hp2
    have hsq : zP q 2 k ^ 2 ^ (k - 1) * zP q 2 k ^ 2 ^ (k - 1) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hk, hζ.pow_eq_one]
    rcases mul_self_eq_one_iff.mp hsq with h2 | h2
    · exfalso
      exact hζ.pow_ne_one_of_pos_of_lt (pow_pos two_pos _).ne' (Nat.pow_lt_pow_right one_lt_two (by omega)) h2
    · exact h2.symm

/-- The `S = {1}` family of Theorem (7.8) for the `k ≤ 2` cases. -/
theorem prod_singleton_gauss {R : Type _} [CommRing R] (χ : MulChar (ZMod q) R)
    (ψ : AddChar (ZMod q) R) :
    ∏ x ∈ ({1} : Finset ℕ), gaussSum (χ ^ x) ψ ^ (fun _ : ℕ => 1) x = gaussSum χ ψ := by
  simp

theorem not_two_dvd_sum_singleton : ¬ 2 ∣ ∑ x ∈ ({1} : Finset ℕ), (fun _ : ℕ => 1) x * x := by
  simp

include hp hk hpk hg hpn in
/-- **The `p = 2` endgame**: a (7.9) congruence with root `ζ_P^e₀` and a family with odd
coefficient sum gives the character equation. -/
theorem chiR_eq_of_79 (hn1 : 1 < N) (hqn : ¬ q ∣ N)
    {S : Finset ℕ} {ν : ℕ → ℕ} (hSp : ∀ x ∈ S, ¬ p ∣ x) (hβ : ¬ p ∣ ∑ x ∈ S, ν x * x) {e₀ : ℕ}
    (h79 : (∏ x ∈ S, gaussSum (chiR hp hpk hg ^ x) (psiR q p k hp) ^ ν x) ^ N
      - zP q p k ^ e₀ * sigR hp hk hpk hpn (∏ x ∈ S, gaussSum (chiR hp hpk hg ^ x) (psiR q p k hp) ^ ν x)
      ∈ Ideal.span {((N : ℕ) : CR q p k)}) :
    ∃ f₀ : ℕ, ∀ r, r.Prime → r ∣ N → ∀ m : ℕ,
      ((p : ℤ) ^ ((N ^ ((p - 1) * p ^ k) - 1).factorization p)
        ∣ (r : ℤ) ^ (p - 1) - (N : ℤ) ^ ((p - 1) * m)) →
      chiR hp hpk hg r = zP q p k ^ (f₀ * m) := by
  haveI := isDomain_cycM (cr_pos (q := q) (k := k) hp)
  have hN0 : N ≠ 0 := by omega
  have hNS : ¬ p ∣ N * ∑ x ∈ S, ν x * x := fun hd => by
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact hpn h
    · exact hβ h
  obtain ⟨f₀, hf⟩ := exists_f_dvd hp hNS e₀
  refine ⟨f₀, fun r hr hrn m hm => ?_⟩
  exact theorem_7_8 hp hk hn1 hpn hqn (psiR_primitive hp) (isPrimitiveRoot_zP hp)
    (orderOf_chiR hp hpk hg) (chiR_values hp hpk hg) (sigR_chiR hp hk hpk hg hpn hN0)
    (sigR_psiR hp hk hpk hpn) (sigR_zP hp hk hpk hpn) (natCast_mem_spanN)
    (sigR_spanN_mem hp hk hpk hpn) (spanN_natCast_imp_dvd hp) hSp hβ h79 hr hrn hm hf

end Chains

section TwoChains

variable {q N : ℕ} [hqF : Fact q.Prime] {gu : (ZMod q)ˣ} (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu)
  (hn1 : 1 < N) (hodd : N % 2 = 1) (hqn : ¬ q ∣ N)

include hg hn1 hodd hqn

/-- **The `p^k = 2` chain** (Theorem (9.1)). -/
theorem chiR_eq_of_k1 (hpk : 2 ^ 1 ∣ q - 1) {h : ℕ}
    (h92 : ((N : ℕ) : CycM (2 ^ 1)) ∣ ((q : ℕ) : CycM (2 ^ 1)) ^ ((N - 1) / 2) - zetaM (2 ^ 1) ^ h) :
    ∃ f₀ : ℕ, ∀ r, r.Prime → r ∣ N → ∀ m : ℕ,
      ((2 : ℤ) ^ ((N ^ ((2 - 1) * 2 ^ 1) - 1).factorization 2) ∣ (r : ℤ) ^ (2 - 1) - (N : ℤ) ^ ((2 - 1) * m)) →
      chiR Nat.prime_two hpk hg r = zP q 2 1 ^ (f₀ * m) := by
  have hpn : ¬ 2 ∣ N := by omega
  haveI := isDomain_cycM (cr_pos (q := q) (k := 1) Nat.prime_two)
  have h92' : ((q : ℕ) : CR q 2 1) ^ ((N - 1) / 2) - zP q 2 1 ^ h ∈ Ideal.span {((N : ℕ) : CR q 2 1)} := by
    have := spanN_of_dvd_cycM (q := q) Nat.prime_two h92
    rwa [map_pow, map_natCast] at this
  have h79 := theorem_9_1 (psiR_primitive Nat.prime_two) (orderOf_chiR Nat.prime_two hpk hg) hodd
    (sigR_chiR Nat.prime_two one_pos hpk hg hpn (by omega)) (sigR_psiR Nat.prime_two one_pos hpk hpn) h92'
  obtain ⟨e, he⟩ := chiR_neg_one_eq_pow Nat.prime_two hpk hg rfl one_pos
  rw [he, ← pow_mul, ← pow_add, ← prod_singleton_gauss] at h79
  exact chiR_eq_of_79 Nat.prime_two one_pos hpk hg hpn hn1 hqn (fun x hx => by simp at hx; omega)
    not_two_dvd_sum_singleton h79

/-- **The `p^k = 4`, `n ≡ 1 (mod 4)` chain** (Theorem (9.3)). -/
theorem chiR_eq_of_k2_one (hpk : 2 ^ 2 ∣ q - 1) (hn4 : N % 4 = 1) {h : ℕ}
    (h94 : ((N : ℕ) : CycM (2 ^ 2)) ∣
      jacobiSum (chiT Nat.prime_two hpk hg) (chiT Nat.prime_two hpk hg) ^ ((N - 1) / 2)
        * ((q : ℕ) : CycM (2 ^ 2)) ^ ((N - 1) / 4) - zetaM (2 ^ 2) ^ h) :
    ∃ f₀ : ℕ, ∀ r, r.Prime → r ∣ N → ∀ m : ℕ,
      ((2 : ℤ) ^ ((N ^ ((2 - 1) * 2 ^ 2) - 1).factorization 2) ∣ (r : ℤ) ^ (2 - 1) - (N : ℤ) ^ ((2 - 1) * m)) →
      chiR Nat.prime_two hpk hg r = zP q 2 2 ^ (f₀ * m) := by
  have hpn : ¬ 2 ∣ N := by omega
  haveI := isDomain_cycM (cr_pos (q := q) (k := 2) Nat.prime_two)
  have h94' : jacobiSum (chiR Nat.prime_two hpk hg) (chiR Nat.prime_two hpk hg) ^ ((N - 1) / 2)
      * ((q : ℕ) : CR q 2 2) ^ ((N - 1) / 4) - zP q 2 2 ^ h ∈ Ideal.span {((N : ℕ) : CR q 2 2)} := by
    have := spanN_of_dvd_cycM (q := q) Nat.prime_two h94
    have hJ := phiR_jacobiSum Nat.prime_two hpk hg 1 1
    simp only [pow_one] at hJ
    rwa [map_mul, map_pow, map_pow, map_natCast, hJ] at this
  have h79 := theorem_9_3 (psiR_primitive Nat.prime_two) (orderOf_chiR Nat.prime_two hpk hg) hn4
    (sigR_chiR Nat.prime_two two_pos hpk hg hpn (by omega)) (sigR_psiR Nat.prime_two two_pos hpk hpn) h94'
  rw [← prod_singleton_gauss] at h79
  exact chiR_eq_of_79 Nat.prime_two two_pos hpk hg hpn hn1 hqn (fun x hx => by simp at hx; omega)
    not_two_dvd_sum_singleton h79

/-- **The `p^k = 4`, `n ≡ 3 (mod 4)` chain** (Theorem (9.5)). -/
theorem chiR_eq_of_k2_three (hpk : 2 ^ 2 ∣ q - 1) (hn4 : N % 4 = 3) {h : ℕ}
    (h96 : ((N : ℕ) : CycM (2 ^ 2)) ∣
      jacobiSum (chiT Nat.prime_two hpk hg) (chiT Nat.prime_two hpk hg) ^ ((N + 1) / 2)
        * ((q : ℕ) : CycM (2 ^ 2)) ^ ((N - 3) / 4) - zetaM (2 ^ 2) ^ h) :
    ∃ f₀ : ℕ, ∀ r, r.Prime → r ∣ N → ∀ m : ℕ,
      ((2 : ℤ) ^ ((N ^ ((2 - 1) * 2 ^ 2) - 1).factorization 2) ∣ (r : ℤ) ^ (2 - 1) - (N : ℤ) ^ ((2 - 1) * m)) →
      chiR Nat.prime_two hpk hg r = zP q 2 2 ^ (f₀ * m) := by
  have hpn : ¬ 2 ∣ N := by omega
  haveI := isDomain_cycM (cr_pos (q := q) (k := 2) Nat.prime_two)
  have h96' : jacobiSum (chiR Nat.prime_two hpk hg) (chiR Nat.prime_two hpk hg) ^ ((N + 1) / 2)
      * ((q : ℕ) : CR q 2 2) ^ ((N - 3) / 4) - zP q 2 2 ^ h ∈ Ideal.span {((N : ℕ) : CR q 2 2)} := by
    have := spanN_of_dvd_cycM (q := q) Nat.prime_two h96
    have hJ := phiR_jacobiSum Nat.prime_two hpk hg 1 1
    simp only [pow_one] at hJ
    rwa [map_mul, map_pow, map_pow, map_natCast, hJ] at this
  have h79 := theorem_9_5 (psiR_primitive Nat.prime_two) (orderOf_chiR Nat.prime_two hpk hg) hn4
    (natCast_q_ne_zero Nat.prime_two) (sigR_chiR Nat.prime_two two_pos hpk hg hpn (by omega))
    (sigR_psiR Nat.prime_two two_pos hpk hpn) h96'
  obtain ⟨e, he⟩ := chiR_neg_one_eq_pow Nat.prime_two hpk hg rfl two_pos
  rw [he, ← pow_add, ← prod_singleton_gauss] at h79
  exact chiR_eq_of_79 Nat.prime_two two_pos hpk hg hpn hn1 hqn (fun x hx => by simp at hx; omega)
    not_two_dvd_sum_singleton h79

variable {k : ℕ} (hk3 : 3 ≤ k) (hpk : 2 ^ k ∣ q - 1)
include hk3 hpk

omit hn1 hodd hqn hk3 in
/-- The (9.11) product transported into the common ring. -/
theorem phiR_prod_M2 (N : ℕ) :
    phiR (q := q) Nat.prime_two (∏ x ∈ M2set k,
        (jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x) (chiT Nat.prime_two hpk hg ^ minv 2 k x)
          * jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x)
              (chiT Nat.prime_two hpk hg ^ (2 * minv 2 k x))) ^ αc N 2 k x)
      = ∏ x ∈ M2set k,
        (jacobiSum (chiR Nat.prime_two hpk hg ^ minv 2 k x) (chiR Nat.prime_two hpk hg ^ minv 2 k x)
          * jacobiSum (chiR Nat.prime_two hpk hg ^ minv 2 k x)
              (chiR Nat.prime_two hpk hg ^ (2 * minv 2 k x))) ^ αc N 2 k x := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [map_pow, map_mul, phiR_jacobiSum, phiR_jacobiSum]

/-- **The `p = 2`, `k ≥ 3`, `n ≡ 1, 3 (mod 8)` chain** (Theorem (9.10)). -/
theorem chiR_eq_of_k3_low (hn8 : N % 8 = 1 ∨ N % 8 = 3) {h : ℕ}
    (h911 : ((N : ℕ) : CycM (2 ^ k)) ∣ (∏ x ∈ M2set k,
        (jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x) (chiT Nat.prime_two hpk hg ^ minv 2 k x)
          * jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x)
              (chiT Nat.prime_two hpk hg ^ (2 * minv 2 k x))) ^ αc N 2 k x)
      - zetaM (2 ^ k) ^ h) :
    ∃ f₀ : ℕ, ∀ r, r.Prime → r ∣ N → ∀ m : ℕ,
      ((2 : ℤ) ^ ((N ^ ((2 - 1) * 2 ^ k) - 1).factorization 2) ∣ (r : ℤ) ^ (2 - 1) - (N : ℤ) ^ ((2 - 1) * m)) →
      chiR Nat.prime_two hpk hg r = zP q 2 k ^ (f₀ * m) := by
  have hpn : ¬ 2 ∣ N := by omega
  have hk : 0 < k := by omega
  haveI := isDomain_cycM (cr_pos (q := q) (k := k) Nat.prime_two)
  have h911' := spanN_of_dvd_cycM (q := q) Nat.prime_two h911
  rw [phiR_prod_M2 hg hpk] at h911'
  have h79 := theorem_9_10 hk3 (by omega) (orderOf_chiR Nat.prime_two hpk hg) (psiR_primitive Nat.prime_two)
    (natCast_q_ne_zero Nat.prime_two) hn8 (sigR_chiR Nat.prime_two hk hpk hg hpn (by omega))
    (sigR_psiR Nat.prime_two hk hpk hpn) h911'
  exact chiR_eq_of_79 Nat.prime_two hk hpk hg hpn hn1 hqn (fun x hx => M2_odd hx) (eq_9_14 hk3) h79

/-- **The `p = 2`, `k ≥ 3`, `n ≡ 5, 7 (mod 8)` chain** (Theorem (9.19)). -/
theorem chiR_eq_of_k3_high (hn8 : N % 8 = 5 ∨ N % 8 = 7) {h : ℕ}
    (h920 : ((N : ℕ) : CycM (2 ^ k)) ∣ (∏ x ∈ M2set k,
        (jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x) (chiT Nat.prime_two hpk hg ^ minv 2 k x)
          * jacobiSum (chiT Nat.prime_two hpk hg ^ minv 2 k x)
              (chiT Nat.prime_two hpk hg ^ (2 * minv 2 k x))) ^ αc N 2 k x)
        * jacobiSum (chiT Nat.prime_two hpk hg ^ 2 ^ (k - 3))
            ((chiT Nat.prime_two hpk hg ^ 2 ^ (k - 3)) ^ 3) ^ 2
      - zetaM (2 ^ k) ^ h) :
    ∃ f₀ : ℕ, ∀ r, r.Prime → r ∣ N → ∀ m : ℕ,
      ((2 : ℤ) ^ ((N ^ ((2 - 1) * 2 ^ k) - 1).factorization 2) ∣ (r : ℤ) ^ (2 - 1) - (N : ℤ) ^ ((2 - 1) * m)) →
      chiR Nat.prime_two hpk hg r = zP q 2 k ^ (f₀ * m) := by
  have hpn : ¬ 2 ∣ N := by omega
  have hk : 0 < k := by omega
  haveI := isDomain_cycM (cr_pos (q := q) (k := k) Nat.prime_two)
  have h920' := spanN_of_dvd_cycM (q := q) Nat.prime_two h920
  rw [map_mul, phiR_prod_M2 hg hpk, map_pow, ← pow_mul, phiR_jacobiSum, pow_mul] at h920'
  have h79 := theorem_9_19 hk3 (orderOf_chiR Nat.prime_two hpk hg) (psiR_primitive Nat.prime_two)
    (natCast_q_ne_zero Nat.prime_two) hn8 (sigR_chiR Nat.prime_two hk hpk hg hpn (by omega))
    (sigR_psiR Nat.prime_two hk hpk hpn) h920'
  obtain ⟨e, he⟩ := chiR_neg_one_eq_pow Nat.prime_two hpk hg rfl hk
  rw [he, ← pow_add] at h79
  exact chiR_eq_of_79 Nat.prime_two hk hpk hg hpn hn1 hqn (fun x hx => M2_odd hx) (eq_9_14 hk3) h79

end TwoChains

end APRCL

end Azurite
