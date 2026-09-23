/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Cohen–Lenstra §10, Method (10.2): the ideal `𝔪 = (n, h(ζ))` of
  `ℤ[ζ_m]`.**

  §10 constructs, for probable-prime `n`, ideals `𝔪` of
  `ℤ[ζ_{p^k}]` satisfying the paper's (10.1) (= our (7.7)):

    `𝔪 ∩ ℤ = nℤ`,   `σ_n[𝔪] = 𝔪`,

  as large as possible — the tests (8.8)/(9.x) are then computations
  in the small quotient `ℤ[ζ_{p^k}]/𝔪`.  Method (10.2): find a monic
  degree-`f` polynomial `h ∈ ℤ[T]` (`f` the order of `n` mod `p^k`)
  with `(h mod n) ∣ (Φ_{p^k} mod n)`, and set `𝔪 = (n, h(ζ))`.

  We formalize the method's claims over the symbolic model
  `CycM m = ℤ[x]/(Φ_m)` of the Crandall–Pomerance arc (at general
  `m`; the paper's `Σ_{i<p} T^{i·p^(k−1)}` *is* `Φ_{p^k}`):

  * `sigmaN` — the ring endomorphism `σ_n` with `σ_n(ζ) = ζ^n`
    (well-defined since `ζ^n` is again a primitive root for
    `gcd(n, m) = 1`); `map_sigmaN_eq_of_mem` upgrades any
    `σ_n`-stability inclusion to the (10.1)-equality via the finite
    order of `σ_n` (Euler: `σ_n^(φ(m)) = id`).
  * `mIdeal_natCast_imp_dvd` — `𝔪 ∩ ℤ = nℤ`: an integer in `𝔪`
    lifts to `a = U·n + V·h + W·Φ_m` in `ℤ[X]`; mod `n` the monic
    degree-`≥ 1` polynomial `(h mod n)` divides the constant
    `(a mod n)`, forcing it to vanish.
  * `mIdeal_sigmaN_mem`/`mIdeal_sigmaN_map_eq` — the σ-stability of
    `𝔪` follows from the paper's *checkable* condition "`ζ̄^n` is a
    zero of `(h mod n)`", rendered as `h(ζ^n) ∈ 𝔪`.
  * `sigmaN_sub_pow_mem`/`map_sigmaN_eq_of_prime` — the paper's
    remark: for *prime* `n`, `σ_n(α) ≡ α^n mod nℤ[ζ_m]` (the (1.3)
    Frobenius congruence, via `p`-th-power freshman's dream in
    `(ℤ/n)[X]`), so *every* ideal containing `n` is σ-stable.
  * `mIdeal_eq_span_natCast` — the degenerate case: if
    `deg h = φ(m)` then `(h mod n) = (Φ_m mod n)` and the method
    yields `𝔪 = nℤ[ζ_m]` (that this is then the *only* ideal
    satisfying (10.1) awaits (10.5)).

  The paper finds `h` by Berlekamp's algorithm; in our architecture
  `h`-finding is generator-side and *any* factoring method serves —
  in particular the verified Cantor–Zassenhaus rail
  (`AzPolynomial.EqualDegreeSplitting`/`Factorization`, GG Alg 14.8/
  14.13): for prime `n` the polynomial `Φ_{p^k} mod n` is squarefree
  with all irreducible factors of degree exactly `f`, the pure
  equal-degree situation.  Soundness never depends on `h`'s
  provenance: the checker verifies `Monic h`, `deg h`,
  `(h mod n) ∣ (Φ mod n)` and the `ζ̄^n`-condition, which are the
  hypotheses above.  The existence of `h` for prime `n` (with
  `(h mod n)` irreducible) is generator-side completeness, deferred
  to the algorithm assembly.
-/
import Azurite.CrandallPomerance.Chapter4.CycM
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Finite.Basic

namespace Azurite

namespace CL

open Polynomial Azurite.CP

variable {m n : ℕ} {h : Polynomial ℤ}

/-! ### The endomorphism `σ_n` of `ℤ[ζ_m]` -/

/-- **The paper's `σ_n`**: the ring endomorphism of `ℤ[ζ_m]` with
`σ_n(ζ_m) = ζ_m^n`, for `gcd(n, m) = 1`. -/
noncomputable def sigmaN (hm : 0 < m) (hco : Nat.Coprime n m) :
    CycM m →+* CycM m :=
  AdjoinRoot.lift (Int.castRingHom (CycM m)) (zetaM m ^ n) <| by
    have := isDomain_cycM hm
    have : NeZero ((m : ℕ) : CycM m) := ⟨natCast_ne_zero_cycM hm hm.ne'⟩
    have hprim : IsPrimitiveRoot (zetaM m ^ n) m :=
      (isPrimitiveRoot_zetaM hm).pow_of_coprime n hco
    have hroot : IsRoot (cyclotomic m (CycM m)) (zetaM m ^ n) :=
      isRoot_cyclotomic_iff.mpr hprim
    rw [eval₂_eq_eval_map, map_cyclotomic]
    exact hroot

theorem sigmaN_zetaM (hm : 0 < m) (hco : Nat.Coprime n m) :
    sigmaN hm hco (zetaM m) = zetaM m ^ n :=
  AdjoinRoot.lift_root _

theorem sigmaN_aeval (hm : 0 < m) (hco : Nat.Coprime n m)
    (x : CycM m) (U : Polynomial ℤ) :
    sigmaN hm hco (aeval x U) = aeval (sigmaN hm hco x) U :=
  (Polynomial.aeval_algHom_apply (sigmaN hm hco).toIntAlgHom x U).symm

/-- Every element of the model is a polynomial in `ζ_m`. -/
theorem exists_aeval_rep (α : CycM m) :
    ∃ U : Polynomial ℤ, α = aeval (zetaM m) U := by
  obtain ⟨U, rfl⟩ := AdjoinRoot.mk_surjective α
  exact ⟨U, (AdjoinRoot.aeval_eq U).symm⟩

theorem sigmaN_iterate_zetaM (hm : 0 < m) (hco : Nat.Coprime n m)
    (i : ℕ) :
    (⇑(sigmaN hm hco))^[i] (zetaM m) = zetaM m ^ n ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, map_pow, sigmaN_zetaM,
      ← pow_mul]
    congr 1
    rw [pow_succ]
    ring

/-- **The finite-order upgrade**: a `σ_n`-stability *inclusion* for
an ideal of `ℤ[ζ_m]` is automatically the (10.1)-*equality*, because
`σ_n^(φ(m)) = id` (Euler). -/
theorem map_sigmaN_eq_of_mem (hm : 0 < m) (hco : Nat.Coprime n m)
    (I : Ideal (CycM m))
    (hstep : ∀ x ∈ I, sigmaN hm hco x ∈ I) :
    Ideal.map (sigmaN hm hco) I = I := by
  set σ := sigmaN hm hco with hσ
  have hiter : ∀ i, ∀ x ∈ I, (⇑σ)^[i] x ∈ I := by
    intro i
    induction i with
    | zero => intro x hx; simpa using hx
    | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hstep _ (ih x hx)
  have hcomm : ∀ (i : ℕ) (U : Polynomial ℤ),
      (⇑σ)^[i] (aeval (zetaM m) U) = aeval ((⇑σ)^[i] (zetaM m)) U := by
    intro i U
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih]
      exact sigmaN_aeval hm hco _ U
  have hid : ∀ α : CycM m, (⇑σ)^[m.totient] α = α := by
    intro α
    obtain ⟨U, rfl⟩ := exists_aeval_rep α
    rw [hcomm, sigmaN_iterate_zetaM hm hco]
    have heuler : n ^ m.totient ≡ 1 [MOD m] := Nat.ModEq.pow_totient hco
    have hζ := isPrimitiveRoot_zetaM hm
    have hcong : ∀ a b : ℕ, a ≡ b [MOD m] → zetaM m ^ a = zetaM m ^ b := by
      intro a b hab
      have hred : ∀ c : ℕ, zetaM m ^ c = zetaM m ^ (c % m) := by
        intro c
        conv_lhs => rw [← Nat.div_add_mod c m]
        rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
      rw [hred a, hred b, hab]
    have hζeq : zetaM m ^ n ^ m.totient = zetaM m := by
      have := hcong (n ^ m.totient) 1 heuler
      rwa [pow_one] at this
    rw [hζeq]
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx =>
    hstep x hx) ?_
  intro α hα
  have he : 0 < m.totient := Nat.totient_pos.mpr hm
  have hβ : (⇑σ)^[m.totient - 1] α ∈ I := hiter _ α hα
  have hσβ : σ ((⇑σ)^[m.totient - 1] α) = α := by
    calc σ ((⇑σ)^[m.totient - 1] α)
        = (⇑σ)^[m.totient - 1 + 1] α :=
          (Function.iterate_succ_apply' (⇑σ) _ _).symm
      _ = (⇑σ)^[m.totient] α := by
          rw [show m.totient - 1 + 1 = m.totient from by omega]
      _ = α := hid α
  rw [← hσβ]
  exact Ideal.mem_map_of_mem σ hβ

/-! ### The ideal `𝔪 = (n, h(ζ))` and the (10.1)-conditions -/

/-- **The paper's (10.2)-ideal**: `𝔪 = (n, h(ζ_m)) ⊆ ℤ[ζ_m]`. -/
noncomputable def mIdeal (m n : ℕ) (h : Polynomial ℤ) : Ideal (CycM m) :=
  Ideal.span {(n : CycM m), aeval (zetaM m) h}

theorem natCast_mem_mIdeal (m n : ℕ) (h : Polynomial ℤ) :
    ((n : ℕ) : CycM m) ∈ mIdeal m n h :=
  Ideal.subset_span (by simp)

theorem aeval_mem_mIdeal (m n : ℕ) (h : Polynomial ℤ) :
    aeval (zetaM m) h ∈ mIdeal m n h :=
  Ideal.subset_span (by simp)

/-- **`𝔪 ∩ ℤ = nℤ`** (the first (10.1)-condition, in the
`hIZ`-shape of Theorem (7.8)): an integer lying in `𝔪` is divisible
by `n`.  Needs only that `(h mod n)` is monic of positive degree and
divides `(Φ_m mod n)`. -/
theorem mIdeal_natCast_imp_dvd (hn : 1 < n)
    (hmonic : h.Monic) (hdeg : 0 < h.natDegree)
    (hdvd : h.map (Int.castRingHom (ZMod n))
      ∣ (cyclotomic m ℤ).map (Int.castRingHom (ZMod n))) :
    ∀ a : ℕ, ((a : ℕ) : CycM m) ∈ mIdeal m n h → n ∣ a := by
  have : Fact (1 < n) := ⟨hn⟩
  intro a ha
  rw [mIdeal, Ideal.mem_span_pair] at ha
  obtain ⟨u, v, huv⟩ := ha
  obtain ⟨U, rfl⟩ := AdjoinRoot.mk_surjective u
  obtain ⟨V, rfl⟩ := AdjoinRoot.mk_surjective v
  -- lift to a polynomial identity in `ℤ[X]`
  have hmkn : ((n : ℕ) : CycM m)
      = AdjoinRoot.mk (cyclotomic m ℤ) ((n : ℕ) : Polynomial ℤ) :=
    (map_natCast (AdjoinRoot.mk (cyclotomic m ℤ)) n).symm
  have hmka : ((a : ℕ) : CycM m)
      = AdjoinRoot.mk (cyclotomic m ℤ) ((a : ℕ) : Polynomial ℤ) :=
    (map_natCast (AdjoinRoot.mk (cyclotomic m ℤ)) a).symm
  have hmkh : aeval (zetaM m) h = AdjoinRoot.mk (cyclotomic m ℤ) h :=
    AdjoinRoot.aeval_eq h
  rw [hmkn, hmka, hmkh, ← map_mul, ← map_mul, ← map_add] at huv
  have hz : AdjoinRoot.mk (cyclotomic m ℤ)
      (U * ((n : ℕ) : Polynomial ℤ) + V * h - ((a : ℕ) : Polynomial ℤ))
      = 0 := by
    rw [map_sub, huv, sub_self]
  rw [AdjoinRoot.mk_eq_zero] at hz
  obtain ⟨W, hW⟩ := hz
  -- reduce mod `n`
  have hmap := congrArg (Polynomial.map (Int.castRingHom (ZMod n))) hW
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_natCast] at hmap
  have hn0 : ((n : ℕ) : Polynomial (ZMod n)) = 0 := by
    rw [← Polynomial.C_eq_natCast, ZMod.natCast_self, Polynomial.C_0]
  rw [hn0, mul_zero, zero_add] at hmap
  -- `(h mod n)` divides the constant `(a mod n)`
  have hdvda : h.map (Int.castRingHom (ZMod n))
      ∣ ((a : ℕ) : Polynomial (ZMod n)) := by
    have h1 : ((a : ℕ) : Polynomial (ZMod n))
        = V.map (Int.castRingHom (ZMod n))
            * h.map (Int.castRingHom (ZMod n))
          - (cyclotomic m ℤ).map (Int.castRingHom (ZMod n))
            * W.map (Int.castRingHom (ZMod n)) := by
      rw [← hmap]
      ring
    rw [h1]
    exact dvd_sub (dvd_mul_left _ _) (hdvd.mul_right _)
  by_contra hnd
  have ha0 : ((a : ℕ) : ZMod n) ≠ 0 := fun h0 =>
    hnd ((ZMod.natCast_eq_zero_iff a n).mp h0)
  have hane : ((a : ℕ) : Polynomial (ZMod n)) ≠ 0 := by
    rw [← Polynomial.C_eq_natCast]
    exact fun h0 => ha0 (by simpa using congrArg (fun P => P.coeff 0) h0)
  -- monic-divisor degree count (no `NoZeroDivisors` available mod `n`)
  have hmonich : (h.map (Int.castRingHom (ZMod n))).Monic := hmonic.map _
  obtain ⟨c, hc⟩ := hdvda
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact hane hc
  have hdeg1 : ((a : ℕ) : Polynomial (ZMod n)).natDegree
      = (h.map (Int.castRingHom (ZMod n))).natDegree + c.natDegree := by
    rw [hc, hmonich.natDegree_mul' hc0]
  have hdegmap : (h.map (Int.castRingHom (ZMod n))).natDegree
      = h.natDegree := hmonic.natDegree_map _
  have hdegC : ((a : ℕ) : Polynomial (ZMod n)).natDegree = 0 := by
    rw [← Polynomial.C_eq_natCast, Polynomial.natDegree_C]
  omega

/-- **σ-stability of `𝔪` from the checkable condition** "`ζ̄^n` is a
zero of `(h mod n)`", rendered as `h(ζ^n) ∈ 𝔪` — the inclusion
step, in the `hσI`-shape of Theorem (7.8). -/
theorem mIdeal_sigmaN_mem (hm : 0 < m) (hco : Nat.Coprime n m)
    (hcheck : aeval (zetaM m ^ n) h ∈ mIdeal m n h) :
    ∀ x ∈ mIdeal m n h, sigmaN hm hco x ∈ mIdeal m n h := by
  intro x hx
  rw [mIdeal, Ideal.mem_span_pair] at hx
  obtain ⟨u, v, huv⟩ := hx
  rw [← huv, map_add, map_mul, map_mul, map_natCast]
  have hσh : sigmaN hm hco (aeval (zetaM m) h)
      = aeval (zetaM m ^ n) h := by
    rw [sigmaN_aeval, sigmaN_zetaM]
  rw [hσh]
  exact Ideal.add_mem _
    (Ideal.mul_mem_left _ _ (natCast_mem_mIdeal m n h))
    (Ideal.mul_mem_left _ _ hcheck)

/-- **The second (10.1)-condition**: `σ_n[𝔪] = 𝔪`, from the
checkable `ζ̄^n`-condition. -/
theorem mIdeal_sigmaN_map_eq (hm : 0 < m) (hco : Nat.Coprime n m)
    (hcheck : aeval (zetaM m ^ n) h ∈ mIdeal m n h) :
    Ideal.map (sigmaN hm hco) (mIdeal m n h) = mIdeal m n h :=
  map_sigmaN_eq_of_mem hm hco _ (mIdeal_sigmaN_mem hm hco hcheck)

/-! ### The prime-`n` remark: Frobenius makes every ideal σ-stable -/

/-- **The (1.3)-Frobenius congruence in the model**: for prime `n`
(coprime to `m`), `σ_n(α) ≡ α^n mod nℤ[ζ_m]` — freshman's dream in
`(ℤ/n)[X]` pulled back along `aeval ζ`. -/
theorem sigmaN_sub_pow_mem (hm : 0 < m) (hn : n.Prime)
    (hco : Nat.Coprime n m) (α : CycM m) :
    sigmaN hm hco α - α ^ n ∈ Ideal.span {((n : ℕ) : CycM m)} := by
  have : Fact n.Prime := ⟨hn⟩
  obtain ⟨U, rfl⟩ := exists_aeval_rep α
  -- polynomial level: `C n ∣ expand n U − U^n`
  have hkey : Polynomial.C ((n : ℕ) : ℤ)
      ∣ (Polynomial.expand ℤ n U - U ^ n) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hmap : (Polynomial.expand ℤ n U - U ^ n).map
        (Int.castRingHom (ZMod n)) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_expand, Polynomial.map_pow]
      have h1 : Polynomial.expand (ZMod n) n
          (U.map (Int.castRingHom (ZMod n)))
          = (U.map (Int.castRingHom (ZMod n))) ^ n := by
        have h2 := Polynomial.map_frobenius_expand (R := ZMod n)
          (p := n) (U.map (Int.castRingHom (ZMod n)))
        rwa [ZMod.frobenius_zmod, Polynomial.map_id] at h2
      rw [h1, sub_self]
    have hci := congrArg (fun P => Polynomial.coeff P i) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hci
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hci
  obtain ⟨D, hD⟩ := hkey
  have hα : sigmaN hm hco (aeval (zetaM m) U) - (aeval (zetaM m) U) ^ n
      = ((n : ℕ) : CycM m) * aeval (zetaM m) D := by
    rw [sigmaN_aeval, sigmaN_zetaM]
    have hexp : aeval (zetaM m ^ n) U
        = aeval (zetaM m) (Polynomial.expand ℤ n U) :=
      (Polynomial.expand_aeval n U (zetaM m)).symm
    rw [hexp, ← map_pow, ← map_sub, hD, map_mul, aeval_C, map_natCast]
  rw [hα]
  exact Ideal.mem_span_singleton.mpr ⟨aeval (zetaM m) D, rfl⟩

/-- **The paper's remark**: for *prime* `n`, `σ_n[𝔪] = 𝔪` holds for
*every* ideal `𝔪` of `ℤ[ζ_m]` containing `n`. -/
theorem map_sigmaN_eq_of_prime (hm : 0 < m) (hn : n.Prime)
    (hco : Nat.Coprime n m) (I : Ideal (CycM m))
    (hnI : ((n : ℕ) : CycM m) ∈ I) :
    Ideal.map (sigmaN hm hco) I = I := by
  refine map_sigmaN_eq_of_mem hm hco I fun x hx => ?_
  have hmem := sigmaN_sub_pow_mem hm hn hco x
  have hspan : Ideal.span {((n : ℕ) : CycM m)} ≤ I :=
    (Ideal.span_singleton_le_iff_mem I).mpr hnI
  have h1 : sigmaN hm hco x - x ^ n ∈ I := hspan hmem
  have h2 : x ^ n ∈ I := Ideal.pow_mem_of_mem I hx n hn.pos
  have h3 := Ideal.add_mem I h1 h2
  simpa using h3

/-! ### The degenerate case `deg h = φ(m)` -/

/-- **The paper's closing observation**: if `deg h = φ(m)` (the
paper's `f = (p−1)p^(k−1)` case) then `(h mod n) = (Φ_m mod n)` and
the method degenerates to `𝔪 = nℤ[ζ_m]`.  (That this is then the
*only* ideal satisfying (10.1) awaits (10.5).) -/
theorem mIdeal_eq_span_natCast (hn : 1 < n) (hmonic : h.Monic)
    (hdvd : h.map (Int.castRingHom (ZMod n))
      ∣ (cyclotomic m ℤ).map (Int.castRingHom (ZMod n)))
    (hdeg : h.natDegree = m.totient) :
    mIdeal m n h = Ideal.span {((n : ℕ) : CycM m)} := by
  have : Fact (1 < n) := ⟨hn⟩
  have : NeZero n := ⟨by omega⟩
  -- `(h mod n) = (Φ_m mod n)`: monic divisor of equal degree
  have hmonich : (h.map (Int.castRingHom (ZMod n))).Monic :=
    hmonic.map _
  have hmonicΦ : ((cyclotomic m ℤ).map (Int.castRingHom (ZMod n))).Monic :=
    (cyclotomic.monic m ℤ).map _
  have hdegh : (h.map (Int.castRingHom (ZMod n))).natDegree = m.totient := by
    rw [hmonic.natDegree_map, hdeg]
  have hdegΦ : ((cyclotomic m ℤ).map (Int.castRingHom (ZMod n))).natDegree
      = m.totient := by
    rw [(cyclotomic.monic m ℤ).natDegree_map, natDegree_cyclotomic]
  have heq : h.map (Int.castRingHom (ZMod n))
      = (cyclotomic m ℤ).map (Int.castRingHom (ZMod n)) := by
    obtain ⟨c, hc⟩ := hdvd
    have hpq : ((h.map (Int.castRingHom (ZMod n))) * c).Monic := by
      rw [← hc]
      exact hmonicΦ
    have hcm : c.Monic := hmonich.of_mul_monic_left hpq
    have hdegc : c.natDegree = 0 := by
      have h1 : ((h.map (Int.castRingHom (ZMod n))) * c).natDegree
          = m.totient := by
        rw [← hc, hdegΦ]
      rw [hmonich.natDegree_mul' hcm.ne_zero, hdegh] at h1
      omega
    have hc1 : c = 1 := by
      have h2 := Polynomial.eq_C_of_natDegree_eq_zero hdegc
      have h3 : c.coeff 0 = 1 := by
        have := hcm
        rw [Polynomial.Monic, Polynomial.leadingCoeff, hdegc] at this
        exact this
      rw [h2, h3, Polynomial.C_1]
    rw [hc, hc1, mul_one]
  -- so `C n ∣ h − Φ_m` in `ℤ[X]`
  have hkey : Polynomial.C ((n : ℕ) : ℤ) ∣ (h - cyclotomic m ℤ) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hmap0 : (h - cyclotomic m ℤ).map (Int.castRingHom (ZMod n))
        = 0 := by
      rw [Polynomial.map_sub, heq, sub_self]
    have hci := congrArg (fun P => Polynomial.coeff P i) hmap0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hci
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hci
  obtain ⟨D, hD⟩ := hkey
  have hhval : aeval (zetaM m) h
      = ((n : ℕ) : CycM m) * aeval (zetaM m) D := by
    have h1 : h = cyclotomic m ℤ + Polynomial.C ((n : ℕ) : ℤ) * D := by
      rw [← hD]
      ring
    have hΦ0 : aeval (zetaM m) (cyclotomic m ℤ) = 0 := by
      rw [show zetaM m = AdjoinRoot.root (cyclotomic m ℤ) from rfl,
        AdjoinRoot.aeval_eq]
      exact AdjoinRoot.mk_self
    rw [h1, map_add, map_mul, aeval_C, hΦ0, zero_add, map_natCast]
  rw [mIdeal, hhval]
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    rintro x hx
    rcases hx with rfl | hx
    · exact Ideal.subset_span rfl
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Ideal.subset_span (by simp)

end CL

end Azurite
