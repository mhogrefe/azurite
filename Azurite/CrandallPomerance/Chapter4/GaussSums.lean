/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Crandall–Pomerance §4.4, opening: Gauss sums for Dirichlet
  characters — the setup for the Gauss sums primality test, treated
  SYMBOLICALLY, per the book's own advice ("It is very important in
  actual ring computations to treat ζ_p, ζ_q symbolically … one may
  avoid complex-floating-point methods").

  As with the Lucas sequences (§4.2, where Binet's formulas hold for
  the roots of the quadratic in ANY commutative ring), everything
  here is stated over an arbitrary commutative ring `R` carrying the
  needed roots of unity, rather than over `ℂ`; the book's concrete
  `ζ_n = e^(2πi/n)` is one instance.

  Mathlib already provides the key objects:
  * the book's character construction "χ(g^k) = ζ^k" from a
    primitive root `g` mod `q` and a `(q−1)`-th root of unity `ζ` is
    verbatim `MulChar.ofRootOfUnity` (with `ofRootOfUnity_spec`);
    Dirichlet characters mod `q` are `MulChar (ZMod q) R`;
  * the Gauss sum `τ(χ) = ∑ χ(m) ζ_q^m` is `gaussSum χ ψ` with
    `ψ = AddChar.zmodChar q hζq` the additive character `m ↦ ζ_q^m`;
  * over `ℂ`, conjugation is character inversion
    (`MulChar.star_eq_inv`), the book's `α ↦ ᾱ` remark.

  What this file adds, following the passage:
  * `orderOf_ofRootOfUnity` — the order of the constructed character
    equals the order of `ζ` (Mathlib-generic: any finite monoid with
    cyclic unit group).  Specializing to a primitive `p`-th root of
    unity for a prime `p ∣ q − 1` gives the book's order-`p`
    character `χ_{p,q}` (`orderOf_ofRootOfUnity_eq_orderOf`-style
    corollaries below), and membership of such `ζ` in the required
    root-of-unity group (`mem_rootsOfUnity_card_units_of_dvd`).
  * `orderOf_ofRootOfUnity_dvd` — "as a character mod q, the order
    of χ is a divisor of q − 1".
  * `gaussSum_eq_sum_range` — the book's displayed reindexing
    `τ(χ) = ∑_{k} χ(g)^k ζ_q^(g^k)`: the Gauss sum as a sum over
    powers of the primitive root.  (We index `k = 0, …, q−2`; the
    book's `k = 1, …, q−1` traverses the same units, since
    `g^(q−1) = g^0`.)

  The ring `ℤ[ζ_p, ζ_q]` with its unique representation
  `∑ a_{j,k} ζ_p^j ζ_q^k` (`0 ≤ j ≤ p−2`, `0 ≤ k ≤ q−2`) and the
  coefficientwise congruence mod `n` will be realized COMPUTABLY,
  when the test itself arrives, as the symbolic tower the book
  describes: `AzPolyMod`-arithmetic modulo
  `x^(p−1) + … + 1` and `y^(q−1) + … + 1` over `AzZMod n` — the
  polynomial normal form of the tower IS the book's unique
  representation.
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Data.ZMod.Basic

namespace Azurite

namespace CP

open MulChar Finset

section OrderOf

variable {M : Type _} [CommMonoid M] [Fintype M] [DecidableEq M]
  {R : Type _} [CommMonoidWithZero R]

/-- **The order of the constructed character is the order of `ζ`**:
`χ(g^k) = ζ^k` defines a character of the same order as `ζ`.  (The
book's argument for `χ_{p,q}`: `χ^p = 1` pointwise since `ζ_p^p = 1`,
and `χ(g) = ζ_p ≠ 1`.) -/
theorem orderOf_ofRootOfUnity {ζ : Rˣ}
    (hζ : ζ ∈ rootsOfUnity (Fintype.card Mˣ) R)
    {g : Mˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    orderOf (MulChar.ofRootOfUnity hζ hg) = orderOf ζ := by
  rw [orderOf_eq_orderOf_iff]
  intro k
  constructor
  · intro h
    have happ := congrArg (fun χ : MulChar M R => χ (g : M)) h
    simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe,
      MulChar.ofRootOfUnity_spec hζ hg] at happ
    exact_mod_cast Units.ext (by exact_mod_cast happ)
  · intro h
    rw [MulChar.eq_iff hg]
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe,
      MulChar.ofRootOfUnity_spec hζ hg]
    exact_mod_cast congrArg Units.val h

/-- "As a character mod `q`, the order of `χ` is a divisor of
`q − 1`" — generically, the order of the constructed character
divides the order of the unit group. -/
theorem orderOf_ofRootOfUnity_dvd {ζ : Rˣ}
    (hζ : ζ ∈ rootsOfUnity (Fintype.card Mˣ) R)
    {g : Mˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    orderOf (MulChar.ofRootOfUnity hζ hg) ∣ Fintype.card Mˣ := by
  rw [orderOf_ofRootOfUnity hζ hg]
  exact orderOf_dvd_iff_pow_eq_one.mpr ((mem_rootsOfUnity _ ζ).mp hζ)

end OrderOf

section ChiPQ

variable {R : Type _} [CommMonoidWithZero R]

/-- A `p`-th root of unity qualifies for the character construction
mod `q` whenever `p ∣ q − 1` — the setup of the book's `χ_{p,q}`. -/
theorem mem_rootsOfUnity_card_units_of_dvd {q p : ℕ} [Fact q.Prime]
    {ζ : Rˣ} (h1 : ζ ^ p = 1) (hdvd : p ∣ q - 1) :
    ζ ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R := by
  rw [mem_rootsOfUnity]
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [ZMod.card_units_eq_totient,
      Nat.totient_prime (Fact.out (p := q.Prime))]
  obtain ⟨t, ht⟩ := hdvd
  rw [hcard, ht, pow_mul, h1, one_pow]

/-- **The book's `χ_{p,q}` has order exactly `p`**: the character
sending a primitive root mod `q` to a primitive `p`-th root of
unity, for `p ∣ q − 1`. -/
theorem orderOf_ofRootOfUnity_eq {q p : ℕ} [Fact q.Prime]
    {ζ : Rˣ} (hζp : IsPrimitiveRoot ζ p)
    (hζ : ζ ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    orderOf (MulChar.ofRootOfUnity hζ hg) = p := by
  rw [orderOf_ofRootOfUnity hζ hg, ← hζp.eq_orderOf]

end ChiPQ

section GaussSumFormula

variable {q : ℕ} [Fact q.Prime] {R : Type _} [CommRing R]

/-- **The book's displayed reindexing of the Gauss sum**:
`τ(χ) = ∑_k χ(g)^k · ζ_q^(g^k)` — summing over the powers of a
primitive root `g` mod `q` instead of over all residues (the zero
residue contributes nothing, and the nonzero residues are exactly
`g^0, …, g^(q−2)`). -/
theorem gaussSum_eq_sum_range {ζq : R} (hζq : ζq ^ q = 1)
    (χ : MulChar (ZMod q) R) {g : (ZMod q)ˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    gaussSum χ (AddChar.zmodChar q hζq)
      = ∑ k ∈ range (q - 1),
          χ (g : ZMod q) ^ k * ζq ^ ((g ^ k : (ZMod q)ˣ) : ZMod q).val := by
  have : NeZero q := ⟨(Fact.out (p := q.Prime)).pos.ne'⟩
  have hq1 : 1 < q := (Fact.out (p := q.Prime)).one_lt
  have hord : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out (p := q.Prime))]
  -- drop the zero residue
  have hzero : χ (0 : ZMod q) * AddChar.zmodChar q hζq (0 : ZMod q) = 0 := by
    rw [χ.map_nonunit (by
      rw [isUnit_zero_iff]
      intro h01
      exact one_ne_zero (α := ZMod q) h01.symm), zero_mul]
  rw [gaussSum, ← Finset.insert_erase (Finset.mem_univ (0 : ZMod q)),
    Finset.sum_insert (Finset.notMem_erase _ _), hzero, zero_add]
  -- reindex the nonzero residues by powers of the primitive root
  refine (Finset.sum_bij
    (fun k _ => ((g ^ k : (ZMod q)ˣ) : ZMod q)) ?_ ?_ ?_ ?_).symm
  · -- powers of `g` are nonzero residues
    intro k _
    rw [Finset.mem_erase]
    exact ⟨Units.ne_zero _, Finset.mem_univ _⟩
  · -- injectivity below the order
    intro k hk j hj hkj
    rw [Finset.mem_range] at hk hj
    refine pow_injOn_Iio_orderOf ?_ ?_ (Units.ext hkj)
    · rw [Set.mem_Iio, hord]
      exact hk
    · rw [Set.mem_Iio, hord]
      exact hj
  · -- surjectivity: every nonzero residue is a power of `g`
    intro x hx
    rw [Finset.mem_erase] at hx
    have hxu : IsUnit x := hx.1.isUnit
    obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr (hg hxu.unit)
    have hn' : g ^ n = hxu.unit := hn
    refine ⟨n % (q - 1), Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
    show ((g ^ (n % (q - 1)) : (ZMod q)ˣ) : ZMod q) = x
    rw [← hord, pow_mod_orderOf, hn', IsUnit.unit_spec]
  · -- the summands match
    intro k _
    rw [AddChar.zmodChar_apply, Units.val_pow_eq_pow_val, map_pow]

/-- A character constructed from a root of unity of order `> 1` is
nontrivial. -/
theorem ofRootOfUnity_ne_one {M : Type _} [CommMonoid M] [Fintype M]
    [DecidableEq M] {R' : Type _} [CommMonoidWithZero R'] {ζ : R'ˣ}
    (hζ : ζ ∈ rootsOfUnity (Fintype.card Mˣ) R')
    {g : Mˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) (hord : 1 < orderOf ζ) :
    MulChar.ofRootOfUnity hζ hg ≠ 1 := by
  intro h1
  have := orderOf_ofRootOfUnity hζ hg
  rw [h1, orderOf_one] at this
  omega

/-- **Lemma 4.4.1**: `G(p,q) · conj(G(p,q)) = q` — the Gauss sum norm
relation, stated symbolically: conjugation inverts the roots of
unity, i.e. sends `χ` to `χ⁻¹` and the additive character to its
inverse (over `ℂ` this is literally complex conjugation,
`MulChar.star_eq_inv`).  The content is Mathlib's
`gaussSum_mul_gaussSum_eq_card` — whose proof is the book's: expand
the double sum, substitute `a = m₁m₂⁻¹`, evaluate the inner
geometric sum, and kill the remaining character sum by the book's
(1.28) (`MulChar.sum_eq_zero_of_ne_one`).  Our contribution is the
instantiation at the order-`p` character `χ_{p,q}`: nontriviality
comes from `1 < p` (the book takes `p` prime).  The hypothesis
`p ∣ q − 1` is carried by the root-of-unity membership `hζmem`
(see `mem_rootsOfUnity_card_units_of_dvd`). -/
theorem lemma_4_4_1 {q p : ℕ} [Fact q.Prime] (hp : 1 < p)
    {R : Type _} [CommRing R] [IsDomain R]
    {ζp : Rˣ} (hζp : IsPrimitiveRoot ζp p)
    (hζmem : ζp ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {ζq : R} (hζq : IsPrimitiveRoot ζq q) :
    gaussSum (MulChar.ofRootOfUnity hζmem hg)
        (AddChar.zmodChar q hζq.pow_eq_one)
      * gaussSum (MulChar.ofRootOfUnity hζmem hg)⁻¹
        (AddChar.zmodChar q hζq.pow_eq_one)⁻¹
      = (q : R) := by
  have : NeZero q := ⟨(Fact.out (p := q.Prime)).pos.ne'⟩
  have hχ : MulChar.ofRootOfUnity hζmem hg ≠ 1 :=
    ofRootOfUnity_ne_one hζmem hg (by rw [← hζp.eq_orderOf]; exact hp)
  have hψ : (AddChar.zmodChar q hζq.pow_eq_one).IsPrimitive := by
    have h := AddChar.zmodChar_primitive_of_primitive_root q hζq
    convert h using 2
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rwa [ZMod.card] at h

/-- **Lemma 4.4.2**: for primes `p, q, n` with `p ∣ q − 1` and
`gcd(pq, n) = 1`,
`G(p,q)^(n^(p−1) − 1) ≡ χ_{p,q}(n) (mod n)` — stated as ring
divisibility `(n : R) ∣ G^(n^(p−1)−1) − χ(n)` in any integral domain
carrying the roots of unity (in `ℤ[ζ_p, ζ_q]` this is the book's
coefficientwise congruence, by freeness).

The proof is the book's, run in the quotient ring `R⧸(n)`: there the
characteristic is `n` (or the quotient collapses, making the claim
trivial), so the multinomial step is the Frobenius
(`sum_pow_char_pow`); Fermat's little theorem gives
`χ(m)^(n^(p−1)) = χ(m)`; the substitution `m ↦ m·n^(p−1)` is
`gaussSum_mulShift`, costing `χ(n^(p−1))⁻¹ = χ(n)` since
`χ(n)^p = 1`; this yields `G^(n^(p−1)) ≡ χ(n)·G`.  Multiplying by
`conj G` and using Lemma 4.4.1 turns both sides into multiples of
`q`, which is invertible mod `n` by Bézout, and the cancellation
gives the result. -/
theorem lemma_4_4_2 {q p n : ℕ} [Fact q.Prime] (hp : p.Prime)
    (hn : n.Prime) (hgcd : Nat.Coprime (p * q) n)
    {R : Type _} [CommRing R] [IsDomain R]
    {ζp : Rˣ} (hζp : IsPrimitiveRoot ζp p)
    (hζmem : ζp ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {ζq : R} (hζq : IsPrimitiveRoot ζq q) :
    (n : R) ∣ gaussSum (MulChar.ofRootOfUnity hζmem hg)
        (AddChar.zmodChar q hζq.pow_eq_one) ^ (n ^ (p - 1) - 1)
      - MulChar.ofRootOfUnity hζmem hg (n : ZMod q) := by
  have : NeZero q := ⟨(Fact.out (p := q.Prime)).pos.ne'⟩
  set χ := MulChar.ofRootOfUnity hζmem hg with hχdef
  set ψ := AddChar.zmodChar q hζq.pow_eq_one with hψdef
  have hpn : Nat.Coprime p n :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_right p q) hgcd
  have hqn : Nat.Coprime q n :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_left q p) hgcd
  -- `χ` has order `p`
  have hχp : χ ^ p = 1 := by
    have horder := orderOf_ofRootOfUnity_eq hζp hζmem hg
    rw [← hχdef] at horder
    rw [← horder]
    exact pow_orderOf_eq_one χ
  -- `n` is a unit mod `q`
  have hnq0 : (n : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact absurd ((Nat.prime_dvd_prime_iff_eq
        (Fact.out (p := q.Prime)) hn).mp hdvd)
      ((Nat.coprime_primes (Fact.out (p := q.Prime)) hn).mp hqn)
  have hnu : IsUnit (n : ZMod q) := isUnit_iff_ne_zero.mpr hnq0
  have hN1 : 1 ≤ n ^ (p - 1) := Nat.one_le_pow _ _ hn.pos
  -- Fermat: `n^(p−1) = 1 + p·t`
  obtain ⟨t, ht⟩ : ∃ t, n ^ (p - 1) = 1 + p * t := by
    have : Fact p.Prime := ⟨hp⟩
    have hfer : (n : ZMod p) ^ (p - 1) = 1 := by
      apply ZMod.pow_card_sub_one_eq_one
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp hn).mp hdvd)
        ((Nat.coprime_primes hp hn).mp hpn)
    have hmod : 1 ≡ n ^ (p - 1) [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      exact hfer.symm
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hN1).mp hmod
    exact ⟨t, by omega⟩
  -- `χ(m)^(n^(p−1)) = χ(m)`
  have hχpow : ∀ m : ZMod q, χ m ^ n ^ (p - 1) = χ m := by
    intro m
    by_cases hm : IsUnit m
    · have hmp : χ m ^ p = 1 := by
        rw [← MulChar.pow_apply' χ hp.pos.ne' m, hχp, MulChar.one_apply hm]
      rw [ht, pow_add, pow_one, pow_mul, hmp, one_pow, mul_one]
    · rw [χ.map_nonunit hm, zero_pow (by omega)]
  -- the substitution `m ↦ m·n^(p−1)` costs exactly `χ(n)`
  have hshift : gaussSum χ (ψ.mulShift
        ((hnu.unit ^ (p - 1) : (ZMod q)ˣ) : ZMod q))
      = χ (n : ZMod q) * gaussSum χ ψ := by
    have h1 := gaussSum_mulShift χ ψ (hnu.unit ^ (p - 1))
    have hnp : χ (n : ZMod q)
        * χ ((hnu.unit ^ (p - 1) : (ZMod q)ˣ) : ZMod q) = 1 := by
      rw [← map_mul]
      have hval : (n : ZMod q)
          * ((hnu.unit ^ (p - 1) : (ZMod q)ˣ) : ZMod q)
          = (n : ZMod q) ^ p := by
        rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← pow_succ']
        congr 1
        have := hp.two_le
        omega
      rw [hval, map_pow, ← MulChar.pow_apply' χ hp.pos.ne', hχp,
        MulChar.one_apply hnu]
    calc gaussSum χ (ψ.mulShift
          ((hnu.unit ^ (p - 1) : (ZMod q)ˣ) : ZMod q))
        = (χ (n : ZMod q)
            * χ ((hnu.unit ^ (p - 1) : (ZMod q)ˣ) : ZMod q))
          * gaussSum χ (ψ.mulShift
            ((hnu.unit ^ (p - 1) : (ZMod q)ˣ) : ZMod q)) := by
          rw [hnp, one_mul]
      _ = χ (n : ZMod q)
          * (χ ((hnu.unit ^ (p - 1) : (ZMod q)ˣ) : ZMod q)
            * gaussSum χ (ψ.mulShift
              ((hnu.unit ^ (p - 1) : (ZMod q)ˣ) : ZMod q))) := by
          ring
      _ = χ (n : ZMod q) * gaussSum χ ψ := by rw [h1]
  -- pass to the quotient `R⧸(n)`
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  set π := Ideal.Quotient.mk (Ideal.span {(n : R)}) with hπdef
  rcases subsingleton_or_nontrivial (R ⧸ Ideal.span {(n : R)}) with hS | hS
  · exact Subsingleton.elim _ _
  have hnS : ((n : ℕ) : R ⧸ Ideal.span {(n : R)}) = 0 := by
    rw [show ((n : ℕ) : R ⧸ Ideal.span {(n : R)}) = π (n : R) from
      (map_natCast π n).symm, hπdef, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have : CharP (R ⧸ Ideal.span {(n : R)}) n := by
    have hdvd : ringChar (R ⧸ Ideal.span {(n : R)}) ∣ n := ringChar.dvd hnS
    rcases hn.eq_one_or_self_of_dvd _ hdvd with h1 | hcharn
    · exfalso
      have h0 := CharP.cast_eq_zero (R ⧸ Ideal.span {(n : R)})
        (ringChar (R ⧸ Ideal.span {(n : R)}))
      rw [h1, Nat.cast_one] at h0
      exact one_ne_zero h0
    · exact CharP.congr (ringChar (R ⧸ Ideal.span {(n : R)})) hcharn
  have : Fact n.Prime := ⟨hn⟩
  -- Frobenius: the multinomial step of the book
  have hfrob : π (gaussSum χ ψ) ^ n ^ (p - 1)
      = π (gaussSum χ (ψ.mulShift
        ((hnu.unit ^ (p - 1) : (ZMod q)ˣ) : ZMod q))) := by
    rw [gaussSum, gaussSum, map_sum, map_sum, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← map_pow, mul_pow, hχpow m, ← AddChar.map_nsmul_eq_pow,
      AddChar.mulShift_apply]
    congr 2
    rw [nsmul_eq_mul, Nat.cast_pow, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec]
  -- combine: `G^(n^(p−1)) ≡ χ(n)·G (mod n)`
  have hkey : π (gaussSum χ ψ) ^ n ^ (p - 1)
      = π (χ (n : ZMod q)) * π (gaussSum χ ψ) := by
    rw [hfrob, hshift, map_mul]
  -- Lemma 4.4.1, pushed to the quotient
  have h441 := lemma_4_4_1 hp.one_lt hζp hζmem hg hζq
  rw [← hχdef, ← hψdef] at h441
  have h441' : π (gaussSum χ ψ) * π (gaussSum χ⁻¹ ψ⁻¹)
      = ((q : ℕ) : R ⧸ Ideal.span {(n : R)}) := by
    rw [← map_mul, h441, map_natCast]
  -- `q` is a unit mod `n`
  have hqu : IsUnit ((q : ℕ) : R ⧸ Ideal.span {(n : R)}) := by
    have hb := Nat.gcd_eq_gcd_ab q n
    rw [Nat.Coprime.gcd_eq_one hqn] at hb
    have hcast := congrArg
      (fun z : ℤ => (z : R ⧸ Ideal.span {(n : R)})) hb
    push_cast at hcast
    rw [hnS, zero_mul, add_zero] at hcast
    exact IsUnit.of_mul_eq_one _ hcast.symm
  -- split off one factor of `G` and cancel `q`
  have hsplit : π (gaussSum χ ψ) ^ n ^ (p - 1)
      = π (gaussSum χ ψ) ^ (n ^ (p - 1) - 1) * π (gaussSum χ ψ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hmul : π (gaussSum χ ψ) ^ n ^ (p - 1) * π (gaussSum χ⁻¹ ψ⁻¹)
      = π (χ (n : ZMod q)) * π (gaussSum χ ψ)
        * π (gaussSum χ⁻¹ ψ⁻¹) := by
    rw [hkey]
  rw [hsplit, mul_assoc, mul_assoc, h441'] at hmul
  rw [mul_comm _ ((q : ℕ) : R ⧸ Ideal.span {(n : R)}),
    mul_comm _ ((q : ℕ) : R ⧸ Ideal.span {(n : R)})] at hmul
  have hcancel := hqu.mul_left_cancel hmul
  rw [map_sub, map_pow, hcancel, sub_self]

/-- **Lemma 4.4.3**: distinct powers of a root of unity remain
distinct mod `n` — if `ζ_m^j ≡ ζ_m^k (mod n)` and `n ∤ m`, then
`ζ_m^j = ζ_m^k`.  Stated symbolically over a domain, with the
arithmetic hypothesis in its ring form `¬(n : R) ∣ (m : R)` (in
`ℤ[ζ_m]`, divisibility of integers in the ring descends to `ℤ` by
freeness, so this is exactly the book's `n ∤ m`).  The proof is the
book's: multiplying by `ζ^((m−1)k)` reduces to a congruence
`ζ^e ≡ 1`; if `ζ^e ≠ 1`, then `1 − ζ^(e mod m)` is one of the
factors of `∏_(l=1)^(m−1) (1 − ζ^l) = m` (Mathlib's
`IsPrimitiveRoot.prod_one_sub_pow_eq_order`), so `n` would divide
`m`. -/
theorem lemma_4_4_3 {m n : ℕ} {R : Type _} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ m) (hnm : ¬(n : R) ∣ (m : R))
    {j k : ℕ} (hcong : (n : R) ∣ ζ ^ j - ζ ^ k) :
    ζ ^ j = ζ ^ k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hnm (by rw [Nat.cast_zero]; exact dvd_zero _)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- core: a congruence to `1` forces equality to `1`
  have hcore : ∀ e : ℕ, (n : R) ∣ ζ ^ e - 1 → ζ ^ e = 1 := by
    intro e hdvd
    have hmod : ζ ^ e = ζ ^ (e % (m' + 1)) := by
      conv_lhs => rw [← Nat.div_add_mod e (m' + 1), pow_add, pow_mul,
        hζ.pow_eq_one, one_pow, one_mul]
    rcases Nat.eq_zero_or_pos (e % (m' + 1)) with h0 | hpos
    · rw [hmod, h0, pow_zero]
    · exfalso
      apply hnm
      have hlt : e % (m' + 1) < m' + 1 := Nat.mod_lt _ (by omega)
      -- the factor `1 − ζ^(e mod m)` divides `m`
      have hfac : (1 - ζ ^ (e % (m' + 1))) ∣ ((m' : R) + 1) := by
        rw [← hζ.prod_one_sub_pow_eq_order]
        obtain ⟨d, hd⟩ : ∃ d, e % (m' + 1) = d + 1 :=
          ⟨e % (m' + 1) - 1, by omega⟩
        rw [hd]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
      -- and `n` divides that factor
      have hn1 : (n : R) ∣ 1 - ζ ^ (e % (m' + 1)) := by
        rw [hmod] at hdvd
        have h := (dvd_neg (α := R)).mpr hdvd
        rwa [neg_sub] at h
      have := hn1.trans hfac
      rwa [show ((m' + 1 : ℕ) : R) = (m' : R) + 1 by push_cast; ring]
  -- reduce the congruence to the core by multiplying with `ζ^(m'·k)`
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
  have hstep : (n : R) ∣ ζ ^ (j + m' * k) - 1 := by
    have h := hcong.mul_right (ζ ^ (m' * k))
    have hrw : (ζ ^ j - ζ ^ k) * ζ ^ (m' * k)
        = ζ ^ (j + m' * k) - ζ ^ ((m' + 1) * k) := by
      rw [sub_mul, ← pow_add, ← pow_add]
      congr 2
      ring
    rw [hrw, show ζ ^ ((m' + 1) * k) = 1 by
      rw [pow_mul, hζ.pow_eq_one, one_pow]] at h
    exact h
  have h1 : ζ ^ (j + m' * k) = 1 := hcore _ hstep
  have h2 : ζ ^ (k + m' * k) = 1 := by
    rw [show k + m' * k = (m' + 1) * k by ring, pow_mul, hζ.pow_eq_one,
      one_pow]
  have hmul : ζ ^ j * ζ ^ (m' * k) = ζ ^ k * ζ ^ (m' * k) := by
    rw [← pow_add, ← pow_add, h1, h2]
  exact mul_right_cancel₀ (pow_ne_zero _ hζ0) hmul

end GaussSumFormula

section ChiValues

/-! ### Character values are `ζ`-powers

The bookkeeping feeding Lemma 4.4.2 into the (4.21)/(4.23) machinery
of Theorem 4.4.6: the constructed character `χ_(p,q)` takes the
value `ζ^k` at `g^k`, so every unit value is a `ζ`-power, and
Lemma 4.4.2's congruence `G^(n^(p−1)−1) ≡ χ(n) (mod n)` becomes the
`h42` hypothesis shape `G^N ≡ ζ^(j₀) (mod n)`. -/

variable {q : ℕ} [Fact q.Prime] {R : Type _} [CommMonoidWithZero R]

/-- The defining values of the constructed character:
`χ(g^k) = ζ^k`. -/
theorem ofRootOfUnity_apply_pow {ζ : Rˣ}
    (hζ : ζ ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) (k : ℕ) :
    MulChar.ofRootOfUnity hζ hg ((g ^ k : (ZMod q)ˣ) : ZMod q)
      = (ζ : R) ^ k := by
  rw [Units.val_pow_eq_pow_val, map_pow, MulChar.ofRootOfUnity_spec]

/-- Every unit value of the constructed character is a `ζ`-power. -/
theorem exists_ofRootOfUnity_apply_eq {ζ : Rˣ}
    (hζ : ζ ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {x : ZMod q} (hx : IsUnit x) :
    ∃ k, MulChar.ofRootOfUnity hζ hg x = (ζ : R) ^ k := by
  obtain ⟨xu, rfl⟩ := hx
  have hmem : xu ∈ Submonoid.powers g :=
    (mem_powers_iff_mem_zpowers ..).mpr (hg xu)
  obtain ⟨k, hk⟩ := hmem
  have hk' : g ^ k = xu := hk
  exact ⟨k, by rw [← hk']; exact ofRootOfUnity_apply_pow hζ hg k⟩

/-- **Lemma 4.4.2 in root-of-unity form** — the `h42` hypothesis of
the (4.21)/(4.23) machinery: there is `j₀` with
`G^(n^(p−1)−1) ≡ ζ_p^(j₀) (mod n)`. -/
theorem lemma_4_4_2_zeta_pow {p n : ℕ} (hp : p.Prime)
    (hn : n.Prime) (hgcd : Nat.Coprime (p * q) n)
    {R : Type _} [CommRing R] [IsDomain R]
    {ζp : Rˣ} (hζp : IsPrimitiveRoot ζp p)
    (hζmem : ζp ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {ζq : R} (hζq : IsPrimitiveRoot ζq q) :
    ∃ j₀, (n : R) ∣ gaussSum (MulChar.ofRootOfUnity hζmem hg)
        (AddChar.zmodChar q hζq.pow_eq_one) ^ (n ^ (p - 1) - 1)
      - (ζp : R) ^ j₀ := by
  have hq := Fact.out (p := q.Prime)
  have : NeZero q := ⟨hq.ne_zero⟩
  have hunit : IsUnit ((n : ℕ) : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.coprime_dvd_right (dvd_mul_left q p) hgcd.symm
  obtain ⟨j₀, hj⟩ := exists_ofRootOfUnity_apply_eq hζmem hg hunit
  have h42 := lemma_4_4_2 hp hn hgcd hζp hζmem hg hζq
  rw [hj] at h42
  exact ⟨j₀, h42⟩

end ChiValues

end CP

end Azurite
