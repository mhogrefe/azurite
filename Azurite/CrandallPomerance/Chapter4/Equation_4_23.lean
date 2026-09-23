/-
  Crandall–Pomerance, equation (4.23), the per-pair chain: for each
  pair of primes `p ∣ I`, `q ∣ F` with `p ∣ q − 1`, the proof of
  Theorem 4.4.6 runs

    `χ(r) = χ(r)^(b_p) ≡ G^((r^(p−1)−1) b_p) = G^(p^(w) u_p a_p)
       ≡ χ(l)^(a_p) = χ(l^a)  (mod r)`,

  and upgrades the congruence between the two root-of-unity values
  to an EQUALITY by Lemma 4.4.3.  Here this is `eq_4_23_pair`, in
  root-of-unity form (the character bookkeeping `χ(r) = ζ^(j₀)`,
  `χ(l^a) = ζ^(l a)` happens at assembly): from the Lemma-4.4.2
  congruence `G^N ≡ ζ^(j₀) (mod r)`, the step-3/4 congruence
  `G^(p^w u) ≡ ζ^l (mod r)`, and the (4.22) exponent identity
  `N b = p^w u a` with `b ≡ 1 (mod p)`, conclude

    `ζ^(j₀) = ζ^(l a)`.

  Also here: the quotient-descent toolkit for instantiating the
  (4.21) engines at `M = R/(r)` —
  * `quotientMk_eq_iff_dvd`: images agree in `R/(r)` iff `r`
    divides the difference (so the algorithm's mod-`n` checks, which
    descend to mod-`r`, become EQUATIONS in the quotient monoid);
  * `orderOf_quotientMk_zeta`: a primitive `p`-th root of `R` keeps
    order EXACTLY `p` in `R/(r)` when `r ∤ p` — surviving via
    Lemma 4.4.3 (a trivialized `ζ` mod `r` would force `ζ = 1`
    in `R`) — the `orderOf ζ = p` hypothesis of the engines.
-/
import Azurite.CrandallPomerance.Chapter4.Equation_4_21
import Azurite.CrandallPomerance.Chapter4.Equation_4_22
import Azurite.CrandallPomerance.Chapter4.Exercise_4_24
import Azurite.CrandallPomerance.Chapter4.GaussSums

namespace Azurite

namespace CP

variable {R : Type _} [CommRing R]

/-- Images agree in `R/(r)` iff `r` divides the difference. -/
theorem quotientMk_eq_iff_dvd {r : ℕ} (x y : R) :
    Ideal.Quotient.mk (Ideal.span {(r : R)}) x
      = Ideal.Quotient.mk (Ideal.span {(r : R)}) y ↔ (r : R) ∣ x - y := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

/-- A primitive `p`-th root of unity keeps order exactly `p` in the
quotient `R/(r)` when `r ∤ p` (via Lemma 4.4.3): the `orderOf`
hypothesis of the (4.21) engines. -/
theorem orderOf_quotientMk_zeta [IsDomain R] {r p : ℕ} {ζ : R}
    (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (hrp : ¬(r : R) ∣ (p : R)) :
    orderOf (Ideal.Quotient.mk (Ideal.span {(r : R)}) ζ) = p := by
  have hpow : (Ideal.Quotient.mk (Ideal.span {(r : R)}) ζ) ^ p = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow) with
    h1 | h1
  · exfalso
    have hone : Ideal.Quotient.mk (Ideal.span {(r : R)}) ζ
        = Ideal.Quotient.mk (Ideal.span {(r : R)}) 1 := by
      rw [map_one]
      exact orderOf_eq_one_iff.mp h1
    have hdd : (r : R) ∣ ζ ^ 1 - ζ ^ 0 := by
      rw [pow_one, pow_zero]
      exact (quotientMk_eq_iff_dvd ζ 1).mp hone
    have hζ1 := lemma_4_4_3 hζ hrp hdd
    rw [pow_one, pow_zero] at hζ1
    have hord := hζ.eq_orderOf
    rw [hζ1, orderOf_one] at hord
    exact hp.one_lt.ne' hord
  · exact h1

/-- **Equation (4.23), the per-pair chain**: from the Lemma-4.4.2
congruence `G^N ≡ ζ^(j₀)`, the step-3/4 congruence
`G^(p^w u) ≡ ζ^l` (both mod `r`), and the (4.22) identity
`N b = p^w u a` with `b ≡ 1 (mod p)`, the two root-of-unity values
are EQUAL: `ζ^(j₀) = ζ^(l a)` (Lemma 4.4.3 upgrades the congruence). -/
theorem eq_4_23_pair [IsDomain R] {r p : ℕ} {G ζ : R} (hp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) (hrp : ¬(r : R) ∣ (p : R))
    {N w u a b l j₀ : ℕ} (hexp : N * b = p ^ w * u * a)
    (hb : b ≡ 1 [MOD p])
    (h42 : (r : R) ∣ G ^ N - ζ ^ j₀)
    (hstep : (r : R) ∣ G ^ (p ^ w * u) - ζ ^ l) :
    ζ ^ j₀ = ζ ^ (l * a) := by
  -- power the two congruences into a common exponent
  have h42b : (r : R) ∣ G ^ (N * b) - ζ ^ (j₀ * b) := by
    rw [pow_mul G N b, pow_mul ζ j₀ b]
    exact h42.trans (sub_dvd_pow_sub_pow _ _ b)
  have hstepa : (r : R) ∣ G ^ (p ^ w * u * a) - ζ ^ (l * a) := by
    rw [pow_mul G (p ^ w * u) a, pow_mul ζ l a]
    exact hstep.trans (sub_dvd_pow_sub_pow _ _ a)
  rw [hexp] at h42b
  -- `ζ^(j₀ b) = ζ^(j₀)` since `b ≡ 1 (mod p)` and `ζ` has order `p`
  have hζfin : IsOfFinOrder ζ := by
    rw [← orderOf_pos_iff, ← hζ.eq_orderOf]
    exact hp.pos
  have hbord : ζ ^ (j₀ * b) = ζ ^ j₀ := by
    rw [hζfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]
    simpa using (hb.mul_left j₀)
  rw [hbord] at h42b
  -- the two `ζ`-powers are congruent mod `r`, hence equal
  have hchain : (r : R) ∣ ζ ^ j₀ - ζ ^ (l * a) := by
    have hd := dvd_sub hstepa h42b
    have hrw : G ^ (p ^ w * u * a) - ζ ^ (l * a)
        - (G ^ (p ^ w * u * a) - ζ ^ j₀) = ζ ^ j₀ - ζ ^ (l * a) := by
      ring
    rwa [hrw] at hd
  exact lemma_4_4_3 hζ hrp hchain

/-- **Equation (4.21), assembled**: the engines instantiated at
`R/(r)`.  From the step-3/4 congruence `G^(p^w u) ≡ ζ^l (mod r)`
(descended from mod `n`), the Lemma-4.4.2 congruence
`G^N ≡ ζ^(j₀) (mod r)`, and — when `l ≡ 0` — the step-5 coprime
check, conclude `p^w ∣ N`; in the `l ≡ 0` case moreover
`ζ^(j₀) = 1` (back in `R`, via Lemma 4.4.3), the value the (4.23)
chain needs. -/
theorem eq_4_21 [IsDomain R] {r p : ℕ} {G ζ : R} (hp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) (hrp : ¬(r : R) ∣ (p : R))
    {w u l N j₀ : ℕ} (hu : ¬p ∣ u) (hw : 0 < w)
    (hstep : (r : R) ∣ G ^ (p ^ w * u) - ζ ^ l)
    (h42 : (r : R) ∣ G ^ N - ζ ^ j₀)
    (h5 : p ∣ l → ∀ j, ¬(r : R) ∣ G ^ (p ^ (w - 1) * u) - ζ ^ j) :
    p ^ w ∣ N ∧ (p ∣ l → ζ ^ j₀ = 1) := by
  set π := Ideal.Quotient.mk (Ideal.span {(r : R)}) with hπ
  have hζq : orderOf (π ζ) = p := orderOf_quotientMk_zeta hp hζ hrp
  have hstepq : π G ^ (p ^ w * u) = π ζ ^ l := by
    rw [← map_pow, ← map_pow]
    exact (quotientMk_eq_iff_dvd _ _).mpr hstep
  have h42q : π G ^ N = π ζ ^ j₀ := by
    rw [← map_pow, ← map_pow]
    exact (quotientMk_eq_iff_dvd _ _).mpr h42
  by_cases hpl : p ∣ l
  · -- the `l ≡ 0` case: engine 2, then Lemma 4.4.3 lifts
    -- `(π ζ)^(j₀) = 1` back to `R`
    obtain ⟨t, rfl⟩ := hpl
    have h1 : π G ^ (p ^ w * u) = 1 := by
      rw [hstepq, pow_mul, ← hζq, pow_orderOf_eq_one, one_pow]
    have h5' : ∀ j, π G ^ (p ^ (w - 1) * u) ≠ π ζ ^ j := by
      intro j hj
      refine h5 ⟨t, rfl⟩ j ?_
      rw [← quotientMk_eq_iff_dvd, map_pow, map_pow]
      exact hj
    obtain ⟨hdvd, hone⟩ := eq_4_21_of_forall_ne hp hζq hu hw h1 h5' h42q
    refine ⟨hdvd, fun _ => ?_⟩
    have hdd : (r : R) ∣ ζ ^ j₀ - ζ ^ 0 := by
      rw [← quotientMk_eq_iff_dvd, map_pow, map_pow, hone, pow_zero]
    have hlift := lemma_4_4_3 hζ hrp hdd
    rwa [pow_zero] at hlift
  · -- the `l ≢ 0` case: engine 1 on `G^(pN) = 1`
    have h42p : π G ^ (p * N) = 1 := by
      rw [mul_comm p N, pow_mul, h42q, ← pow_mul, mul_comm j₀ p, pow_mul,
        ← hζq, pow_orderOf_eq_one, one_pow]
    exact ⟨eq_4_21_of_ne_one hp hζq hpl hstepq h42p,
      fun hpl' => absurd hpl' hpl⟩

section GaussSumInstances

/-! ### The engines fed by the Gauss sum

The per-`p` and per-pair master results for a surviving composite:
`G` is now the Gauss sum, `ζ` the constructed character's root,
and Lemma 4.4.2 (in root-of-unity form) supplies `h42`. -/

variable {q p r : ℕ} [Fact q.Prime]

/-- **The per-`p` data of (4.22) exists for a surviving composite**:
from the step-3/4 congruence at `q₀(p)` and (when `l ≡ 0`) the
step-5 coprime check, Lemma 4.4.2 and the (4.21) engines produce
`p^w ∣ r^(p−1) − 1`, and (4.22) turns it into the exponent identity
`(r^(p−1) − 1) b = p^w u a` with `b ≡ 1 (mod p)`. -/
theorem exists_eq_4_22_data (hp : p.Prime) (hr : r.Prime)
    (hgcd : Nat.Coprime (p * q) r)
    {R : Type _} [CommRing R] [IsDomain R]
    {ζp : Rˣ} (hζp : IsPrimitiveRoot ζp p)
    (hζmem : ζp ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {ζq : R} (hζq : IsPrimitiveRoot ζq q)
    (hrp : ¬(r : R) ∣ (p : R))
    {w u l : ℕ} (hu : ¬p ∣ u) (hw : 0 < w)
    (hstep : (r : R) ∣ gaussSum (MulChar.ofRootOfUnity hζmem hg)
        (AddChar.zmodChar q hζq.pow_eq_one) ^ (p ^ w * u)
      - (ζp : R) ^ l)
    (h5 : p ∣ l → ∀ j,
      ¬(r : R) ∣ gaussSum (MulChar.ofRootOfUnity hζmem hg)
          (AddChar.zmodChar q hζq.pow_eq_one) ^ (p ^ (w - 1) * u)
        - (ζp : R) ^ j) :
    ∃ a b, (r ^ (p - 1) - 1) * b = p ^ w * u * a ∧ b ≡ 1 [MOD p] := by
  obtain ⟨j₀, h42⟩ := lemma_4_4_2_zeta_pow hp hr hgcd hζp hζmem hg hζq
  obtain ⟨hdvd, -⟩ := eq_4_21 hp (IsPrimitiveRoot.coe_units_iff.mpr hζp)
    hrp hu hw hstep h42 h5
  exact eq_4_22 hp hu hdvd

/-- **The per-pair character value** (the display before (4.23)):
with the per-`p` exponent identity of (4.22) in hand, the pair's
step-3/4 congruence pins the character value of the least prime
factor: `χ_(p,q)(r) = ζ_p^(l a)`. -/
theorem eq_4_23_char (hp : p.Prime) (hr : r.Prime)
    (hgcd : Nat.Coprime (p * q) r)
    {R : Type _} [CommRing R] [IsDomain R]
    {ζp : Rˣ} (hζp : IsPrimitiveRoot ζp p)
    (hζmem : ζp ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {ζq : R} (hζq : IsPrimitiveRoot ζq q)
    (hrp : ¬(r : R) ∣ (p : R))
    {w u a b l : ℕ} (hexp : (r ^ (p - 1) - 1) * b = p ^ w * u * a)
    (hb : b ≡ 1 [MOD p])
    (hstep : (r : R) ∣ gaussSum (MulChar.ofRootOfUnity hζmem hg)
        (AddChar.zmodChar q hζq.pow_eq_one) ^ (p ^ w * u)
      - (ζp : R) ^ l) :
    MulChar.ofRootOfUnity hζmem hg ((r : ℕ) : ZMod q)
      = (ζp : R) ^ (l * a) := by
  have hq := Fact.out (p := q.Prime)
  have : NeZero q := ⟨hq.ne_zero⟩
  have hunit : IsUnit ((r : ℕ) : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.coprime_dvd_right (dvd_mul_left q p) hgcd.symm
  obtain ⟨j₀, hj⟩ := exists_ofRootOfUnity_apply_eq hζmem hg hunit
  have h42 := lemma_4_4_2 hp hr hgcd hζp hζmem hg hζq
  rw [hj] at h42 ⊢
  exact eq_4_23_pair hp (IsPrimitiveRoot.coe_units_iff.mpr hζp) hrp
    hexp hb h42 hstep

/-- **The per-`q` conclusion of (4.23)**: `r ≡ l^a (mod q)`.  For
`q − 1` squarefree, primitive `p`-th roots `ζ_p` for every prime
`p ∣ q − 1` living in ONE domain, and the common generator `g_q`:
if each character value at `r` is `ζ_p^(e_p)` (supplied per pair by
`eq_4_23_char` with `e_p = l(p,q) a_p`), the exponents match the
CRT data (`e_p ≡ l(q)·a (mod p)`), and `l ≡ g_q^(l(q)) (mod q)`
(step 6), then the product-character engine of Exercise 4.24 forces
`r ≡ l^a (mod q)`. -/
theorem eq_4_23_mod_q {q : ℕ} [Fact q.Prime] (hsq : Squarefree (q - 1))
    {R : Type _} [CommRing R] [IsDomain R] {ζ : ℕ → Rˣ}
    (hζmem : ∀ p, ζ p ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) R)
    (hζord : ∀ p ∈ (q - 1).primeFactors, IsPrimitiveRoot (ζ p) p)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {r l a lq : ℕ} {e : ℕ → ℕ}
    (hrval : ∀ p ∈ (q - 1).primeFactors,
      MulChar.ofRootOfUnity (hζmem p) hg ((r : ℕ) : ZMod q)
        = ((ζ p : Rˣ) : R) ^ e p)
    (hecong : ∀ p ∈ (q - 1).primeFactors, e p ≡ lq * a [MOD p])
    (hl : ((l : ℕ) : ZMod q) = ((g ^ lq : (ZMod q)ˣ) : ZMod q))
    (hr : IsUnit ((r : ℕ) : ZMod q)) :
    r ≡ l ^ a [MOD q] := by
  have hlunit : IsUnit ((l : ℕ) : ZMod q) := by
    rw [hl]
    exact (g ^ lq).isUnit
  have hla : (((l ^ a : ℕ) : ZMod q))
      = ((g ^ (lq * a) : (ZMod q)ˣ) : ZMod q) := by
    rw [Nat.cast_pow, hl, ← Units.val_pow_eq_pow_val, ← pow_mul]
  have hval : ∀ p ∈ (q - 1).primeFactors,
      MulChar.ofRootOfUnity (hζmem p) hg ((r : ℕ) : ZMod q)
        = MulChar.ofRootOfUnity (hζmem p) hg ((l ^ a : ℕ) : ZMod q) := by
    intro p hp
    rw [hrval p hp, hla, ofRootOfUnity_apply_pow (hζmem p) hg]
    have hordp : orderOf ((ζ p : Rˣ) : R) = p := by
      rw [← IsPrimitiveRoot.eq_orderOf
        (IsPrimitiveRoot.coe_units_iff.mpr (hζord p hp))]
    have hfin : IsOfFinOrder ((ζ p : Rˣ) : R) := by
      rw [← orderOf_pos_iff, hordp]
      exact (Nat.prime_of_mem_primeFactors hp).pos
    rw [hfin.pow_eq_pow_iff_modEq, hordp]
    exact hecong p hp
  have hla_unit : IsUnit (((l ^ a : ℕ) : ZMod q)) := by
    rw [Nat.cast_pow]
    exact hlunit.pow a
  have heq := eq_of_forall_primeFactor_char_eq
    (x := ((r : ℕ) : ZMod q)) (y := ((l ^ a : ℕ) : ZMod q)) hsq
    (fun p => MulChar.ofRootOfUnity (hζmem p) hg)
    (fun p hp => orderOf_ofRootOfUnity_eq (hζord p hp) (hζmem p) hg)
    hr hla_unit hval
  rwa [ZMod.natCast_eq_natCast_iff] at heq

/-- Congruence modulo each of a set of distinct primes combines to
congruence modulo their product. -/
theorem modEq_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {x y : ℕ} (h : ∀ p ∈ s, x ≡ y [MOD p]) :
    x ≡ y [MOD ∏ p ∈ s, p] := by
  induction s using Finset.induction with
  | empty => simpa using Nat.modEq_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hco : Nat.Coprime a (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes (hs a (Finset.mem_insert_self a s))
          (hs p (Finset.mem_insert_of_mem hp))).mpr
          (fun hEq => ha (hEq ▸ hp))
    exact (Nat.modEq_and_modEq_iff_modEq_mul hco).mp
      ⟨h a (Finset.mem_insert_self a s),
        ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
          (fun p hp => h p (Finset.mem_insert_of_mem hp))⟩

/-- **Equation (4.23)**: `r ≡ l^a (mod F)` — the per-`q` congruences
(from `eq_4_23_mod_q`) combine over the squarefree `F`.  With
`F > √n ≥ r` and `F ≠ r` this pins `r` as the least positive
residue of `l^a mod F`, so the step-6 divisor search finds it. -/
theorem modEq_of_forall_primeFactor {F x y : ℕ} (hsq : Squarefree F)
    (h : ∀ q ∈ F.primeFactors, x ≡ y [MOD q]) : x ≡ y [MOD F] := by
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  exact modEq_prod_primes (fun p hp => Nat.prime_of_mem_primeFactors hp) h

end GaussSumInstances

end CP

end Azurite
