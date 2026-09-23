/-
  Soundness of the finite field primality test
  (`Azurite.AzPolynomial.finiteFieldTest`): pure verdict pass-through
  from the certificate checker — whichever attempt reaches a verdict,
  `lenstraTest_eq_some_true` / `lenstraTest_eq_some_false` applies to
  that attempt's witness pair.  (Completeness — a prime `n` is
  certified once the exhaustive tail reaches the witness pair that
  `CP.exists_lenstra_witness` provides — is deferred, as for the
  `n − 1` test.)
-/
import Azurite.AzPolynomial.FiniteFieldTest
import Azurite.AzPolynomial.Equiv.LenstraTest

namespace Azurite.AzPolynomial

variable {m : AzNat} [NeZero m.toNat] {I : ℕ} {F : AzNat}
  {qs : List AzNat} {attempts : ℕ} {seed : UInt64}

private theorem finiteFieldTestAux_verdict {b : Bool} :
    ∀ (attempts i : ℕ),
      finiteFieldTestAux m I F qs seed attempts i = some b →
      ∃ f g : AzPolynomial (AzZMod m), lenstraTest m I F qs f g = some b := by
  intro attempts
  induction attempts with
  | zero =>
    intro i h
    exact absurd h (by simp [finiteFieldTestAux])
  | succ attempts ih =>
    intro i h
    rw [finiteFieldTestAux] at h
    cases hlt : lenstraTest m I F qs (witnessPair m I seed i).1
        (witnessPair m I seed i).2 with
    | some b' =>
      rw [hlt] at h
      dsimp only at h
      obtain rfl : b' = b := by simpa using h
      exact ⟨_, _, hlt⟩
    | none =>
      rw [hlt] at h
      dsimp only at h
      exact ih (i + 1) h

/-- **A `some true` verdict of the finite field test proves `n`
prime.** -/
theorem finiteFieldTest_eq_some_true
    (h : finiteFieldTest m I F qs attempts seed = some true) :
    Nat.Prime m.toNat := by
  obtain ⟨f, g, hfg⟩ := finiteFieldTestAux_verdict attempts 0 h
  exact lenstraTest_eq_some_true hfg

/-- **A `some false` verdict of the finite field test proves `n`
composite.** -/
theorem finiteFieldTest_eq_some_false
    (h : finiteFieldTest m I F qs attempts seed = some false) :
    ¬Nat.Prime m.toNat := by
  obtain ⟨f, g, hfg⟩ := finiteFieldTestAux_verdict attempts 0 h
  exact lenstraTest_eq_some_false hfg

/-! ### Completeness: a prime is eventually certified -/

section Completeness

open Polynomial

/-- Invert `toZModPoly`: transport a `ZMod`-level polynomial to the
`Az` level. -/
private noncomputable def ofZModPoly (m : AzNat) [NeZero m.toNat]
    (w : Polynomial (ZMod m.toNat)) : AzPolynomial (AzZMod m) :=
  AzPolynomial.ofPoly (w.map
    ((AzZMod.ringEquivZMod (m := m)).symm : ZMod m.toNat →+* AzZMod m))

private theorem toZModPoly_ofZModPoly (w : Polynomial (ZMod m.toNat)) :
    toZModPoly (ofZModPoly m w) = w := by
  unfold toZModPoly ofZModPoly
  rw [toPoly_ofPoly, Polynomial.map_map]
  have hcomp : (AzZMod.toZModRingHom (m := m)).comp
      ((AzZMod.ringEquivZMod (m := m)).symm : ZMod m.toNat →+* AzZMod m)
      = RingHom.id _ := by
    ext x
    show AzZMod.toZModRingHom ((AzZMod.ringEquivZMod (m := m)).symm x) = x
    rw [AzZMod.toZModRingHom_apply, AzZMod.ringEquivZMod_symm_apply,
      AzZMod.toZMod_ofZMod]
  rw [hcomp, Polynomial.map_id]

private theorem degree_ofZModPoly (w : Polynomial (ZMod m.toNat)) :
    (ofZModPoly m w).degree = w.degree := by
  rw [ofZModPoly, ← AzPolynomial.degree_toPoly, toPoly_ofPoly,
    Polynomial.degree_map_eq_of_injective
      (AzZMod.ringEquivZMod (m := m)).symm.injective]

/-- Divisors of the accumulator persist through the product fold. -/
private theorem dvd_foldl_mul :
    ∀ (qs : List AzNat) (acc : AzNat) {d : ℕ}, d ∣ acc.toNat →
      d ∣ (qs.foldl (· * ·) acc).toNat
  | [], _, _, h => h
  | q :: qs, acc, d, h => by
    show d ∣ (qs.foldl (· * ·) (acc * q)).toNat
    exact dvd_foldl_mul qs (acc * q) (by
      rw [AzNat.toNat_mul]
      exact h.mul_right _)

/-- Every list element divides the product fold. -/
private theorem mem_dvd_foldl_mul :
    ∀ (qs : List AzNat) (acc : AzNat) {q : AzNat}, q ∈ qs →
      q.toNat ∣ (qs.foldl (· * ·) acc).toNat
  | q₀ :: qs, acc, q, hq => by
    rcases List.mem_cons.mp hq with rfl | hmem
    · exact dvd_foldl_mul qs (acc * q) (by
        rw [AzNat.toNat_mul]
        exact dvd_mul_left _ _)
    · exact mem_dvd_foldl_mul qs (acc * q₀) hmem

/-- The attempt loop reaches a `some true` index, given that no
earlier index can return `some false`. -/
private theorem finiteFieldTestAux_reaches
    (hnofalse : ∀ j, lenstraTest m I F qs (witnessPair m I seed j).1
      (witnessPair m I seed j).2 ≠ some false)
    {i₀ : ℕ} (hi₀ : lenstraTest m I F qs (witnessPair m I seed i₀).1
      (witnessPair m I seed i₀).2 = some true) :
    ∀ (k i : ℕ), i ≤ i₀ → i₀ < i + k →
      finiteFieldTestAux m I F qs seed k i = some true := by
  intro k
  induction k with
  | zero =>
    intro i h1 h2
    omega
  | succ k ih =>
    intro i h1 h2
    rw [finiteFieldTestAux]
    cases hlt : lenstraTest m I F qs (witnessPair m I seed i).1
        (witnessPair m I seed i).2 with
    | some b =>
      dsimp only
      cases b with
      | true => rfl
      | false => exact absurd hlt (hnofalse i)
    | none =>
      dsimp only
      have hne : i ≠ i₀ := by
        intro heq
        rw [heq, hi₀] at hlt
        exact absurd hlt (by simp)
      exact ih (i + 1) (by omega) (by omega)

/-- **Completeness**: for a prime `n` with valid certificate data,
some number of attempts certifies it — the hybrid stream's exhaustive
tail reaches the witness pair built from an irreducible polynomial of
degree `I` (which exists) and a cyclic generator of the extension
field's multiplicative group (which exists), and no attempt before it
can return `some false`, by soundness. -/
theorem finiteFieldTest_complete (hp : Nat.Prime m.toNat) (hI : 0 < I)
    (hqsp : (qs.all AzNat.isPrime : Bool) = true)
    (hqsF : qs.foldl (· * ·) (AzNat.ofNat 1) = F)
    (hFdvd : (m.pow I - 1) % F = 0)
    (hnF2 : m ≤ F * F) (seed : UInt64) :
    ∃ attempts, finiteFieldTest m I F qs attempts seed = some true := by
  have := Fact.mk hp
  have hN1 : 1 ≤ m.toNat ^ I - 1 := by
    have h2 : 2 ≤ m.toNat := hp.two_le
    have h2I : 2 ≤ m.toNat ^ I := le_trans h2 (Nat.le_self_pow hI.ne' _)
    omega
  -- the `ZMod`-level witnesses
  obtain ⟨μ, hμm, hμirr, hμdeg⟩ :=
    CP.exists_monic_irreducible_of_degree m.toNat I hI
  obtain ⟨gZ, hgZdeg, hgZ1, hgZ2⟩ :=
    CP.exists_lenstra_witness hI hμm hμirr hμdeg
  have hgZ0 : gZ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega), zero_sub] at hgZ1
    exact hμirr.not_isUnit (isUnit_of_dvd_one (dvd_neg.mp hgZ1))
  -- transport bookkeeping
  have htoZadd : ∀ a b : AzPolynomial (AzZMod m),
      toZModPoly (a + b) = toZModPoly a + toZModPoly b := by
    intro a b
    unfold toZModPoly
    rw [toPoly_add, Polynomial.map_add]
  have htoZmono : toZModPoly (monomial I (1 : AzZMod m))
      = Polynomial.monomial I 1 := by
    unfold toZModPoly
    rw [toPoly_monomial, Polynomial.map_monomial, map_one]
  -- the `Az`-level witness pair, as stream candidates
  have hμ0 : μ ≠ 0 := hμm.ne_zero
  have hdegμ' : (μ - Polynomial.monomial I 1).degree < (I : WithBot ℕ) := by
    have hmono : (Polynomial.monomial I (1 : ZMod m.toNat)).degree
        = (I : WithBot ℕ) := Polynomial.degree_monomial I one_ne_zero
    have hdμ : μ.degree = (I : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hμ0, hμdeg]
    have hd : μ.degree = (Polynomial.monomial I (1 : ZMod m.toNat)).degree := by
      rw [hdμ, hmono]
    have hlc : μ.leadingCoeff
        = (Polynomial.monomial I (1 : ZMod m.toNat)).leadingCoeff := by
      rw [hμm.leadingCoeff, Polynomial.leadingCoeff_monomial]
    have h := Polynomial.degree_sub_lt_left hd hμ0 hlc
    rwa [hdμ] at h
  have hdegcf : (ofZModPoly m (μ - Polynomial.monomial I 1)).degree
      < (I : WithBot ℕ) := by
    rw [degree_ofZModPoly]
    exact hdegμ'
  have hdegcg : (ofZModPoly m gZ).degree < (I : WithBot ℕ) := by
    rw [degree_ofZModPoly]
    rcases eq_or_ne gZ 0 with rfl | h0
    · rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe I
    · rw [Polynomial.degree_eq_natDegree h0]
      exact_mod_cast hgZdeg
  -- the hybrid stream reaches both candidates
  obtain ⟨jf, hjf⟩ := hybridPolyCandidate_hits (AzZMod m) seed hdegcf
  obtain ⟨jg, hjg⟩ := hybridPolyCandidate_hits (AzZMod m) seed hdegcg
  have hpair : witnessPair m I seed (Nat.pair jf jg)
      = (monomial I 1 + ofZModPoly m (μ - Polynomial.monomial I 1),
        ofZModPoly m gZ) := by
    rw [witnessPair, Nat.unpair_pair]
    dsimp only
    rw [hjf, hjg]
  -- the pair is a valid witness: the checker says `some true`
  have htoZf : toZModPoly
      (monomial I 1 + ofZModPoly m (μ - Polynomial.monomial I 1)) = μ := by
    rw [htoZadd, htoZmono, toZModPoly_ofZModPoly]
    ring
  have hfm : (monomial I 1
      + ofZModPoly m (μ - Polynomial.monomial I 1)).Monic :=
    Monic_toZModPoly.mp (by rw [htoZf]; exact hμm)
  have hfdeg : (monomial I 1
      + ofZModPoly m (μ - Polynomial.monomial I 1)).natDegree = I := by
    have h := natDegree_toZModPoly_eq
      (monomial I 1 + ofZModPoly m (μ - Polynomial.monomial I 1))
    rw [htoZf, hμdeg] at h
    exact h.symm
  have hg0 : ofZModPoly m gZ ≠ 0 := by
    intro h0
    apply hgZ0
    have := toZModPoly_ofZModPoly (m := m) gZ
    rw [h0] at this
    rw [← this]
    unfold toZModPoly
    rw [toPoly_zero, Polynomial.map_zero]
  have hgdeg : (ofZModPoly m gZ).natDegree < I := by
    have h := natDegree_toZModPoly_eq (ofZModPoly m gZ)
    rw [toZModPoly_ofZModPoly] at h
    rw [← h]
    exact hgZdeg
  have hFdvd' : F.toNat ∣ m.toNat ^ I - 1 := by
    have hc := congrArg AzNat.toNat hFdvd
    rw [AzNat.toNat_mod, AzNat.toNat_sub, AzNat.toNat_pow, AzNat.toNat_one,
      AzNat.toNat_zero] at hc
    exact Nat.dvd_of_mod_eq_zero hc
  have hlt : lenstraTest m I F qs
      (monomial I 1 + ofZModPoly m (μ - Polynomial.monomial I 1))
      (ofZModPoly m gZ) = some true := by
    refine lenstraTest_eq_some_true_of hp hI hfm hfdeg hg0 hgdeg hqsp hqsF
      hFdvd hnF2 (by rw [htoZf]; exact hμirr) ?_ ?_
    · rw [htoZf, toZModPoly_ofZModPoly]
      exact hgZ1
    · intro q hq
      rw [htoZf, toZModPoly_ofZModPoly]
      refine hgZ2 q.toNat ?_ ?_
      · exact (AzNat.isPrime_eq_true_iff q).mp
          (List.all_eq_true.mp hqsp q hq)
      · refine dvd_trans ?_ hFdvd'
        rw [← hqsF]
        exact mem_dvd_foldl_mul qs (AzNat.ofNat 1) hq
  -- walk the loop to the witness index
  have hnofalse : ∀ j, lenstraTest m I F qs (witnessPair m I seed j).1
      (witnessPair m I seed j).2 ≠ some false := by
    intro j hfj
    exact absurd hp (lenstraTest_eq_some_false hfj)
  refine ⟨Nat.pair jf jg + 1,
    finiteFieldTestAux_reaches (i₀ := Nat.pair jf jg) hnofalse ?_ _ 0
      (by omega) (by omega)⟩
  rw [hpair]
  exact hlt

end Completeness

end Azurite.AzPolynomial
