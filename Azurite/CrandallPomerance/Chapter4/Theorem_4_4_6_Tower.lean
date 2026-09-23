/-
  Theorem 4.4.6, the composite direction, with hypotheses in the
  CHECKER'S NATIVE LAND: the pair towers `ℤ[ζ_p, ζ_q]` of
  Definition 4.4.4, where Algorithm 4.4.5 computes.

  The key architectural point: divisibility transfers COVARIANTLY
  along the tower-to-common-ring homomorphism, but not conversely —
  so the step-5 NON-divisibility hypothesis cannot be pushed from
  the tower into `ℤ[ζ_((q−1)q)]` without a rings-of-integers
  reflection argument.  Instead, the per-`p` order-climbing
  ((4.21)/(4.22), which consumes step 5) and the per-pair character
  pinning (`eq_4_23_char`) run ENTIRELY in the tower — a faithful
  domain with the right roots, by the Definition-4.4.4 machinery —
  and only the resulting character-value EQUALITIES cross the
  homomorphism `towerToCycM` (`ζ_p ↦ ζ^((q−1)q/p)`,
  `ζ_q ↦ ζ^(q−1)`, a double `AdjoinRoot.lift`), under which the
  character construction and the Gauss sum commute
  (`towerToCycM_char`, `towerToCycM_gaussSum`).  The per-`q`
  product-character step then runs in `ℤ[ζ_((q−1)q)]` as before.

  `theorem_4_4_6_composite_tower` is the checker-facing form of
  Theorem 4.4.6's composite direction: every hypothesis is either
  arithmetic or a congruence in some `ℤ[ζ_p, ζ_q]`.
-/
import Azurite.CrandallPomerance.Chapter4.CycPQDomain
import Azurite.CrandallPomerance.Chapter4.Theorem_4_4_6_CycM

namespace Azurite

namespace CP

open Polynomial

/-- `ζ_p` of the pair tower as a unit (junk parameters get `1`). -/
noncomputable def zetaPQUnit (p q : ℕ) : (CycPQ p q)ˣ :=
  if h : p.Prime ∧ q.Prime ∧ p ≠ q then
    haveI : Fact p.Prime := ⟨h.1⟩
    haveI : Fact q.Prime := ⟨h.2.1⟩
    ((isPrimitiveRoot_zetaP p q h.2.2).isUnit h.1.pos.ne').unit
  else 1

section Tower

variable {q p : ℕ} [Fact q.Prime]

private theorem hm_pos' : 0 < (q - 1) * q := by
  have := (Fact.out (p := q.Prime)).two_le
  exact Nat.mul_pos (by omega) (by omega)

private theorem hcond_of_mem (hp : p ∈ (q - 1).primeFactors) :
    p.Prime ∧ q.Prime ∧ p ≠ q := by
  have hqp := Fact.out (p := q.Prime)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  refine ⟨hpp, hqp, ?_⟩
  have h2 := hqp.two_le
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

theorem val_zetaPQUnit (hp : p ∈ (q - 1).primeFactors) :
    ((zetaPQUnit p q : (CycPQ p q)ˣ) : CycPQ p q) = zetaP p q := by
  rw [zetaPQUnit, dite_eq_left (hcond_of_mem hp)]
  exact IsUnit.unit_spec _

theorem isPrimitiveRoot_zetaPQUnit (hp : p ∈ (q - 1).primeFactors) :
    IsPrimitiveRoot (zetaPQUnit p q) p := by
  rw [← IsPrimitiveRoot.coe_units_iff, val_zetaPQUnit hp]
  have : Fact p.Prime := ⟨(hcond_of_mem hp).1⟩
  exact isPrimitiveRoot_zetaP p q (hcond_of_mem hp).2.2

theorem zetaPQUnit_mem (hp : p ∈ (q - 1).primeFactors) :
    zetaPQUnit p q ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) (CycPQ p q) := by
  refine mem_rootsOfUnity_card_units_of_dvd ?_
    (Nat.dvd_of_mem_primeFactors hp)
  ext
  rw [Units.val_pow_eq_pow_val, val_zetaPQUnit hp, Units.val_one]
  have : Fact p.Prime := ⟨(hcond_of_mem hp).1⟩
  exact (isPrimitiveRoot_zetaP p q (hcond_of_mem hp).2.2).pow_eq_one

theorem isPrimitiveRoot_zetaQPQ (hp : p ∈ (q - 1).primeFactors) :
    IsPrimitiveRoot (zetaQ p q) q := by
  have : Fact p.Prime := ⟨(hcond_of_mem hp).1⟩
  exact isPrimitiveRoot_zetaQ p q (hcond_of_mem hp).2.2

private theorem eval₂_cyclotomic_int' {R : Type _} [CommRing R] [IsDomain R]
    {k : ℕ} (hk : 0 < k) {ζ : R} (hζ : IsPrimitiveRoot ζ k) :
    (cyclotomic k ℤ).eval₂ (Int.castRingHom R) ζ = 0 := by
  rw [eval₂_eq_eval_map, map_cyclotomic]
  exact hζ.isRoot_cyclotomic hk

/-- The first leg of the transfer: `ℤ[ζ_p] → ℤ[ζ_((q−1)q)]`,
`ζ_p ↦ ζ^((q−1)q/p)`. -/
noncomputable def towerToCycMP (hp : p ∈ (q - 1).primeFactors) :
    CycP p →+* CycM ((q - 1) * q) :=
  AdjoinRoot.lift (Int.castRingHom _)
    ((zetaPFam q p : (CycM ((q - 1) * q))ˣ) : CycM ((q - 1) * q)) (by
      have := isDomain_cycM (hm_pos' (q := q))
      exact eval₂_cyclotomic_int' (hcond_of_mem hp).1.pos
        (IsPrimitiveRoot.coe_units_iff.mpr (isPrimitiveRoot_zetaPFam hp)))

/-- **The tower-to-common-ring homomorphism**
`ℤ[ζ_p, ζ_q] → ℤ[ζ_((q−1)q)]`: `ζ_p ↦ ζ^((q−1)q/p)`,
`ζ_q ↦ ζ^(q−1)`. -/
noncomputable def towerToCycM (hp : p ∈ (q - 1).primeFactors) :
    CycPQ p q →+* CycM ((q - 1) * q) :=
  AdjoinRoot.lift (towerToCycMP hp) (zetaQFam q) (by
    rw [show cyclotomic q (CycP p)
        = map (Int.castRingHom (CycP p)) (cyclotomic q ℤ) from
        (map_cyclotomic q (Int.castRingHom (CycP p))).symm,
      eval₂_map,
      Subsingleton.elim ((towerToCycMP hp).comp (Int.castRingHom (CycP p)))
        (Int.castRingHom _)]
    have := isDomain_cycM (hm_pos' (q := q))
    exact eval₂_cyclotomic_int' (Fact.out (p := q.Prime)).pos
      isPrimitiveRoot_zetaQFam)

@[simp] theorem towerToCycM_zetaP (hp : p ∈ (q - 1).primeFactors) :
    towerToCycM hp (zetaP p q)
      = ((zetaPFam q p : (CycM ((q - 1) * q))ˣ) : CycM ((q - 1) * q)) := by
  rw [zetaP, towerToCycM]
  rw [show (algebraMap (CycP p) (CycPQ p q)) (AdjoinRoot.root _)
      = AdjoinRoot.of _ (AdjoinRoot.root _) from rfl,
    AdjoinRoot.lift_of, towerToCycMP, AdjoinRoot.lift_root]

@[simp] theorem towerToCycM_zetaQ (hp : p ∈ (q - 1).primeFactors) :
    towerToCycM hp (zetaQ p q) = zetaQFam q := by
  rw [zetaQ, towerToCycM, AdjoinRoot.lift_root]

/-- The character construction commutes with the transfer. -/
theorem towerToCycM_char (hp : p ∈ (q - 1).primeFactors)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (MulChar.ofRootOfUnity (zetaPQUnit_mem hp) hg).ringHomComp
        (towerToCycM hp)
      = MulChar.ofRootOfUnity (zetaPFam_mem p) hg := by
  rw [MulChar.eq_iff hg, MulChar.ringHomComp_apply,
    MulChar.ofRootOfUnity_spec, MulChar.ofRootOfUnity_spec,
    val_zetaPQUnit hp, towerToCycM_zetaP hp]

/-- The Gauss sum commutes with the transfer. -/
theorem towerToCycM_gaussSum (hp : p ∈ (q - 1).primeFactors)
    {g : (ZMod q)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    towerToCycM hp (gaussSum
        (MulChar.ofRootOfUnity (zetaPQUnit_mem hp) hg)
        (AddChar.zmodChar q (isPrimitiveRoot_zetaQPQ hp).pow_eq_one))
      = gaussSum (MulChar.ofRootOfUnity (zetaPFam_mem p) hg)
        (AddChar.zmodChar q isPrimitiveRoot_zetaQFam.pow_eq_one) := by
  rw [gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul]
  congr 1
  · have h := congrArg
      (fun χ : MulChar (ZMod q) (CycM ((q - 1) * q)) => χ a)
      (towerToCycM_char hp hg)
    simpa only [MulChar.ringHomComp_apply] using h
  · rw [AddChar.zmodChar_apply, AddChar.zmodChar_apply, map_pow,
      towerToCycM_zetaQ hp]

end Tower

/-- **Theorem 4.4.6, composite direction, tower-hypothesis form** —
the checker-facing statement: every hypothesis is arithmetic or a
congruence in a pair tower `ℤ[ζ_p, ζ_q]`, where Algorithm 4.4.5
computes.  The per-`p` order climbing and the per-pair character
pinning run in the towers; the character values transfer to
`ℤ[ζ_((q−1)q)]`, where the per-`q` product-character step and the
final CRT/divisor-search argument conclude. -/
theorem theorem_4_4_6_composite_tower
    {n I F : ℕ} (hn1 : 1 < n) (hncomp : ¬n.Prime)
    (hI : Squarefree I) (hF : Squarefree F)
    (hqI : ∀ q ∈ F.primeFactors, (q - 1) ∣ I)
    (hgcd : Nat.Coprime (I * F) n) (hnF : n < F ^ 2)
    {w u : ℕ → ℕ}
    (hw : ∀ p ∈ I.primeFactors, 0 < w p)
    (hu : ∀ p ∈ I.primeFactors, ¬p ∣ u p)
    {lTab : ℕ → ℕ → ℕ} {lq : ℕ → ℕ} {l : ℕ} {q₀ : ℕ → ℕ}
    (hq₀ : ∀ p ∈ I.primeFactors, q₀ p ∈ F.primeFactors ∧ p ∣ q₀ p - 1)
    {g : (q : ℕ) → (ZMod q)ˣ}
    (hgen : ∀ q, q ∈ F.primeFactors → ∀ x, x ∈ Subgroup.zpowers (g q))
    (hstep : ∀ q (hq : q ∈ F.primeFactors) [Fact q.Prime],
      ∀ p (hp : p ∈ (q - 1).primeFactors),
      (n : CycPQ p q)
        ∣ gaussSum (MulChar.ofRootOfUnity (zetaPQUnit_mem hp) (hgen q hq))
            (AddChar.zmodChar q (isPrimitiveRoot_zetaQPQ hp).pow_eq_one)
            ^ (p ^ w p * u p)
          - ((zetaPQUnit p q : (CycPQ p q)ˣ) : CycPQ p q) ^ lTab p q)
    (h5 : ∀ q (hq : q ∈ F.primeFactors) [Fact q.Prime],
      ∀ p (hp : p ∈ (q - 1).primeFactors), q₀ p = q →
      ∀ d, d ∣ n → 1 < d → ∀ j,
      ¬(d : CycPQ p q)
        ∣ gaussSum (MulChar.ofRootOfUnity (zetaPQUnit_mem hp) (hgen q hq))
            (AddChar.zmodChar q (isPrimitiveRoot_zetaQPQ hp).pow_eq_one)
            ^ (p ^ (w p - 1) * u p)
          - ((zetaPQUnit p q : (CycPQ p q)ˣ) : CycPQ p q) ^ j)
    (hlq : ∀ q ∈ F.primeFactors, ∀ p ∈ (q - 1).primeFactors,
      lq q ≡ lTab p q [MOD p])
    (hl : ∀ q ∈ F.primeFactors,
      ((l : ℕ) : ZMod q) = ((g q ^ lq q : (ZMod q)ˣ) : ZMod q)) :
    ∃ j, 0 < j ∧ j < I ∧ l ^ j % F ∣ n ∧ 1 < l ^ j % F ∧ l ^ j % F < n := by
  have hrprime : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hrdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hIpos : 0 < I := Nat.pos_of_ne_zero hI.ne_zero
  have hpq_co : ∀ p q', p ∣ I → q' ∣ F → Nat.Coprime (p * q') n.minFac :=
    fun p q' hpI hqF =>
      (hgcd.coprime_dvd_left (mul_dvd_mul hpI hqF)).coprime_dvd_right hrdvd
  have hnotdvd : ∀ p q', p ∣ I → q' ∣ F → ¬n.minFac ∣ p := by
    intro p q' hpI hqF hdvd
    have hco := hpq_co p q' hpI hqF
    have h1 : n.minFac ∣ Nat.gcd (p * q') n.minFac :=
      Nat.dvd_gcd (dvd_mul_of_dvd_left hdvd q') dvd_rfl
    rw [hco] at h1
    exact absurd (Nat.dvd_one.mp h1) (by have := hrprime.one_lt; omega)
  -- per `p ∣ I`: the (4.22) data, from the `q₀(p)` checks IN THE TOWER
  have hab : ∀ p ∈ I.primeFactors, ∃ a b,
      (n.minFac ^ (p - 1) - 1) * b = p ^ w p * u p * a
        ∧ b ≡ 1 [MOD p] := by
    intro p hp
    obtain ⟨hq₀mem, hq₀dvd⟩ := hq₀ p hp
    have hq'prime : (q₀ p).Prime := Nat.prime_of_mem_primeFactors hq₀mem
    have : Fact (q₀ p).Prime := ⟨hq'prime⟩
    have hpmem : p ∈ (q₀ p - 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hq₀dvd,
        by have := hq'prime.two_le; omega⟩
    have : Fact p.Prime := ⟨(hcond_of_mem hpmem).1⟩
    have : IsDomain (CycPQ p (q₀ p)) :=
      isDomain_cycPQ p (q₀ p) (hcond_of_mem hpmem).2.2
    have hco : Nat.Coprime (p * q₀ p) n.minFac :=
      hpq_co p (q₀ p) (Nat.dvd_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hq₀mem)
    have hrp : ¬((n.minFac : CycPQ p (q₀ p)) ∣ (p : CycPQ p (q₀ p))) := by
      rw [natCast_dvd_natCast_iff]
      exact hnotdvd p (q₀ p) (Nat.dvd_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hq₀mem)
    have hstepr : (n.minFac : CycPQ p (q₀ p))
        ∣ gaussSum (MulChar.ofRootOfUnity (zetaPQUnit_mem hpmem)
            (hgen (q₀ p) hq₀mem))
            (AddChar.zmodChar (q₀ p)
              (isPrimitiveRoot_zetaQPQ hpmem).pow_eq_one)
            ^ (p ^ w p * u p)
          - ((zetaPQUnit p (q₀ p) : (CycPQ p (q₀ p))ˣ) : CycPQ p (q₀ p))
            ^ lTab p (q₀ p) :=
      (Nat.cast_dvd_cast hrdvd).trans (hstep (q₀ p) hq₀mem p hpmem)
    exact exists_eq_4_22_data (Nat.prime_of_mem_primeFactors hp) hrprime
      hco (isPrimitiveRoot_zetaPQUnit hpmem) (zetaPQUnit_mem hpmem)
      (hgen (q₀ p) hq₀mem) (isPrimitiveRoot_zetaQPQ hpmem) hrp
      (hu p hp) (hw p hp) hstepr
      (fun _ => h5 (q₀ p) hq₀mem p hpmem rfl n.minFac hrdvd
        hrprime.one_lt)
  choose! aTab bTab hab1 hab2 using hab
  obtain ⟨a, ha⟩ := exists_forall_modEq_primes
    (fun p hp => Nat.prime_of_mem_primeFactors hp) aTab
  -- per `q ∣ F`: pin the character values in the tower, transfer,
  -- and conclude `r ≡ l^a (mod q)` in the common ring
  have hqmod : ∀ q ∈ F.primeFactors, n.minFac ≡ l ^ a [MOD q] := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have : Fact q.Prime := ⟨hqprime⟩
    have hsqf : Squarefree (q - 1) :=
      Squarefree.squarefree_of_dvd (hqI q hq) hI
    have : IsDomain (CycM ((q - 1) * q)) := isDomain_cycM (hm_pos' (q := q))
    refine eq_4_23_mod_q (r := n.minFac) (l := l) (a := a) (lq := lq q)
      (e := fun p => lTab p q * aTab p) hsqf zetaPFam_mem
      (fun p hp => isPrimitiveRoot_zetaPFam hp) (hgen q hq) ?_ ?_
      (hl q hq) ?_
    · -- the character values, per pair: pinned in the tower, then
      -- transferred along `towerToCycM`
      intro p hpmem
      have : Fact p.Prime := ⟨(hcond_of_mem hpmem).1⟩
      have : IsDomain (CycPQ p q) :=
        isDomain_cycPQ p q (hcond_of_mem hpmem).2.2
      have hpI : p ∈ I.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpmem,
          (Nat.dvd_of_mem_primeFactors hpmem).trans (hqI q hq), hI.ne_zero⟩
      have hco : Nat.Coprime (p * q) n.minFac :=
        hpq_co p q (Nat.dvd_of_mem_primeFactors hpI)
          (Nat.dvd_of_mem_primeFactors hq)
      have hrp : ¬((n.minFac : CycPQ p q) ∣ (p : CycPQ p q)) := by
        rw [natCast_dvd_natCast_iff]
        exact hnotdvd p q (Nat.dvd_of_mem_primeFactors hpI)
          (Nat.dvd_of_mem_primeFactors hq)
      have hstepr : (n.minFac : CycPQ p q)
          ∣ gaussSum (MulChar.ofRootOfUnity (zetaPQUnit_mem hpmem)
              (hgen q hq))
              (AddChar.zmodChar q
                (isPrimitiveRoot_zetaQPQ hpmem).pow_eq_one)
              ^ (p ^ w p * u p)
            - ((zetaPQUnit p q : (CycPQ p q)ˣ) : CycPQ p q)
              ^ lTab p q :=
        (Nat.cast_dvd_cast hrdvd).trans (hstep q hq p hpmem)
      have hchar := eq_4_23_char (Nat.prime_of_mem_primeFactors hpmem)
        hrprime hco (isPrimitiveRoot_zetaPQUnit hpmem)
        (zetaPQUnit_mem hpmem) (hgen q hq)
        (isPrimitiveRoot_zetaQPQ hpmem) hrp (hab1 p hpI) (hab2 p hpI)
        hstepr
      -- transfer the value equation along the homomorphism
      have htr := congrArg (towerToCycM hpmem) hchar
      rw [map_pow] at htr
      rw [show towerToCycM hpmem
            ((MulChar.ofRootOfUnity (zetaPQUnit_mem hpmem) (hgen q hq))
              ((n.minFac : ℕ) : ZMod q))
          = ((MulChar.ofRootOfUnity (zetaPQUnit_mem hpmem)
              (hgen q hq)).ringHomComp (towerToCycM hpmem))
              ((n.minFac : ℕ) : ZMod q) from
          (MulChar.ringHomComp_apply _ _ _).symm,
        towerToCycM_char hpmem (hgen q hq),
        val_zetaPQUnit hpmem, towerToCycM_zetaP hpmem] at htr
      exact htr
    · -- the exponent congruences
      intro p hpmem
      have hpI : p ∈ I.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpmem,
          (Nat.dvd_of_mem_primeFactors hpmem).trans (hqI q hq), hI.ne_zero⟩
      exact Nat.ModEq.mul (hlq q hq p hpmem).symm (ha p hpI).symm
    · -- `r` is a unit mod `q`
      rw [ZMod.isUnit_iff_coprime]
      exact ((hgcd.coprime_dvd_left (dvd_mul_of_dvd_right
        (Nat.dvd_of_mem_primeFactors hq) I)).coprime_dvd_right hrdvd).symm
  have hlunit : ∀ q ∈ F.primeFactors, IsUnit ((l : ℕ) : ZMod q) := by
    intro q hq
    have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    rw [hl q hq]
    exact (g q ^ lq q).isUnit
  exact step6_finds_factor hn1 hncomp hIpos hnF
    (l_pow_I_modEq_one hF hqI hlunit)
    (modEq_of_forall_primeFactor hF hqmod)

end CP

end Azurite
