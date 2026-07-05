import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_48
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Corollary_8_38
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_46
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_52

/-!
# BPR §8.3.4 Theorem 8.51: size of signed remainders

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, Springer 2006, §8.3.4.

**Theorem 8.51.** If `P, Q ∈ ℤ[X]` have degrees `p, q < p` and coefficients of bitsize `≤ τ`, then
the numerators and denominators of the coefficients of the polynomials in the signed remainder
sequence of `P, Q` (over `ℚ`) have bitsizes bounded by `(p+q)(q+1)(τ + bit(p+q)) + τ`.

The proof (BPR) writes each signed remainder `Sₗ` as `βₗ · sResP_{d(ℓ-1)-1}` (Cor 8.38), with
`βₗ ∈ ℚ` obeying `βₗ = (s_j t_{i-1})/(s_k t_{j-1}) β_{ℓ-2}` (Theorem 8.34).  The coefficients of
`sResP` are integers bounded by Proposition 8.48, and the rational `βₗ` is tracked as an explicit
integer numerator/denominator through the recurrence.

This file builds the supporting machinery first.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

/-- The base change of an integer polynomial to `ℚ`. -/
noncomputable abbrev mapQ (f : ℤ[X]) : ℚ[X] := f.map (Int.castRingHom ℚ)

/-- Bitsize is subadditive over products: `bit(a·b) ≤ bit(a) + bit(b)`. -/
theorem int_size_mul_le (a b : ℤ) : Int.size (a * b) ≤ Int.size a + Int.size b := by
  unfold Int.size
  rw [Int.natAbs_mul, Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _)

/-- The bitsize of a divisor is at most the bitsize of the (nonzero) dividend. -/
theorem int_size_dvd_le {d n : ℤ} (hn : n ≠ 0) (h : d ∣ n) : Int.size d ≤ Int.size n := by
  unfold Int.size
  exact Nat.size_le_size (Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.natAbs_dvd_natAbs.mpr h))

/-- **`sResP` commutes with an injective ring homomorphism.**  For `φ : D →+* E` injective,
    `sResP (P.map φ) (Q.map φ) j = (sResP P Q j).map φ` (the injective special case of
    Proposition 8.52, since injective maps preserve degrees). -/
theorem sResP_map {D E : Type*} [CommRing E] [CommRing D] {φ : D →+* E}
    (hφ : Function.Injective φ) (P Q : D[X]) (j : ℕ) :
    sResP (P.map φ) (Q.map φ) j = (sResP P Q j).map φ :=
  proposition_8_52 φ P Q (Polynomial.natDegree_map_eq_of_injective hφ P)
    (Polynomial.natDegree_map_eq_of_injective hφ Q) j

/-- **`sResV` commutes with a degree-preserving ring homomorphism.**  The
    `V`-cofactor is the determinant of `sResVMat`, whose entries (constants from
    `SyHa` and monomials) all map coefficient-wise; the dimension is aligned by a
    `finCongr` reindex. -/
theorem sResV_map_of_natDegree_eq {D E : Type*} [CommRing D] [CommRing E] (f : D →+* E)
    (P Q : D[X]) (hP : (P.map f).natDegree = P.natDegree)
    (hQ : (Q.map f).natDegree = Q.natDegree) (j : ℕ) :
    sResV (P.map f) (Q.map f) j = (sResV P Q j).map f := by
  have hm : (P.map f).natDegree + (Q.map f).natDegree - 2 * j
      = P.natDegree + Q.natDegree - 2 * j := by rw [hP, hQ]
  rw [sResV, sResV]
  have hmat : sResVMat (P.map f) (Q.map f) j
      = ((sResVMat P Q j).map (Polynomial.mapRingHom f)).submatrix
          (finCongr hm) (finCongr hm) := by
    ext i k
    rw [Matrix.submatrix_apply, Matrix.map_apply, sResVMat, sResVMat,
      Matrix.of_apply, Matrix.of_apply]
    rcases Nat.lt_or_ge ((k : ℕ) + 1) ((P.map f).natDegree + (Q.map f).natDegree - 2 * j)
      with hk1 | hk1
    · rw [if_pos hk1,
        if_pos (show (((finCongr hm) k : Fin _) : ℕ) + 1 < P.natDegree + Q.natDegree - 2 * j
          from by show (k : ℕ) + 1 < _; omega),
        Polynomial.coe_mapRingHom, Polynomial.map_C]
      congr 1
      -- the `SyHa` entries map coefficient-wise
      rw [Azurite.BPR.Chapter4.SyHa, Azurite.BPR.Chapter4.SyHa,
        Matrix.of_apply, Matrix.of_apply]
      rcases Nat.lt_or_ge (i : ℕ) ((Q.map f).natDegree - j) with hib | hib
      · rw [if_pos hib,
          if_pos (show (((finCongr hm) i : Fin _) : ℕ) < Q.natDegree - j
            from by show (i : ℕ) < _; omega)]
        rw [show Polynomial.X ^ ((Q.map f).natDegree - j - 1 - (i : ℕ)) * P.map f
            = (Polynomial.X ^ (Q.natDegree - j - 1 - (i : ℕ)) * P).map f from by
          rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
          congr 2
          omega,
          Polynomial.coeff_map]
        congr 1
        simp only [Fin.val_castLE, finCongr_apply, Fin.val_cast]
        congr 2
        all_goals first | rfl | omega
      · rw [if_neg (show ¬ ((i : ℕ) < (Q.map f).natDegree - j) from by omega),
          if_neg (show ¬ ((((finCongr hm) i : Fin _) : ℕ) < Q.natDegree - j)
            from by show ¬ ((i : ℕ) < _); omega)]
        rw [show Polynomial.X ^ ((i : ℕ) - ((Q.map f).natDegree - j)) * Q.map f
            = (Polynomial.X ^ ((i : ℕ) - (Q.natDegree - j)) * Q).map f from by
          rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
          congr 2
          omega,
          Polynomial.coeff_map]
        congr 1
        simp only [Fin.val_castLE, finCongr_apply, Fin.val_cast]
        congr 2
        all_goals first | rfl | omega
    · rw [if_neg (show ¬ ((k : ℕ) + 1
            < (P.map f).natDegree + (Q.map f).natDegree - 2 * j) from by omega),
        if_neg (show ¬ ((((finCongr hm) k : Fin _) : ℕ) + 1 < P.natDegree + Q.natDegree - 2 * j)
          from by show ¬ ((k : ℕ) + 1 < _); omega)]
      rcases Nat.lt_or_ge (i : ℕ) ((Q.map f).natDegree - j) with hib | hib
      · rw [if_pos hib,
          if_pos (show (((finCongr hm) i : Fin _) : ℕ) < Q.natDegree - j
            from by show (i : ℕ) < _; omega),
          Polynomial.coe_mapRingHom, Polynomial.map_zero]
      · rw [if_neg (show ¬ ((i : ℕ) < (Q.map f).natDegree - j) from by omega),
          if_neg (show ¬ ((((finCongr hm) i : Fin _) : ℕ) < Q.natDegree - j)
            from by show ¬ ((i : ℕ) < _); omega),
          Polynomial.coe_mapRingHom, Polynomial.map_pow, Polynomial.map_X]
        congr 2
        show (i : ℕ) - ((Q.map f).natDegree - j) = (((finCongr hm) i : Fin _) : ℕ) - (Q.natDegree - j)
        simp only [finCongr_apply, Fin.val_cast]
        omega
  rw [hmat, Matrix.det_submatrix_equiv_self, ← Polynomial.coe_mapRingHom,
    RingHom.map_det]
  rfl

/-- **`sResV` commutes with an injective ring homomorphism** (the injective special
    case, mirroring `sResP_map`). -/
theorem sResV_map {D E : Type*} [CommRing E] [CommRing D] {φ : D →+* E}
    (hφ : Function.Injective φ) (P Q : D[X]) (j : ℕ) :
    sResV (P.map φ) (Q.map φ) j = (sResV P Q j).map φ :=
  sResV_map_of_natDegree_eq φ P Q (Polynomial.natDegree_map_eq_of_injective hφ P)
    (Polynomial.natDegree_map_eq_of_injective hφ Q) j

/-- **`Chapter4.sRes` commutes with an injective ring homomorphism** (for `j ≤ deg P`).  From
    `sResP_map` + `coeff_sResP` (`sRes_j` is the `Xʲ`-coefficient of `sResP_j`). -/
theorem sRes_map {D E : Type*} [CommRing E] [CommRing D] {φ : D →+* E}
    (hφ : Function.Injective φ) (P Q : D[X]) (hpq : Q.natDegree < P.natDegree) {m : ℕ}
    (hm : m ≤ P.natDegree) :
    Azurite.BPR.Chapter4.sRes (P.map φ) (Q.map φ) m = φ (Azurite.BPR.Chapter4.sRes P Q m) := by
  rw [← coeff_sResP (P.map φ) (Q.map φ)
        (by rwa [Polynomial.natDegree_map_eq_of_injective hφ,
          Polynomial.natDegree_map_eq_of_injective hφ])
        (by rw [Polynomial.natDegree_map_eq_of_injective hφ]; exact hm),
    sResP_map hφ, Polynomial.coeff_map, coeff_sResP P Q hpq hm]

/-- **Cleared defective-block scalar identity over an integral domain** (Prop 8.46 (★'), descended).
    `sRes_k · sRes_j^{j-k-1} = (-1)^{(j-k-1)(j-k)/2} · t_{j-1}^{j-k}` — obtained by transporting the
    field-level `sRes_block_identity` through `Frac D` by injectivity. -/
theorem sRes_block_identity_domain {D : Type*} [CommRing D] [IsDomain D] (P Q : D[X])
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) {j k : ℕ} (hjq : j ≤ Q.natDegree)
    (hj1 : 1 ≤ j) (hjnd : (sResP P Q j).natDegree = j) (hk0 : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) :
    Azurite.BPR.Chapter4.sRes P Q k * Azurite.BPR.Chapter4.sRes P Q j ^ (j - k - 1)
      = (-1 : D) ^ ((j - k - 1) * (j - k) / 2) * (sResP P Q (j - 1)).leadingCoeff ^ (j - k) := by
  have hkj : k ≤ j - 1 := by
    have := Polynomial.natDegree_le_iff_degree_le.mpr
      (sResP_degree_le P Q hpq (show j - 1 ≤ Q.natDegree by omega))
    rw [hkdeg] at this; omega
  have hkp : k ≤ P.natDegree := by omega
  have hjp : j ≤ P.natDegree := by omega
  set f := algebraMap D (FractionRing D) with hf_def
  have hf : Function.Injective f := IsFractionRing.injective D (FractionRing D)
  have hpqK : (Q.map f).natDegree < (P.map f).natDegree := by
    rwa [Polynomial.natDegree_map_eq_of_injective hf, Polynomial.natDegree_map_eq_of_injective hf]
  have hjndK : (sResP (P.map f) (Q.map f) j).natDegree = j := by
    rw [sResP_map hf, Polynomial.natDegree_map_eq_of_injective hf]; exact hjnd
  have hk0K : sResP (P.map f) (Q.map f) (j - 1) ≠ 0 := by
    rw [sResP_map hf]; exact (Polynomial.map_ne_zero_iff hf).mpr hk0
  have hkdegK : (sResP (P.map f) (Q.map f) (j - 1)).natDegree = k := by
    rw [sResP_map hf, Polynomial.natDegree_map_eq_of_injective hf]; exact hkdeg
  have hkey := sRes_block_identity (P.map f) (Q.map f) ((Polynomial.map_ne_zero_iff hf).mpr hP)
    ((Polynomial.map_ne_zero_iff hf).mpr hQ) hpqK
    (by rwa [Polynomial.natDegree_map_eq_of_injective hf]) hj1 hjndK hk0K hkdegK
  rw [sRes_map hf P Q hpq hkp, sRes_map hf P Q hpq hjp, sResP_map hf,
    Polynomial.leadingCoeff_map_of_injective hf] at hkey
  apply hf
  simp only [map_mul, map_pow, map_neg, map_one]
  exact hkey

/-- For associate `a, b` over a domain, `C(lcof b)·a = C(lcof a)·b` (division-free; the unit
    relating `a`, `b` is a constant `C c`). -/
theorem C_leadingCoeff_mul_eq_of_associated {D : Type*} [CommRing D] [IsDomain D] {a b : D[X]}
    (hab : Associated a b) :
    Polynomial.C b.leadingCoeff * a = Polynomial.C a.leadingCoeff * b := by
  obtain ⟨u, hu⟩ := hab
  obtain ⟨c, _, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hca : b = a * Polynomial.C c := by rw [← hu, ← hcu]
  have hlb : b.leadingCoeff = a.leadingCoeff * c := by
    rw [hca, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  rw [hlb, hca, Polynomial.C_mul]; ring

/-- **Cleared defective-block proportionality over an integral domain** (Prop 8.46, descended):
    `C(t_{j-1})·sResP_k = C(sRes_k)·sResP_{j-1}`.  Over `Frac D` the two subresultants are
    *associate* (block proportionality); the cleared identity is integral and descends. -/
theorem sResP_clear_domain {D : Type*} [CommRing D] [IsDomain D] (P Q : D[X])
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) {j k : ℕ} (hjq : j ≤ Q.natDegree)
    (hj1 : 1 ≤ j) (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k) :
    Polynomial.C (sResP P Q (j - 1)).leadingCoeff * sResP P Q k
      = Polynomial.C (Azurite.BPR.Chapter4.sRes P Q k) * sResP P Q (j - 1) := by
  have hkj : k ≤ j - 1 := by
    have := Polynomial.natDegree_le_iff_degree_le.mpr
      (sResP_degree_le P Q hpq (show j - 1 ≤ Q.natDegree by omega))
    rw [hkdeg] at this; omega
  have hkp : k ≤ P.natDegree := by omega
  set f := algebraMap D (FractionRing D) with hf_def
  have hf : Function.Injective f := IsFractionRing.injective D (FractionRing D)
  have hpqK : (Q.map f).natDegree < (P.map f).natDegree := by
    rwa [Polynomial.natDegree_map_eq_of_injective hf, Polynomial.natDegree_map_eq_of_injective hf]
  have hk0K : sResP (P.map f) (Q.map f) (j - 1) ≠ 0 := by
    rw [sResP_map hf]; exact (Polynomial.map_ne_zero_iff hf).mpr hk0
  have hkdegK : (sResP (P.map f) (Q.map f) (j - 1)).natDegree = k := by
    rw [sResP_map hf, Polynomial.natDegree_map_eq_of_injective hf]; exact hkdeg
  have hassoc : Associated (sResP (P.map f) (Q.map f) k) (sResP (P.map f) (Q.map f) (j - 1)) := by
    have h := sResP_block_associated (P.map f) (Q.map f) ((Polynomial.map_ne_zero_iff hf).mpr hP)
      ((Polynomial.map_ne_zero_iff hf).mpr hQ) hpqK
      (show j - 1 ≤ (Q.map f).natDegree by rw [Polynomial.natDegree_map_eq_of_injective hf]; omega)
      hk0K
    rwa [hkdegK] at h
  have hkneK : sResP (P.map f) (Q.map f) k ≠ 0 := fun h =>
    hk0K ((associated_zero_iff_eq_zero _).mp (h ▸ hassoc).symm)
  have hkdegKk : (sResP (P.map f) (Q.map f) k).natDegree = k :=
    (Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated hassoc)).trans hkdegK
  have hlcofK : (sResP (P.map f) (Q.map f) k).leadingCoeff = f (Azurite.BPR.Chapter4.sRes P Q k) := by
    rw [leadingCoeff_sResP_eq_sRes (P.map f) (Q.map f) hpqK
        (by rw [Polynomial.natDegree_map_eq_of_injective hf]; omega)
        (show IsNonDefective (P.map f) (Q.map f) k from by
          rw [IsNonDefective, Polynomial.degree_eq_natDegree hkneK, hkdegKk]),
      sRes_map hf P Q hpq hkp]
  apply Polynomial.map_injective f hf
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
    ← sResP_map hf, ← sResP_map hf,
    show f (sResP P Q (j - 1)).leadingCoeff = (sResP (P.map f) (Q.map f) (j - 1)).leadingCoeff from by
      rw [sResP_map hf, Polynomial.leadingCoeff_map_of_injective hf],
    ← hlcofK]
  exact C_leadingCoeff_mul_eq_of_associated hassoc

/-- **Cofactor clearing in a defective block** (`k < j-1`, `sResP_k ≠ 0`).  The `sResU`/`sResV`
    cofactors inherit the same proportionality as `sResP_clear_domain`:
    `C(lcof sResP_{j-1})·sResU_k = C(s_k)·sResU_{j-1}` (and likewise `sResV`).  Proof: the difference
    `A := C(t)·sResU_k − C(s)·sResU_{j-1}` (and `B` for `sResV`) satisfies `A·P + B·Q = 0` (combining
    the two Bézout relations with `sResP_clear_domain`).  Over `Frac(D)`, `gcd(P,Q) ∣ sResP_k` so
    `deg gcd ≤ k`; then `Q/gcd ∣ A` while `deg A ≤ q-1-k < q − deg gcd = deg(Q/gcd)`, forcing `A = 0`,
    after which `B·Q = 0` gives `B = 0`. -/
theorem sResUV_clear_domain {D : Type*} [CommRing D] [IsDomain D] (P Q : D[X])
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) {j k : ℕ} (hjq : j ≤ Q.natDegree)
    (hj1 : 1 ≤ j) (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k)
    (hkj : k < j - 1) :
    Polynomial.C (sResP P Q (j - 1)).leadingCoeff * sResU P Q k
        = Polynomial.C (Azurite.BPR.Chapter4.sRes P Q k) * sResU P Q (j - 1)
      ∧ Polynomial.C (sResP P Q (j - 1)).leadingCoeff * sResV P Q k
        = Polynomial.C (Azurite.BPR.Chapter4.sRes P Q k) * sResV P Q (j - 1) := by
  have hkq : k ≤ Q.natDegree := by omega
  have hjm1q : j - 1 ≤ Q.natDegree := by omega
  set t := (sResP P Q (j - 1)).leadingCoeff with ht_def
  set s := Azurite.BPR.Chapter4.sRes P Q k with hs_def
  have hbk : sResP P Q k = sResU P Q k * P + sResV P Q k * Q := sResP_eq_cofactor P Q hQ hpq hkq
  have hbj : sResP P Q (j - 1) = sResU P Q (j - 1) * P + sResV P Q (j - 1) * Q :=
    sResP_eq_cofactor P Q hQ hpq hjm1q
  have hclear : C t * sResP P Q k = C s * sResP P Q (j - 1) :=
    sResP_clear_domain P Q hP hQ hpq hjq hj1 hk0 hkdeg
  set A := C t * sResU P Q k - C s * sResU P Q (j - 1) with hA_def
  set B := C t * sResV P Q k - C s * sResV P Q (j - 1) with hB_def
  have hAB : A * P + B * Q = 0 := by
    rw [hA_def, hB_def]; linear_combination C s * hbj + hclear - C t * hbk
  have hA : A = 0 := by
    set f := algebraMap D (FractionRing D) with hf_def
    have hf : Function.Injective f := IsFractionRing.injective D (FractionRing D)
    by_contra hAne
    set AK := A.map f with hAK_def
    set BK := B.map f with hBK_def
    set PK := P.map f with hPK_def
    set QK := Q.map f with hQK_def
    have hAKne : AK ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hAne
    have hPKne : PK ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hP
    have hQKne : QK ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hQ
    have hABK : AK * PK + BK * QK = 0 := by
      have h := congrArg (Polynomial.map f) hAB
      rwa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_zero] at h
    have hdvd : QK ∣ AK * PK := ⟨- BK, by linear_combination hABK⟩
    set g := gcd PK QK with hg_def
    have hgr : g ∣ QK := gcd_dvd_right PK QK
    have hgl : g ∣ PK := gcd_dvd_left PK QK
    have hgne : g ≠ 0 := fun h => hQKne ((gcd_eq_zero_iff PK QK).mp h).2
    -- `deg g ≤ k`, since `g ∣ sResP_{j-1}` (mapped) which is nonzero of degree `k`.
    have hsResPK : sResP PK QK (j - 1) = (sResP P Q (j - 1)).map f := by rw [sResP_map hf]
    have hgsResP : g ∣ sResP PK QK (j - 1) := by
      rw [sResP_eq_cofactor PK QK hQKne
        (by rw [hPK_def, hQK_def, Polynomial.natDegree_map_eq_of_injective hf,
          Polynomial.natDegree_map_eq_of_injective hf]; exact hpq)
        (by rw [hQK_def, Polynomial.natDegree_map_eq_of_injective hf]; exact hjm1q)]
      exact dvd_add (Dvd.dvd.mul_left hgl _) (Dvd.dvd.mul_left hgr _)
    have hsResPKne : sResP PK QK (j - 1) ≠ 0 := by
      rw [hsResPK]; exact (Polynomial.map_ne_zero_iff hf).mpr hk0
    have hgdeg : g.natDegree ≤ k := by
      refine le_trans (Polynomial.natDegree_le_of_dvd hgsResP hsResPKne) ?_
      rw [hsResPK, Polynomial.natDegree_map_eq_of_injective hf, hkdeg]
    -- `Q/g ∣ A`, with `deg(Q/g) ≥ q − k > deg A`.
    have hcop : IsCoprime (PK / g) (QK / g) := isCoprime_div_gcd_div_gcd hQKne
    have hPKfac : PK = g * (PK / g) := (EuclideanDomain.mul_div_cancel' hgne hgl).symm
    have hQKfac : QK = g * (QK / g) := (EuclideanDomain.mul_div_cancel' hgne hgr).symm
    have hdvd2 : QK / g ∣ AK := by
      have h1 : g * (QK / g) ∣ g * (AK * (PK / g)) := by
        rw [← hQKfac]
        calc QK ∣ AK * PK := hdvd
          _ = g * (AK * (PK / g)) := by linear_combination AK * hPKfac
      have h2 : QK / g ∣ AK * (PK / g) := (mul_dvd_mul_iff_left hgne).mp h1
      exact hcop.symm.dvd_of_dvd_mul_right h2
    have hQKgne : QK / g ≠ 0 := by
      intro h; rw [h, mul_zero] at hQKfac; exact hQKne hQKfac
    have hmul : g.natDegree + (QK / g).natDegree = Q.natDegree := by
      rw [← Polynomial.natDegree_mul hgne hQKgne, ← hQKfac, hQK_def,
        Polynomial.natDegree_map_eq_of_injective hf]
    have hAdeg : AK.natDegree ≤ Q.natDegree - 1 - k := by
      rw [hAK_def, Polynomial.natDegree_map_eq_of_injective hf, hA_def]
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (sResU_natDegree_le P Q hpq hkq)
      · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        exact le_trans (sResU_natDegree_le P Q hpq hjm1q) (by omega)
    have := Polynomial.natDegree_le_of_dvd hdvd2 hAKne
    omega
  refine ⟨sub_eq_zero.mp hA, sub_eq_zero.mp ?_⟩
  have hBQ : B * Q = 0 := by rw [hA, zero_mul, zero_add] at hAB; exact hAB
  exact (mul_eq_zero.mp hBQ).resolve_right hQ

/-- **Theorem 8.34 gcd-zeros branch over an integral domain** (descended): if `sResP_{j-1} = 0` then
    `sResP_ℓ = 0` for all `ℓ < j`. -/
theorem theorem_8_34_gcd_zeros_domain {D : Type*} [CommRing D] [IsDomain D] (P Q : D[X])
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hip : i ≤ P.natDegree + 1) (hne : sResP P Q (i - 1) ≠ 0)
    (hdeg : (sResP P Q (i - 1)).natDegree = j) (hzero : sResP P Q (j - 1) = 0) :
    ∀ ℓ, ℓ < j → sResP P Q ℓ = 0 := by
  set f := algebraMap D (FractionRing D) with hf_def
  have hf : Function.Injective f := IsFractionRing.injective D (FractionRing D)
  have hpqK : (Q.map f).natDegree < (P.map f).natDegree := by
    rwa [Polynomial.natDegree_map_eq_of_injective hf, Polynomial.natDegree_map_eq_of_injective hf]
  have hzeroK : sResP (P.map f) (Q.map f) (j - 1) = 0 := by
    rw [sResP_map hf, hzero, Polynomial.map_zero]
  have hkey := (theorem_8_34_monolithic (P.map f) (Q.map f) ((Polynomial.map_ne_zero_iff hf).mpr hP)
    ((Polynomial.map_ne_zero_iff hf).mpr hQ) hpqK (by rwa [Polynomial.natDegree_map_eq_of_injective hf])
    hj1 hji (by rwa [Polynomial.natDegree_map_eq_of_injective hf])
    (by rw [sResP_map hf]; exact (Polynomial.map_ne_zero_iff hf).mpr hne)
    (by rw [sResP_map hf, Polynomial.natDegree_map_eq_of_injective hf]; exact hdeg)).1 hzeroK
  intro ℓ hl
  have h := hkey.2 ℓ hl
  rw [sResP_map hf] at h
  exact (Polynomial.map_eq_zero_iff hf).mp h

/-- **Theorem 8.34 gap-zeros branch over an integral domain** (descended): in a defective block
    (`k = deg sResP_{j-1} < j-1`), `sResP_ℓ = 0` for `k < ℓ < j-1`. -/
theorem theorem_8_34_gap_zeros_domain {D : Type*} [CommRing D] [IsDomain D] (P Q : D[X])
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hip : i ≤ P.natDegree + 1) (hne : sResP P Q (i - 1) ≠ 0)
    (hdeg : (sResP P Q (i - 1)).natDegree = j) {k : ℕ} (hk0 : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hkj : k < j - 1) :
    ∀ ℓ, k < ℓ → ℓ < j - 1 → sResP P Q ℓ = 0 := by
  set f := algebraMap D (FractionRing D) with hf_def
  have hf : Function.Injective f := IsFractionRing.injective D (FractionRing D)
  have hpqK : (Q.map f).natDegree < (P.map f).natDegree := by
    rwa [Polynomial.natDegree_map_eq_of_injective hf, Polynomial.natDegree_map_eq_of_injective hf]
  have hgapK := (((theorem_8_34_monolithic (P.map f) (Q.map f) ((Polynomial.map_ne_zero_iff hf).mpr hP)
    ((Polynomial.map_ne_zero_iff hf).mpr hQ) hpqK (by rwa [Polynomial.natDegree_map_eq_of_injective hf])
    hj1 hji (by rwa [Polynomial.natDegree_map_eq_of_injective hf])
    (by rw [sResP_map hf]; exact (Polynomial.map_ne_zero_iff hf).mpr hne)
    (by rw [sResP_map hf, Polynomial.natDegree_map_eq_of_injective hf]; exact hdeg)).2 k
    (by rw [sResP_map hf]; exact (Polynomial.map_ne_zero_iff hf).mpr hk0)
    (by rw [sResP_map hf, Polynomial.natDegree_map_eq_of_injective hf]; exact hkdeg)).2 hkj).1
  intro ℓ hl1 hl2
  have h := hgapK ℓ hl1 hl2
  rw [sResP_map hf] at h
  exact (Polynomial.map_eq_zero_iff hf).mp h

/-- **The `β_ℓ` proportionality.**  Each nonzero signed remainder is an explicit scalar multiple
    of a signed subresultant polynomial: `Sₗ = C(βₗ) · sResP_{d(ℓ-1)-1}` with
    `βₗ = lcof(Sₗ) / lcof(sResP_{d(ℓ-1)-1})` (Corollary 8.38 + leading-coefficient ratio). -/
theorem SRemS_eq_C_mul_sResP {K : Type*} [Field K] (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ)
    (hℓne : SRemS P Q ℓ ≠ 0) :
    SRemS P Q ℓ
      = C ((SRemS P Q ℓ).leadingCoeff
            / (sResP P Q ((SRemS P Q (ℓ - 1)).natDegree - 1)).leadingCoeff)
        * sResP P Q ((SRemS P Q (ℓ - 1)).natDegree - 1) := by
  have hassoc := (corollary_8_38 P Q hP hQ hpq hq1 hℓ1 hℓne).1
  have hsne : sResP P Q ((SRemS P Q (ℓ - 1)).natDegree - 1) ≠ 0 := fun h => hℓne
    ((associated_zero_iff_eq_zero _).mp (h ▸ hassoc).symm)
  exact eq_C_leadingCoeff_ratio_mul_of_associated hsne hassoc.symm

/-- **Theorem 8.34 recurrence in remainder form.**  In the recurrence setting, the remainder of
    `sResP_{i-1}` by `sResP_{j-1}` is the explicit scalar multiple
    `-(s_j t_{i-1})/(s_k t_{j-1}) · sResP_{k-1}`. -/
theorem sResP_mod_eq {K : Type*} [Field K] (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hip : i ≤ P.natDegree + 1) (hne : sResP P Q (i - 1) ≠ 0)
    (hdeg : (sResP P Q (i - 1)).natDegree = j) {k : ℕ} (hk0 : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hk1 : 1 ≤ k)
    (hstd : sBPR P Q k * tBPR P Q (j - 1) ≠ 0) :
    sResP P Q (i - 1) % sResP P Q (j - 1)
      = -(C ((sBPR P Q j * tBPR P Q (i - 1)) / (sBPR P Q k * tBPR P Q (j - 1)))
          * sResP P Q (k - 1)) := by
  obtain ⟨hrec, _⟩ :=
    (theorem_8_34_monolithic P Q hP hQ hpq hq1 hj1 hji hip hne hdeg).2 k hk0 hkdeg
  rw [if_neg (show ¬ k = 0 by omega)] at hrec
  simp only [← Polynomial.C_mul] at hrec
  rw [rem_C_mul] at hrec
  -- hrec : C(s_j t_{i-1}) sResP_{k-1} = -(C(s_k t_{j-1}) (sResP_{i-1} % sResP_{j-1}))
  have hsc : sBPR P Q k * tBPR P Q (j - 1)
      * (sBPR P Q j * tBPR P Q (i - 1) / (sBPR P Q k * tBPR P Q (j - 1)))
      = sBPR P Q j * tBPR P Q (i - 1) := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hstd]
  apply mul_left_cancel₀ (show (C (sBPR P Q k * tBPR P Q (j - 1)) : K[X]) ≠ 0
    from Polynomial.C_ne_zero.mpr hstd)
  rw [mul_neg, ← mul_assoc, ← Polynomial.C_mul, hsc]
  linear_combination hrec

section SRemSdeg

variable {K : Type*} [Field K] (P Q : K[X])

/-- If `S_{n+1} ≠ 0` then `S_n ≠ 0`. -/
theorem SRemS_ne_pred (hP : P ≠ 0) {n : ℕ} (hn : SRemS P Q (n + 1) ≠ 0) : SRemS P Q n ≠ 0 := by
  intro hn0
  rcases n with _ | n'
  · exact hP (by rw [← SRemS_fst (P := P) (Q := Q)]; exact hn0)
  · exact hn (SRemS_zero_ge P Q n' hn0 (n' + 2) (by omega))

/-- A nonzero signed remainder has all predecessors nonzero. -/
theorem SRemS_ne_of_le (hP : P ≠ 0) {ℓ : ℕ} (hℓ : SRemS P Q ℓ ≠ 0) {m : ℕ} (hm : m ≤ ℓ) :
    SRemS P Q m ≠ 0 := by
  induction ℓ with
  | zero => rwa [Nat.le_zero.mp hm]
  | succ ℓ' ih =>
    rcases Nat.lt_or_ge m (ℓ' + 1) with h | h
    · exact ih (SRemS_ne_pred P Q hP hℓ) (by omega)
    · rw [show m = ℓ' + 1 by omega]; exact hℓ

/-- Degrees in the signed remainder sequence strictly decrease at nonzero steps. -/
theorem SRemS_natDegree_lt (hpq : Q.natDegree < P.natDegree) {n : ℕ}
    (hn : SRemS P Q (n + 1) ≠ 0) :
    (SRemS P Q (n + 1)).natDegree < (SRemS P Q n).natDegree := by
  rcases n with _ | n'
  · rw [SRemS_fst, SRemS_snd]; exact hpq
  · have hn0 : SRemS P Q (n' + 1) ≠ 0 := fun h =>
      hn (SRemS_zero_ge P Q n' h (n' + 2) (by omega))
    have hx : SRemS P Q n' % SRemS P Q (n' + 1) ≠ 0 := fun h =>
      hn (by rw [SRemS_ss P Q n' hn0, h, neg_zero])
    rw [SRemS_ss P Q n' hn0, Polynomial.natDegree_neg]
    exact Polynomial.natDegree_lt_natDegree hx (Polynomial.degree_mod_lt (SRemS P Q n') hn0)

/-- For `n ≥ 1`, a nonzero `S_n` has degree `≤ q`. -/
theorem SRemS_natDegree_le_q (hpq : Q.natDegree < P.natDegree) (hP : P ≠ 0) {n : ℕ}
    (hn : SRemS P Q (n + 1) ≠ 0) : (SRemS P Q (n + 1)).natDegree ≤ Q.natDegree := by
  induction n with
  | zero => rw [SRemS_snd]
  | succ n' ih =>
    have h1 := SRemS_natDegree_lt P Q hpq hn
    have h2 := ih (SRemS_ne_pred P Q hP hn)
    omega

/-- A nonzero signed remainder has degree `≤ p`. -/
theorem SRemS_natDegree_le_p (hpq : Q.natDegree < P.natDegree) (hP : P ≠ 0) {n : ℕ}
    (hn : SRemS P Q n ≠ 0) : (SRemS P Q n).natDegree ≤ P.natDegree := by
  rcases n with _ | n'
  · rw [SRemS_fst]
  · have := SRemS_natDegree_le_q P Q hpq hP hn; omega

end SRemSdeg

/-! ### Connecting the rational `s_j`, `t_j` to bounded integers

Over `ℚ` (with `P = P₀.map (ℤ→ℚ)`), the signed-subresultant coefficients `s_j = sBPR` and
`t_j = tBPR` are *integers* (casts of coefficients of the integer `sResP P₀ Q₀`).  We record this
integer and its bitsize bound (from Proposition 8.48). -/

/-- The integer underlying `s_j` over `ℚ`: the `Xʲ`-coefficient of the integer `sResP_j`
    (with the convention `s_p = 1`). -/
noncomputable def Sℤ (P₀ Q₀ : ℤ[X]) (j : ℕ) : ℤ :=
  if j = P₀.natDegree then 1 else (sResP P₀ Q₀ j).coeff j

/-- The integer underlying `t_m` over `ℚ` (with the convention `t_p = 1`). -/
noncomputable def Tℤ (P₀ Q₀ : ℤ[X]) (m : ℕ) : ℤ :=
  if m = P₀.natDegree then 1 else (sResP P₀ Q₀ m).leadingCoeff

section Sizes

variable (P₀ Q₀ : ℤ[X])

/-- Over `ℚ`, `s_j = sBPR` is the integer `Sℤ` (cast), for `j ≤ q` or `j = p`. -/
theorem sBPR_eq_cast {j : ℕ} (hpq : Q₀.natDegree < P₀.natDegree)
    (hjq : j ≤ Q₀.natDegree ∨ j = P₀.natDegree) :
    sBPR (P₀.map (Int.castRingHom ℚ)) (Q₀.map (Int.castRingHom ℚ)) j = (Sℤ P₀ Q₀ j : ℚ) := by
  have hpm : (P₀.map (Int.castRingHom ℚ)).natDegree = P₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P₀
  have hqm : (Q₀.map (Int.castRingHom ℚ)).natDegree = Q₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective Q₀
  rw [sBPR, hpm, Sℤ]
  rcases hjq with hjq | hjp
  · rw [if_neg (by omega), if_neg (by omega),
      ← coeff_sResP _ _ (by rw [hpm, hqm]; exact hpq) (by rw [hpm]; omega),
      sResP_map Int.cast_injective, Polynomial.coeff_map]
    rfl
  · rw [if_pos hjp, if_pos hjp, Int.cast_one]

/-- Over `ℚ`, `t_m = tBPR` is the integer `Tℤ` (cast), for all `m`. -/
theorem tBPR_eq_cast (m : ℕ) :
    tBPR (P₀.map (Int.castRingHom ℚ)) (Q₀.map (Int.castRingHom ℚ)) m = (Tℤ P₀ Q₀ m : ℚ) := by
  have hpm : (P₀.map (Int.castRingHom ℚ)).natDegree = P₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P₀
  rw [tBPR, hpm, Tℤ]
  by_cases hm : m = P₀.natDegree
  · rw [if_pos hm, if_pos hm, Int.cast_one]
  · rw [if_neg hm, if_neg hm, sResP_map Int.cast_injective, Polynomial.leadingCoeff,
      Polynomial.leadingCoeff, Polynomial.coeff_map,
      Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    rfl

variable {τ : ℕ} (hP : ∀ i, Int.size (P₀.coeff i) ≤ τ) (hQ : ∀ i, Int.size (Q₀.coeff i) ≤ τ)
  (hpq : Q₀.natDegree < P₀.natDegree)

/-- Abbreviation for the per-coefficient bound `B = (p+q)(τ + bit(p+q))`. -/
local notation "B" => (P₀.natDegree + Q₀.natDegree) * (τ + Nat.size (P₀.natDegree + Q₀.natDegree))

include hP hQ hpq in
/-- `Sℤ j` has bitsize `≤ B`, for `j ≤ q` or `j = p` (Proposition 8.48 / convention). -/
theorem Sℤ_size_le {j : ℕ} (hjq : j ≤ Q₀.natDegree ∨ j = P₀.natDegree) :
    Int.size (Sℤ P₀ Q₀ j) ≤ B := by
  rw [Sℤ]
  rcases hjq with hjq | hjp
  · rw [if_neg (by omega)]
    refine le_trans (sResP_coeff_size_le P₀ Q₀ hP hQ hpq hjq j) ?_
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add_left (Nat.size_le_size (by omega)) _)
  · rw [if_pos hjp]
    have hpq1 : 1 ≤ P₀.natDegree + Q₀.natDegree := by omega
    have hsz1 : 1 ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := by
      have : Nat.size (P₀.natDegree + Q₀.natDegree) ≠ 0 := by rw [Ne, Nat.size_eq_zero]; omega
      omega
    have hB1 : 1 ≤ B := by have := Nat.mul_le_mul hpq1 hsz1; simpa using this
    simpa [Int.size] using hB1

include hP hQ hpq in
/-- `Tℤ m` has bitsize `≤ B`, for all `m` (Proposition 8.48 / boundary conventions). -/
theorem Tℤ_size_le (m : ℕ) : Int.size (Tℤ P₀ Q₀ m) ≤ B := by
  have hpq1 : 1 ≤ P₀.natDegree + Q₀.natDegree := by omega
  have hsz1 : 1 ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := by
    have : Nat.size (P₀.natDegree + Q₀.natDegree) ≠ 0 := by rw [Ne, Nat.size_eq_zero]; omega
    omega
  have hB1 : 1 ≤ B := by
    have := Nat.mul_le_mul hpq1 hsz1; simpa using this
  have hτB : τ ≤ B := by
    calc τ ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := Nat.le_add_right _ _
    _ = 1 * (τ + Nat.size (P₀.natDegree + Q₀.natDegree)) := (one_mul _).symm
    _ ≤ B := Nat.mul_le_mul hpq1 le_rfl
  rw [Tℤ]
  by_cases hm : m = P₀.natDegree
  · rw [if_pos hm]; simpa [Int.size] using hB1
  · rw [if_neg hm]
    by_cases hmq : m ≤ Q₀.natDegree
    · -- determinant range: leadingCoeff is a coefficient, use Prop 8.48
      rw [Polynomial.leadingCoeff]
      exact le_trans (sResP_coeff_size_le P₀ Q₀ hP hQ hpq hmq _)
        (Nat.mul_le_mul (by omega) (Nat.add_le_add_left (Nat.size_le_size (by omega)) _))
    · by_cases hmp1 : m = P₀.natDegree - 1
      · rcases Nat.lt_or_ge (Q₀.natDegree + 1) P₀.natDegree with hgap | hgap
        · -- proper gap: sResP_{p-1} = Q, leadingCoeff(Q) ≤ τ ≤ B
          subst hmp1
          rw [sResP_eq_self_Q P₀ Q₀ hgap, Polynomial.leadingCoeff]
          exact le_trans (hQ _) hτB
        · omega
      · rw [sResP_eq_zero P₀ Q₀ (by omega) hm hmp1, Polynomial.leadingCoeff_zero]
        simp [Int.size]

end Sizes

/-! ### The main induction

Each nonzero signed remainder over `ℚ` is `C(N/D) · sResP_{m}` with integer `N, D` of bitsize
`≤ 1 + ℓ·B`, where `m = mIdx ℓ`. -/

section MainInduction

variable (P₀ Q₀ : ℤ[X]) {τ : ℕ}
  (hP : ∀ i, Int.size (P₀.coeff i) ≤ τ) (hQ : ∀ i, Int.size (Q₀.coeff i) ≤ τ)
  (hpq0 : Q₀.natDegree < P₀.natDegree) (hq1 : 1 ≤ Q₀.natDegree)

local notation "B" => (P₀.natDegree + Q₀.natDegree) * (τ + Nat.size (P₀.natDegree + Q₀.natDegree))

include hP hQ hpq0 hq1 in
/-- **Main induction for Theorem 8.51.**  Each nonzero signed remainder `S_ℓ` over `ℚ` is
    `C(N/D) · sResP_{mIdx ℓ}` for integers `N, D` (`D ≠ 0`) with `bit(N), bit(D) ≤ 1 + ℓ·B`. -/
theorem SRemS_eq_divInt (ℓ : ℕ) (hℓne : SRemS (mapQ P₀) (mapQ Q₀) ℓ ≠ 0) :
    ∃ N D : ℤ, D ≠ 0 ∧ Int.size N ≤ 1 + ℓ * B ∧ Int.size D ≤ 1 + ℓ * B
      ∧ SRemS (mapQ P₀) (mapQ Q₀) ℓ
        = C ((N : ℚ) / (D : ℚ))
          * sResP (mapQ P₀) (mapQ Q₀)
              (if ℓ = 0 then P₀.natDegree
               else (SRemS (mapQ P₀) (mapQ Q₀) (ℓ - 1)).natDegree - 1) := by
  have hP₀ : P₀ ≠ 0 := by rintro rfl; simp at hpq0
  have hQ₀ : Q₀ ≠ 0 := by rintro rfl; simp at hq1
  have hpdm : (mapQ P₀).natDegree = P₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P₀
  have hqdm : (mapQ Q₀).natDegree = Q₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective Q₀
  have hPm : mapQ P₀ ≠ 0 := by intro h; rw [h] at hpdm; simp at hpdm; omega
  have hQm : mapQ Q₀ ≠ 0 := by intro h; rw [h] at hqdm; simp at hqdm; omega
  have hpqm : (mapQ Q₀).natDegree < (mapQ P₀).natDegree := by rw [hpdm, hqdm]; exact hpq0
  have hq1m : 1 ≤ (mapQ Q₀).natDegree := by rw [hqdm]; exact hq1
  suffices key : ∀ N : ℕ, SRemS (mapQ P₀) (mapQ Q₀) N ≠ 0 →
      ∃ NN DD : ℤ, DD ≠ 0 ∧ Int.size NN ≤ 1 + N * B ∧ Int.size DD ≤ 1 + N * B
        ∧ SRemS (mapQ P₀) (mapQ Q₀) N
          = C ((NN : ℚ) / (DD : ℚ))
            * sResP (mapQ P₀) (mapQ Q₀)
                (if N = 0 then P₀.natDegree
                 else (SRemS (mapQ P₀) (mapQ Q₀) (N - 1)).natDegree - 1) from key ℓ hℓne
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hNne
  have hτB : τ ≤ B := by
    calc τ ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := Nat.le_add_right _ _
    _ = 1 * (τ + Nat.size (P₀.natDegree + Q₀.natDegree)) := (one_mul _).symm
    _ ≤ B := Nat.mul_le_mul (by omega) le_rfl
  rcases N with _ | _ | m
  · -- N = 0 : S₀ = P = sResP_p
    refine ⟨1, 1, one_ne_zero, by simp [Int.size], by simp [Int.size], ?_⟩
    rw [if_pos rfl, SRemS_fst, show P₀.natDegree = (mapQ P₀).natDegree from hpdm.symm,
      sResP_eq_self _ _ hpqm, Int.cast_one, div_one, map_one, one_mul]
  · -- N = 1 : S₁ = Q = C(lcof Q / lcof sResP_{p-1}) · sResP_{p-1}
    have hb_idx : ((SRemS (mapQ P₀) (mapQ Q₀) (1 - 1)).natDegree - 1)
        = (mapQ P₀).natDegree - 1 := by rw [Nat.sub_self, SRemS_fst]
    have heq := SRemS_eq_C_mul_sResP (mapQ P₀) (mapQ Q₀) hPm hQm hpqm hq1m (ℓ := 1) le_rfl hNne
    rw [hb_idx] at heq ⊢
    have hbne : sResP (mapQ P₀) (mapQ Q₀) ((mapQ P₀).natDegree - 1) ≠ 0 := by
      intro h; apply hNne; rw [heq, h, mul_zero]
    refine ⟨Q₀.leadingCoeff, Tℤ P₀ Q₀ (P₀.natDegree - 1), ?_, ?_, ?_, ?_⟩
    · -- D ≠ 0
      rw [Tℤ, if_neg (by omega), Ne, Polynomial.leadingCoeff_eq_zero]
      intro h; apply hbne
      rw [hpdm, sResP_map Int.cast_injective, h, Polynomial.map_zero]
    · have h1 : Int.size Q₀.leadingCoeff ≤ τ := by rw [Polynomial.leadingCoeff]; exact hQ _
      have hb : (0 + 1) * B = B := by ring
      rw [hb]; omega
    · have hb : (0 + 1) * B = B := by ring
      rw [hb]; exact le_trans (Tℤ_size_le P₀ Q₀ hP hQ hpq0 (P₀.natDegree - 1)) (by omega)
    · have e1 : (mapQ Q₀).leadingCoeff = (Q₀.leadingCoeff : ℚ) := by
        simp only [Polynomial.leadingCoeff]; rw [Polynomial.coeff_map, hqdm]; rfl
      have e2 : (sResP (mapQ P₀) (mapQ Q₀) ((mapQ P₀).natDegree - 1)).leadingCoeff
          = (Tℤ P₀ Q₀ (P₀.natDegree - 1) : ℚ) := by
        rw [Tℤ, if_neg (show P₀.natDegree - 1 ≠ P₀.natDegree by omega), hpdm,
          sResP_map Int.cast_injective, Polynomial.leadingCoeff, Polynomial.leadingCoeff,
          Polynomial.coeff_map, Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
        rfl
      rw [if_neg (by omega), heq, SRemS_snd, e1, e2]
  · -- N = m + 2 (inductive step)
    rw [if_neg (by omega)]
    simp only [Nat.add_sub_cancel]
    -- predecessors nonzero
    have hSm1ne : SRemS (mapQ P₀) (mapQ Q₀) (m + 1) ≠ 0 := SRemS_ne_pred _ _ hPm hNne
    have hSmne : SRemS (mapQ P₀) (mapQ Q₀) m ≠ 0 := SRemS_ne_pred _ _ hPm hSm1ne
    -- IH at m
    obtain ⟨N₂, D₂, hD₂ne, hN₂sz, hD₂sz, hSm_eq⟩ := ih m (by omega) hSmne
    -- proportionality of S_{m+1}
    have hSm1_eq := SRemS_eq_C_mul_sResP (mapQ P₀) (mapQ Q₀) hPm hQm hpqm hq1m
      (ℓ := m + 1) (by omega) hSm1ne
    simp only [Nat.add_sub_cancel] at hSm1_eq
    -- name the indices
    set a := (if m = 0 then P₀.natDegree
              else (SRemS (mapQ P₀) (mapQ Q₀) (m - 1)).natDegree - 1) with ha_def
    set J := (SRemS (mapQ P₀) (mapQ Q₀) m).natDegree with hJ_def
    set K := (SRemS (mapQ P₀) (mapQ Q₀) (m + 1)).natDegree with hK_def
    -- facts about sResP a (from hSm_eq)
    have hc₂ne : ((N₂ : ℚ) / (D₂ : ℚ)) ≠ 0 :=
      fun h => hSmne (by rw [hSm_eq, h, map_zero, zero_mul])
    have hsResPa_ne : sResP (mapQ P₀) (mapQ Q₀) a ≠ 0 :=
      fun h => hSmne (by rw [hSm_eq, h, mul_zero])
    have hdeg_a : (sResP (mapQ P₀) (mapQ Q₀) a).natDegree = J := by
      rw [hJ_def, hSm_eq, Polynomial.natDegree_C_mul hc₂ne]
    -- facts about sResP (J-1) (from hSm1_eq)
    have hsResPb_ne : sResP (mapQ P₀) (mapQ Q₀) (J - 1) ≠ 0 :=
      fun h => hSm1ne (by rw [hSm1_eq, h, mul_zero])
    have hc₁ne : ((SRemS (mapQ P₀) (mapQ Q₀) (m + 1)).leadingCoeff
        / (sResP (mapQ P₀) (mapQ Q₀) (J - 1)).leadingCoeff) ≠ 0 :=
      div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hSm1ne)
        (Polynomial.leadingCoeff_ne_zero.mpr hsResPb_ne)
    have hdeg_b : (sResP (mapQ P₀) (mapQ Q₀) (J - 1)).natDegree = K := by
      rw [hK_def, hSm1_eq, Polynomial.natDegree_C_mul hc₁ne]
    -- degree bookkeeping
    have hK_le_qm : K ≤ (mapQ Q₀).natDegree := by
      rw [hK_def]; exact SRemS_natDegree_le_q (mapQ P₀) (mapQ Q₀) hpqm hPm hSm1ne
    have hK_le_q : K ≤ Q₀.natDegree := by rw [← hqdm]; exact hK_le_qm
    have hJ_cases : J ≤ Q₀.natDegree ∨ J = P₀.natDegree := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · right; rw [hJ_def, hm0, SRemS_fst, hpdm]
      · left
        have hSm_1ne : SRemS (mapQ P₀) (mapQ Q₀) (m - 1) ≠ 0 :=
          SRemS_ne_of_le (mapQ P₀) (mapQ Q₀) hPm hSmne (by omega)
        have hlt := SRemS_natDegree_lt (mapQ P₀) (mapQ Q₀) hpqm
          (n := m - 1) (by rwa [Nat.sub_add_cancel hmpos])
        have hle := SRemS_natDegree_le_q (mapQ P₀) (mapQ Q₀) hpqm hPm
          (n := m - 1) (by rwa [Nat.sub_add_cancel hmpos])
        rw [Nat.sub_add_cancel hmpos] at hlt hle
        rw [hJ_def]; omega
    have hJ_le_p : J ≤ P₀.natDegree := by rcases hJ_cases with h | h <;> omega
    have hJ_pos : 1 ≤ J := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [hJ_def, hm0, SRemS_fst, hpdm]; omega
      · by_contra hcon
        have hunit : IsUnit (SRemS (mapQ P₀) (mapQ Q₀) m) :=
          Polynomial.isUnit_iff_degree_eq_zero.mpr (by
            rw [Polynomial.degree_eq_natDegree hSmne, ← hJ_def]; norm_cast; omega)
        apply hSm1ne
        have hmm : m + 1 = (m - 1) + 2 := by omega
        rw [hmm, SRemS_ss (mapQ P₀) (mapQ Q₀) (m - 1) (by rwa [Nat.sub_add_cancel hmpos]),
          Nat.sub_add_cancel hmpos, EuclideanDomain.mod_eq_zero.mpr hunit.dvd, neg_zero]
    have hK_pos : 1 ≤ K := by
      by_contra hcon
      have hunit : IsUnit (SRemS (mapQ P₀) (mapQ Q₀) (m + 1)) :=
        Polynomial.isUnit_iff_degree_eq_zero.mpr (by
          rw [Polynomial.degree_eq_natDegree hSm1ne, ← hK_def]; norm_cast; omega)
      apply hNne
      rw [SRemS_ss (mapQ P₀) (mapQ Q₀) m hSm1ne, EuclideanDomain.mod_eq_zero.mpr hunit.dvd, neg_zero]
    have ha_le_J : J ≤ a := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [ha_def, hm0, if_pos rfl, hJ_def, hm0, SRemS_fst, hpdm]
      · rw [ha_def, if_neg (by omega)]
        have hSm_1ne : SRemS (mapQ P₀) (mapQ Q₀) (m - 1) ≠ 0 :=
          SRemS_ne_of_le (mapQ P₀) (mapQ Q₀) hPm hSmne (by omega)
        have hlt := SRemS_natDegree_lt (mapQ P₀) (mapQ Q₀) hpqm
          (n := m - 1) (by rwa [Nat.sub_add_cancel hmpos])
        rw [Nat.sub_add_cancel hmpos] at hlt
        rw [hJ_def]; omega
    have ha_le_p : a ≤ P₀.natDegree := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [ha_def, hm0, if_pos rfl]
      · rw [ha_def, if_neg (by omega)]
        have hSm_1ne : SRemS (mapQ P₀) (mapQ Q₀) (m - 1) ≠ 0 :=
          SRemS_ne_of_le (mapQ P₀) (mapQ Q₀) hPm hSmne (by omega)
        have := SRemS_natDegree_le_p (mapQ P₀) (mapQ Q₀) hpqm hPm hSm_1ne
        rw [hpdm] at this; omega
    -- non-defectiveness at K (Corollary 8.38, part 2) ⟹ s_K ≠ 0
    have hcor := (corollary_8_38 (mapQ P₀) (mapQ Q₀) hPm hQm hpqm hq1m
      (ℓ := m + 1) (by omega) hSm1ne).2
    rw [← hK_def] at hcor
    have hsResPK_ne : sResP (mapQ P₀) (mapQ Q₀) K ≠ 0 :=
      fun h => hSm1ne (hcor.eq_zero_iff.mp h)
    have hdeg_K : (sResP (mapQ P₀) (mapQ Q₀) K).natDegree = K := by
      have := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hcor)
      rw [← hK_def] at this; exact this
    have hsBPRK_ne : sBPR (mapQ P₀) (mapQ Q₀) K ≠ 0 :=
      sBPR_ne_of_nondef (mapQ P₀) (mapQ Q₀) hpqm hK_le_qm hsResPK_ne hdeg_K
    have htBPRb_ne : tBPR (mapQ P₀) (mapQ Q₀) (J - 1) ≠ 0 :=
      tBPR_ne_of_ne (mapQ P₀) (mapQ Q₀) (by rw [hpdm]; omega) hsResPb_ne
    have hstd : sBPR (mapQ P₀) (mapQ Q₀) K * tBPR (mapQ P₀) (mapQ Q₀) (J - 1) ≠ 0 :=
      mul_ne_zero hsBPRK_ne htBPRb_ne
    -- cast bridges
    have es_J : sBPR (mapQ P₀) (mapQ Q₀) J = (Sℤ P₀ Q₀ J : ℚ) := sBPR_eq_cast P₀ Q₀ hpq0 hJ_cases
    have et_a : tBPR (mapQ P₀) (mapQ Q₀) a = (Tℤ P₀ Q₀ a : ℚ) := tBPR_eq_cast P₀ Q₀ a
    have es_K : sBPR (mapQ P₀) (mapQ Q₀) K = (Sℤ P₀ Q₀ K : ℚ) :=
      sBPR_eq_cast P₀ Q₀ hpq0 (Or.inl hK_le_q)
    have et_b : tBPR (mapQ P₀) (mapQ Q₀) (J - 1) = (Tℤ P₀ Q₀ (J - 1) : ℚ) := tBPR_eq_cast P₀ Q₀ _
    -- the remainder identity (Theorem 8.34 recurrence)
    have heq_mod := sResP_mod_eq (mapQ P₀) (mapQ Q₀) hPm hQm hpqm hq1m
      (i := a + 1) (j := J) hJ_pos (by omega) (by rw [hpdm]; omega) hsResPa_ne hdeg_a
      hsResPb_ne hdeg_b hK_pos hstd
    simp only [Nat.add_sub_cancel] at heq_mod
    -- nonzero witnesses for D
    have hSℤKne : Sℤ P₀ Q₀ K ≠ 0 := by
      have : (Sℤ P₀ Q₀ K : ℚ) ≠ 0 := es_K ▸ hsBPRK_ne; exact_mod_cast this
    have hTℤbne : Tℤ P₀ Q₀ (J - 1) ≠ 0 := by
      have : (Tℤ P₀ Q₀ (J - 1) : ℚ) ≠ 0 := et_b ▸ htBPRb_ne; exact_mod_cast this
    refine ⟨N₂ * Sℤ P₀ Q₀ J * Tℤ P₀ Q₀ a, D₂ * Sℤ P₀ Q₀ K * Tℤ P₀ Q₀ (J - 1),
      mul_ne_zero (mul_ne_zero hD₂ne hSℤKne) hTℤbne, ?_, ?_, ?_⟩
    · -- size of N
      have hexp : 1 + (m + 2) * B = (1 + m * B) + B + B := by ring
      have h1 := int_size_mul_le (N₂ * Sℤ P₀ Q₀ J) (Tℤ P₀ Q₀ a)
      have h2 := int_size_mul_le N₂ (Sℤ P₀ Q₀ J)
      have h3 := Sℤ_size_le P₀ Q₀ hP hQ hpq0 hJ_cases
      have h4 := Tℤ_size_le P₀ Q₀ hP hQ hpq0 a
      rw [hexp]; omega
    · -- size of D
      have hexp : 1 + (m + 2) * B = (1 + m * B) + B + B := by ring
      have h1 := int_size_mul_le (D₂ * Sℤ P₀ Q₀ K) (Tℤ P₀ Q₀ (J - 1))
      have h2 := int_size_mul_le D₂ (Sℤ P₀ Q₀ K)
      have h3 := Sℤ_size_le P₀ Q₀ hP hQ hpq0 (Or.inl hK_le_q)
      have h4 := Tℤ_size_le P₀ Q₀ hP hQ hpq0 (J - 1)
      rw [hexp]; omega
    · -- the equation
      have hscalar : ((N₂ : ℚ) / (D₂ : ℚ))
          * (((Sℤ P₀ Q₀ J : ℚ) * (Tℤ P₀ Q₀ a : ℚ))
              / ((Sℤ P₀ Q₀ K : ℚ) * (Tℤ P₀ Q₀ (J - 1) : ℚ)))
          = ((N₂ * Sℤ P₀ Q₀ J * Tℤ P₀ Q₀ a : ℤ) : ℚ)
            / ((D₂ * Sℤ P₀ Q₀ K * Tℤ P₀ Q₀ (J - 1) : ℤ) : ℚ) := by
        push_cast; ring
      rw [SRemS_ss (mapQ P₀) (mapQ Q₀) m hSm1ne, hSm_eq, hSm1_eq, rem_C_mul,
        mod_C_mul_right _ _ hc₁ne, heq_mod, es_J, et_a, es_K, et_b,
        mul_neg, neg_neg, ← mul_assoc, ← Polynomial.C_mul, hscalar]

include hP hQ hpq0 hq1 in
/-- **BPR Theorem 8.51 (size of signed remainders).**  For `P, Q ∈ ℤ[X]` of degrees `p, q < p`
    with coefficients of bitsize `≤ τ`, the numerator and denominator of every coefficient of the
    signed remainder sequence (over `ℚ`) have bitsizes bounded (with `B = (p+q)(τ + bit(p+q))`) by
    `(q+2)B + 1` and `(q+1)B + 1` respectively (an honest tightening of BPR's `(p+q)(q+1)(τ +
    bit(p+q)) + τ`). -/
theorem theorem_8_51 (ℓ : ℕ) (hℓ : ℓ ≤ Q₀.natDegree + 1) (a : ℕ) :
    Int.size ((SRemS (mapQ P₀) (mapQ Q₀) ℓ).coeff a).num ≤ (Q₀.natDegree + 2) * B + 1
      ∧ Nat.size ((SRemS (mapQ P₀) (mapQ Q₀) ℓ).coeff a).den ≤ (Q₀.natDegree + 1) * B + 1 := by
  have hpdm : (mapQ P₀).natDegree = P₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P₀
  have hqdm : (mapQ Q₀).natDegree = Q₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective Q₀
  have hPm : mapQ P₀ ≠ 0 := by intro h; rw [h] at hpdm; simp at hpdm; omega
  have hpqm : (mapQ Q₀).natDegree < (mapQ P₀).natDegree := by rw [hpdm, hqdm]; exact hpq0
  have hB1 : 1 ≤ B := by
    have h2 : 1 ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := by
      have : Nat.size (P₀.natDegree + Q₀.natDegree) ≠ 0 := by rw [Ne, Nat.size_eq_zero]; omega
      omega
    have := Nat.mul_le_mul (show 1 ≤ P₀.natDegree + Q₀.natDegree by omega) h2; simpa using this
  have hτB : τ ≤ B := by
    calc τ ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := Nat.le_add_right _ _
    _ = 1 * (τ + Nat.size (P₀.natDegree + Q₀.natDegree)) := (one_mul _).symm
    _ ≤ B := Nat.mul_le_mul (by omega) le_rfl
  have hmono2 : B ≤ (Q₀.natDegree + 2) * B := Nat.le_mul_of_pos_left B (by omega)
  have hmono1 : B ≤ (Q₀.natDegree + 1) * B := Nat.le_mul_of_pos_left B (by omega)
  have hsize1 : Nat.size 1 ≤ 1 := Nat.size_le.mpr (by norm_num)
  by_cases hℓne : SRemS (mapQ P₀) (mapQ Q₀) ℓ = 0
  · rw [hℓne, Polynomial.coeff_zero]
    refine ⟨by rw [Rat.num_zero]; simp [Int.size], ?_⟩
    rw [Rat.den_zero]; omega
  · rcases ℓ with _ | _ | ℓ'
    · -- ℓ = 0 : coeff of P
      rw [SRemS_fst, Polynomial.coeff_map]
      simp only [eq_intCast, Rat.num_intCast, Rat.den_intCast]
      exact ⟨by have := hP a; omega, by omega⟩
    · -- ℓ = 1 : coeff of Q
      rw [SRemS_snd, Polynomial.coeff_map]
      simp only [eq_intCast, Rat.num_intCast, Rat.den_intCast]
      exact ⟨by have := hQ a; omega, by omega⟩
    · -- ℓ = ℓ' + 2
      obtain ⟨N, D, hDne, hNsz, hDsz, hSeq⟩ :=
        SRemS_eq_divInt P₀ Q₀ hP hQ hpq0 hq1 (ℓ' + 1 + 1) hℓne
      rw [if_neg (by omega)] at hSeq
      simp only [Nat.add_sub_cancel] at hSeq
      have hSm1ne : SRemS (mapQ P₀) (mapQ Q₀) (ℓ' + 1) ≠ 0 :=
        SRemS_ne_of_le (mapQ P₀) (mapQ Q₀) hPm hℓne (by omega)
      set mIdx := (SRemS (mapQ P₀) (mapQ Q₀) (ℓ' + 1)).natDegree - 1 with hmIdx_def
      have hmIdx_le : mIdx ≤ Q₀.natDegree := by
        rw [hmIdx_def, ← hqdm]
        have := SRemS_natDegree_le_q (mapQ P₀) (mapQ Q₀) hpqm hPm hSm1ne; omega
      have hIa : Int.size ((sResP P₀ Q₀ mIdx).coeff a) ≤ B :=
        le_trans (sResP_coeff_size_le P₀ Q₀ hP hQ hpq0 hmIdx_le a)
          (Nat.mul_le_mul (by omega) (Nat.add_le_add_left (Nat.size_le_size (by omega)) _))
      have hcoeff : (SRemS (mapQ P₀) (mapQ Q₀) (ℓ' + 1 + 1)).coeff a
          = Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D := by
        rw [hSeq, Polynomial.coeff_C_mul, sResP_map Int.cast_injective, Polynomial.coeff_map]
        simp only [eq_intCast, Rat.divInt_eq_div]; push_cast; ring
      rw [hcoeff]
      have hNmono : Int.size N ≤ 1 + (Q₀.natDegree + 1) * B := by
        refine le_trans hNsz ?_
        have : (ℓ' + 1 + 1) * B ≤ (Q₀.natDegree + 1) * B := Nat.mul_le_mul (by omega) le_rfl
        omega
      have hDmono : Int.size D ≤ 1 + (Q₀.natDegree + 1) * B := by
        refine le_trans hDsz ?_
        have : (ℓ' + 1 + 1) * B ≤ (Q₀.natDegree + 1) * B := Nat.mul_le_mul (by omega) le_rfl
        omega
      refine ⟨?_, ?_⟩
      · have hnum : Int.size (Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D).num
            ≤ Int.size (N * (sResP P₀ Q₀ mIdx).coeff a) := by
          rcases eq_or_ne (N * (sResP P₀ Q₀ mIdx).coeff a) 0 with h0 | h0
          · rw [h0, Rat.zero_divInt]; simp [Int.size]
          · exact int_size_dvd_le h0 (Rat.num_dvd _ hDne)
        have hmul := int_size_mul_le N ((sResP P₀ Q₀ mIdx).coeff a)
        have hexp : (Q₀.natDegree + 2) * B + 1 = (1 + (Q₀.natDegree + 1) * B) + B := by ring
        rw [hexp]; omega
      · have hden : ((Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D).den : ℤ) ∣ D :=
          Rat.den_dvd _ _
        have hdd : (Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D).den ∣ D.natAbs := by
          have := Int.natAbs_dvd_natAbs.mpr hden; simpa using this
        have hle : (Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D).den ≤ D.natAbs :=
          Nat.le_of_dvd (Int.natAbs_pos.mpr hDne) hdd
        have hsz : Nat.size (Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D).den
            ≤ Int.size D := Nat.size_le_size hle
        omega

end MainInduction

end Azurite.BPR.Chapter8
