import Azurite.AzPolynomial.Equiv.Gcd
import Azurite.AzPolynomial.Equiv.Content
import Azurite.AzPolynomial.Equiv.SignedSubresultantBoundary
import Azurite.BasuPollackRoy.Chapter10.Section10_1.Proposition_10_14
import Azurite.AzPolynomial.Equiv.Neg
import Azurite.AzInt.Equiv.RingEquiv
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Correctness of `gcdNormalizedInt`: equivalence with the `ℤ[X]` gcd

**`map_toPoly_gcdNormalizedInt`** — for all `P, Q : AzPolynomial AzInt`,

  `(toPoly (gcdNormalizedInt P Q)).map ι = gcd ((toPoly P).map ι) ((toPoly Q).map ι)`

in `ℤ[X]` with Mathlib's `NormalizedGCDMonoid` gcd, where `ι` is the
`AzInt → ℤ` coefficient hom.

Proof architecture: the normalized `ℤ[X]` gcd is characterized
(`int_gcd_eq`) as `C d · G` where `d = gcd(cont A, cont B)` and `G` is
primitive with positive leading coefficient and `ℚ[X]`-associated to the
rational gcd — divisibility both ways splits into the content part (integer
gcd) and the primitive part (Gauss descent,
`IsPrimitive.dvd_of_fraction_map_dvd_fraction_map`). Each branch of
`gcdNormalizedInt` produces exactly such a pair: `d` from the computable
contents (`content_toPoly`), and `G` from `primPos` of the subresultant core
(`primPos_spec`), whose `ℚ[X]`-association to the rational gcd comes from
the `AzInt`-level Algorithm 8.21 bridge transported along `sResP_map`
(`subresGcd_int_qassoc`); the `p = q` pre-step is invisible over `ℚ`
(`gcd_pre_step`).
-/

namespace Azurite.AzPolynomial

open Polynomial

attribute [local instance 0] Azurite.BPR.gcdMonoidPolynomial

/-! ### Small bridges: signs, contents, `primPos`, `signNorm` -/

private theorem toInt_ne_zero {z : AzInt} (hz : z ≠ 0) : z.toInt ≠ 0 :=
  fun h => hz (Azurite.AzInt.ringEquivInt.injective (by simpa using h))

private theorem toInt_pos_iff_sign {z : AzInt} (hz : z ≠ 0) :
    (0 < z.toInt ↔ z.sign = true) := by
  have h0 := toInt_ne_zero hz
  rw [Azurite.AzInt.toInt] at h0 ⊢
  rcases hs : z.sign with _ | _ <;> rw [hs] at h0 <;> simp at h0 ⊢
  all_goals omega

/-- `AzInt` divisibility along the ring equivalence. -/
private theorem azInt_dvd_of_toInt_dvd {a b : AzInt} (h : a.toInt ∣ b.toInt) :
    a ∣ b := by
  obtain ⟨c, hc⟩ := h
  refine ⟨Azurite.AzInt.ringEquivInt.symm c, Azurite.AzInt.ringEquivInt.injective ?_⟩
  rw [map_mul]
  simpa using hc

private theorem toInt_azNatToAzInt (n : AzNat) :
    (azNatToAzInt n).toInt = (n.toNat : ℤ) := rfl

/-- Content of the represented `ℤ[X]` polynomial is nonzero for `g ≠ 0`. -/
private theorem content_map_ne_zero {g : AzPolynomial AzInt} (hg : g ≠ 0) :
    ((AzPolynomial.toPoly g).map AzInt.toIntRingHom).content ≠ 0 := by
  rw [Ne, Polynomial.content_eq_zero_iff, Polynomial.map_eq_zero_iff
    (fun a b h => Azurite.AzInt.ringEquivInt.injective (by simpa using h))]
  exact fun h => hg (toPoly_inj.mp (h.trans toPoly_zero.symm))

private theorem computable_content_ne_zero {g : AzPolynomial AzInt} (hg : g ≠ 0) :
    (g.content.toNat : ℤ) ≠ 0 := by
  rw [← content_toPoly]
  exact content_map_ne_zero hg

/-- Leading coefficient of the represented polynomial. -/
private theorem leadingCoeff_map_toPoly (p : AzPolynomial AzInt) :
    ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).leadingCoeff
      = (p.leadingCoeff).toInt := by
  have hinj : Function.Injective (AzInt.toIntRingHom) :=
    fun a b h => Azurite.AzInt.ringEquivInt.injective (by simpa using h)
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.coeff_map, ← Polynomial.leadingCoeff, leadingCoeff_toPoly]
  rfl

/-- `normalize` fixes `ℤ[X]` polynomials with positive leading coefficient. -/
private theorem normalize_eq_self_of_pos_lcof {p : ℤ[X]} (hp : 0 < p.leadingCoeff) :
    _root_.normalize p = p := by
  have h1 : _root_.normalize p.leadingCoeff = p.leadingCoeff := by
    rw [← Int.abs_eq_normalize, abs_of_pos hp]
  have h2 : (normUnit p.leadingCoeff : ℤ) = 1 := by
    have h3 := h1
    rw [normalize_apply] at h3
    have h4 : p.leadingCoeff * ↑(normUnit p.leadingCoeff) - p.leadingCoeff * 1 = 0 := by
      rw [mul_one, h3, sub_self]
    rw [← mul_sub] at h4
    have h5 := mul_eq_zero.mp h4
    rcases h5 with h5 | h5
    · exact absurd h5 (by omega)
    · omega
  rw [normalize_apply, Polynomial.coe_normUnit, h2, Polynomial.C_1, mul_one]

/-- The `primPos` specification: a nonzero constant multiple relation with
the input, primitivity, and positive leading coefficient. -/
private theorem primPos_spec {g : AzPolynomial AzInt} (hg : g ≠ 0) :
    ∃ c : ℤ, c ≠ 0
      ∧ Polynomial.C c * ((AzPolynomial.toPoly (primPos g)).map AzInt.toIntRingHom)
          = (AzPolynomial.toPoly g).map AzInt.toIntRingHom
      ∧ ((AzPolynomial.toPoly (primPos g)).map AzInt.toIntRingHom).IsPrimitive
      ∧ 0 < ((AzPolynomial.toPoly (primPos g)).map AzInt.toIntRingHom).leadingCoeff := by
  classical
  set s : AzInt := if g.leadingCoeff.sign then azNatToAzInt g.content
    else -azNatToAzInt g.content with hs
  set gZ : ℤ[X] := (AzPolynomial.toPoly g).map AzInt.toIntRingHom with hgZ
  have hcont0 : (g.content.toNat : ℤ) ≠ 0 := computable_content_ne_zero hg
  have hsZ : s.toInt = if g.leadingCoeff.sign then (g.content.toNat : ℤ)
      else -(g.content.toNat : ℤ) := by
    rw [hs]
    split <;> simp [toInt_azNatToAzInt]
  have hs0 : s.toInt ≠ 0 := by
    rw [hsZ]
    split <;> omega
  have hsabs : |s.toInt| = (g.content.toNat : ℤ) := by
    rw [hsZ]
    split
    · exact abs_of_nonneg (Int.natCast_nonneg _)
    · rw [abs_neg]
      exact abs_of_nonneg (Int.natCast_nonneg _)
  -- `s` divides every coefficient of `g` (the content does, in `ℤ`)
  have hdvd : ∀ i, s ∣ g.coeff i := by
    intro i
    apply azInt_dvd_of_toInt_dvd
    have h1 : gZ.content ∣ gZ.coeff i := gZ.content_dvd_coeff i
    rw [hgZ, content_toPoly] at h1
    have h2 : (g.coeff i).toInt = gZ.coeff i := by
      rw [hgZ, Polynomial.coeff_map, coeff_toPoly]; rfl
    rw [h2]
    rw [hsZ]
    split
    · exact h1
    · exact (neg_dvd).mpr h1
  -- the exact-division identity, mapped to `ℤ[X]`
  have hsne : s ≠ 0 := fun h => hs0 (by rw [h]; rfl)
  have hkey : Polynomial.C s * AzPolynomial.toPoly (primPos g) = AzPolynomial.toPoly g := by
    rw [primPos]
    exact C_mul_toPoly_divByRingElt s hsne g hdvd
  have hkeyZ : Polynomial.C s.toInt
      * ((AzPolynomial.toPoly (primPos g)).map AzInt.toIntRingHom) = gZ := by
    have h := congrArg (Polynomial.map (AzInt.toIntRingHom)) hkey
    rw [Polynomial.map_mul, Polynomial.map_C] at h
    exact h
  refine ⟨s.toInt, hs0, hkeyZ, ?_, ?_⟩
  · -- primitivity: `|s| · content(primPos) = content g = |s|`
    have h1 := congrArg Polynomial.content hkeyZ
    rw [Polynomial.content_C_mul, hgZ, content_toPoly, content_toPoly,
      ← Int.abs_eq_normalize, hsabs] at h1
    rw [Polynomial.isPrimitive_iff_content_eq_one, content_toPoly]
    have h3 : (g.content.toNat : ℤ) * (((primPos g).content.toNat : ℤ) - 1) = 0 := by
      rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hcont0
    · omega
  · -- positive leading coefficient, by the sign choice
    have hlcg : g.leadingCoeff ≠ 0 := by
      intro h
      have := leadingCoeff_map_toPoly g
      rw [h] at this
      have hgZ0 : gZ ≠ 0 := by
        rw [hgZ, Ne, Polynomial.map_eq_zero_iff
          (fun a b h => Azurite.AzInt.ringEquivInt.injective (by simpa using h))]
        exact fun h2 => hg (toPoly_inj.mp (h2.trans toPoly_zero.symm))
      exact Polynomial.leadingCoeff_ne_zero.mpr hgZ0 (by
        rw [← hgZ] at this
        simpa using this)
    have hlc := congrArg Polynomial.leadingCoeff hkeyZ
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hgZ,
      leadingCoeff_map_toPoly, leadingCoeff_map_toPoly] at hlc
    -- `hlc : s.toInt * (primPos g).leadingCoeff.toInt = g.leadingCoeff.toInt`
    rw [leadingCoeff_map_toPoly]
    rcases hsgn : g.leadingCoeff.sign with _ | _
    · -- negative leading coefficient: `s < 0` and `lcof gZ < 0`
      have hneg : g.leadingCoeff.toInt < 0 := by
        have hiff := toInt_pos_iff_sign hlcg
        have h0 := toInt_ne_zero hlcg
        rcases lt_trichotomy g.leadingCoeff.toInt 0 with h | h | h
        · exact h
        · exact absurd h h0
        · rw [hiff.mp h] at hsgn; exact absurd hsgn (by simp)
      have hsneg : s.toInt < 0 := by
        rw [hsZ, hsgn]
        simp only [Bool.false_eq_true, if_false]
        omega
      by_contra hcon
      push Not at hcon
      nlinarith [hlc, mul_nonneg (neg_nonneg.mpr hsneg.le) (neg_nonneg.mpr hcon)]
    · -- positive leading coefficient: `s > 0` and `lcof gZ > 0`
      have hpos : 0 < g.leadingCoeff.toInt := (toInt_pos_iff_sign hlcg).mpr hsgn
      have hspos : 0 < s.toInt := by
        rw [hsZ, hsgn]
        simp only [if_true]
        omega
      by_contra hcon
      push Not at hcon
      nlinarith [hlc, mul_nonneg hspos.le (neg_nonneg.mpr hcon)]

/-- `signNorm` computes `normalize` on the represented polynomial. -/
private theorem map_toPoly_signNorm {p : AzPolynomial AzInt} (hp : p ≠ 0) :
    (AzPolynomial.toPoly (signNorm p)).map AzInt.toIntRingHom
      = _root_.normalize ((AzPolynomial.toPoly p).map AzInt.toIntRingHom) := by
  set pZ : ℤ[X] := (AzPolynomial.toPoly p).map AzInt.toIntRingHom with hpZ
  have hinj : Function.Injective (AzInt.toIntRingHom) :=
    fun a b h => Azurite.AzInt.ringEquivInt.injective (by simpa using h)
  have hpZ0 : pZ ≠ 0 := by
    rw [hpZ, Ne, Polynomial.map_eq_zero_iff hinj]
    exact fun h => hp (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hlcp : p.leadingCoeff ≠ 0 := by
    intro h
    have := leadingCoeff_map_toPoly p
    rw [h] at this
    exact Polynomial.leadingCoeff_ne_zero.mpr hpZ0 (by rw [← hpZ] at this; simpa using this)
  rw [signNorm]
  rcases hsgn : p.leadingCoeff.sign with _ | _
  · -- negative: output `-p`, i.e. `-pZ`, which has positive lcof
    simp only [Bool.false_eq_true, if_false]
    have hneg : pZ.leadingCoeff < 0 := by
      rw [leadingCoeff_map_toPoly]
      have h0 := toInt_ne_zero hlcp
      rcases lt_trichotomy p.leadingCoeff.toInt 0 with h | h | h
      · exact h
      · exact absurd h h0
      · rw [(toInt_pos_iff_sign hlcp).mp h] at hsgn; exact absurd hsgn (by simp)
    have himg : (AzPolynomial.toPoly (-p)).map AzInt.toIntRingHom = -pZ := by
      rw [toPoly_neg, Polynomial.map_neg, hpZ]
    rw [himg]
    have hpos : 0 < (-pZ).leadingCoeff := by
      rw [Polynomial.leadingCoeff_neg]
      omega
    have hassoc : Associated (-pZ) pZ :=
      Associated.symm ⟨-1, by rw [Units.val_neg, Units.val_one, mul_neg, mul_one]⟩
    calc -pZ = _root_.normalize (-pZ) := (normalize_eq_self_of_pos_lcof hpos).symm
      _ = _root_.normalize pZ := normalize_eq_normalize_iff_associated.mpr hassoc
  · -- positive: output `p` itself, already normalized
    simp only [reduceIte]
    have hpos : 0 < pZ.leadingCoeff := by
      rw [leadingCoeff_map_toPoly]
      exact (toInt_pos_iff_sign hlcp).mpr hsgn
    rw [hpZ]
    exact (normalize_eq_self_of_pos_lcof hpos).symm

/-! ### The `ℤ[X]` gcd characterization -/

private theorem content_dvd_of_dvd {e A : ℤ[X]} (h : e ∣ A) : e.content ∣ A.content := by
  obtain ⟨f, rfl⟩ := h
  rw [Polynomial.content_mul]
  exact Dvd.intro _ rfl

/-- **Characterization of the normalized `ℤ[X]` gcd.** If
`d = gcd(cont A, cont B)` and `G` is primitive with positive leading
coefficient whose `ℚ[X]` image is associated to the rational gcd, then
`C d · G` is the (normalized) gcd of `A` and `B`. -/
private theorem int_gcd_eq {A B G : ℤ[X]} {d : ℤ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hd : d = GCDMonoid.gcd A.content B.content)
    (hGprim : G.IsPrimitive) (hGpos : 0 < G.leadingCoeff)
    (hGq : Associated (G.map (Int.castRingHom ℚ))
      (GCDMonoid.gcd (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))) :
    Polynomial.C d * G = GCDMonoid.gcd A B := by
  have hcontA : A.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
  have hcontB : B.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
  have hd0 : d ≠ 0 := by
    rw [hd]
    intro h
    exact hcontA ((gcd_eq_zero_iff _ _).mp h).1
  have hdpos : 0 < d := by
    have h1 : _root_.normalize d = d := by rw [hd]; exact normalize_gcd _ _
    rw [← Int.abs_eq_normalize] at h1
    have h2 : 0 ≤ d := by rw [← h1]; exact abs_nonneg d
    rcases h2.lt_or_eq with h | h
    · exact h
    · exact absurd h.symm hd0
  have hκinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  -- `ℚ[X]` image of a primitive part is associated to the image itself
  have hprimq : ∀ (T : ℤ[X]), T ≠ 0 →
      Associated (T.map (Int.castRingHom ℚ)) ((T.primPart).map (Int.castRingHom ℚ)) := by
    intro T hT
    have hcT : T.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
    have hu : IsUnit (Polynomial.C ((T.content : ℤ) : ℚ) : ℚ[X]) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hcT))
    have h1 : T.map (Int.castRingHom ℚ)
        = Polynomial.C ((T.content : ℤ) : ℚ) * (T.primPart).map (Int.castRingHom ℚ) := by
      conv_lhs => rw [T.eq_C_content_mul_primPart]
      rw [Polynomial.map_mul, Polynomial.map_C]
      rfl
    rw [h1]
    exact Associated.symm ⟨hu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩
  -- (i)/(ii): `C d · G` divides both `A` and `B`
  have hGdvdA : G ∣ A.primPart := by
    refine hGprim.dvd_of_fraction_map_dvd_fraction_map (K := ℚ) A.isPrimitive_primPart ?_
    exact (hGq.dvd.trans (gcd_dvd_left _ _)).trans (hprimq A hA).dvd
  have hGdvdB : G ∣ B.primPart := by
    refine hGprim.dvd_of_fraction_map_dvd_fraction_map (K := ℚ) B.isPrimitive_primPart ?_
    exact (hGq.dvd.trans (gcd_dvd_right _ _)).trans (hprimq B hB).dvd
  have hdvdA : Polynomial.C d * G ∣ A := by
    conv_rhs => rw [A.eq_C_content_mul_primPart]
    exact mul_dvd_mul (map_dvd (Polynomial.C : ℤ →+* ℤ[X]) (hd ▸ gcd_dvd_left _ _)) hGdvdA
  have hdvdB : Polynomial.C d * G ∣ B := by
    conv_rhs => rw [B.eq_C_content_mul_primPart]
    exact mul_dvd_mul (map_dvd (Polynomial.C : ℤ →+* ℤ[X]) (hd ▸ gcd_dvd_right _ _)) hGdvdB
  -- (iii): maximality
  have hmax : ∀ e : ℤ[X], e ∣ A → e ∣ B → e ∣ Polynomial.C d * G := by
    intro e heA heB
    have hce : e.content ∣ d := by
      rw [hd]
      exact dvd_gcd (content_dvd_of_dvd heA) (content_dvd_of_dvd heB)
    have hpe : e.primPart ∣ G := by
      refine e.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (K := ℚ) hGprim ?_
      have h1 : (e.primPart).map (Int.castRingHom ℚ) ∣ A.map (Int.castRingHom ℚ) :=
        Polynomial.map_dvd _ (e.primPart_dvd.trans heA)
      have h2 : (e.primPart).map (Int.castRingHom ℚ) ∣ B.map (Int.castRingHom ℚ) :=
        Polynomial.map_dvd _ (e.primPart_dvd.trans heB)
      exact (dvd_gcd h1 h2).trans hGq.symm.dvd
    calc e = Polynomial.C e.content * e.primPart := e.eq_C_content_mul_primPart
      _ ∣ Polynomial.C d * G :=
        mul_dvd_mul (map_dvd (Polynomial.C : ℤ →+* ℤ[X]) hce) hpe
  -- (iv): normalized output
  have hnorm : _root_.normalize (Polynomial.C d * G) = Polynomial.C d * G := by
    apply normalize_eq_self_of_pos_lcof
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact mul_pos hdpos hGpos
  exact dvd_antisymm_of_normalize_eq hnorm (normalize_gcd A B)
    (dvd_gcd hdvdA hdvdB) (hmax _ (gcd_dvd_left A B) (gcd_dvd_right A B))

/-! ### The core over `AzInt`, transported to `ℚ[X]` -/

open Azurite.BPR.Chapter8 in
/-- **Core correctness over `AzInt`.** For `P, Q ≠ 0` with
`deg P > deg Q ≥ 1`, the `ℚ[X]` image of `subresGcd P Q` is associated to
the rational gcd, and the output is nonzero. Mirror of
`toPoly_subresGcd_associated`, with the `AzInt`-level Algorithm 8.21 bridge
transported along `sResP_map`. -/
theorem subresGcd_int_qassoc (P Q : AzPolynomial AzInt) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    Associated
      ((AzPolynomial.toPoly (subresGcd P Q)).map
        ((Int.castRingHom ℚ).comp AzInt.toIntRingHom))
      (GCDMonoid.gcd
        ((AzPolynomial.toPoly P).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom))
        ((AzPolynomial.toPoly Q).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)))
    ∧ subresGcd P Q ≠ 0 := by
  set ψ : AzInt →+* ℚ := (Int.castRingHom ℚ).comp AzInt.toIntRingHom with hψ
  have hψinj : Function.Injective ψ := by
    intro a b h
    rw [hψ] at h
    simp only [RingHom.comp_apply] at h
    have h3 : ((a.toInt : ℚ)) = ((b.toInt : ℚ)) := by simpa using h
    have h2 : a.toInt = b.toInt := by exact_mod_cast h3
    exact Azurite.AzInt.ringEquivInt.injective (by simpa using h2)
  set Aq : ℚ[X] := (AzPolynomial.toPoly P).map ψ with hAq
  set Bq : ℚ[X] := (AzPolynomial.toPoly Q).map ψ with hBq
  have hP' : AzPolynomial.toPoly P ≠ 0 := toPoly_ne_zero hP
  have hQ' : AzPolynomial.toPoly Q ≠ 0 := toPoly_ne_zero hQ
  have hAq0 : Aq ≠ 0 := by
    rw [hAq, Ne, Polynomial.map_eq_zero_iff hψinj]
    exact hP'
  have hBq0 : Bq ≠ 0 := by
    rw [hBq, Ne, Polynomial.map_eq_zero_iff hψinj]
    exact hQ'
  have hdA : Aq.natDegree = P.natDegree := by
    rw [hAq, Polynomial.natDegree_map_eq_of_injective hψinj, AzPolynomial.natDegree_toPoly]
  have hdB : Bq.natDegree = Q.natDegree := by
    rw [hBq, Polynomial.natDegree_map_eq_of_injective hψinj, AzPolynomial.natDegree_toPoly]
  have hpq' : Bq.natDegree < Aq.natDegree := by rw [hdA, hdB]; exact hpq
  have hq1' : 1 ≤ Bq.natDegree := by rw [hdB]; exact hq1
  -- Algorithm 8.21 bridge over the domain `AzInt`
  have hlist := (signedSubresultant_toPoly_domain P Q hP hQ hpq hq1).1
  set sP := (signedSubresultant P Q).1 with hsP
  have hlen : sP.size = P.natDegree + 1 := by
    have := congrArg List.length hlist
    simpa using this
  -- index-wise identification, transported to `ℚ[X]` along `sResP_map`
  have hidx : ∀ j (hj : j < P.natDegree + 1),
      (AzPolynomial.toPoly (sP[j]!)).map ψ = sResP Aq Bq j := by
    intro j hj
    have hjs : j < sP.size := by omega
    have h1 : (sP.toList.map AzPolynomial.toPoly)[j]'(by simpa using hjs)
        = ((List.range (P.natDegree + 1)).map
            (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)))[j]'(by simpa using hj) := by
      congr 1
    rw [List.getElem_map, List.getElem_map, List.getElem_range] at h1
    have h2 : AzPolynomial.toPoly (sP[j]!)
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j := by
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjs]
      simpa [Array.getElem_toList] using h1
    rw [h2, hAq, hBq, ← sResP_map hψinj]
  -- the gcd degree at `ℚ` (`EuclideanDomain`-instance, driving Chapter 8)
  set j₀ := (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial Aq Bq).natDegree with hj₀
  have hj₀q : j₀ ≤ Bq.natDegree :=
    Polynomial.natDegree_le_of_dvd
      (@gcd_dvd_right _ _ Azurite.BPR.gcdMonoidPolynomial _ _) hBq0
  have hj₀lt : j₀ < P.natDegree + 1 := by
    rw [hdB] at hj₀q
    omega
  -- zeros below the gcd degree, nonzero at it
  have hzero : ∀ i, i < j₀ → sP[i]! = 0 := by
    intro i hi
    apply toPoly_inj.mp
    have h1 : (AzPolynomial.toPoly (sP[i]!)).map ψ = 0 := by
      rw [hidx i (by omega)]
      exact sResP_eq_zero_of_lt_gcd _ _ hAq0 hBq0 hpq' (by omega) hi
    rw [toPoly_zero]
    exact (Polynomial.map_eq_zero_iff hψinj).mp h1
  have hne : sP[j₀]! ≠ 0 := by
    intro h
    have h2 := hidx j₀ hj₀lt
    rw [h, toPoly_zero, Polynomial.map_zero] at h2
    exact sResP_natDegree_gcd_ne_zero _ _ hAq0 hBq0 hpq' h2.symm
  have hfind : firstNonzero sP = some j₀ :=
    firstNonzero_eq_some sP j₀ (by omega) hzero hne
  have hout : subresGcd P Q = sP[j₀]! := by
    rw [subresGcd]
    rw [← hsP, hfind]
  rw [hout]
  refine ⟨?_, hne⟩
  rw [hidx j₀ hj₀lt]
  have hbridge : Associated
      (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial Aq Bq)
      (GCDMonoid.gcd Aq Bq) :=
    associated_of_dvd_dvd
      (dvd_gcd (@gcd_dvd_left _ _ Azurite.BPR.gcdMonoidPolynomial _ _)
        (@gcd_dvd_right _ _ Azurite.BPR.gcdMonoidPolynomial _ _))
      (@dvd_gcd _ _ Azurite.BPR.gcdMonoidPolynomial _ _ _
        (gcd_dvd_left _ _) (gcd_dvd_right _ _))
  exact (associated_sResP_gcd _ _ hAq0 hBq0 hpq' rfl).trans hbridge

/-! ### Assembly: `gcdNormalizedInt` computes the `ℤ[X]` gcd -/

private theorem hιinj : Function.Injective (AzInt.toIntRingHom) :=
  fun a b h => Azurite.AzInt.ringEquivInt.injective (by simpa using h)

private theorem map_toPoly_ne_zero {T : AzPolynomial AzInt} (hT : T ≠ 0) :
    (AzPolynomial.toPoly T).map AzInt.toIntRingHom ≠ 0 := by
  rw [Ne, Polynomial.map_eq_zero_iff hιinj]
  exact toPoly_ne_zero hT

private theorem natDegree_map_toPoly (T : AzPolynomial AzInt) :
    ((AzPolynomial.toPoly T).map AzInt.toIntRingHom).natDegree = T.natDegree := by
  rw [Polynomial.natDegree_map_eq_of_injective hιinj, AzPolynomial.natDegree_toPoly]

private theorem signNorm_zero : signNorm (0 : AzPolynomial AzInt) = 0 := by
  rw [signNorm]
  split <;> simp

/-- `contentGcdInt` represents the `ℤ`-gcd of the contents. -/
private theorem toInt_contentGcdInt (P Q : AzPolynomial AzInt) :
    (contentGcdInt P Q).toInt
      = GCDMonoid.gcd ((AzPolynomial.toPoly P).map AzInt.toIntRingHom).content
          ((AzPolynomial.toPoly Q).map AzInt.toIntRingHom).content := by
  rw [contentGcdInt, toInt_azNatToAzInt, Azurite.AzNat.toNat_gcd, content_toPoly,
    content_toPoly, ← Int.gcd_natCast_natCast, Int.coe_gcd]

/-- Mapped scalar action. -/
private theorem map_toPoly_smul (c : AzInt) (X : AzPolynomial AzInt) :
    (AzPolynomial.toPoly (c • X)).map AzInt.toIntRingHom
      = Polynomial.C c.toInt * ((AzPolynomial.toPoly X).map AzInt.toIntRingHom) := by
  rw [toPoly_smul, Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C]
  rfl

private theorem isUnit_Q_of_natDegree_eq_zero {p : ℚ[X]} (hp : p ≠ 0)
    (hd : p.natDegree = 0) : IsUnit p := by
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hd
  rw [hC]
  refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h => hp ?_))
  rw [hC, h, Polynomial.C_0]

/-- Fuse the two coefficient maps. -/
private theorem map_map_fuse (T : AzPolynomial AzInt) :
    ((AzPolynomial.toPoly T).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
      = (AzPolynomial.toPoly T).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) :=
  Polynomial.map_map _ _ _

set_option maxHeartbeats 1600000 in
/-- **Equivalence with the `ℤ[X]` gcd.**
`(toPoly (gcdNormalizedInt P Q)).map ι = gcd ((toPoly P).map ι) ((toPoly Q).map ι)`
— the computable gcd represents Mathlib's normalized `ℤ[X]` gcd exactly,
for all `P, Q`. -/
theorem map_toPoly_gcdNormalizedInt (P Q : AzPolynomial AzInt) :
    (AzPolynomial.toPoly (gcdNormalizedInt P Q)).map AzInt.toIntRingHom
      = GCDMonoid.gcd ((AzPolynomial.toPoly P).map AzInt.toIntRingHom)
          ((AzPolynomial.toPoly Q).map AzInt.toIntRingHom) := by
  set A : ℤ[X] := (AzPolynomial.toPoly P).map AzInt.toIntRingHom with hA
  set B : ℤ[X] := (AzPolynomial.toPoly Q).map AzInt.toIntRingHom with hB
  rw [gcdNormalizedInt]
  by_cases hP0 : P = 0
  · rw [if_pos hP0]
    have hA0 : A = 0 := by rw [hA, hP0, toPoly_zero, Polynomial.map_zero]
    by_cases hQ0 : Q = 0
    · have hB0 : B = 0 := by rw [hB, hQ0, toPoly_zero, Polynomial.map_zero]
      rw [hQ0, signNorm_zero, toPoly_zero, Polynomial.map_zero, hA0, hB0,
        gcd_zero_right, normalize_zero]
    · rw [map_toPoly_signNorm hQ0, hA0, gcd_zero_left, hB]
  rw [if_neg hP0]
  by_cases hQ0 : Q = 0
  · rw [if_pos hQ0]
    have hB0 : B = 0 := by rw [hB, hQ0, toPoly_zero, Polynomial.map_zero]
    rw [map_toPoly_signNorm hP0, hB0, gcd_zero_right, hA]
  rw [if_neg hQ0]
  have hA0 : A ≠ 0 := hA ▸ map_toPoly_ne_zero hP0
  have hB0 : B ≠ 0 := hB ▸ map_toPoly_ne_zero hQ0
  have hd : (contentGcdInt P Q).toInt = GCDMonoid.gcd A.content B.content := by
    rw [hA, hB]; exact toInt_contentGcdInt P Q
  -- ℚ-side abbreviations
  have hAq0 : A.map (Int.castRingHom ℚ) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff Int.cast_injective]
    exact hA0
  have hBq0 : B.map (Int.castRingHom ℚ) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff Int.cast_injective]
    exact hB0
  have hdAq : (A.map (Int.castRingHom ℚ)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hA,
      natDegree_map_toPoly]
  have hdBq : (B.map (Int.castRingHom ℚ)).natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hB,
      natDegree_map_toPoly]
  -- the `hGq` of a `primPos` of a nonzero polynomial `g` whose `ℚ`-image is
  -- associated to the rational gcd
  have hGq_of : ∀ (g : AzPolynomial AzInt), g ≠ 0 →
      Associated
        (((AzPolynomial.toPoly g).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
        (GCDMonoid.gcd (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ))) →
      Associated
        (((AzPolynomial.toPoly (primPos g)).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
        (GCDMonoid.gcd (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ))) := by
    intro g hg hassoc
    obtain ⟨c, hc0, hkey, _, _⟩ := primPos_spec hg
    have hkeyq := congrArg (Polynomial.map (Int.castRingHom ℚ)) hkey
    rw [Polynomial.map_mul, Polynomial.map_C,
      show (Int.castRingHom ℚ) c = ((c : ℤ) : ℚ) from rfl] at hkeyq
    have hu : IsUnit (Polynomial.C ((c : ℤ) : ℚ) : ℚ[X]) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hc0))
    have h1 : Associated
        (((AzPolynomial.toPoly (primPos g)).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
        (((AzPolynomial.toPoly g).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)) := by
      rw [← hkeyq]
      exact ⟨hu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩
    exact h1.trans hassoc
  by_cases hdeg0 : P.natDegree = 0 ∨ Q.natDegree = 0
  · rw [if_pos hdeg0]
    -- constant case: the gcd is the content gcd
    rw [map_toPoly_smul, toPoly_one, Polynomial.map_one, mul_one,
      show Polynomial.C (contentGcdInt P Q).toInt
        = Polynomial.C (contentGcdInt P Q).toInt * 1 from (mul_one _).symm, hA, hB]
    apply int_gcd_eq (hA ▸ hA0) (hB ▸ hB0) (hA ▸ hB ▸ hd) Polynomial.isPrimitive_one
      (by rw [Polynomial.leadingCoeff_one]; norm_num)
    rw [Polynomial.map_one]
    have hunit : IsUnit (A.map (Int.castRingHom ℚ))
        ∨ IsUnit (B.map (Int.castRingHom ℚ)) := by
      rcases hdeg0 with h | h
      · exact Or.inl (isUnit_Q_of_natDegree_eq_zero hAq0 (by rw [hdAq]; exact h))
      · exact Or.inr (isUnit_Q_of_natDegree_eq_zero hBq0 (by rw [hdBq]; exact h))
    rcases hunit with h | h
    · rw [gcd_isUnit_left h]
    · rw [gcd_isUnit_right h]
  rw [if_neg hdeg0]
  push Not at hdeg0
  obtain ⟨hPd0, hQd0⟩ := hdeg0
  -- common: apply `int_gcd_eq` after producing `(G, hGq)` per branch
  have happly : ∀ (g : AzPolynomial AzInt), g ≠ 0 →
      Associated
        (((AzPolynomial.toPoly g).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
        (GCDMonoid.gcd (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ))) →
      (AzPolynomial.toPoly (contentGcdInt P Q • primPos g)).map AzInt.toIntRingHom
        = GCDMonoid.gcd A B := by
    intro g hg hassoc
    rw [map_toPoly_smul]
    obtain ⟨c, hc0, hkey, hprim, hpos⟩ := primPos_spec hg
    exact int_gcd_eq hA0 hB0 hd hprim hpos (hGq_of g hg hassoc)
  by_cases hdeq : P.natDegree = Q.natDegree
  · rw [if_pos hdeq]
    set T := preStep P Q with hT
    have hlcPq : ((P.leadingCoeff.toInt : ℤ) : ℚ) ≠ 0 := by
      have h1 : A.leadingCoeff = P.leadingCoeff.toInt := hA ▸ leadingCoeff_map_toPoly P
      have h2 : A.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hA0
      rw [h1] at h2
      exact_mod_cast h2
    have hTq : ((AzPolynomial.toPoly T).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
        = Polynomial.C ((P.leadingCoeff.toInt : ℤ) : ℚ) * (B.map (Int.castRingHom ℚ))
          - Polynomial.C ((Q.leadingCoeff.toInt : ℤ) : ℚ) * (A.map (Int.castRingHom ℚ)) := by
      rw [hT, preStep, toPoly_pre_step, Polynomial.map_sub, Polynomial.map_sub,
        Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_C, Polynomial.map_C, Polynomial.map_C, hA, hB]
      rfl
    have hstepq : GCDMonoid.gcd (A.map (Int.castRingHom ℚ))
          (((AzPolynomial.toPoly T).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
        = GCDMonoid.gcd (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) := by
      rw [hTq]
      exact gcd_pre_step _ _ hlcPq
    by_cases hT0 : T = 0
    · rw [if_pos hT0]
      -- proportional: `Aq ∣ Bq`, so the gcd is `normalize Aq ~ Aq`
      have hprop : Polynomial.C ((P.leadingCoeff.toInt : ℤ) : ℚ)
            * (B.map (Int.castRingHom ℚ))
          = Polynomial.C ((Q.leadingCoeff.toInt : ℤ) : ℚ)
            * (A.map (Int.castRingHom ℚ)) := by
        have h := hTq
        rw [hT0, toPoly_zero, Polynomial.map_zero, Polynomial.map_zero] at h
        exact (sub_eq_zero.mp h.symm)
      have hdvd : A.map (Int.castRingHom ℚ) ∣ B.map (Int.castRingHom ℚ) := by
        refine ⟨Polynomial.C ((P.leadingCoeff.toInt : ℤ) : ℚ)⁻¹
          * Polynomial.C ((Q.leadingCoeff.toInt : ℤ) : ℚ), ?_⟩
        have h2 := congrArg
          (fun z => Polynomial.C ((P.leadingCoeff.toInt : ℤ) : ℚ)⁻¹ * z) hprop
        simp only [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlcPq,
          Polynomial.C_1, one_mul] at h2
        rw [h2, Polynomial.C_mul]
        ring
      refine happly P hP0 ?_
      rw [hA, gcd_eq_normalize_left hdvd]
      exact (associated_normalize _)
    rw [if_neg hT0]
    by_cases hTd : T.natDegree = 0
    · rw [if_pos hTd]
      -- the pre-step output is a nonzero rational unit: the gcd is `1`
      rw [map_toPoly_smul, toPoly_one, Polynomial.map_one, mul_one,
        show Polynomial.C (contentGcdInt P Q).toInt
          = Polynomial.C (contentGcdInt P Q).toInt * 1 from (mul_one _).symm]
      apply int_gcd_eq hA0 hB0 hd Polynomial.isPrimitive_one
        (by rw [Polynomial.leadingCoeff_one]; norm_num)
      rw [Polynomial.map_one, ← hstepq]
      have hTq0 : ((AzPolynomial.toPoly T).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
          ≠ 0 := by
        rw [Ne, Polynomial.map_eq_zero_iff Int.cast_injective]
        exact map_toPoly_ne_zero hT0
      have hTdq : (((AzPolynomial.toPoly T).map AzInt.toIntRingHom).map
          (Int.castRingHom ℚ)).natDegree = 0 := by
        rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
          natDegree_map_toPoly]
        exact hTd
      rw [gcd_isUnit_right (isUnit_Q_of_natDegree_eq_zero hTq0 hTdq)]
    rw [if_neg hTd]
    -- main equal-degree branch: core on `(P, T)`, pre-step invisible over `ℚ`
    have hlt : T.natDegree < P.natDegree := by
      rw [hT, preStep]
      refine pre_step_natDegree_lt hP0 hQ0 hdeq ?_
      rw [hT, preStep] at hT0
      exact hT0
    obtain ⟨hcore, hne⟩ := subresGcd_int_qassoc P T hP0 hT0 hlt (by omega)
    refine happly _ hne ?_
    have h1 := hcore
    rw [← map_map_fuse, ← map_map_fuse, ← map_map_fuse, ← hA] at h1
    rw [← hstepq]
    exact h1
  rw [if_neg hdeq]
  by_cases hdlt : P.natDegree < Q.natDegree
  · rw [if_pos hdlt]
    obtain ⟨hcore, hne⟩ := subresGcd_int_qassoc Q P hQ0 hP0 hdlt (by omega)
    refine happly _ hne ?_
    have h1 := hcore
    rw [← map_map_fuse, ← map_map_fuse, ← map_map_fuse, ← hA, ← hB] at h1
    rw [gcd_comm]
    exact h1
  · rw [if_neg hdlt]
    obtain ⟨hcore, hne⟩ := subresGcd_int_qassoc P Q hP0 hQ0 (by omega) (by omega)
    refine happly _ hne ?_
    have h1 := hcore
    rw [← map_map_fuse, ← map_map_fuse, ← map_map_fuse, ← hA, ← hB] at h1
    exact h1

/-! ### The `GcdImpl` interface: `gcd` and the canonical pair -/

/-- **`gcd` (typeclass) computes the `ℤ[X]` gcd.** -/
theorem map_toPoly_gcd_int (P Q : AzPolynomial AzInt) :
    (AzPolynomial.toPoly (gcd P Q)).map AzInt.toIntRingHom
      = GCDMonoid.gcd ((AzPolynomial.toPoly P).map AzInt.toIntRingHom)
          ((AzPolynomial.toPoly Q).map AzInt.toIntRingHom) :=
  map_toPoly_gcdNormalizedInt P Q

/-- **The canonical pair over `ℤ`.** The first component is the gcd, and the
second is the exact quotient: `gcd(A, B) · (snd-image) = A`, unconditionally. -/
theorem gcdGcdFreePart_int_spec (P Q : AzPolynomial AzInt) :
    (gcdGcdFreePart P Q).1 = gcd P Q
    ∧ GCDMonoid.gcd ((AzPolynomial.toPoly P).map AzInt.toIntRingHom)
          ((AzPolynomial.toPoly Q).map AzInt.toIntRingHom)
        * ((AzPolynomial.toPoly (gcdGcdFreePart P Q).2).map AzInt.toIntRingHom)
      = (AzPolynomial.toPoly P).map AzInt.toIntRingHom := by
  set A : ℤ[X] := (AzPolynomial.toPoly P).map AzInt.toIntRingHom with hA
  set g := gcdNormalizedInt P Q with hg
  have hpair : gcdGcdFreePart P Q
      = (g, if g = 0 then 0 else (exactDivQuoRem P g).1) := rfl
  have hgcd : (AzPolynomial.toPoly g).map AzInt.toIntRingHom
      = GCDMonoid.gcd A ((AzPolynomial.toPoly Q).map AzInt.toIntRingHom) := by
    rw [hg, hA]
    exact map_toPoly_gcdNormalizedInt P Q
  refine ⟨by rw [hpair]; rfl, ?_⟩
  rw [hpair]
  by_cases hg0 : g = 0
  · -- both inputs vanish: everything is `0`
    have hgcd0 : GCDMonoid.gcd A ((AzPolynomial.toPoly Q).map AzInt.toIntRingHom) = 0 := by
      rw [← hgcd, hg0, toPoly_zero, Polynomial.map_zero]
    have hA0 : A = 0 := ((gcd_eq_zero_iff _ _).mp hgcd0).1
    simp only [hg0, if_true]
    rw [hgcd0, hA0, zero_mul]
  · simp only [if_neg hg0]
    -- the gcd divides `A`; identify the computable quotient with the cofactor
    have hGz : (AzPolynomial.toPoly g).map AzInt.toIntRingHom ∣ A := by
      rw [hgcd]
      exact gcd_dvd_left _ _
    obtain ⟨Hz, hHz⟩ := hGz
    -- pull the cofactor back along the coefficient equivalence
    set ε : (Polynomial AzInt) ≃+* ℤ[X] := Polynomial.mapEquiv Azurite.AzInt.ringEquivInt
      with hε
    have hεapp : ∀ T : Polynomial AzInt, ε T = T.map AzInt.toIntRingHom := fun _ => rfl
    set H : Polynomial AzInt := ε.symm Hz with hH
    have hεH : H.map AzInt.toIntRingHom = Hz := by
      rw [← hεapp, hH, RingEquiv.apply_symm_apply]
    have hfac : AzPolynomial.toPoly P = H * AzPolynomial.toPoly g := by
      apply ε.injective
      rw [map_mul, hεapp, hεapp, hεH, ← hA, hHz, hεapp]
      ring
    have hg' : AzPolynomial.toPoly g ≠ 0 := toPoly_ne_zero hg0
    have hquo : AzPolynomial.toPoly ((exactDivQuoRem P g).1) = H := by
      refine toPoly_exactDivQuoRem_fst_of_euclidean P g H 0 hg' ?_ ?_
      · rw [add_zero, hfac]
      · rw [Polynomial.degree_zero]
        exact bot_lt_iff_ne_bot.mpr (fun h => hg' (Polynomial.degree_eq_bot.mp h))
    rw [hquo, hεH, ← hgcd]
    exact hHz.symm

/-! ### `ofPoly` directions over `ℤ` -/

/-- Round trip: pull a `ℤ[X]` polynomial back to `AzInt` coefficients and
represent it again. -/
private theorem map_toPoly_ofPoly_map (p : ℤ[X]) :
    (AzPolynomial.toPoly (AzPolynomial.ofPoly
        (p.map AzInt.ringEquivInt.symm.toRingHom))).map AzInt.toIntRingHom = p := by
  rw [toPoly_ofPoly, Polynomial.map_map]
  have hcomp : AzInt.toIntRingHom.comp AzInt.ringEquivInt.symm.toRingHom
      = RingHom.id ℤ :=
    RingHom.ext fun x => Azurite.AzInt.ringEquivInt.apply_symm_apply x
  rw [hcomp, Polynomial.map_id]

/-! ### Exactness core for the raw BPR pair (Algorithm 10.1 over `ℤ`) -/

/-- `ℚ[X]` image of a polynomial is associated to that of its primitive part. -/
private theorem map_assoc_primPart {T : ℤ[X]} (hT : T ≠ 0) :
    Associated (T.map (Int.castRingHom ℚ)) ((T.primPart).map (Int.castRingHom ℚ)) := by
  have hcT : T.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
  have hu : IsUnit (Polynomial.C ((T.content : ℤ) : ℚ) : ℚ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hcT))
  have h1 : T.map (Int.castRingHom ℚ)
      = Polynomial.C ((T.content : ℤ) : ℚ) * (T.primPart).map (Int.castRingHom ℚ) := by
    conv_lhs => rw [T.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
    rfl
  rw [h1]
  exact Associated.symm ⟨hu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩

/-- **Exactness core for the `a_p·sResV_{j−1}/lcof` normalization** (BPR's
Lemma 10.17 argument): if `V` divides `A` over `ℚ`, then `lcof(V)` divides
`lcof(A) · v` for every coefficient `v` of `V` — `lc(primPart V)` divides
`lc(primPart A)` by primitive descent (Gauss), hence divides `lcof(A)`,
while the content of `V` cancels against itself. -/
private theorem lcof_dvd_lcof_mul_coeff {A V : ℤ[X]} (hA : A ≠ 0) (hV : V ≠ 0)
    (hdvd : V.map (Int.castRingHom ℚ) ∣ A.map (Int.castRingHom ℚ)) (i : ℕ) :
    V.leadingCoeff ∣ A.leadingCoeff * V.coeff i := by
  -- primitive descent: `primPart V ∣ primPart A` in `ℤ[X]`
  have hPdvd : V.primPart ∣ A.primPart := by
    refine V.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (K := ℚ)
      A.isPrimitive_primPart ?_
    exact ((map_assoc_primPart hV).symm.dvd.trans hdvd).trans (map_assoc_primPart hA).dvd
  obtain ⟨W, hW⟩ := hPdvd
  have hlcP : V.primPart.leadingCoeff ∣ A.leadingCoeff := by
    have h1 : A.primPart.leadingCoeff = V.primPart.leadingCoeff * W.leadingCoeff := by
      rw [hW, Polynomial.leadingCoeff_mul]
    have h2 : A.leadingCoeff = A.content * A.primPart.leadingCoeff := by
      conv_lhs => rw [A.eq_C_content_mul_primPart]
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact (Dvd.intro _ h1.symm).trans (Dvd.intro_left _ h2.symm)
  have hlcV : V.leadingCoeff = V.content * V.primPart.leadingCoeff := by
    conv_lhs => rw [V.eq_C_content_mul_primPart]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  have hcoefV : V.coeff i = V.content * V.primPart.coeff i := by
    conv_lhs => rw [V.eq_C_content_mul_primPart]
    rw [Polynomial.coeff_C_mul]
  rw [hlcV, hcoefV,
    show A.leadingCoeff * (V.content * V.primPart.coeff i)
      = V.content * (A.leadingCoeff * V.primPart.coeff i) from by ring]
  exact mul_dvd_mul_left _ (dvd_mul_of_dvd_left hlcP _)

/-- **`ofPoly` version of the `ℤ[X]` equivalence**: pulling two `ℤ[X]`
polynomials back to `AzInt` coefficients, the computable gcd represents
Mathlib's normalized `ℤ[X]` gcd. -/
theorem ofPoly_gcd_int (p q : ℤ[X]) :
    gcd (AzPolynomial.ofPoly (p.map AzInt.ringEquivInt.symm.toRingHom))
        (AzPolynomial.ofPoly (q.map AzInt.ringEquivInt.symm.toRingHom))
      = AzPolynomial.ofPoly ((GCDMonoid.gcd p q).map AzInt.ringEquivInt.symm.toRingHom) := by
  apply toPoly_inj.mp
  have hιinj' : Function.Injective (Polynomial.map (AzInt.toIntRingHom)) :=
    fun a b h => by
      have := congrArg (Polynomial.map AzInt.ringEquivInt.symm.toRingHom) h
      rw [Polynomial.map_map, Polynomial.map_map,
        show AzInt.ringEquivInt.symm.toRingHom.comp AzInt.toIntRingHom
          = RingHom.id AzInt from RingHom.ext fun x =>
            Azurite.AzInt.ringEquivInt.symm_apply_apply x,
        Polynomial.map_id, Polynomial.map_id] at this
      exact this
  apply hιinj'
  rw [map_toPoly_gcd_int, map_toPoly_ofPoly_map, map_toPoly_ofPoly_map,
    map_toPoly_ofPoly_map]

/-- **`ofPoly` version of the canonical pair over `ℤ`** (multiplicative
form for the exact quotient). -/
theorem ofPoly_gcdGcdFreePart_int (p q : ℤ[X]) :
    (gcdGcdFreePart (AzPolynomial.ofPoly (p.map AzInt.ringEquivInt.symm.toRingHom))
        (AzPolynomial.ofPoly (q.map AzInt.ringEquivInt.symm.toRingHom))).1
      = AzPolynomial.ofPoly ((GCDMonoid.gcd p q).map AzInt.ringEquivInt.symm.toRingHom)
    ∧ GCDMonoid.gcd p q
        * ((AzPolynomial.toPoly
            (gcdGcdFreePart (AzPolynomial.ofPoly (p.map AzInt.ringEquivInt.symm.toRingHom))
              (AzPolynomial.ofPoly (q.map AzInt.ringEquivInt.symm.toRingHom))).2).map
            AzInt.toIntRingHom)
      = p := by
  obtain ⟨h1, h2⟩ := gcdGcdFreePart_int_spec
    (AzPolynomial.ofPoly (p.map AzInt.ringEquivInt.symm.toRingHom))
    (AzPolynomial.ofPoly (q.map AzInt.ringEquivInt.symm.toRingHom))
  rw [map_toPoly_ofPoly_map, map_toPoly_ofPoly_map] at h2
  refine ⟨?_, h2⟩
  rw [h1]
  exact ofPoly_gcd_int p q

/-! ### The raw BPR-normalized pair over `ℤ`: gcd-free-part correctness -/

open Azurite.BPR.Chapter8 in
/-- **Gcd-free-part correctness of the raw `ℤ` pair** (BPR Algorithm 10.1 over
`AzInt`, `deg P > deg Q ≥ 1`, gcd degree `j₀ ≥ 1` over `ℚ`): the second
output of `gcdGcdFreePartInt` — the BPR-normalized
`a_p·sResV_{j₀−1}/lcof(sResV_{j₀−1})`, whose divisions are exact by the
Lemma 10.17 content argument — times the gcd is associated to `P` over `ℚ`:
it is the gcd-free part of `P` with respect to `Q` up to a multiplicative
constant. -/
theorem gcdGcdFreePartInt_snd_gcdFree (P Q : AzPolynomial AzInt)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {j₀ : ℕ} (hj₀1 : 1 ≤ j₀)
    (hj₀ : (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
        (((AzPolynomial.toPoly P).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
        (((AzPolynomial.toPoly Q).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))).natDegree
      = j₀) :
    Associated
      ((((AzPolynomial.toPoly (gcdGcdFreePartInt P Q).2).map AzInt.toIntRingHom).map
          (Int.castRingHom ℚ))
        * @GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
            (((AzPolynomial.toPoly P).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
            (((AzPolynomial.toPoly Q).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)))
      (((AzPolynomial.toPoly P).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)) := by
  have hψinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  -- abbreviations
  set A : ℤ[X] := (AzPolynomial.toPoly P).map AzInt.toIntRingHom with hA
  set B : ℤ[X] := (AzPolynomial.toPoly Q).map AzInt.toIntRingHom with hB
  set Aq : ℚ[X] := A.map (Int.castRingHom ℚ) with hAq
  set Bq : ℚ[X] := B.map (Int.castRingHom ℚ) with hBq
  have hP' : AzPolynomial.toPoly P ≠ 0 := toPoly_ne_zero hP
  have hQ' : AzPolynomial.toPoly Q ≠ 0 := toPoly_ne_zero hQ
  have hA0 : A ≠ 0 := map_toPoly_ne_zero hP
  have hB0 : B ≠ 0 := map_toPoly_ne_zero hQ
  have hAq0 : Aq ≠ 0 := by
    rw [hAq, Ne, Polynomial.map_eq_zero_iff hψinj]
    exact hA0
  have hBq0 : Bq ≠ 0 := by
    rw [hBq, Ne, Polynomial.map_eq_zero_iff hψinj]
    exact hB0
  have hdegA : A.natDegree = P.natDegree := natDegree_map_toPoly P
  have hdegB : B.natDegree = Q.natDegree := natDegree_map_toPoly Q
  have hdegAq : Aq.natDegree = P.natDegree := by
    rw [hAq, Polynomial.natDegree_map_eq_of_injective hψinj, hdegA]
  have hdegBq : Bq.natDegree = Q.natDegree := by
    rw [hBq, Polynomial.natDegree_map_eq_of_injective hψinj, hdegB]
  have hpqq : Bq.natDegree < Aq.natDegree := by rw [hdegAq, hdegBq]; exact hpq
  have hjq : j₀ ≤ Q.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd
      (@gcd_dvd_right _ _ Azurite.BPR.gcdMonoidPolynomial Aq Bq) hBq0
    rw [hj₀, hdegBq] at h
    exact h
  -- ℚ-side sResP facts at the gcd degree, transferred down to `AzInt`
  have hq0 : sResP Aq Bq (j₀ - 1) = 0 :=
    sResP_eq_zero_of_lt_gcd Aq Bq hAq0 hBq0 hpqq (by omega) (by omega)
  have hqne : sResP Aq Bq j₀ ≠ 0 :=
    fun h => sResP_natDegree_gcd_ne_zero Aq Bq hAq0 hBq0 hpqq (hj₀ ▸ h)
  have hqnd : (sResP Aq Bq j₀).natDegree = j₀ := by
    have h1 : (sResP Aq Bq j₀).natDegree ≤ j₀ :=
      Polynomial.natDegree_le_iff_degree_le.mpr
        (sResP_degree_le Aq Bq hpqq (by rw [hdegBq]; exact hjq))
    have h2 : j₀ ≤ (sResP Aq Bq j₀).natDegree := by
      have h := natDegree_gcd_le_natDegree_sResP Aq Bq hAq0 hBq0 hpqq hqne
      rwa [hj₀] at h
    omega
  -- fuse the two coefficient maps into one for `sResP_map`/`sResV_map`
  have hAfuse : Aq = (AzPolynomial.toPoly P).map
      ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) := by
    rw [hAq, hA, Polynomial.map_map]
  have hBfuse : Bq = (AzPolynomial.toPoly Q).map
      ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) := by
    rw [hBq, hB, Polynomial.map_map]
  have hρinj : Function.Injective ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) :=
    fun a b h => hιinj (hψinj h)
  have hsResPq : ∀ m, sResP Aq Bq m
      = (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) m).map
          ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) := by
    intro m
    rw [hAfuse, hBfuse, sResP_map hρinj]
  have hsResVq : ∀ m, sResV Aq Bq m
      = (sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) m).map
          ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) := by
    intro m
    rw [hAfuse, hBfuse, sResV_map hρinj]
  have h0 : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) = 0 := by
    have h := hq0
    rw [hsResPq] at h
    exact (Polynomial.map_eq_zero_iff hρinj).mp h
  have hne : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀ ≠ 0 := by
    intro h
    apply hqne
    rw [hsResPq, h, Polynomial.map_zero]
  have hnd : (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀).natDegree = j₀ := by
    have h := hqnd
    rw [hsResPq, Polynomial.natDegree_map_eq_of_injective hρinj] at h
    exact h
  -- boundary identification for the `AzInt` run
  have hbnd := extendedSignedSubresultant_boundary_domain P Q hP hQ hpq hq1 hj₀1 hjq
    h0 hnd hne
  -- the scan lands exactly on `j₀`
  obtain ⟨hmaps, -⟩ := signedSubresultant_toPoly_domain P Q hP hQ hpq hq1
  have hlen : (signedSubresultant P Q).1.size = P.natDegree + 1 := by
    have h := congrArg List.length hmaps
    simpa using h
  have hentry : ∀ ℓ, ℓ < P.natDegree + 1 →
      AzPolynomial.toPoly ((signedSubresultant P Q).1[ℓ]!)
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) ℓ := by
    intro ℓ hℓ
    have h := congrArg (fun l => l[ℓ]?) hmaps
    simp only [List.getElem?_map, List.getElem?_range, hℓ] at h
    have hℓs : ℓ < (signedSubresultant P Q).1.toList.length := by
      simpa [hlen] using hℓ
    rw [List.getElem?_eq_getElem hℓs] at h
    simp only [Option.map_some] at h
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega : ℓ < (signedSubresultant P Q).1.size)]
    simpa [Array.getElem_toList] using h
  have hfst : (extendedSignedSubresultant P Q).1 = (signedSubresultant P Q).1 :=
    extendedSignedSubresultant_fst P Q
  have hfind : firstNonzero (extendedSignedSubresultant P Q).1 = some j₀ := by
    rw [hfst]
    refine firstNonzero_eq_some _ j₀ (by omega) ?_ ?_
    · intro i hi
      apply toPoly_inj.mp
      rw [hentry i (by omega), toPoly_zero]
      -- below `j₀` everything vanishes: transfer the `ℚ`-side vanishing down
      have hqz : sResP Aq Bq i = 0 :=
        sResP_eq_zero_of_lt_gcd Aq Bq hAq0 hBq0 hpqq (by omega) (by omega)
      rw [hsResPq] at hqz
      exact (Polynomial.map_eq_zero_iff hρinj).mp hqz
    · intro h
      have h2 := hentry j₀ (by omega)
      rw [h, toPoly_zero] at h2
      exact hne h2.symm
  -- reduce the wrapper
  have hsnd : (gcdGcdFreePartInt P Q).2
      = divByRingElt ((extendedSignedSubresultant P Q).2.2.2[j₀ - 1]!).leadingCoeff
          (P.leadingCoeff • (extendedSignedSubresultant P Q).2.2.2[j₀ - 1]!) := by
    rw [gcdGcdFreePartInt, if_neg hQ, if_neg (by omega)]
    show (gcdGcdFreePartIntCore P Q).2 = _
    rw [gcdGcdFreePartIntCore]
    split
    rename_i sP s sU sV heq
    have hsP : sP = (extendedSignedSubresultant P Q).1 := by rw [heq]
    have hsV : sV = (extendedSignedSubresultant P Q).2.2.2 := by rw [heq]
    rw [show firstNonzero sP = some j₀ from by rw [hsP]; exact hfind, hsV]
    match j₀, hj₀1 with
    | jj + 1, _ => rfl
  -- names for the boundary tuple
  set W : AzPolynomial AzInt := (extendedSignedSubresultant P Q).2.2.2[j₀ - 1]! with hWdef
  have hW : AzPolynomial.toPoly W
      = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j₀ - 1) := hbnd
  -- `V ≠ 0` over `ℚ` (Proposition 8.42(c) at the non-defective gcd degree)
  have hsRes : Azurite.BPR.Chapter4.sRes Aq Bq j₀ ≠ 0 :=
    ((Azurite.BPR.Chapter4.Proposition_4_26 Aq Bq hAq0 hBq0 j₀
      (by rw [hdegBq]; exact hjq) (by omega)).mp hj₀).2
  obtain ⟨hVnd, hVlc⟩ := sResV_sub_one_natDegree Aq Bq hAq0 hpqq hj₀1
    (by rw [hdegBq]; exact hjq) hsRes
  have hVqne : sResV Aq Bq (j₀ - 1) ≠ 0 := by
    intro h
    rw [h, Polynomial.leadingCoeff_zero] at hVlc
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hAq0) hsRes hVlc.symm
  have hWne : W ≠ 0 := by
    intro h
    apply hVqne
    rw [hsResVq, ← hW, h, toPoly_zero, Polynomial.map_zero]
  have hWlc0 : W.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_toPoly]
    exact Polynomial.leadingCoeff_ne_zero.mpr (toPoly_ne_zero hWne)
  have hPlc0 : P.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_toPoly]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP'
  -- exactness of the normalization (Lemma 10.17 content argument)
  have hVzq_dvd : ((AzPolynomial.toPoly W).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
      ∣ Aq := by
    have hassoc := Azurite.BPR.sResV_gcdFree_associated (K := ℚ) hAq0 hBq0 hpqq hj₀1 hj₀
    have h1 : sResV Aq Bq (j₀ - 1) ∣ Aq :=
      (dvd_mul_right _ _).trans hassoc.dvd
    rw [hW, Polynomial.map_map, ← hsResVq]
    exact h1
  have hdvd_az : ∀ i, W.leadingCoeff ∣ (P.leadingCoeff • W).coeff i := by
    intro i
    apply azInt_dvd_of_toInt_dvd
    have hz := lcof_dvd_lcof_mul_coeff hA0
      (map_toPoly_ne_zero hWne)
      (by rw [← hAq]; exact hVzq_dvd) i
    rw [leadingCoeff_map_toPoly, leadingCoeff_map_toPoly] at hz
    have hcoeff : ((P.leadingCoeff • W).coeff i).toInt
        = (P.leadingCoeff).toInt * (W.coeff i).toInt := by
      rw [coeff_smul, smul_eq_mul, Azurite.AzInt.toInt_mul]
    rw [hcoeff]
    have hWc : ((AzPolynomial.toPoly W).map AzInt.toIntRingHom).coeff i
        = (W.coeff i).toInt := by
      rw [Polynomial.coeff_map, coeff_toPoly_eq]
      rfl
    rwa [hWc] at hz
  -- the division identity at the `AzInt[X]` level, mapped to `ℚ[X]`
  have hCmul := C_mul_toPoly_divByRingElt W.leadingCoeff hWlc0
    (P.leadingCoeff • W) hdvd_az
  have hWqVq : ((AzPolynomial.toPoly W).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
      = sResV Aq Bq (j₀ - 1) := by
    rw [hW, Polynomial.map_map, ← hsResVq]
  have hmapped : Polynomial.C ((W.leadingCoeff.toInt : ℚ))
      * (((AzPolynomial.toPoly (gcdGcdFreePartInt P Q).2).map AzInt.toIntRingHom).map
          (Int.castRingHom ℚ))
      = Polynomial.C ((P.leadingCoeff.toInt : ℚ)) * sResV Aq Bq (j₀ - 1) := by
    have h1 := congrArg (fun p : Polynomial AzInt =>
      (p.map AzInt.toIntRingHom).map (Int.castRingHom ℚ)) hCmul
    simp only [Polynomial.map_mul, Polynomial.map_C] at h1
    have h2 : ((AzPolynomial.toPoly (P.leadingCoeff • W)).map AzInt.toIntRingHom).map
        (Int.castRingHom ℚ)
        = Polynomial.C ((P.leadingCoeff.toInt : ℚ)) * sResV Aq Bq (j₀ - 1) := by
      rw [map_toPoly_smul, Polynomial.map_mul, Polynomial.map_C, hWqVq]
      rfl
    rw [hsnd]
    rw [h2] at h1
    convert h1 using 3
    rfl
  have ha : ((W.leadingCoeff.toInt : ℚ)) ≠ 0 := by
    rw [Ne, Int.cast_eq_zero]
    exact toInt_ne_zero hWlc0
  have hb : ((P.leadingCoeff.toInt : ℚ)) ≠ 0 := by
    rw [Ne, Int.cast_eq_zero]
    exact toInt_ne_zero hPlc0
  have hsnd_eq : (((AzPolynomial.toPoly (gcdGcdFreePartInt P Q).2).map AzInt.toIntRingHom).map
      (Int.castRingHom ℚ))
      = Polynomial.C ((W.leadingCoeff.toInt : ℚ)⁻¹ * (P.leadingCoeff.toInt : ℚ))
        * sResV Aq Bq (j₀ - 1) := by
    have h3 : Polynomial.C ((W.leadingCoeff.toInt : ℚ))⁻¹
        * (Polynomial.C ((W.leadingCoeff.toInt : ℚ))
          * (((AzPolynomial.toPoly (gcdGcdFreePartInt P Q).2).map AzInt.toIntRingHom).map
              (Int.castRingHom ℚ)))
        = Polynomial.C ((W.leadingCoeff.toInt : ℚ))⁻¹
          * (Polynomial.C ((P.leadingCoeff.toInt : ℚ)) * sResV Aq Bq (j₀ - 1)) := by
      rw [hmapped]
    rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1, one_mul] at h3
    rw [h3, ← mul_assoc, ← Polynomial.C_mul]
  have hu : IsUnit (Polynomial.C
      ((W.leadingCoeff.toInt : ℚ)⁻¹ * (P.leadingCoeff.toInt : ℚ)) : ℚ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero ha) hb))
  have hassocV : Associated
      ((((AzPolynomial.toPoly (gcdGcdFreePartInt P Q).2).map AzInt.toIntRingHom).map
          (Int.castRingHom ℚ)))
      (sResV Aq Bq (j₀ - 1)) := by
    rw [hsnd_eq]
    exact Associated.symm ⟨hu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩
  exact (hassocV.mul_mul (Associated.refl _)).trans
    (Azurite.BPR.sResV_gcdFree_associated hAq0 hBq0 hpqq hj₀1 hj₀)

open Azurite.BPR.Chapter8 in
/-- **Gcd correctness of the raw `ℤ` pair's first output** (BPR Algorithm
10.1 over `AzInt`): the first output of `gcdGcdFreePartInt` — the
BPR-normalized `a_p·sResP_{j₀}/s_{j₀}`, whose division is exact by the same
Lemma 10.17 content argument since the non-defective `sResP_{j₀}` has
leading coefficient `s_{j₀}` — has `ℚ[X]` image associated to the gcd.
(Holds for any gcd degree `j₀ ≤ deg Q`, including the coprime case
`j₀ = 0`.) -/
theorem gcdGcdFreePartInt_fst_gcd (P Q : AzPolynomial AzInt)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {j₀ : ℕ}
    (hj₀ : (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
        (((AzPolynomial.toPoly P).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
        (((AzPolynomial.toPoly Q).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))).natDegree
      = j₀) :
    Associated
      ((((AzPolynomial.toPoly (gcdGcdFreePartInt P Q).1).map AzInt.toIntRingHom).map
          (Int.castRingHom ℚ)))
      (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
        (((AzPolynomial.toPoly P).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
        (((AzPolynomial.toPoly Q).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))) := by
  have hψinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  set A : ℤ[X] := (AzPolynomial.toPoly P).map AzInt.toIntRingHom with hA
  set B : ℤ[X] := (AzPolynomial.toPoly Q).map AzInt.toIntRingHom with hB
  set Aq : ℚ[X] := A.map (Int.castRingHom ℚ) with hAq
  set Bq : ℚ[X] := B.map (Int.castRingHom ℚ) with hBq
  have hP' : AzPolynomial.toPoly P ≠ 0 := toPoly_ne_zero hP
  have hA0 : A ≠ 0 := map_toPoly_ne_zero hP
  have hB0 : B ≠ 0 := map_toPoly_ne_zero hQ
  have hAq0 : Aq ≠ 0 := by
    rw [hAq, Ne, Polynomial.map_eq_zero_iff hψinj]
    exact hA0
  have hBq0 : Bq ≠ 0 := by
    rw [hBq, Ne, Polynomial.map_eq_zero_iff hψinj]
    exact hB0
  have hdegAq : Aq.natDegree = P.natDegree := by
    rw [hAq, Polynomial.natDegree_map_eq_of_injective hψinj, natDegree_map_toPoly]
  have hdegBq : Bq.natDegree = Q.natDegree := by
    rw [hBq, Polynomial.natDegree_map_eq_of_injective hψinj, natDegree_map_toPoly]
  have hpqq : Bq.natDegree < Aq.natDegree := by rw [hdegAq, hdegBq]; exact hpq
  have hjq : j₀ ≤ Q.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd
      (@gcd_dvd_right _ _ Azurite.BPR.gcdMonoidPolynomial Aq Bq) hBq0
    rw [hj₀, hdegBq] at h
    exact h
  -- ℚ-side facts at the gcd degree, transferred down to `AzInt`
  have hqne : sResP Aq Bq j₀ ≠ 0 :=
    fun h => sResP_natDegree_gcd_ne_zero Aq Bq hAq0 hBq0 hpqq (hj₀ ▸ h)
  have hqnd : (sResP Aq Bq j₀).natDegree = j₀ := by
    have h1 : (sResP Aq Bq j₀).natDegree ≤ j₀ :=
      Polynomial.natDegree_le_iff_degree_le.mpr
        (sResP_degree_le Aq Bq hpqq (by rw [hdegBq]; exact hjq))
    have h2 : j₀ ≤ (sResP Aq Bq j₀).natDegree := by
      have h := natDegree_gcd_le_natDegree_sResP Aq Bq hAq0 hBq0 hpqq hqne
      rwa [hj₀] at h
    omega
  have hAfuse : Aq = (AzPolynomial.toPoly P).map
      ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) := by
    rw [hAq, hA, Polynomial.map_map]
  have hBfuse : Bq = (AzPolynomial.toPoly Q).map
      ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) := by
    rw [hBq, hB, Polynomial.map_map]
  have hρinj : Function.Injective ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) :=
    fun a b h => hιinj (hψinj h)
  have hsResPq : ∀ m, sResP Aq Bq m
      = (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) m).map
          ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) := by
    intro m
    rw [hAfuse, hBfuse, sResP_map hρinj]
  have hne : sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀ ≠ 0 := by
    intro h
    apply hqne
    rw [hsResPq, h, Polynomial.map_zero]
  have hnd : (sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀).natDegree = j₀ := by
    have h := hqnd
    rw [hsResPq, Polynomial.natDegree_map_eq_of_injective hρinj] at h
    exact h
  -- positional identification of the two output arrays
  obtain ⟨hmaps, hmaps2⟩ := signedSubresultant_toPoly_domain P Q hP hQ hpq hq1
  have hlen : (signedSubresultant P Q).1.size = P.natDegree + 1 := by
    have h := congrArg List.length hmaps
    simpa using h
  have hlen2 : (signedSubresultant P Q).2.size = P.natDegree + 1 := by
    have h := congrArg List.length hmaps2
    simpa using h
  have hentry : ∀ ℓ, ℓ < P.natDegree + 1 →
      AzPolynomial.toPoly ((signedSubresultant P Q).1[ℓ]!)
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) ℓ := by
    intro ℓ hℓ
    have h := congrArg (fun l => l[ℓ]?) hmaps
    simp only [List.getElem?_map, List.getElem?_range, hℓ] at h
    have hℓs : ℓ < (signedSubresultant P Q).1.toList.length := by
      simpa [hlen] using hℓ
    rw [List.getElem?_eq_getElem hℓs] at h
    simp only [Option.map_some] at h
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega : ℓ < (signedSubresultant P Q).1.size)]
    simpa [Array.getElem_toList] using h
  have hentry2 : ∀ ℓ, ℓ < P.natDegree + 1 →
      (signedSubresultant P Q).2[ℓ]!
        = Azurite.BPR.Chapter4.sRes (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) ℓ := by
    intro ℓ hℓ
    have h := congrArg (fun l => l[ℓ]?) hmaps2
    simp only [List.getElem?_map, List.getElem?_range, hℓ] at h
    have hℓs : ℓ < (signedSubresultant P Q).2.toList.length := by
      simpa [hlen2] using hℓ
    rw [List.getElem?_eq_getElem hℓs] at h
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega : ℓ < (signedSubresultant P Q).2.size)]
    simpa [Array.getElem_toList] using h
  have hfstarr : (extendedSignedSubresultant P Q).1 = (signedSubresultant P Q).1 :=
    extendedSignedSubresultant_fst P Q
  have hsndarr : (extendedSignedSubresultant P Q).2.1 = (signedSubresultant P Q).2 :=
    extendedSignedSubresultant_snd_fst P Q
  have hfind : firstNonzero (extendedSignedSubresultant P Q).1 = some j₀ := by
    rw [hfstarr]
    refine firstNonzero_eq_some _ j₀ (by omega) ?_ ?_
    · intro i hi
      apply toPoly_inj.mp
      rw [hentry i (by omega), toPoly_zero]
      have hqz : sResP Aq Bq i = 0 :=
        sResP_eq_zero_of_lt_gcd Aq Bq hAq0 hBq0 hpqq (by omega) (by omega)
      rw [hsResPq] at hqz
      exact (Polynomial.map_eq_zero_iff hρinj).mp hqz
    · intro h
      have h2 := hentry j₀ (by omega)
      rw [h, toPoly_zero] at h2
      exact hne h2.symm
  -- reduce the wrapper (both `some 0` and `some (j+1)` arms give this `fst`)
  have hfstval : (gcdGcdFreePartInt P Q).1
      = divByRingElt ((extendedSignedSubresultant P Q).2.1[j₀]!)
          (P.leadingCoeff • (extendedSignedSubresultant P Q).1[j₀]!) := by
    rw [gcdGcdFreePartInt, if_neg hQ, if_neg (by omega)]
    show (gcdGcdFreePartIntCore P Q).1 = _
    rw [gcdGcdFreePartIntCore]
    split
    rename_i sP s sU sV heq
    have hsP : sP = (extendedSignedSubresultant P Q).1 := by rw [heq]
    have hs : s = (extendedSignedSubresultant P Q).2.1 := by rw [heq]
    rw [show firstNonzero sP = some j₀ from by rw [hsP]; exact hfind, hsP, hs]
    match j₀ with
    | 0 => rfl
    | jj + 1 => rfl
  -- names for the gcd tuple
  set V : AzPolynomial AzInt := (extendedSignedSubresultant P Q).1[j₀]! with hVdef
  have hV : AzPolynomial.toPoly V
      = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j₀ := by
    rw [hVdef, hfstarr]
    exact hentry j₀ (by omega)
  -- the divisor is the leading coefficient: `s_{j₀} = lcof(sResP_{j₀})`
  have hsval : (extendedSignedSubresultant P Q).2.1[j₀]! = V.leadingCoeff := by
    rw [hsndarr, hentry2 j₀ (by omega), ← leadingCoeff_toPoly, hV,
      Polynomial.leadingCoeff, hnd]
    exact (coeff_sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
      (by rw [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]; exact hpq)
      (by rw [AzPolynomial.natDegree_toPoly]; omega)).symm
  have hVne : V ≠ 0 := by
    intro h
    apply hne
    rw [← hV, h, toPoly_zero]
  have hVlc0 : V.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_toPoly]
    exact Polynomial.leadingCoeff_ne_zero.mpr (toPoly_ne_zero hVne)
  -- exactness (Lemma 10.17 content argument, `sResP_{j₀} ~ gcd ∣ P` over `ℚ`)
  have hVzq_dvd : ((AzPolynomial.toPoly V).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
      ∣ Aq := by
    have hassoc := associated_sResP_gcd Aq Bq hAq0 hBq0 hpqq hj₀
    have h1 : sResP Aq Bq j₀ ∣ Aq :=
      hassoc.dvd.trans (@gcd_dvd_left _ _ Azurite.BPR.gcdMonoidPolynomial Aq Bq)
    rw [hV, Polynomial.map_map, ← hsResPq]
    exact h1
  have hdvd_az : ∀ i, V.leadingCoeff ∣ (P.leadingCoeff • V).coeff i := by
    intro i
    apply azInt_dvd_of_toInt_dvd
    have hz := lcof_dvd_lcof_mul_coeff hA0
      (map_toPoly_ne_zero hVne)
      (by rw [← hAq]; exact hVzq_dvd) i
    rw [leadingCoeff_map_toPoly, leadingCoeff_map_toPoly] at hz
    have hcoeff : ((P.leadingCoeff • V).coeff i).toInt
        = (P.leadingCoeff).toInt * (V.coeff i).toInt := by
      rw [coeff_smul, smul_eq_mul, Azurite.AzInt.toInt_mul]
    rw [hcoeff]
    have hVc : ((AzPolynomial.toPoly V).map AzInt.toIntRingHom).coeff i
        = (V.coeff i).toInt := by
      rw [Polynomial.coeff_map, coeff_toPoly_eq]
      rfl
    rwa [hVc] at hz
  have hCmul := C_mul_toPoly_divByRingElt V.leadingCoeff hVlc0
    (P.leadingCoeff • V) hdvd_az
  -- pass to `ℚ[X]`
  have hVqPq : ((AzPolynomial.toPoly V).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
      = sResP Aq Bq j₀ := by
    rw [hV, Polynomial.map_map, ← hsResPq]
  have hmapped : Polynomial.C ((V.leadingCoeff.toInt : ℚ))
      * (((AzPolynomial.toPoly (gcdGcdFreePartInt P Q).1).map AzInt.toIntRingHom).map
          (Int.castRingHom ℚ))
      = Polynomial.C ((P.leadingCoeff.toInt : ℚ)) * sResP Aq Bq j₀ := by
    have h1 := congrArg (fun p : Polynomial AzInt =>
      (p.map AzInt.toIntRingHom).map (Int.castRingHom ℚ)) hCmul
    simp only [Polynomial.map_mul, Polynomial.map_C] at h1
    have h2 : ((AzPolynomial.toPoly (P.leadingCoeff • V)).map AzInt.toIntRingHom).map
        (Int.castRingHom ℚ)
        = Polynomial.C ((P.leadingCoeff.toInt : ℚ)) * sResP Aq Bq j₀ := by
      rw [map_toPoly_smul, Polynomial.map_mul, Polynomial.map_C, hVqPq]
      rfl
    rw [hfstval, hsval]
    rw [h2] at h1
    convert h1 using 3
    rfl
  have hPlc0 : P.leadingCoeff ≠ 0 := by
    rw [← leadingCoeff_toPoly]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP'
  have ha : ((V.leadingCoeff.toInt : ℚ)) ≠ 0 := by
    rw [Ne, Int.cast_eq_zero]
    exact toInt_ne_zero hVlc0
  have hb : ((P.leadingCoeff.toInt : ℚ)) ≠ 0 := by
    rw [Ne, Int.cast_eq_zero]
    exact toInt_ne_zero hPlc0
  have hfst_eq : (((AzPolynomial.toPoly (gcdGcdFreePartInt P Q).1).map AzInt.toIntRingHom).map
      (Int.castRingHom ℚ))
      = Polynomial.C ((V.leadingCoeff.toInt : ℚ)⁻¹ * (P.leadingCoeff.toInt : ℚ))
        * sResP Aq Bq j₀ := by
    have h3 : Polynomial.C ((V.leadingCoeff.toInt : ℚ))⁻¹
        * (Polynomial.C ((V.leadingCoeff.toInt : ℚ))
          * (((AzPolynomial.toPoly (gcdGcdFreePartInt P Q).1).map AzInt.toIntRingHom).map
              (Int.castRingHom ℚ)))
        = Polynomial.C ((V.leadingCoeff.toInt : ℚ))⁻¹
          * (Polynomial.C ((P.leadingCoeff.toInt : ℚ)) * sResP Aq Bq j₀) := by
      rw [hmapped]
    rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1, one_mul] at h3
    rw [h3, ← mul_assoc, ← Polynomial.C_mul]
  have hu : IsUnit (Polynomial.C
      ((V.leadingCoeff.toInt : ℚ)⁻¹ * (P.leadingCoeff.toInt : ℚ)) : ℚ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero ha) hb))
  have hassocP : Associated
      ((((AzPolynomial.toPoly (gcdGcdFreePartInt P Q).1).map AzInt.toIntRingHom).map
          (Int.castRingHom ℚ)))
      (sResP Aq Bq j₀) := by
    rw [hfst_eq]
    exact Associated.symm ⟨hu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩
  exact hassocP.trans (associated_sResP_gcd Aq Bq hAq0 hBq0 hpqq hj₀)

end Azurite.AzPolynomial
