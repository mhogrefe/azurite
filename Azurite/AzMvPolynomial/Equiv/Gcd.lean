import Azurite.AzInt.Equiv.NormalizedGcd
import Azurite.AzMvPolynomial.Gcd
import Azurite.AzMvPolynomial.Equiv.FinSuccEquiv
import Azurite.AzMvPolynomial.Equiv.FinZeroAlgEquiv
import Azurite.AzPolynomial.Equiv.Map
import Azurite.AzPolynomial.Equiv.Predicates
import Azurite.AzMvPolynomial.Equiv.OfAzPolynomial
import Azurite.AzMvPolynomial.Equiv.CompareEmbed
import Azurite.AzMvPolynomial.Equiv.Derivative
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Correctness of `AzMvPolynomial.gcd`

Top-level correctness of the multivariate polynomial gcd over `AzInt`.

**Main results** (`P, Q : AzMvPolynomial n AzInt ord`, images in
`MvPolynomial (Fin n) ℤ` via `toMvPoly` followed by the `AzInt → ℤ`
coefficient map — no gcd instance on `MvPolynomial` is required, and
Mathlib provides no canonical `NormalizedGCDMonoid (MvPolynomial σ R)`
instance to compare against):

* `AzMvPolynomial.gcd_dvd_left` / `gcd_dvd_right` / `dvd_gcd` — the gcd
  divisibility characterization **in the computable ring itself**;
* `AzMvPolynomial.toMvPoly_gcd_dvd_left` / `toMvPoly_gcd_dvd_right` /
  `dvd_toMvPoly_gcd` — the same characterization for the represented
  polynomials in `MvPolynomial (Fin n) ℤ`;
* `AzMvPolynomial.towerBridge_toNested_gcd` — the sharper *normalized*
  equality in the nested model `ModelPoly n = ℤ[x_{n-1}]…[x_0]`
  (iterated `Polynomial`): the model image of `gcd P Q` **equals**
  Mathlib's `NormalizedGCDMonoid` gcd of the model images.

## Architecture

The proof assembles the three phases:

* the **model tower** `ModelPoly n` (`GcdModelRing`/`intModelTower`) is the
  mathematical mirror of `NestedPoly n` — `ℤ`, then `Polynomial` at each
  level, with `NormalizedGCDMonoid` propagating by Mathlib's
  `Polynomial.normalizedGcdMonoid`;
* the **bridge tower** `towerBridge n : NormalizedGcdBridge (NestedPoly n)
  (ModelPoly n)` iterates `NormalizedGcdBridge.step` (Phase 2, one tower
  level of gcd correctness) from the base bridge
  `Azurite.AzInt.intNormalizedGcdBridge`;
* the **boundary** `toNested`/`ofNested` conversions are identified with a
  ring isomorphism `nestedRingEquiv n` assembled from the proven bundled
  equivalences `finZeroAlgEquiv`/`finSuccAlgEquiv`/`ringEquivPolynomial`
  (`toNested_eq`/`ofNested_eq`), giving the round trips and divisibility
  transport.
-/

namespace Azurite

open AzMvPolynomial

/-! ### The mathematical model tower: `ℤ`, `ℤ[y]`, `ℤ[y][x]`, … -/

/-- A carrier bundled with the instances the *model* side of the gcd tower
needs: a `NormalizedGCDMonoid` domain. Mirror of `GcdRing` (the computable
side). -/
structure GcdModelRing where
  /-- The carrier type of this model level. -/
  carrier : Type
  [commRing : CommRing carrier]
  [isDomain : IsDomain carrier]
  [normalizedGCD : NormalizedGCDMonoid carrier]

attribute [instance] GcdModelRing.commRing GcdModelRing.isDomain
  GcdModelRing.normalizedGCD

/-- One model tower step: adjoin one polynomial variable
(`NormalizedGCDMonoid` propagates by `Polynomial.normalizedGcdMonoid`). -/
noncomputable def GcdModelRing.step (S : GcdModelRing) : GcdModelRing :=
  { carrier := Polynomial S.carrier
    commRing := inferInstance
    isDomain := inferInstance
    normalizedGCD := inferInstance }

/-- The `ℤ`-based model tower: `ℤ`, `ℤ[x]`, `ℤ[x][T]`, … -/
noncomputable def intModelTower : ℕ → GcdModelRing
  | 0 =>
    { carrier := ℤ
      commRing := inferInstance
      isDomain := inferInstance
      normalizedGCD := inferInstance }
  | n + 1 => (intModelTower n).step

/-- The `n`-level model carrier, the iterated `Polynomial^n ℤ` — the
mathematical mirror of `NestedPoly n`. -/
noncomputable abbrev ModelPoly (n : ℕ) : Type := (intModelTower n).carrier

/-! ### The bridge tower -/

/-- The bridge tower with its surjectivity invariant: at each level, a
`NormalizedGcdBridge (NestedPoly n) (ModelPoly n)` whose homomorphism is
surjective, built by iterating `NormalizedGcdBridge.step` from the base
bridge `AzInt → ℤ`. -/
noncomputable def AzMvPolynomial.towerBridgeAux : (n : ℕ) →
    { β : Azurite.AzPolynomial.NormalizedGcdBridge (NestedPoly n)
          (ModelPoly n) // Function.Surjective β.hom }
  | 0 =>
    ⟨Azurite.AzInt.intNormalizedGcdBridge,
     Azurite.AzInt.intNormalizedGcdBridge_hom_surjective⟩
  | n + 1 =>
    ⟨((towerBridgeAux n).1).step (towerBridgeAux n).2,
     Azurite.AzPolynomial.NormalizedGcdBridge.step_hom_surjective _ _⟩

/-- **The bridge tower**: the correctness bridge from the computable nested
tower to its mathematical model, at every level. Its `map_ngcd` field is
the level-`n` normalized-gcd correctness. -/
noncomputable def AzMvPolynomial.towerBridge (n : ℕ) :
    Azurite.AzPolynomial.NormalizedGcdBridge (NestedPoly n) (ModelPoly n) :=
  (AzMvPolynomial.towerBridgeAux n).1

/-! ### The nested descent as a ring isomorphism -/

variable {ord : MonomialOrder}

/-- The boundary descent `AzMvPolynomial n AzInt ord ≃+* NestedPoly n` as a
bundled ring isomorphism, assembled from the proven equivalences
`finZeroAlgEquiv`, `finSuccAlgEquiv` and `ringEquivPolynomial`. The
computable `toNested`/`ofNested` are its two directions
(`toNested_eq`/`ofNested_eq`). -/
noncomputable def AzMvPolynomial.nestedRingEquiv :
    (n : ℕ) → AzMvPolynomial n AzInt ord ≃+* NestedPoly n
  | 0 => (AzMvPolynomial.finZeroAlgEquiv (R := AzInt)
      (ord := ord)).toRingEquiv
  | n + 1 =>
    (AzMvPolynomial.finSuccAlgEquiv (R := AzInt) (n := n)
        (ord := ord)).toRingEquiv.trans
      ((Azurite.AzPolynomial.ringEquivPolynomial).trans
        ((Polynomial.mapEquiv (nestedRingEquiv n)).trans
          (Azurite.AzPolynomial.ringEquivPolynomial
            (R := NestedPoly n)).symm))

/-- The computable descent `toNested` is the forward direction of
`nestedRingEquiv`. -/
theorem AzMvPolynomial.toNested_eq :
    ∀ (n : ℕ) (p : AzMvPolynomial n AzInt ord),
      toNested n p = nestedRingEquiv n p
  | 0, _ => rfl
  | n + 1, p => by
    have ih : (toNested (ord := ord) n)
        = ⇑(nestedRingEquiv (ord := ord) n) :=
      funext (toNested_eq n)
    show AzPolynomial.normalize
          ((finSuccEquiv p).coeffs.map (toNested (ord := ord) n))
        = AzPolynomial.ofPoly
            ((AzPolynomial.toPoly (finSuccEquiv p)).map
              ((nestedRingEquiv (ord := ord) n :
                  AzMvPolynomial n AzInt ord →+* NestedPoly n)))
    rw [ih]
    show AzPolynomial.map
          ((nestedRingEquiv (ord := ord) n :
              AzMvPolynomial n AzInt ord →+* NestedPoly n))
          (finSuccEquiv p)
        = AzPolynomial.ofPoly
            ((AzPolynomial.toPoly (finSuccEquiv p)).map _)
    rw [← Azurite.AzPolynomial.toPoly_map, ofPoly_toPoly]

/-- The computable ascent `ofNested` is the inverse direction of
`nestedRingEquiv`. -/
theorem AzMvPolynomial.ofNested_eq :
    ∀ (n : ℕ) (x : NestedPoly n),
      ofNested (ord := ord) n x = (nestedRingEquiv (ord := ord) n).symm x
  | 0, _ => rfl
  | n + 1, q => by
    have ih : (ofNested (ord := ord) n)
        = ⇑(nestedRingEquiv (ord := ord) n).symm :=
      funext (ofNested_eq n)
    show finSuccEquivSymm
          (AzPolynomial.normalize
            ((q : AzPolynomial (NestedPoly n)).coeffs.map
              (ofNested (ord := ord) n)))
        = finSuccEquivSymm
            (AzPolynomial.ofPoly
              ((AzPolynomial.toPoly (q : AzPolynomial (NestedPoly n))).map
                ((nestedRingEquiv (ord := ord) n).symm :
                    NestedPoly n →+* AzMvPolynomial n AzInt ord)))
    congr 1
    rw [ih]
    show AzPolynomial.map
          ((nestedRingEquiv (ord := ord) n).symm :
              NestedPoly n →+* AzMvPolynomial n AzInt ord)
          (q : AzPolynomial (NestedPoly n))
        = AzPolynomial.ofPoly
            ((AzPolynomial.toPoly (q : AzPolynomial (NestedPoly n))).map _)
    rw [← Azurite.AzPolynomial.toPoly_map, ofPoly_toPoly]

/-! ### Round trips and divisibility transport -/

theorem AzMvPolynomial.toNested_ofNested (n : ℕ) (x : NestedPoly n) :
    toNested (ord := ord) n (ofNested n x) = x := by
  rw [toNested_eq, ofNested_eq, RingEquiv.apply_symm_apply]

theorem AzMvPolynomial.ofNested_toNested (n : ℕ)
    (P : AzMvPolynomial n AzInt ord) : ofNested n (toNested n P) = P := by
  rw [toNested_eq, ofNested_eq, RingEquiv.symm_apply_apply]

theorem AzMvPolynomial.toNested_dvd_iff {n : ℕ}
    {x y : AzMvPolynomial n AzInt ord} :
    toNested n x ∣ toNested n y ↔ x ∣ y := by
  rw [toNested_eq, toNested_eq]
  exact map_dvd_iff (nestedRingEquiv (ord := ord) n)

/-! ### `gcd` through the boundary -/

/-- The descent of `AzMvPolynomial.gcd` is the nested normalized gcd of the
descents. -/
theorem AzMvPolynomial.toNested_gcd {n : ℕ}
    (P Q : AzMvPolynomial n AzInt ord) :
    toNested n (AzMvPolynomial.gcd P Q)
      = NormalizedGcd.ngcd (toNested n P) (toNested n Q) := by
  rw [AzMvPolynomial.gcd, toNested_ofNested]

/-- **The sharper, normalized correctness statement**: in the nested
mathematical model `ModelPoly n` (the iterated `Polynomial^n ℤ`, a
`NormalizedGCDMonoid`), the model image of `AzMvPolynomial.gcd P Q`
**equals** Mathlib's normalized gcd of the model images. -/
theorem AzMvPolynomial.towerBridge_toNested_gcd {n : ℕ}
    (P Q : AzMvPolynomial n AzInt ord) :
    (towerBridge n).hom (toNested n (AzMvPolynomial.gcd P Q))
      = GCDMonoid.gcd ((towerBridge n).hom (toNested n P))
          ((towerBridge n).hom (toNested n Q)) := by
  rw [toNested_gcd]
  exact (towerBridge n).map_ngcd _ _

/-! ### The divisibility characterization, in the computable ring -/

/-- `AzMvPolynomial.gcd P Q` divides `P`. -/
theorem AzMvPolynomial.gcd_dvd_left {n : ℕ}
    (P Q : AzMvPolynomial n AzInt ord) : AzMvPolynomial.gcd P Q ∣ P := by
  rw [← toNested_dvd_iff]
  apply (towerBridge n).dvd_reflect
  rw [towerBridge_toNested_gcd]
  exact GCDMonoid.gcd_dvd_left _ _

/-- `AzMvPolynomial.gcd P Q` divides `Q`. -/
theorem AzMvPolynomial.gcd_dvd_right {n : ℕ}
    (P Q : AzMvPolynomial n AzInt ord) : AzMvPolynomial.gcd P Q ∣ Q := by
  rw [← toNested_dvd_iff]
  apply (towerBridge n).dvd_reflect
  rw [towerBridge_toNested_gcd]
  exact GCDMonoid.gcd_dvd_right _ _

/-- Every common divisor of `P` and `Q` divides `AzMvPolynomial.gcd P Q`. -/
theorem AzMvPolynomial.dvd_gcd {n : ℕ}
    {e P Q : AzMvPolynomial n AzInt ord} (hP : e ∣ P) (hQ : e ∣ Q) :
    e ∣ AzMvPolynomial.gcd P Q := by
  rw [← toNested_dvd_iff] at hP hQ ⊢
  apply (towerBridge n).dvd_reflect
  rw [towerBridge_toNested_gcd]
  exact GCDMonoid.dvd_gcd (map_dvd _ hP) (map_dvd _ hQ)

/-! ### The divisibility characterization, in `MvPolynomial (Fin n) ℤ` -/

/-- The composite ring isomorphism onto the `ℤ`-coefficient model,
`AzMvPolynomial n AzInt ord ≃+* MvPolynomial (Fin n) ℤ`. -/
noncomputable def AzMvPolynomial.ringEquivMvPolynomialInt
    {n : ℕ} {ord : MonomialOrder} :
    AzMvPolynomial n AzInt ord ≃+* MvPolynomial (Fin n) ℤ :=
  (ringEquivMvPolynomial).trans
    (MvPolynomial.mapEquiv (Fin n) Azurite.AzInt.ringEquivInt)

theorem AzMvPolynomial.ringEquivMvPolynomialInt_apply {n : ℕ}
    (P : AzMvPolynomial n AzInt ord) :
    ringEquivMvPolynomialInt P
      = MvPolynomial.map AzInt.toIntRingHom P.toMvPoly := rfl

/-- **`toMvPoly_gcd_dvd_left`**: the represented `MvPolynomial (Fin n) ℤ`
image of the gcd divides the image of `P` (no gcd instance on
`MvPolynomial` needed). -/
theorem AzMvPolynomial.toMvPoly_gcd_dvd_left {n : ℕ}
    (P Q : AzMvPolynomial n AzInt ord) :
    MvPolynomial.map AzInt.toIntRingHom (AzMvPolynomial.gcd P Q).toMvPoly
      ∣ MvPolynomial.map AzInt.toIntRingHom P.toMvPoly := by
  rw [← ringEquivMvPolynomialInt_apply, ← ringEquivMvPolynomialInt_apply]
  exact (map_dvd_iff (ringEquivMvPolynomialInt (n := n) (ord := ord))).mpr
    (gcd_dvd_left P Q)

/-- **`toMvPoly_gcd_dvd_right`**: the image of the gcd divides the image of
`Q`. -/
theorem AzMvPolynomial.toMvPoly_gcd_dvd_right {n : ℕ}
    (P Q : AzMvPolynomial n AzInt ord) :
    MvPolynomial.map AzInt.toIntRingHom (AzMvPolynomial.gcd P Q).toMvPoly
      ∣ MvPolynomial.map AzInt.toIntRingHom Q.toMvPoly := by
  rw [← ringEquivMvPolynomialInt_apply, ← ringEquivMvPolynomialInt_apply]
  exact (map_dvd_iff (ringEquivMvPolynomialInt (n := n) (ord := ord))).mpr
    (gcd_dvd_right P Q)

/-- **`dvd_toMvPoly_gcd`**: every common divisor (in
`MvPolynomial (Fin n) ℤ`) of the images of `P` and `Q` divides the image of
their gcd. -/
theorem AzMvPolynomial.dvd_toMvPoly_gcd {n : ℕ}
    {e : MvPolynomial (Fin n) ℤ} {P Q : AzMvPolynomial n AzInt ord}
    (hP : e ∣ MvPolynomial.map AzInt.toIntRingHom P.toMvPoly)
    (hQ : e ∣ MvPolynomial.map AzInt.toIntRingHom Q.toMvPoly) :
    e ∣ MvPolynomial.map AzInt.toIntRingHom
        (AzMvPolynomial.gcd P Q).toMvPoly := by
  rw [← ringEquivMvPolynomialInt_apply] at hP hQ ⊢
  obtain ⟨e', rfl⟩ :=
    (ringEquivMvPolynomialInt (n := n) (ord := ord)).surjective e
  have hP' : e' ∣ P := (map_dvd_iff (ringEquivMvPolynomialInt)).mp hP
  have hQ' : e' ∣ Q := (map_dvd_iff (ringEquivMvPolynomialInt)).mp hQ
  exact (map_dvd_iff (ringEquivMvPolynomialInt)).mpr (dvd_gcd hP' hQ')

/-! ### Small boundary bridges -/

theorem AzMvPolynomial.toNested_zero (n : ℕ) :
    toNested (ord := ord) n 0 = 0 := by
  rw [toNested_eq]
  exact map_zero _

theorem AzMvPolynomial.toNested_one (n : ℕ) :
    toNested (ord := ord) n 1 = 1 := by
  rw [toNested_eq]
  exact map_one _

theorem AzMvPolynomial.toNested_injective {n : ℕ} :
    Function.Injective (toNested (ord := ord) n) := by
  intro a b h
  rw [toNested_eq, toNested_eq] at h
  exact (nestedRingEquiv n).injective h

/-- The successor-level bridge homomorphism is `toPoly` followed by the
coefficient-wise previous-level homomorphism. -/
theorem AzMvPolynomial.towerBridge_succ_hom_apply {n : ℕ}
    (X : NestedPoly (n + 1)) :
    (towerBridge (n + 1)).hom X
      = (AzPolynomial.toPoly (nestedDown X)).map (towerBridge n).hom := rfl

/-- The successor-level bridge maps `AzPolynomial.C` to `Polynomial.C`. -/
theorem AzMvPolynomial.towerBridge_succ_hom_C {n : ℕ} (y : NestedPoly n) :
    (towerBridge (n + 1)).hom (AzPolynomial.C y)
      = Polynomial.C ((towerBridge n).hom y) := by
  have h1 : (towerBridge (n + 1)).hom (AzPolynomial.C y)
      = (AzPolynomial.toPoly (AzPolynomial.C y)).map (towerBridge n).hom :=
    towerBridge_succ_hom_apply _
  rw [h1, AzPolynomial.toPoly_C, Polynomial.map_C]

/-! ### Convenience gcd corollaries -/

/-- `normalized` represents Mathlib's `normalize` in the nested model. -/
theorem AzMvPolynomial.towerBridge_toNested_normalized {n : ℕ}
    (P : AzMvPolynomial n AzInt ord) :
    (towerBridge n).hom (toNested n (AzMvPolynomial.normalized P))
      = _root_.normalize ((towerBridge n).hom (toNested n P)) := by
  rw [AzMvPolynomial.normalized, toNested_ofNested]
  exact Azurite.AzPolynomial.map_norm (towerBridge n).map_ngcd _

/-- The gcd is symmetric. -/
theorem AzMvPolynomial.gcd_comm {n : ℕ} (P Q : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial.gcd P Q = AzMvPolynomial.gcd Q P := by
  apply toNested_injective
  apply (towerBridge n).injective
  rw [towerBridge_toNested_gcd, towerBridge_toNested_gcd, _root_.gcd_comm]

/-- The gcd is associative. -/
theorem AzMvPolynomial.gcd_assoc {n : ℕ}
    (P Q R : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial.gcd (AzMvPolynomial.gcd P Q) R
      = AzMvPolynomial.gcd P (AzMvPolynomial.gcd Q R) := by
  apply toNested_injective
  apply (towerBridge n).injective
  simp only [towerBridge_toNested_gcd]
  exact _root_.gcd_assoc _ _ _

/-- `gcd P 0` is the normalized representative of `P`. -/
theorem AzMvPolynomial.gcd_zero_right {n : ℕ}
    (P : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial.gcd P 0 = AzMvPolynomial.normalized P := by
  rw [AzMvPolynomial.gcd, AzMvPolynomial.normalized, toNested_zero]
  rfl

/-- `gcd 0 P` is the normalized representative of `P`. -/
theorem AzMvPolynomial.gcd_zero_left {n : ℕ}
    (P : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial.gcd 0 P = AzMvPolynomial.normalized P := by
  rw [gcd_comm, gcd_zero_right]

/-- `gcd P P` is the normalized representative of `P`. -/
theorem AzMvPolynomial.gcd_self {n : ℕ} (P : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial.gcd P P = AzMvPolynomial.normalized P := by
  apply toNested_injective
  apply (towerBridge n).injective
  rw [towerBridge_toNested_gcd, towerBridge_toNested_normalized]
  exact gcd_same _

/-! ### Content and primitive part -/

/-- Descent of the flat `content`: it is `contentGen` of the descent. -/
theorem AzMvPolynomial.toNested_content {n : ℕ}
    (P : AzMvPolynomial (n + 1) AzInt ord) :
    toNested n (AzMvPolynomial.content P)
      = Azurite.AzPolynomial.contentGen (nestedDown (toNested (n + 1) P)) := by
  rw [AzMvPolynomial.content, toNested_ofNested]

/-- **`content` represents `Polynomial.content`**: the model image of the
content is Mathlib's content of the (one-level) model image of `P`. -/
theorem AzMvPolynomial.towerBridge_toNested_content {n : ℕ}
    (P : AzMvPolynomial (n + 1) AzInt ord) :
    (towerBridge n).hom (toNested n (AzMvPolynomial.content P))
      = ((towerBridge (n + 1)).hom (toNested (n + 1) P)).content := by
  rw [toNested_content, towerBridge_succ_hom_apply]
  exact Azurite.AzPolynomial.map_contentGen (towerBridge n).map_ngcd
    (nestedDown (toNested (n + 1) P))

/-- The content divides every `x_0`-coefficient of the descent (in the
computable nested ring). -/
theorem AzMvPolynomial.content_dvd_coeff {n : ℕ}
    (P : AzMvPolynomial (n + 1) AzInt ord) (i : ℕ) :
    Azurite.AzPolynomial.contentGen (nestedDown (toNested (n + 1) P))
      ∣ (nestedDown (toNested (n + 1) P)).coeff i := by
  apply (towerBridge n).dvd_reflect
  rw [Azurite.AzPolynomial.map_contentGen (towerBridge n).map_ngcd]
  have h1 : ((AzPolynomial.toPoly (nestedDown (toNested (n + 1) P))).map
          (towerBridge n).hom).coeff i
      = (towerBridge n).hom ((nestedDown (toNested (n + 1) P)).coeff i) := by
    rw [Polynomial.coeff_map, coeff_toPoly_eq]
  rw [← h1]
  exact Polynomial.content_dvd_coeff _

/-- **The exact content–primitive-part decomposition**, at the computable
nested level: `C(content P) · primitivePart P = P` (descended), with no
side conditions (`0 = 0` at `P = 0`). -/
theorem AzMvPolynomial.toNested_content_mul_primitivePart {n : ℕ}
    (P : AzMvPolynomial (n + 1) AzInt ord) :
    AzPolynomial.C (toNested n (AzMvPolynomial.content P))
        * nestedDown (toNested (n + 1) (AzMvPolynomial.primitivePart P))
      = nestedDown (toNested (n + 1) P) := by
  rw [toNested_content, AzMvPolynomial.primitivePart, toNested_ofNested]
  by_cases hX : nestedDown (toNested (n + 1) P) = 0
  · rw [hX,
      show Azurite.AzPolynomial.contentGen
        (0 : AzPolynomial (NestedPoly n)) = 0 from rfl,
      show (AzPolynomial.C (0 : NestedPoly n)) = 0 from
        map_zero Azurite.AzPolynomial.CHom,
      zero_mul]
  · have hc : Azurite.AzPolynomial.contentGen
        (nestedDown (toNested (n + 1) P)) ≠ 0 :=
      Azurite.AzPolynomial.contentGen_ne_zero (towerBridge n).injective
        (towerBridge n).map_ngcd hX
    apply toPoly_inj.mp
    rw [Azurite.AzPolynomial.toPoly_mul, AzPolynomial.toPoly_C]
    exact Azurite.AzPolynomial.C_mul_toPoly_divByRingElt _ hc _
      (content_dvd_coeff P)

/-- **`primitivePart` represents `Polynomial.primPart`** (for `P ≠ 0`; at
`0` our convention gives `0` where Mathlib's gives `1`). -/
theorem AzMvPolynomial.towerBridge_toNested_primitivePart {n : ℕ}
    {P : AzMvPolynomial (n + 1) AzInt ord} (hP : P ≠ 0) :
    (towerBridge (n + 1)).hom
        (toNested (n + 1) (AzMvPolynomial.primitivePart P))
      = ((towerBridge (n + 1)).hom (toNested (n + 1) P)).primPart := by
  have hX0 : nestedDown (toNested (ord := ord) (n + 1) P) ≠ 0 := by
    intro h
    apply hP
    apply toNested_injective (n := n + 1)
    rw [toNested_zero]
    exact h
  -- the D-level exact-division identity, mapped into the model
  have hkey := congrArg (Polynomial.map (towerBridge n).hom)
    (Azurite.AzPolynomial.C_mul_toPoly_divByRingElt
      (Azurite.AzPolynomial.contentGen (nestedDown (toNested (n + 1) P)))
      (Azurite.AzPolynomial.contentGen_ne_zero (towerBridge n).injective
        (towerBridge n).map_ngcd hX0)
      (nestedDown (toNested (n + 1) P))
      (content_dvd_coeff P))
  rw [Polynomial.map_mul, Polynomial.map_C,
    Azurite.AzPolynomial.map_contentGen (towerBridge n).map_ngcd,
    ← towerBridge_succ_hom_apply] at hkey
  -- identify the primitive-part image
  have himg : (towerBridge (n + 1)).hom
        (toNested (n + 1) (AzMvPolynomial.primitivePart P))
      = (AzPolynomial.toPoly
          (Azurite.AzPolynomial.divByRingElt
            (Azurite.AzPolynomial.contentGen (nestedDown (toNested (n + 1) P)))
            (nestedDown (toNested (n + 1) P)))).map (towerBridge n).hom := by
    rw [AzMvPolynomial.primitivePart, toNested_ofNested]
    exact towerBridge_succ_hom_apply _
  rw [himg]
  have hA0 : (towerBridge (n + 1)).hom (toNested (n + 1) P) ≠ 0 := by
    intro h
    apply hX0
    show toNested (ord := ord) (n + 1) P = 0
    apply (towerBridge (n + 1)).injective
    rw [h, map_zero]
  have hc0 : (Polynomial.C ((towerBridge (n + 1)).hom
      (toNested (n + 1) P)).content : Polynomial (ModelPoly n)) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero, Polynomial.content_eq_zero_iff]
    exact hA0
  apply mul_left_cancel₀ hc0
  rw [hkey]
  exact ((towerBridge (n + 1)).hom (toNested (n + 1) P)).eq_C_content_mul_primPart

/-! ### Predicates: primitivity and coprimality -/

/-- **`isPrimitive` decides `Polynomial.IsPrimitive`** of the (one-level)
nested model image. -/
theorem AzMvPolynomial.isPrimitive_iff {n : ℕ}
    {P : AzMvPolynomial (n + 1) AzInt ord} :
    AzMvPolynomial.isPrimitive P = true
      ↔ ((towerBridge (n + 1)).hom (toNested (n + 1) P)).IsPrimitive := by
  rw [AzMvPolynomial.isPrimitive, beq_iff_eq,
    Polynomial.isPrimitive_iff_content_eq_one, ← towerBridge_toNested_content]
  constructor
  · intro h
    rw [h, toNested_one, map_one]
  · intro h
    apply toNested_injective (n := n)
    apply (towerBridge n).injective
    rw [h, toNested_one, map_one]

/-- A flat characterization: the normalized gcd is `1` iff every common
divisor (in the computable ring) is a unit. NB this is the **strong**
(content-included) coprimality of `ℤ[x⃗]`; it is *not* what
`AzMvPolynomial.coprime` decides (that is the weaker fraction-field notion,
`coprime_iff`). -/
theorem AzMvPolynomial.gcd_eq_one_iff {n : ℕ}
    {P Q : AzMvPolynomial n AzInt ord} :
    AzMvPolynomial.gcd P Q = 1
      ↔ ∀ e : AzMvPolynomial n AzInt ord, e ∣ P → e ∣ Q → IsUnit e := by
  constructor
  · intro h e heP heQ
    refine isUnit_of_dvd_one ?_
    rw [← h]
    exact dvd_gcd heP heQ
  · intro h
    have hu : IsUnit (AzMvPolynomial.gcd P Q) :=
      h _ (gcd_dvd_left P Q) (gcd_dvd_right P Q)
    -- transport to the model, where the gcd is normalized
    have huM : IsUnit ((towerBridge n).hom
        (toNested n (AzMvPolynomial.gcd P Q))) := by
      have h1 : (towerBridge n).hom (toNested n (AzMvPolynomial.gcd P Q))
          = ((towerBridge n).hom.comp
              ((nestedRingEquiv (ord := ord) n :
                AzMvPolynomial n AzInt ord →+* NestedPoly n)))
              (AzMvPolynomial.gcd P Q) :=
        congrArg (towerBridge n).hom (toNested_eq n _)
      rw [h1]
      exact hu.map _
    rw [towerBridge_toNested_gcd] at huM
    have hM : GCDMonoid.gcd
        ((towerBridge n).hom (toNested n P))
        ((towerBridge n).hom (toNested n Q)) = 1 := by
      rw [← normalize_gcd]
      exact normalize_eq_one.mpr huM
    apply toNested_injective (n := n)
    apply (towerBridge n).injective
    rw [towerBridge_toNested_gcd, hM, toNested_one, map_one]

/-! ### The fraction-field coprimality characterization

`AzMvPolynomial.coprime P Q` decides that `gcd P Q` is a nonzero constant —
equivalently, that the represented polynomials have no common factor of
positive total degree. Over `ℚ[x⃗]` (base change of the coefficients to
`ℚ`) this is exactly "the gcd becomes a **unit**", the content-cleared /
fraction-field notion of coprimality, matching the univariate
`AzPolynomial.coprime` (`coprime_int_iff`). -/

/-- The coefficient homomorphism `AzInt →+* ℚ` used for the fraction-field
statements: `ℤ`-cast composed with `toInt`. -/
def AzMvPolynomial.coeffToRat : AzInt →+* ℚ :=
  (Int.castRingHom ℚ).comp AzInt.toIntRingHom

private theorem AzMvPolynomial.coeffToRat_injective :
    Function.Injective AzMvPolynomial.coeffToRat := fun a b h =>
  Azurite.AzInt.ringEquivInt.injective (by
    have := Int.cast_injective (α := ℚ) (by simpa [AzMvPolynomial.coeffToRat] using h)
    simpa using this)

/-- A nonzero polynomial of total degree `0` over a domain maps, under an
injective coefficient hom into a field, to a unit; and conversely. -/
private theorem AzMvPolynomial.isUnit_map_coeffToRat_iff {n : ℕ}
    (p : MvPolynomial (Fin n) AzInt) :
    IsUnit (MvPolynomial.map AzMvPolynomial.coeffToRat p)
      ↔ p ≠ 0 ∧ p.totalDegree = 0 := by
  set φ := AzMvPolynomial.coeffToRat with hφ
  have hφinj := AzMvPolynomial.coeffToRat_injective
  constructor
  · intro hu
    have htd : (MvPolynomial.map φ p).totalDegree = 0 :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have hne : MvPolynomial.map φ p ≠ 0 := hu.ne_zero
    -- every nonzero-monomial coefficient of `p` vanishes
    have hcoeff : ∀ m, m ≠ 0 → p.coeff m = 0 := by
      intro m hm
      have h0 : (MvPolynomial.map φ p).coeff m = 0 := by
        rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd, MvPolynomial.coeff_C,
          if_neg (Ne.symm hm)]
      rw [MvPolynomial.coeff_map] at h0
      exact hφinj (by rw [h0, map_zero])
    refine ⟨?_, ?_⟩
    · intro hp0
      exact hne (by rw [hp0, map_zero])
    · rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C]
      ext m
      rw [MvPolynomial.coeff_C]
      split_ifs with hm
      · rw [hm]
      · exact hcoeff m (Ne.symm hm)
  · rintro ⟨hne, htd⟩
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd, MvPolynomial.map_C]
    have hc0 : p.coeff 0 ≠ 0 := by
      intro h
      exact hne (by rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd, h, map_zero])
    exact (isUnit_iff_ne_zero.mpr (fun h => hc0 (hφinj (by rw [h, map_zero])))).map
      MvPolynomial.C

/-- **`coprime` decides that the gcd is a unit over `ℚ[x⃗]`** — the
fraction-field (content-cleared) coprimality of the represented
polynomials: `gcd P Q` has no common factor of positive total degree,
equivalently it becomes a unit after base change of the coefficients to
`ℚ`. (The full "`IsRelPrime` over `ℚ[x⃗]`" form is equivalent but its
`coprime → IsRelPrime` direction is a multivariate Gauss statement; the
easy direction is `coprime_of_isRelPrime` below.) -/
theorem AzMvPolynomial.coprime_iff {n : ℕ}
    {P Q : AzMvPolynomial n AzInt ord} :
    AzMvPolynomial.coprime P Q = true
      ↔ IsUnit (MvPolynomial.map AzMvPolynomial.coeffToRat
          (AzMvPolynomial.gcd P Q).toMvPoly) := by
  rw [AzMvPolynomial.coprime, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    AzMvPolynomial.isUnit_map_coeffToRat_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h1 (toMvPoly_injective (by rw [h, toMvPoly_zero])),
      by rw [← totalDegree_toMvPoly]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (by rw [h, toMvPoly_zero]),
      by rw [totalDegree_toMvPoly]; exact h2⟩

/-- The image of `P` over `ℚ[x⃗]`. -/
noncomputable def AzMvPolynomial.ratImg {n : ℕ} (P : AzMvPolynomial n AzInt ord) :
    MvPolynomial (Fin n) ℚ :=
  MvPolynomial.map AzMvPolynomial.coeffToRat P.toMvPoly

/-- The gcd's `ℚ[x⃗]`-image divides each input's `ℚ[x⃗]`-image. -/
private theorem AzMvPolynomial.ratImg_gcd_dvd_left {n : ℕ}
    (P Q : AzMvPolynomial n AzInt ord) :
    MvPolynomial.map AzMvPolynomial.coeffToRat (AzMvPolynomial.gcd P Q).toMvPoly
      ∣ AzMvPolynomial.ratImg P :=
  map_dvd (MvPolynomial.map AzMvPolynomial.coeffToRat)
    (map_dvd AzMvPolynomial.toMvPolyHom (gcd_dvd_left P Q))

/-- The gcd's `ℚ[x⃗]`-image divides `Q`'s `ℚ[x⃗]`-image. -/
private theorem AzMvPolynomial.ratImg_gcd_dvd_right {n : ℕ}
    (P Q : AzMvPolynomial n AzInt ord) :
    MvPolynomial.map AzMvPolynomial.coeffToRat (AzMvPolynomial.gcd P Q).toMvPoly
      ∣ AzMvPolynomial.ratImg Q :=
  map_dvd (MvPolynomial.map AzMvPolynomial.coeffToRat)
    (map_dvd AzMvPolynomial.toMvPolyHom (gcd_dvd_right P Q))

/-- **The easy direction of the `IsRelPrime` characterization**: if the
`ℚ[x⃗]`-images of `P` and `Q` are relatively prime (every common divisor is
a unit), then `P` and `Q` are `coprime`. (The converse holds too but is a
multivariate Gauss statement.) -/
theorem AzMvPolynomial.coprime_of_isRelPrime {n : ℕ}
    {P Q : AzMvPolynomial n AzInt ord}
    (h : IsRelPrime (AzMvPolynomial.ratImg P) (AzMvPolynomial.ratImg Q)) :
    AzMvPolynomial.coprime P Q = true := by
  rw [AzMvPolynomial.coprime_iff]
  exact h (ratImg_gcd_dvd_left P Q) (ratImg_gcd_dvd_right P Q)

/-! ### Lifting a univariate polynomial preserves coprimality (Task 2) -/

/-- The single-variable embedding `ℚ[x] →+* ℚ[x⃗]` sending `x ↦ x_i`. -/
noncomputable def AzMvPolynomial.embVar {n : ℕ} (i : Fin n) :
    Polynomial ℚ →+* MvPolynomial (Fin n) ℚ :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X i)

/-- The `ℚ[x⃗]`-image of a lift is the `x_i`-embedding of the univariate
`ℚ[x]`-image: `ratImg (P.toAzMvPolynomial i) = embVar i (Pℚ)`. -/
theorem AzMvPolynomial.ratImg_toAzMvPolynomial {n : ℕ} (i : Fin n)
    (P : AzPolynomial AzInt) :
    AzMvPolynomial.ratImg (P.toAzMvPolynomial i ord)
      = AzMvPolynomial.embVar i
          ((AzPolynomial.toPoly P).map AzMvPolynomial.coeffToRat) := by
  rw [AzMvPolynomial.ratImg, toMvPoly_toAzMvPolynomial, AzMvPolynomial.embVar,
    Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  · ext a
    simp
  · simp

/-- The univariate `ℚ[x]`-image used by `AzPolynomial.coprime_int_iff`. -/
private theorem AzMvPolynomial.coeffToRat_eq :
    AzMvPolynomial.coeffToRat = (Int.castRingHom ℚ).comp AzInt.toIntRingHom := rfl

/-- **Lifting preserves coprimality — forward direction.** If `P, Q` are
coprime (over `ℚ[x]`), then their lifts into `AzMvPolynomial` via the
`i`-th variable are coprime. Gauss-free: `IsCoprime` pushes forward along
the `x_i`-embedding, and coprimality of the images implies `coprime`. -/
theorem AzMvPolynomial.coprime_toAzMvPolynomial_of {n : ℕ} (i : Fin n)
    (P Q : AzPolynomial AzInt) (h : AzPolynomial.coprime P Q = true) :
    AzMvPolynomial.coprime (P.toAzMvPolynomial i ord)
        (Q.toAzMvPolynomial i ord) = true := by
  have hc : IsCoprime
      ((AzPolynomial.toPoly P).map AzMvPolynomial.coeffToRat)
      ((AzPolynomial.toPoly Q).map AzMvPolynomial.coeffToRat) := by
    rw [AzMvPolynomial.coeffToRat_eq]
    exact (AzPolynomial.coprime_int_iff P Q).mp h
  have hcmv : IsCoprime
      (AzMvPolynomial.ratImg (P.toAzMvPolynomial i ord))
      (AzMvPolynomial.ratImg (Q.toAzMvPolynomial i ord)) := by
    rw [ratImg_toAzMvPolynomial, ratImg_toAzMvPolynomial]
    exact hc.map (AzMvPolynomial.embVar i)
  exact AzMvPolynomial.coprime_of_isRelPrime hcmv.isRelPrime

/-! ### Reverse direction and the full equality -/

/-- The lift of `0` is `0`. -/
private theorem AzPolynomial.toAzMvPolynomial_zero {n : ℕ} (i : Fin n) :
    (0 : AzPolynomial AzInt).toAzMvPolynomial i ord = 0 := by
  apply toMvPoly_injective
  rw [toMvPoly_toAzMvPolynomial, toMvPoly_zero, toPoly_zero, Polynomial.eval₂_zero]

/-- A nonzero polynomial has a nonempty coefficient array. -/
private theorem AzPolynomial.coeffs_size_pos {g : AzPolynomial AzInt}
    (hg : g ≠ 0) : 0 < g.coeffs.size := by
  rcases Nat.eq_zero_or_pos g.coeffs.size with h | h
  · exact absurd (AzPolynomial.ext (Array.eq_empty_of_size_eq_zero h)) hg
  · exact h

/-- The lift of `g` (via variable `i`) has total degree `natDegree g`. -/
private theorem AzMvPolynomial.lift_totalDegree {n : ℕ} (i : Fin n)
    {g : AzPolynomial AzInt} (hg : g ≠ 0) :
    (g.toAzMvPolynomial i ord).totalDegree = g.natDegree := by
  rw [Azurite.totalDegree_image i g (AzPolynomial.coeffs_size_pos hg)]
  rfl

/-- Lifting (via variable `i`) preserves divisibility. -/
private theorem AzMvPolynomial.lift_dvd {n : ℕ} (i : Fin n)
    {a b : AzPolynomial AzInt} (h : a ∣ b) :
    a.toAzMvPolynomial i ord ∣ b.toAzMvPolynomial i ord := by
  have hφ : toMvPoly (a.toAzMvPolynomial i ord) ∣ toMvPoly (b.toAzMvPolynomial i ord) := by
    rw [toMvPoly_toAzMvPolynomial, toMvPoly_toAzMvPolynomial]
    exact map_dvd (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X i))
      (map_dvd AzPolynomial.toPolyHom h)
  obtain ⟨c, hc⟩ := hφ
  exact ⟨AzMvPolynomial.ofMvPoly c, toMvPoly_injective (by
    rw [toMvPoly_mul, toMvPoly_ofMvPoly, hc])⟩

/-- Total degree is monotone under divisibility (nonzero divisor). -/
private theorem AzMvPolynomial.totalDegree_le_of_dvd {n : ℕ}
    {a b : AzMvPolynomial n AzInt ord} (h : a ∣ b) (hb : b ≠ 0) :
    a.totalDegree ≤ b.totalDegree := by
  rw [totalDegree_toMvPoly, totalDegree_toMvPoly]
  refine MvPolynomial.totalDegree_le_of_dvd_of_isDomain (map_dvd toMvPolyHom h) ?_
  exact fun h0 => hb (toMvPoly_injective (by rw [h0, toMvPoly_zero]))

/-- `gcd 0 0 = 0`. -/
theorem AzMvPolynomial.gcd_zero_zero {n : ℕ} :
    AzMvPolynomial.gcd (0 : AzMvPolynomial n AzInt ord) 0 = 0 := by
  rw [gcd_zero_right]
  apply toNested_injective (n := n)
  apply (towerBridge n).injective
  simp only [towerBridge_toNested_normalized, toNested_zero, map_zero]

/-- **Lifting a univariate polynomial into `AzMvPolynomial` (via variable
`x_i`) does not affect coprimality.** -/
theorem AzMvPolynomial.coprime_toAzMvPolynomial {n : ℕ} (i : Fin n)
    (P Q : AzPolynomial AzInt) :
    AzMvPolynomial.coprime (P.toAzMvPolynomial i ord)
        (Q.toAzMvPolynomial i ord) = AzPolynomial.coprime P Q := by
  refine Bool.coe_iff_coe.mp ⟨fun hmv => ?_,
    fun hu => coprime_toAzMvPolynomial_of i P Q hu⟩
  -- reverse: mv coprime of the lifts ⟹ univariate coprime
  rw [AzPolynomial.coprime_iff_gcd_isConstant]
  set g := AzPolynomial.gcd P Q with hgdef
  have hgdvd : (g.toAzMvPolynomial i ord)
      ∣ AzMvPolynomial.gcd (P.toAzMvPolynomial i ord) (Q.toAzMvPolynomial i ord) :=
    AzMvPolynomial.dvd_gcd (lift_dvd i (AzPolynomial.gcd_dvd_left_int P Q))
      (lift_dvd i (AzPolynomial.gcd_dvd_right_int P Q))
  rw [AzMvPolynomial.coprime, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hmv
  obtain ⟨hgl_ne, hgl_td⟩ := hmv
  have hg_ne : g ≠ 0 := by
    intro hg0
    obtain ⟨hP0, hQ0⟩ := AzPolynomial.gcd_eq_zero_iff_int.mp hg0
    apply hgl_ne
    rw [hP0, hQ0, AzPolynomial.toAzMvPolynomial_zero, gcd_zero_zero]
  refine ⟨hg_ne, ?_⟩
  have htd_le := AzMvPolynomial.totalDegree_le_of_dvd hgdvd hgl_ne
  rw [lift_totalDegree i hg_ne, hgl_td] at htd_le
  omega

/-! ### Gcd and gcd-free part -/

/-- **The canonical pair, computable-ring form**: the first component of
`gcdGcdFreePart` is the gcd, and the gcd-free part (second component) times
the gcd recovers `P` **as an `AzMvPolynomial n AzInt ord` identity**,
unconditionally — no base change required (mirror of the univariate
`gcdGcdFreePart_int_spec`). This is the strongest statement; the
`MvPolynomial (Fin n) ℤ`-image form follows as `gcdGcdFreePart_spec`. -/
theorem AzMvPolynomial.gcdGcdFreePart_spec' {n : ℕ}
    (P Q : AzMvPolynomial n AzInt ord) :
    (AzMvPolynomial.gcdGcdFreePart P Q).1 = AzMvPolynomial.gcd P Q
    ∧ (AzMvPolynomial.gcdGcdFreePart P Q).2 * AzMvPolynomial.gcd P Q = P := by
  have hpair : AzMvPolynomial.gcdGcdFreePart P Q
      = (AzMvPolynomial.gcd P Q,
         if AzMvPolynomial.gcd P Q = 0 then 0
         else Azurite.ExactDiv.exactDiv P (AzMvPolynomial.gcd P Q)) := rfl
  refine ⟨by rw [hpair], ?_⟩
  rw [hpair]
  by_cases hg : AzMvPolynomial.gcd P Q = 0
  · have hP0 : P = 0 := zero_dvd_iff.mp (hg ▸ gcd_dvd_left P Q)
    rw [if_pos hg, hg, hP0, mul_zero]
  · rw [if_neg hg]
    exact Azurite.ExactDiv.exactDiv_mul_self P _ (gcd_dvd_left P Q) hg

/-- **The canonical pair, image form**: `gcd(P,Q)-image · snd-image =
P-image` in `MvPolynomial (Fin n) ℤ`, unconditionally — an immediate
corollary of the computable-ring identity `gcdGcdFreePart_spec'`. -/
theorem AzMvPolynomial.gcdGcdFreePart_spec {n : ℕ}
    (P Q : AzMvPolynomial n AzInt ord) :
    (AzMvPolynomial.gcdGcdFreePart P Q).1 = AzMvPolynomial.gcd P Q
    ∧ MvPolynomial.map AzInt.toIntRingHom (AzMvPolynomial.gcd P Q).toMvPoly
        * MvPolynomial.map AzInt.toIntRingHom
            (AzMvPolynomial.gcdGcdFreePart P Q).2.toMvPoly
      = MvPolynomial.map AzInt.toIntRingHom P.toMvPoly := by
  obtain ⟨h1, hkey⟩ := AzMvPolynomial.gcdGcdFreePart_spec' P Q
  refine ⟨h1, ?_⟩
  have h2 := congrArg
    (fun z : AzMvPolynomial n AzInt ord =>
      MvPolynomial.map AzInt.toIntRingHom z.toMvPoly) hkey
  simp only [toMvPoly_mul, map_mul] at h2
  rw [← h2]
  ring

/-! ### Squarefreeness

`AzMvPolynomial.isSquarefree` decides that `squarefreeGradientGcd P` (the gcd
of `P` with its whole gradient) is a nonzero constant, i.e. becomes a unit
over `ℚ[x⃗]` — the fraction-field / characteristic-`0` notion, consistent
with `coprime`. Two correctness statements are shipped:

* `isSquarefree_iff` (structural, both directions);
* `isSquarefree_of_squarefree` (the Gauss-free intrinsic half:
  `Squarefree` of the `ℚ[x⃗]`-image implies `isSquarefree`).

The reverse intrinsic direction (`isSquarefree P → Squarefree Pℚ`) needs the
multivariate Gauss / content-descent that is deferred for `coprime`'s full
`IsRelPrime` iff, and is not attempted here. -/

section GeneralDerivative

open MvPolynomial Finsupp
open scoped Classical

variable {σ : Type*} {K : Type*} [Field K] [CharZero K]

/-- Characteristic-`0` gradient lemma: a multivariate polynomial all of whose
partial derivatives vanish has total degree `0` (is a constant). -/
theorem MvPolynomial.totalDegree_eq_zero_of_forall_pderiv_eq_zero
    (q : MvPolynomial σ K) (h : ∀ i, pderiv i q = 0) : q.totalDegree = 0 := by
  by_contra hne
  have hpos : 0 < q.totalDegree := Nat.pos_of_ne_zero hne
  have hsupp : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro he
    rw [MvPolynomial.totalDegree, he, Finset.sup_empty] at hpos; exact absurd hpos (by simp)
  obtain ⟨m, hm, hmeq⟩ := q.support.exists_mem_eq_sup hsupp (fun s => s.sum fun _ e => e)
  have hmpos : 0 < m.sum fun _ e => e := by rw [← hmeq]; exact hpos
  obtain ⟨i, hi0⟩ : ∃ i, 0 < m i := by
    by_contra hc; push Not at hc
    have hm0 : m = 0 := by ext j; exact Nat.le_zero.mp (hc j)
    rw [hm0, Finsupp.sum_zero_index] at hmpos; exact absurd hmpos (lt_irrefl 0)
  set d : σ →₀ ℕ := m - single i 1 with hd
  have hcoeff := coeff_pderiv (i := i) q d
  have hadd : d + single i 1 = m := by
    rw [hd, tsub_add_cancel_of_le]; rw [Finsupp.single_le_iff]; omega
  have hmiN : d i + 1 = m i := by rw [hd, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
  have hmi : (d i : K) + 1 = (m i : K) := by rw [← hmiN]; push_cast; ring
  rw [hadd, hmi, h i, coeff_zero] at hcoeff
  have hcm : coeff m q ≠ 0 := by rwa [← MvPolynomial.mem_support_iff]
  have hne0 : (m i : K) ≠ 0 := by exact_mod_cast (by omega : m i ≠ 0)
  exact (mul_ne_zero hcm hne0) hcoeff.symm

omit [CharZero K] in
/-- A nonzero partial derivative strictly lowers the total degree. -/
theorem MvPolynomial.totalDegree_pderiv_lt (q : MvPolynomial σ K) (i : σ)
    (hq : pderiv i q ≠ 0) : (pderiv i q).totalDegree < q.totalDegree := by
  have key : ∀ m ∈ (pderiv i q).support, (m.sum fun _ e => e) < q.totalDegree := by
    intro m hm
    have hcm : coeff m (pderiv i q) ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    rw [coeff_pderiv] at hcm
    have hmem : (m + single i 1) ∈ q.support :=
      MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hcm)
    have hle := le_totalDegree hmem
    have hsum : ((m + single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl]
    rw [hsum] at hle; omega
  have hne : (pderiv i q).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro he
    exact hq (by rwa [← MvPolynomial.support_eq_empty])
  have h0 : 0 < q.totalDegree := by
    obtain ⟨m, hm⟩ := hne; exact lt_of_le_of_lt (Nat.zero_le _) (key m hm)
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff h0]; exact key

/-- **Squarefree-gradient core** (characteristic `0`): if a prime `q` divides
a polynomial `p` and *all* its partial derivatives, then `q²` divides `p`. -/
theorem MvPolynomial.sq_dvd_of_prime_dvd_pderiv (p q : MvPolynomial σ K)
    (hq : Prime q) (hp : q ∣ p) (hpd : ∀ j, q ∣ pderiv j p) : q * q ∣ p := by
  obtain ⟨s, rfl⟩ := hp
  suffices hs : q ∣ s by obtain ⟨t, rfl⟩ := hs; exact ⟨t, by ring⟩
  by_contra hns
  have hqd : ∀ j, q ∣ pderiv j q := by
    intro j
    have hh := hpd j
    rw [pderiv_mul, add_comm] at hh
    have h2 : q ∣ pderiv j q * s :=
      (dvd_add_right (dvd_mul_right q (pderiv j s))).mp hh
    exact (hq.dvd_or_dvd h2).resolve_right hns
  have htd : q.totalDegree = 0 :=
    MvPolynomial.totalDegree_eq_zero_of_forall_pderiv_eq_zero q (fun j => by
      by_contra hnz
      exact absurd (MvPolynomial.totalDegree_le_of_dvd_of_isDomain (hqd j) hnz)
        (by have := MvPolynomial.totalDegree_pderiv_lt q j hnz; omega))
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at htd
  have hc0 : coeff 0 q ≠ 0 := fun h => hq.ne_zero (by rw [htd, h, map_zero])
  exact hq.not_unit (htd ▸ ((isUnit_iff_ne_zero.mpr hc0).map MvPolynomial.C))

end GeneralDerivative

/-! ### Squarefreeness of `AzMvPolynomial` over `AzInt` -/

/-- **`isSquarefree` decides that the gradient gcd is a unit over `ℚ[x⃗]`** —
the fraction-field / characteristic-`0` squarefreeness. -/
theorem AzMvPolynomial.isSquarefree_iff {n : ℕ}
    {P : AzMvPolynomial n AzInt ord} :
    AzMvPolynomial.isSquarefree P = true
      ↔ IsUnit (MvPolynomial.map AzMvPolynomial.coeffToRat
          (AzMvPolynomial.squarefreeGradientGcd P).toMvPoly) := by
  rw [AzMvPolynomial.isSquarefree, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    AzMvPolynomial.isUnit_map_coeffToRat_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (toMvPoly_injective (by rw [h, toMvPoly_zero])),
      by rw [← totalDegree_toMvPoly]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (by rw [h, toMvPoly_zero]),
      by rw [totalDegree_toMvPoly]; exact h2⟩

/-- A `gcd`-fold divides its initial value. -/
private theorem AzMvPolynomial.foldl_gcd_dvd_init {n : ℕ}
    (l : List (Fin n)) (init : AzMvPolynomial n AzInt ord)
    (f : Fin n → AzMvPolynomial n AzInt ord) :
    l.foldl (fun acc j => AzMvPolynomial.gcd acc (f j)) init ∣ init := by
  induction l generalizing init with
  | nil => exact dvd_refl _
  | cons a t ih => exact (ih _).trans (gcd_dvd_left _ _)

/-- A `gcd`-fold divides `f j` for each `j` in the list. -/
private theorem AzMvPolynomial.foldl_gcd_dvd_mem {n : ℕ}
    (l : List (Fin n)) (init : AzMvPolynomial n AzInt ord)
    (f : Fin n → AzMvPolynomial n AzInt ord) {j : Fin n} (hj : j ∈ l) :
    l.foldl (fun acc k => AzMvPolynomial.gcd acc (f k)) init ∣ f j := by
  induction l generalizing init with
  | nil => exact absurd hj List.not_mem_nil
  | cons a t ih =>
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact (foldl_gcd_dvd_init t _ f).trans (gcd_dvd_right _ _)
    · exact ih _ hj'

/-- The gradient gcd divides `P`. -/
theorem AzMvPolynomial.squarefreeGradientGcd_dvd_self {n : ℕ}
    (P : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial.squarefreeGradientGcd P ∣ P :=
  foldl_gcd_dvd_init _ P _

/-- The gradient gcd divides each partial derivative `∂P/∂x_j`. -/
theorem AzMvPolynomial.squarefreeGradientGcd_dvd_pderiv {n : ℕ}
    (P : AzMvPolynomial n AzInt ord) (j : Fin n) :
    AzMvPolynomial.squarefreeGradientGcd P ∣ AzMvPolynomial.pderivGeneral j P :=
  foldl_gcd_dvd_mem _ P _ (List.mem_finRange j)

/-- The `ℚ[x⃗]`-image commutes with the partial derivative. -/
theorem AzMvPolynomial.ratImg_pderivGeneral {n : ℕ}
    (P : AzMvPolynomial n AzInt ord) (j : Fin n) :
    AzMvPolynomial.ratImg (AzMvPolynomial.pderivGeneral j P)
      = MvPolynomial.pderiv j (AzMvPolynomial.ratImg P) := by
  rw [AzMvPolynomial.ratImg, AzMvPolynomial.ratImg, toMvPoly_pderivGeneral,
    MvPolynomial.pderiv_map]

/-- **The Gauss-free intrinsic half of squarefreeness correctness.** If the
`ℚ[x⃗]`-image of `P` is `Squarefree`, then `P` passes the `isSquarefree`
test. -/
theorem AzMvPolynomial.isSquarefree_of_squarefree {n : ℕ}
    {P : AzMvPolynomial n AzInt ord}
    (h : Squarefree (MvPolynomial.map AzMvPolynomial.coeffToRat P.toMvPoly)) :
    AzMvPolynomial.isSquarefree P = true := by
  set g := AzMvPolynomial.squarefreeGradientGcd P with hg
  have hPsf : Squarefree (AzMvPolynomial.ratImg P) := h
  have hP0 : AzMvPolynomial.ratImg P ≠ 0 := by
    intro h0
    exact not_isUnit_zero (hPsf 0 (by rw [h0]; simp))
  have hgdvdP : AzMvPolynomial.ratImg g ∣ AzMvPolynomial.ratImg P :=
    map_dvd (MvPolynomial.map AzMvPolynomial.coeffToRat)
      (map_dvd toMvPolyHom (squarefreeGradientGcd_dvd_self P))
  have hgdvdD : ∀ j, AzMvPolynomial.ratImg g
      ∣ MvPolynomial.pderiv j (AzMvPolynomial.ratImg P) := by
    intro j
    rw [← ratImg_pderivGeneral]
    exact map_dvd (MvPolynomial.map AzMvPolynomial.coeffToRat)
      (map_dvd toMvPolyHom (squarefreeGradientGcd_dvd_pderiv P j))
  have hgU : IsUnit (AzMvPolynomial.ratImg g) := by
    by_contra hnu
    have hg0 : AzMvPolynomial.ratImg g ≠ 0 :=
      fun h0 => hP0 (zero_dvd_iff.mp (h0 ▸ hgdvdP))
    obtain ⟨q, hqirr, hqdvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hg0
    have hqp : Prime q := hqirr.prime
    have hsq : q * q ∣ AzMvPolynomial.ratImg P :=
      MvPolynomial.sq_dvd_of_prime_dvd_pderiv (AzMvPolynomial.ratImg P) q hqp
        (hqdvd.trans hgdvdP) (fun j => (hqdvd.trans (hgdvdD j)))
    exact hqp.not_unit (hPsf q hsq)
  rw [AzMvPolynomial.isSquarefree_iff]
  exact hgU

end Azurite
