import Azurite.AzPolynomial.GcdTower
import Azurite.AzPolynomial.Equiv.Gcd
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Correctness of `ngcdPoly`: one tower level, UFD-generic

**`map_toPoly_ngcdPoly`** — under the *bridge package* below, for all
`P, Q : AzPolynomial D`,

  `(toPoly (ngcdPoly P Q)).map ρ = gcd ((toPoly P).map ρ) ((toPoly Q).map ρ)`

with Mathlib's `NormalizedGCDMonoid` gcd in `M[X]`.

## The bridge package

* `D` — the computable coefficient type:
  `[CommRing D] [DecidableEq D] [Azurite.ExactDiv D] [IsDomain D]
   [NormalizedGcd D]`;
* `M` — the mathematical model:
  `[CommRing M] [IsDomain M] [NormalizedGCDMonoid M]`;
* `ρ : D →+* M` with
  - `hρ : Function.Injective ρ`,
  - `hrefl : ∀ a b, ρ a ∣ ρ b → a ∣ b` (divisibility reflects — for the
    tower `ρ` is a ring isomorphism onto `M`, so this is automatic),
  - `hgcd : ∀ a b, ρ (NormalizedGcd.ngcd a b) = gcd (ρ a) (ρ b)` (the
    coefficient-level `ngcd` represents Mathlib's normalized gcd).

Everything else in the Phase-1 contract is **derived** from `hgcd`:
`ρ (norm a) = normalize (ρ a)` (`map_norm`), `norm a ∣ a` (`norm_dvd`), and
the unit-part identity `ρ (unitPart a) · normUnit (ρ a) = 1`
(`map_unitPart_mul_normUnit`), which is what makes `leadNormalize` compute
`normalize` and `primNormalized` produce the primitive part with normalized
leading coefficient.

## Proof architecture

Generalization of `Equiv/GcdInt.lean` (the `D = AzInt`, `M = ℤ` case),
branch-for-branch — Phase 1 kept `ngcdPoly` branch-identical to
`gcdNormalizedInt` for exactly this purpose. The normalized `M[X]` gcd is
characterized (`gcd_char`) as `C d · G` with `d = gcd(cont A, cont B)` and
`G` primitive with normalized leading coefficient whose `Frac(M)[X]` image
is associated to the fraction-field gcd (divisibility both ways splits into
the content part and the primitive part, Gauss descent via
`IsPrimitive.dvd_of_fraction_map_dvd_fraction_map`). Each branch of
`ngcdPoly` produces such a pair: `d` from `contentGcdGen`
(`map_contentGen`), `G` from `primNormalized` of the subresultant core
(`primNormalized_spec`), whose association to the fraction-field gcd is the
`D`-level Algorithm 8.21 bridge (`signedSubresultant_toPoly_domain`)
transported along `Frac(M) ∘ ρ` by `sResP_map` (`subresGcd_frac_assoc`);
the `p = q` pre-step is invisible over `Frac(M)` (`gcd_pre_step`).

The fraction field is `FractionRing M`; its `DecidableEq` (required by the
`CommGroupWithZero → NormalizedGCDMonoid` instance underlying the ambient
`NormalizedGCDMonoid (Frac(M))[X]`) is a local `Classical.decEq` — it never
appears in an exported statement, since `map_toPoly_ngcdPoly` mentions only
`D` and `M`.
-/

set_option linter.unusedSectionVars false

namespace Azurite.AzPolynomial

open Polynomial

/- Chapter 1 (imported through the Chapter 8 subresultant theory) installs
the `EuclideanDomain`-derived `GCDMonoid K[X]` instance
`Azurite.BPR.gcdMonoidPolynomial`, which would win over Mathlib's
`NormalizedGCDMonoid`-derived gcd on the fraction-field side. This file's
statements are about **Mathlib's** gcd, so we locally prefer it; the
Chapter 8 gcd facts are transported across the (associated) instances once,
in `subresGcd_frac_assoc`. -/
attribute [local instance 0] Azurite.BPR.gcdMonoidPolynomial

section TowerBridge

variable {D M : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
  [IsDomain D] [NormalizedGcd D] [CommRing M] [IsDomain M]
  [NormalizedGCDMonoid M] {ρ : D →+* M}

/-- `DecidableEq` on the fraction field, needed only so that the ambient
`NormalizedGCDMonoid (FractionRing M)` (the `CommGroupWithZero` instance)
and hence `NormalizedGCDMonoid (FractionRing M)[X]` resolve. Local — no
exported statement mentions the fraction field. -/
private noncomputable local instance : DecidableEq (FractionRing M) :=
  Classical.decEq _

/-! ### Basic image bridges -/

private theorem map_toPoly_ne_zero' (hρ : Function.Injective ρ)
    {T : AzPolynomial D} (hT : T ≠ 0) : (AzPolynomial.toPoly T).map ρ ≠ 0 := by
  rw [Ne, Polynomial.map_eq_zero_iff hρ]
  exact toPoly_ne_zero hT

private theorem natDegree_map_toPoly' (hρ : Function.Injective ρ)
    (T : AzPolynomial D) :
    ((AzPolynomial.toPoly T).map ρ).natDegree = T.natDegree := by
  rw [Polynomial.natDegree_map_eq_of_injective hρ, AzPolynomial.natDegree_toPoly]

private theorem leadingCoeff_map_toPoly' (hρ : Function.Injective ρ)
    (p : AzPolynomial D) :
    ((AzPolynomial.toPoly p).map ρ).leadingCoeff = ρ p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_map_eq_of_injective hρ,
    Polynomial.coeff_map, ← Polynomial.leadingCoeff, leadingCoeff_toPoly]

private theorem coeff_map_toPoly' (p : AzPolynomial D) (i : ℕ) :
    ((AzPolynomial.toPoly p).map ρ).coeff i = ρ (p.coeff i) := by
  rw [Polynomial.coeff_map, coeff_toPoly_eq]

private theorem leadingCoeff_ne_zero' {p : AzPolynomial D} (hp : p ≠ 0) :
    p.leadingCoeff ≠ 0 := by
  intro h
  have h1 := leadingCoeff_toPoly p
  rw [h] at h1
  exact Polynomial.leadingCoeff_ne_zero.mpr (toPoly_ne_zero hp) h1

/-! ### Derived `NormalizedGcd` laws

Everything below is derived from the single package hypothesis `hgcd`. -/

/-- `norm` represents Mathlib's `normalize`. -/
theorem map_norm
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    (a : D) : ρ (NormalizedGcd.norm a) = _root_.normalize (ρ a) := by
  rw [NormalizedGcd.norm, hgcd, map_zero, gcd_zero_right]

/-- The normalization divides the element (in `D`). -/
theorem norm_dvd (hrefl : ∀ a b : D, ρ a ∣ ρ b → a ∣ b)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    (a : D) : NormalizedGcd.norm a ∣ a :=
  hrefl _ _ (by rw [map_norm hgcd]; exact (normalize_associated (ρ a)).dvd)

theorem norm_ne_zero (hρ : Function.Injective ρ)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    {a : D} (ha : a ≠ 0) : NormalizedGcd.norm a ≠ 0 := by
  intro h
  have h1 := map_norm hgcd a
  rw [h, map_zero] at h1
  exact ha (hρ (by rw [map_zero, normalize_eq_zero.mp h1.symm]))

/-- The unit-part identity in `D`: `unitPart a · norm a = a`. -/
theorem unitPart_mul_norm (hρ : Function.Injective ρ)
    (hrefl : ∀ a b : D, ρ a ∣ ρ b → a ∣ b)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    {a : D} (ha : a ≠ 0) :
    NormalizedGcd.unitPart a * NormalizedGcd.norm a = a := by
  rw [NormalizedGcd.unitPart]
  exact Azurite.ExactDiv.exactDiv_mul_self a _ (norm_dvd hrefl hgcd a)
    (norm_ne_zero hρ hgcd ha)

/-- The unit-part identity in `M`: `ρ (unitPart a) · normUnit (ρ a) = 1`. -/
theorem map_unitPart_mul_normUnit (hρ : Function.Injective ρ)
    (hrefl : ∀ a b : D, ρ a ∣ ρ b → a ∣ b)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    {a : D} (ha : a ≠ 0) :
    ρ (NormalizedGcd.unitPart a) * (normUnit (ρ a) : M) = 1 := by
  have hρa : ρ a ≠ 0 := fun h => ha (hρ (by rw [h, map_zero]))
  have h1 := congrArg ρ (unitPart_mul_norm hρ hrefl hgcd ha)
  rw [map_mul, map_norm hgcd, normalize_apply] at h1
  apply mul_left_cancel₀ hρa
  rw [mul_one]
  calc ρ a * (ρ (NormalizedGcd.unitPart a) * (normUnit (ρ a) : M))
      = ρ (NormalizedGcd.unitPart a) * (ρ a * (normUnit (ρ a) : M)) := by ring
    _ = ρ a := h1

theorem isUnit_map_unitPart (hρ : Function.Injective ρ)
    (hrefl : ∀ a b : D, ρ a ∣ ρ b → a ∣ b)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    {a : D} (ha : a ≠ 0) : IsUnit (ρ (NormalizedGcd.unitPart a)) :=
  IsUnit.of_mul_eq_one _ (map_unitPart_mul_normUnit hρ hrefl hgcd ha)

theorem unitPart_ne_zero (hρ : Function.Injective ρ)
    (hrefl : ∀ a b : D, ρ a ∣ ρ b → a ∣ b)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    {a : D} (ha : a ≠ 0) : NormalizedGcd.unitPart a ≠ 0 := by
  intro h
  have h1 := isUnit_map_unitPart hρ hrefl hgcd ha
  rw [h, map_zero] at h1
  exact not_isUnit_zero h1

/-! ### `contentGen` represents `Polynomial.content` -/

private theorem foldl_gcd_dvd_init (l : List M) (init : M) :
    l.foldl (fun acc a => GCDMonoid.gcd acc a) init ∣ init := by
  induction l generalizing init with
  | nil => exact dvd_refl _
  | cons a l ih => exact (ih _).trans (gcd_dvd_left _ _)

private theorem foldl_gcd_dvd_mem (l : List M) (init : M) {x : M} (hx : x ∈ l) :
    l.foldl (fun acc a => GCDMonoid.gcd acc a) init ∣ x := by
  induction l generalizing init with
  | nil => exact absurd hx List.not_mem_nil
  | cons b l ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact (foldl_gcd_dvd_init l _).trans (gcd_dvd_right _ _)
    · exact ih _ hx'

private theorem dvd_foldl_gcd (l : List M) (init : M) {c : M} (hi : c ∣ init)
    (h : ∀ x ∈ l, c ∣ x) :
    c ∣ l.foldl (fun acc a => GCDMonoid.gcd acc a) init := by
  induction l generalizing init with
  | nil => exact hi
  | cons a l ih =>
    exact ih _ (dvd_gcd hi (h a List.mem_cons_self))
      (fun b hb => h b (List.mem_cons_of_mem _ hb))

private theorem normalize_foldl_gcd (l : List M) (init : M)
    (h : _root_.normalize init = init) :
    _root_.normalize (l.foldl (fun acc a => GCDMonoid.gcd acc a) init)
      = l.foldl (fun acc a => GCDMonoid.gcd acc a) init := by
  induction l generalizing init with
  | nil => exact h
  | cons a l ih => exact ih _ (normalize_gcd _ _)

private theorem map_foldl_ngcd
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    (l : List D) (acc : D) :
    ρ (l.foldl (fun acc a => NormalizedGcd.ngcd acc a) acc)
      = (l.map ρ).foldl (fun acc a => GCDMonoid.gcd acc a) (ρ acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, hgcd]

private theorem coeff_eq_toList_getElem (p : AzPolynomial D) {i : ℕ}
    (hi : i < p.coeffs.size) :
    p.coeff i = p.coeffs.toList[i]'(by simpa using hi) := by
  rw [AzPolynomial.coeff, Array.getElem?_eq_getElem hi]
  simp

private theorem coeff_eq_zero_of_ge (p : AzPolynomial D) {i : ℕ}
    (hi : p.coeffs.size ≤ i) : p.coeff i = 0 := by
  rw [AzPolynomial.coeff, Array.getElem?_eq_none (by omega)]
  rfl

/-- **`contentGen` represents Mathlib's content** — the generalization of
`content_toPoly` to the tower: the `ngcd`-fold over the coefficients maps to
`Polynomial.content` of the represented polynomial. Both sides are
normalized gcds of the coefficient list, so they agree by `dvd`-antisymmetry
of normalized elements. -/
theorem map_contentGen
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    (p : AzPolynomial D) :
    ρ (contentGen p) = ((AzPolynomial.toPoly p).map ρ).content := by
  set Q : M[X] := (AzPolynomial.toPoly p).map ρ with hQ
  have hQcoeff : ∀ i, Q.coeff i = ρ (p.coeff i) := fun i => by
    rw [hQ, coeff_map_toPoly']
  have hfold : ρ (contentGen p)
      = (p.coeffs.toList.map ρ).foldl (fun acc a => GCDMonoid.gcd acc a) 0 := by
    rw [contentGen, ← Array.foldl_toList, map_foldl_ngcd hgcd, map_zero]
  rw [hfold]
  apply dvd_antisymm_of_normalize_eq (normalize_foldl_gcd _ _ normalize_zero)
    Q.normalize_content
  · -- the fold divides the content
    rw [Polynomial.content]
    apply Finset.dvd_gcd
    intro i hi
    have hne : Q.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hlt : i < p.coeffs.size := by
      by_contra hge
      exact hne (by rw [hQcoeff, coeff_eq_zero_of_ge p (by omega), map_zero])
    have hx : Q.coeff i = ρ (p.coeffs.toList[i]'(by simpa using hlt)) := by
      rw [hQcoeff, coeff_eq_toList_getElem p hlt]
    rw [hx]
    exact foldl_gcd_dvd_mem _ _
      (List.mem_map.mpr ⟨_, List.getElem_mem (by simpa using hlt), rfl⟩)
  · -- the content divides the fold
    apply dvd_foldl_gcd _ _ (dvd_zero _)
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    have hx2 : ρ (p.coeffs.toList[i]'hi) = Q.coeff i := by
      rw [hQcoeff, coeff_eq_toList_getElem p (by simpa using hi)]
    rw [hx2]
    exact Q.content_dvd_coeff i

theorem contentGen_ne_zero (hρ : Function.Injective ρ)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    {g : AzPolynomial D} (hg : g ≠ 0) : contentGen g ≠ 0 := by
  intro h
  have h1 := map_contentGen hgcd g
  rw [h, map_zero] at h1
  have h2 : ((AzPolynomial.toPoly g).map ρ).content ≠ 0 := by
    rw [Ne, Polynomial.content_eq_zero_iff]
    exact map_toPoly_ne_zero' hρ hg
  exact h2 h1.symm

/-- `contentGcdGen` represents the `M`-gcd of the contents. -/
theorem map_contentGcdGen
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    (P Q : AzPolynomial D) :
    ρ (contentGcdGen P Q)
      = GCDMonoid.gcd ((AzPolynomial.toPoly P).map ρ).content
          ((AzPolynomial.toPoly Q).map ρ).content := by
  rw [contentGcdGen, hgcd, map_contentGen hgcd, map_contentGen hgcd]

/-- **Content is multiplicative** (Gauss, one tower level): `contentGen`
respects products. Proved by transporting to `M` (a `NormalizedGCDMonoid`)
along the injective bridge `ρ` and using Mathlib's `Polynomial.content_mul`. -/
theorem contentGen_mul (hρ : Function.Injective ρ)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    (p q : AzPolynomial D) :
    contentGen (p * q) = contentGen p * contentGen q := by
  apply hρ
  rw [map_mul, map_contentGen hgcd, map_contentGen hgcd, map_contentGen hgcd,
    Azurite.AzPolynomial.toPoly_mul, Polynomial.map_mul, Polynomial.content_mul]

private theorem normalize_mul' (a b : M) :
    _root_.normalize (a * b) = _root_.normalize a * _root_.normalize b :=
  map_mul _root_.normalize a b

/-! ### `leadNormalize` represents `normalize` -/

theorem leadNormalize_zero : leadNormalize (0 : AzPolynomial D) = 0 := by
  rw [leadNormalize, if_pos rfl]

/-- **`leadNormalize` represents Mathlib's `normalize`** (the generalization
of `map_toPoly_signNorm`): dividing out the unit part of the leading
coefficient computes the normalized associate. -/
theorem map_toPoly_leadNormalize (hρ : Function.Injective ρ)
    (hrefl : ∀ a b : D, ρ a ∣ ρ b → a ∣ b)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    {p : AzPolynomial D} (hp : p ≠ 0) :
    (AzPolynomial.toPoly (leadNormalize p)).map ρ
      = _root_.normalize ((AzPolynomial.toPoly p).map ρ) := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero' hp
  have huu : IsUnit (ρ (NormalizedGcd.unitPart p.leadingCoeff)) :=
    isUnit_map_unitPart hρ hrefl hgcd hlc
  have hu0 : NormalizedGcd.unitPart p.leadingCoeff ≠ 0 :=
    unitPart_ne_zero hρ hrefl hgcd hlc
  have hudvd : ∀ i, NormalizedGcd.unitPart p.leadingCoeff ∣ p.coeff i :=
    fun i => hrefl _ _ (huu.dvd)
  have hkey : Polynomial.C (NormalizedGcd.unitPart p.leadingCoeff)
      * AzPolynomial.toPoly (leadNormalize p) = AzPolynomial.toPoly p := by
    rw [leadNormalize, if_neg hp]
    exact C_mul_toPoly_divByRingElt _ hu0 p hudvd
  have hkeyM : Polynomial.C (ρ (NormalizedGcd.unitPart p.leadingCoeff))
      * ((AzPolynomial.toPoly (leadNormalize p)).map ρ)
      = (AzPolynomial.toPoly p).map ρ := by
    have h := congrArg (Polynomial.map ρ) hkey
    rwa [Polynomial.map_mul, Polynomial.map_C] at h
  have hnu := map_unitPart_mul_normUnit hρ hrefl hgcd hlc
  calc (AzPolynomial.toPoly (leadNormalize p)).map ρ
      = ((AzPolynomial.toPoly (leadNormalize p)).map ρ)
          * Polynomial.C (ρ (NormalizedGcd.unitPart p.leadingCoeff)
              * (normUnit (ρ p.leadingCoeff) : M)) := by
        rw [hnu, Polynomial.C_1, mul_one]
    _ = (Polynomial.C (ρ (NormalizedGcd.unitPart p.leadingCoeff))
          * ((AzPolynomial.toPoly (leadNormalize p)).map ρ))
          * Polynomial.C ((normUnit (ρ p.leadingCoeff) : M)) := by
        rw [Polynomial.C_mul]; ring
    _ = ((AzPolynomial.toPoly p).map ρ)
          * Polynomial.C ((normUnit (ρ p.leadingCoeff) : M)) := by rw [hkeyM]
    _ = _root_.normalize ((AzPolynomial.toPoly p).map ρ) := by
        rw [normalize_apply, Polynomial.coe_normUnit, leadingCoeff_map_toPoly' hρ]

/-! ### The `primNormalized` specification -/

/-- **The `primNormalized` specification** (generalization of
`primPos_spec`): a nonzero constant multiple relation with the input,
primitivity of the image, and normalized leading coefficient. -/
theorem primNormalized_spec (hρ : Function.Injective ρ)
    (hrefl : ∀ a b : D, ρ a ∣ ρ b → a ∣ b)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    {g : AzPolynomial D} (hg : g ≠ 0) :
    ∃ c : M, c ≠ 0
      ∧ Polynomial.C c * ((AzPolynomial.toPoly (primNormalized g)).map ρ)
          = (AzPolynomial.toPoly g).map ρ
      ∧ ((AzPolynomial.toPoly (primNormalized g)).map ρ).IsPrimitive
      ∧ _root_.normalize
            ((AzPolynomial.toPoly (primNormalized g)).map ρ).leadingCoeff
          = ((AzPolynomial.toPoly (primNormalized g)).map ρ).leadingCoeff := by
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero' hg
  set s : D := contentGen g * NormalizedGcd.unitPart g.leadingCoeff with hs
  set gM : M[X] := (AzPolynomial.toPoly g).map ρ with hgM
  have hgM0 : gM ≠ 0 := map_toPoly_ne_zero' hρ hg
  have hcont0 : gM.content ≠ 0 := by
    rw [Ne, Polynomial.content_eq_zero_iff]
    exact hgM0
  have hcg0 : contentGen g ≠ 0 := contentGen_ne_zero hρ hgcd hg
  have huu : IsUnit (ρ (NormalizedGcd.unitPart g.leadingCoeff)) :=
    isUnit_map_unitPart hρ hrefl hgcd hlc
  have hu0 : NormalizedGcd.unitPart g.leadingCoeff ≠ 0 :=
    unitPart_ne_zero hρ hrefl hgcd hlc
  have hs0 : s ≠ 0 := mul_ne_zero hcg0 hu0
  have hρs : ρ s = gM.content * ρ (NormalizedGcd.unitPart g.leadingCoeff) := by
    rw [hs, map_mul, map_contentGen hgcd, hgM]
  -- `s` divides every coefficient in `D`
  have hdvd : ∀ i, s ∣ g.coeff i := by
    intro i
    apply hrefl
    rw [hρs, huu.mul_right_dvd]
    have h1 : gM.coeff i = ρ (g.coeff i) := by rw [hgM, coeff_map_toPoly']
    rw [← h1]
    exact gM.content_dvd_coeff i
  -- the exact-division identity, mapped to `M[X]`
  have hkey : Polynomial.C s * AzPolynomial.toPoly (primNormalized g)
      = AzPolynomial.toPoly g := by
    rw [primNormalized, if_neg hg]
    exact C_mul_toPoly_divByRingElt s hs0 g hdvd
  have hkeyM : Polynomial.C (ρ s)
      * ((AzPolynomial.toPoly (primNormalized g)).map ρ) = gM := by
    have h := congrArg (Polynomial.map ρ) hkey
    rwa [Polynomial.map_mul, Polynomial.map_C, ← hgM] at h
  have hρs0 : ρ s ≠ 0 := fun h => hs0 (hρ (by rw [h, map_zero]))
  refine ⟨ρ s, hρs0, hkeyM, ?_, ?_⟩
  · -- primitivity: `content gM · content(prim-img) = content gM`
    have h1 := congrArg Polynomial.content hkeyM
    rw [Polynomial.content_C_mul] at h1
    have h2 : _root_.normalize (ρ s) = gM.content := by
      rw [hρs, normalize_mul' _ _, gM.normalize_content,
        normalize_eq_one.mpr huu, mul_one]
    rw [h2] at h1
    rw [Polynomial.isPrimitive_iff_content_eq_one]
    exact mul_left_cancel₀ hcont0 (by rw [h1, mul_one])
  · -- normalized leading coefficient
    rw [leadingCoeff_map_toPoly' hρ]
    have hlcM := congrArg Polynomial.leadingCoeff hkeyM
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hgM,
      leadingCoeff_map_toPoly' hρ, leadingCoeff_map_toPoly' hρ] at hlcM
    -- hlcM : ρ s * ρ (primNormalized g).leadingCoeff = ρ g.leadingCoeff
    have hnu := map_unitPart_mul_normUnit hρ hrefl hgcd hlc
    have h3 : _root_.normalize (ρ g.leadingCoeff)
        = gM.content * ρ (primNormalized g).leadingCoeff := by
      calc _root_.normalize (ρ g.leadingCoeff)
          = ρ g.leadingCoeff * (normUnit (ρ g.leadingCoeff) : M) :=
            normalize_apply _
        _ = (ρ s * ρ (primNormalized g).leadingCoeff)
              * (normUnit (ρ g.leadingCoeff) : M) := by rw [hlcM]
        _ = gM.content * ρ (primNormalized g).leadingCoeff
              * (ρ (NormalizedGcd.unitPart g.leadingCoeff)
                  * (normUnit (ρ g.leadingCoeff) : M)) := by
            rw [hρs]; ring
        _ = gM.content * ρ (primNormalized g).leadingCoeff := by
            rw [hnu, mul_one]
    have h4 := congrArg _root_.normalize h3
    rw [normalize_idem, h3, normalize_mul' _ _, gM.normalize_content] at h4
    exact (mul_left_cancel₀ hcont0 h4).symm

/-! ### The `M[X]` gcd characterization -/

private theorem normalize_eq_self_of_normalized_lcof {p : M[X]}
    (hp : _root_.normalize p.leadingCoeff = p.leadingCoeff) :
    _root_.normalize p = p := by
  by_cases hp0 : p = 0
  · rw [hp0, normalize_zero]
  have hlc0 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have h1 : (normUnit p.leadingCoeff : M) = 1 := by
    have h2 := hp
    rw [normalize_apply] at h2
    exact mul_left_cancel₀ hlc0 (h2.trans (mul_one p.leadingCoeff).symm)
  rw [normalize_apply, Polynomial.coe_normUnit, h1, Polynomial.C_1, mul_one]

private theorem content_dvd_of_dvd {e A : M[X]} (h : e ∣ A) :
    e.content ∣ A.content := by
  obtain ⟨f, rfl⟩ := h
  rw [Polynomial.content_mul]
  exact Dvd.intro _ rfl

/-- `Frac(M)[X]` image of a polynomial is associated to that of its
primitive part. -/
private theorem map_assoc_primPart {T : M[X]} (hT : T ≠ 0) :
    Associated (T.map (algebraMap M (FractionRing M)))
      ((T.primPart).map (algebraMap M (FractionRing M))) := by
  have hcT : T.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
  have hinj : Function.Injective (algebraMap M (FractionRing M)) :=
    IsFractionRing.injective M (FractionRing M)
  have hu : IsUnit (Polynomial.C (algebraMap M (FractionRing M) T.content)
      : (FractionRing M)[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (fun h => hcT (hinj (by rw [h, map_zero]))))
  have h1 : T.map (algebraMap M (FractionRing M))
      = Polynomial.C (algebraMap M (FractionRing M) T.content)
        * (T.primPart).map (algebraMap M (FractionRing M)) := by
    conv_lhs => rw [T.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
  rw [h1]
  exact Associated.symm ⟨hu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩

/-- **Characterization of the normalized `M[X]` gcd** (generalization of
`int_gcd_eq`, with "positive leading coefficient" replaced by "normalized
leading coefficient"): if `d = gcd(cont A, cont B)` and `G` is primitive
with normalized leading coefficient whose `Frac(M)[X]` image is associated
to the fraction-field gcd, then `C d · G` is the normalized gcd of `A` and
`B`. -/
private theorem gcd_char {A B G : M[X]} {d : M} (hA : A ≠ 0) (hB : B ≠ 0)
    (hd : d = GCDMonoid.gcd A.content B.content)
    (hGprim : G.IsPrimitive)
    (hGlc : _root_.normalize G.leadingCoeff = G.leadingCoeff)
    (hGq : Associated (G.map (algebraMap M (FractionRing M)))
      (GCDMonoid.gcd (A.map (algebraMap M (FractionRing M)))
        (B.map (algebraMap M (FractionRing M))))) :
    Polynomial.C d * G = GCDMonoid.gcd A B := by
  have hcontA : A.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
  have hdnorm : _root_.normalize d = d := by rw [hd]; exact normalize_gcd _ _
  -- (i)/(ii): `C d · G` divides both `A` and `B`
  have hGdvdA : G ∣ A.primPart := by
    refine hGprim.dvd_of_fraction_map_dvd_fraction_map (K := FractionRing M)
      A.isPrimitive_primPart ?_
    exact (hGq.dvd.trans (gcd_dvd_left _ _)).trans (map_assoc_primPart hA).dvd
  have hGdvdB : G ∣ B.primPart := by
    refine hGprim.dvd_of_fraction_map_dvd_fraction_map (K := FractionRing M)
      B.isPrimitive_primPart ?_
    exact (hGq.dvd.trans (gcd_dvd_right _ _)).trans (map_assoc_primPart hB).dvd
  have hdvdA : Polynomial.C d * G ∣ A := by
    conv_rhs => rw [A.eq_C_content_mul_primPart]
    exact mul_dvd_mul
      (map_dvd (Polynomial.C : M →+* M[X]) (hd ▸ gcd_dvd_left _ _)) hGdvdA
  have hdvdB : Polynomial.C d * G ∣ B := by
    conv_rhs => rw [B.eq_C_content_mul_primPart]
    exact mul_dvd_mul
      (map_dvd (Polynomial.C : M →+* M[X]) (hd ▸ gcd_dvd_right _ _)) hGdvdB
  -- (iii): maximality
  have hmax : ∀ e : M[X], e ∣ A → e ∣ B → e ∣ Polynomial.C d * G := by
    intro e heA heB
    have hce : e.content ∣ d := by
      rw [hd]
      exact dvd_gcd (content_dvd_of_dvd heA) (content_dvd_of_dvd heB)
    have hpe : e.primPart ∣ G := by
      refine e.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map
        (K := FractionRing M) hGprim ?_
      have h1 : (e.primPart).map (algebraMap M (FractionRing M))
          ∣ A.map (algebraMap M (FractionRing M)) :=
        Polynomial.map_dvd _ (e.primPart_dvd.trans heA)
      have h2 : (e.primPart).map (algebraMap M (FractionRing M))
          ∣ B.map (algebraMap M (FractionRing M)) :=
        Polynomial.map_dvd _ (e.primPart_dvd.trans heB)
      exact (dvd_gcd h1 h2).trans hGq.symm.dvd
    calc e = Polynomial.C e.content * e.primPart := e.eq_C_content_mul_primPart
      _ ∣ Polynomial.C d * G :=
        mul_dvd_mul (map_dvd (Polynomial.C : M →+* M[X]) hce) hpe
  -- (iv): normalized output
  have hnorm : _root_.normalize (Polynomial.C d * G) = Polynomial.C d * G := by
    apply normalize_eq_self_of_normalized_lcof
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      normalize_mul' _ _, hdnorm, hGlc]
  exact dvd_antisymm_of_normalize_eq hnorm (normalize_gcd A B)
    (dvd_gcd hdvdA hdvdB) (hmax _ (gcd_dvd_left A B) (gcd_dvd_right A B))

/-! ### The core over `D`, transported to `Frac(M)[X]` -/

open Azurite.BPR.Chapter8 in
/-- **Core correctness over `D`** (generalization of `subresGcd_int_qassoc`):
for `P, Q ≠ 0` with `deg P > deg Q ≥ 1`, the `Frac(M)[X]` image of
`subresGcd P Q` is associated to the fraction-field gcd, and the output is
nonzero. The `D`-level Algorithm 8.21 bridge
(`signedSubresultant_toPoly_domain`) is transported along
`algebraMap M (Frac M) ∘ ρ` by `sResP_map`. -/
private theorem subresGcd_frac_assoc (hρ : Function.Injective ρ)
    (P Q : AzPolynomial D) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    Associated
      ((AzPolynomial.toPoly (subresGcd P Q)).map
        ((algebraMap M (FractionRing M)).comp ρ))
      (GCDMonoid.gcd
        ((AzPolynomial.toPoly P).map ((algebraMap M (FractionRing M)).comp ρ))
        ((AzPolynomial.toPoly Q).map ((algebraMap M (FractionRing M)).comp ρ)))
    ∧ subresGcd P Q ≠ 0 := by
  set ψ : D →+* FractionRing M := (algebraMap M (FractionRing M)).comp ρ
    with hψ
  have hψinj : Function.Injective ψ := by
    intro a b h
    rw [hψ] at h
    simp only [RingHom.comp_apply] at h
    exact hρ (IsFractionRing.injective M (FractionRing M) h)
  set Aq : (FractionRing M)[X] := (AzPolynomial.toPoly P).map ψ with hAq
  set Bq : (FractionRing M)[X] := (AzPolynomial.toPoly Q).map ψ with hBq
  have hP' : AzPolynomial.toPoly P ≠ 0 := toPoly_ne_zero hP
  have hQ' : AzPolynomial.toPoly Q ≠ 0 := toPoly_ne_zero hQ
  have hAq0 : Aq ≠ 0 := by
    rw [hAq, Ne, Polynomial.map_eq_zero_iff hψinj]
    exact hP'
  have hBq0 : Bq ≠ 0 := by
    rw [hBq, Ne, Polynomial.map_eq_zero_iff hψinj]
    exact hQ'
  have hdA : Aq.natDegree = P.natDegree := by
    rw [hAq, Polynomial.natDegree_map_eq_of_injective hψinj,
      AzPolynomial.natDegree_toPoly]
  have hdB : Bq.natDegree = Q.natDegree := by
    rw [hBq, Polynomial.natDegree_map_eq_of_injective hψinj,
      AzPolynomial.natDegree_toPoly]
  have hpq' : Bq.natDegree < Aq.natDegree := by rw [hdA, hdB]; exact hpq
  have hq1' : 1 ≤ Bq.natDegree := by rw [hdB]; exact hq1
  -- Algorithm 8.21 bridge over the domain `D`
  have hlist := (signedSubresultant_toPoly_domain P Q hP hQ hpq hq1).1
  set sP := (signedSubresultant P Q).1 with hsP
  have hlen : sP.size = P.natDegree + 1 := by
    have := congrArg List.length hlist
    simpa using this
  -- index-wise identification, transported to `Frac(M)[X]` along `sResP_map`
  have hidx : ∀ j (hj : j < P.natDegree + 1),
      (AzPolynomial.toPoly (sP[j]!)).map ψ = sResP Aq Bq j := by
    intro j hj
    have hjs : j < sP.size := by omega
    have h1 : (sP.toList.map AzPolynomial.toPoly)[j]'(by simpa using hjs)
        = ((List.range (P.natDegree + 1)).map
            (sResP (AzPolynomial.toPoly P)
              (AzPolynomial.toPoly Q)))[j]'(by simpa using hj) := by
      congr 1
    rw [List.getElem_map, List.getElem_map, List.getElem_range] at h1
    have h2 : AzPolynomial.toPoly (sP[j]!)
        = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j := by
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hjs]
      simpa [Array.getElem_toList] using h1
    rw [h2, hAq, hBq, ← sResP_map hψinj]
  -- the gcd degree at `Frac(M)` (`EuclideanDomain`-instance, driving Ch. 8)
  set j₀ := (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial Aq Bq).natDegree
    with hj₀
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

/-! ### Assembly: `ngcdPoly` computes the `M[X]` gcd -/

private theorem map_toPoly_smul' (c : D) (T : AzPolynomial D) :
    (AzPolynomial.toPoly (c • T)).map ρ
      = Polynomial.C (ρ c) * ((AzPolynomial.toPoly T).map ρ) := by
  rw [toPoly_smul, Polynomial.smul_eq_C_mul, Polynomial.map_mul,
    Polynomial.map_C]

private theorem isUnit_frac_of_natDegree_eq_zero {p : (FractionRing M)[X]}
    (hp : p ≠ 0) (hd : p.natDegree = 0) : IsUnit p := by
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hd
  rw [hC]
  refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h => hp ?_))
  rw [hC, h, Polynomial.C_0]

/-- Fuse the two coefficient maps. -/
private theorem map_map_fuse' (T : AzPolynomial D) :
    ((AzPolynomial.toPoly T).map ρ).map (algebraMap M (FractionRing M))
      = (AzPolynomial.toPoly T).map ((algebraMap M (FractionRing M)).comp ρ) :=
  Polynomial.map_map _ _ _

set_option maxHeartbeats 1600000 in
/-- **Correctness of `ngcdPoly`, one tower level.** Under the bridge
package, `(toPoly (ngcdPoly P Q)).map ρ = gcd ((toPoly P).map ρ)
((toPoly Q).map ρ)` — the computable normalized gcd represents Mathlib's
normalized `M[X]` gcd exactly, for all `P, Q`. -/
theorem map_toPoly_ngcdPoly (hρ : Function.Injective ρ)
    (hrefl : ∀ a b : D, ρ a ∣ ρ b → a ∣ b)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    (P Q : AzPolynomial D) :
    (AzPolynomial.toPoly (ngcdPoly P Q)).map ρ
      = GCDMonoid.gcd ((AzPolynomial.toPoly P).map ρ)
          ((AzPolynomial.toPoly Q).map ρ) := by
  set A : M[X] := (AzPolynomial.toPoly P).map ρ with hA
  set B : M[X] := (AzPolynomial.toPoly Q).map ρ with hB
  have hκinj : Function.Injective (algebraMap M (FractionRing M)) :=
    IsFractionRing.injective M (FractionRing M)
  rw [ngcdPoly]
  by_cases hP0 : P = 0
  · rw [if_pos hP0]
    have hA0 : A = 0 := by rw [hA, hP0, toPoly_zero, Polynomial.map_zero]
    by_cases hQ0 : Q = 0
    · have hB0 : B = 0 := by rw [hB, hQ0, toPoly_zero, Polynomial.map_zero]
      rw [hQ0, leadNormalize_zero, toPoly_zero, Polynomial.map_zero, hA0, hB0,
        gcd_zero_right, normalize_zero]
    · rw [map_toPoly_leadNormalize hρ hrefl hgcd hQ0, hA0, gcd_zero_left, hB]
  rw [if_neg hP0]
  by_cases hQ0 : Q = 0
  · rw [if_pos hQ0]
    have hB0 : B = 0 := by rw [hB, hQ0, toPoly_zero, Polynomial.map_zero]
    rw [map_toPoly_leadNormalize hρ hrefl hgcd hP0, hB0, gcd_zero_right, hA]
  rw [if_neg hQ0]
  have hA0 : A ≠ 0 := hA ▸ map_toPoly_ne_zero' hρ hP0
  have hB0 : B ≠ 0 := hB ▸ map_toPoly_ne_zero' hρ hQ0
  have hd : ρ (contentGcdGen P Q) = GCDMonoid.gcd A.content B.content := by
    rw [hA, hB]
    exact map_contentGcdGen hgcd P Q
  -- `Frac(M)`-side abbreviations
  have hAq0 : A.map (algebraMap M (FractionRing M)) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff hκinj]
    exact hA0
  have hBq0 : B.map (algebraMap M (FractionRing M)) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff hκinj]
    exact hB0
  have hdAq : (A.map (algebraMap M (FractionRing M))).natDegree
      = P.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hκinj, hA,
      natDegree_map_toPoly' hρ]
  have hdBq : (B.map (algebraMap M (FractionRing M))).natDegree
      = Q.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hκinj, hB,
      natDegree_map_toPoly' hρ]
  -- common: apply `gcd_char` after producing the association per branch
  have happly : ∀ (g : AzPolynomial D), g ≠ 0 →
      Associated
        (((AzPolynomial.toPoly g).map ρ).map (algebraMap M (FractionRing M)))
        (GCDMonoid.gcd (A.map (algebraMap M (FractionRing M)))
          (B.map (algebraMap M (FractionRing M)))) →
      (AzPolynomial.toPoly (contentGcdGen P Q • primNormalized g)).map ρ
        = GCDMonoid.gcd A B := by
    intro g hg hassoc
    rw [map_toPoly_smul']
    obtain ⟨c, hc0, hkey, hprim, hlcn⟩ := primNormalized_spec hρ hrefl hgcd hg
    refine gcd_char hA0 hB0 hd hprim hlcn ?_
    have hkeyq := congrArg (Polynomial.map (algebraMap M (FractionRing M))) hkey
    rw [Polynomial.map_mul, Polynomial.map_C] at hkeyq
    have hcq0 : algebraMap M (FractionRing M) c ≠ 0 :=
      fun h => hc0 (hκinj (by rw [h, map_zero]))
    have hu : IsUnit (Polynomial.C (algebraMap M (FractionRing M) c)
        : (FractionRing M)[X]) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcq0)
    have h1 : Associated
        (((AzPolynomial.toPoly (primNormalized g)).map ρ).map
          (algebraMap M (FractionRing M)))
        (((AzPolynomial.toPoly g).map ρ).map
          (algebraMap M (FractionRing M))) := by
      rw [← hkeyq]
      exact ⟨hu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩
    exact h1.trans hassoc
  by_cases hdeg0 : P.natDegree = 0 ∨ Q.natDegree = 0
  · rw [if_pos hdeg0]
    -- constant case: the gcd is the content gcd
    rw [map_toPoly_smul', toPoly_one, Polynomial.map_one, mul_one,
      show Polynomial.C (ρ (contentGcdGen P Q))
        = Polynomial.C (ρ (contentGcdGen P Q)) * 1 from (mul_one _).symm]
    apply gcd_char hA0 hB0 hd Polynomial.isPrimitive_one
      (by rw [Polynomial.leadingCoeff_one, normalize_one])
    rw [Polynomial.map_one]
    have hunit : IsUnit (A.map (algebraMap M (FractionRing M)))
        ∨ IsUnit (B.map (algebraMap M (FractionRing M))) := by
      rcases hdeg0 with h | h
      · exact Or.inl
          (isUnit_frac_of_natDegree_eq_zero hAq0 (by rw [hdAq]; exact h))
      · exact Or.inr
          (isUnit_frac_of_natDegree_eq_zero hBq0 (by rw [hdBq]; exact h))
    rcases hunit with h | h
    · rw [gcd_isUnit_left h]
    · rw [gcd_isUnit_right h]
  rw [if_neg hdeg0]
  push Not at hdeg0
  obtain ⟨hPd0, hQd0⟩ := hdeg0
  by_cases hdeq : P.natDegree = Q.natDegree
  · rw [if_pos hdeq]
    set T := preStep P Q with hT
    have hlcP : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero' hP0
    have hlcPq : algebraMap M (FractionRing M) (ρ P.leadingCoeff) ≠ 0 :=
      fun h => hlcP (hρ (hκinj (by rw [h, map_zero, map_zero])))
    have hTq : ((AzPolynomial.toPoly T).map ρ).map
          (algebraMap M (FractionRing M))
        = Polynomial.C (algebraMap M (FractionRing M) (ρ P.leadingCoeff))
            * (B.map (algebraMap M (FractionRing M)))
          - Polynomial.C (algebraMap M (FractionRing M) (ρ Q.leadingCoeff))
            * (A.map (algebraMap M (FractionRing M))) := by
      rw [hT, preStep, toPoly_pre_step, Polynomial.map_sub, Polynomial.map_sub,
        Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
        Polynomial.map_C, Polynomial.map_C, hA, hB]
    have hstepq : GCDMonoid.gcd (A.map (algebraMap M (FractionRing M)))
          (((AzPolynomial.toPoly T).map ρ).map (algebraMap M (FractionRing M)))
        = GCDMonoid.gcd (A.map (algebraMap M (FractionRing M)))
            (B.map (algebraMap M (FractionRing M))) := by
      rw [hTq]
      exact gcd_pre_step _ _ hlcPq
    by_cases hT0 : T = 0
    · rw [if_pos hT0]
      -- proportional: `A ∣ B` over the fraction field, gcd = normalize A
      have hprop : Polynomial.C (algebraMap M (FractionRing M)
              (ρ P.leadingCoeff))
            * (B.map (algebraMap M (FractionRing M)))
          = Polynomial.C (algebraMap M (FractionRing M) (ρ Q.leadingCoeff))
            * (A.map (algebraMap M (FractionRing M))) := by
        have h := hTq
        rw [hT0, toPoly_zero, Polynomial.map_zero, Polynomial.map_zero] at h
        exact (sub_eq_zero.mp h.symm)
      have hdvd : A.map (algebraMap M (FractionRing M))
          ∣ B.map (algebraMap M (FractionRing M)) := by
        refine ⟨Polynomial.C (algebraMap M (FractionRing M)
            (ρ P.leadingCoeff))⁻¹
          * Polynomial.C (algebraMap M (FractionRing M)
            (ρ Q.leadingCoeff)), ?_⟩
        have h2 := congrArg
          (fun z => Polynomial.C
            (algebraMap M (FractionRing M) (ρ P.leadingCoeff))⁻¹ * z) hprop
        simp only [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlcPq,
          Polynomial.C_1, one_mul] at h2
        rw [h2, Polynomial.C_mul]
        ring
      refine happly P hP0 ?_
      rw [← hA, gcd_eq_normalize_left hdvd]
      exact (associated_normalize _)
    rw [if_neg hT0]
    by_cases hTd : T.natDegree = 0
    · rw [if_pos hTd]
      -- the pre-step output is a fraction-field unit: the gcd is `1`
      rw [map_toPoly_smul', toPoly_one, Polynomial.map_one, mul_one,
        show Polynomial.C (ρ (contentGcdGen P Q))
          = Polynomial.C (ρ (contentGcdGen P Q)) * 1 from (mul_one _).symm]
      apply gcd_char hA0 hB0 hd Polynomial.isPrimitive_one
        (by rw [Polynomial.leadingCoeff_one, normalize_one])
      rw [Polynomial.map_one, ← hstepq]
      have hTq0 : ((AzPolynomial.toPoly T).map ρ).map
          (algebraMap M (FractionRing M)) ≠ 0 := by
        rw [Ne, Polynomial.map_eq_zero_iff hκinj]
        exact map_toPoly_ne_zero' hρ hT0
      have hTdq : (((AzPolynomial.toPoly T).map ρ).map
          (algebraMap M (FractionRing M))).natDegree = 0 := by
        rw [Polynomial.natDegree_map_eq_of_injective hκinj,
          natDegree_map_toPoly' hρ]
        exact hTd
      rw [gcd_isUnit_right (isUnit_frac_of_natDegree_eq_zero hTq0 hTdq)]
    rw [if_neg hTd]
    -- main equal-degree branch: core on `(P, T)`, pre-step invisible
    have hlt : T.natDegree < P.natDegree := by
      rw [hT, preStep]
      refine pre_step_natDegree_lt hP0 hQ0 hdeq ?_
      rw [hT, preStep] at hT0
      exact hT0
    obtain ⟨hcore, hne⟩ := subresGcd_frac_assoc hρ P T hP0 hT0 hlt (by omega)
    refine happly _ hne ?_
    have h1 := hcore
    rw [← map_map_fuse', ← map_map_fuse', ← map_map_fuse', ← hA] at h1
    rw [← hstepq]
    exact h1
  rw [if_neg hdeq]
  by_cases hdlt : P.natDegree < Q.natDegree
  · rw [if_pos hdlt]
    obtain ⟨hcore, hne⟩ := subresGcd_frac_assoc hρ Q P hQ0 hP0 hdlt (by omega)
    refine happly _ hne ?_
    have h1 := hcore
    rw [← map_map_fuse', ← map_map_fuse', ← map_map_fuse', ← hA, ← hB] at h1
    rw [gcd_comm]
    exact h1
  · rw [if_neg hdlt]
    obtain ⟨hcore, hne⟩ := subresGcd_frac_assoc hρ P Q hP0 hQ0 (by omega)
      (by omega)
    refine happly _ hne ?_
    have h1 := hcore
    rw [← map_map_fuse', ← map_map_fuse', ← map_map_fuse', ← hA, ← hB] at h1
    exact h1

/-- Instance form of the main theorem: `NormalizedGcd.ngcd` on
`AzPolynomial D` (which is `ngcdPoly` by definition) represents the
normalized `M[X]` gcd. -/
theorem map_toPoly_ngcd (hρ : Function.Injective ρ)
    (hrefl : ∀ a b : D, ρ a ∣ ρ b → a ∣ b)
    (hgcd : ∀ a b : D, ρ (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (ρ a) (ρ b))
    (P Q : AzPolynomial D) :
    (AzPolynomial.toPoly (NormalizedGcd.ngcd P Q)).map ρ
      = GCDMonoid.gcd ((AzPolynomial.toPoly P).map ρ)
          ((AzPolynomial.toPoly Q).map ρ) :=
  map_toPoly_ngcdPoly hρ hrefl hgcd P Q

end TowerBridge

/-! ### The bundled bridge, and the induction step up the tower -/

/-- The Phase-3 hypothesis package, bundled: a coefficient-model
homomorphism along which `NormalizedGcd.ngcd` represents Mathlib's
normalized gcd. For the `AzInt`-based tower every `hom` is (the composite
of) ring isomorphisms, so `dvd_reflect` is automatic (see
`NormalizedGcdBridge.step`). -/
structure NormalizedGcdBridge (D M : Type _) [CommRing D] [DecidableEq D]
    [Azurite.ExactDiv D] [IsDomain D] [NormalizedGcd D] [CommRing M]
    [IsDomain M] [NormalizedGCDMonoid M] where
  /-- The coefficient-model homomorphism. -/
  hom : D →+* M
  /-- `hom` is injective. -/
  injective : Function.Injective hom
  /-- Divisibility reflects along `hom`. -/
  dvd_reflect : ∀ a b : D, hom a ∣ hom b → a ∣ b
  /-- `ngcd` represents Mathlib's normalized gcd. -/
  map_ngcd : ∀ a b : D,
    hom (NormalizedGcd.ngcd a b) = GCDMonoid.gcd (hom a) (hom b)

namespace NormalizedGcdBridge

variable {D M : Type _} [CommRing D] [DecidableEq D] [Azurite.ExactDiv D]
  [IsDomain D] [NormalizedGcd D] [CommRing M] [IsDomain M]
  [NormalizedGCDMonoid M]

/-- Bundled form of `contentGen_mul`: content is multiplicative. -/
theorem contentGen_mul' (β : NormalizedGcdBridge D M) (p q : AzPolynomial D) :
    contentGen (p * q) = contentGen p * contentGen q :=
  contentGen_mul β.injective β.map_ngcd p q

/-- Bundled form of `map_toPoly_ngcdPoly`. -/
theorem map_toPoly_ngcd' (β : NormalizedGcdBridge D M) (P Q : AzPolynomial D) :
    (AzPolynomial.toPoly (NormalizedGcd.ngcd P Q)).map β.hom
      = GCDMonoid.gcd ((AzPolynomial.toPoly P).map β.hom)
          ((AzPolynomial.toPoly Q).map β.hom) :=
  map_toPoly_ngcd β.injective β.dvd_reflect β.map_ngcd P Q

/-- **The induction step up the tower**: a *surjective* bridge `D → M`
induces a bridge `AzPolynomial D → M[X]` (via `toPoly` followed by the
coefficient map), whose `map_ngcd` field is exactly
`map_toPoly_ngcdPoly`. For the `AzInt`-based tower every level's `hom` is
bijective, so iterating this step equips the whole nested tower. -/
noncomputable def step (β : NormalizedGcdBridge D M)
    (hsurj : Function.Surjective β.hom) :
    NormalizedGcdBridge (AzPolynomial D) (Polynomial M) where
  hom := (Polynomial.mapRingHom β.hom).comp toPolyHom
  injective := by
    intro a b h
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom] at h
    exact toPoly_inj.mp (Polynomial.map_injective _ β.injective h)
  dvd_reflect := by
    intro a b h
    have hsurj' : Function.Surjective
        ((Polynomial.mapRingHom β.hom).comp toPolyHom) := by
      intro p
      obtain ⟨q, hq⟩ := Polynomial.map_surjective _ hsurj p
      refine ⟨AzPolynomial.ofPoly q, ?_⟩
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom]
      show (AzPolynomial.toPoly (AzPolynomial.ofPoly q)).map _ = p
      rw [toPoly_ofPoly, hq]
    obtain ⟨c, hc⟩ := h
    obtain ⟨c', rfl⟩ := hsurj' c
    refine ⟨c', ?_⟩
    have hinj : Function.Injective
        ((Polynomial.mapRingHom β.hom).comp toPolyHom) := by
      intro x y hxy
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom] at hxy
      exact toPoly_inj.mp (Polynomial.map_injective _ β.injective hxy)
    apply hinj
    rw [map_mul]
    exact hc
  map_ngcd := fun a b =>
    map_toPoly_ngcd β.injective β.dvd_reflect β.map_ngcd a b

/-- The step homomorphism of a surjective bridge is again surjective, so
the step can be iterated up the tower. -/
theorem step_hom_surjective (β : NormalizedGcdBridge D M)
    (hsurj : Function.Surjective β.hom) :
    Function.Surjective (β.step hsurj).hom := by
  intro p
  obtain ⟨q, hq⟩ := Polynomial.map_surjective _ hsurj p
  refine ⟨AzPolynomial.ofPoly q, ?_⟩
  show ((Polynomial.mapRingHom β.hom).comp toPolyHom) _ = p
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom]
  show (AzPolynomial.toPoly (AzPolynomial.ofPoly q)).map _ = p
  rw [toPoly_ofPoly, hq]

end NormalizedGcdBridge

end Azurite.AzPolynomial
