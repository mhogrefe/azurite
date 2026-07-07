import Azurite.AzMvPolynomial.Equiv.Gcd

/-!
# The `NormalizedGCDMonoid` / `UniqueFactorizationMonoid` structure on the
tower coefficient ring `AzMvPolynomial n AzInt ord`

The multivariate Yun square-free factorization (`mvSquarefreeFactorization`)
peels off the first variable and runs the *univariate* Yun over the
coefficient ring `R := AzMvPolynomial n AzInt ord`. To instantiate the
univariate UFD-Yun correctness (`Azurite.AzPolynomial.UFD`), `R` must be a
characteristic-zero `UniqueFactorizationMonoid` **and** a
`NormalizedGCDMonoid` — and, crucially, its `GCDMonoid.gcd` must agree with
the computable `AzMvPolynomial.gcd` so the algorithm's gcds are the lawful
ones.

This file supplies both:

* `UniqueFactorizationMonoid R` — transported from `MvPolynomial (Fin n) ℤ`
  (a Mathlib UFD) across the ring iso `ringEquivMvPolynomialInt`.
* `NormalizedGCDMonoid R` — transported from the nested *model* tower
  `ModelPoly n` (a Mathlib `NormalizedGCDMonoid`) across the composite ring
  iso `modelEquiv : R ≃+* ModelPoly n`. Because `AzMvPolynomial.gcd`
  represents the model's normalized gcd exactly (`towerBridge_toNested_gcd`),
  the transported `GCDMonoid.gcd` **equals** `AzMvPolynomial.gcd`
  (`GCDMonoid_gcd_eq`).

The generic `RingEquiv.transfer*` helpers (pull a
`NormalizationMonoid` / `GCDMonoid` / `NormalizedGCDMonoid` back along a ring
isomorphism) are reusable.
-/

open scoped Classical

set_option maxHeartbeats 1000000

/-! ### Generic transport of the gcd structure along a ring isomorphism -/

/-- Pull a `NormalizationMonoid` back along a ring isomorphism. -/
@[reducible] noncomputable def RingEquiv.transferNormalizationMonoid
    {α β : Type*} [CommRing α] [IsDomain α] [CommRing β] [IsDomain β]
    [NormalizationMonoid β] (e : α ≃+* β) : NormalizationMonoid α where
  normUnit a := (Units.mapEquiv (e.symm.toMulEquiv)) (normUnit (e a))
  normUnit_zero := by simp
  normUnit_mul {a b} ha hb := by
    have hea : e a ≠ 0 := fun h => ha (by simpa using congrArg e.symm h)
    have heb : e b ≠ 0 := fun h => hb (by simpa using congrArg e.symm h)
    simp only [map_mul, normUnit_mul hea heb]
  normUnit_coe_units u := by
    have : e ↑u = ↑(Units.mapEquiv e.toMulEquiv u) := rfl
    rw [this, normUnit_coe_units]; ext; simp

/-- Pull a `GCDMonoid` back along a ring isomorphism. -/
@[reducible] noncomputable def RingEquiv.transferGCDMonoid
    {α β : Type*} [CommRing α] [IsDomain α] [CommRing β] [IsDomain β]
    [GCDMonoid β] (e : α ≃+* β) : GCDMonoid α where
  gcd a b := e.symm (gcd (e a) (e b))
  lcm a b := e.symm (lcm (e a) (e b))
  gcd_dvd_left a b := by simpa using map_dvd e.symm.toRingHom (gcd_dvd_left (e a) (e b))
  gcd_dvd_right a b := by simpa using map_dvd e.symm.toRingHom (gcd_dvd_right (e a) (e b))
  dvd_gcd {a b c} hac hab := by
    have := map_dvd e.symm.toRingHom (dvd_gcd (map_dvd e.toRingHom hac) (map_dvd e.toRingHom hab))
    simpa using this
  gcd_mul_lcm a b := by
    have h := gcd_mul_lcm (e a) (e b)
    have : Associated (e.symm (gcd (e a) (e b)) * e.symm (lcm (e a) (e b))) (e.symm (e a * e b)) := by
      rw [← map_mul]; exact Associated.map e.symm.toMonoidHom h
    simpa using this
  lcm_zero_left a := by simp
  lcm_zero_right a := by simp

/-- With the transported `NormalizationMonoid`, `normalize` conjugates to the
target's `normalize` across the ring isomorphism. -/
theorem RingEquiv.transfer_normalize
    {α β : Type*} [CommRing α] [IsDomain α] [CommRing β] [IsDomain β]
    [NormalizationMonoid β] (e : α ≃+* β) (a : α) :
    letI := e.transferNormalizationMonoid
    normalize a = e.symm (normalize (e a)) := by
  letI := e.transferNormalizationMonoid
  rw [normalize_apply, normalize_apply]
  show a * ↑((Units.mapEquiv (e.symm.toMulEquiv)) (normUnit (e a)))
      = e.symm (e a * ↑(normUnit (e a)))
  rw [map_mul, RingEquiv.symm_apply_apply]; rfl

/-- Pull a `NormalizedGCDMonoid` back along a ring isomorphism. -/
@[reducible] noncomputable def RingEquiv.transferNormalizedGCDMonoid
    {α β : Type*} [CommRing α] [IsDomain α] [CommRing β] [IsDomain β]
    [NormalizedGCDMonoid β] (e : α ≃+* β) : NormalizedGCDMonoid α :=
  letI := e.transferNormalizationMonoid
  letI := e.transferGCDMonoid
  { normalize_gcd := by
      intro a b
      rw [e.transfer_normalize]
      show e.symm (normalize (e (e.symm (gcd (e a) (e b))))) = e.symm (gcd (e a) (e b))
      rw [RingEquiv.apply_symm_apply, normalize_gcd]
    normalize_lcm := by
      intro a b
      rw [e.transfer_normalize]
      show e.symm (normalize (e (e.symm (lcm (e a) (e b))))) = e.symm (lcm (e a) (e b))
      rw [RingEquiv.apply_symm_apply, normalize_lcm] }

namespace Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-! ### `UniqueFactorizationMonoid` on the tower ring -/

/-- `AzMvPolynomial n AzInt ord` is a unique factorization monoid, transported
from `MvPolynomial (Fin n) ℤ`. -/
noncomputable instance instUniqueFactorizationMonoid :
    UniqueFactorizationMonoid (AzMvPolynomial n AzInt ord) :=
  MulEquiv.uniqueFactorizationMonoid
    (AzMvPolynomial.ringEquivMvPolynomialInt (n := n) (ord := ord)).symm.toMulEquiv
    inferInstance

/-- `AzMvPolynomial n AzInt ord` has characteristic zero (transported from
`MvPolynomial (Fin n) ℤ`). -/
instance instCharZero : CharZero (AzMvPolynomial n AzInt ord) :=
  (AzMvPolynomial.ringEquivMvPolynomialInt (n := n) (ord := ord)).toRingHom.charZero

/-! ### The ring iso onto the normalized model, and the `NormalizedGCDMonoid` -/

/-- The composite ring isomorphism `AzMvPolynomial n AzInt ord ≃+* ModelPoly n`
onto the mathematical model tower (a `NormalizedGCDMonoid`). -/
noncomputable def modelEquiv (n : ℕ) :
    AzMvPolynomial n AzInt ord ≃+* ModelPoly n :=
  (nestedRingEquiv n).trans
    (RingEquiv.ofBijective (towerBridge n).hom
      ⟨(towerBridge n).injective, (towerBridgeAux n).2⟩)

theorem modelEquiv_apply (n : ℕ) (P : AzMvPolynomial n AzInt ord) :
    modelEquiv n P = (towerBridge n).hom (toNested n P) := by
  rw [modelEquiv, RingEquiv.trans_apply, toNested_eq]; rfl

/-- `modelEquiv` intertwines `AzMvPolynomial.gcd` with the model's normalized
gcd. -/
theorem modelEquiv_gcd (P Q : AzMvPolynomial n AzInt ord) :
    modelEquiv n (AzMvPolynomial.gcd P Q)
      = GCDMonoid.gcd (modelEquiv n P) (modelEquiv n Q) := by
  rw [modelEquiv_apply, towerBridge_toNested_gcd, ← modelEquiv_apply, ← modelEquiv_apply]

/-- `AzMvPolynomial n AzInt ord` is a normalized gcd monoid, transported from
the model tower `ModelPoly n`. -/
noncomputable instance instNormalizedGCDMonoid :
    NormalizedGCDMonoid (AzMvPolynomial n AzInt ord) :=
  (modelEquiv n).transferNormalizedGCDMonoid

/-- **The lawfulness of the computable gcd**: Mathlib's normalized
`GCDMonoid.gcd` on the tower ring is exactly the computable
`AzMvPolynomial.gcd`. -/
theorem GCDMonoid_gcd_eq (P Q : AzMvPolynomial n AzInt ord) :
    GCDMonoid.gcd P Q = AzMvPolynomial.gcd P Q := by
  show (modelEquiv n).symm (GCDMonoid.gcd (modelEquiv n P) (modelEquiv n Q)) = _
  rw [← modelEquiv_gcd]
  exact (modelEquiv n).symm_apply_apply _

/-! ### The tower-commutation diagram

`ModelPoly (n+1)` is *definitionally* `Polynomial (ModelPoly n)`, and the model
tower commutes with the boundary iso `e := toPoly ∘ finSuccEquiv` peeling `x₀`:
`modelEquiv (n+1)` is `Polynomial.map (modelEquiv n)` precomposed with `e`. -/

/-- The one-level model image of `toNested (n+1)`: `Polynomial.map`-ing the
`x₀`-peel `toPoly (finSuccEquiv X)`. -/
theorem toPoly_toNested_succ (n : ℕ) (X : AzMvPolynomial (n + 1) AzInt ord) :
    AzPolynomial.toPoly (nestedDown (toNested (n + 1) X))
      = Polynomial.map ((nestedRingEquiv (ord := ord) n :
          AzMvPolynomial n AzInt ord →+* NestedPoly n))
          (AzPolynomial.toPoly (finSuccEquiv X)) := by
  have hfun : (toNested (ord := ord) n)
      = ⇑((nestedRingEquiv (ord := ord) n :
          AzMvPolynomial n AzInt ord →+* NestedPoly n)) :=
    funext (toNested_eq (ord := ord) n)
  have hmap : toNested (n + 1) X
      = AzPolynomial.map (nestedRingEquiv (ord := ord) n) (finSuccEquiv X) := by
    show AzPolynomial.normalize ((finSuccEquiv X).coeffs.map (toNested (ord := ord) n))
        = AzPolynomial.normalize ((finSuccEquiv X).coeffs.map _)
    rw [hfun]
  show AzPolynomial.toPoly (toNested (n + 1) X) = _
  rw [hmap, AzPolynomial.toPoly_map]

/-- `modelEquiv` as a ring hom is `towerBridge.hom ∘ nestedRingEquiv`. -/
theorem modelEquiv_toRingHom_eq (n : ℕ) :
    ((modelEquiv (ord := ord) n : AzMvPolynomial n AzInt ord →+* ModelPoly n))
      = (towerBridge n).hom.comp (nestedRingEquiv (ord := ord) n) := by
  ext x
  show modelEquiv (ord := ord) n x = (towerBridge n).hom ((nestedRingEquiv (ord := ord) n) x)
  rw [modelEquiv_apply, toNested_eq]

/-- **The tower-commutation square**: `modelEquiv (n+1)` factors as
`Polynomial.map (modelEquiv n)` after peeling `x₀`. -/
theorem modelEquiv_succ (n : ℕ) (X : AzMvPolynomial (n + 1) AzInt ord) :
    (modelEquiv (n + 1) X : Polynomial (ModelPoly n))
      = Polynomial.map (modelEquiv (ord := ord) n :
          AzMvPolynomial n AzInt ord →+* ModelPoly n)
          (AzPolynomial.toPoly (finSuccEquiv X)) := by
  rw [modelEquiv_apply, towerBridge_succ_hom_apply, toPoly_toNested_succ, Polynomial.map_map,
      modelEquiv_toRingHom_eq]

/-! ### Normalization transports along `modelEquiv` -/

/-- `normUnit` transports along `modelEquiv` (holds by construction of the
transported normalization structure). -/
theorem normUnit_modelEquiv (x : AzMvPolynomial n AzInt ord) :
    (modelEquiv n) ((normUnit x : (AzMvPolynomial n AzInt ord)ˣ) : AzMvPolynomial n AzInt ord)
      = ((normUnit (modelEquiv n x) : (ModelPoly n)ˣ) : ModelPoly n) := by
  have hnu : (normUnit x : (AzMvPolynomial n AzInt ord)ˣ)
      = (Units.mapEquiv ((modelEquiv n).symm.toMulEquiv)) (normUnit (modelEquiv n x)) := rfl
  rw [hnu, Units.coe_mapEquiv]
  exact RingEquiv.apply_symm_apply _ _

/-- `Polynomial.map (modelEquiv n)` intertwines `normalize`. -/
theorem map_normalize (p : Polynomial (AzMvPolynomial n AzInt ord)) :
    Polynomial.map ((modelEquiv (ord := ord) n :
        AzMvPolynomial n AzInt ord →+* ModelPoly n)) (normalize p)
      = normalize (Polynomial.map ((modelEquiv (ord := ord) n :
          AzMvPolynomial n AzInt ord →+* ModelPoly n)) p) := by
  rw [normalize_apply, normalize_apply, Polynomial.coe_normUnit, Polynomial.coe_normUnit,
      Polynomial.map_mul, Polynomial.map_C,
      Polynomial.leadingCoeff_map_of_injective (modelEquiv (ord := ord) n).injective]
  congr 2
  exact normUnit_modelEquiv p.leadingCoeff

/-! ### The `x₀`-peel iso and gcd lawfulness in `Polynomial R` -/

/-- The boundary iso `AzMvPolynomial (n+1) ≃+* Polynomial (AzMvPolynomial n)`
peeling `x₀` (`toPoly ∘ finSuccEquiv`). -/
noncomputable def peelEquiv (n : ℕ) :
    AzMvPolynomial (n + 1) AzInt ord ≃+* Polynomial (AzMvPolynomial n AzInt ord) :=
  (finSuccAlgEquiv).toRingEquiv.trans AzPolynomial.ringEquivPolynomial

theorem peelEquiv_apply (n : ℕ) (X : AzMvPolynomial (n + 1) AzInt ord) :
    peelEquiv n X = AzPolynomial.toPoly (finSuccEquiv X) := rfl

/-- **Gcd lawfulness in the peeled tower**: the `x₀`-peel of
`AzMvPolynomial.gcd` is Mathlib's normalized `GCDMonoid.gcd` in
`Polynomial (AzMvPolynomial n AzInt ord)`. This is the linchpin for the
univariate UFD-Yun `hgcd_law`. -/
theorem toPoly_finSuccEquiv_gcd (a b : AzMvPolynomial (n + 1) AzInt ord) :
    AzPolynomial.toPoly (finSuccEquiv (AzMvPolynomial.gcd a b))
      = GCDMonoid.gcd (AzPolynomial.toPoly (finSuccEquiv a))
          (AzPolynomial.toPoly (finSuccEquiv b)) := by
  rw [← peelEquiv_apply, ← peelEquiv_apply, ← peelEquiv_apply]
  set g := peelEquiv n (AzMvPolynomial.gcd a b) with hg
  set G := GCDMonoid.gcd (peelEquiv n a) (peelEquiv n b) with hG
  have hdl : g ∣ peelEquiv n a := hg ▸ map_dvd (peelEquiv n) (gcd_dvd_left a b)
  have hdr : g ∣ peelEquiv n b := hg ▸ map_dvd (peelEquiv n) (gcd_dvd_right a b)
  have hgG : g ∣ G := hG ▸ GCDMonoid.dvd_gcd hdl hdr
  have hGg : G ∣ g := by
    have hGa : (peelEquiv n).symm G ∣ a := by
      have := map_dvd (peelEquiv n).symm (hG ▸ GCDMonoid.gcd_dvd_left (peelEquiv n a) (peelEquiv n b))
      simpa using this
    have hGb : (peelEquiv n).symm G ∣ b := by
      have := map_dvd (peelEquiv n).symm (hG ▸ GCDMonoid.gcd_dvd_right (peelEquiv n a) (peelEquiv n b))
      simpa using this
    have := map_dvd (peelEquiv n) (AzMvPolynomial.dvd_gcd hGa hGb)
    simpa [hg] using this
  have hf_inj : Function.Injective
      (Polynomial.map (modelEquiv (ord := ord) n : AzMvPolynomial n AzInt ord →+* ModelPoly n)) :=
    Polynomial.map_injective _ (modelEquiv (ord := ord) n).injective
  have hfg : Polynomial.map (modelEquiv (ord := ord) n :
        AzMvPolynomial n AzInt ord →+* ModelPoly n) g
      = modelEquiv (n + 1) (AzMvPolynomial.gcd a b) := by
    rw [hg, peelEquiv_apply]; exact (modelEquiv_succ n (AzMvPolynomial.gcd a b)).symm
  have hmnorm : normalize (modelEquiv (n + 1) (AzMvPolynomial.gcd a b))
      = modelEquiv (n + 1) (AzMvPolynomial.gcd a b) := by
    rw [modelEquiv_gcd]; exact normalize_gcd _ _
  have hgnorm : normalize g = g := by
    apply hf_inj
    rw [map_normalize, hfg]; exact hmnorm
  calc g = normalize g := hgnorm.symm
    _ = normalize G := normalize_eq_normalize hgG hGg
    _ = G := hG ▸ normalize_gcd _ _

end Azurite.AzMvPolynomial
