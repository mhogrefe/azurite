import Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxSeries

/-! # BPR §2.6 — functoriality of Puiseux series

A ring isomorphism `e : A ≃+* B` of coefficient fields induces a ring isomorphism
`PuiseuxSeries A ≃+* PuiseuxSeries B` (`puiseuxCongr`), by applying `e` coefficientwise. This is the
functoriality used in Theorem 2.92 to transport `IsAlgClosed` along `C ≅ R[i]`.

We package the coefficientwise action of a ring hom on Hahn series as a `RingHom`
(`HahnSeries.mapRingHom`) and a ring iso (`HahnSeries.mapRingEquiv`), check it commutes with the
exponent-rescaling embedding `puiseuxEmb`, and conclude it carries the Puiseux subfield onto its
image. -/

namespace Azurite.BPR

open HahnSeries

section Map

variable {Γ : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  {R S : Type*} [CommRing R] [CommRing S]

/-- A ring hom on coefficients induces a ring hom on Hahn series. -/
def HahnSeries.mapRingHom (f : R →+* S) : HahnSeries Γ R →+* HahnSeries Γ S where
  toFun x := x.map f
  map_zero' := by ext g; exact map_zero f
  map_one' := by
    ext g
    show f ((1 : HahnSeries Γ R).coeff g) = (1 : HahnSeries Γ S).coeff g
    rw [coeff_one, coeff_one, apply_ite f, map_one, map_zero]
  map_add' x y := by ext g; exact map_add f (x.coeff g) (y.coeff g)
  map_mul' x y := HahnSeries.map_mul f.toNonUnitalRingHom

@[simp] theorem HahnSeries.mapRingHom_coeff (f : R →+* S) (x : HahnSeries Γ R) (g : Γ) :
    (HahnSeries.mapRingHom f x).coeff g = f (x.coeff g) := rfl

/-- A ring iso on coefficients induces a ring iso on Hahn series. -/
def HahnSeries.mapRingEquiv (e : R ≃+* S) : HahnSeries Γ R ≃+* HahnSeries Γ S :=
  { HahnSeries.mapRingHom (e : R →+* S) with
    invFun := fun x => x.map (e.symm : S →+* R)
    left_inv := fun x => by
      ext g; show (e.symm : S →+* R) ((e : R →+* S) (x.coeff g)) = x.coeff g; simp
    right_inv := fun x => by
      ext g; show (e : R →+* S) ((e.symm : S →+* R) (x.coeff g)) = x.coeff g; simp }

@[simp] theorem HahnSeries.mapRingEquiv_coeff (e : R ≃+* S) (x : HahnSeries Γ R) (g : Γ) :
    (HahnSeries.mapRingEquiv e x).coeff g = e (x.coeff g) := rfl

@[simp] theorem HahnSeries.mapRingEquiv_symm (e : R ≃+* S) :
    (HahnSeries.mapRingEquiv e (Γ := Γ)).symm = HahnSeries.mapRingEquiv e.symm := rfl

end Map

/-- Coefficientwise mapping commutes with exponent-embedding `embDomain`. -/
theorem HahnSeries.map_embDomain {Γ₁ Γ₂ : Type*} [PartialOrder Γ₁] [PartialOrder Γ₂]
    {A B : Type*} [Zero A] [Zero B] {F : Type*} [FunLike F A B] [ZeroHomClass F A B]
    (g : F) (f : Γ₁ ↪o Γ₂) (x : HahnSeries Γ₁ A) :
    (HahnSeries.embDomain f x).map g = HahnSeries.embDomain f (x.map g) := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [HahnSeries.map_coeff, HahnSeries.embDomain_coeff, HahnSeries.embDomain_coeff,
      HahnSeries.map_coeff]
  · rw [HahnSeries.map_coeff, HahnSeries.embDomain_notin_range hb,
      HahnSeries.embDomain_notin_range hb, map_zero]

section Puiseux

variable {R S : Type*} [Field R] [Field S]

/-- The coefficient map commutes with the exponent-rescaling embedding `puiseuxEmb`. -/
theorem mapRingHom_puiseuxEmb (e : R →+* S) (q : ℕ+) (z : HahnSeries ℤ R) :
    HahnSeries.mapRingHom e (puiseuxEmb R q z)
      = puiseuxEmb S q (HahnSeries.mapRingHom e z) := by
  show (puiseuxEmb R q z).map e = puiseuxEmb S q (z.map e)
  rw [puiseuxEmb, HahnSeries.embDomainRingHom_apply, HahnSeries.map_embDomain, puiseuxEmb,
    HahnSeries.embDomainRingHom_apply]

/-- The coefficient iso carries `PuiseuxSeries R` into `PuiseuxSeries S`. -/
theorem mapRingEquiv_mem_puiseux (e : R ≃+* S) {x : HahnSeries ℚ R}
    (hx : x ∈ PuiseuxSeries R) : HahnSeries.mapRingEquiv e x ∈ PuiseuxSeries S := by
  rw [mem_puiseuxSeries_iff] at hx ⊢
  obtain ⟨q, hq⟩ := hx
  rw [puiseuxSubfield, RingHom.mem_fieldRange] at hq
  obtain ⟨z, rfl⟩ := hq
  refine ⟨q, ?_⟩
  rw [puiseuxSubfield, RingHom.mem_fieldRange]
  exact ⟨HahnSeries.mapRingHom (e : R →+* S) z, (mapRingHom_puiseuxEmb (e : R →+* S) q z).symm⟩

/-- **Functoriality of Puiseux series.** A ring iso `e : R ≃+* S` induces a ring iso
`PuiseuxSeries R ≃+* PuiseuxSeries S` by applying `e` to each coefficient. -/
noncomputable def puiseuxCongr (e : R ≃+* S) : PuiseuxSeries R ≃+* PuiseuxSeries S where
  toFun x := ⟨HahnSeries.mapRingEquiv e x.1, mapRingEquiv_mem_puiseux e x.2⟩
  invFun y := ⟨(HahnSeries.mapRingEquiv e).symm y.1, by
    rw [HahnSeries.mapRingEquiv_symm]; exact mapRingEquiv_mem_puiseux e.symm y.2⟩
  left_inv x := Subtype.ext ((HahnSeries.mapRingEquiv e).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((HahnSeries.mapRingEquiv e).apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul (HahnSeries.mapRingEquiv e) x.1 y.1)
  map_add' x y := Subtype.ext (map_add (HahnSeries.mapRingEquiv e) x.1 y.1)

@[simp] theorem puiseuxCongr_coe (e : R ≃+* S) (x : PuiseuxSeries R) :
    ((puiseuxCongr e x : PuiseuxSeries S) : HahnSeries ℚ S) = HahnSeries.mapRingEquiv e x.1 := rfl

/-- The coefficient ring hom carries `PuiseuxSeries R` into `PuiseuxSeries S`. -/
theorem mapRingHom_mem_puiseux (f : R →+* S) {x : HahnSeries ℚ R} (hx : x ∈ PuiseuxSeries R) :
    HahnSeries.mapRingHom f x ∈ PuiseuxSeries S := by
  rw [mem_puiseuxSeries_iff] at hx ⊢
  obtain ⟨q, hq⟩ := hx
  rw [puiseuxSubfield, RingHom.mem_fieldRange] at hq
  obtain ⟨z, rfl⟩ := hq
  refine ⟨q, ?_⟩
  rw [puiseuxSubfield, RingHom.mem_fieldRange]
  exact ⟨HahnSeries.mapRingHom f z, (mapRingHom_puiseuxEmb f q z).symm⟩

/-- **Functoriality (ring-hom version).** A ring hom `f : R →+* S` induces a ring hom
`PuiseuxSeries R →+* PuiseuxSeries S`. -/
noncomputable def puiseuxMapRingHom (f : R →+* S) : PuiseuxSeries R →+* PuiseuxSeries S where
  toFun x := ⟨HahnSeries.mapRingHom f x.1, mapRingHom_mem_puiseux f x.2⟩
  map_one' := Subtype.ext (map_one (HahnSeries.mapRingHom f))
  map_mul' x y := Subtype.ext (map_mul (HahnSeries.mapRingHom f) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (HahnSeries.mapRingHom f))
  map_add' x y := Subtype.ext (map_add (HahnSeries.mapRingHom f) x.1 y.1)

@[simp] theorem puiseuxMapRingHom_coe (f : R →+* S) (x : PuiseuxSeries R) :
    ((puiseuxMapRingHom f x : PuiseuxSeries S) : HahnSeries ℚ S) = HahnSeries.mapRingHom f x.1 := rfl

/-- A `ZeroHom`/additive coefficient map carries `PuiseuxSeries R` into `PuiseuxSeries S`. -/
theorem map_zeroHom_mem_puiseux {F : Type*} [FunLike F R S] [ZeroHomClass F R S] (g : F)
    {x : HahnSeries ℚ R} (hx : x ∈ PuiseuxSeries R) : x.map g ∈ PuiseuxSeries S := by
  rw [mem_puiseuxSeries_iff] at hx ⊢
  obtain ⟨q, hq⟩ := hx
  rw [puiseuxSubfield, RingHom.mem_fieldRange] at hq
  obtain ⟨z, rfl⟩ := hq
  refine ⟨q, ?_⟩
  rw [puiseuxSubfield, RingHom.mem_fieldRange]
  refine ⟨z.map g, ?_⟩
  simp only [puiseuxEmb, HahnSeries.embDomainRingHom_apply]
  rw [HahnSeries.map_embDomain]

end Puiseux

end Azurite.BPR
