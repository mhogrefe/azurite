import Azurite.BasuPollackRoy.Chapter3.Section3_1.SemialgebraicHomeomorphism
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.IsomorphismClasses

/-! # BPR §3.1 — the groupoid of semialgebraic sets

Semialgebraic sets (of any ambient dimension over `R`) and semialgebraic homeomorphisms form a
**groupoid**. We package this two ways:

* the elementary statement that *being semialgebraically homeomorphic is an equivalence relation*
  (`semialgHomeomorphicSetoid`), and
* an actual `CategoryTheory.Groupoid (SemialgSet R)` instance.

Morphisms are semialgebraic homeomorphisms taken **up to agreement on the carrier** (a `Quotient` by
`Set.EqOn`). This is exactly what makes every morphism invertible: `f ∘ f⁻¹` is the identity *on the
carrier*, not as a raw total function, so the inverse laws hold only after the quotient. The
isomorphism relation of this groupoid recovers `SemialgHomeomorphic`. -/

namespace Azurite.BPR

open CategoryTheory

variable (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A **semialgebraic set** over `R`, of arbitrary ambient dimension. -/
structure SemialgSet where
  /-- the ambient dimension -/
  dim : ℕ
  /-- the underlying subset of `R^dim` -/
  carrier : Set (Fin dim → R)
  /-- the carrier is semialgebraic -/
  isSemialgebraic : IsSemialgebraicSet carrier

variable {R}

/-! ### Being semialgebraically homeomorphic is an equivalence relation -/

/-- `X` and `Y` are **semialgebraically homeomorphic** if some semialgebraic homeomorphism connects
them. -/
def SemialgHomeomorphic (X Y : SemialgSet R) : Prop :=
  ∃ (f : (Fin X.dim → R) → (Fin Y.dim → R)) (g : (Fin Y.dim → R) → (Fin X.dim → R)),
    IsSemialgebraicHomeomorphism X.carrier Y.carrier f g

theorem SemialgHomeomorphic.rfl (X : SemialgSet R) : SemialgHomeomorphic X X :=
  ⟨id, id, IsSemialgebraicHomeomorphism.refl X.isSemialgebraic⟩

theorem SemialgHomeomorphic.symm {X Y : SemialgSet R} :
    SemialgHomeomorphic X Y → SemialgHomeomorphic Y X :=
  fun ⟨f, g, hfg⟩ => ⟨g, f, hfg.symm⟩

theorem SemialgHomeomorphic.trans {X Y Z : SemialgSet R} :
    SemialgHomeomorphic X Y → SemialgHomeomorphic Y Z → SemialgHomeomorphic X Z :=
  fun ⟨f, g, hfg⟩ ⟨f', g', hfg'⟩ => ⟨f' ∘ f, g ∘ g', hfg.trans hfg'⟩

/-- **Being semialgebraically homeomorphic is an equivalence relation.** -/
theorem semialgHomeomorphic_equivalence : Equivalence (SemialgHomeomorphic (R := R)) :=
  ⟨SemialgHomeomorphic.rfl, SemialgHomeomorphic.symm, SemialgHomeomorphic.trans⟩

/-- The equivalence relation "semialgebraically homeomorphic" as a `Setoid`. -/
instance semialgHomeomorphicSetoid : Setoid (SemialgSet R) :=
  ⟨SemialgHomeomorphic, semialgHomeomorphic_equivalence⟩

/-! ### The groupoid of semialgebraic sets and semialgebraic homeomorphisms

Morphisms are semialgebraic homeomorphisms (`SAHom`) taken up to agreement on the carrier
(`SAHom.rel`). The quotient is what makes the inverse laws hold: `f ∘ f⁻¹` is the identity only on
the carrier. -/

/-- A semialgebraic homeomorphism between two `SemialgSet`s, as raw data. -/
structure SAHom (X Y : SemialgSet R) where
  /-- the underlying total map -/
  toFun : (Fin X.dim → R) → (Fin Y.dim → R)
  /-- its inverse -/
  invFun : (Fin Y.dim → R) → (Fin X.dim → R)
  /-- the homeomorphism data -/
  isHomeo : IsSemialgebraicHomeomorphism X.carrier Y.carrier toFun invFun

/-- Two `SAHom`s are identified when their forward maps agree on `X.carrier` and their inverses
agree on `Y.carrier`. -/
def SAHom.rel {X Y : SemialgSet R} (f g : SAHom X Y) : Prop :=
  Set.EqOn f.toFun g.toFun X.carrier ∧ Set.EqOn f.invFun g.invFun Y.carrier

theorem SAHom.rel_equivalence {X Y : SemialgSet R} : Equivalence (SAHom.rel (X := X) (Y := Y)) where
  refl _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  symm h := ⟨h.1.symm, h.2.symm⟩
  trans h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

instance SAHom.setoid (X Y : SemialgSet R) : Setoid (SAHom X Y) :=
  ⟨SAHom.rel, SAHom.rel_equivalence⟩

/-- The identity semialgebraic homeomorphism. -/
def SAHom.id (X : SemialgSet R) : SAHom X X :=
  ⟨_root_.id, _root_.id, IsSemialgebraicHomeomorphism.refl X.isSemialgebraic⟩

/-- Composition of semialgebraic homeomorphisms. -/
def SAHom.comp {X Y Z : SemialgSet R} (f : SAHom X Y) (g : SAHom Y Z) : SAHom X Z :=
  ⟨g.toFun ∘ f.toFun, f.invFun ∘ g.invFun, f.isHomeo.trans g.isHomeo⟩

/-- The inverse semialgebraic homeomorphism. -/
def SAHom.symm {X Y : SemialgSet R} (f : SAHom X Y) : SAHom Y X :=
  ⟨f.invFun, f.toFun, f.isHomeo.symm⟩

/-- **The groupoid of semialgebraic sets**: objects are semialgebraic sets of any ambient
dimension, morphisms are semialgebraic homeomorphisms up to agreement on the carrier. -/
instance : Groupoid (SemialgSet R) where
  Hom X Y := Quotient (SAHom.setoid X Y)
  id X := Quotient.mk _ (SAHom.id X)
  comp {X Y Z} f g :=
    Quotient.liftOn₂ f g (fun a b => Quotient.mk _ (a.comp b)) <| by
      rintro a₁ b₁ a₂ b₂ ha hb
      refine Quotient.sound ⟨fun x hx => ?_, fun z hz => ?_⟩
      · show b₁.toFun (a₁.toFun x) = b₂.toFun (a₂.toFun x)
        rw [ha.1 hx]; exact hb.1 (a₂.isHomeo.bijOn.mapsTo hx)
      · show a₁.invFun (b₁.invFun z) = a₂.invFun (b₂.invFun z)
        rw [hb.2 hz]; exact ha.2 (b₂.isHomeo.symm.bijOn.mapsTo hz)
  inv {X Y} f :=
    Quotient.liftOn f (fun a => Quotient.mk _ a.symm) <| by
      rintro a b h; exact Quotient.sound ⟨h.2, h.1⟩
  id_comp := by rintro X Y f; induction f using Quotient.inductionOn; rfl
  comp_id := by rintro X Y f; induction f using Quotient.inductionOn; rfl
  assoc := by
    rintro W X Y Z f g h
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    induction h using Quotient.inductionOn
    rfl
  inv_comp := by
    rintro X Y f
    induction f using Quotient.inductionOn with
    | _ a => exact Quotient.sound ⟨fun y hy => a.isHomeo.invOn.2 hy, fun y hy => a.isHomeo.invOn.2 hy⟩
  comp_inv := by
    rintro X Y f
    induction f using Quotient.inductionOn with
    | _ a => exact Quotient.sound ⟨fun x hx => a.isHomeo.invOn.1 hx, fun x hx => a.isHomeo.invOn.1 hx⟩

/-- **The isomorphism relation of the groupoid is exactly `SemialgHomeomorphic`.** Two semialgebraic
sets are isomorphic objects of the groupoid iff they are semialgebraically homeomorphic. -/
theorem semialgHomeomorphic_iff_isIsomorphic {X Y : SemialgSet R} :
    SemialgHomeomorphic X Y ↔ IsIsomorphic X Y := by
  rw [Groupoid.isIsomorphic_iff_nonempty_hom]
  constructor
  · rintro ⟨f, g, h⟩; exact ⟨Quotient.mk _ ⟨f, g, h⟩⟩
  · rintro ⟨q⟩
    induction q using Quotient.inductionOn with
    | _ a => exact ⟨a.toFun, a.invFun, a.isHomeo⟩

end Azurite.BPR
