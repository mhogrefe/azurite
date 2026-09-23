/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.EmbeddingExtension
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11
import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealClosedField
import Mathlib.FieldTheory.Extension

/-! # Artin–Schreier embedding extension (Stage 3 plumbing)

Building the order-preserving `F`-algebra embedding `R →ₐ[F] R'` between two real
closures, via a Zorn argument over order-preserving partial lifts.

This file currently provides the adapted single-element extension step:

* `exists_lift_of_root` — a variant of `IntermediateField.Lifts.exists_lift_of_splits'`
  that needs only **one root** of the mapped minimal polynomial (rather than full
  splitting), and additionally exposes that the new lift sends the adjoined
  element to that chosen root. This is what lets us extend a partial lift using
  the Thom-encoding root (`exists_unique_thom_root`), keeping order-preservation
  (`sign_preserved`).
-/

open Polynomial IntermediateField IntermediateField.Lifts

namespace Azurite.BPR

variable {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
/-- A lift `x : Lifts F E K` extends over an integral element `s` as soon as the
mapped minimal polynomial `(minpoly x.carrier s).map x.emb` has a **single root**
`β` in `K` — no full splitting needed. The extended lift sends `s` to `β`.

Adapted from `IntermediateField.Lifts.exists_lift_of_splits'`, whose only use of
the splitting hypothesis is to produce one root (`rootOfSplits`). -/
theorem exists_lift_of_root (x : Lifts F E K) {s : E} (h1 : IsIntegral x.carrier s)
    (β : K) (hβ : ((minpoly x.carrier s).map x.emb.toRingHom).IsRoot β) :
    ∃ y, x ≤ y ∧ ∃ hs : s ∈ y.carrier, y.emb ⟨s, hs⟩ = β ∧
      ∀ z : ↥y.carrier, (z : E) ∈ Algebra.adjoin x.carrier ({s} : Set E) := by
  let : Algebra x.carrier K := x.emb.toRingHom.toAlgebra
  let carrier := x.carrier⟮s⟯.restrictScalars F
  let : Algebra x.carrier carrier := x.carrier⟮s⟯.toSubalgebra.algebra
  let hts : IsScalarTower F x.carrier carrier := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let φ : carrier →ₐ[x.carrier] K := (algHomAdjoinIntegralEquiv x.carrier h1).symm
    ⟨β, by
      rw [mem_aroots, and_iff_right (minpoly.ne_zero h1), aeval_def, eval₂_eq_eval_map]
      exact hβ⟩
  have hφgen : φ (AdjoinSimple.gen x.carrier s) = β :=
    algHomAdjoinIntegralEquiv_symm_apply_gen x.carrier h1 _
  refine ⟨⟨carrier, (algHomEquivSigma (A := F) (B := x.carrier) (C := carrier) (D := K)).symm
      ⟨x.emb, φ⟩⟩,
    ⟨fun z hz ↦ IntermediateField.algebraMap_mem x.carrier⟮s⟯ ⟨z, hz⟩, φ.commutes⟩,
    mem_adjoin_simple_self x.carrier s, ?_, ?_⟩
  · show (φ.restrictScalars F) (AdjoinSimple.gen x.carrier s) = β
    exact hφgen
  · intro z
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic h1.isAlgebraic]
    exact z.2

/-- The lift's embedding applied to `q(s)` (built as `eval₂` along the inclusion)
equals `(q.map x.emb).eval (y.emb s)`. A ring-hom commutes with `eval₂`, and the
extension relation `y.emb ∘ inclusion = x.emb` collapses the coefficient map. -/
lemma emb_eval₂ {x y : Lifts F E K} (hxy : x ≤ y) {s : E} (hs : s ∈ y.carrier)
    (q : (↥x.carrier)[X]) :
    y.emb (eval₂ (inclusion hxy.1).toRingHom ⟨s, hs⟩ q)
      = (q.map x.emb.toRingHom).eval (y.emb ⟨s, hs⟩) := by
  have h := hom_eval₂ q (inclusion hxy.1).toRingHom y.emb.toRingHom ⟨s, hs⟩
  have hcomp : y.emb.toRingHom.comp (inclusion hxy.1).toRingHom = x.emb.toRingHom := by
    ext z; exact hxy.2 z
  rw [hcomp] at h
  rw [show y.emb (eval₂ (inclusion hxy.1).toRingHom ⟨s, hs⟩ q)
        = y.emb.toRingHom (eval₂ (inclusion hxy.1).toRingHom ⟨s, hs⟩ q) from rfl, h,
      eval₂_eq_eval_map]
  rfl

/-- The underlying value (in `E`) of the same `eval₂` element is `q(s)` evaluated
in `E` along the base algebra map. -/
lemma val_eval₂ {x y : Lifts F E K} (hxy : x ≤ y) {s : E} (hs : s ∈ y.carrier)
    (q : (↥x.carrier)[X]) :
    ((eval₂ (inclusion hxy.1).toRingHom ⟨s, hs⟩ q : ↥y.carrier) : E)
      = eval₂ (algebraMap (↥x.carrier) E) s q := by
  have h := hom_eval₂ q (inclusion hxy.1).toRingHom (y.carrier.val).toRingHom ⟨s, hs⟩
  rw [show ((eval₂ (inclusion hxy.1).toRingHom ⟨s, hs⟩ q : ↥y.carrier) : E)
        = (y.carrier.val).toRingHom (eval₂ (inclusion hxy.1).toRingHom ⟨s, hs⟩ q) from rfl, h]
  congr 1

end Azurite.BPR

namespace Azurite.BPR

open Azurite.BPR.Proposition2_27 IntermediateField.Lifts

variable {F R R' : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field R'] [LinearOrder R'] [IsStrictOrderedRing R']
    [Algebra F R] [Algebra F R']

/-- A lift `x : Lifts F R R'` is *sign-preserving* if its embedding preserves the
sign of every element (equivalently, is order-preserving — see
`StrictMono_of_signPreserving`). This is the Zorn invariant for the
Artin–Schreier embedding extension. -/
def SignPreserving (x : Lifts F R R') : Prop :=
  ∀ a : ↥x.carrier, SignType.sign (a : R) = SignType.sign (x.emb a)

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- A sign-preserving lift is strictly monotone. -/
lemma StrictMono_of_signPreserving {x : Lifts F R R'} (hx : SignPreserving x) :
    StrictMono x.emb := by
  intro a b hab
  have hsign := hx (b - a)
  have hcoe : ((b - a : ↥x.carrier) : R) = (b : R) - (a : R) := by push_cast; ring
  rw [hcoe, sign_pos (by exact_mod_cast sub_pos.mpr hab), map_sub] at hsign
  have : (0:R') < x.emb b - x.emb a := sign_eq_one_iff.mp hsign.symm
  linarith

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- **The single-element extension, preserving sign.** A sign-preserving lift `x`
extends to a sign-preserving lift `y` whose carrier contains any element `s`
integral over `x.carrier`. The image of `s` is the unique root of the mapped
minimal polynomial carrying `s`'s Thom encoding (`exists_unique_thom_root`); sign
preservation propagates by `sign_preserved`, since every element of `x.carrier⟮s⟯`
is a polynomial in `s`. -/
theorem signPreserving_ext
    (hR : HasIntermediateValueProperty R) (hR' : HasIntermediateValueProperty R')
    (x : Lifts F R R') (hx : SignPreserving x) (s : R) (hs_int : IsIntegral ↥x.carrier s) :
    ∃ y, x ≤ y ∧ s ∈ y.carrier ∧ SignPreserving y := by
  have hιmono : StrictMono (algebraMap ↥x.carrier R) := fun a b h => h
  have hτmono : StrictMono x.emb.toRingHom := StrictMono_of_signPreserving hx
  set p := minpoly ↥x.carrier s with hp_def
  have hp : p ≠ 0 := minpoly.ne_zero hs_int
  have hα : (p.map (algebraMap ↥x.carrier R)).IsRoot s := by
    rw [Polynomial.IsRoot, eval_map]; exact minpoly.aeval _ _
  obtain ⟨β, hβ⟩ := exists_unique_thom_root hR hR' (algebraMap ↥x.carrier R) hιmono
    x.emb.toRingHom hτmono p hp s hα
  have hβroot : (p.map x.emb.toRingHom).IsRoot β := by
    have hmem : β ∈ derReali (p.map x.emb.toRingHom)
        (p.map (algebraMap ↥x.carrier R)).natDegree
        (thomEnc (p.map (algebraMap ↥x.carrier R)) s) := by rw [hβ]; rfl
    have h0 := hmem 0 (Nat.zero_le _)
    rw [Function.iterate_zero_apply] at h0
    have hz : thomEnc (p.map (algebraMap ↥x.carrier R)) s 0 = 0 := by
      simp [thomEnc, hα.eq_zero]
    rw [hz] at h0
    exact sign_eq_zero_iff.mp h0
  obtain ⟨y, hxy, hs_mem, hys, hadjoin⟩ := exists_lift_of_root x hs_int β hβroot
  refine ⟨y, hxy, hs_mem, fun a => ?_⟩
  have haval := hadjoin a
  rw [Algebra.adjoin_singleton_eq_range_aeval] at haval
  obtain ⟨q, hq⟩ := haval
  have ha_eq : a = eval₂ (inclusion hxy.1).toRingHom ⟨s, hs_mem⟩ q := by
    apply Subtype.ext; rw [val_eval₂ hxy, ← hq]; rfl
  rw [ha_eq, val_eval₂ hxy, emb_eval₂ hxy, hys, ← eval_map]
  exact sign_preserved hR hR' (algebraMap ↥x.carrier R) hιmono x.emb.toRingHom hτmono
    p hp s hα β hβ q

omit [IsStrictOrderedRing F] [IsStrictOrderedRing R] [IsStrictOrderedRing R'] in
/-- The bottom lift (carrier `⊥ ≅ F`, embedding `τ`) is sign-preserving, provided
the base maps `F → R` and `F → R'` are order-preserving. -/
theorem signPreserving_bot (hιF : StrictMono (algebraMap F R))
    (hτF : StrictMono (algebraMap F R')) : SignPreserving (⊥ : Lifts F R R') := by
  intro a
  obtain ⟨f, rfl⟩ := (botEquiv F R).symm.surjective a
  show SignType.sign (((botEquiv F R).symm f : ↥(⊥ : IntermediateField F R)) : R)
     = SignType.sign ((⊥ : Lifts F R R').emb ((botEquiv F R).symm f))
  rw [show (⊥ : Lifts F R R').emb = (Algebra.ofId F R').comp (botEquiv F R) from rfl]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  rw [show (((botEquiv F R).symm f : ↥(⊥ : IntermediateField F R)) : R) = algebraMap F R f from by
        simp [IntermediateField.botEquiv_symm],
    show (Algebra.ofId F R') f = algebraMap F R' f from rfl, hιF.sign_comp, hτF.sign_comp]

omit [LinearOrder F] [IsStrictOrderedRing F] [IsStrictOrderedRing R] [IsStrictOrderedRing R'] in
/-- A chain of sign-preserving lifts has a sign-preserving union. -/
theorem signPreserving_union {c : Set (Lifts F R R')} (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) (hsp : ∀ i ∈ c, SignPreserving i) : SignPreserving (union c hc) := by
  have : Nonempty ↥c := hne.to_subtype
  intro w
  have hmem : (w : R) ∈ ⨆ i : c, i.1.carrier := by rw [← carrier_union]; exact w.2
  have hdir : Directed (· ≤ ·) (fun i : c => i.1.carrier) :=
    hc.directedOn.directed_val.mono_comp _ fun _ _ h ↦ h.1
  rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion] at hmem
  obtain ⟨i, hi⟩ := hmem
  rw [SetLike.mem_coe] at hi
  obtain ⟨hle, hext⟩ := le_union c hc i.2
  have key : (union c hc).emb w = i.1.emb ⟨(w : R), hi⟩ := by
    rw [← hext ⟨(w : R), hi⟩]; congr 1
  rw [key]
  exact hsp i.1 i.2 ⟨(w : R), hi⟩

omit [IsStrictOrderedRing F] in
/-- **Artin–Schreier embedding extension.** If `R` is algebraic over the ordered
field `F` (embedded order-preservingly into `R` and into `R'`, both with the
intermediate value property), there is an `F`-algebra embedding `R →ₐ[F] R'`.

Zorn's lemma over sign-preserving partial lifts: the bottom lift `⊥ ≅ F` is
sign-preserving (`signPreserving_bot`), chains have sign-preserving unions
(`signPreserving_union`), and any proper sign-preserving lift extends
(`signPreserving_ext`), so a maximal one has carrier `⊤ = R`. -/
theorem exists_algHom
    (hR : HasIntermediateValueProperty R) (hR' : HasIntermediateValueProperty R')
    (halg : Algebra.IsAlgebraic F R)
    (hιF : StrictMono (algebraMap F R)) (hτF : StrictMono (algebraMap F R')) :
    Nonempty (R →ₐ[F] R') := by
  obtain ⟨m, hm_sp, hm_max⟩ := zorn_le₀ {x : Lifts F R R' | SignPreserving x}
    (fun cc hsub hchain => by
      rcases cc.eq_empty_or_nonempty with rfl | hne
      · exact ⟨⊥, signPreserving_bot hιF hτF, fun z hz => absurd hz (Set.notMem_empty z)⟩
      · exact ⟨union cc hchain, signPreserving_union hchain hne hsub,
          fun z hz => le_union cc hchain hz⟩)
  have htop : m.carrier = ⊤ := by
    by_contra hnt
    obtain ⟨s, hs⟩ : ∃ s : R, s ∉ m.carrier := by
      by_contra h; push Not at h; exact hnt (top_unique fun x _ => h x)
    have hs_int : IsIntegral ↥m.carrier s := (halg.isIntegral.isIntegral s).tower_top
    obtain ⟨y, hxy, hs_mem, hy_sp⟩ := signPreserving_ext hR hR' m hm_sp s hs_int
    rw [le_antisymm (hm_max hy_sp hxy) hxy] at hs_mem
    exact hs hs_mem
  exact ⟨m.emb.comp ((IntermediateField.equivOfEq htop).symm.toAlgHom.comp
    (IntermediateField.topEquiv).symm.toAlgHom)⟩

omit [IsStrictOrderedRing F] in
/-- **Uniqueness of the real closure.** Two real closures of the ordered field `F`
— real closed (here: with the intermediate value property) fields, algebraic over
`F`, with order-preserving embeddings of `F` — are `F`-algebra isomorphic.

Apply `exists_algHom` in both directions to get `φ : R →ₐ[F] R'` and `ψ : R' →ₐ[F] R`;
then `φ ∘ ψ` is an endomorphism of the algebraic extension `R'`, hence bijective, so
`φ` is surjective, and being a field homomorphism it is injective — an isomorphism.
(The isomorphism is automatically order-preserving, as any field homomorphism between
real closed fields preserves squares, hence the order.) -/
theorem realClosure_equiv
    (hR : HasIntermediateValueProperty R) (hR' : HasIntermediateValueProperty R')
    (halg : Algebra.IsAlgebraic F R) (halg' : Algebra.IsAlgebraic F R')
    (hιF : StrictMono (algebraMap F R)) (hτF : StrictMono (algebraMap F R')) :
    Nonempty (R ≃ₐ[F] R') := by
  obtain ⟨φ⟩ := exists_algHom hR hR' halg hιF hτF
  obtain ⟨ψ⟩ := exists_algHom hR' hR halg' hτF hιF
  have hφψ : Function.Bijective (φ.comp ψ) := halg'.algHom_bijective _
  have hφ_surj : Function.Surjective φ := Function.Surjective.of_comp hφψ.2
  exact ⟨AlgEquiv.ofBijective φ ⟨φ.injective, hφ_surj⟩⟩

end Azurite.BPR

namespace Azurite.BPR

open Azurite.BPR.Theorem2_11

/-- If the order of a real closed field `S` extends `F`'s order in the sense that
every nonnegative element of `F` maps to a square (`= nonnegative`) in `S`, then
the structure map `F → S` is strictly monotone. -/
private lemma strictMono_algebraMap_of_isSquare
    {F S : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field S] [LinearOrder S] [IsStrictOrderedRing S] [Algebra F S] [IsRealClosed S]
    (hext : ∀ p : F, 0 ≤ p → IsSquare (algebraMap F S p)) :
    StrictMono (algebraMap F S) := by
  intro a b hab
  have hnn : (0 : S) ≤ algebraMap F S (b - a) :=
    IsRealClosed.nonneg_iff_isSquare.mpr (hext (b - a) (by linarith))
  rw [map_sub] at hnn
  exact lt_of_le_of_ne (by linarith)
    ((FaithfulSMul.algebraMap_injective F S).ne (ne_of_lt hab))

/-- **Uniqueness of the real closure (BPR Section 2.1).** Let `F` be an ordered
field. A *real closure* of `F` is a real closed field, algebraic over `F`, whose
order extends that of `F` (every nonnegative `p ∈ F` becomes a square). Any two
real closures of `F` are isomorphic as `F`-algebras (and the isomorphism is
automatically order-preserving).

This is the `IsRealClosed`-stated form of `realClosure_equiv`: real-closedness
supplies the intermediate value property (`theorem_2_11_b_c`) and the canonical
order (`IsRealClosed.toLinearOrder`), and the square hypothesis supplies the
order-preservation of `F`'s embedding. -/
theorem realClosure_unique
    {F R R' : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field R] [IsRealClosed R] [Field R'] [IsRealClosed R']
    [Algebra F R] [Algebra F R']
    (halg : Algebra.IsAlgebraic F R) (halg' : Algebra.IsAlgebraic F R')
    (hR_ext : ∀ p : F, 0 ≤ p → IsSquare (algebraMap F R p))
    (hR'_ext : ∀ p : F, 0 ≤ p → IsSquare (algebraMap F R' p)) :
    Nonempty (R ≃ₐ[F] R') := by
  let : LinearOrder R := IsRealClosed.toLinearOrder
  have : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  have : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  have : IsAlgClosed (Ri R) := isAlgClosed_Ri
  let : LinearOrder R' := IsRealClosed.toLinearOrder
  have : IsOrderedRing R' := IsRealClosed.toIsOrderedRing
  have : IsStrictOrderedRing R' := IsOrderedRing.toIsStrictOrderedRing R'
  have : IsAlgClosed (Ri R') := isAlgClosed_Ri
  exact realClosure_equiv theorem_2_11_b_c theorem_2_11_b_c halg halg'
    (strictMono_algebraMap_of_isSquare hR_ext) (strictMono_algebraMap_of_isSquare hR'_ext)

end Azurite.BPR
