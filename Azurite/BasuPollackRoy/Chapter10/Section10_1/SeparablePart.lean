import Azurite.BasuPollackRoy.Chapter10.Section10_1.NormLengthMeasure
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_a_b

/-!
# BPR §10.1: the separable part

The *separable part* of `P` is a separable polynomial with the same set of
roots as `P` in `C`; it is unique up to a multiplicative constant.

Formalized as the predicate `IsSeparablePart S P` (separability plus equality
of the root *sets*, i.e. of the deduplicated root multisets), with the
canonical monic witness

  `separablePart P = ∏_{z ∈ distinct roots of P} (X − z)`

(`separablePart_isSeparablePart`; over the algebraically closed `C` this
product is separable since its roots are distinct by construction —
`nodup_roots_iff_of_splits`). Uniqueness (`isSeparablePart_unique`) comes
through the normal form `IsSeparablePart.eq_C_leadingCoeff_mul`: any
separable part equals its leading coefficient times the canonical one,
because a separable polynomial splits into distinct linear factors indexed
exactly by the common root set.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- `S` is a **separable part** of `P`: `S` is separable and has the same set
of roots as `P` in `C`. -/
def IsSeparablePart (S P : Polynomial (Ri R)) : Prop :=
  S.Separable ∧ S.roots.toFinset = P.roots.toFinset

/-- The canonical separable part: the monic product of `X − z` over the
distinct roots of `P`. -/
noncomputable def separablePart (P : Polynomial (Ri R)) : Polynomial (Ri R) :=
  (P.roots.toFinset.val.map (fun z => X - C z)).prod

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem separablePart_monic (P : Polynomial (Ri R)) : (separablePart P).Monic :=
  monic_multiset_prod_of_monic _ _ (fun z _ => monic_X_sub_C z)

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem roots_separablePart (P : Polynomial (Ri R)) :
    (separablePart P).roots = P.roots.toFinset.val := by
  rw [separablePart, Polynomial.roots_multiset_prod_X_sub_C]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **Existence.** The canonical separable part is one. -/
theorem separablePart_isSeparablePart (P : Polynomial (Ri R)) :
    IsSeparablePart (separablePart P) P := by
  have : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  constructor
  · rw [← Polynomial.nodup_roots_iff_of_splits (separablePart_monic P).ne_zero
      (IsAlgClosed.splits _), roots_separablePart]
    exact P.roots.toFinset.nodup
  · rw [roots_separablePart, Finset.val_toFinset]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **Normal form.** Any separable part of `P` equals its leading coefficient
times the canonical one: a separable polynomial splits into distinct linear
factors, indexed by the common root set. -/
theorem IsSeparablePart.eq_C_leadingCoeff_mul {S P : Polynomial (Ri R)}
    (hS : IsSeparablePart S P) : S = C S.leadingCoeff * separablePart P := by
  have : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  have hcard : S.roots.card = S.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroots : S.roots = P.roots.toFinset.val := by
    have hnodup : S.roots.Nodup := Polynomial.nodup_roots hS.1
    calc S.roots = S.roots.toFinset.val := by
          rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
      _ = P.roots.toFinset.val := by rw [hS.2]
  calc S = C S.leadingCoeff * (S.roots.map (fun z => X - C z)).prod :=
        (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard).symm
    _ = C S.leadingCoeff * separablePart P := by rw [hroots, separablePart]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Being a separable part is invariant under nonzero constant multiples. -/
theorem IsSeparablePart.C_mul_left {S P : Polynomial (Ri R)} {c : Ri R} (hc : c ≠ 0)
    (hS : IsSeparablePart S P) : IsSeparablePart (C c * S) P := by
  have : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  have hS0 : S ≠ 0 := hS.1.ne_zero
  have hroots : (C c * S).roots = S.roots := Polynomial.roots_C_mul _ hc
  constructor
  · rw [← Polynomial.nodup_roots_iff_of_splits
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hS0) (IsAlgClosed.splits _), hroots]
    exact Polynomial.nodup_roots hS.1
  · rw [hroots]
    exact hS.2

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **Uniqueness.** The separable part of `P` is unique up to a
multiplicative constant. -/
theorem isSeparablePart_unique {S₁ S₂ P : Polynomial (Ri R)}
    (h₁ : IsSeparablePart S₁ P) (h₂ : IsSeparablePart S₂ P) :
    ∃ c : Ri R, c ≠ 0 ∧ S₁ = C c * S₂ := by
  set c₁ := S₁.leadingCoeff with hc₁
  set c₂ := S₂.leadingCoeff with hc₂
  have hlc₁ : c₁ ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr h₁.1.ne_zero
  have hlc₂ : c₂ ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr h₂.1.ne_zero
  have e₁ : S₁ = C c₁ * separablePart P := h₁.eq_C_leadingCoeff_mul
  have e₂ : S₂ = C c₂ * separablePart P := h₂.eq_C_leadingCoeff_mul
  refine ⟨c₁ * c₂⁻¹, mul_ne_zero hlc₁ (inv_ne_zero hlc₂), ?_⟩
  rw [e₁, e₂, ← mul_assoc, ← Polynomial.C_mul]
  congr 2
  field_simp

end Azurite.BPR
