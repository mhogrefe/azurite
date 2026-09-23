/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Equiv.ComposedOps

/-!
# Superset correctness of coefficient elimination

`eliminateCoeffs Ps` runs an iterated resultant cascade whose output should
cover, for every choice of roots `cᵢ` of the defining polynomials `Pᵢ`, all
roots of `F = ∑ cᵢ xⁱ`. This file proves that superset property
(`isRoot_eliminateCoeffs_map`): for `f : R →+* K` into **any field** (no
algebraic closure is needed — the containment direction of the resultant
theory is unconditional), if each `f` survives the leading coefficients and
`z` makes the Horner value `∑ cᵢ zⁱ` vanish, then `z` is a root of the mapped
`eliminateCoeffs Ps`.

The proof is a downward induction along the cascade:

* **`Polynomial.resultant_eq_zero_of_isRoot_isRoot`** — the key new
  root-level fact: a *pinned* resultant vanishes on a common root even when
  the pinned sizes strictly exceed the true degrees (mapping coefficients can
  only lower degrees, and the Sylvester determinant does not care). Proved by
  peeling the pinned sizes down with `resultant_add_left_deg`/
  `resultant_add_right_deg` and applying `resultant_eq_zero_iff` at the true
  degrees.
* **`isRoot_composedSum_map_of`** — the superset half of the composed-sum
  correctness over any field: `a + b` is a root of the mapped
  `composedSum P Q` whenever `a`, `b` are roots of the mapped `P`, `Q`. Only
  `P`'s leading coefficient must survive `f`; `Q` is unconstrained (a
  degenerate `Q` only enlarges the root set). Proved generically, so that the
  cascade step can *apply* it at the coefficient ring `AzPolynomial R` —
  instantiating rather than re-unfolding keeps the nested instances opaque.
* **`isRoot_cascade_step` / `isRoot_cascade_fold`** — one step of the fold
  tracks the Horner value `c + z·v` (via `isRoot_map_toPoly_scaleRoots_of`,
  the generic form of scaling roots by a ring element seen through `f`), and
  `List.Forall₂` induction carries it along the whole cascade.
-/

set_option autoImplicit false

open Polynomial

/-- Two polynomials with a common root are not coprime. -/
theorem Polynomial.not_isCoprime_of_isRoot_isRoot {K : Type _} [CommRing K] [Nontrivial K]
    {p q : K[X]} {a : K} (hpa : p.IsRoot a) (hqa : q.IsRoot a) :
    ¬IsCoprime p q := by
  rintro ⟨u, v, huv⟩
  have h := congrArg (Polynomial.eval a) huv
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_one,
    hpa, hqa, mul_zero, mul_zero, add_zero] at h
  exact zero_ne_one h

/-- **Pinned resultants vanish on common roots.** If `p` and `q` share a root
and the pinned sizes dominate the degrees (with a nonempty matrix), the
resultant vanishes — even when the pinned sizes strictly exceed the true
degrees, the situation after mapping coefficients along a ring homomorphism. -/
theorem Polynomial.resultant_eq_zero_of_isRoot_isRoot {K : Type _} [Field K]
    {p q : K[X]} {m n : ℕ} (hmn : 0 < m + n)
    (hpm : p.natDegree ≤ m) (hqn : q.natDegree ≤ n)
    {a : K} (hpa : p.IsRoot a) (hqa : q.IsRoot a) :
    Polynomial.resultant p q m n = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [Polynomial.resultant_zero_left]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hq0 : q.coeff 0 = 0 := by
        have hC := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hqn)
        rw [hC, Polynomial.IsRoot, Polynomial.eval_C] at hqa
        exact hqa
      rw [hq0, pow_zero, one_mul, zero_pow (by omega : m ≠ 0)]
    · rw [zero_pow (by omega : n ≠ 0), zero_mul]
  · rcases eq_or_ne q 0 with rfl | hq
    · rw [Polynomial.resultant_zero_right]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exfalso
        have hC := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hpm)
        rw [hC, Polynomial.IsRoot, Polynomial.eval_C] at hpa
        exact hp (by rw [hC, hpa, Polynomial.C_0])
      · rw [zero_pow (by omega : m ≠ 0), zero_mul]
    · -- both nonzero: peel the pinned sizes down to the true degrees
      obtain ⟨k, rfl⟩ : ∃ k, m = p.natDegree + k := ⟨m - p.natDegree, by omega⟩
      obtain ⟨l, rfl⟩ : ∃ l, n = q.natDegree + l := ⟨n - q.natDegree, by omega⟩
      rw [Polynomial.resultant_add_left_deg _ _ _ _ _ le_rfl,
        Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl,
        show Polynomial.resultant p q p.natDegree q.natDegree = Polynomial.resultant p q from rfl,
        Polynomial.resultant_eq_zero_iff.mpr
          ⟨Or.inl hp, Polynomial.not_isCoprime_of_isRoot_isRoot hpa hqa⟩]
      simp

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] {K : Type _} [Field K]

/-- Scaling roots by a ring element `s`, seen through `f`: if `v` is a root of
the mapped `Q`, then `f s · v` is a root of the mapped `scaleRoots Q s 1`. -/
theorem isRoot_map_toPoly_scaleRoots_of (f : R →+* K) (s : R) (Q : AzPolynomial R)
    {v : K} (hv : Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly Q)) v) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (scaleRoots Q s 1))) (f s * v) := by
  rw [Polynomial.IsRoot, toPoly_scaleRoots, Polynomial.C_1, one_mul, Polynomial.comp_X,
    Polynomial.eval_map,
    Polynomial.scaleRoots_eval₂_mul (p := AzPolynomial.toPoly Q) f v s,
    ← Polynomial.eval_map]
  rw [Polynomial.IsRoot] at hv
  rw [hv, mul_zero]

variable [IsDomain R] [Azurite.ExactDiv R]

/-- **Superset half of the composed-sum correctness, over any field** (no
algebraic closure): if `a` is a root of the mapped `P` and `b` of the mapped
`Q`, then `a + b` is a root of the mapped `composedSum P Q`. Only `P`'s
leading coefficient must survive `f`; `Q` is unconstrained. -/
theorem isRoot_composedSum_map_of (f : R →+* K) (P Q : AzPolynomial R)
    (hfP : f P.leadingCoeff ≠ 0)
    {a b : K} (ha : Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly P)) a)
    (hb : Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly Q)) b) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (composedSum P Q))) (a + b) := by
  have hPne : P ≠ 0 := fun h => hfP (by
    rw [h, show (0 : AzPolynomial R).leadingCoeff = 0 from rfl, map_zero])
  have hdP : 0 < P.natDegree := by
    by_contra h0
    have hC := Polynomial.eq_C_of_natDegree_eq_zero
      (show (AzPolynomial.toPoly P).natDegree = 0 by
        rw [AzPolynomial.natDegree_toPoly]; omega)
    rw [hC, Polynomial.map_C, Polynomial.IsRoot, Polynomial.eval_C] at ha
    exact hfP (by
      rw [show P.leadingCoeff = P.coeff P.natDegree from rfl,
        show P.natDegree = 0 by omega, ← AzPolynomial.coeff_toPoly]
      exact ha)
  have hPYne : AzPolynomial.toPoly (P.map (CRingHom : R →+* AzPolynomial R)) ≠ 0 := by
    intro h
    exact hPne ((map_eq_zero_iff_of_injective CRingHom CRingHom_injective P).mp
      (toPoly_inj.mp (h.trans toPoly_zero.symm)))
  have hmapdegP : (P.map (CRingHom : R →+* AzPolynomial R)).natDegree = P.natDegree :=
    natDegree_map_of_injective CRingHom CRingHom_injective P
  have hmapdegQ : (Q.map (CRingHom : R →+* AzPolynomial R)).natDegree = Q.natDegree :=
    natDegree_map_of_injective CRingHom CRingHom_injective Q
  show Polynomial.eval (a + b) (Polynomial.map f (AzPolynomial.toPoly (composedSum P Q))) = 0
  rw [← evalMapHom_apply f (a + b)]
  rw [show composedSum P Q
      = resultant (P.map CRingHom) ((negateRoots (Q.map CRingHom)).translate X) from rfl,
    resultant_eq _ _ hPYne, Azurite.BPR.Chapter4.Res_eq_resultant,
    ← Polynomial.resultant_map_map]
  rw [map_evalMapHom_toPoly_map_CRingHom f (a + b) P,
    map_evalMapHom_toPoly_sumArg f (a + b) Q]
  apply Polynomial.resultant_eq_zero_of_isRoot_isRoot (a := a)
  · rw [AzPolynomial.natDegree_toPoly, hmapdegP]
    omega
  · calc (Polynomial.map f (AzPolynomial.toPoly P)).natDegree
        ≤ (AzPolynomial.toPoly P).natDegree := Polynomial.natDegree_map_le
      _ = P.natDegree := AzPolynomial.natDegree_toPoly P
      _ = _ := by rw [AzPolynomial.natDegree_toPoly, hmapdegP]
  · calc ((Polynomial.map f (AzPolynomial.toPoly Q)).comp
          (Polynomial.C (a + b) - Polynomial.X)).natDegree
        ≤ (Polynomial.map f (AzPolynomial.toPoly Q)).natDegree
            * (Polynomial.C (a + b) - Polynomial.X).natDegree :=
          Polynomial.natDegree_comp_le
      _ ≤ (AzPolynomial.toPoly Q).natDegree * 1 := by
          apply Nat.mul_le_mul Polynomial.natDegree_map_le
          rw [show (Polynomial.C (a + b) - Polynomial.X : K[X])
              = -(Polynomial.X - Polynomial.C (a + b)) by ring,
            Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
      _ = Q.natDegree := by rw [mul_one, AzPolynomial.natDegree_toPoly]
      _ ≤ _ := by
          rw [AzPolynomial.natDegree_toPoly, natDegree_translate, natDegree_negateRoots,
            hmapdegQ]
  · exact ha
  · rw [Polynomial.IsRoot, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X, show a + b - a = b by ring]
    exact hb

/-- **Cascade step.** One step of the elimination fold: if `c` is a root of
the mapped defining polynomial and `v` a root of the evaluated accumulator,
then the next Horner value `c + z·v` is a root of the evaluated next
accumulator. A pure instantiation of `isRoot_composedSum_map_of` at the
coefficient ring `AzPolynomial R`. -/
theorem isRoot_cascade_step (f : R →+* K) (z : K) (P : AzPolynomial R)
    (A : AzPolynomial (AzPolynomial R)) (hfP : f P.leadingCoeff ≠ 0)
    {c v : K} (hc : Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly P)) c)
    (hv : Polynomial.IsRoot (Polynomial.map (evalMapHom f z) (AzPolynomial.toPoly A)) v) :
    Polynomial.IsRoot
      (Polynomial.map (evalMapHom f z)
        (AzPolynomial.toPoly (composedSum (P.map CRingHom) (scaleRoots A X 1)))) (c + z * v) := by
  have hd1 : (P.map (CRingHom : R →+* AzPolynomial R)).natDegree = P.natDegree :=
    natDegree_map_of_injective CRingHom CRingHom_injective P
  have hlc : (evalMapHom f z) ((P.map (CRingHom : R →+* AzPolynomial R)).leadingCoeff) ≠ 0 := by
    rw [show (P.map (CRingHom : R →+* AzPolynomial R)).leadingCoeff
        = (P.map CRingHom).coeff ((P.map CRingHom).natDegree) from rfl, hd1, coeff_map',
      CRingHom_apply, evalMapHom_apply, toPoly_C, Polynomial.map_C, Polynomial.eval_C]
    exact hfP
  have ha : Polynomial.IsRoot
      (Polynomial.map (evalMapHom f z) (AzPolynomial.toPoly (P.map CRingHom))) c := by
    rw [map_evalMapHom_toPoly_map_CRingHom]
    exact hc
  have hb := isRoot_map_toPoly_scaleRoots_of (evalMapHom f z) (X : AzPolynomial R) A hv
  rw [evalMapHom_X] at hb
  exact isRoot_composedSum_map_of (evalMapHom f z) (P.map CRingHom) (scaleRoots A X 1)
    hlc ha hb

/-- **Cascade fold.** `List.Forall₂` induction carries the Horner value along
the whole elimination fold. -/
theorem isRoot_cascade_fold (f : R →+* K) (z : K)
    {rest : List (AzPolynomial R)} {csr : List K}
    (hpairs : List.Forall₂ (fun P c => f P.leadingCoeff ≠ 0 ∧
      Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly P)) c) rest csr)
    (A : AzPolynomial (AzPolynomial R)) (v : K)
    (hv : Polynomial.IsRoot (Polynomial.map (evalMapHom f z) (AzPolynomial.toPoly A)) v) :
    Polynomial.IsRoot
      (Polynomial.map (evalMapHom f z)
        (AzPolynomial.toPoly (rest.foldl
          (fun B Pk => composedSum (Pk.map CRingHom) (scaleRoots B X 1)) A)))
      (csr.foldl (fun acc c => c + z * acc) v) := by
  induction hpairs generalizing A v with
  | nil => exact hv
  | cons hPc _ ih =>
    exact ih _ _ (isRoot_cascade_step f z _ A hPc.1 hPc.2 hv)

/-- **Superset correctness of `eliminateCoeffs`.** Let `f : R →+* K` map an
integral domain with exact division into any field, let `cs` pair with `Ps`
so that each `cᵢ` is a root of the mapped `Pᵢ` and `f` does not kill the
leading coefficient of any `Pᵢ` (all automatic for the inclusion of `ℤ` into
`ℂ` or `ℝ`), and let `z` be a root of `F = ∑ cᵢ xⁱ` — phrased as its Horner
value: `cs.foldr (fun c acc => c + z * acc) 0 = 0`. Then `z` is a root of
the mapped `eliminateCoeffs Ps`. -/
theorem isRoot_eliminateCoeffs_map (f : R →+* K) {Ps : List (AzPolynomial R)} {cs : List K}
    (hpairs : List.Forall₂ (fun P c => f P.leadingCoeff ≠ 0 ∧
      Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly P)) c) Ps cs)
    (z : K) (hF : cs.foldr (fun c acc => c + z * acc) 0 = 0) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (eliminateCoeffs Ps))) z := by
  have hrev := List.forall₂_reverse_iff.mpr hpairs
  rw [← List.foldl_reverse] at hF
  unfold eliminateCoeffs
  cases hPsrev : Ps.reverse with
  | nil =>
    simp [toPoly_zero]
  | cons Pn rest =>
    rw [hPsrev] at hrev
    obtain ⟨cn, csr, hPc, hrest, hcsrev⟩ := List.forall₂_cons_left_iff.mp hrev
    rw [hcsrev] at hF
    simp only [List.foldl_cons, mul_zero, add_zero] at hF
    have hbase : Polynomial.IsRoot
        (Polynomial.map (evalMapHom f z) (AzPolynomial.toPoly (Pn.map CRingHom))) cn := by
      rw [map_evalMapHom_toPoly_map_CRingHom]
      exact hPc.2
    have hfold := isRoot_cascade_fold f z hrest (Pn.map CRingHom) cn hbase
    rw [hF] at hfold
    show Polynomial.eval z (Polynomial.map f (AzPolynomial.toPoly _)) = 0
    calc Polynomial.eval z (Polynomial.map f (AzPolynomial.toPoly
            ((rest.foldl (fun B Pk => composedSum (Pk.map CRingHom) (scaleRoots B X 1))
              (Pn.map CRingHom)).coeff 0)))
        = (evalMapHom f z) ((rest.foldl
            (fun B Pk => composedSum (Pk.map CRingHom) (scaleRoots B X 1))
            (Pn.map CRingHom)).coeff 0) := rfl
      _ = (Polynomial.map (evalMapHom f z) (AzPolynomial.toPoly
            (rest.foldl (fun B Pk => composedSum (Pk.map CRingHom) (scaleRoots B X 1))
              (Pn.map CRingHom)))).coeff 0 := by
          rw [Polynomial.coeff_map, AzPolynomial.coeff_toPoly]
      _ = Polynomial.eval 0 (Polynomial.map (evalMapHom f z) (AzPolynomial.toPoly
            (rest.foldl (fun B Pk => composedSum (Pk.map CRingHom) (scaleRoots B X 1))
              (Pn.map CRingHom)))) := by
          rw [← Polynomial.coeff_zero_eq_eval_zero]
      _ = 0 := hfold

end Azurite.AzPolynomial
