/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_3.Proposition_4_49
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Proposition_4_9
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Theorem_4_34
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_26
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# BPR Proposition 4.50: an algebraic proof that a symmetric matrix has real eigenvalues

Let `M` be a symmetric matrix with entries in a real closed field `R`. Then the
eigenvalues of `M` lie in `R`, i.e. the characteristic polynomial of `M` splits over `R`.

This is BPR's *algebraic* proof of (part of) Theorem 4.43, independent of the spectral
theorem. The number of roots of `CharPol(M)` in `R` is `p − k` (Proposition 4.49 forces
the subdiscriminants into a staircase, and Theorem 4.34 counts real roots as
`PmV(sDisc…)`), while the number of *distinct* roots in the algebraic closure is also
`p − k` (Proposition 4.26, via `deg gcd(CharPol(M), CharPol(M)')`). The two counts agree,
so every root is real.

The bridge connecting the matrix subdiscriminants `sDiscOfMatrix i M` (Proposition 4.49)
to the polynomial subdiscriminants `sDiscK (CharPol M) i` is the identity
`newtonSum (CharPol M) m = Tr(M^m)` (Newton sums of the characteristic polynomial are
traces of powers) together with Proposition 4.9 (`sDisc = det(Newton matrix)`).
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix
open Matrix Polynomial

section

variable {p : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-! ### (P1) Newton sums of the characteristic polynomial are traces of powers -/

/-- If `g - μ` is nilpotent on a finite free module, then `trace (g ^ m) = μ ^ m · finrank`.
(All eigenvalues of `g` are `μ`; the nilpotent part contributes nothing to the trace.) -/
private theorem trace_pow_eq_of_isNilpotent_sub {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] [Module.Free K M] [Module.Finite K M] (g : Module.End K M) (μ : K)
    (hg : IsNilpotent (g - algebraMap K (Module.End K M) μ)) (m : ℕ) :
    LinearMap.trace K M (g ^ m) = μ ^ m * (Module.finrank K M : K) := by
  induction m with
  | zero => simp [LinearMap.trace_one (R := K) (M := M)]
  | succ m ih =>
      have hcomm : Commute (g ^ m) g := (Commute.refl g).pow_left m
      rw [pow_succ, Module.End.mul_eq_comp,
        LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ hcomm hg, ih]
      ring

/-- **(P1) crux.** Over an algebraically closed field `K`, the `m`-th power sum of the
eigenvalues of `A` (the roots of its characteristic polynomial, with multiplicity) is the
trace of `A ^ m`. Equivalently, `(A ^ m).charpoly.roots = A.charpoly.roots.map (· ^ m)`. -/
theorem trace_pow_eq_sum_roots_pow {n : ℕ} {K : Type*} [Field K] [IsAlgClosed K]
    (A : Matrix (Fin n) (Fin n) K) (m : ℕ) :
    Matrix.trace (A ^ m) = (A.charpoly.roots.map (fun x => x ^ m)).sum := by
  classical
  -- Transport to the endomorphism `f := toLin' A` of `V := Fin n → K`.
  set f : Module.End K (Fin n → K) := Matrix.toLin' A with hf
  -- `trace (A ^ m) = trace (f ^ m)`.
  have htrace : Matrix.trace (A ^ m) = LinearMap.trace K (Fin n → K) (f ^ m) := by
    rw [← Matrix.trace_toLin'_eq (A ^ m), Matrix.toLin'_pow]
  -- The charpoly of `f` is the charpoly of `A`.
  have hcp : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  rw [htrace]
  -- The maximal generalized eigenspaces of `f` are independent and span everything.
  have hindep : iSupIndep f.maxGenEigenspace := f.independent_maxGenEigenspace
  have htop : ⨆ μ, f.maxGenEigenspace μ = ⊤ := Module.End.iSup_maxGenEigenspace_eq_top f
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep htop
  have hfin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hindep
  -- `f ^ m` maps each maximal generalized eigenspace into itself.
  have hmaps : ∀ μ, Set.MapsTo ⇑(f ^ m) ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right m) μ
  -- The trace decomposes over the eigenspaces.
  rw [LinearMap.trace_eq_sum_trace_restrict' hds hfin hmaps]
  -- On `E_μ`, the restriction of `f ^ m` is `(f|_{E_μ}) ^ m`, with `f|_{E_μ} - μ` nilpotent.
  have hsummand : ∀ μ ∈ hfin.toFinset,
      LinearMap.trace K (f.maxGenEigenspace μ) ((f ^ m).restrict (hmaps μ))
        = μ ^ m * (Module.finrank K (f.maxGenEigenspace μ) : K) := by
    intro μ _
    set hfμ := f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ with hhfμ
    rw [← Module.End.pow_restrict m hfμ]
    exact trace_pow_eq_of_isNilpotent_sub (f.restrict hfμ) μ
      (f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ) m
  rw [Finset.sum_congr rfl hsummand]
  -- The eigenspace dimension is the root multiplicity, so the index finset matches the roots.
  have hPne : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  have hdimroot : ∀ μ, (Module.finrank K (f.maxGenEigenspace μ) : K)
      = (A.charpoly.roots.count μ : K) := by
    intro μ
    rw [LinearMap.finrank_maxGenEigenspace_eq, hcp, ← Polynomial.count_roots]
  -- Rewrite the eigenvalue sum as a sum over the distinct roots.
  rw [Finset.sum_multiset_map_count]
  -- The two index finsets agree.
  have hset : hfin.toFinset = A.charpoly.roots.toFinset := by
    ext μ
    have hfc : Module.finrank K (f.maxGenEigenspace μ) = Multiset.count μ A.charpoly.roots := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hcp, ← Polynomial.count_roots]
    have key : f.maxGenEigenspace μ ≠ ⊥ ↔ Multiset.count μ A.charpoly.roots ≠ 0 := by
      rw [← hfc, ne_eq, ne_eq]
      exact not_congr (Submodule.finrank_eq_zero).symm
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Multiset.mem_toFinset, ← Multiset.count_pos,
      pos_iff_ne_zero, key]
  rw [hset]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [hdimroot, nsmul_eq_mul]
  ring

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **(P1).** `newtonSum (CharPol M) m = algebraMap R C (Tr (M ^ m))`, for `C` an
algebraically closed `R`-algebra (e.g. `AlgebraicClosure R`). -/
theorem newtonSum_charpoly_eq_trace {C : Type*} [Field C] [Algebra R C]
    [IsAlgClosed C] (M : Matrix (Fin p) (Fin p) R) (m : ℕ) :
    newtonSum (C := C) M.charpoly m = algebraMap R C (Matrix.trace (M ^ m)) := by
  classical
  set φ := algebraMap R C with hφ
  -- The mapped matrix and its charpoly.
  have hcharmap : (M.map φ).charpoly = M.charpoly.map φ := Matrix.charpoly_map M φ
  -- newtonSum unfolds to a sum over aroots, which are the roots of the mapped charpoly.
  unfold newtonSum
  rw [show (M.charpoly.aroots C) = (M.map φ).charpoly.roots from by
    rw [hcharmap, Polynomial.aroots]]
  -- trace (M^m) maps to trace of the mapped power.
  rw [AddMonoidHom.map_trace (φ : R →+* C) (M ^ m)]
  rw [Matrix.map_pow M φ]
  -- Apply the crux to the mapped matrix.
  rw [trace_pow_eq_sum_roots_pow (M.map φ) m]

/-! ### (P2) Matrix subdiscriminant equals polynomial subdiscriminant -/

omit [IsRealClosed R] in
/-- **(P2).** The `i`-th matrix subdiscriminant of `M` (a determinant of trace–Hankel
data) equals the `i`-th subdiscriminant `sDiscK` of the characteristic polynomial. -/
theorem sDiscOfMatrix_eq_sDiscK_charpoly [NeZero p]
    (M : Matrix (Fin p) (Fin p) R) (i : ℕ) (hi : i ≤ p) :
    sDiscOfMatrix i M = sDiscK M.charpoly i := by
  classical
  set C := AlgebraicClosure R
  set φ := algebraMap R C with hφ
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hdeg : M.charpoly.natDegree = p := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmonic : M.charpoly.Monic := M.charpoly_monic
  have hlc : M.charpoly.leadingCoeff = 1 := hmonic
  have hposdeg : 0 < M.charpoly.natDegree := by rw [hdeg]; exact hp
  -- Number of roots (with multiplicity) in C.
  have hcard : (M.charpoly.aroots C).card = p := by
    rw [IsAlgClosed.card_aroots_eq_natDegree, hdeg]
  -- Proposition 4.9 with k := p - i.
  have hk : (p - i) ≤ (M.charpoly.aroots C).card := by rw [hcard]; omega
  have h49 := proposition_4_9 (C := C) M.charpoly (p - i) hk
  rw [hcard] at h49
  rw [show p - (p - i) = i from by omega] at h49
  rw [hlc, map_one, one_pow, one_mul] at h49
  -- Identify the Newton matrix (over C) with the mapped trace–Hankel matrix.
  have hmat : (newtMat M.charpoly (p - i) : Matrix (Fin (p - i)) (Fin (p - i)) C)
      = (traceNewtMatrix i M).map φ := by
    apply Matrix.ext
    intro a b
    simp only [newtMat, Matrix.of_apply, traceNewtMatrix, Matrix.map_apply]
    rw [newtonSum_charpoly_eq_trace (C := C) M ((a : ℕ) + (b : ℕ))]
  rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h49
  -- So `sDisc M.charpoly i = φ (sDiscOfMatrix i M)`.
  rw [show (traceNewtMatrix i M).det = sDiscOfMatrix i M from rfl] at h49
  -- Remark 4.29: `φ (sDiscK M.charpoly i) = sDisc M.charpoly i`.
  have hr29 := Remark_4_29 (C := C) M.charpoly hposdeg i (by rw [hdeg]; exact hi)
  -- Combine: φ (sDiscK …) = sDisc … = φ (sDiscOfMatrix …); φ injective.
  have : φ (sDiscK M.charpoly i) = φ (sDiscOfMatrix i M) := by
    rw [hr29, h49]
  exact (FaithfulSMul.algebraMap_injective R C this).symm

/-! ### (P3) The real-root count is `p − k` -/

omit [IsRealClosed R] in
/-- **`PmV` of a positive block followed by zeros.** If `pos` is a nonempty list of
positive entries and `zeros` are all zero, then `PmV (pos ++ zeros) = pos.length − 1`
(every adjacent pair within `pos` is a sign permanence, the trailing zeros are skipped). -/
theorem pmv_pos_append_zeros :
    ∀ (pos zeros : List R), pos ≠ [] → (∀ x ∈ pos, 0 < x) → (∀ x ∈ zeros, x = 0) →
      PmV (pos ++ zeros) = (pos.length : ℤ) - 1
  | [], _, h, _, _ => absurd rfl h
  | [a], zeros, _, _, hz => by
      simp only [List.singleton_append, List.length_singleton]
      rw [PmV_cons_all_zero a zeros hz]; simp
  | a :: b :: rest, zeros, _, hpos, hz => by
      have hb : b ≠ 0 := ne_of_gt (hpos b (by simp))
      have hab : (0 : R) < a * b := mul_pos (hpos a (by simp)) (hpos b (by simp))
      have hIH := pmv_pos_append_zeros (b :: rest) zeros (by simp)
        (fun x hx => hpos x (List.mem_cons_of_mem a hx)) hz
      rw [List.cons_append, List.cons_append,
        PmV_cons_cons_ne a b (rest ++ zeros) hb, ← List.cons_append, hIH,
        sign_pos hab]
      simp

omit [IsRealClosed R] in
/-- **(P3).** `PmV (sDiscSeq M.charpoly) = p − k`. From Proposition 4.49 the matrix
subdiscriminants — equal to `sDiscK M.charpoly i` by (P2) — are positive for `k ≤ i ≤ p`
and zero for `i < k`, so `sDiscSeq` is `(p − k + 1)` positive entries followed by `k`
zeros. -/
private theorem pmv_sDiscSeq_eq [NeZero p] (M : Matrix (Fin p) (Fin p) R) (hM : M.IsSymm)
    {k : ℕ} (hk : k ≤ p - 1)
    (hpos : ∀ i, k ≤ i → i ≤ p - 1 → 0 < sDiscOfMatrix i M)
    (hzero : ∀ i, i < k → sDiscOfMatrix i M = 0) :
    PmV (sDiscSeq M.charpoly) = (p : ℤ) - k := by
  classical
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hdeg : M.charpoly.natDegree = p := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- The value of `sDiscK M.charpoly i` for `i ≤ p`.
  have hval : ∀ i, i ≤ p → sDiscK M.charpoly i = sDiscOfMatrix i M := by
    intro i hi; exact (sDiscOfMatrix_eq_sDiscK_charpoly M i hi).symm
  -- positivity of each `sDiscK` for `k ≤ i ≤ p`.
  have hposK : ∀ i, k ≤ i → i ≤ p → 0 < sDiscK M.charpoly i := by
    intro i hki hip
    rcases eq_or_lt_of_le hip with h | h
    · -- i = p : sDiscK = 1 directly from its definition.
      subst h
      rw [sDiscK, ite_eq_right (by rw [hdeg]; omega)]
      exact one_pos
    · rw [hval i hip]; exact hpos i hki (by omega)
  -- vanishing of each `sDiscK` for `i < k`.
  have hzeroK : ∀ i, i < k → sDiscK M.charpoly i = 0 := by
    intro i hik
    rw [hval i (by omega)]; exact hzero i hik
  -- Split `sDiscSeq` into a positive block of length `p-k+1` and `k` trailing zeros.
  set n := p - k + 1 with hn
  set f : ℕ → R := fun j => sDiscK M.charpoly (M.charpoly.natDegree - j) with hf
  have hsplit : sDiscSeq M.charpoly
      = (List.range n).map f ++ (List.range k).map (fun x => f (n + x)) := by
    rw [sDiscSeq, show M.charpoly.natDegree + 1 = n + k from by rw [hdeg]; omega,
      List.range_add, List.map_append, List.map_map]
    rfl
  rw [hsplit]
  have hposBlock : ∀ x ∈ (List.range n).map f, 0 < x := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [hf, hdeg]
    exact hposK (p - j) (by omega) (by omega)
  have hzeroBlock : ∀ x ∈ (List.range k).map (fun x => f (n + x)), x = 0 := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [hf, hdeg]
    exact hzeroK (p - (n + j)) (by omega)
  have hne : (List.range n).map f ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega
  rw [pmv_pos_append_zeros _ _ hne hposBlock hzeroBlock]
  simp only [List.length_map, List.length_range]
  push_cast [hn]
  omega

/-! ### (P4) The distinct-complex-root count is `p − k` -/

omit [IsRealClosed R] in
/-- **(P4) gcd step.** `deg gcd(CharPol(M), CharPol(M)') = k`. The signed subresultant
sequence of `(CharPol M, CharPol M')` is, up to the (unit) leading coefficient, the
subdiscriminant sequence; the staircase from Proposition 4.49 makes `sRes_i = 0` for
`i < k` and `sRes_k ≠ 0`, so Proposition 4.26 pins the gcd degree to `k`. -/
private theorem deg_gcd_charpoly_eq [NeZero p] (M : Matrix (Fin p) (Fin p) R) (_hM : M.IsSymm)
    {k : ℕ} (hk : k ≤ p - 1)
    (hpos : ∀ i, k ≤ i → i ≤ p - 1 → 0 < sDiscOfMatrix i M)
    (hzero : ∀ i, i < k → sDiscOfMatrix i M = 0) :
    (gcd M.charpoly M.charpoly.derivative).natDegree = k := by
  classical
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hdeg : M.charpoly.natDegree = p := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hposdeg : 0 < M.charpoly.natDegree := by rw [hdeg]; exact hp
  have hPne : M.charpoly ≠ 0 := fun h => by
    rw [h] at hposdeg; simp at hposdeg
  have hP'ne : M.charpoly.derivative ≠ 0 := fun h => by
    have := Polynomial.derivative_eq_zero.mp h; omega
  have hderdeg : M.charpoly.derivative.natDegree < M.charpoly.natDegree :=
    Polynomial.natDegree_derivative_lt (by omega)
  have hderdeg_eq : M.charpoly.derivative.natDegree = p - 1 := by
    have h := Polynomial.degree_derivative (p := M.charpoly) (by omega)
    rw [hdeg] at h
    exact Polynomial.natDegree_eq_of_degree_eq_some h
  have hder_q : k ≤ M.charpoly.derivative.natDegree := by
    rw [hderdeg_eq]; omega
  have hder_p : k < M.charpoly.natDegree := by rw [hdeg]; omega
  -- `sRes_i = sDiscK_i` (monic, leadingCoeff = 1).
  have hsres : ∀ i, i ≤ M.charpoly.natDegree →
      sRes M.charpoly M.charpoly.derivative i = sDiscK M.charpoly i := by
    intro i hi
    rw [sRes_eq_leadingCoeff_mul_sDiscK M.charpoly hderdeg hi, M.charpoly_monic, one_mul]
  rw [Proposition_4_26 M.charpoly M.charpoly.derivative hPne hP'ne k hder_q hder_p]
  refine ⟨?_, ?_⟩
  · intro i hik
    rw [hsres i (by omega), ← sDiscOfMatrix_eq_sDiscK_charpoly M i (by omega)]
    exact hzero i hik
  · rw [hsres k (by omega), ← sDiscOfMatrix_eq_sDiscK_charpoly M k (by omega)]
    rcases eq_or_lt_of_le hk with h | h
    · -- k = p - 1
      exact ne_of_gt (hpos k (le_refl k) (by omega))
    · exact ne_of_gt (hpos k (le_refl k) (by omega))

/-- Over a field of characteristic zero, each root `t` of `Q` contributes `mult_t − 1` to
`gcd Q Q'`: `rootMultiplicity t (gcd Q Q') = rootMultiplicity t Q − 1`. -/
private theorem rootMultiplicity_euclideanGcd_derivative {C : Type*} [Field C] [CharZero C]
    [DecidableEq C] {Q : Polynomial C} (hQ : Q ≠ 0) (t : C) :
    Polynomial.rootMultiplicity t (EuclideanDomain.gcd Q Q.derivative)
      = Polynomial.rootMultiplicity t Q - 1 := by
  set d := EuclideanDomain.gcd Q Q.derivative with hd
  have hdQ : d ∣ Q := EuclideanDomain.gcd_dvd_left Q Q.derivative
  have hdQ' : d ∣ Q.derivative := EuclideanDomain.gcd_dvd_right Q Q.derivative
  have hdne : d ≠ 0 := fun h => hQ (by simpa [h] using hdQ)
  by_cases ht : Q.IsRoot t
  · -- `t` is a root: `mult_t Q' = mult_t Q - 1`, so `mult_t (gcd) = min = mult_t Q - 1`.
    have hder : Polynomial.rootMultiplicity t Q.derivative = Polynomial.rootMultiplicity t Q - 1 :=
      Polynomial.derivative_rootMultiplicity_of_root ht
    have hQ'ne : Q.derivative ≠ 0 := by
      intro h
      have hdeg : Q.natDegree = 0 := Polynomial.derivative_eq_zero.mp h
      obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.1 hdeg
      simp only [Polynomial.IsRoot.def, Polynomial.eval_C] at ht
      exact hQ (by rw [ht, map_zero])
    refine le_antisymm ?_ ?_
    · -- `d ∣ Q'`, so `mult_t d ≤ mult_t Q' = mult_t Q - 1`.
      rw [← hder]
      exact Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hQ'ne hdQ' t
    · -- `(X - t)^(mult_t Q - 1)` divides both `Q` and `Q'`, hence `d`.
      rw [Polynomial.le_rootMultiplicity_iff hdne]
      refine EuclideanDomain.dvd_gcd ?_ ?_
      · exact dvd_trans (pow_dvd_pow _ (by omega)) (Polynomial.pow_rootMultiplicity_dvd Q t)
      · rw [show Polynomial.rootMultiplicity t Q - 1 = Polynomial.rootMultiplicity t Q.derivative
          from hder.symm]
        exact Polynomial.pow_rootMultiplicity_dvd Q.derivative t
  · -- `t` is not a root: `mult_t Q = 0`, and `d ∣ Q` forces `mult_t d = 0`.
    rw [Polynomial.rootMultiplicity_eq_zero ht, Nat.zero_sub, Polynomial.rootMultiplicity_eq_zero]
    intro hdroot
    exact ht (Polynomial.IsRoot.dvd hdroot hdQ)

omit [IsRealClosed R] in
/-- **(P4) count.** The number of *distinct* roots of `CharPol(M)` in an algebraically
closed extension `C` of `R` is `p − (gcd-degree)`. Over a field of characteristic zero,
`deg gcd(P, P') = deg P − #{distinct roots of P}` (each root of multiplicity `m`
contributes `m − 1` to the gcd). -/
theorem card_aroots_toFinset_eq {C : Type*} [Field C] [Algebra R C] [IsAlgClosed C]
    [DecidableEq C] (P : Polynomial R) (hP : P ≠ 0) :
    (P.aroots C).toFinset.card = P.natDegree - (gcd P P.derivative).natDegree := by
  classical
  have hCharR : CharZero R := inferInstance
  have hCharC : CharZero C := charZero_of_injective_algebraMap (R := R) (RingHom.injective _)
  set φ := algebraMap R C with hφ
  have hφinj : Function.Injective φ := RingHom.injective _
  set Q := P.map φ with hQ
  have hQne : Q ≠ 0 := by rwa [hQ, Ne, Polynomial.map_eq_zero_iff hφinj]
  have hQ' : Q.derivative = P.derivative.map φ := by rw [hQ, Polynomial.derivative_map]
  -- The distinct aroots are the distinct roots of `Q`.
  have haroots : (P.aroots C).toFinset.card = Q.roots.toFinset.card := by
    rw [Polynomial.aroots, ← hφ]
  rw [haroots]
  -- Descend the gcd degree from `R` to `C`.
  set dR := gcd P P.derivative with hdR
  set dC := EuclideanDomain.gcd Q Q.derivative with hdC
  have hdeg_descent : dR.natDegree = dC.natDegree := by
    -- `dR` (GCDMonoid.gcd) is associated to the EuclideanDomain.gcd over `R`.
    have hassoc : Associated dR (EuclideanDomain.gcd P P.derivative) := by
      apply associated_of_dvd_dvd
      · exact EuclideanDomain.dvd_gcd (gcd_dvd_left _ _) (gcd_dvd_right _ _)
      · exact dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _)
    have h1 : dR.natDegree = (EuclideanDomain.gcd P P.derivative).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hassoc)
    have h2 : (EuclideanDomain.gcd P P.derivative).map φ = dC := by
      rw [hdC, hQ', hQ, Polynomial.gcd_map]
    rw [h1, ← Polynomial.natDegree_map_eq_of_injective hφinj, h2]
  rw [hdeg_descent]
  -- Now everything is over `C`. Express degrees as sums of root multiplicities.
  have hdCdvd : dC ∣ Q := hdC ▸ EuclideanDomain.gcd_dvd_left Q Q.derivative
  have hdCne : dC ≠ 0 := fun h => hQne (by simpa [h] using hdCdvd)
  have hQsplit : Q.Splits := IsAlgClosed.splits Q
  have hdCsplit : dC.Splits := hQsplit.of_dvd hQne hdCdvd
  -- Root sets: roots of `dC` are a subset of roots of `Q`.
  have hsub : dC.roots.toFinset ⊆ Q.roots.toFinset := by
    intro t ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hdCne] at ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQne]
    exact ht.dvd (EuclideanDomain.gcd_dvd_left Q Q.derivative)
  -- natDegree as sum of root multiplicities over the (larger) root finset of `Q`.
  have hPQ : P.natDegree = Q.natDegree := (Polynomial.natDegree_map_eq_of_injective hφinj P).symm
  have hQdeg : Q.natDegree = ∑ t ∈ Q.roots.toFinset, Polynomial.rootMultiplicity t Q := by
    rw [hQsplit.natDegree_eq_card_roots, ← Multiset.toFinset_sum_count_eq]
    exact Finset.sum_congr rfl (fun t _ => Polynomial.count_roots Q)
  have hdCdeg : dC.natDegree = ∑ t ∈ Q.roots.toFinset, Polynomial.rootMultiplicity t dC := by
    rw [hdCsplit.natDegree_eq_card_roots, ← Multiset.toFinset_sum_count_eq]
    rw [Finset.sum_subset hsub (fun t _ ht =>
      Multiset.count_eq_zero.mpr (by rwa [Multiset.mem_toFinset] at ht))]
    exact Finset.sum_congr rfl (fun t _ => Polynomial.count_roots dC)
  -- The distinct-root count as a sum of ones.
  have hcard : Q.roots.toFinset.card = ∑ t ∈ Q.roots.toFinset, 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one]
  -- Each multiplicity in `dC` is one less, and at least one in `Q`.
  rw [hcard, hPQ, hQdeg, hdCdeg, ← Finset.sum_tsub_distrib]
  · refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [hdC, rootMultiplicity_euclideanGcd_derivative hQne t]
    have htr : Q.IsRoot t := by rwa [← Polynomial.mem_roots hQne, ← Multiset.mem_toFinset]
    have h1 : 1 ≤ Polynomial.rootMultiplicity t Q := (Polynomial.rootMultiplicity_pos hQne).2 htr
    omega
  · intro t ht
    rw [hdC, rootMultiplicity_euclideanGcd_derivative hQne t]
    omega

/-! ### (P5) Combine -/

/-- **Proposition 4.50.** The eigenvalues of a symmetric matrix over a real closed field
`R` lie in `R`: the characteristic polynomial splits over `R`. -/
theorem proposition_4_50 [NeZero p] (M : Matrix (Fin p) (Fin p) R) (hM : M.IsSymm) :
    Polynomial.Splits M.charpoly := by
  classical
  set C := AlgebraicClosure R
  set φ := algebraMap R C with hφ
  have hφinj : Function.Injective φ := FaithfulSMul.algebraMap_injective R C
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hdeg : M.charpoly.natDegree = p := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hposdeg : 0 < M.charpoly.natDegree := by rw [hdeg]; exact hp
  have hPne : M.charpoly ≠ 0 := fun h => by rw [h] at hposdeg; simp at hposdeg
  have hmapne : M.charpoly.map φ ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff hφinj]
  -- Reduce to a root-count equality.
  rw [Polynomial.splits_iff_card_roots, hdeg]
  -- Extract the threshold `k` from Proposition 4.49.
  obtain ⟨k, hk, hpos, hzero⟩ := proposition_4_49 M hM
  -- (P3) Distinct real roots: `p - k`.
  have hreal : (M.charpoly.roots.toFinset.card : ℤ) = (p : ℤ) - k := by
    rw [← theorem_4_34 M.charpoly hposdeg]
    exact pmv_sDiscSeq_eq M hM hk hpos hzero
  have hkp : k ≤ p := by omega
  have hrealN : M.charpoly.roots.toFinset.card = p - k := by
    have := hreal; omega
  -- (P4) Distinct complex roots: `p - k`.
  have hgcd : (gcd M.charpoly M.charpoly.derivative).natDegree = k :=
    deg_gcd_charpoly_eq M hM hk hpos hzero
  have hcplx : (M.charpoly.aroots C).toFinset.card = p - k := by
    rw [card_aroots_toFinset_eq M.charpoly hPne, hgcd, hdeg]
  -- The φ-image of a distinct real root is a distinct complex root.
  have haroots_eq : M.charpoly.aroots C = (M.charpoly.map φ).roots := by
    rw [Polynomial.aroots]
  have himg : ∀ r ∈ M.charpoly.roots.toFinset, φ r ∈ (M.charpoly.aroots C).toFinset := by
    intro r hr
    rw [Multiset.mem_toFinset] at hr ⊢
    rw [haroots_eq, Polynomial.mem_roots hmapne]
    have hroot : Polynomial.eval r M.charpoly = 0 := (Polynomial.mem_roots hPne).mp hr
    refine Polynomial.IsRoot.def.mpr ?_
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hroot, map_zero]
  -- The map `r ↦ φ r` from distinct real roots to distinct complex roots is injective,
  -- and both finsets have the same cardinality `p - k`, so it is surjective.
  have hsurj : ∀ c ∈ (M.charpoly.aroots C).toFinset, ∃ r ∈ M.charpoly.roots.toFinset, φ r = c := by
    have hcard : M.charpoly.roots.toFinset.card = (M.charpoly.aroots C).toFinset.card := by
      rw [hrealN, hcplx]
    have hmapsto : Set.MapsTo φ ↑M.charpoly.roots.toFinset ↑(M.charpoly.aroots C).toFinset :=
      fun r hr => himg r hr
    have hbij := Finset.surjOn_of_injOn_of_card_le
      (f := φ) (s := M.charpoly.roots.toFinset) (t := (M.charpoly.aroots C).toFinset)
      (fun r hr => himg r hr) (fun a _ b _ h => hφinj h) (by rw [hcard])
    intro c hc
    obtain ⟨r, hr, hrc⟩ := hbij hc
    exact ⟨r, hr, hrc⟩
  -- Every complex root with multiplicity matches the φ-image of a real root, hence
  -- `(map φ).roots = roots.map φ`, giving `card roots = card (map φ).roots = p`.
  have hmulti : (M.charpoly.map φ).roots = M.charpoly.roots.map φ := by
    refine Multiset.ext.mpr (fun c => ?_)
    by_cases hcr : c ∈ Set.range φ
    · obtain ⟨r, rfl⟩ := hcr
      rw [Multiset.count_map_eq_count' φ _ hφinj]
      rw [Polynomial.count_roots, Polynomial.count_roots,
        ← Polynomial.eq_rootMultiplicity_map hφinj r]
    · -- `c` is not in the image, so it is not a root of `map φ`, and not in `roots.map φ`.
      have hc1 : Multiset.count c (M.charpoly.map φ).roots = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        have : c ∈ (M.charpoly.aroots C).toFinset := by
          rw [Multiset.mem_toFinset, haroots_eq]; exact hmem
        obtain ⟨r, _, hrc⟩ := hsurj c this
        exact hcr ⟨r, hrc⟩
      have hc2 : Multiset.count c (M.charpoly.roots.map φ) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        rw [Multiset.mem_map] at hmem
        obtain ⟨r, _, hrc⟩ := hmem
        exact hcr ⟨r, hrc⟩
      rw [hc1, hc2]
  -- Conclude the root count.
  have hcardmap : (M.charpoly.map φ).roots.card = p := by
    rw [← haroots_eq, IsAlgClosed.card_aroots_eq_natDegree, hdeg]
  rw [hmulti, Multiset.card_map] at hcardmap
  exact hcardmap

end

end Azurite.BPR.Chapter4
