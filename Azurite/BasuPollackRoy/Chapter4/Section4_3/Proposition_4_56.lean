import Azurite.BasuPollackRoy.Chapter4.Section4_3.Proposition_4_55
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Proposition_4_8
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Reverse

/-!
# BPR Proposition 4.56: the expansion of `P' Q / P` in powers of `1/X`

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.3.

For `P` monic of degree `p ≥ 1` and `Q : K[X]`, set `C := (P' Q) /ₘ P` (the polynomial
part of `P' Q / P`) and let
`s n := Tr(L_{Q Xⁿ}) = Algebra.trace K (K[X]/(P)) (mk P (Q Xⁿ))`.
Then, as a formal series in `1/X`,
`P' Q / P = C + ∑_{n ≥ 0} s_n / X^{n+1}`.

We encode the series side using `LaurentSeries K = HahnSeries ℤ K`, which is a field
(as `K` is), with the distinguished element `u := ofPowerSeries X` (a unit). The algebra
map `expand∞ : K[X] →ₐ[K] LaurentSeries K` sends the polynomial variable `X` to `u⁻¹`, so
that `1 / X^{n+1} ↦ u^{n+1}`.
-/

namespace Azurite.BPR.Chapter4

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- The series variable `u = ofPowerSeries X` in `LaurentSeries K`; it represents `1/X`
under `expand∞` (which sends polynomial `X` to `u⁻¹`). It is a unit since `LaurentSeries K`
is a field. -/
noncomputable def laurentX : LaurentSeries K := HahnSeries.ofPowerSeries ℤ K PowerSeries.X

/-- The expansion-at-infinity algebra map `K[X] →ₐ[K] LaurentSeries K`, sending the
polynomial variable `X` to `u⁻¹` (where `u = laurentX`). Hence `1/X^{n+1} ↦ u^{n+1}`. -/
noncomputable def expandInf : K[X] →ₐ[K] LaurentSeries K :=
  Polynomial.aeval (laurentX (K := K))⁻¹

/-- The trace sequence `s n = Tr(L_{Q Xⁿ})`. -/
noncomputable def traceSeq (P Q : K[X]) (n : ℕ) : K :=
  Algebra.trace K (AdjoinRoot P) (AdjoinRoot.mk P (Q * X ^ n))

/-- **Moment recurrence** (free over `K`): for any `a`,
`∑_{b=0}^{p} P.coeff b · s_{a+b} = 0`, where `p = P.natDegree`.
This is the key structural identity: `∑_b a_b s_{a+b} = Tr(L_{Q X^a P}) = Tr(0) = 0`,
since `∑_{b ≤ p} a_b X^b = P` (as `p = deg P`) and `mk P P = 0`. -/
theorem traceSeq_recurrence (P Q : K[X]) (a : ℕ) :
    (Finset.range (P.natDegree + 1)).sum (fun b => P.coeff b * traceSeq P Q (a + b)) = 0 := by
  classical
  -- Rewrite each summand as a trace of a scalar multiple.
  have key : (Finset.range (P.natDegree + 1)).sum
      (fun b => P.coeff b * traceSeq P Q (a + b)) =
      Algebra.trace K (AdjoinRoot P) (AdjoinRoot.mk P (Q * X ^ a * P)) := by
    -- Pull the scalar inside the trace and the K[X] multiplication inside `mk`.
    have hP_sum : P = ∑ b ∈ Finset.range (P.natDegree + 1),
        Polynomial.C (P.coeff b) * X ^ b := by
      have h := Polynomial.as_sum_range' P (P.natDegree + 1) (Nat.lt_succ_self _)
      have h2 : (∑ i ∈ Finset.range (P.natDegree + 1), (monomial i) (P.coeff i))
          = ∑ b ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff b) * X ^ b :=
        Finset.sum_congr rfl (fun b _ => (Polynomial.C_mul_X_pow_eq_monomial).symm)
      conv_lhs => rw [h]
      exact h2
    rw [show Q * X ^ a * P = ∑ b ∈ Finset.range (P.natDegree + 1),
        Polynomial.C (P.coeff b) * (Q * X ^ (a + b)) from by
      conv_lhs => rw [hP_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    -- traceSeq P Q (a+b) = trace (mk (Q * X^(a+b)))
    unfold traceSeq
    rw [show AdjoinRoot.mk P (Polynomial.C (P.coeff b) * (Q * X ^ (a + b)))
        = P.coeff b • AdjoinRoot.mk P (Q * X ^ (a + b)) from by
      rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq, map_mul, AdjoinRoot.mk_C]]
    rw [map_smul, smul_eq_mul]
  rw [key]
  rw [show Q * X ^ a * P = (Q * X ^ a) * P from by ring, map_mul, AdjoinRoot.mk_self,
      mul_zero, map_zero]

section CSide

variable {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-- The polynomial part of `(P' X^d) / P`, namely `∑_{i=0}^{d-1} N_i X^{d-1-i}` over `C`. -/
private noncomputable def polyPart (P : K[X]) (d : ℕ) : C[X] :=
  (Finset.range d).sum (fun i => Polynomial.C (newtonSum (C := C) P i) * X ^ (d - 1 - i))

/-- **Core coefficient computation over `C`** for the monomial case `Q = X^d`.
The proper part `R_C := X^d · P_C' - P_C · (polyPart)` has its `(j-1)`-coefficient equal to
the weighted Newton sum `∑_{n=j}^p a_n N_{n-j+d}`. -/
private theorem proposition_4_56_coeff_C (P : K[X]) (d j : ℕ)
    (hj1 : 1 ≤ j) (hjp : j ≤ P.natDegree) :
    ((X ^ d * (P.map (algebraMap K C)).derivative - (P.map (algebraMap K C)) *
        polyPart (C := C) P d)).coeff (j - 1) =
      (Finset.Ico j (P.natDegree + 1)).sum
        (fun n => (algebraMap K C) (P.coeff n) * newtonSum (C := C) P (n - j + d)) := by
  classical
  set f := algebraMap K C with hf
  set Q_C : C[X] := P.map f with hQC
  set p := P.natDegree with hp_def
  have hQC_coeff : ∀ m, Q_C.coeff m = f (P.coeff m) := fun m => Polynomial.coeff_map f m
  -- Coefficient of `X^d * Q_C'` at `j-1`.
  have hT1 : (X ^ d * Q_C.derivative).coeff (j - 1) =
      if d ≤ j - 1 then ((j - 1 - d + 1 : ℕ) : C) * Q_C.coeff (j - 1 - d + 1) else 0 := by
    rw [show (X : C[X]) ^ d * Q_C.derivative = Q_C.derivative * X ^ d from by ring,
      Polynomial.coeff_mul_X_pow']
    split_ifs with h
    · rw [Polynomial.coeff_derivative]; push_cast; ring
    · rfl
  -- Coefficient of `Q_C * polyPart` at `j-1`.
  have hT2 : (Q_C * polyPart (C := C) P d).coeff (j - 1) =
      (Finset.range d).sum (fun i =>
        newtonSum (C := C) P i *
          (if d - 1 - i ≤ j - 1 then Q_C.coeff (j - 1 - (d - 1 - i)) else 0)) := by
    rw [polyPart, Finset.mul_sum, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i _
    rw [show Q_C * (Polynomial.C (newtonSum (C := C) P i) * X ^ (d - 1 - i)) =
        Polynomial.C (newtonSum (C := C) P i) * (Q_C * X ^ (d - 1 - i)) from by ring,
      Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
  rw [Polynomial.coeff_sub, hT1, hT2]
  -- Convert `Q_C.coeff` to `f (P.coeff ·)`.
  simp_rw [hQC_coeff]
  by_cases hdj : d ≤ j - 1
  · -- Case A: `d < j`. Set `l := j - d ≥ 1`.
    rw [if_pos hdj]
    -- T1 simplifies to `(j-d) * a_{j-d}`.
    rw [show j - 1 - d + 1 = j - d from by omega]
    -- T2 sum: every `if` is true.
    have hT2A : (Finset.range d).sum (fun i =>
          newtonSum (C := C) P i *
            (if d - 1 - i ≤ j - 1 then f (P.coeff (j - 1 - (d - 1 - i))) else 0)) =
        (Finset.range d).sum (fun i =>
          newtonSum (C := C) P i * f (P.coeff (j - d + i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [if_pos (by omega), show j - 1 - (d - 1 - i) = j - d + i from by omega]
    rw [hT2A]
    -- prop_4_8 at l = j - d.
    have h48 := proposition_4_8 (C := C) P (j - d) (by omega)
    -- Split the Ico (j-d) (p+1) range.
    rw [show Finset.Ico (j - d) (p + 1) =
        Finset.Ico (j - d) j ∪ Finset.Ico j (p + 1) from
        (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm] at h48
    rw [Finset.sum_union (by
      rw [Finset.disjoint_left]; intro m hm1 hm2
      rw [Finset.mem_Ico] at hm1 hm2; omega)] at h48
    -- Lower part of h48 equals T2.
    have hlow : (Finset.Ico (j - d) j).sum (fun m =>
          f (P.coeff m) * newtonSum (C := C) P (m - (j - d))) =
        (Finset.range d).sum (fun i =>
          newtonSum (C := C) P i * f (P.coeff (j - d + i))) := by
      apply Finset.sum_nbij' (fun m => m - (j - d)) (fun i => i + (j - d))
      · intro m hm; rw [Finset.mem_Ico] at hm; rw [Finset.mem_range]; omega
      · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Ico]; omega
      · intro m hm; rw [Finset.mem_Ico] at hm; omega
      · intro i hi; rw [Finset.mem_range] at hi; omega
      · intro m hm; rw [Finset.mem_Ico] at hm
        rw [show m - (j - d) = m - (j - d) from rfl,
          show (j - d) + (m - (j - d)) = m from by omega]
        ring
    -- Upper part of h48 equals target RHS.
    have hupp : (Finset.Ico j (p + 1)).sum (fun m =>
          f (P.coeff m) * newtonSum (C := C) P (m - (j - d))) =
        (Finset.Ico j (p + 1)).sum (fun n =>
          f (P.coeff n) * newtonSum (C := C) P (n - j + d)) := by
      apply Finset.sum_congr rfl
      intro m hm; rw [Finset.mem_Ico] at hm
      rw [show m - (j - d) = m - j + d from by omega]
    rw [hlow, hupp] at h48
    -- h48 : (j-d) * a_{j-d} = T2 + target.  Rearrange.
    rw [h48]; ring
  · -- Case B: `j ≤ d`. Set `q := d - j ≥ 0`.
    rw [if_neg hdj]
    set q := d - j with hq_def
    -- T2 sum: only `i ≥ q` survive.
    have hT2B : (Finset.range d).sum (fun i =>
          newtonSum (C := C) P i *
            (if d - 1 - i ≤ j - 1 then f (P.coeff (j - 1 - (d - 1 - i))) else 0)) =
        (Finset.Ico q d).sum (fun i =>
          newtonSum (C := C) P i * f (P.coeff (i - q))) := by
      rw [show Finset.range d = Finset.Ico 0 q ∪ Finset.Ico q d from by
        rw [Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega)]]
      rw [Finset.sum_union (by
        rw [Finset.disjoint_left]; intro i hi1 hi2
        rw [Finset.mem_Ico] at hi1 hi2; omega)]
      rw [show (Finset.Ico 0 q).sum (fun i =>
            newtonSum (C := C) P i *
              (if d - 1 - i ≤ j - 1 then f (P.coeff (j - 1 - (d - 1 - i))) else 0)) = 0 from by
        apply Finset.sum_eq_zero
        intro i hi; rw [Finset.mem_Ico] at hi
        rw [if_neg (by omega), mul_zero]]
      rw [zero_add]
      apply Finset.sum_congr rfl
      intro i hi; rw [Finset.mem_Ico] at hi
      rw [if_pos (by omega), show j - 1 - (d - 1 - i) = i - q from by omega]
    rw [hT2B]
    -- Orthogonality at q.
    have hortho := newtonSum_orthogonality (C := C) P q
    -- Reindex orthogonality to Ico q (p+q+1) with summand a_{i-q} N_i.
    have hortho' : (Finset.Ico q (p + q + 1)).sum (fun i =>
          newtonSum (C := C) P i * f (P.coeff (i - q))) = 0 := by
      rw [← hortho]
      apply Finset.sum_nbij' (fun i => i - q) (fun m => m + q)
      · intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_range]; omega
      · intro m hm; rw [Finset.mem_range] at hm; rw [Finset.mem_Ico]; omega
      · intro i hi; rw [Finset.mem_Ico] at hi; omega
      · intro m hm; rw [Finset.mem_range] at hm; omega
      · intro i hi; rw [Finset.mem_Ico] at hi
        rw [show i - q + q = i from by omega, hf]; ring
    -- Split orthogonality range at d.
    rw [show Finset.Ico q (p + q + 1) =
        Finset.Ico q d ∪ Finset.Ico d (p + q + 1) from
        (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm] at hortho'
    rw [Finset.sum_union (by
      rw [Finset.disjoint_left]; intro i hi1 hi2
      rw [Finset.mem_Ico] at hi1 hi2; omega)] at hortho'
    -- Upper part equals target RHS.
    have hupp : (Finset.Ico d (p + q + 1)).sum (fun i =>
          newtonSum (C := C) P i * f (P.coeff (i - q))) =
        (Finset.Ico j (p + 1)).sum (fun n =>
          f (P.coeff n) * newtonSum (C := C) P (n - j + d)) := by
      apply Finset.sum_nbij' (fun i => i - q) (fun n => n + q)
      · intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_Ico]; omega
      · intro n hn; rw [Finset.mem_Ico] at hn; rw [Finset.mem_Ico]; omega
      · intro i hi; rw [Finset.mem_Ico] at hi; omega
      · intro n hn; rw [Finset.mem_Ico] at hn; omega
      · intro i hi; rw [Finset.mem_Ico] at hi
        rw [show i - q - j + d = i from by omega]
        ring
    rw [hupp] at hortho'
    -- hortho' : T2 + target = 0.  Goal: 0 - T2 = target.
    linear_combination -hortho'

end CSide

/-- **Monomial case** `Q = X^d` of the core identity, over `K`.
Proved by transfer to the algebraic closure of `K`, where it becomes the `C`-side
computation `proposition_4_56_coeff_C`. -/
private theorem proposition_4_56_monomial (P : K[X]) (hP : P.Monic) (hp : 0 < P.natDegree)
    (d j : ℕ) (hj1 : 1 ≤ j) (hjp : j ≤ P.natDegree) :
    ((P.derivative * X ^ d) %ₘ P).coeff (j - 1) =
      (Finset.Ico j (P.natDegree + 1)).sum
        (fun n => P.coeff n * traceSeq P (X ^ d) (n - j)) := by
  classical
  set C := AlgebraicClosure K with hC
  set f := algebraMap K C with hf
  have hf_inj : Function.Injective f := f.injective
  set Q_C : C[X] := P.map f with hQC
  have hQC_monic : Q_C.Monic := hP.map f
  -- It suffices to prove the image identity over `C`.
  apply hf_inj
  -- LHS: push `f` through `coeff` and `modByMonic`.
  rw [hf, ← Polynomial.coeff_map f, Polynomial.map_modByMonic _ hP, Polynomial.map_mul,
    ← Polynomial.derivative_map, Polynomial.map_pow, Polynomial.map_X, ← hQC]
  -- Now LHS = `((Q_C.derivative * X^d) %ₘ Q_C).coeff (j-1)`.
  -- Identify with the truncation polynomial `R_C`.
  set R_C : C[X] := X ^ d * Q_C.derivative - Q_C * polyPart (C := C) P d with hR
  have hdeg : R_C.natDegree < P.natDegree := by
    rw [hR, polyPart]; exact proposition_4_8_series (C := C) P hp d
  have hRmod : (Q_C.derivative * X ^ d) %ₘ Q_C = R_C := by
    rw [show (Q_C.derivative * X ^ d : C[X]) = X ^ d * Q_C.derivative from by ring]
    have hdvd : Q_C ∣ (X ^ d * Q_C.derivative - R_C) :=
      ⟨polyPart (C := C) P d, by rw [hR]; ring⟩
    rw [Polynomial.modByMonic_eq_of_dvd_sub hQC_monic hdvd]
    rw [Polynomial.modByMonic_eq_self_iff hQC_monic]
    have hQCdeg : Q_C.degree = (P.natDegree : WithBot ℕ) := by
      rw [hQC, Polynomial.degree_map_eq_of_injective hf_inj,
        Polynomial.degree_eq_natDegree hP.ne_zero]
    calc R_C.degree ≤ (R_C.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < (P.natDegree : WithBot ℕ) := by exact_mod_cast hdeg
      _ = Q_C.degree := hQCdeg.symm
  rw [hRmod, hR]
  -- Now LHS = `R_C.coeff (j-1)` which equals the `C`-side sum.
  rw [← hR, proposition_4_56_coeff_C P d j hj1 hjp]
  -- RHS: push `f` through the sum and identify `traceSeq` with Newton sums.
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul]
  congr 1
  -- newtonSum P (n-j+d) = f (traceSeq P (X^d) (n-j))
  rw [traceSeq]
  rw [show (X : K[X]) ^ d * X ^ (n - j) = X ^ (n - j + d) from by rw [← pow_add, Nat.add_comm]]
  rw [show AdjoinRoot.mk P (X ^ (n - j + d)) = AdjoinRoot.root P ^ (n - j + d) from by
    rw [map_pow, AdjoinRoot.mk_X]]
  exact (trace_gen_pow_eq_newtonSum (C := C) P hP (n - j + d)).symm

/-- **The core coefficient identity** of Proposition 4.56 (over `K`).
With `R := (P' Q) %ₘ P` the proper part of `P' Q / P` and `s_n = Tr(L_{Q Xⁿ})`, for
`1 ≤ j ≤ p` the coefficient of `R` at `j-1` is
`R.coeff (j-1) = ∑_{n=j}^{p} P.coeff n · s_{n-j}`.
This is the weighted analogue of Proposition 4.8 (which is the case `Q = 1`, `R = P'`). -/
theorem proposition_4_56_coeff (P Q : K[X]) (hP : P.Monic) (hp : 0 < P.natDegree)
    (j : ℕ) (hj1 : 1 ≤ j) (hjp : j ≤ P.natDegree) :
    ((P.derivative * Q) %ₘ P).coeff (j - 1) =
      (Finset.Ico j (P.natDegree + 1)).sum
        (fun n => P.coeff n * traceSeq P Q (n - j)) := by
  classical
  -- Expand `Q` as a sum of monomials.
  have hQexp : Q = ∑ d ∈ Finset.range (Q.natDegree + 1),
      Polynomial.C (Q.coeff d) * X ^ d := by
    conv_lhs => rw [Polynomial.as_sum_range' Q (Q.natDegree + 1) (Nat.lt_succ_self _)]
    exact Finset.sum_congr rfl (fun d _ => (Polynomial.C_mul_X_pow_eq_monomial).symm)
  -- `traceSeq` is `K`-linear in its polynomial argument.
  have htrace_lin : ∀ m, traceSeq P Q m =
      ∑ d ∈ Finset.range (Q.natDegree + 1), Q.coeff d * traceSeq P (X ^ d) m := by
    intro m
    unfold traceSeq
    conv_lhs => rw [hQexp]
    rw [Finset.sum_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [show AdjoinRoot.mk P (Polynomial.C (Q.coeff d) * X ^ d * X ^ m)
        = Q.coeff d • AdjoinRoot.mk P (X ^ d * X ^ m) from by
      rw [show Polynomial.C (Q.coeff d) * X ^ d * X ^ m
          = Polynomial.C (Q.coeff d) * (X ^ d * X ^ m) from by ring,
        Algebra.smul_def, AdjoinRoot.algebraMap_eq, map_mul, AdjoinRoot.mk_C]]
    rw [map_smul, smul_eq_mul]
  -- RHS: pull the `traceSeq` expansion through and swap the order of summation.
  rw [show (Finset.Ico j (P.natDegree + 1)).sum
        (fun n => P.coeff n * traceSeq P Q (n - j)) =
      ∑ d ∈ Finset.range (Q.natDegree + 1), Q.coeff d *
        (Finset.Ico j (P.natDegree + 1)).sum
          (fun n => P.coeff n * traceSeq P (X ^ d) (n - j)) from by
    rw [show (Finset.Ico j (P.natDegree + 1)).sum
          (fun n => P.coeff n * traceSeq P Q (n - j)) =
        ∑ n ∈ Finset.Ico j (P.natDegree + 1), ∑ d ∈ Finset.range (Q.natDegree + 1),
          Q.coeff d * (P.coeff n * traceSeq P (X ^ d) (n - j)) from by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [htrace_lin, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_); ring]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum]]
  -- Replace each monomial sum by the monomial coefficient identity.
  simp_rw [← proposition_4_56_monomial P hP hp _ j hj1 hjp]
  -- LHS: distribute `modByMonic` over the monomial expansion via the linear map `modByMonicHom`.
  conv_lhs => rw [hQexp, Finset.mul_sum]
  rw [show (∑ d ∈ Finset.range (Q.natDegree + 1),
        P.derivative * (Polynomial.C (Q.coeff d) * X ^ d)) %ₘ P
      = ∑ d ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff d) • ((P.derivative * X ^ d) %ₘ P) from by
    rw [← Polynomial.modByMonicHom_apply, map_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [show P.derivative * (Polynomial.C (Q.coeff d) * X ^ d)
        = (Q.coeff d) • (P.derivative * X ^ d) from by
      rw [Polynomial.smul_eq_C_mul]; ring]
    rw [map_smul, Polynomial.modByMonicHom_apply]]
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Polynomial.coeff_smul, smul_eq_mul]

section Packaging

open PowerSeries

/-- **PowerSeries form of Proposition 4.56.** With `R := (P' Q) %ₘ P`, `p := P.natDegree`,
and `s n := Tr(L_{Q Xⁿ})`, the reflected proper part satisfies the power-series identity
`reflect p R = X · (∑ s_n Xⁿ) · reflect p P`. This is the coefficient identity
`proposition_4_56_coeff` (for the low coefficients) together with the moment recurrence
`traceSeq_recurrence` (for the high coefficients), packaged via reflection. -/
theorem proposition_4_56_powerSeries (P Q : K[X]) (hP : P.Monic) (hp : 0 < P.natDegree) :
    (↑(Polynomial.reflect P.natDegree ((P.derivative * Q) %ₘ P)) : PowerSeries K)
      = PowerSeries.X * PowerSeries.mk (traceSeq P Q) *
          (↑(Polynomial.reflect P.natDegree P) : PowerSeries K) := by
  classical
  have hP1 : P ≠ 1 := by intro h; rw [h, Polynomial.natDegree_one] at hp; omega
  set p := P.natDegree with hp_def
  set R : K[X] := (P.derivative * Q) %ₘ P with hR
  set s := traceSeq P Q with hs
  -- `deg R < p`.
  have hRdeg : R.natDegree < p := by
    rw [hR]; exact Polynomial.natDegree_modByMonic_lt _ hP hP1
  have hRzero : ∀ i, p ≤ i → R.coeff i = 0 := fun i hi =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [mul_assoc]
  ext m
  rw [Polynomial.coeff_coe, Polynomial.coeff_reflect]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0: both sides vanish.
    subst hm0
    rw [Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero, hRzero p le_rfl]
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  · -- m = m' + 1.
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_lt hmpos
    rw [Nat.zero_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul]
    -- RHS: ∑_{a+b=m'} s a * (reflect p P).coeff b
    have hRHS : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m',
          (PowerSeries.coeff x.1) (PowerSeries.mk s) *
            (PowerSeries.coeff x.2) (↑(Polynomial.reflect p P) : PowerSeries K) =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m',
          s x.1 * P.coeff (Polynomial.revAt p x.2) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [PowerSeries.coeff_mk, Polynomial.coeff_coe, Polynomial.coeff_reflect]
    rw [hRHS]
    rcases Nat.lt_or_ge m' p with hmp | hmp
    · -- m' < p: use the coefficient identity at j = p - m'.
      rw [Polynomial.revAt_le (by omega)]
      set j := p - m' with hj
      have hj1 : 1 ≤ j := by omega
      have hjp : j ≤ p := by omega
      have hkey := proposition_4_56_coeff P Q hP hp j hj1 hjp
      rw [← hR, ← hs] at hkey
      rw [show p - (m' + 1) = j - 1 from by omega, hkey]
      -- Match: n ↦ (n - j, p - n) is a bijection Ico j (p+1) → antidiagonal m'.
      symm
      apply Finset.sum_nbij' (fun x => p - x.2) (fun n => (n - j, p - n))
      · rintro ⟨a, b⟩ hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [Finset.mem_Ico]; omega
      · intro n hn
        rw [Finset.mem_Ico] at hn
        rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
      · rintro ⟨a, b⟩ hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        ext <;> simp <;> omega
      · intro n hn
        rw [Finset.mem_Ico] at hn; omega
      · rintro ⟨a, b⟩ hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        simp only [Polynomial.revAt_le (show b ≤ p from by omega)]
        rw [mul_comm, show p - b - j = a from by omega]
    · -- m' ≥ p: high coefficients vanish by the moment recurrence.
      rw [Polynomial.revAt_eq_self_of_lt (by omega), hRzero _ (by omega)]
      -- The antidiagonal sum vanishes: it is the moment recurrence at q = m' - p.
      symm
      have hrec := traceSeq_recurrence P Q (m' - p)
      rw [← hs] at hrec
      -- Convert antidiagonal to a range sum.
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun x => s x.1 * P.coeff (Polynomial.revAt p x.2)) m']
      -- The summand at index k vanishes unless m' - k ≤ p; restrict to that range.
      rw [← Finset.sum_subset (s₁ := Finset.Ico (m' - p) (m' + 1))
        (s₂ := Finset.range (m' + 1)) (by
          intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega) (by
          intro k hk2 hk
          rw [Finset.mem_range] at hk2
          rw [Finset.mem_Ico, not_and_or] at hk
          simp only
          -- k < m' - p, so m' - k > p, revAt = m' - k, P.coeff = 0.
          rw [Polynomial.revAt_eq_self_of_lt (show p < m' - k from by omega),
            Polynomial.coeff_eq_zero_of_natDegree_lt (show P.natDegree < m' - k from by
              rw [← hp_def]; omega), mul_zero])]
      -- Now match with the recurrence sum via k ↦ m' - k ↦ n = p - (m' - k).
      rw [← hrec]
      apply Finset.sum_nbij' (fun k => p - (m' - k)) (fun n => m' - p + n)
      · intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega
      · intro n hn; rw [Finset.mem_range] at hn; rw [Finset.mem_Ico]; omega
      · intro k hk; rw [Finset.mem_Ico] at hk; omega
      · intro n hn; rw [Finset.mem_range] at hn; omega
      · intro k hk
        rw [Finset.mem_Ico] at hk
        simp only
        rw [Polynomial.revAt_le (show m' - k ≤ p from by omega),
          show m' - p + (p - (m' - k)) = k from by omega, mul_comm]

/-- `laurentX` is nonzero (it is `ofPowerSeries X`, the image of a nonzero element under an
injective ring hom). -/
theorem laurentX_ne_zero : (laurentX (K := K)) ≠ 0 := by
  rw [laurentX]
  intro h
  exact PowerSeries.X_ne_zero (HahnSeries.ofPowerSeries_injective (by rw [h]; simp))

/-- `ofPowerSeries ∘ (Polynomial coercion) = aeval laurentX`: both are the `K`-algebra map
sending `X ↦ laurentX`. -/
theorem ofPowerSeries_coe_eq_aeval (g : K[X]) :
    HahnSeries.ofPowerSeries ℤ K (↑g : PowerSeries K) = Polynomial.aeval (laurentX (K := K)) g := by
  have hcoe : (↑g : PowerSeries K) = Polynomial.aeval PowerSeries.X g := by
    rw [Polynomial.aeval_def, ← Polynomial.eval₂_C_X_eq_coe]; rfl
  rw [hcoe, Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂,
    laurentX, HahnSeries.ofPowerSeries_X]
  congr 1

/-- **Bridge.** For `f` with `natDegree f ≤ p`, the expansion `expandInf f` equals
`(laurentX)⁻ᵖ · ofPowerSeries (reflect p f)`. (Multiplying by the unit `laurentXᵖ`:
`laurentXᵖ · expandInf f = ofPowerSeries (reflect p f)`.) -/
theorem laurentX_pow_mul_expandInf (f : K[X]) (p : ℕ) (hf : f.natDegree ≤ p) :
    (laurentX (K := K)) ^ p * expandInf f =
      HahnSeries.ofPowerSeries ℤ K (↑(Polynomial.reflect p f) : PowerSeries K) := by
  have hne := laurentX_ne_zero (K := K)
  rw [ofPowerSeries_coe_eq_aeval, expandInf]
  -- Both sides as range sums over `range (p+1)`.
  rw [Polynomial.aeval_eq_sum_range' (show (Polynomial.reflect p f).natDegree < p + 1 from by
    have := @Polynomial.natDegree_reflect_le K _ p f
    omega)]
  rw [Polynomial.aeval_eq_sum_range' (show f.natDegree < p + 1 from by omega)]
  rw [Finset.mul_sum]
  -- Match termwise via the bijection `i ↦ p - i` of `range (p+1)`.
  apply Finset.sum_nbij' (fun i => p - i) (fun b => p - b)
  · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
  · intro b hb; rw [Finset.mem_range] at hb ⊢; omega
  · intro i hi; rw [Finset.mem_range] at hi; omega
  · intro b hb; rw [Finset.mem_range] at hb; omega
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le (show p - i ≤ p from by omega),
      show p - (p - i) = i from by omega]
    rw [Algebra.smul_def, Algebra.smul_def, mul_comm (laurentX ^ p), mul_assoc]
    congr 1
    rw [inv_pow, inv_mul_eq_div]
    exact (pow_sub₀ _ hne (by omega)).symm

/-- **BPR Proposition 4.56.** For `P` monic of degree `p ≥ 1` and `Q : K[X]`, with
`C := (P' Q) /ₘ P` and `s n := Tr(L_{Q Xⁿ})`, the expansion of `P' Q / P` in powers of
`1/X` is
`P' Q / P = C + ∑_{n ≥ 0} s_n / X^{n+1}`.
Encoded in `LaurentSeries K` via `expandInf` (polynomial `X ↦ u⁻¹`, `u = laurentX`):
`expandInf (P' Q) · (expandInf P)⁻¹
  = expandInf ((P' Q) /ₘ P) + laurentX · ofPowerSeries (∑ s_n Xⁿ)`. -/
theorem proposition_4_56 (P Q : K[X]) (hP : P.Monic) (hp : 0 < P.natDegree) :
    expandInf (P.derivative * Q) * (expandInf P)⁻¹
      = expandInf ((P.derivative * Q) /ₘ P)
        + laurentX * HahnSeries.ofPowerSeries ℤ K
            (PowerSeries.mk (fun n =>
              Algebra.trace K (AdjoinRoot P)
                (AdjoinRoot.mk P (Q * (Polynomial.X) ^ n)))) := by
  classical
  have hP1 : P ≠ 1 := by intro h; rw [h, Polynomial.natDegree_one] at hp; omega
  set p := P.natDegree with hp_def
  have hne := laurentX_ne_zero (K := K)
  -- `expandInf P` is a unit (nonzero in the field `LaurentSeries K`):
  -- `laurentX^p * expandInf P = ofPS (reflect p P)` and the latter is nonzero (constant
  -- coeff = leading coeff = 1).
  have hPrefl : (↑(Polynomial.reflect p P) : PowerSeries K) ≠ 0 := by
    intro h
    have : (Polynomial.reflect p P).coeff 0 = 0 := by
      rw [← Polynomial.coeff_coe, h]; simp
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero,
      hp_def, hP.coeff_natDegree] at this
    exact one_ne_zero this
  have hPbridge := laurentX_pow_mul_expandInf P p (le_of_eq hp_def.symm)
  have hexpP_ne : expandInf P ≠ 0 := by
    intro h
    rw [h, mul_zero] at hPbridge
    exact hPrefl (HahnSeries.ofPowerSeries_injective (by rw [← hPbridge]; simp))
  -- Recognise the trace sequence as `traceSeq P Q`.
  rw [show (PowerSeries.mk (fun n => Algebra.trace K (AdjoinRoot P)
        (AdjoinRoot.mk P (Q * (Polynomial.X) ^ n)))) = PowerSeries.mk (traceSeq P Q) from rfl]
  -- Clear the unit `expandInf P`: reduce to `expandInf (P'Q) = RHS * expandInf P`.
  rw [← div_eq_mul_inv, div_eq_iff hexpP_ne]
  -- Use `P'Q = C·P + R` with `R = (P'Q) %ₘ P`, and `expandInf` a ring hom.
  have hdiv : P.derivative * Q = (P.derivative * Q) /ₘ P * P + (P.derivative * Q) %ₘ P := by
    have h := Polynomial.modByMonic_add_div (P.derivative * Q) P
    linear_combination -h
  conv_lhs => rw [hdiv]
  rw [map_add, map_mul, add_mul]
  -- Cancel the polynomial-part term `expandInf C * expandInf P`; reduce to the
  -- proper-part identity `expandInf R = laurentX · ofPS (mk s) · expandInf P`.
  rw [add_left_cancel_iff]
  -- Proper-part identity. Clear `laurentX^p` (unit): it suffices to show
  -- `laurentX^p * expandInf R = laurentX^p * (laurentX · ofPS (mk s) · expandInf P)`.
  have hpos : laurentX (K := K) ^ p ≠ 0 := pow_ne_zero _ hne
  apply mul_left_cancel₀ hpos
  -- LHS via the bridge.
  rw [laurentX_pow_mul_expandInf _ p
    (le_of_lt (Polynomial.natDegree_modByMonic_lt _ hP hP1))]
  -- RHS: regroup `laurentX^p` onto `expandInf P` via the bridge for `P`.
  rw [show laurentX (K := K) ^ p *
        (laurentX * HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk (traceSeq P Q)) * expandInf P)
      = laurentX * HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk (traceSeq P Q)) *
          (laurentX ^ p * expandInf P) from by ring]
  rw [hPbridge]
  -- Now everything is `ofPowerSeries` of polynomials/power-series; use the PowerSeries identity.
  rw [laurentX, ← map_mul, ← map_mul]
  rw [proposition_4_56_powerSeries P Q hP hp]

/-- **Proposition 4.56, stated via the trace `Tr` of the multiplication map `Lmul`.**
The series coefficients are `s_n = Tr(L_{Q Xⁿ}) = Tr (Lmul (mk (Q Xⁿ)))`. -/
theorem proposition_4_56_Tr_Lmul (P Q : K[X]) (hP : P.Monic) (hp : 0 < P.natDegree) :
    expandInf (P.derivative * Q) * (expandInf P)⁻¹
      = expandInf ((P.derivative * Q) /ₘ P)
        + laurentX * HahnSeries.ofPowerSeries ℤ K
            (PowerSeries.mk (fun n => Tr P (Lmul P (AdjoinRoot.mk P (Q * (Polynomial.X) ^ n))))) := by
  have heq : (fun n => Tr P (Lmul P (AdjoinRoot.mk P (Q * (Polynomial.X) ^ n))))
      = fun n => Algebra.trace K (AdjoinRoot P) (AdjoinRoot.mk P (Q * (Polynomial.X) ^ n)) := by
    funext n
    rw [Tr, Lmul, Algebra.trace_apply]
    rfl
  rw [heq]
  exact proposition_4_56 P Q hP hp

end Packaging

/-! ### Notes

Proposition 4.56 implies that the coefficients of `Her(P, Q)` belong to `D`: the
multiplication map `L_f` expressed in the canonical basis `1, X, …, X^{p-1}` has entries in
`D` (for `P, f ∈ D[X]` with `P` monic), so its trace lies in `D`; by Proposition 4.54
(`herMatrix_eq_trace`) those traces are the entries of `Her(P, Q)`. This recovers
`HerMatrix_mem_range` (the coefficients-in-`D` result already proved via symmetric functions).

Proposition 4.56 also generalizes Proposition 4.8: taking `Q = 1`, the polynomial part `C`
vanishes (`derivative_divByMonic_self_eq_zero`) and the traces become the Newton sums
(`traceSeq_one_eq_newtonSum`), so Proposition 4.56 reads `P'/P = ∑ₙ N_n / X^{n+1}`. -/

/-- **Note (generalizes Prop 4.8): the polynomial part vanishes for `Q = 1`.** Since
`deg P' < deg P`, the quotient `(P' · 1) /ₘ P` is zero, so for `Q = 1` Proposition 4.56 has
no polynomial part `C`, matching the logarithmic-derivative identity of Proposition 4.8. -/
theorem derivative_divByMonic_self_eq_zero (P : K[X]) (hP : P.Monic) :
    (P.derivative * 1) /ₘ P = 0 := by
  rw [mul_one, Polynomial.divByMonic_eq_zero_iff hP]
  exact Polynomial.degree_derivative_lt hP.ne_zero

section Generalization

variable {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-- **Note (generalizes Prop 4.8): the `Q = 1` traces are the Newton sums.** For `Q = 1`, the
trace sequence `s n = Tr(L_{Xⁿ})` satisfies `algebraMap K C (s n) = N_n(P)`. Together with
`derivative_divByMonic_self_eq_zero`, this specializes Proposition 4.56 to Proposition 4.8's
identity `P'/P = ∑ₙ N_n / X^{n+1}`. -/
theorem traceSeq_one_eq_newtonSum (P : K[X]) (hP : P.Monic) (n : ℕ) :
    algebraMap K C (traceSeq P 1 n) = newtonSum (C := C) P n := by
  have hmk : AdjoinRoot.mk P (1 * X ^ n) = AdjoinRoot.root P ^ n := by
    rw [one_mul, map_pow, AdjoinRoot.mk_X]
  rw [traceSeq, hmk]
  exact trace_gen_pow_eq_newtonSum P hP n

end Generalization

end Azurite.BPR.Chapter4
