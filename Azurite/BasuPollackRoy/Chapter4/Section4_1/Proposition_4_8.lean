import Azurite.BasuPollackRoy.Chapter4.Section4_1.Definition_4_7
import Mathlib.Algebra.Polynomial.Roots

/-!
# BPR Proposition 4.8: logarithmic derivative and Newton's recurrence

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

For `P = a_p X^p + … + a_0` with roots `x_1, …, x_p` in `C` (with
multiplicity), `P'/P = ∑_{i ≥ 0} N_i / X^{i+1}`. Equating coefficients
of `X^{p-1-i}` in `P' = (P'/P)·P` yields

  `(p - i) · a_{p-i} = a_p N_i + … + a_0 N_{i-p}`.

The Lean statement uses the equivalent **j-form** (`j := p - i`,
`m := p - k`):

  `j · a_j = ∑_{m=j}^{p} a_m · N_{m-j}`,

which keeps all Nat-sub non-negative.

See `Proposition_4_8_PLAN.md` for the proof decomposition.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {K : Type*} [Field K] {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

omit [IsAlgClosed C] in
/-- `N_0(P)` equals the cardinality of `P.aroots C`. -/
lemma newtonSum_zero (P : K[X]) :
    (newtonSum P 0 : C) = ((P.aroots C).card : C) := by
  unfold newtonSum
  simp [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]

section Aux

/-- Swap a Finset.range sum with a Multiset.sum. -/
private lemma finset_range_multiset_sum_swap {D : Type*} [AddCommMonoid D]
    (s : Multiset D) (n : ℕ) (g : ℕ → D → D) :
    (Finset.range n).sum (fun m => (s.map (g m)).sum) =
      (s.map (fun x => (Finset.range n).sum (fun m => g m x))).sum := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, ← Multiset.sum_map_add]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    rw [Finset.sum_range_succ]

/-- Generalised swap on `Finset.Ico`. -/
private lemma finset_Ico_multiset_sum_swap {D : Type*} [AddCommMonoid D]
    (s : Multiset D) (a b : ℕ) (g : ℕ → D → D) :
    (Finset.Ico a b).sum (fun m => (s.map (g m)).sum) =
      (s.map (fun x => (Finset.Ico a b).sum (fun m => g m x))).sum := by
  induction b with
  | zero => simp
  | succ k ih =>
    by_cases hak : a ≤ k
    · rw [Finset.sum_Ico_succ_top hak, ih, ← Multiset.sum_map_add]
      congr 1
      apply Multiset.map_congr rfl
      intro x _
      rw [Finset.sum_Ico_succ_top hak]
    · push Not at hak
      rw [Finset.Ico_eq_empty (by omega : ¬ a < k + 1)]
      simp

/-- Coefficient of `(X - C y) * Q` at index `0`. -/
private lemma coeff_X_sub_C_mul_zero {D : Type*} [CommRing D]
    (Q : D[X]) (y : D) :
    ((X - Polynomial.C y) * Q).coeff 0 = -(y * Q.coeff 0) := by
  rw [sub_mul, coeff_sub, coeff_X_mul_zero, Polynomial.C_mul', coeff_smul,
      smul_eq_mul, zero_sub]

/-- Reindex `∑_{m ∈ Ico a (b+1)} f (m - 1) = ∑_{m ∈ Ico (a-1) b} f m`. -/
private lemma sum_Ico_reindex_pred {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (a b : ℕ) (ha : 1 ≤ a) :
    (Finset.Ico a (b + 1)).sum (fun m => f (m - 1)) =
    (Finset.Ico (a - 1) b).sum f := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
      show b + 1 - a = b - (a - 1) from by omega]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  omega

end Aux

omit [IsAlgClosed C] in
/-- **Orthogonality identity**: `∑_{m=0}^{p} a_m · N_{m+q} = 0` for any `q`.
    Follows from `x^q · Q.eval x = 0` for each root `x` of `Q`, summed.
    Specialises at `q = 0` to the trace identity `∑ a_m · N_m = 0`. -/
lemma newtonSum_orthogonality (P : K[X]) (q : ℕ) :
    (Finset.range (P.natDegree + 1)).sum (fun m =>
        (algebraMap K C) (P.coeff m) * newtonSum P (m + q)) = 0 := by
  classical
  set Q : C[X] := P.map (algebraMap K C) with hQ
  have hQ_natDeg : Q.natDegree ≤ P.natDegree := Polynomial.natDegree_map_le
  have hQ_coeff : ∀ m, Q.coeff m = (algebraMap K C) (P.coeff m) := fun m =>
    Polynomial.coeff_map (algebraMap K C) m
  -- For each x ∈ aroots, x^q · Q.eval x = 0.
  have hsum_eval : ((P.aroots C).map (fun x => x ^ q * Q.eval x)).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro v hv
    rw [Multiset.mem_map] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    rw [show Q.eval x = 0 from (Polynomial.mem_roots'.mp hx).2, mul_zero]
  -- Pull each a_m into multiset, swap sums, identify inner sum with x^q · Q.eval x.
  have h_pull : (Finset.range (P.natDegree + 1)).sum (fun m =>
        (algebraMap K C) (P.coeff m) * newtonSum P (m + q)) =
      (Finset.range (P.natDegree + 1)).sum (fun m =>
        ((P.aroots C).map (fun x =>
          (algebraMap K C) (P.coeff m) * x ^ (m + q))).sum) := by
    apply Finset.sum_congr rfl
    intro m _
    unfold newtonSum
    rw [← Multiset.sum_map_mul_left]
  rw [h_pull, finset_range_multiset_sum_swap]
  have hinner : ∀ x : C,
      (Finset.range (P.natDegree + 1)).sum (fun m =>
        (algebraMap K C) (P.coeff m) * x ^ (m + q)) = x ^ q * Q.eval x := by
    intro x
    rw [Polynomial.eval_eq_sum_range'
      (show Q.natDegree < P.natDegree + 1 by omega) x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [hQ_coeff, pow_add]
    ring
  simp_rw [hinner]
  exact hsum_eval

omit [IsAlgClosed C] in
/-- **Trace identity** (`q = 0` case of `newtonSum_orthogonality`):
    `∑_{m=0}^{p} a_m · N_m = 0`. -/
lemma newtonSum_trace_identity (P : K[X]) :
    (Finset.range (P.natDegree + 1)).sum (fun m =>
        (algebraMap K C) (P.coeff m) * newtonSum P m) = 0 := by
  have h := newtonSum_orthogonality (C := C) P 0
  simpa using h

omit [IsAlgClosed C] in
/-- The j-based Newton recurrence on a multiset of roots in `C`. -/
private lemma proposition_4_8_aux (s : Multiset C) (a_p : C) (j : ℕ)
    (hj : j ≤ s.card) :
    (j : C) * (Polynomial.C a_p *
        (s.map (fun x => X - Polynomial.C x)).prod).coeff j =
      (Finset.Ico j (s.card + 1)).sum (fun m =>
        (Polynomial.C a_p *
            (s.map (fun x => X - Polynomial.C x)).prod).coeff m *
          (s.map (fun x => x ^ (m - j))).sum) := by
  induction s using Multiset.induction generalizing j with
  | empty =>
    -- s = ∅, |s| = 0, so j ≤ 0 → j = 0.
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    simp
  | cons y t ih =>
    -- s' = y ::ₘ t. Set p := t.card.
    set p := t.card with hp_def
    set Q : C[X] := Polynomial.C a_p * (t.map (fun x => X - Polynomial.C x)).prod
      with hQ_def
    have hQ' : Polynomial.C a_p *
        ((y ::ₘ t).map (fun x => X - Polynomial.C x)).prod =
        (X - Polynomial.C y) * Q := by
      rw [Multiset.map_cons, Multiset.prod_cons, hQ_def]; ring
    rw [hQ']
    have hcard : (y ::ₘ t).card = p + 1 := by rw [Multiset.card_cons]
    rw [hcard]
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · -- j = 0: trace identity. RHS = Σ_x Q'.eval(x) = 0.
      subst hj0
      simp only [Nat.cast_zero, zero_mul, Nat.sub_zero]
      symm
      -- Bound Q.natDegree by p, Q'.natDegree by p + 1.
      have hQ_natDeg : Q.natDegree ≤ p := by
        rw [hQ_def]
        calc (Polynomial.C a_p *
                (t.map (fun x => X - Polynomial.C x)).prod).natDegree
            ≤ (Polynomial.C a_p).natDegree +
                (t.map (fun x => X - Polynomial.C x)).prod.natDegree :=
              natDegree_mul_le
          _ ≤ 0 + p := by
              gcongr
              · exact (natDegree_C a_p).le
              · rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
          _ = p := by ring
      have hQ'_natDeg : ((X - Polynomial.C y) * Q).natDegree ≤ p + 1 := by
        calc ((X - Polynomial.C y) * Q).natDegree
            ≤ (X - Polynomial.C y).natDegree + Q.natDegree :=
              natDegree_mul_le
          _ ≤ 1 + p := by gcongr; exact natDegree_X_sub_C_le _
          _ = p + 1 := by ring
      -- Each x ∈ y ::ₘ t is a root of Q'.
      have heval : ∀ x ∈ (y ::ₘ t),
          ((X - Polynomial.C y) * Q).eval x = 0 := by
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hxt
        · simp
        · rw [eval_mul]
          have hroot : (t.map (fun a => X - Polynomial.C a)).prod.eval x = 0 := by
            rw [eval_multiset_prod]
            apply Multiset.prod_eq_zero
            rw [Multiset.mem_map]
            refine ⟨X - Polynomial.C x, ?_, by simp⟩
            rw [Multiset.mem_map]
            exact ⟨x, hxt, rfl⟩
          rw [show eval x Q = 0 from by
            rw [hQ_def, eval_mul, hroot, mul_zero]]
          ring
      -- Σ over s' of Q'.eval = 0.
      have hsum_eval : ((y ::ₘ t).map
          (fun x => ((X - Polynomial.C y) * Q).eval x)).sum = 0 := by
        apply Multiset.sum_eq_zero
        intro v hv
        rw [Multiset.mem_map] at hv
        obtain ⟨x, hx, rfl⟩ := hv
        exact heval x hx
      -- Apply Finset.sum_congr to pull Q'.coeff into multiset.
      have h_pull : (Finset.Ico 0 (p + 1 + 1)).sum (fun m =>
            ((X - Polynomial.C y) * Q).coeff m *
              ((y ::ₘ t).map (fun x => x ^ m)).sum) =
          (Finset.Ico 0 (p + 1 + 1)).sum (fun m =>
            ((y ::ₘ t).map (fun x =>
              ((X - Polynomial.C y) * Q).coeff m * x ^ m)).sum) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [← Multiset.sum_map_mul_left]
      rw [h_pull, finset_Ico_multiset_sum_swap]
      -- Inner sum at x equals Q'.eval x.
      have hinner : ∀ x : C,
          (Finset.Ico 0 (p + 1 + 1)).sum (fun m =>
            ((X - Polynomial.C y) * Q).coeff m * x ^ m) =
          ((X - Polynomial.C y) * Q).eval x := by
        intro x
        rw [← Finset.range_eq_Ico]
        exact (Polynomial.eval_eq_sum_range'
          (lt_of_le_of_lt hQ'_natDeg (by omega)) x).symm
      simp_rw [hinner]
      exact hsum_eval
    · -- j ≥ 1: split on j ≤ p vs j = p+1.
      -- Bound Q.natDegree ≤ p.
      have hQ_natDeg : Q.natDegree ≤ p := by
        rw [hQ_def]
        calc (Polynomial.C a_p *
                (t.map (fun x => X - Polynomial.C x)).prod).natDegree
            ≤ (Polynomial.C a_p).natDegree +
                (t.map (fun x => X - Polynomial.C x)).prod.natDegree :=
              natDegree_mul_le
          _ ≤ 0 + p := by
              gcongr
              · exact (natDegree_C a_p).le
              · rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
          _ = p := by ring
      rcases Nat.lt_or_ge p j with hjp | hjp
      · -- p < j, combined with j ≤ p+1: j = p + 1 (boundary case).
        have hj_eq : j = p + 1 := by omega
        subst hj_eq
        -- Q.coeff (p+1) = 0 since Q.natDegree ≤ p.
        have hQ_p1 : Q.coeff (p + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        -- Q'.coeff (p+1) = Q.coeff p.
        have hQ'_p1 : ((X - Polynomial.C y) * Q).coeff (p + 1) = Q.coeff p := by
          rw [coeff_X_sub_C_mul, hQ_p1, mul_zero, sub_zero]
        rw [hQ'_p1]
        -- RHS sum has the singleton {p+1}.
        rw [show Finset.Ico (p + 1) (p + 1 + 1) = ({p + 1} : Finset ℕ) from by
          ext m
          rw [Finset.mem_Ico, Finset.mem_singleton]
          omega]
        rw [Finset.sum_singleton, hQ'_p1]
        -- (y ::ₘ t).map (·^0) sums to (p+1) via map_const + sum_replicate.
        simp only [Nat.sub_self, pow_zero, Multiset.map_const',
          Multiset.sum_replicate, Multiset.card_cons]
        rw [hp_def]
        push_cast
        ring
      · -- j ≤ p: substitute Q'.coeff and N_{m-j}(s'), then IH at j and j-1.
        have hQ'_j : ((X - Polynomial.C y) * Q).coeff j =
            Q.coeff (j - 1) - y * Q.coeff j := by
          have h := @coeff_X_sub_C_mul C _ Q y (j - 1)
          rw [show (j - 1) + 1 = j from by omega] at h
          exact h
        rw [hQ'_j]
        have hQ_p1 : Q.coeff (p + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have ihj := ih j hjp
        have ihj' := ih (j - 1) (by omega)
        -- Substitute and expand each summand into 4 terms via `ring`.
        have hsub : (Finset.Ico j (p + 1 + 1)).sum (fun m =>
              ((X - Polynomial.C y) * Q).coeff m *
                ((y ::ₘ t).map (fun x => x ^ (m - j))).sum) =
            (Finset.Ico j (p + 1 + 1)).sum (fun m =>
              (Q.coeff (m - 1) * y ^ (m - j) +
                Q.coeff (m - 1) * (t.map (fun x => x ^ (m - j))).sum) -
              y * Q.coeff m * y ^ (m - j) -
              y * Q.coeff m * (t.map (fun x => x ^ (m - j))).sum) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mem_Ico] at hm
          have hm1 : 1 ≤ m := by omega
          rw [show m = (m - 1) + 1 from by omega, coeff_X_sub_C_mul,
              show (m - 1) + 1 - 1 = m - 1 from by omega,
              show (m - 1) + 1 - j = m - j from by omega,
              Multiset.map_cons, Multiset.sum_cons]
          ring
        rw [hsub]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            Finset.sum_add_distrib]
        -- Sum_B = (j - 1) * Q.coeff (j - 1) via reindex (Finset.sum_nbij') + IH at j-1.
        have hSumB : (Finset.Ico j (p + 1 + 1)).sum (fun m =>
              Q.coeff (m - 1) * (t.map (fun x => x ^ (m - j))).sum) =
            ((j - 1 : ℕ) : C) * Q.coeff (j - 1) := by
          have h_bij : (Finset.Ico j (p + 1 + 1)).sum (fun m =>
                Q.coeff (m - 1) * (t.map (fun x => x ^ (m - j))).sum) =
              (Finset.Ico (j - 1) (p + 1)).sum (fun n =>
                Q.coeff n * (t.map (fun x => x ^ (n - (j - 1)))).sum) := by
            apply Finset.sum_nbij' (fun m => m - 1) (fun n => n + 1)
            · intro m hm
              rw [Finset.mem_Ico] at hm ⊢; omega
            · intro n hn
              rw [Finset.mem_Ico] at hn ⊢; omega
            · intro m hm
              rw [Finset.mem_Ico] at hm; omega
            · intro n hn
              rw [Finset.mem_Ico] at hn; omega
            · intro m hm
              rw [Finset.mem_Ico] at hm
              rw [show m - 1 - (j - 1) = m - j from by omega]
          rw [h_bij]
          exact ihj'.symm
        -- Sum_D = y * j * Q.coeff j (drop m=p+1 term, apply IH at j).
        have hSumD : (Finset.Ico j (p + 1 + 1)).sum (fun m =>
              y * Q.coeff m * (t.map (fun x => x ^ (m - j))).sum) =
            y * ((j : ℕ) : C) * Q.coeff j := by
          rw [Finset.sum_Ico_succ_top (show j ≤ p + 1 from by omega)]
          rw [show y * Q.coeff (p + 1) *
                (t.map (fun x => x ^ (p + 1 - j))).sum = 0 from by
            rw [hQ_p1]; ring]
          rw [add_zero, show (Finset.Ico j (p + 1)).sum (fun m =>
                y * Q.coeff m * (t.map (fun x => x ^ (m - j))).sum) =
              y * (Finset.Ico j (p + 1)).sum (fun m =>
                Q.coeff m * (t.map (fun x => x ^ (m - j))).sum) from by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl
            intro m _; ring]
          rw [← ihj]; ring
        -- Sum_A reindexed to Ico (j-1) (p+1).
        have hSumA : (Finset.Ico j (p + 1 + 1)).sum (fun m =>
              Q.coeff (m - 1) * y ^ (m - j)) =
            (Finset.Ico (j - 1) (p + 1)).sum (fun m =>
              Q.coeff m * y ^ (m - (j - 1))) := by
          apply Finset.sum_nbij' (fun m => m - 1) (fun n => n + 1)
          · intro m hm
            rw [Finset.mem_Ico] at hm ⊢; omega
          · intro n hn
            rw [Finset.mem_Ico] at hn ⊢; omega
          · intro m hm
            rw [Finset.mem_Ico] at hm; omega
          · intro n hn
            rw [Finset.mem_Ico] at hn; omega
          · intro m hm
            rw [Finset.mem_Ico] at hm
            rw [show m - 1 - (j - 1) = m - j from by omega]
        -- Sum_C dropped to Ico j (p+1), with y absorbed.
        have hSumC : (Finset.Ico j (p + 1 + 1)).sum (fun m =>
              y * Q.coeff m * y ^ (m - j)) =
            (Finset.Ico j (p + 1)).sum (fun m =>
              Q.coeff m * y ^ (m - (j - 1))) := by
          rw [Finset.sum_Ico_succ_top (show j ≤ p + 1 from by omega)]
          rw [show y * Q.coeff (p + 1) * y ^ (p + 1 - j) = 0 from by
            rw [hQ_p1]; ring]
          rw [add_zero]
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mem_Ico] at hm
          rw [show m - (j - 1) = m - j + 1 from by omega, pow_succ]
          ring
        -- Telescope: Sum_A - Sum_C = Q.coeff (j - 1).
        have hTelescope : (Finset.Ico (j - 1) (p + 1)).sum (fun m =>
              Q.coeff m * y ^ (m - (j - 1))) -
            (Finset.Ico j (p + 1)).sum (fun m =>
              Q.coeff m * y ^ (m - (j - 1))) =
            Q.coeff (j - 1) := by
          have h_union : Finset.Ico (j - 1) (p + 1) =
              insert (j - 1) (Finset.Ico j (p + 1)) := by
            ext k
            rw [Finset.mem_insert, Finset.mem_Ico, Finset.mem_Ico]
            omega
          rw [h_union, Finset.sum_insert (by rw [Finset.mem_Ico]; omega)]
          rw [show (j - 1) - (j - 1) = 0 from by omega, pow_zero, mul_one]
          ring
        rw [hSumA, hSumB, hSumC, hSumD]
        have hcast : ((j - 1 : ℕ) : C) = ((j : ℕ) : C) - 1 :=
          Nat.cast_pred hj1
        rw [hcast]
        linear_combination -hTelescope

/-- **BPR Proposition 4.8** (Newton's coefficient recurrence, j-form).
    For `P : K[X]` and `j ≤ p = P.natDegree`,
    `j · a_j = ∑_{m=j}^{p} a_m · N_{m-j}`. -/
theorem proposition_4_8 (P : K[X]) (j : ℕ) (hj : j ≤ P.natDegree) :
    (j : C) * (algebraMap K C) (P.coeff j) =
      (Finset.Ico j (P.natDegree + 1)).sum (fun m =>
        (algebraMap K C) (P.coeff m) * newtonSum P (m - j)) := by
  classical
  by_cases hP : P = 0
  · subst hP
    simp [newtonSum]
  -- Lift to C[X]: Q := P.map (algebraMap K C).
  set Q : C[X] := P.map (algebraMap K C) with hQ_def
  have hf_inj : Function.Injective (algebraMap K C) := (algebraMap K C).injective
  have hQ_natDeg : Q.natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf_inj P
  have hQ_coeff : ∀ m, Q.coeff m = (algebraMap K C) (P.coeff m) := fun m =>
    Polynomial.coeff_map (algebraMap K C) m
  have hQ_leading : Q.leadingCoeff = (algebraMap K C) P.leadingCoeff :=
    Polynomial.leadingCoeff_map_of_injective hf_inj P
  have hQ_roots_card : Q.roots.card = Q.natDegree := by
    rw [hQ_def, hQ_natDeg]
    exact IsAlgClosed.card_roots_map_eq_natDegree_of_injective P hf_inj
  -- Q = C(leadingCoeff) * (Q.roots.map (X - C ·)).prod.
  have hQ_factor : Q = Polynomial.C Q.leadingCoeff *
      (Q.roots.map (fun x => X - Polynomial.C x)).prod :=
    (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hQ_roots_card).symm
  -- Apply aux with s := Q.roots, a_p := Q.leadingCoeff.
  have h_aux := proposition_4_8_aux Q.roots Q.leadingCoeff j
    (by rw [hQ_roots_card, hQ_natDeg]; exact hj)
  -- Translate.
  rw [← hQ_factor] at h_aux
  rw [hQ_roots_card, hQ_natDeg] at h_aux
  rw [hQ_coeff] at h_aux
  -- The RHS sums match: `newtonSum P k = (Q.roots.map (·^k)).sum` by definition.
  convert h_aux using 1
  apply Finset.sum_congr rfl
  intro m _
  rw [hQ_coeff]
  rfl

/-- **BPR Proposition 4.8** (logarithmic-derivative form). For
    non-constant `P` and any `N`, the polynomial truncation
    `X^N · P' - P · ∑_{i=0}^{N-1} N_i · X^{N-1-i}`
    has degree strictly less than `P.natDegree`, expressing the formal
    series identity `P'/P = ∑_{i=0}^{∞} N_i / X^{i+1}` modulo terms of
    order `X^{-(N+1)}` and higher (after clearing the `P · X^N` factor).

    Equivalent to `proposition_4_8`: matching the coefficient of `X^k`
    for each `k ≥ P.natDegree` gives Newton's recurrence at `j = k − N + 1`.
    -/
theorem proposition_4_8_series (P : K[X]) (hP : 0 < P.natDegree) (N : ℕ) :
    ((Polynomial.X : C[X])^N * (P.map (algebraMap K C)).derivative -
     (P.map (algebraMap K C)) *
       (Finset.range N).sum (fun i =>
         Polynomial.C (newtonSum P i) * (Polynomial.X : C[X])^(N - 1 - i))
    ).natDegree < P.natDegree := by
  classical
  set Q : C[X] := P.map (algebraMap K C) with hQ_def
  have hf_inj : Function.Injective (algebraMap K C) := (algebraMap K C).injective
  have hQ_natDeg : Q.natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf_inj P
  have hQ_coeff : ∀ m, Q.coeff m = (algebraMap K C) (P.coeff m) := fun m =>
    Polynomial.coeff_map (algebraMap K C) m
  have hQ_coeff_zero : ∀ m, P.natDegree < m → Q.coeff m = 0 := fun m hm =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ_natDeg]; exact hm)
  -- It suffices to show every coefficient at index ≥ P.natDegree vanishes.
  suffices h : ∀ k, P.natDegree ≤ k →
      ((Polynomial.X : C[X])^N * Q.derivative -
       Q * (Finset.range N).sum (fun i =>
         Polynomial.C (newtonSum P i) * (Polynomial.X : C[X])^(N - 1 - i))
      ).coeff k = 0 by
    have h_le : ((Polynomial.X : C[X])^N * Q.derivative -
        Q * (Finset.range N).sum (fun i =>
          Polynomial.C (newtonSum P i) *
            (Polynomial.X : C[X])^(N - 1 - i))).natDegree ≤ P.natDegree - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      exact h n (by omega)
    omega
  intro k hk
  rw [Polynomial.coeff_sub]
  -- Compute (X^N * Q.derivative).coeff k.
  have hT1 : ((Polynomial.X : C[X])^N * Q.derivative).coeff k =
      if N ≤ k then ((k - N + 1 : ℕ) : C) * Q.coeff (k - N + 1) else 0 := by
    rw [show (Polynomial.X : C[X])^N * Q.derivative =
        Q.derivative * Polynomial.X^N from by ring]
    rw [Polynomial.coeff_mul_X_pow']
    split_ifs with h
    · rw [Polynomial.coeff_derivative]; push_cast; ring
    · rfl
  -- Compute (Q * Σ N_i X^{N-1-i}).coeff k.
  have hT2 : (Q * (Finset.range N).sum (fun i =>
        Polynomial.C (newtonSum P i) * (Polynomial.X : C[X])^(N - 1 - i))).coeff k =
      (Finset.range N).sum (fun i =>
        newtonSum P i *
          (if N - 1 - i ≤ k then Q.coeff (k - (N - 1 - i)) else 0)) := by
    rw [Finset.mul_sum, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i _
    rw [show Q * (Polynomial.C (newtonSum P i) *
        (Polynomial.X : C[X])^(N - 1 - i)) =
        Polynomial.C (newtonSum P i) *
          (Q * (Polynomial.X : C[X])^(N - 1 - i)) from by ring]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
  rw [hT1, hT2]
  by_cases hkN : N ≤ k
  · -- Case k ≥ N: use Prop 4.8 at j = k - N + 1.
    rw [if_pos hkN]
    -- Drop the if from T2 (always true when k ≥ N).
    have hT2_simp : (Finset.range N).sum (fun i =>
          newtonSum P i *
            (if N - 1 - i ≤ k then Q.coeff (k - (N - 1 - i)) else 0)) =
        (Finset.Ico (k - N + 1) (k + 1)).sum (fun m =>
          Q.coeff m * newtonSum P (m - (k - N + 1))) := by
      rw [show (Finset.range N).sum (fun i =>
            newtonSum P i *
              (if N - 1 - i ≤ k then Q.coeff (k - (N - 1 - i)) else 0)) =
          (Finset.range N).sum (fun i =>
            newtonSum P i * Q.coeff (k - N + 1 + i)) from by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have : N - 1 - i ≤ k := by omega
        rw [if_pos this]
        congr 2; omega]
      apply Finset.sum_nbij' (fun i => i + (k - N + 1)) (fun m => m - (k - N + 1))
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [Finset.mem_Ico]; omega
      · intro m hm
        rw [Finset.mem_Ico] at hm
        rw [Finset.mem_range]; omega
      · intro i hi
        rw [Finset.mem_range] at hi; omega
      · intro m hm
        rw [Finset.mem_Ico] at hm; omega
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [show (i + (k - N + 1)) - (k - N + 1) = i from by omega]
        rw [show k - N + 1 + i = i + (k - N + 1) from by omega]
        ring
    rw [hT2_simp]
    by_cases hjP : k - N + 1 ≤ P.natDegree
    · -- j ≤ P.natDegree: Prop 4.8 applies.
      have hProp48 := proposition_4_8 (C := C) P (k - N + 1) hjP
      -- Convert sum from Ico (k-N+1) (P.natDegree+1) to Ico (k-N+1) (k+1) via Q.coeff = 0 outside.
      have h_eq_sums : (Finset.Ico (k - N + 1) (P.natDegree + 1)).sum (fun m =>
            Q.coeff m * newtonSum P (m - (k - N + 1))) =
          (Finset.Ico (k - N + 1) (k + 1)).sum (fun m =>
            Q.coeff m * newtonSum P (m - (k - N + 1))) := by
        rw [show Finset.Ico (k - N + 1) (k + 1) =
            Finset.Ico (k - N + 1) (P.natDegree + 1) ∪
              Finset.Ico (P.natDegree + 1) (k + 1) from
            (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm]
        rw [Finset.sum_union (by
          rw [Finset.disjoint_left]
          intro m hm1 hm2
          rw [Finset.mem_Ico] at hm1 hm2; omega)]
        rw [show (Finset.Ico (P.natDegree + 1) (k + 1)).sum (fun m =>
                Q.coeff m * newtonSum P (m - (k - N + 1))) = 0 from by
            apply Finset.sum_eq_zero
            intro m hm
            rw [Finset.mem_Ico] at hm
            rw [hQ_coeff_zero m hm.1, zero_mul]]
        ring
      rw [← h_eq_sums]
      -- Convert Q.coeff to algebraMap (P.coeff) to match hProp48.
      simp_rw [hQ_coeff]
      rw [← hProp48]
      ring
    · -- j > P.natDegree: Q.coeff j = 0 and all Q.coeff (m) for m in Ico j (k+1) are 0.
      push Not at hjP
      have h_Q_j : Q.coeff (k - N + 1) = 0 := hQ_coeff_zero _ hjP
      rw [h_Q_j]
      rw [show (Finset.Ico (k - N + 1) (k + 1)).sum (fun m =>
            Q.coeff m * newtonSum P (m - (k - N + 1))) = 0 from by
        apply Finset.sum_eq_zero
        intro m hm
        rw [Finset.mem_Ico] at hm
        rw [hQ_coeff_zero m (by omega), zero_mul]]
      ring
  · -- Case k < N: T1 = 0, T2 = 0 via orthogonality.
    rw [if_neg hkN]
    push Not at hkN
    rw [zero_sub, neg_eq_zero]
    -- T2 simplifies via reindex + orthogonality at q = N - 1 - k.
    set q := N - 1 - k with hq_def
    have hT2_eq : (Finset.range N).sum (fun i =>
          newtonSum P i *
            (if N - 1 - i ≤ k then Q.coeff (k - (N - 1 - i)) else 0)) =
        (Finset.range (P.natDegree + 1)).sum (fun m =>
          (algebraMap K C) (P.coeff m) * newtonSum P (m + q)) := by
      -- Pre-process: zero out i < q, simplify when i ≥ q.
      rw [show (Finset.range N).sum (fun i =>
            newtonSum P i *
              (if N - 1 - i ≤ k then Q.coeff (k - (N - 1 - i)) else 0)) =
          (Finset.Ico q N).sum (fun i =>
            newtonSum P i * Q.coeff (i - q)) from by
        rw [show Finset.range N = Finset.Ico 0 q ∪ Finset.Ico q N from by
          rw [Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico
            (Nat.zero_le _) (by omega : q ≤ N)]]
        rw [Finset.sum_union (by
          rw [Finset.disjoint_left]
          intro i hi1 hi2
          rw [Finset.mem_Ico] at hi1 hi2; omega)]
        rw [show (Finset.Ico 0 q).sum (fun i =>
              newtonSum P i *
                (if N - 1 - i ≤ k then Q.coeff (k - (N - 1 - i)) else 0)) = 0 from by
          apply Finset.sum_eq_zero
          intro i hi
          rw [Finset.mem_Ico] at hi
          have : ¬ (N - 1 - i ≤ k) := by omega
          rw [if_neg this]; ring]
        rw [zero_add]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_Ico] at hi
        have : N - 1 - i ≤ k := by omega
        rw [if_pos this]
        congr 2; omega]
      -- Reindex i = m + q, m ∈ [0, N - q) = [0, k + 1)
      rw [show (Finset.Ico q N).sum (fun i =>
            newtonSum P i * Q.coeff (i - q)) =
          (Finset.range (k + 1)).sum (fun m =>
            Q.coeff m * newtonSum P (m + q)) from by
        apply Finset.sum_nbij' (fun i => i - q) (fun m => m + q)
        · intro i hi
          rw [Finset.mem_Ico] at hi
          rw [Finset.mem_range]; omega
        · intro m hm
          rw [Finset.mem_range] at hm
          rw [Finset.mem_Ico]; omega
        · intro i hi
          rw [Finset.mem_Ico] at hi; omega
        · intro m hm
          rw [Finset.mem_range] at hm; omega
        · intro i hi
          rw [Finset.mem_Ico] at hi
          rw [show i - q + q = i from by omega]
          ring]
      -- Extend range to P.natDegree + 1 (extra terms have Q.coeff = 0).
      rw [show (Finset.range (k + 1)).sum (fun m =>
            Q.coeff m * newtonSum P (m + q)) =
          (Finset.range (P.natDegree + 1)).sum (fun m =>
            Q.coeff m * newtonSum P (m + q)) from by
        simp_rw [Finset.range_eq_Ico]
        rw [show Finset.Ico 0 (k + 1) =
              Finset.Ico 0 (P.natDegree + 1) ∪ Finset.Ico (P.natDegree + 1) (k + 1) from
            (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega)).symm]
        rw [Finset.sum_union (by
          rw [Finset.disjoint_left]
          intro m hm1 hm2
          rw [Finset.mem_Ico] at hm1 hm2; omega)]
        rw [show (Finset.Ico (P.natDegree + 1) (k + 1)).sum (fun m =>
              Q.coeff m * newtonSum P (m + q)) = 0 from by
          apply Finset.sum_eq_zero
          intro m hm
          rw [Finset.mem_Ico] at hm
          rw [hQ_coeff_zero m hm.1, zero_mul]]
        ring]
      -- Use hQ_coeff to convert Q.coeff m to (algebraMap K C) (P.coeff m).
      apply Finset.sum_congr rfl
      intro m _
      rw [hQ_coeff]
    rw [hT2_eq]
    exact newtonSum_orthogonality P q

end Azurite.BPR.Chapter4
