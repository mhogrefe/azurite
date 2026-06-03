import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygon

/-! # BPR §2.6 — existence of the Newton polygon

Every polynomial `P ∈ R⟨⟨ε⟩⟩[X]` with nonzero constant term `P.coeff 0 ≠ 0` has a Newton polygon
(`exists_isNewtonPolygon`). This is the lower convex hull of the column points `M_i = (i, o(ā_i))`
(`i ∈ support`), and is built by a Jarvis march (gift-wrapping): starting at column `0`, the next
vertex is the column minimizing the slope from the current vertex.

The construction carries a **supporting-line invariant** that turns the otherwise global
"every diagram point lies on or above every edge" property into a self-propagating local one: if
the line of slope `s` through the current vertex `a` lies below every column point, then the
minimal-slope next vertex `b` has outgoing slope `s' ≥ s`, the edge `[a, b]` lies below every
column point (right points by minimality, left points because `s' ≥ s` and the lines agree at
`a`), and this *is* the invariant at `b`. Lifting from column bottom points to all diagram points
is immediate (`r ≥ o(ā_i)`), and convexity of the vertex chain follows since each vertex is a
diagram point above the previous edge.

The hypothesis `P.coeff 0 ≠ 0` is necessary: `IsNewtonPolygon` forces a vertex at column `0`
(`head_eq`), which requires `o(ā₀)` finite; when `X ∣ P` one peels off `0` as a root first.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- The order of the `i`-th coefficient as a rational — the `y`-coordinate of the bottom point of
column `i` (junk value `0` when `ā_i = 0`, which does not occur on the support). -/
noncomputable def colOrd (P : Polynomial (PuiseuxSeries R)) (i : ℕ) : ℚ :=
  HahnSeries.order ((P.coeff i : PuiseuxSeries R) : HahnSeries ℚ R)

/-- On the support, `puiseuxOrder` of the coefficient is the finite value `colOrd`. -/
theorem puiseuxOrder_eq_colOrd {P : Polynomial (PuiseuxSeries R)} {i : ℕ} (hi : P.coeff i ≠ 0) :
    puiseuxOrder R (P.coeff i) = (colOrd P i : WithTop ℚ) := by
  have hcoe : ((P.coeff i : PuiseuxSeries R) : HahnSeries ℚ R) ≠ 0 := by
    rw [Ne, ZeroMemClass.coe_eq_zero]; exact hi
  rw [puiseuxOrder, colOrd]
  exact (HahnSeries.order_eq_orderTop_of_ne_zero hcoe).symm

/-- **Convexity from edge-support.** If each vertex of `M` is a column point `(i, f i)` with
`i ∈ S`, and every edge of `M` lies on or above every column point, then the vertex chain turns
the right way: each vertex lies on or above the previous edge. -/
theorem isChain_zip_tail_of_colChain {S : Finset ℕ} {f : ℕ → ℚ} :
    ∀ M : List (ℕ × ℚ), (∀ V ∈ M, V.2 = f V.1 ∧ V.1 ∈ S) →
      M.IsChain (fun A B => ∀ i ∈ S, OnOrAbove A B (i, f i)) →
      (M.zip M.tail).IsChain (fun e₁ e₂ : (ℕ × ℚ) × (ℕ × ℚ) => OnOrAbove e₁.1 e₁.2 e₂.2)
  | [], _, _ => List.isChain_nil
  | [_], _, _ => List.isChain_nil
  | a :: b :: l, hcol, hch => by
      have hchbl : (b :: l).IsChain (fun A B => ∀ i ∈ S, OnOrAbove A B (i, f i)) :=
        (List.isChain_cons.mp hch).2
      have hcolbl : ∀ V ∈ (b :: l), V.2 = f V.1 ∧ V.1 ∈ S :=
        fun V hV => hcol V (List.mem_cons_of_mem _ hV)
      have ih := isChain_zip_tail_of_colChain (b :: l) hcolbl hchbl
      have habrel : ∀ i ∈ S, OnOrAbove a b (i, f i) := by
        have h := (List.isChain_cons.mp hch).1
        rw [List.head?_cons] at h
        exact h b rfl
      rw [show (a :: b :: l).zip (a :: b :: l).tail = (a, b) :: (b :: l).zip (b :: l).tail from by
        rw [List.tail_cons, List.zip_cons_cons, List.tail_cons], List.isChain_cons]
      refine ⟨fun e he => ?_, ih⟩
      cases l with
      | nil => simp at he
      | cons c l' =>
          rw [List.tail_cons, List.zip_cons_cons, List.head?_cons, Option.mem_some_iff] at he
          subst he
          obtain ⟨hc2, hc1⟩ := hcol c (by simp)
          have := habrel c.1 hc1
          rwa [show (c.1, f c.1) = c from Prod.ext rfl hc2.symm] at this

/-- **The lower-hull construction (Jarvis march).** From a vertex `a ∈ S` whose supporting line of
slope `s` lies below every column point of `S`, there is a vertex chain from `a` to `N`
satisfying the Newton-polygon conditions (over column bottom points). Proven by strong induction
on the remaining span `N − a`. -/
theorem lower_hull_exists (S : Finset ℕ) (f : ℕ → ℚ) (N : ℕ)
    (hSN : ∀ i ∈ S, i ≤ N) (hNS : N ∈ S) :
    ∀ d : ℕ, ∀ a : ℕ, a ∈ S → N - a ≤ d → ∀ s : ℚ,
      (∀ i ∈ S, f a + s * ((i : ℚ) - a) ≤ f i) →
      ∃ M : List (ℕ × ℚ), M.head? = some (a, f a) ∧ M.getLast? = some (N, f N)
        ∧ (∀ V ∈ M, V.2 = f V.1 ∧ V.1 ∈ S)
        ∧ M.IsChain (fun A B => A.1 < B.1)
        ∧ M.IsChain (fun A B : ℕ × ℚ => ∀ i ∈ S, OnOrAbove A B (i, f i)) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d IH =>
    intro a haS hda s hs
    rcases eq_or_lt_of_le (hSN a haS) with haN | haN
    · subst haN
      exact ⟨[(a, f a)], rfl, rfl, by
        intro V hV; rw [List.mem_singleton] at hV; subst hV; exact ⟨rfl, haS⟩,
        List.isChain_singleton _, List.isChain_singleton _⟩
    · -- pick the minimal-slope next vertex `b`
      have hTne : (S.filter (a < ·)).Nonempty := ⟨N, Finset.mem_filter.mpr ⟨hNS, haN⟩⟩
      obtain ⟨b, hbT, hbmin⟩ :=
        (S.filter (a < ·)).exists_min_image (fun j => newtonSlope (a, f a) (j, f j)) hTne
      have hbS : b ∈ S := (Finset.mem_filter.mp hbT).1
      have hab : a < b := (Finset.mem_filter.mp hbT).2
      have hbN : b ≤ N := hSN b hbS
      set sout := newtonSlope (a, f a) (b, f b) with hsout
      have hrunb : (0 : ℚ) < (b : ℚ) - a := by
        have : (a : ℚ) < b := by exact_mod_cast hab
        linarith
      -- `sout * (b - a) = f b - f a`
      have hfb : f a + sout * ((b : ℚ) - a) = f b := by
        have := newtonSlope_mul_sub (p := (a, f a)) (q := (b, f b)) (ne_of_lt hab)
        rw [hsout]; simp only at this; linarith [this]
      -- the edge `[a, b]` lies below every column point
      have hedge : ∀ i ∈ S, f a + sout * ((i : ℚ) - a) ≤ f i := by
        intro i hiS
        rcases lt_trichotomy i a with hia | hia | hia
        · have hsle : s ≤ sout := by
            rw [hsout, newtonSlope_def, le_div_iff₀ hrunb]
            simp only
            linarith [hs b hbS]
          have hia' : (i : ℚ) - a < 0 := by
            have : (i : ℚ) < a := by exact_mod_cast hia
            linarith
          have hmul : sout * ((i : ℚ) - a) ≤ s * ((i : ℚ) - a) :=
            mul_le_mul_of_nonpos_right hsle (le_of_lt hia')
          linarith [hs i hiS, hmul]
        · subst hia; simp
        · have hiT : i ∈ S.filter (a < ·) := Finset.mem_filter.mpr ⟨hiS, hia⟩
          have hmin := hbmin i hiT
          have hrun : (0 : ℚ) < (i : ℚ) - a := by
            have : (a : ℚ) < i := by exact_mod_cast hia
            linarith
          have hsi := newtonSlope_mul_sub (p := (a, f a)) (q := (i, f i)) (ne_of_lt hia)
          have hmul : sout * ((i : ℚ) - a) ≤ newtonSlope (a, f a) (i, f i) * ((i : ℚ) - a) :=
            mul_le_mul_of_nonneg_right hmin (le_of_lt hrun)
          simp only at hsi
          linarith [hmul, hsi]
      -- the new supporting-line invariant at `b`
      have hinv : ∀ i ∈ S, f b + sout * ((i : ℚ) - b) ≤ f i := by
        intro i hiS
        have hdist : sout * ((i : ℚ) - b) + sout * ((b : ℚ) - a) = sout * ((i : ℚ) - a) := by ring
        linarith [hedge i hiS, hfb, hdist]
      -- recurse from `b`
      obtain ⟨Mb, hMb_head, hMb_last, hMb_col, hMb_mono, hMb_diag⟩ :=
        IH (N - b) (by omega) b hbS (le_refl _) sout hinv
      have hMb_ne : Mb ≠ [] := by intro h; rw [h] at hMb_head; simp at hMb_head
      refine ⟨(a, f a) :: Mb, rfl, ?_, ?_, ?_, ?_⟩
      · rw [List.getLast?_cons_of_ne_nil hMb_ne]; exact hMb_last
      · intro V hV
        rcases List.mem_cons.mp hV with rfl | hV
        · exact ⟨rfl, haS⟩
        · exact hMb_col V hV
      · rw [List.isChain_cons]
        refine ⟨?_, hMb_mono⟩
        rw [hMb_head]; intro y hy; rw [Option.mem_some_iff] at hy; subst hy; exact hab
      · rw [List.isChain_cons]
        refine ⟨?_, hMb_diag⟩
        rw [hMb_head]; intro y hy; rw [Option.mem_some_iff] at hy; subst hy
        intro i hiS
        rw [onOrAbove_iff, ← hsout]
        simp only
        linarith [hedge i hiS]

/-- **Existence of the Newton polygon.** Every polynomial with nonzero constant term has a Newton
polygon (the lower convex hull of its column points). -/
theorem exists_isNewtonPolygon (P : Polynomial (PuiseuxSeries R)) (h0 : P.coeff 0 ≠ 0) :
    ∃ M, IsNewtonPolygon P M := by
  classical
  have hP : P ≠ 0 := fun h => h0 (by rw [h, coeff_zero])
  have hS0 : (0 : ℕ) ∈ P.support := mem_support_iff.mpr h0
  have hSN_mem : P.natDegree ∈ P.support :=
    mem_support_iff.mpr (by rw [← leadingCoeff]; exact leadingCoeff_ne_zero.mpr hP)
  have hSN : ∀ i ∈ P.support, i ≤ P.natDegree :=
    fun i hi => le_natDegree_of_ne_zero (mem_support_iff.mp hi)
  -- seed supporting slope at column `0`
  have seed : ∃ s : ℚ, ∀ i ∈ P.support, colOrd P 0 + s * ((i : ℚ) - 0) ≤ colOrd P i := by
    by_cases hT : (P.support.filter (0 < ·)).Nonempty
    · obtain ⟨b, hbT, hbmin⟩ := (P.support.filter (0 < ·)).exists_min_image
        (fun j => newtonSlope (0, colOrd P 0) (j, colOrd P j)) hT
      refine ⟨newtonSlope (0, colOrd P 0) (b, colOrd P b), fun i hiS => ?_⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp
      · have hiT := Finset.mem_filter.mpr ⟨hiS, hi⟩
        have hmin := hbmin i hiT
        have hrun : (0 : ℚ) < (i : ℚ) - 0 := by
          have : (0 : ℚ) < i := by exact_mod_cast hi
          linarith
        have hsi := newtonSlope_mul_sub (p := (0, colOrd P 0)) (q := (i, colOrd P i))
          (ne_of_lt hi)
        have hmul := mul_le_mul_of_nonneg_right hmin (le_of_lt hrun)
        simp only [Nat.cast_zero, sub_zero] at hsi hmul ⊢
        linarith [hmul, hsi]
    · refine ⟨0, fun i hiS => ?_⟩
      have : i = 0 := by
        by_contra hi0
        exact hT ⟨i, Finset.mem_filter.mpr ⟨hiS, Nat.pos_of_ne_zero hi0⟩⟩
      subst this; simp
  obtain ⟨s0, hs0⟩ := seed
  obtain ⟨M, hhead, hlast, hcol, hmono, hdiag⟩ :=
    lower_hull_exists P.support (colOrd P) P.natDegree hSN hSN_mem P.natDegree 0 hS0
      (by omega) s0 hs0
  -- lift the column-point chain to all diagram points
  have hdiagram : M.IsChain (fun A B => ∀ Q ∈ newtonDiagram P, OnOrAbove A B Q) := by
    refine hdiag.imp (fun A B hAB Q hQ => ?_)
    obtain ⟨q1, q2⟩ := Q
    rw [mem_newtonDiagram, newtonCoeff] at hQ
    have hq1S : q1 ∈ P.support := by
      apply mem_support_iff.mpr
      rw [Ne, ← ZeroMemClass.coe_eq_zero]
      exact fun h => hQ (by rw [h]; simp)
    have hq12 : colOrd P q1 ≤ q2 := HahnSeries.order_le_of_coeff_ne_zero hQ
    have hcA := hAB q1 hq1S
    rw [onOrAbove_iff] at hcA ⊢
    dsimp only at hcA ⊢
    linarith [hcA, hq12]
  exact ⟨M, {
    isColumnPoint := by
      intro V hV
      obtain ⟨hV2, hV1⟩ := hcol V hV
      rw [hV2]; exact puiseuxOrder_eq_colOrd (mem_support_iff.mp hV1)
    head_eq := ⟨colOrd P 0, hhead⟩
    getLast_eq := ⟨colOrd P P.natDegree, hlast⟩
    strictMono_fst := hmono
    diagram_onOrAbove := hdiagram
    convex := isChain_zip_tail_of_colChain M hcol hdiag }⟩

end Azurite.BPR
