import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygonExists
import Azurite.BasuPollackRoy.Chapter2.Section2_6.CharacteristicPolynomial

/-! # BPR §2.6 — the strict Newton polygon (edges support `honseg`)

The Newton-polygon existence of `NewtonPolygonExists` uses *any* minimal-slope next vertex, so its
edges can be non-maximal pieces of a collinear segment; then a later vertex lies on the same line
beyond an edge, and the Lemma-2.95 hypothesis `honseg` (on-line columns lie within `[A.1, B.1]`)
fails. Here we redo the gift-wrapping breaking ties by the **largest** column achieving the
minimal slope, which makes every vertex a strict corner. Carrying a strict lower bound on the
right-slopes (`hstr`) alongside the supporting line (`hs`), the construction yields, per edge, the
`honseg` property (`exists_isNewtonPolygon_honseg`).
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- **The strict lower-hull construction.** Carries both a (non-strict) supporting line `hs` and a
strict lower bound `hstr` on the right-slopes; the next vertex is the *largest* column achieving
the minimal slope. Outputs the usual polygon data plus the per-edge `honseg` property. -/
theorem lower_hull_exists_strict (S : Finset ℕ) (f : ℕ → ℚ) (N : ℕ)
    (hSN : ∀ i ∈ S, i ≤ N) (hNS : N ∈ S) :
    ∀ d : ℕ, ∀ a : ℕ, a ∈ S → N - a ≤ d → ∀ s : ℚ,
      (∀ i ∈ S, f a + s * ((i : ℚ) - a) ≤ f i) →
      (∀ i ∈ S, a < i → f a + s * ((i : ℚ) - a) < f i) →
      ∃ M : List (ℕ × ℚ), M.head? = some (a, f a) ∧ M.getLast? = some (N, f N)
        ∧ (∀ V ∈ M, V.2 = f V.1 ∧ V.1 ∈ S)
        ∧ M.IsChain (fun A B => A.1 < B.1)
        ∧ M.IsChain (fun A B : ℕ × ℚ => ∀ i ∈ S, OnOrAbove A B (i, f i))
        ∧ (∀ U V : ℕ × ℚ, (U, V) ∈ M.zip M.tail →
            ∀ h ∈ S, (f h : ℚ) = lineValue U V h → U.1 ≤ h ∧ h ≤ V.1) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d IH =>
    intro a haS hda s hs hstr
    rcases eq_or_lt_of_le (hSN a haS) with haN | haN
    · subst haN
      refine ⟨[(a, f a)], rfl, rfl, ?_, List.isChain_singleton _, List.isChain_singleton _, ?_⟩
      · intro V hV; rw [List.mem_singleton] at hV; subst hV; exact ⟨rfl, haS⟩
      · intro U V hUV; simp at hUV
    · have hTne : (S.filter (a < ·)).Nonempty := ⟨N, Finset.mem_filter.mpr ⟨hNS, haN⟩⟩
      set m := (S.filter (a < ·)).inf' hTne (fun j => newtonSlope (a, f a) (j, f j)) with hmdef
      obtain ⟨b0, hb0T, hb0m⟩ :=
        Finset.exists_mem_eq_inf' hTne (fun j => newtonSlope (a, f a) (j, f j))
      set T' := (S.filter (a < ·)).filter (fun j => newtonSlope (a, f a) (j, f j) = m) with hT'def
      have hT'ne : T'.Nonempty := ⟨b0, Finset.mem_filter.mpr ⟨hb0T, hb0m.symm⟩⟩
      set b := T'.max' hT'ne with hbdef
      have hbT' : b ∈ T' := T'.max'_mem hT'ne
      have hbTf : b ∈ S.filter (a < ·) := (Finset.mem_filter.mp hbT').1
      have hbm : newtonSlope (a, f a) (b, f b) = m := (Finset.mem_filter.mp hbT').2
      have hbS : b ∈ S := (Finset.mem_filter.mp hbTf).1
      have hab : a < b := (Finset.mem_filter.mp hbTf).2
      have hrunb : (0 : ℚ) < (b : ℚ) - a := by
        have : (a : ℚ) < b := by exact_mod_cast hab
        linarith
      have hmin : ∀ j ∈ S, a < j → m ≤ newtonSlope (a, f a) (j, f j) :=
        fun j hjS hj => Finset.inf'_le _ (Finset.mem_filter.mpr ⟨hjS, hj⟩)
      have hmax : ∀ j ∈ S, a < j → newtonSlope (a, f a) (j, f j) = m → j ≤ b :=
        fun j hjS hj hjm =>
          Finset.le_max' T' j (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hjS, hj⟩, hjm⟩)
      have hfb : f a + m * ((b : ℚ) - a) = f b := by
        have hh := newtonSlope_mul_sub (p := (a, f a)) (q := (b, f b)) (ne_of_lt hab)
        rw [hbm] at hh; simp only at hh; linarith [hh]
      have hsm : s < m := by
        have h1 := hstr b hbS hab
        rw [← hfb] at h1
        have h2 : s * ((b : ℚ) - a) < m * ((b : ℚ) - a) := by linarith
        exact lt_of_mul_lt_mul_right h2 (le_of_lt hrunb)
      have hedge : ∀ i ∈ S, f a + m * ((i : ℚ) - a) ≤ f i := by
        intro i hiS
        rcases lt_trichotomy i a with hia | hia | hia
        · have hia' : (i : ℚ) - a < 0 := by
            have : (i : ℚ) < a := by exact_mod_cast hia
            linarith
          have hmul : m * ((i : ℚ) - a) ≤ s * ((i : ℚ) - a) :=
            mul_le_mul_of_nonpos_right (le_of_lt hsm) (le_of_lt hia')
          linarith [hs i hiS, hmul]
        · subst hia; simp
        · have hmi := hmin i hiS hia
          have hrun : (0 : ℚ) < (i : ℚ) - a := by
            have : (a : ℚ) < i := by exact_mod_cast hia
            linarith
          have hsi := newtonSlope_mul_sub (p := (a, f a)) (q := (i, f i)) (ne_of_lt hia)
          simp only at hsi
          have hmul : m * ((i : ℚ) - a) ≤ newtonSlope (a, f a) (i, f i) * ((i : ℚ) - a) :=
            mul_le_mul_of_nonneg_right hmi (le_of_lt hrun)
          linarith [hmul, hsi]
      have hinv1 : ∀ i ∈ S, f b + m * ((i : ℚ) - b) ≤ f i := by
        intro i hiS
        have hd2 : m * ((i : ℚ) - b) + m * ((b : ℚ) - a) = m * ((i : ℚ) - a) := by ring
        linarith [hedge i hiS, hfb, hd2]
      have hinv2 : ∀ i ∈ S, b < i → f b + m * ((i : ℚ) - b) < f i := by
        intro i hiS hbi
        have hai : a < i := lt_trans hab hbi
        have hmi := hmin i hiS hai
        have hgt : m < newtonSlope (a, f a) (i, f i) := by
          rcases lt_or_eq_of_le hmi with h | h
          · exact h
          · exact absurd (hmax i hiS hai h.symm) (by omega)
        have hrun : (0 : ℚ) < (i : ℚ) - a := by
          have : (a : ℚ) < i := by exact_mod_cast hai
          linarith
        have hsi := newtonSlope_mul_sub (p := (a, f a)) (q := (i, f i)) (ne_of_lt hai)
        simp only at hsi
        have hmul : m * ((i : ℚ) - a) < newtonSlope (a, f a) (i, f i) * ((i : ℚ) - a) :=
          mul_lt_mul_of_pos_right hgt hrun
        have hd2 : m * ((i : ℚ) - b) + m * ((b : ℚ) - a) = m * ((i : ℚ) - a) := by ring
        linarith [hmul, hsi, hfb, hd2]
      obtain ⟨Mb, hMb_head, hMb_last, hMb_col, hMb_mono, hMb_diag, hMb_hon⟩ :=
        IH (N - b) (by omega) b hbS (le_refl _) m hinv1 hinv2
      obtain ⟨bp, Mbt, rfl⟩ :=
        List.exists_cons_of_ne_nil (show Mb ≠ [] by intro h; rw [h] at hMb_head; simp at hMb_head)
      rw [List.head?_cons, Option.some_inj] at hMb_head; subst hMb_head
      have hhonab : ∀ h ∈ S, (f h : ℚ) = lineValue (a, f a) (b, f b) h → a ≤ h ∧ h ≤ b := by
        intro h hhS hhf
        rw [lineValue] at hhf; simp only at hhf; rw [hbm] at hhf
        refine ⟨?_, ?_⟩
        · by_contra hlt
          rw [not_le] at hlt
          have hha' : (h : ℚ) - a < 0 := by
            have : (h : ℚ) < a := by exact_mod_cast hlt
            linarith
          have hle := hs h hhS
          rw [hhf] at hle
          nlinarith [hle, mul_pos (sub_pos.mpr hsm) (neg_pos.mpr hha')]
        · rcases Nat.lt_or_ge a h with hha | hha
          · have hrunh : (0 : ℚ) < (h : ℚ) - a := by
              have : (a : ℚ) < h := by exact_mod_cast hha
              linarith
            have hslope : newtonSlope (a, f a) (h, f h) = m := by
              rw [newtonSlope]; dsimp only; rw [div_eq_iff hrunh.ne']; linarith [hhf]
            exact hmax h hhS hha hslope
          · omega
      refine ⟨(a, f a) :: (b, f b) :: Mbt, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.getLast?_cons_cons]; exact hMb_last
      · intro V hV
        rcases List.mem_cons.mp hV with rfl | hV
        · exact ⟨rfl, haS⟩
        · exact hMb_col V hV
      · rw [List.isChain_cons_cons]; exact ⟨hab, hMb_mono⟩
      · rw [List.isChain_cons_cons]
        refine ⟨fun i hiS => ?_, hMb_diag⟩
        rw [onOrAbove_iff, hbm]; dsimp only; linarith [hedge i hiS]
      · intro U V hUV h hhS hhf
        rw [List.tail_cons, List.zip_cons_cons] at hUV
        rcases List.mem_cons.mp hUV with heq | hUV
        · rw [Prod.mk.injEq] at heq; obtain ⟨hU, hV⟩ := heq; subst hU; subst hV
          exact hhonab h hhS hhf
        · exact hMb_hon U V hUV h hhS hhf

open Classical in
/-- **Existence of a strict Newton polygon.** Every polynomial with nonzero constant term has a
Newton polygon all of whose edges satisfy `honseg`: a column on an edge line lies within the
edge's horizontal projection. -/
theorem exists_isNewtonPolygon_honseg (P : Polynomial (PuiseuxSeries R)) (h0 : P.coeff 0 ≠ 0) :
    ∃ M, IsNewtonPolygon P M ∧
      ∀ A B : ℕ × ℚ, (A, B) ∈ M.zip M.tail → ∀ h, colOnLine P A B h → A.1 ≤ h ∧ h ≤ B.1 := by
  have hP : P ≠ 0 := fun h => h0 (by rw [h, coeff_zero])
  have hS0 : (0 : ℕ) ∈ P.support := mem_support_iff.mpr h0
  have hSN_mem : P.natDegree ∈ P.support :=
    mem_support_iff.mpr (by rw [← leadingCoeff]; exact leadingCoeff_ne_zero.mpr hP)
  have hSN : ∀ i ∈ P.support, i ≤ P.natDegree :=
    fun i hi => le_natDegree_of_ne_zero (mem_support_iff.mp hi)
  have seed : ∃ s : ℚ, (∀ i ∈ P.support, colOrd P 0 + s * ((i : ℚ) - 0) ≤ colOrd P i) ∧
      (∀ i ∈ P.support, 0 < i → colOrd P 0 + s * ((i : ℚ) - 0) < colOrd P i) := by
    by_cases hT : (P.support.filter (0 < ·)).Nonempty
    · have key : ∀ i ∈ P.support, 0 < i → colOrd P 0 + ((P.support.filter (0 < ·)).inf' hT
          (fun j => newtonSlope (0, colOrd P 0) (j, colOrd P j)) - 1) * ((i : ℚ) - 0) < colOrd P i := by
        intro i hiS hi
        have hmem := Finset.mem_filter.mpr ⟨hiS, hi⟩
        have hle := Finset.inf'_le (fun j => newtonSlope (0, colOrd P 0) (j, colOrd P j)) hmem
        have hrun : (0 : ℚ) < (i : ℚ) := by exact_mod_cast hi
        have hsi := newtonSlope_mul_sub (p := (0, colOrd P 0)) (q := (i, colOrd P i)) (ne_of_lt hi)
        simp only [Nat.cast_zero, sub_zero] at hsi ⊢
        nlinarith [hle, hsi, hrun, mul_nonneg (sub_nonneg.mpr hle) (le_of_lt hrun)]
      refine ⟨_, fun i hiS => ?_, key⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp
      · exact le_of_lt (key i hiS hi)
    · refine ⟨0, ?_, ?_⟩
      · intro i hiS
        have : i = 0 := by
          by_contra hi0
          exact hT ⟨i, Finset.mem_filter.mpr ⟨hiS, Nat.pos_of_ne_zero hi0⟩⟩
        subst this; simp
      · intro i hiS hi
        exact absurd ⟨i, Finset.mem_filter.mpr ⟨hiS, hi⟩⟩ hT
  obtain ⟨s0, hs0, hstr0⟩ := seed
  obtain ⟨M, hhead, hlast, hcol, hmono, hdiag, hhon⟩ :=
    lower_hull_exists_strict P.support (colOrd P) P.natDegree hSN hSN_mem P.natDegree 0 hS0
      (by omega) s0 hs0 hstr0
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
  refine ⟨M, ?_, ?_⟩
  · exact
      { isColumnPoint := fun V hV => by
          obtain ⟨hV2, hV1⟩ := hcol V hV
          rw [hV2]; exact puiseuxOrder_eq_colOrd (mem_support_iff.mp hV1)
        head_eq := ⟨colOrd P 0, hhead⟩
        getLast_eq := ⟨colOrd P P.natDegree, hlast⟩
        strictMono_fst := hmono
        diagram_onOrAbove := hdiagram
        convex := isChain_zip_tail_of_colChain M hcol hdiag }
  · intro A B hAB h hcolh
    have hcolh' : puiseuxOrder R (P.coeff h) = (lineValue A B h : WithTop ℚ) := hcolh
    have hhS : h ∈ P.support := by
      apply mem_support_iff.mpr
      intro hc; rw [hc, puiseuxOrder_zero] at hcolh'; exact WithTop.top_ne_coe hcolh'
    have hfh : colOrd P h = lineValue A B h := by
      rw [puiseuxOrder_eq_colOrd (mem_support_iff.mp hhS)] at hcolh'
      exact_mod_cast hcolh'
    exact hhon A B hAB h hhS hfh

end Azurite.BPR
