import Azurite.BasuPollackRoy.Chapter4.Section4_7.MomentMapRecover
import Azurite.BasuPollackRoy.Chapter4.Section4_7.MomentMapTopology
import Azurite.BasuPollackRoy.Chapter3.Section3_3.Proposition_3_18

/-!
# BPR §4.7: projective completeness (the substitute for compactness)

Over a real closed field a closed and bounded semialgebraic set need not be compact, so we cannot use
topological compactness to produce limits of curves. The replacement is **projective completeness**:
a continuous semialgebraic curve `γ : (0, a) → ℙ_k(C)` has a limit at `0⁺`.

We encode the curve by the components of its moment map `momentMap (γ s) : MomentIndex k → R` being
semialgebraically continuous on the right-neighborhood `(0, a)`. Since every component of the moment
map is bounded by `1` in absolute value (`abs_projReV_le_one` / `abs_projImV_le_one`), each component
has a limit `L idx` at `0⁺` by **Proposition 3.18**. The diagonal real limits sum to `1` (passing the
trace identity `sum_projReV_diag` to the limit), so by pigeonhole some diagonal `L (inl (i₀, i₀))` is
`≥ 1/(k+1) > 0`; this forces the curve eventually into the affine chart `𝒰_{i₀}`. On that chart the
chart coordinates `chartInv i₀ (γ s)` are ratios of moment-map entries (`reL_chartInv_eq` /
`imL_chartInv_eq`), so they converge to the corresponding ratios of the limits `L`, which are exactly
the chart coordinates of the recovered limit point `z := chartMap i₀ w`.

The only genuine analysis is the quotient-limit lemma `ratio_limit` (limit of a quotient with nonzero
limit denominator) and the trace-limit / pigeonhole chart selection. -/

namespace Azurite.BPR.Chapter4

open Azurite.BPR (IsSemialgContinuousOn rightNbhd constPt proposition_3_18)
open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-! ### The quotient-limit lemma -/

set_option linter.unusedSectionVars false in
/-- **Quotient limit (ε–δ form).** If `n s → N` and `d s → D` as `s → 0⁺` (in the eventual ε–δ sense),
with `D > 0`, and the numerators/denominators are uniformly bounded (`|n s| ≤ B`, `|d s| ≤ B`,
`|N| ≤ B`), then `n s / d s → N / D`. The denominator stays `≥ D/2 > 0` eventually, and the standard
estimate `|n/d − N/D| = |n·D − N·d| / (d·D)` controls the quotient. -/
theorem ratio_limit (n d : R → R) (N D : R) (hD : 0 < D) (B : R) (hB : 0 < B)
    (hNB : |N| ≤ B)
    (hn : ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ → |n s - N| < r)
    (hd : ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ → |d s - D| < r) :
    ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ →
      |n s / d s - N / D| < r := by
  intro r hr
  -- choose a small `ρ` controlling both numerator and denominator deviations
  -- target: `|n D − N d| < ρ (B + D)` and `d ≥ D/2`, giving `|n/d − N/D| < 2 ρ (B+D)/D²`.
  -- pick `ρ := min (D/2) (r * D^2 / (2 * (B + D + 1)))`.
  set C := B + D + 1 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  set ρ := min (D / 2) (r * D ^ 2 / (2 * C)) with hρ
  have hρpos : 0 < ρ := by
    rw [hρ]; exact lt_min (by positivity) (by positivity)
  obtain ⟨δn, hδn, Hn⟩ := hn ρ hρpos
  obtain ⟨δd, hδd, Hd⟩ := hd ρ hρpos
  refine ⟨min δn δd, lt_min hδn hδd, fun s hs hsδ => ?_⟩
  have hsn : s < δn := lt_of_lt_of_le hsδ (min_le_left _ _)
  have hsd : s < δd := lt_of_lt_of_le hsδ (min_le_right _ _)
  have hnr : |n s - N| < ρ := Hn s hs hsn
  have hdr : |d s - D| < ρ := Hd s hs hsd
  -- denominator stays positive
  have hρhalf : ρ ≤ D / 2 := by rw [hρ]; exact min_le_left _ _
  have hdpos : D / 2 < d s := by
    have := abs_lt.mp hdr
    have : d s - D > -ρ := this.1
    linarith [hρhalf]
  have hdsne : d s ≠ 0 := ne_of_gt (by linarith)
  have hDne : D ≠ 0 := ne_of_gt hD
  -- the core algebraic identity
  have hkey : n s / d s - N / D = (n s * D - N * d s) / (d s * D) := by
    rw [div_sub_div _ _ hdsne hDne]; ring_nf
  rw [hkey, abs_div]
  have hden : 0 < |d s * D| := by
    rw [abs_mul]; exact mul_pos (abs_pos.mpr hdsne) (abs_pos.mpr hDne)
  rw [div_lt_iff₀ hden]
  -- bound numerator: `n D − N d = (n − N) D + N (D − d)`, strictly `< ρ D + B ρ`
  have hnumeq : n s * D - N * d s = (n s - N) * D + N * (D - d s) := by ring
  have hbnum : |n s * D - N * d s| < ρ * D + B * ρ := by
    rw [hnumeq]
    have h1 : |(n s - N) * D| < ρ * D := by
      rw [abs_mul, abs_of_pos hD]
      exact mul_lt_mul_of_pos_right hnr hD
    have h2 : |N * (D - d s)| ≤ B * ρ := by
      rw [abs_mul]
      refine mul_le_mul hNB ?_ (abs_nonneg _) hB.le
      rw [abs_sub_comm]; exact le_of_lt hdr
    exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)
  -- `|d s * D| ≥ (D/2) * D`
  have hdenlb : (D / 2) * D ≤ |d s * D| := by
    rw [abs_mul, abs_of_pos hD]
    have habs : D / 2 ≤ |d s| := le_of_lt (lt_of_lt_of_le hdpos (le_abs_self _))
    nlinarith [habs, hD]
  -- `ρ * C ≤ r D² / 2`, with `C = B + D + 1`
  have hρC : ρ * C ≤ r * D ^ 2 / 2 := by
    have hle : ρ * (2 * C) ≤ r * D ^ 2 := by
      have hmin : ρ ≤ r * D ^ 2 / (2 * C) := by rw [hρ]; exact min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at hmin; exact hmin
    nlinarith [hle, hCpos]
  -- `ρ D + B ρ < ρ C` since `C = B + D + 1`
  have hnumC : |n s * D - N * d s| < ρ * C := by
    refine lt_of_lt_of_le hbnum ?_
    rw [hC]; nlinarith [hρpos]
  -- chain: |num| < ρ C ≤ r D²/2 = r ((D/2) D) ≤ r |d s D|
  have hstep : ρ * C ≤ r * ((D / 2) * D) := by
    have heq : r * ((D / 2) * D) = r * D ^ 2 / 2 := by ring
    rw [heq]; exact hρC
  calc |n s * D - N * d s| < ρ * C := hnumC
    _ ≤ r * ((D / 2) * D) := hstep
    _ ≤ r * |d s * D| := mul_le_mul_of_nonneg_left hdenlb hr.le

/-! ### A real eventual ε–δ limit is unique / determined -/

set_option linter.unusedSectionVars false in
/-- If `|x| < r` for every `r > 0`, then `x = 0`. -/
private theorem eq_zero_of_abs_lt_all {x : R} (h : ∀ r : R, 0 < r → |x| < r) : x = 0 := by
  by_contra hx
  exact (lt_irrefl _ (h |x| (abs_pos.mpr hx)))

set_option linter.unusedSectionVars false in
/-- **Common eventual bound.** Given a finite family `Q j` of properties each holding on some
right-neighborhood `(0, δ j)`, there is a single `δ > 0`, bounded by a prescribed `a'`, on which all
of them hold. Handles the empty index type (`k = 0`) uniformly. -/
theorem exists_common_eventual_bound {m : ℕ} (a' : R) (ha' : 0 < a') (Q : Fin m → R → Prop)
    (h : ∀ j, ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ → Q j s) :
    ∃ δ : R, 0 < δ ∧ δ ≤ a' ∧ ∀ s : R, 0 < s → s < δ → ∀ j, Q j s := by
  classical
  choose δ hδpos Hδ using h
  rcases isEmpty_or_nonempty (Fin m) with he | hne
  · exact ⟨a', ha', le_refl _, fun s _ _ j => (he.false j).elim⟩
  · haveI := hne
    set δ0 : R := Finset.univ.inf' Finset.univ_nonempty δ ⊓ a' with hδ0
    have hδ0pos : 0 < δ0 :=
      lt_inf_iff.mpr ⟨(Finset.lt_inf'_iff _).mpr fun j _ => hδpos j, ha'⟩
    refine ⟨δ0, hδ0pos, inf_le_right, fun s hs hsδ j => ?_⟩
    have hsj : s < δ j :=
      lt_of_lt_of_le hsδ (le_trans inf_le_left (Finset.inf'_le _ (Finset.mem_univ j)))
    exact Hδ j s hs hsj

set_option linter.unusedSectionVars false in
/-- A complex number with prescribed real and imaginary parts exists. Stated as an existence (and
consumed via `choose`) so that the literal `AdjoinRoot.of (X²+1) …` constructor — which triggers the
known `Ri R = AdjoinRoot (X²+1)` `whnf` blow-up when placed in a large proof context — stays confined
to this tiny term-mode lemma. -/
theorem exists_ri_reL_imL {S : Type*} [CommRing S] [Nontrivial S] (re im : S) :
    ∃ c : Ri S, Ri.reL c = re ∧ Ri.imL c = im :=
  ⟨AdjoinRoot.of (Polynomial.X ^ 2 + 1) re
      + AdjoinRoot.of (Polynomial.X ^ 2 + 1) im * Ri.i S,
    Ri.reL_lin re im, Ri.imL_lin re im⟩

/-! ### Projective completeness -/

set_option linter.unusedSectionVars false in
/-- **Projective completeness.** A continuous semialgebraic curve into `ℙ_k(C)`, encoded by its
moment-map components being semialgebraically continuous on the right-neighborhood `(0, a)`, has a
limit at `0⁺`: there is a point `z ∈ ℙ_k(C)` and a chart index `i` so that the curve eventually lies
in the chart `𝒰ᵢ` and its chart coordinates `chartInv i (γ s)` converge (real and imaginary parts) to
those of `z`. This replaces topological compactness (which fails over a real closed field). -/
theorem projective_curve_limit (a : R) (ha : 0 < a) (γ : R → complexProjectiveSpace R k)
    (hcont : ∀ idx : MomentIndex k,
        IsSemialgContinuousOn (rightNbhd a) (fun w : Fin 1 → R => momentMap (γ (w 0)) idx)) :
    ∃ (z : complexProjectiveSpace R k) (i : Fin (k + 1)),
      z.rep i ≠ 0 ∧
      ∃ a' : R, 0 < a' ∧ (∀ s, 0 < s → s < a' → (γ s).rep i ≠ 0) ∧
        (∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ →
          (∀ j, |Ri.reL (chartInv i (γ s) j) - Ri.reL (chartInv i z j)| < r) ∧
          (∀ j, |Ri.imL (chartInv i (γ s) j) - Ri.imL (chartInv i z j)| < r)) := by
  classical
  -- Step 1: each component has a limit `L idx`.
  have hcomp : ∀ idx : MomentIndex k, ∃ b : R, ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧
      ∀ s : R, 0 < s → s < δ → |momentMap (γ s) idx - b| < r := by
    intro idx
    refine proposition_3_18 a ha (fun w => momentMap (γ (w 0)) idx) (hcont idx) 2 ?_
    intro s hs hsa
    have hrep : (γ s).rep ≠ 0 := (γ s).rep_nonzero
    have hcs : (constPt s : Fin 1 → R) 0 = s := rfl
    rw [hcs]
    obtain ⟨p⟩ | ⟨p⟩ := idx
    · show |projReV (γ s).rep p.1 p.2| < 2
      exact lt_of_le_of_lt (abs_projReV_le_one hrep p.1 p.2) (by norm_num)
    · show |projImV (γ s).rep p.1 p.2| < 2
      exact lt_of_le_of_lt (abs_projImV_le_one hrep p.1 p.2) (by norm_num)
  choose L hL using hcomp
  -- abbreviation: diagonal real limits
  -- Step 2: the diagonal real limits sum to 1.
  have htrace : (∑ i, L (Sum.inl (i, i))) = 1 := by
    -- `|∑ L(inl(i,i)) - 1| < r` for all `r > 0`.
    refine sub_eq_zero.mp (eq_zero_of_abs_lt_all fun r hr => ?_)
    set m := Fintype.card (Fin (k + 1)) with hm
    have hmpos : (0 : R) < m := by rw [hm, Fintype.card_fin]; positivity
    -- choose a common δ achieving `|momentMap (γ s) (inl(i,i)) - L(inl(i,i))| < r / m`.
    have hrm : 0 < r / m := by positivity
    have hδi : ∀ i : Fin (k + 1), ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ →
        |momentMap (γ s) (Sum.inl (i, i)) - L (Sum.inl (i, i))| < r / m :=
      fun i => hL (Sum.inl (i, i)) (r / m) hrm
    choose δ hδpos hδ using hδi
    -- common δ: min over the finite family, intersected with `a`.
    set δ0 : R := Finset.univ.inf' Finset.univ_nonempty δ ⊓ a with hδ0
    have hδ0pos : 0 < δ0 := by
      rw [hδ0]
      refine lt_inf_iff.mpr ⟨(Finset.lt_inf'_iff _).mpr (fun i _ => hδpos i), ha⟩
    -- evaluate at `s = δ0 / 2`
    set s := δ0 / 2 with hs
    have hspos : 0 < s := by rw [hs]; positivity
    have hsa : s < a := by
      rw [hs]; have : δ0 ≤ a := inf_le_right; linarith [hδ0pos]
    have hsδ : ∀ i, s < δ i := by
      intro i
      have hle : δ0 ≤ δ i := le_trans inf_le_left (Finset.inf'_le _ (Finset.mem_univ i))
      rw [hs]; linarith [hδ0pos]
    -- the trace identity at `s`
    have hsumeq : (∑ i, momentMap (γ s) (Sum.inl (i, i))) = 1 := by
      have : (∑ i, momentMap (γ s) (Sum.inl (i, i)))
          = ∑ i, projReV (γ s).rep i i := rfl
      rw [this, sum_projReV_diag (γ s).rep_nonzero]
    -- bound the difference
    have hbound : |(∑ i, momentMap (γ s) (Sum.inl (i, i))) - (∑ i, L (Sum.inl (i, i)))| < r := by
      have hsubsum : (∑ i, momentMap (γ s) (Sum.inl (i, i))) - (∑ i, L (Sum.inl (i, i)))
          = ∑ i, (momentMap (γ s) (Sum.inl (i, i)) - L (Sum.inl (i, i))) := by
        rw [Finset.sum_sub_distrib]
      rw [hsubsum]
      refine lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ i ∈ Finset.univ,
          |momentMap (γ s) (Sum.inl (i, i)) - L (Sum.inl (i, i))| < r / m :=
        fun i _ => hδ i s hspos (hsδ i)
      calc ∑ i, |momentMap (γ s) (Sum.inl (i, i)) - L (Sum.inl (i, i))|
            < ∑ _i : Fin (k + 1), r / m :=
              Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hterm
        _ = m * (r / m) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; rw [hm,
                Fintype.card_fin]
        _ = r := by field_simp
    rw [hsumeq, abs_sub_comm] at hbound
    exact hbound
  -- pigeonhole: some diagonal limit is `≥ 1/(k+1)`.
  have hpig : ∃ i₀ : Fin (k + 1), 1 / (k + 1 : R) ≤ L (Sum.inl (i₀, i₀)) := by
    have hcst : (∑ _i : Fin (k + 1), (1 / (k + 1 : R))) ≤ ∑ i, L (Sum.inl (i, i)) := by
      rw [htrace, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_add, Nat.cast_one, mul_one_div, div_self (by positivity)]
    obtain ⟨i₀, _, hi₀⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hcst
    exact ⟨i₀, hi₀⟩
  obtain ⟨i₀, hi₀⟩ := hpig
  set c₀ : R := L (Sum.inl (i₀, i₀)) with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]; refine lt_of_lt_of_le ?_ hi₀; positivity
  -- Step 3: the curve eventually enters the chart `𝒰_{i₀}`.
  -- `momentMap (γ s) (inl(i₀,i₀)) = projReV (γ s).rep i₀ i₀ → c₀`, so eventually `> c₀/2 > 0`.
  obtain ⟨δ3, hδ3pos, Hδ3⟩ := hL (Sum.inl (i₀, i₀)) (c₀ / 2) (by positivity)
  set a' : R := min δ3 a with ha'
  have ha'pos : 0 < a' := lt_min hδ3pos ha
  have hchart : ∀ s : R, 0 < s → s < a' → (γ s).rep i₀ ≠ 0 := by
    intro s hs hsa' hcontra
    -- if `(γ s).rep i₀ = 0` then `projReV (γ s).rep i₀ i₀ = 0`, contradicting `> c₀/2`.
    have hlt : s < δ3 := lt_of_lt_of_le hsa' (min_le_left _ _)
    have hb := Hδ3 s hs hlt
    have hbig : c₀ / 2 < momentMap (γ s) (Sum.inl (i₀, i₀)) := by
      have := abs_lt.mp hb; linarith [this.1]
    have hzero : momentMap (γ s) (Sum.inl (i₀, i₀)) = 0 := by
      show projReV (γ s).rep i₀ i₀ = 0
      rw [projReV]
      have hre : Ri.reL ((γ s).rep i₀) = 0 := by rw [hcontra]; simp
      have him : Ri.imL ((γ s).rep i₀) = 0 := by rw [hcontra]; simp
      rw [hre, him]; simp
    rw [hzero] at hbig; linarith [hc₀pos]
  -- Step 4: build the limit point `z = chartMap i₀ w`, with `w j` having the limit ratios as its
  -- real/imaginary parts (constructed via `choose` to avoid the `of`-form blow-up).
  choose w hwre hwim using fun j : Fin k => exists_ri_reL_imL
    (L (Sum.inl (i₀.succAbove j, i₀)) / c₀) (L (Sum.inr (i₀.succAbove j, i₀)) / c₀)
  set z : complexProjectiveSpace R k := chartMap i₀ w with hz
  have hzrep : z.rep i₀ ≠ 0 := by
    have hmem : z ∈ (chartSet i₀ : Set (complexProjectiveSpace R k)) := ⟨w, rfl⟩
    rw [chartSet_eq] at hmem; exact hmem
  have hzinv : chartInv i₀ z = w := by rw [hz]; exact chartInv_chartMap i₀ w
  -- each moment-map component is bounded by `1`, so each limit `L idx` satisfies `|L idx| ≤ 1`.
  have hmomle : ∀ idx : MomentIndex k, ∀ s : R, |momentMap (γ s) idx| ≤ 1 := by
    intro idx s
    have hrep := (γ s).rep_nonzero
    obtain ⟨p⟩ | ⟨p⟩ := idx
    · exact abs_projReV_le_one hrep p.1 p.2
    · exact abs_projImV_le_one hrep p.1 p.2
  have hLbound : ∀ idx : MomentIndex k, |L idx| ≤ 1 := by
    intro idx
    by_contra hcon
    push Not at hcon
    obtain ⟨δ, hδpos, Hδ⟩ := hL idx (|L idx| - 1) (by linarith)
    have hb := Hδ (δ / 2) (by positivity) (by linarith)
    have hm := hmomle idx (δ / 2)
    -- `|L idx| ≤ |L idx - mom| + |mom| < (|L idx| - 1) + 1 = |L idx|`, contradiction.
    have htri : |L idx| ≤ |L idx - momentMap (γ (δ / 2)) idx| + |momentMap (γ (δ / 2)) idx| := by
      have := abs_add_le (L idx - momentMap (γ (δ / 2)) idx) (momentMap (γ (δ / 2)) idx)
      simpa using this
    rw [abs_sub_comm] at hb
    linarith
  refine ⟨z, i₀, hzrep, a', ha'pos, hchart, fun r hr => ?_⟩
  -- Step 5: convergence of the chart coordinates via the quotient-limit lemma.
  -- Per `j`, real and imaginary parts; both via `ratio_limit` with `B = 1`.
  -- the real-part quotient-limit for index `j`
  have hRe : ∀ j : Fin k, ∀ rr : R, 0 < rr → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ →
      |projReV (γ s).rep (i₀.succAbove j) i₀ / projReV (γ s).rep i₀ i₀
        - L (Sum.inl (i₀.succAbove j, i₀)) / c₀| < rr := by
    intro j
    refine ratio_limit
      (fun s => momentMap (γ s) (Sum.inl (i₀.succAbove j, i₀)))
      (fun s => momentMap (γ s) (Sum.inl (i₀, i₀)))
      (L (Sum.inl (i₀.succAbove j, i₀))) c₀ hc₀pos 1 one_pos
      (hLbound (Sum.inl (i₀.succAbove j, i₀)))
      (hL (Sum.inl (i₀.succAbove j, i₀))) (hL (Sum.inl (i₀, i₀)))
  have hIm : ∀ j : Fin k, ∀ rr : R, 0 < rr → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ →
      |projImV (γ s).rep (i₀.succAbove j) i₀ / projReV (γ s).rep i₀ i₀
        - L (Sum.inr (i₀.succAbove j, i₀)) / c₀| < rr := by
    intro j
    refine ratio_limit
      (fun s => momentMap (γ s) (Sum.inr (i₀.succAbove j, i₀)))
      (fun s => momentMap (γ s) (Sum.inl (i₀, i₀)))
      (L (Sum.inr (i₀.succAbove j, i₀))) c₀ hc₀pos 1 one_pos
      (hLbound (Sum.inr (i₀.succAbove j, i₀)))
      (hL (Sum.inr (i₀.succAbove j, i₀))) (hL (Sum.inl (i₀, i₀)))
  -- combine the real and imaginary quotient-limits per `j` into one eventual property.
  set Q : Fin k → R → Prop := fun j s =>
    |projReV (γ s).rep (i₀.succAbove j) i₀ / projReV (γ s).rep i₀ i₀
        - L (Sum.inl (i₀.succAbove j, i₀)) / c₀| < r ∧
    |projImV (γ s).rep (i₀.succAbove j) i₀ / projReV (γ s).rep i₀ i₀
        - L (Sum.inr (i₀.succAbove j, i₀)) / c₀| < r with hQ
  have hQev : ∀ j, ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ → Q j s := by
    intro j
    obtain ⟨δa, hδa, Ha⟩ := hRe j r hr
    obtain ⟨δb, hδb, Hb⟩ := hIm j r hr
    refine ⟨min δa δb, lt_min hδa hδb, fun s hs hsδ => ?_⟩
    exact ⟨Ha s hs (lt_of_lt_of_le hsδ (min_le_left _ _)),
      Hb s hs (lt_of_lt_of_le hsδ (min_le_right _ _))⟩
  obtain ⟨δ, hδpos, hδa', hδall⟩ := exists_common_eventual_bound a' ha'pos Q hQev
  refine ⟨δ, hδpos, fun s hs hsδ => ?_⟩
  have hsa' : s < a' := lt_of_lt_of_le hsδ hδa'
  have hsrep : (γ s).rep i₀ ≠ 0 := hchart s hs hsa'
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rw [reL_chartInv_eq hsrep j, hzinv, hwre j]
    exact (hδall s hs hsδ j).1
  · rw [imL_chartInv_eq hsrep j, hzinv, hwim j]
    exact (hδall s hs hsδ j).2
