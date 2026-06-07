import Azurite.BasuPollackRoy.Chapter3.Section3_3.GermPolynomial
import Azurite.BasuPollackRoy.Chapter3.Section3_3.GermRootCount
import Azurite.BasuPollackRoy.Chapter3.Section3_3.Proposition_3_10

/-! # BPR §3.3 — continuous root branches of a germ polynomial

Towards BPR's separable intermediate value property: once the fiber `P(t, ·) = specializeAt Q (constPt t)`
is nonzero with a fixed number `r` of distinct (necessarily simple) roots near `0⁺`, each root varies
continuously. This file develops the branch machinery from the strengthened implicit function theorem
(`proposition_3_10`): a simple root of the fiber extends to a continuous branch, and — because the
total number of roots is fixed (`germPoly_rootCount_eventually_constant`) — finitely many such branches
exhaust all the roots near a point. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **A root of a polynomial coprime with its derivative is simple.** If `IsCoprime Q Q'` and `y` is a
root of `Q`, then `Q'(y) ≠ 0`. This is BPR's "the roots are simple" coming from `gcd(P, P') = 1`. -/
theorem isSimpleRoot_of_isCoprime {Q : Polynomial R} (h : IsCoprime Q (Polynomial.derivative Q))
    {y : R} (hy : Q.eval y = 0) : IsSimpleRoot Q y := by
  refine ⟨hy, fun hd => ?_⟩
  obtain ⟨a, b, hab⟩ := h
  have := congrArg (Polynomial.eval y) hab
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, hy, hd, mul_zero,
    add_zero] at this
  exact one_ne_zero this.symm

/-- **A relatively open neighborhood of `constPt t*` contains an interval.** If `U` is open in the
right-neighborhood `(0, t₁)` and `constPt t* ∈ U`, then `constPt u ∈ U` for all `u` in an interval
`(t* − m, t* + m)` that also lies in `(0, t₁)`. -/
theorem exists_interval_subset_of_isOpenIn {t₁ : R} {U : Set (Fin 1 → R)} {t : R}
    (hU : IsOpenIn (rightNbhd t₁) U) (htU : constPt t ∈ U) :
    ∃ m, 0 < m ∧ ∀ u : R, |u - t| < m → 0 < u → u < t₁ → constPt u ∈ U := by
  obtain ⟨V, hVopen, hUV⟩ := hU
  rw [hUV] at htU
  obtain ⟨hxV, _⟩ := htU
  obtain ⟨r, hr, hsub⟩ := isOpen_iff_ball_self.mp hVopen (constPt t) hxV
  refine ⟨r, hr, fun u hu hu0 hu1 => ?_⟩
  rw [hUV]
  refine ⟨hsub ?_, ?_⟩
  · rw [mem_openBall_iff_norm hr]
    have hcp : constPt u - constPt t = constPt (u - t) := by funext i; simp [constPt]
    rw [hcp, euclideanNorm_fin_one]
    simpa [constPt] using hu
  · exact ⟨by simpa [constPt] using hu0, by simpa [constPt] using hu1⟩

/-- **A continuous scalar function positive at a point is positive nearby.** -/
theorem eventually_pos_of_continuousOn {k : ℕ} {U : Set (Fin k → R)} {h : (Fin k → R) → R}
    (hcont : ContinuousOn (scalarFun h) U) {x : Fin k → R} (hxU : x ∈ U) (hpos : 0 < h x) :
    ∃ δ, 0 < δ ∧ ∀ w ∈ U, euclideanNorm (w - x) < δ → 0 < h w := by
  rw [continuousOn_fin_one_iff] at hcont
  obtain ⟨δ, hδ, H⟩ := hcont x hxU (h x) hpos
  refine ⟨δ, hδ, fun w hw hwx => ?_⟩
  have hb := H w hw hwx
  simp only [scalarFun, constPt] at hb
  rw [abs_lt] at hb
  linarith [hb.1]

/-- **Two continuous scalar functions strictly ordered at a point stay ordered nearby.** -/
theorem eventually_lt_of_continuousOn {k : ℕ} {U : Set (Fin k → R)} {g h : (Fin k → R) → R}
    (hg : ContinuousOn (scalarFun g) U) (hh : ContinuousOn (scalarFun h) U) {x : Fin k → R}
    (hxU : x ∈ U) (hlt : g x < h x) :
    ∃ δ, 0 < δ ∧ ∀ w ∈ U, euclideanNorm (w - x) < δ → g w < h w := by
  rw [continuousOn_fin_one_iff] at hg hh
  have hεpos : 0 < (h x - g x) / 2 := by linarith
  obtain ⟨δg, hδg, Hg⟩ := hg x hxU ((h x - g x) / 2) hεpos
  obtain ⟨δh, hδh, Hh⟩ := hh x hxU ((h x - g x) / 2) hεpos
  refine ⟨min δg δh, lt_min hδg hδh, fun w hw hwx => ?_⟩
  have hbg := Hg w hw (lt_of_lt_of_le hwx (min_le_left _ _))
  have hbh := Hh w hw (lt_of_lt_of_le hwx (min_le_right _ _))
  simp only [scalarFun, constPt] at hbg hbh
  rw [abs_lt] at hbg hbh
  linarith [hbg.2, hbh.1]

/-- **Exhaustion of the roots by continuous branches.** If the fiber `P(w, ·) = specializeAt Q w` is
nonzero with a fixed number `r` of distinct simple roots for all `w ∈ (0, t₁)`, then near any point
`x` there is a relatively open neighborhood `U` and `r` continuous branches `F j` such that, for
`w ∈ U`, the `F j w` are exactly the (strictly increasing) roots of `P(w, ·)`. This is BPR's "the
roots `h_i(u)` are necessarily the `g_i(u)` because the number of roots is fixed." -/
theorem roots_exhausted_by_branches {t₁ : R} {Q : Polynomial ((Fin 1 → R) → R)}
    (hQ : HasSemialgContinuousCoeffs (rightNbhd t₁) Q) {r : ℕ}
    (hnz : ∀ w ∈ rightNbhd t₁, specializeAt Q w ≠ 0)
    (hcount : ∀ w ∈ rightNbhd t₁, (specializeAt Q w).roots.toFinset.card = r)
    (hcoprime : ∀ w ∈ rightNbhd t₁,
      IsCoprime (specializeAt Q w) (Polynomial.derivative (specializeAt Q w)))
    {x : Fin 1 → R} (hx : x ∈ rightNbhd t₁) :
    ∃ U : Set (Fin 1 → R), IsOpenIn (rightNbhd t₁) U ∧ x ∈ U ∧ U ⊆ rightNbhd t₁ ∧
      ∃ F : Fin r → (Fin 1 → R) → R,
        (∀ j, ContinuousOn (scalarFun (F j)) U) ∧
        (∀ w ∈ U, ∀ j, (specializeAt Q w).eval (F j w) = 0) ∧
        (∀ w ∈ U, StrictMono (fun j => F j w)) ∧
        (∀ w ∈ U, ∀ z, (specializeAt Q w).eval z = 0 → ∃ j, z = F j w) := by
  classical
  have hscard : (specializeAt Q x).roots.toFinset.card = r := hcount x hx
  set y : Fin r → R := fun j => (specializeAt Q x).roots.toFinset.orderEmbOfFin hscard j with hydef
  have hymono : StrictMono y := ((specializeAt Q x).roots.toFinset.orderEmbOfFin hscard).strictMono
  have hyroot : ∀ j, (specializeAt Q x).eval (y j) = 0 := by
    intro j
    have hmem := (specializeAt Q x).roots.toFinset.orderEmbOfFin_mem hscard j
    rw [Multiset.mem_toFinset, Polynomial.mem_roots'] at hmem
    exact hmem.2
  have hysimple : ∀ j, IsSimpleRoot (specializeAt Q x) (y j) :=
    fun j => isSimpleRoot_of_isCoprime (hcoprime x hx) (hyroot j)
  -- the `r` branches from the strengthened implicit function theorem
  have hbr : ∀ j : Fin r, ∃ U, IsSemialgebraicSet U ∧ IsOpenIn (rightNbhd t₁) U ∧ x ∈ U ∧
      ∃ f, IsSemialgContinuousOn U f ∧ f x = y j ∧
        (∀ x' ∈ U, IsSimpleRoot (specializeAt Q x') (f x')) ∧
        ∃ a b, a < y j ∧ y j < b ∧ ∀ x' ∈ U, f x' ∈ Set.Ioo a b ∧
          ∀ c ∈ Set.Ioo a b, (specializeAt Q x').eval c = 0 → c = f x' :=
    fun j => proposition_3_10 (isSemialgebraicSet_rightNbhd t₁) hQ hx (hysimple j)
  choose Uf _ hUfopen hxUf F hFsacont hFx hFsimple _ _ _ _ _ using hbr
  have hFcont : ∀ j, ContinuousOn (scalarFun (F j)) (Uf j) := fun j => (hFsacont j).2
  have hx_const : x = constPt (x 0) := by funext i; rw [Subsingleton.elim i 0]; rfl
  -- interval radius: `w ∈ rightNbhd`, `‖w - x‖ < δint j` ⟹ `w ∈ Uf j`
  have hint : ∀ j : Fin r, ∃ δ, 0 < δ ∧
      ∀ w ∈ rightNbhd t₁, euclideanNorm (w - x) < δ → w ∈ Uf j := by
    intro j
    obtain ⟨m, hm, Hm⟩ := exists_interval_subset_of_isOpenIn (hUfopen j) (hx_const ▸ hxUf j)
    refine ⟨m, hm, fun w hw hwx => ?_⟩
    have hw_const : w = constPt (w 0) := by funext i; rw [Subsingleton.elim i 0]; rfl
    rw [hw_const]
    refine Hm (w 0) ?_ hw.1 hw.2
    rw [euclideanNorm_fin_one] at hwx
    simpa only [Pi.sub_apply] using hwx
  choose δint hδintpos hδint using hint
  -- ordering radius: for `i < j`, `F i w < F j w` near `x`
  have hord : ∀ p : Fin r × Fin r, ∃ δ, 0 < δ ∧
      (p.1 < p.2 → ∀ w ∈ Uf p.1 ∩ Uf p.2, euclideanNorm (w - x) < δ → F p.1 w < F p.2 w) := by
    rintro ⟨i, j⟩
    by_cases hij : i < j
    · obtain ⟨δ, hδ, H⟩ := eventually_lt_of_continuousOn ((hFcont i).mono Set.inter_subset_left)
        ((hFcont j).mono Set.inter_subset_right) ⟨hxUf i, hxUf j⟩
        (by rw [hFx i, hFx j]; exact hymono hij)
      exact ⟨δ, hδ, fun _ => H⟩
    · exact ⟨1, one_pos, fun h => absurd h hij⟩
  choose δord hδordpos hδord using hord
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    refine ⟨rightNbhd t₁, isOpenIn_self _, hx, subset_rfl, Fin.elim0,
      fun j => j.elim0, fun w _ j => j.elim0, fun w _ a b hab => a.elim0, fun w hw z hz => ?_⟩
    exfalso
    have : z ∈ (specializeAt Q w).roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']; exact ⟨hnz w hw, hz⟩
    rw [Finset.card_eq_zero.mp (hcount w hw)] at this
    exact absurd this (Finset.notMem_empty z)
  · haveI : NeZero r := ⟨Nat.pos_iff_ne_zero.mp hrpos⟩
    have hune : (Finset.univ : Finset (Fin r)).Nonempty := Finset.univ_nonempty
    have hunep : (Finset.univ : Finset (Fin r × Fin r)).Nonempty := Finset.univ_nonempty
    set m : R := min (Finset.univ.inf' hune δint) (Finset.univ.inf' hunep δord) with hmdef
    have hmpos : 0 < m :=
      lt_min ((Finset.lt_inf'_iff hune).mpr fun j _ => hδintpos j)
        ((Finset.lt_inf'_iff hunep).mpr fun p _ => hδordpos p)
    set U : Set (Fin 1 → R) :=
      {w | w ∈ rightNbhd t₁ ∧ euclideanNorm (w - x) < m} with hUdef
    have hUsub_nbhd : U ⊆ rightNbhd t₁ := fun w hw => hw.1
    have hUsub : ∀ j, U ⊆ Uf j := fun j w hw =>
      hδint j w hw.1 (lt_of_lt_of_le hw.2 (le_trans (min_le_left _ _) (Finset.inf'_le _ (Finset.mem_univ j))))
    have hxU : x ∈ U := by
      refine ⟨hx, ?_⟩
      rw [euclideanNorm_fin_one]; simpa only [Pi.sub_apply, sub_self, abs_zero] using hmpos
    have hUopen : IsOpenIn (rightNbhd t₁) U := by
      refine ⟨openBall x m, isOpen_openBall x hmpos, ?_⟩
      ext w
      simp only [hUdef, Set.mem_setOf_eq, Set.mem_inter_iff, mem_openBall_iff_norm hmpos]
      tauto
    refine ⟨U, hUopen, hxU, hUsub_nbhd, F, fun j => (hFcont j).mono (hUsub j), ?_, ?_, ?_⟩
    · exact fun w hw j => (hFsimple j w (hUsub j hw)).1
    · intro w hw i j hij
      exact hδord (i, j) hij w ⟨hUsub i hw, hUsub j hw⟩
        (lt_of_lt_of_le hw.2 (le_trans (min_le_right _ _) (Finset.inf'_le _ (Finset.mem_univ (i, j)))))
    · intro w hw z hz
      have hStrict : StrictMono (fun j => F j w) := fun i j hij =>
        hδord (i, j) hij w ⟨hUsub i hw, hUsub j hw⟩
          (lt_of_lt_of_le hw.2 (le_trans (min_le_right _ _) (Finset.inf'_le _ (Finset.mem_univ (i, j)))))
      have hginj : Function.Injective (fun j => F j w) := hStrict.injective
      have hgroot : ∀ j, F j w ∈ (specializeAt Q w).roots.toFinset := by
        intro j
        rw [Multiset.mem_toFinset, Polynomial.mem_roots']
        exact ⟨hnz w (hUsub_nbhd hw), (hFsimple j w (hUsub j hw)).1⟩
      have hsubset : Finset.univ.image (fun j => F j w) ⊆ (specializeAt Q w).roots.toFinset :=
        fun a ha => by
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha; exact hgroot j
      have hcard_im : (Finset.univ.image (fun j => F j w)).card = r := by
        rw [Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_fin]
      have heq : Finset.univ.image (fun j => F j w) = (specializeAt Q w).roots.toFinset :=
        Finset.eq_of_subset_of_card_le hsubset (by rw [hcard_im, hcount w (hUsub_nbhd hw)])
      have hzmem : z ∈ (specializeAt Q w).roots.toFinset := by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots']; exact ⟨hnz w (hUsub_nbhd hw), hz⟩
      rw [← heq] at hzmem
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hzmem
      exact ⟨j, hj.symm⟩

/-- The **smallest root** of the fiber `P(w, ·)` lying strictly between `f₁ w` and `f₂ w` (and `f₁ w`
as a default when there is none). -/
noncomputable def smallestRootIn (Q : Polynomial ((Fin 1 → R) → R)) (f₁ f₂ : (Fin 1 → R) → R)
    (w : Fin 1 → R) : R := by
  classical
  exact if h : ((specializeAt Q w).roots.toFinset.filter (fun z => f₁ w < z ∧ z < f₂ w)).Nonempty
    then ((specializeAt Q w).roots.toFinset.filter (fun z => f₁ w < z ∧ z < f₂ w)).min' h
    else f₁ w

/-- **Specification of `smallestRootIn`.** When `P(w, f₁ w) · P(w, f₂ w) < 0` and `f₁ w < f₂ w`, the
value `smallestRootIn Q f₁ f₂ w` is a root of `P(w, ·)` in `(f₁ w, f₂ w)`, and it is the least such. -/
theorem smallestRootIn_spec {Q : Polynomial ((Fin 1 → R) → R)} {f₁ f₂ : (Fin 1 → R) → R}
    {w : Fin 1 → R} (hnz : specializeAt Q w ≠ 0) (hlt : f₁ w < f₂ w)
    (hsign : (specializeAt Q w).eval (f₁ w) * (specializeAt Q w).eval (f₂ w) < 0) :
    (specializeAt Q w).eval (smallestRootIn Q f₁ f₂ w) = 0 ∧
      f₁ w < smallestRootIn Q f₁ f₂ w ∧ smallestRootIn Q f₁ f₂ w < f₂ w ∧
      ∀ z, (specializeAt Q w).eval z = 0 → f₁ w < z → z < f₂ w →
        smallestRootIn Q f₁ f₂ w ≤ z := by
  classical
  obtain ⟨x₀, hx₀a, hx₀b, hx₀e⟩ :=
    hasIVP_of_isRealClosed (specializeAt Q w) (f₁ w) (f₂ w) hlt hsign
  set S := (specializeAt Q w).roots.toFinset.filter (fun z => f₁ w < z ∧ z < f₂ w) with hSdef
  have hmem_iff : ∀ z, z ∈ S ↔ (specializeAt Q w).eval z = 0 ∧ f₁ w < z ∧ z < f₂ w := by
    intro z
    rw [hSdef, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots']
    constructor
    · rintro ⟨⟨_, hr⟩, hb⟩; exact ⟨hr, hb⟩
    · rintro ⟨hr, hb⟩; exact ⟨⟨hnz, hr⟩, hb⟩
  have hne : S.Nonempty := ⟨x₀, (hmem_iff x₀).mpr ⟨hx₀e, hx₀a, hx₀b⟩⟩
  have hc : smallestRootIn Q f₁ f₂ w = S.min' hne := by
    rw [smallestRootIn]; rw [dif_pos hne]
  rw [hc]
  obtain ⟨he, ha, hb⟩ := (hmem_iff _).mp (S.min'_mem hne)
  exact ⟨he, ha, hb, fun z hz hza hzb => S.min'_le z ((hmem_iff z).mpr ⟨hz, hza, hzb⟩)⟩

/-- **The selected root is continuous.** Under the standing hypotheses (fiber nonzero with a fixed
number of simple roots, `f₁ < f₂` continuous with `P(·, f₁) P(·, f₂) < 0`), the smallest root of
`P(w, ·)` between `f₁ w` and `f₂ w` is a continuous function of `w` on `(0, t₁)`. The branch through
the value at each point (`roots_exhausted_by_branches`) coincides with the selection nearby, because
no other root can slip below it without crossing `f₁` (which is never a root). -/
theorem continuousOn_smallestRootIn {t₁ : R} {Q : Polynomial ((Fin 1 → R) → R)}
    (hQ : HasSemialgContinuousCoeffs (rightNbhd t₁) Q) {r : ℕ}
    (hnz : ∀ w ∈ rightNbhd t₁, specializeAt Q w ≠ 0)
    (hcount : ∀ w ∈ rightNbhd t₁, (specializeAt Q w).roots.toFinset.card = r)
    (hcoprime : ∀ w ∈ rightNbhd t₁,
      IsCoprime (specializeAt Q w) (Polynomial.derivative (specializeAt Q w)))
    {f₁ f₂ : (Fin 1 → R) → R} (hf₁ : ContinuousOn (scalarFun f₁) (rightNbhd t₁))
    (hf₂ : ContinuousOn (scalarFun f₂) (rightNbhd t₁))
    (hlt : ∀ w ∈ rightNbhd t₁, f₁ w < f₂ w)
    (hsign : ∀ w ∈ rightNbhd t₁,
      (specializeAt Q w).eval (f₁ w) * (specializeAt Q w).eval (f₂ w) < 0) :
    ContinuousOn (scalarFun (smallestRootIn Q f₁ f₂)) (rightNbhd t₁) := by
  classical
  rw [continuousOn_fin_one_iff]
  intro w₀ hw₀ ε hε
  set c := smallestRootIn Q f₁ f₂ with hcdef
  obtain ⟨hce0, hcf1, hcf2, hcmin⟩ := smallestRootIn_spec (hnz w₀ hw₀) (hlt w₀ hw₀) (hsign w₀ hw₀)
  obtain ⟨U, hUopen, hw₀U, hUsub, F, hFcont, hFroot, hFmono, hFexh⟩ :=
    roots_exhausted_by_branches hQ hnz hcount hcoprime hw₀
  obtain ⟨jstar, hjstar⟩ := hFexh w₀ hw₀U (c w₀) hce0
  have hf1nr : (specializeAt Q w₀).eval (f₁ w₀) ≠ 0 :=
    left_ne_zero_of_mul (hsign w₀ hw₀).ne
  -- branches below `jstar` are below `f₁ w₀`
  have hFklt : ∀ k : Fin r, k < jstar → F k w₀ < f₁ w₀ := by
    intro k hk
    have hFkroot : (specializeAt Q w₀).eval (F k w₀) = 0 := hFroot w₀ hw₀U k
    have hFkc : F k w₀ < c w₀ := by rw [hjstar]; exact hFmono w₀ hw₀U hk
    by_contra hcon
    rw [not_lt] at hcon
    have hne : F k w₀ ≠ f₁ w₀ := fun h => hf1nr (h ▸ hFkroot)
    have hf1lt : f₁ w₀ < F k w₀ := lt_of_le_of_ne hcon (Ne.symm hne)
    have hF2 : F k w₀ < f₂ w₀ := lt_trans hFkc hcf2
    have := hcmin (F k w₀) hFkroot hf1lt hF2
    linarith
  -- radii
  have hw₀_const : w₀ = constPt (w₀ 0) := by funext i; rw [Subsingleton.elim i 0]; rfl
  obtain ⟨mU, hmUpos, HmU⟩ := exists_interval_subset_of_isOpenIn hUopen (hw₀_const ▸ hw₀U)
  obtain ⟨δA, hδApos, HδA⟩ := eventually_lt_of_continuousOn (hf₁.mono hUsub) (hFcont jstar) hw₀U
    (by rw [← hjstar]; exact hcf1)
  obtain ⟨δB, hδBpos, HδB⟩ := eventually_lt_of_continuousOn (hFcont jstar) (hf₂.mono hUsub) hw₀U
    (by rw [← hjstar]; exact hcf2)
  have hCk : ∀ k : Fin r, ∃ δ, 0 < δ ∧
      (k < jstar → ∀ w ∈ U, euclideanNorm (w - w₀) < δ → F k w < f₁ w) := by
    intro k
    by_cases hk : k < jstar
    · obtain ⟨δ, hδ, H⟩ :=
        eventually_lt_of_continuousOn (hFcont k) (hf₁.mono hUsub) hw₀U (hFklt k hk)
      exact ⟨δ, hδ, fun _ => H⟩
    · exact ⟨1, one_pos, fun h => absurd h hk⟩
  choose δC hδCpos hδC using hCk
  have hrpos : 0 < r := lt_of_le_of_lt (Nat.zero_le jstar) jstar.isLt
  haveI : NeZero r := ⟨Nat.pos_iff_ne_zero.mp hrpos⟩
  have hune : (Finset.univ : Finset (Fin r)).Nonempty := Finset.univ_nonempty
  have hFjcont := (hFcont jstar)
  rw [continuousOn_fin_one_iff] at hFjcont
  obtain ⟨δD, hδDpos, HδD⟩ := hFjcont w₀ hw₀U ε hε
  set δ : R := min (min mU δA) (min (min δB (Finset.univ.inf' hune δC)) δD) with hδdef
  have hδpos : 0 < δ :=
    lt_min (lt_min hmUpos hδApos)
      (lt_min (lt_min hδBpos ((Finset.lt_inf'_iff hune).mpr fun k _ => hδCpos k)) hδDpos)
  refine ⟨δ, hδpos, fun w hw hwx => ?_⟩
  -- bounds on `w`
  have hbU : euclideanNorm (w - w₀) < mU :=
    lt_of_lt_of_le hwx (le_trans (min_le_left _ _) (min_le_left _ _))
  have hbA : euclideanNorm (w - w₀) < δA :=
    lt_of_lt_of_le hwx (le_trans (min_le_left _ _) (min_le_right _ _))
  have hbB : euclideanNorm (w - w₀) < δB :=
    lt_of_lt_of_le hwx (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hbCinf : euclideanNorm (w - w₀) < Finset.univ.inf' hune δC :=
    lt_of_lt_of_le hwx (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hbD : euclideanNorm (w - w₀) < δD :=
    lt_of_lt_of_le hwx (le_trans (min_le_right _ _) (min_le_right _ _))
  have hwU : w ∈ U := by
    have hw_const : w = constPt (w 0) := by funext i; rw [Subsingleton.elim i 0]; rfl
    rw [hw_const]
    refine HmU (w 0) ?_ hw.1 hw.2
    have hb := hbU
    rw [euclideanNorm_fin_one, Pi.sub_apply] at hb
    exact hb
  -- the selection equals the branch through `jstar` at `w`
  obtain ⟨hcwe, hcwa, hcwb, hcwmin⟩ := smallestRootIn_spec (hnz w hw) (hlt w hw) (hsign w hw)
  have hAw : f₁ w < F jstar w := HδA w hwU hbA
  have hBw : F jstar w < f₂ w := HδB w hwU hbB
  have hle : c w ≤ F jstar w := hcwmin (F jstar w) (hFroot w hwU jstar) hAw hBw
  obtain ⟨kk, hkk⟩ := hFexh w hwU (c w) hcwe
  have hge : F jstar w ≤ c w := by
    rw [hkk]
    by_contra hcon
    rw [not_le] at hcon
    have hkkj : kk < jstar := (hFmono w hwU).lt_iff_lt.mp hcon
    have hkflt := hδC kk hkkj w hwU (lt_of_lt_of_le hbCinf (Finset.inf'_le _ (Finset.mem_univ kk)))
    rw [← hkk] at hkflt
    linarith
  have hcw : c w = F jstar w := le_antisymm hle hge
  -- conclude continuity
  simp only [scalarFun, constPt]
  rw [hcw, hjstar]
  have := HδD w hwU hbD
  simpa only [scalarFun, constPt] using this

end Azurite.BPR

/-! # BPR §3.3 — the selected root is a semialgebraic function

The continuous root selection `smallestRootIn Q f₁ f₂` (from `GermRootBranch`) is also semialgebraic.
BPR: "the function `g_i` ... is semialgebraic ... because it can be described by a formula." We build
its graph in `R²` from the bivariate zero set `{(w, v) | P(w, v) = 0}` (`isSemialgebraicFunction_bivariateEval`),
the graphs of `f₁, f₂`, polynomial order conditions, and one existential projection for the `∀v'`
minimality clause — all semialgebraic by the closure properties of §2.3/§2.5. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The bivariate zero set `Z = {(w, v) ∈ R² | w ∈ (0, t₁) ∧ P(w, v) = 0}` is semialgebraic. -/
theorem isSemialgebraicSet_fiberZero {t₁ : R} {Q : Polynomial ((Fin 1 → R) → R)}
    (hQ : HasSemialgContinuousCoeffs (rightNbhd t₁) Q) :
    IsSemialgebraicSet (setProd (rightNbhd t₁) (Set.univ : Set (Fin 1 → R)) ∩
      bivariateEval Q ⁻¹' {y : Fin 1 → R | MvPolynomial.eval y (MvPolynomial.X 0) = 0}) :=
  (proposition_2_83 (isSemialgebraicFunction_bivariateEval (isSemialgebraicSet_rightNbhd t₁) hQ)).2
    (IsSemialgebraicSet.eqZero (MvPolynomial.X 0))

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Membership in the fiber zero set, in coordinates. -/
theorem mem_fiberZero {t₁ : R} {Q : Polynomial ((Fin 1 → R) → R)} (z : Fin (1 + 1) → R) :
    z ∈ (setProd (rightNbhd t₁) (Set.univ : Set (Fin 1 → R)) ∩
      bivariateEval Q ⁻¹' {y : Fin 1 → R | MvPolynomial.eval y (MvPolynomial.X 0) = 0}) ↔
      (z ∘ Fin.castAdd 1) ∈ rightNbhd t₁ ∧
        (specializeAt Q (z ∘ Fin.castAdd 1)).eval (z (Fin.natAdd 1 (0 : Fin 1))) = 0 := by
  simp only [Set.mem_inter_iff, setProd, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ, and_true,
    bivariateEval, constPt, MvPolynomial.eval_X]

/-- **The selected root is a semialgebraic function.** Combined with `continuousOn_smallestRootIn`,
this makes `smallestRootIn Q f₁ f₂` a representative of a germ of a semialgebraic continuous function. -/
theorem isSemialgebraicFunction_smallestRootIn {t₁ : R} {Q : Polynomial ((Fin 1 → R) → R)}
    (hQ : HasSemialgContinuousCoeffs (rightNbhd t₁) Q)
    {f₁ f₂ : (Fin 1 → R) → R} (hf₁ : IsSemialgebraicFunction (rightNbhd t₁) (scalarFun f₁))
    (hf₂ : IsSemialgebraicFunction (rightNbhd t₁) (scalarFun f₂))
    (hnz : ∀ w ∈ rightNbhd t₁, specializeAt Q w ≠ 0)
    (hlt : ∀ w ∈ rightNbhd t₁, f₁ w < f₂ w)
    (hsign : ∀ w ∈ rightNbhd t₁,
      (specializeAt Q w).eval (f₁ w) * (specializeAt Q w).eval (f₂ w) < 0) :
    IsSemialgebraicFunction (rightNbhd t₁) (scalarFun (smallestRootIn Q f₁ f₂)) := by
  classical
  set Z := setProd (rightNbhd t₁) (Set.univ : Set (Fin 1 → R)) ∩
    bivariateEval Q ⁻¹' {y : Fin 1 → R | MvPolynomial.eval y (MvPolynomial.X 0) = 0} with hZdef
  have hZ : IsSemialgebraicSet Z := isSemialgebraicSet_fiberZero hQ
  have hZmem : ∀ z : Fin (1 + 1) → R, z ∈ Z ↔
      (z ∘ Fin.castAdd 1) ∈ rightNbhd t₁ ∧
        (specializeAt Q (z ∘ Fin.castAdd 1)).eval (z (Fin.natAdd 1 0)) = 0 := by
    intro z; rw [hZdef]; exact mem_fiberZero z
  -- The inner set for the `∀ v'` clause, in `Fin 5 = (w, v, s₁, s₂, v')`.
  set Inner : Set (Fin (4 + 1) → R) :=
    {z | (z ∘ ![Fin.castAdd 1 (0 : Fin 4), Fin.natAdd 4 (0 : Fin 1)]) ∈ Z} ∩
      {z | MvPolynomial.eval z (MvPolynomial.X 4 - MvPolynomial.X 2) > 0} ∩
      {z | MvPolynomial.eval z (MvPolynomial.X 3 - MvPolynomial.X 4) > 0} ∩
      {z | MvPolynomial.eval z (MvPolynomial.X 1 - MvPolynomial.X 4) > 0} with hInnerdef
  have hInner : IsSemialgebraicSet Inner :=
    (((IsSemialgebraicSet.comap _ hZ).inter (IsSemialgebraicSet.gtZero _)).inter
      (IsSemialgebraicSet.gtZero _)).inter (IsSemialgebraicSet.gtZero _)
  -- `W4 ⊆ Fin 4 = (w, v, s₁, s₂)`.
  set W4 : Set (Fin (2 + 2) → R) :=
    {z | (z ∘ Fin.castAdd 2) ∈ Z} ∩
      {z | (z ∘ ![Fin.castAdd 2 (0 : Fin 2), Fin.natAdd 2 (0 : Fin 2)])
        ∈ funGraph (rightNbhd t₁) (scalarFun f₁)} ∩
      {z | (z ∘ ![Fin.castAdd 2 (0 : Fin 2), Fin.natAdd 2 (1 : Fin 2)])
        ∈ funGraph (rightNbhd t₁) (scalarFun f₂)} ∩
      {z | MvPolynomial.eval z (MvPolynomial.X 1 - MvPolynomial.X 2) > 0} ∩
      {z | MvPolynomial.eval z (MvPolynomial.X 3 - MvPolynomial.X 1) > 0} ∩
      {z : Fin (2 + 2) → R | ∃ v' : Fin 1 → R, Fin.append z v' ∈ Inner}ᶜ with hW4def
  have hW4 : IsSemialgebraicSet W4 :=
    ((((IsSemialgebraicSet.comap _ hZ).inter (IsSemialgebraicSet.comap _ hf₁)).inter
      (IsSemialgebraicSet.comap _ hf₂)).inter (IsSemialgebraicSet.gtZero _)).inter
      (IsSemialgebraicSet.gtZero _) |>.inter hInner.exists_append_right.compl
  show IsSemialgebraicSet (funGraph (rightNbhd t₁) (scalarFun (smallestRootIn Q f₁ f₂)))
  -- coordinate-level membership in `W4` for `append z y`.
  have hW4mem : ∀ (z : Fin (1 + 1) → R) (y : Fin 2 → R),
      Fin.append z y ∈ W4 ↔
        ((z ∘ Fin.castAdd 1) ∈ rightNbhd t₁ ∧
          (specializeAt Q (z ∘ Fin.castAdd 1)).eval (z (Fin.natAdd 1 0)) = 0) ∧
        (y 0 = f₁ (z ∘ Fin.castAdd 1)) ∧ (y 1 = f₂ (z ∘ Fin.castAdd 1)) ∧
        (y 0 < z (Fin.natAdd 1 0)) ∧ (z (Fin.natAdd 1 0) < y 1) ∧
        ¬ ∃ v' : R, ((z ∘ Fin.castAdd 1) ∈ rightNbhd t₁ ∧
            (specializeAt Q (z ∘ Fin.castAdd 1)).eval v' = 0) ∧
          y 0 < v' ∧ v' < y 1 ∧ v' < z (Fin.natAdd 1 0) := by
    intro z y
    have hcast1 : ∀ b : R, (![z 0, b] : Fin 2 → R) ∘ Fin.castAdd 1 = z ∘ Fin.castAdd 1 := by
      intro b; funext i; rw [Subsingleton.elim i 0]; simp [Matrix.cons_val_zero]
    have hB : Fin.append z y ∘ ![Fin.castAdd 2 (0 : Fin 2), Fin.natAdd 2 (0 : Fin 2)]
        = ![z 0, y 0] := by
      funext i; fin_cases i <;> rfl
    have hC : Fin.append z y ∘ ![Fin.castAdd 2 (0 : Fin 2), Fin.natAdd 2 (1 : Fin 2)]
        = ![z 0, y 1] := by
      funext i; fin_cases i <;> rfl
    have hcw1 : (![z 0, y 0] : Fin 2 → R) (Fin.natAdd 1 (0 : Fin 1)) = y 0 := rfl
    have hcw2 : (![z 0, y 1] : Fin 2 → R) (Fin.natAdd 1 (0 : Fin 1)) = y 1 := rfl
    have hBmem : (![z 0, y 0] : Fin 2 → R) ∈ funGraph (rightNbhd t₁) (scalarFun f₁) ↔
        (z ∘ Fin.castAdd 1) ∈ rightNbhd t₁ ∧ y 0 = f₁ (z ∘ Fin.castAdd 1) := by
      rw [mem_funGraph, hcast1 (y 0)]
      refine and_congr_right fun _ => ?_
      constructor
      · intro h; have := congrFun h 0; simpa [scalarFun, constPt, hcw1] using this
      · intro h; funext i; rw [Subsingleton.elim i 0]; simp [scalarFun, constPt, h]
    have hCmem : (![z 0, y 1] : Fin 2 → R) ∈ funGraph (rightNbhd t₁) (scalarFun f₂) ↔
        (z ∘ Fin.castAdd 1) ∈ rightNbhd t₁ ∧ y 1 = f₂ (z ∘ Fin.castAdd 1) := by
      rw [mem_funGraph, hcast1 (y 1)]
      refine and_congr_right fun _ => ?_
      constructor
      · intro h; have := congrFun h 0; simpa [scalarFun, constPt, hcw2] using this
      · intro h; funext i; rw [Subsingleton.elim i 0]; simp [scalarFun, constPt, h]
    have hExBridge : (∃ v' : Fin 1 → R, Fin.append (Fin.append z y) v' ∈ Inner) ↔
        ∃ v'0 : R, Fin.append (Fin.append z y) (fun _ : Fin 1 => v'0) ∈ Inner := by
      constructor
      · rintro ⟨v', h⟩
        exact ⟨v' 0, by rwa [show (fun _ : Fin 1 => v' 0) = v' from
          funext fun i => by rw [Subsingleton.elim i 0]]⟩
      · rintro ⟨v'0, h⟩; exact ⟨_, h⟩
    have hInnerMem : ∀ v' : R, Fin.append (Fin.append z y) (fun _ : Fin 1 => v') ∈ Inner ↔
        ((z ∘ Fin.castAdd 1) ∈ rightNbhd t₁ ∧
          (specializeAt Q (z ∘ Fin.castAdd 1)).eval v' = 0) ∧
        y 0 < v' ∧ v' < y 1 ∧ v' < z (Fin.natAdd 1 0) := by
      intro v'
      have hZc : Fin.append (Fin.append z y) (fun _ : Fin 1 => v') ∘
          ![Fin.castAdd 1 (0 : Fin 4), Fin.natAdd 4 (0 : Fin 1)] = ![z 0, v'] := by
        funext i; fin_cases i <;> rfl
      have ha1 : Fin.append (Fin.append z y) (fun _ : Fin 1 => v') (1 : Fin (4 + 1))
        = z (Fin.natAdd 1 0) := rfl
      have ha2 : Fin.append (Fin.append z y) (fun _ : Fin 1 => v') (2 : Fin (4 + 1)) = y 0 := rfl
      have ha3 : Fin.append (Fin.append z y) (fun _ : Fin 1 => v') (3 : Fin (4 + 1)) = y 1 := rfl
      have ha4 : Fin.append (Fin.append z y) (fun _ : Fin 1 => v') (4 : Fin (4 + 1)) = v' := rfl
      have hcv : (![z 0, v'] : Fin 2 → R) (Fin.natAdd 1 (0 : Fin 1)) = v' := rfl
      simp only [hInnerdef, Set.mem_inter_iff, Set.mem_setOf_eq, hZc, hZmem, hcast1, hcv,
        MvPolynomial.eval_sub, MvPolynomial.eval_X, gt_iff_lt, ha1, ha2, ha3, ha4, sub_pos]
      tauto
    have hb1 : Fin.append z y (1 : Fin (2 + 2)) = z (Fin.natAdd 1 0) := rfl
    have hb2 : Fin.append z y (2 : Fin (2 + 2)) = y 0 := rfl
    have hb3 : Fin.append z y (3 : Fin (2 + 2)) = y 1 := rfl
    simp only [hW4def, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff,
      append_comp_castAdd, hZmem, hB, hC, hBmem, hCmem, hExBridge, hInnerMem,
      MvPolynomial.eval_sub, MvPolynomial.eval_X, gt_iff_lt, hb1, hb2, hb3, sub_pos]
    tauto
  have hgraph : funGraph (rightNbhd t₁) (scalarFun (smallestRootIn Q f₁ f₂))
      = {z : Fin (1 + 1) → R | ∃ y : Fin 2 → R, Fin.append z y ∈ W4} := by
    ext z
    rw [mem_funGraph]
    simp only [Set.mem_setOf_eq, hW4mem]
    constructor
    · rintro ⟨hwR, hvc⟩
      have hv : z (Fin.natAdd 1 0) = smallestRootIn Q f₁ f₂ (z ∘ Fin.castAdd 1) := by
        have := congrFun hvc 0; simpa [scalarFun, constPt] using this
      obtain ⟨hroot, hf1v, hvf2, hmin⟩ :=
        smallestRootIn_spec (hnz _ hwR) (hlt _ hwR) (hsign _ hwR)
      refine ⟨![f₁ (z ∘ Fin.castAdd 1), f₂ (z ∘ Fin.castAdd 1)], ⟨hwR, by rw [hv]; exact hroot⟩,
        rfl, rfl, by rw [hv]; exact hf1v, by rw [hv]; exact hvf2, ?_⟩
      rintro ⟨v', ⟨_, hv'root⟩, hv'1, hv'2, hv'lt⟩
      exact absurd (hmin v' hv'root hv'1 hv'2) (by rw [hv] at hv'lt; exact not_le.mpr hv'lt)
    · rintro ⟨y, ⟨hwR, hroot'⟩, hy0, hy1, hD, hE, hF⟩
      refine ⟨hwR, ?_⟩
      obtain ⟨hcroot, hcf1, hcf2, hcmin⟩ :=
        smallestRootIn_spec (hnz _ hwR) (hlt _ hwR) (hsign _ hwR)
      have hf1v : f₁ (z ∘ Fin.castAdd 1) < z (Fin.natAdd 1 0) := hy0 ▸ hD
      have hvf2 : z (Fin.natAdd 1 0) < f₂ (z ∘ Fin.castAdd 1) := hy1 ▸ hE
      have hveq : z (Fin.natAdd 1 0) = smallestRootIn Q f₁ f₂ (z ∘ Fin.castAdd 1) :=
        le_antisymm
          (not_lt.mp fun h => hF ⟨_, ⟨hwR, hcroot⟩, hy0 ▸ hcf1, hy1 ▸ hcf2, h⟩)
          (hcmin _ hroot' hf1v hvf2)
      funext i; rw [Subsingleton.elim i 0]; simpa [scalarFun, constPt] using hveq
  rw [hgraph]
  exact hW4.exists_append_right

end Azurite.BPR
