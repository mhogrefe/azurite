import Azurite.BasuPollackRoy.Chapter2.Section2_1.Corollary_2_23
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Corollary_2_24
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_25
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_21

/-!
# BPR Proposition 2.27: Basic Thom's Lemma

**Proposition 2.27 (BPR).** Let `P ∈ R[X]` have degree `p` and let `σ` be a
sign condition on `Der(P)`. Then `Reali(σ)` is either empty, a point, or an
open interval.

The proof is by induction on the depth `n` of the derivative list.
-/

namespace Azurite.BPR.Proposition2_27

open Polynomial Azurite.BPR Azurite.BPR.Proposition2_21
  Azurite.BPR.Corollary2_23 Azurite.BPR.Corollary2_24

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Open interval predicate -/

/-- A set is an **open interval** (possibly unbounded): nonempty, ord-connected,
    and every element has strictly smaller and larger elements in the set. -/
def IsOpenInterval (S : Set R) : Prop :=
  S.Nonempty ∧ S.OrdConnected ∧
  (∀ x ∈ S, ∃ y ∈ S, y < x) ∧
  (∀ x ∈ S, ∃ y ∈ S, x < y)

private lemma isOpenInterval_univ : IsOpenInterval (Set.univ : Set R) :=
  ⟨⟨0, trivial⟩, Set.ordConnected_univ,
   fun x _ => ⟨x - 1, trivial, sub_lt_self x one_pos⟩,
   fun x _ => ⟨x + 1, trivial, lt_add_one x⟩⟩

private lemma isOpenInterval_inter_Ioi {S : Set R} (hS : IsOpenInterval S)
    {c : R} (hcS : c ∈ S) (hgt : ∃ y ∈ S, c < y) :
    IsOpenInterval (S ∩ Set.Ioi c) := by
  obtain ⟨y₀, hy₀S, hcy₀⟩ := hgt
  refine ⟨⟨y₀, hy₀S, hcy₀⟩, hS.2.1.inter Set.ordConnected_Ioi, ?_, ?_⟩
  · intro x ⟨hxS, (hcx : c < x)⟩
    exact ⟨(c + x) / 2,
      ⟨hS.2.1.out hcS hxS ⟨by linarith, by linarith⟩, by show c < _; linarith⟩,
      by linarith⟩
  · intro x ⟨hxS, hcx⟩
    obtain ⟨z, hzS, hxz⟩ := hS.2.2.2 x hxS
    exact ⟨z, ⟨hzS, lt_trans hcx hxz⟩, hxz⟩

private lemma isOpenInterval_inter_Iio {S : Set R} (hS : IsOpenInterval S)
    {c : R} (hcS : c ∈ S) (hlt : ∃ y ∈ S, y < c) :
    IsOpenInterval (S ∩ Set.Iio c) := by
  obtain ⟨y₀, hy₀S, hy₀c⟩ := hlt
  refine ⟨⟨y₀, hy₀S, hy₀c⟩, hS.2.1.inter Set.ordConnected_Iio, ?_, ?_⟩
  · intro x ⟨hxS, hxc⟩
    obtain ⟨z, hzS, hzx⟩ := hS.2.2.1 x hxS
    exact ⟨z, ⟨hzS, lt_trans hzx hxc⟩, hzx⟩
  · intro x ⟨hxS, (hxc : x < c)⟩
    exact ⟨(x + c) / 2,
      ⟨hS.2.1.out hxS hcS ⟨by linarith, by linarith⟩, by show _ < c; linarith⟩,
      by linarith⟩

/-! ### Derivative realization set -/

/-- The realization set of sign condition `σ` on the first `n + 1` derivatives
    of `P`: `{x | ∀ i ≤ n, sign(P⁽ⁱ⁾(x)) = σ(i)}`. -/
noncomputable def derReali (P : R[X]) (n : ℕ) (σ : ℕ → SignType) : Set R :=
  {x | ∀ i ≤ n, SignType.sign (((⇑derivative)^[i] P).eval x) = σ i}

/-! ### Monotonicity from derivative sign on open intervals -/

lemma strictMonoOn_of_deriv_pos (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {S : Set R} (hS : IsOpenInterval S)
    (hP' : ∀ x ∈ S, 0 < (derivative P).eval x) :
    StrictMonoOn (fun x => P.eval x) S := by
  intro a ha b hb hab
  have hder : ∀ z ∈ Set.Ioo a b, 0 < (derivative P).eval z :=
    fun z ⟨haz, hzb⟩ => hP' z (hS.2.1.out ha hb ⟨le_of_lt haz, le_of_lt hzb⟩)
  exact corollary_2_24_increasing hIVP P hab hder
    (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) hab

lemma strictAntiOn_of_deriv_neg (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {S : Set R} (hS : IsOpenInterval S)
    (hP' : ∀ x ∈ S, (derivative P).eval x < 0) :
    StrictAntiOn (fun x => P.eval x) S := by
  intro a ha b hb hab
  have hder : ∀ z ∈ Set.Ioo a b, (derivative P).eval z < 0 :=
    fun z ⟨haz, hzb⟩ => hP' z (hS.2.1.out ha hb ⟨le_of_lt haz, le_of_lt hzb⟩)
  exact corollary_2_24_decreasing hIVP P hab hder
    (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) hab

/-! ### Sign filter for strictly monotone polynomials -/

/-- For a strictly increasing polynomial on an open interval, filtering by a
    sign condition gives ∅, a singleton, or an open interval. -/
private lemma sign_filter_mono (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {S : Set R} (hS : IsOpenInterval S)
    (hmono : StrictMonoOn (fun x => P.eval x) S) (s : SignType) :
    let T := {x ∈ S | SignType.sign (P.eval x) = s}
    T = ∅ ∨ (∃ a, T = {a}) ∨ IsOpenInterval T := by
  intro T
  by_cases hT : T.Nonempty
  swap; · left; exact Set.not_nonempty_iff_eq_empty.mp hT
  obtain ⟨x₀, hx₀S, hx₀sign⟩ := hT
  -- Case split on s via rcases + rfl to substitute everywhere
  have hs : s = 0 ∨ s = 1 ∨ s = -1 := by
    rcases s with _ | _ | _
    · left; rfl
    · right; right; rfl
    · right; left; rfl
  rcases hs with rfl | rfl | rfl
  · -- s = 0: P(x₀) = 0, at most one root by strict monotonicity
    right; left
    have hPx₀ : P.eval x₀ = 0 := sign_eq_zero_iff.mp hx₀sign
    refine ⟨x₀, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hx₀S, hx₀sign⟩, ?_⟩⟩
    intro y ⟨hyS, hysign⟩
    have hPy : P.eval y = 0 := sign_eq_zero_iff.mp hysign
    exact hmono.injOn hyS hx₀S (by linarith)
  · -- s = 1: P(x₀) > 0, T is a tail of S
    right; right
    have hPx₀ : 0 < P.eval x₀ := sign_eq_one_iff.mp hx₀sign
    by_cases hall : ∀ x ∈ S, 0 < P.eval x
    · -- T = S
      suffices T = S from this ▸ hS
      ext x; exact ⟨fun ⟨h, _⟩ => h, fun hxS => ⟨hxS, sign_pos (hall x hxS)⟩⟩
    · -- Find root c, T = S ∩ Ioi c
      push Not at hall; obtain ⟨x₁, hx₁S, hx₁⟩ := hall
      have hx₁x₀ : x₁ < x₀ := by
        rcases lt_trichotomy x₁ x₀ with h | rfl | h
        · exact h
        · linarith
        · have : P.eval x₀ < P.eval x₁ := hmono hx₀S hx₁S h; linarith
      obtain ⟨c, hcS, hPc, hcx₀⟩ : ∃ c ∈ S, P.eval c = 0 ∧ c < x₀ := by
        rcases hx₁.eq_or_lt with hx₁eq | hx₁neg
        · exact ⟨x₁, hx₁S, hx₁eq, hx₁x₀⟩
        · obtain ⟨c, hx₁c, hcx₀, hPc⟩ := hIVP P x₁ x₀ hx₁x₀ (by nlinarith)
          exact ⟨c, hS.2.1.out hx₁S hx₀S ⟨le_of_lt hx₁c, le_of_lt hcx₀⟩, hPc, hcx₀⟩
      suffices hTeq : T = S ∩ Set.Ioi c from
        hTeq ▸ isOpenInterval_inter_Ioi hS hcS ⟨x₀, hx₀S, hcx₀⟩
      ext x; constructor
      · intro ⟨hxS, hxsign⟩
        have hPx : 0 < P.eval x := sign_eq_one_iff.mp hxsign
        refine ⟨hxS, ?_⟩
        rcases lt_trichotomy c x with h | rfl | h
        · exact h
        · linarith
        · have : P.eval x < P.eval c := hmono hxS hcS h; linarith
      · intro ⟨hxS, (hcx : c < x)⟩
        have hlt : P.eval c < P.eval x := hmono hcS hxS hcx
        exact ⟨hxS, sign_pos (by linarith)⟩
  · -- s = -1: P(x₀) < 0, T is an initial segment of S
    right; right
    have hPx₀ : P.eval x₀ < 0 := sign_eq_neg_one_iff.mp hx₀sign
    by_cases hall : ∀ x ∈ S, P.eval x < 0
    · suffices T = S from this ▸ hS
      ext x; exact ⟨fun ⟨h, _⟩ => h, fun hxS => ⟨hxS, sign_neg (hall x hxS)⟩⟩
    · push Not at hall; obtain ⟨x₁, hx₁S, hx₁⟩ := hall
      have hx₀x₁ : x₀ < x₁ := by
        rcases lt_trichotomy x₀ x₁ with h | rfl | h
        · exact h
        · linarith
        · have : P.eval x₁ < P.eval x₀ := hmono hx₁S hx₀S h; linarith
      obtain ⟨c, hcS, hPc, hx₀c⟩ : ∃ c ∈ S, P.eval c = 0 ∧ x₀ < c := by
        rcases hx₁.eq_or_lt with hx₁eq | hx₁pos
        · exact ⟨x₁, hx₁S, hx₁eq.symm, hx₀x₁⟩
        · obtain ⟨c, hx₀c, hcx₁, hPc⟩ := hIVP P x₀ x₁ hx₀x₁ (by nlinarith)
          exact ⟨c, hS.2.1.out hx₀S hx₁S ⟨le_of_lt hx₀c, le_of_lt hcx₁⟩, hPc, hx₀c⟩
      suffices hTeq : T = S ∩ Set.Iio c from
        hTeq ▸ isOpenInterval_inter_Iio hS hcS ⟨x₀, hx₀S, hx₀c⟩
      ext x; constructor
      · intro ⟨hxS, hxsign⟩
        have hPx : P.eval x < 0 := sign_eq_neg_one_iff.mp hxsign
        refine ⟨hxS, ?_⟩
        rcases lt_trichotomy x c with h | rfl | h
        · exact h
        · linarith
        · have : P.eval c < P.eval x := hmono hcS hxS h; linarith
      · intro ⟨hxS, (hxc : x < c)⟩
        have hlt : P.eval x < P.eval c := hmono hxS hcS hxc
        exact ⟨hxS, sign_neg (by linarith)⟩

/-- Strictly anti-monotone version, derived via negation. -/
private lemma sign_filter_anti (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {S : Set R} (hS : IsOpenInterval S)
    (hanti : StrictAntiOn (fun x => P.eval x) S) (s : SignType) :
    let T := {x ∈ S | SignType.sign (P.eval x) = s}
    T = ∅ ∨ (∃ a, T = {a}) ∨ IsOpenInterval T := by
  have hmono : StrictMonoOn (fun x => (-P).eval x) S := by
    intro a ha b hb hab; simp only [eval_neg]; exact neg_lt_neg (hanti ha hb hab)
  have hTeq : {x ∈ S | SignType.sign (P.eval x) = s} =
      {x ∈ S | SignType.sign ((-P).eval x) = -s} := by
    ext x; simp only [Set.mem_sep_iff, eval_neg]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [Left.sign_neg, h2]⟩
    · rintro ⟨h1, h2⟩
      rw [Left.sign_neg] at h2
      exact ⟨h1, by have := congr_arg Neg.neg h2; simpa using this⟩
  intro T; rw [show T = {x ∈ S | SignType.sign (P.eval x) = s} from rfl, hTeq]
  exact sign_filter_mono hIVP hS hmono (-s)

/-! ### Proposition 2.27 -/

/-- **BPR Proposition 2.27 (Basic Thom's Lemma).** Let `P ∈ R[X]` with
    `natDegree P ≤ n` and `σ` a sign condition on the first `n + 1`
    derivatives. Then `Reali(σ)` is either empty, a point, or an open
    interval. -/
theorem proposition_2_27 (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) (n : ℕ) (σ : ℕ → SignType) (hn : P.natDegree ≤ n) :
    let S := derReali P n σ
    S = ∅ ∨ (∃ a, S = {a}) ∨ IsOpenInterval S := by
  intro S
  induction n generalizing P σ with
  | zero =>
    -- n = 0 means P is constant
    have hP_eq : ∀ x : R, P.eval x = P.coeff 0 := by
      have hP := eq_C_of_natDegree_le_zero hn
      intro x; conv_lhs => rw [hP]
      simp
    by_cases hsign : SignType.sign (P.coeff 0) = σ 0
    · right; right
      suffices S = Set.univ from this ▸ isOpenInterval_univ
      ext x; refine ⟨fun _ => trivial, fun _ i hi => ?_⟩
      rw [Nat.le_zero.mp hi, Function.iterate_zero_apply, hP_eq]; exact hsign
    · left; ext x; refine ⟨fun hx => ?_, fun hx => hx.elim⟩
      exact hsign (by have := hx 0 (le_refl 0); rwa [Function.iterate_zero_apply, hP_eq] at this)
  | succ n ih =>
    -- Decompose: derReali P (n+1) σ = {sign(P.eval x) = σ 0} ∩ derReali P' n σ'
    set σ' := fun i => σ (i + 1)
    set S' := derReali (derivative P) n σ'
    have hdecomp : S = {x | SignType.sign (P.eval x) = σ 0} ∩ S' := by
      ext x
      simp only [S, S', derReali, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro h
        refine ⟨?_, fun i hi => ?_⟩
        · have := h 0 (Nat.zero_le _)
          rwa [Function.iterate_zero_apply] at this
        · have := h (i + 1) (by omega)
          rwa [Function.iterate_succ_apply] at this
      · intro ⟨h0, htail⟩ i hi
        rcases i with _ | i
        · rwa [Function.iterate_zero_apply]
        · rw [Function.iterate_succ_apply]
          exact htail i (by omega)
    -- IH on derivative P
    have hP'deg : (derivative P).natDegree ≤ n := by
      have h1 := natDegree_derivative_le (p := P)
      omega
    rcases ih (derivative P) σ' hP'deg with hS'_empty | ⟨a, hS'_sing⟩ | hS'_open
    · -- S' = ∅: S ⊆ S' = ∅
      left; rw [hdecomp, show S' = ∅ from hS'_empty, Set.inter_empty]
    · -- S' = {a}: S ⊆ {a}
      rw [hdecomp, show S' = {a} from hS'_sing]
      by_cases ha : SignType.sign (P.eval a) = σ 0
      · right; left
        refine ⟨a, ?_⟩
        ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h ▸ ha, h⟩⟩
      · left
        ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hxsign hx; exact ha (hx ▸ hxsign)
    · -- S' is an open interval
      rw [hdecomp]
      -- hS'_open uses the unfolded form; convert to S'
      have hS'_open' : IsOpenInterval S' := hS'_open
      -- Extract that P' has constant sign σ(1) on S'
      have hP'_sign : ∀ x ∈ S', SignType.sign ((derivative P).eval x) = σ 1 := by
        intro x hx
        have := hx 0 (Nat.zero_le n)
        rwa [Function.iterate_zero_apply] at this
      -- Case split on σ(1)
      have hσ1_cases : σ 1 = 0 ∨ σ 1 = 1 ∨ σ 1 = -1 := by
        rcases (σ 1) with _ | _ | _
        · left; rfl
        · right; right; rfl
        · right; left; rfl
      rcases hσ1_cases with hσ1 | hσ1 | hσ1
      · -- σ(1) = 0: P' = 0 on S', so P is constant on S' via MVT
        have hP'_zero : ∀ x ∈ S', (derivative P).eval x = 0 := by
          intro x hx
          have h := hP'_sign x hx; rw [hσ1] at h
          exact sign_eq_zero_iff.mp h
        have hP_const : ∀ x ∈ S', ∀ y ∈ S', P.eval x = P.eval y := by
          suffices ∀ x ∈ S', ∀ y ∈ S', x < y → P.eval x = P.eval y by
            intro x hx y hy
            rcases lt_trichotomy x y with h | rfl | h
            · exact this x hx y hy h
            · rfl
            · exact (this y hy x hx h).symm
          intro x hx y hy hxy
          obtain ⟨c, hc, hMVT⟩ := corollary_2_23 hIVP P hxy
          have hcS' : c ∈ S' :=
            hS'_open'.2.1.out hx hy ⟨le_of_lt hc.1, le_of_lt hc.2⟩
          have h0 := hP'_zero c hcS'
          linarith [show (y - x) * (derivative P).eval c = 0 from by rw [h0, mul_zero]]
        -- derReali = S' or ∅
        obtain ⟨a, haS'⟩ := hS'_open'.1
        by_cases ha : SignType.sign (P.eval a) = σ 0
        · right; right
          suffices h : {x | SignType.sign (P.eval x) = σ 0} ∩ S' = S' by
            rw [h]; exact hS'_open'
          ext x; constructor
          · exact fun ⟨_, h⟩ => h
          · intro hx
            refine ⟨?_, hx⟩
            show SignType.sign (P.eval x) = σ 0
            rw [hP_const x hx a haS']; exact ha
        · left
          ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro hxsign hxS'
          exact ha (by rw [hP_const a haS' x hxS']; exact hxsign)
      · -- σ(1) = 1: P' > 0 on S', P strictly increasing
        have hP'_pos : ∀ x ∈ S', 0 < (derivative P).eval x := by
          intro x hx
          have h := hP'_sign x hx; rw [hσ1] at h
          exact sign_eq_one_iff.mp h
        have hmono := strictMonoOn_of_deriv_pos hIVP hS'_open' hP'_pos
        have hTeq : {x | SignType.sign (P.eval x) = σ 0} ∩ S' =
            {x ∈ S' | SignType.sign (P.eval x) = σ 0} := by
          ext x; simp [Set.mem_inter_iff, and_comm]
        rw [hTeq]
        exact sign_filter_mono hIVP hS'_open' hmono (σ 0)
      · -- σ(1) = -1: P' < 0 on S', P strictly decreasing
        have hP'_neg : ∀ x ∈ S', (derivative P).eval x < 0 := by
          intro x hx
          have h := hP'_sign x hx; rw [hσ1] at h
          exact sign_eq_neg_one_iff.mp h
        have hanti := strictAntiOn_of_deriv_neg hIVP hS'_open' hP'_neg
        have hTeq : {x | SignType.sign (P.eval x) = σ 0} ∩ S' =
            {x ∈ S' | SignType.sign (P.eval x) = σ 0} := by
          ext x; simp [Set.mem_inter_iff, and_comm]
        rw [hTeq]
        exact sign_filter_anti hIVP hS'_open' hanti (σ 0)

/-- **Proposition 2.27, real closed form.** -/
theorem proposition_2_27_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) (n : ℕ) (σ : ℕ → SignType) (hn : P.natDegree ≤ n) :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    let S := derReali P n σ
    S = ∅ ∨ (∃ a, S = {a}) ∨ IsOpenInterval S := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  haveI : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  exact proposition_2_27 Theorem2_11.theorem_2_11_b_c P n σ hn

end Azurite.BPR.Proposition2_27
