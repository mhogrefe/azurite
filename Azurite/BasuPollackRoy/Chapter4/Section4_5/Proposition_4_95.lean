import Azurite.BasuPollackRoy.Chapter4.Section4_5.SimpleZero
import Azurite.BasuPollackRoy.Chapter4.Section4_5.NonsingularZero
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Definitions
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_92
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_93
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Data.List.TFAE
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# BPR §4.5, Proposition 4.95: characterizations of a non-singular / simple zero

For a zero-dimensional system `𝒫 = {P₁, …, P_k} ⊂ K[X₁, …, X_k]` and a zero `x ∈ Cᵏ`, the
following are equivalent:
* (a) `x` is a non-singular zero of `𝒫`;
* (b) `x` is simple (multiplicity `1`, `Ā_x = C`);
* (c) `M_x ⊆ Ideal(𝒫, C) + M_x²`, where `M_x` is the ideal of elements of `C[X₁, …, X_k]`
  vanishing at `x`.

(Statement only for now; the proof — a TFAE chain — is to follow.)
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K]

section NonsingularImpCotangent

variable {R : Type*} [Field R]

/-- The generator `X i - C (x i)` of the maximal ideal `M_x`. -/
private noncomputable def gen (x : Fin k → R) (i : Fin k) : MvPolynomial (Fin k) R :=
  (X i : MvPolynomial (Fin k) R) - C (x i)

private theorem gen_mem_vanishing (x : Fin k → R) (i : Fin k) :
    gen x i ∈ MvPolynomial.vanishingIdeal R ({x} : Set (Fin k → R)) := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  simp [gen, map_sub]

/-- **Step A.** `M_x` is the span of the generators `X i - C (x i)`. -/
private theorem vanishing_eq_span (x : Fin k → R) :
    MvPolynomial.vanishingIdeal R ({x} : Set (Fin k → R))
      = Ideal.span (Set.range (gen x)) := by
  apply le_antisymm
  · -- M ≤ span
    have sub_const_mem_span : ∀ p : MvPolynomial (Fin k) R,
        p - C (MvPolynomial.aeval x p) ∈ Ideal.span (Set.range (gen x)) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
          have : (p + q) - C (MvPolynomial.aeval x (p + q))
              = (p - C (MvPolynomial.aeval x p)) + (q - C (MvPolynomial.aeval x q)) := by
            rw [map_add, map_add]; ring
          rw [this]
          exact Ideal.add_mem _ hp hq
      | mul_X p j hp =>
          have hgenj : gen x j ∈ Ideal.span (Set.range (gen x)) :=
            Ideal.subset_span ⟨j, rfl⟩
          have key : p * X j - C (MvPolynomial.aeval x (p * X j))
              = (p - C (MvPolynomial.aeval x p)) * X j
                + C (MvPolynomial.aeval x p) * gen x j := by
            simp only [gen, map_mul, aeval_X]
            ring
          rw [key]
          exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp)
            (Ideal.mul_mem_left _ _ hgenj)
    intro p hp
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hp
    have hpx : MvPolynomial.aeval x p = 0 := hp x (Set.mem_singleton _)
    have := sub_const_mem_span p
    rwa [hpx, map_zero, sub_zero] at this
  · -- span ≤ M
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact gen_mem_vanishing x i

/-- **Step B (Taylor remainder).** For any `p`, the first-order Taylor remainder of `p` at `x`
lies in `M_x²`. -/
private theorem taylor_mem (x : Fin k → R) (p : MvPolynomial (Fin k) R) :
    p - C (MvPolynomial.aeval x p)
        - ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i p)) * gen x i
      ∈ (MvPolynomial.vanishingIdeal R ({x} : Set (Fin k → R))) ^ 2 := by
  set M := MvPolynomial.vanishingIdeal R ({x} : Set (Fin k → R)) with hM
  have hMsq : M ^ 2 = M * M := sq M
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      have heq : (p + q) - C (MvPolynomial.aeval x (p + q))
            - ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i (p + q))) * gen x i
          = (p - C (MvPolynomial.aeval x p)
              - ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i p)) * gen x i)
            + (q - C (MvPolynomial.aeval x q)
              - ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i q)) * gen x i) := by
        have hsum : ∀ r s : MvPolynomial (Fin k) R,
            ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i (r + s))) * gen x i
            = (∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i r)) * gen x i)
              + ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i s)) * gen x i := by
          intro r s
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_add, map_add, map_add, add_mul]
        rw [hsum, map_add, map_add]
        ring
      rw [heq]
      exact Ideal.add_mem _ hp hq
  | mul_X p j hp =>
      -- abbreviations
      set a := MvPolynomial.aeval x p with ha
      set b : Fin k → R := fun i => MvPolynomial.aeval x (MvPolynomial.pderiv i p) with hb
      -- the Taylor remainder of `p` (the IH term)
      set S : MvPolynomial (Fin k) R := ∑ i, C (b i) * gen x i with hS
      set E : MvPolynomial (Fin k) R := p - C a - S with hE
      -- aeval of derivative of `p * X j`
      have hderiv : ∀ i, MvPolynomial.aeval x (MvPolynomial.pderiv i (p * X j))
          = b i * x j + (if i = j then a else 0) := by
        intro i
        rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, aeval_X]
        by_cases hij : i = j
        · subst hij
          rw [MvPolynomial.pderiv_X_self, map_one, ite_eq_left rfl, mul_one, ← ha]
        · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij), map_zero, mul_zero, add_zero, ite_eq_right hij,
            add_zero]
      have haevalmul : MvPolynomial.aeval x (p * X j) = a * x j := by
        rw [map_mul, aeval_X]
      -- rewrite the sum of derivative-terms as `C (x j) * S + C a * gen j`
      have hsumderiv :
          ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i (p * X j))) * gen x i
          = C (x j) * S + C a * gen x j := by
        have step : ∀ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i (p * X j))) * gen x i
            = C (x j) * (C (b i) * gen x i) + (if i = j then C a * gen x j else 0) := by
          intro i
          rw [hderiv, map_add, add_mul]
          by_cases hij : i = j
          · subst hij
            rw [ite_eq_left rfl, ite_eq_left rfl, map_mul]; ring
          · rw [ite_eq_right hij, ite_eq_right hij, map_zero, zero_mul, add_zero, map_mul]; ring
        rw [Finset.sum_congr rfl (fun i _ => step i), Finset.sum_add_distrib,
          Finset.sum_ite_eq' Finset.univ j (fun _ => C a * gen x j)]
        rw [ite_eq_left (Finset.mem_univ j), ← Finset.mul_sum]
      -- the main polynomial identity
      have hSgenj : (∑ i, C (b i) * (gen x i * gen x j)) = S * gen x j := by
        rw [hS, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => by ring
      have key : (p * X j) - C (MvPolynomial.aeval x (p * X j))
          - ∑ i, C (MvPolynomial.aeval x (MvPolynomial.pderiv i (p * X j))) * gen x i
          = (∑ i, C (b i) * (gen x i * gen x j)) + E * X j := by
        rw [hsumderiv, haevalmul, hSgenj, hE]
        have hgenj : gen x j = X j - C (x j) := rfl
        have hCmul : (C (a * x j) : MvPolynomial (Fin k) R) = C a * C (x j) := by rw [map_mul]
        rw [hgenj, hCmul]
        ring
      rw [key]
      -- both summands lie in M²
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hp)
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hMsq]
      exact Ideal.mul_mem_left _ _
        (Ideal.mul_mem_mul (gen_mem_vanishing x i) (gen_mem_vanishing x j))

end NonsingularImpCotangent

/-- **BPR Proposition 4.95, implication (a) ⟹ (c).** If `x` is a non-singular zero of the
extended system `map(P₁), …, map(P_k)` over `C`, then the maximal ideal `M_x` of `x` is contained
in `Ideal(𝒫, C) + M_x²`. (No `IsAlgClosed`/`CharZero` is needed for this direction.) -/
theorem nonsingular_imp_cotangent {C : Type*} [Field C] [Algebra K C]
    (P : Fin k → MvPolynomial (Fin k) K) (x : Fin k → C)
    (ha : IsNonsingularZero (fun i => MvPolynomial.map (algebraMap K C) (P i)) x) :
    MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C))
      ≤ idealOfPolysExt C (Finset.univ.image P)
        + (MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C))) ^ 2 := by
  classical
  set M := MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C)) with hM
  set I := idealOfPolysExt C (Finset.univ.image P) + M ^ 2 with hI
  -- The Jacobian of the extended system at `x`.
  set Pt : Fin k → MvPolynomial (Fin k) C :=
    fun i => MvPolynomial.map (algebraMap K C) (P i) with hPt
  set J := jacobian Pt x with hJ
  obtain ⟨hzero, hdet⟩ := ha
  -- `J.det` is a unit, so `J` is invertible.
  have hunit : IsUnit J.det := (isUnit_iff_ne_zero).2 hdet
  -- Each `Pt j` is a generator of `Ideal(𝒫, C)`.
  have hPt_mem : ∀ j, Pt j ∈ idealOfPolysExt C (Finset.univ.image P) := by
    intro j
    refine Ideal.subset_span ?_
    rw [Finset.coe_image, Set.mem_image]
    exact ⟨P j, by rw [Finset.coe_image, Set.mem_image]; exact ⟨j, Finset.mem_univ j, rfl⟩, rfl⟩
  -- Step C, part 1: `∑ i, C (J j i) * gen i ∈ I` for each `j`.
  have hw : ∀ j, (∑ i, MvPolynomial.C (J j i) * gen x i) ∈ I := by
    intro j
    have htay := taylor_mem x (Pt j)
    -- `aeval x (Pt j) = 0`
    have h0 : MvPolynomial.aeval x (Pt j) = 0 := hzero j
    -- `aeval x (pderiv i (Pt j)) = J j i`
    have hderiv : ∀ i, MvPolynomial.aeval x (MvPolynomial.pderiv i (Pt j)) = J j i := by
      intro i; rfl
    rw [h0, map_zero, sub_zero] at htay
    rw [Finset.sum_congr rfl (fun i _ => by rw [hderiv i] :
      ∀ i ∈ Finset.univ,
        MvPolynomial.C (MvPolynomial.aeval x (MvPolynomial.pderiv i (Pt j))) * gen x i
          = MvPolynomial.C (J j i) * gen x i)] at htay
    -- `Pt j - ∑ ... ∈ M²`, and `Pt j ∈ Ideal(𝒫,C)`, so the sum `∈ I`.
    have h1 : Pt j ∈ I := Ideal.mem_sup_left (hPt_mem j)
    have h2 : Pt j - ∑ i, MvPolynomial.C (J j i) * gen x i ∈ I :=
      Ideal.mem_sup_right htay
    have : (∑ i, MvPolynomial.C (J j i) * gen x i)
        = Pt j - (Pt j - ∑ i, MvPolynomial.C (J j i) * gen x i) := by ring
    rw [this]
    exact Ideal.sub_mem _ h1 h2
  -- Step C, part 2: each `gen i ∈ I`, via the inverse of `J`.
  have hgen : ∀ i, gen x i ∈ I := by
    intro i
    have hexpand : gen x i
        = ∑ j, MvPolynomial.C (J⁻¹ i j) * (∑ l, MvPolynomial.C (J j l) * gen x l) := by
      have hstep1 : (∑ j, MvPolynomial.C (J⁻¹ i j) * (∑ l, MvPolynomial.C (J j l) * gen x l))
          = ∑ l, MvPolynomial.C ((J⁻¹ * J) i l) * gen x l := by
        rw [Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum] :
          ∀ j ∈ Finset.univ,
            MvPolynomial.C (J⁻¹ i j) * (∑ l, MvPolynomial.C (J j l) * gen x l)
              = ∑ l, MvPolynomial.C (J⁻¹ i j) * (MvPolynomial.C (J j l) * gen x l))]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]; ring
      rw [hstep1, Matrix.nonsing_inv_mul J hunit]
      rw [Finset.sum_congr rfl (fun l _ => by rw [Matrix.one_apply] :
        ∀ l ∈ Finset.univ,
          MvPolynomial.C ((1 : Matrix (Fin k) (Fin k) C) i l) * gen x l
            = MvPolynomial.C (if i = l then 1 else 0) * gen x l)]
      rw [Finset.sum_congr rfl (fun l _ => by
        by_cases h : i = l
        · rw [ite_eq_left h, ite_eq_left h, map_one, one_mul]
        · rw [ite_eq_right h, ite_eq_right h, map_zero, zero_mul] :
        ∀ l ∈ Finset.univ,
          MvPolynomial.C (if i = l then 1 else 0) * gen x l
            = (if i = l then gen x l else 0))]
      rw [Finset.sum_ite_eq Finset.univ i (gen x), ite_eq_left (Finset.mem_univ i)]
    rw [hexpand]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Ideal.mul_mem_left _ _ (hw j)
  -- Assembly: `M = span (gen)` and every generator is in `I`.
  rw [hM, vanishing_eq_span]
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hgen i

section CotangentImpSimple

variable {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]

omit [IsAlgClosed C] in
/-- **The maximal ideal `m = Ideal.map mk M` equals `ker (evalBar)`.** -/
private theorem map_vanishing_eq_ker (P : Fin k → MvPolynomial (Fin k) K) (x : Fin k → C)
    (hx : x ∈ zerOfFinset C (Finset.univ.image P)) :
    Ideal.map (Ideal.Quotient.mk (idealOfPolysExt C (Finset.univ.image P)))
        (MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C)))
      = RingHom.ker (evalBar C (Finset.univ.image P) x hx) := by
  set Ps := Finset.univ.image P
  set mk := Ideal.Quotient.mk (idealOfPolysExt C Ps)
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker, evalBar_mk]
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hp
    exact hp x (Set.mem_singleton _)
  · intro w hw
    obtain ⟨W, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [RingHom.mem_ker, evalBar_mk] at hw
    have hWM : W ∈ MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C)) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy; subst hy; exact hw
    exact Ideal.mem_map_of_mem mk hWM

end CotangentImpSimple

/-- **BPR Proposition 4.95, implication (c) ⟹ (b).** If the maximal ideal `M_x` of `x` is
contained in `Ideal(𝒫, C) + M_x²`, then `x` is a simple zero. -/
theorem cotangent_imp_simple [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]
    (P : Fin k → MvPolynomial (Fin k) K) (hzd : IsZeroDimensional C (Finset.univ.image P))
    (x : Fin k → C) (hx : x ∈ zerOfFinset C (Finset.univ.image P))
    (hc : MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C))
            ≤ idealOfPolysExt C (Finset.univ.image P)
              + (MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C))) ^ 2) :
    IsSimpleZero C (Finset.univ.image P) x hx := by
  classical
  set Ps := Finset.univ.image P with hPs
  set M := MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C)) with hMdef
  set mk := Ideal.Quotient.mk (idealOfPolysExt C Ps) with hmkdef
  set m : Ideal (quotPolysExt C Ps) := Ideal.map mk M with hmdef
  -- The idempotent `ex` at `x` from Proposition 4.92.
  obtain ⟨e, _hsum, _horth, hsq, heval1, heval0⟩ := proposition_4_92 (C := C) Ps hzd.2
  set ex : quotPolysExt C Ps := e x with hexdef
  have hexidem : ex ^ 2 = ex := hsq x (hzd.2.mem_toFinset.mpr hx)
  have hex_eval1 : evalBar C Ps x hx ex = 1 := heval1 x hx
  -- `ker (evalBar) = m`.
  have hker : RingHom.ker (evalBar C Ps x hx) = m :=
    (map_vanishing_eq_ker P x hx).symm
  -- Step 1a: `m = m^2`.
  have hm_sq : m = m ^ 2 := by
    have hmap : Ideal.map mk M ≤ Ideal.map mk (idealOfPolysExt C Ps + M ^ 2) :=
      Ideal.map_mono hc
    rw [Ideal.add_eq_sup, Ideal.map_sup, Ideal.map_quotient_self, Ideal.map_pow] at hmap
    have : (⊥ : Ideal (quotPolysExt C Ps)) ⊔ (Ideal.map mk M) ^ 2 = m ^ 2 := by
      rw [bot_sup_eq]
    rw [this] at hmap
    exact le_antisymm hmap (Ideal.pow_le_self (by norm_num))
  -- `m = m^j` for all `j ≥ 1`.
  have hm_pow : ∀ j, 1 ≤ j → m = m ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rw [pow_one]
    | succ n hn ih =>
        rw [pow_succ, ← ih, ← sq, ← hm_sq]
  -- Step 1b: the ideal `N := span (range (mk (gen x ·) * ex))` is nilpotent.
  set g : Fin k → quotPolysExt C Ps := fun i => mk (gen x i) * ex with hgdef
  have hg_nilp : ∀ i, IsNilpotent (g i) := by
    intro i
    refine nilpotent_of_eval_zero Ps (g i) ?_
    intro z hz
    rw [hgdef]
    simp only
    rw [map_mul]
    by_cases hzx : z = x
    · subst hzx
      have : evalBar C Ps z hz (mk (gen z i)) = 0 := by
        rw [hmkdef, evalBar_mk]; show MvPolynomial.aeval z (gen z i) = 0; simp [gen, map_sub]
      rw [this, zero_mul]
    · have : evalBar C Ps z hz ex = 0 := heval0 x hx z hz (fun h => hzx h.symm)
      rw [this, mul_zero]
  set N : Ideal (quotPolysExt C Ps) := Ideal.span (Set.range g) with hNdef
  have hN_le : N ≤ nilradical (quotPolysExt C Ps) := by
    rw [hNdef, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_nilradical]
    exact hg_nilp i
  have hN_fg : N.FG := by
    rw [hNdef]
    exact ⟨Finset.image g Finset.univ, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  obtain ⟨MN, hMN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (J := (⊥ : Ideal (quotPolysExt C Ps))) hN_le hN_fg
  -- `N = m * span {ex}` and `N ^ MN = m ^ MN * span {ex}`.
  have hN_eq : N = m * Ideal.span {ex} := by
    rw [hNdef, hmdef]
    have hmspan : Ideal.map mk M = Ideal.span (Set.range (fun i => mk (gen x i))) := by
      rw [hmkdef, hMdef, vanishing_eq_span, Ideal.map_span, ← Set.range_comp]
      rfl
    rw [hmspan, Ideal.span_mul_span]
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨mk (gen x i), ⟨i, rfl⟩, ex, rfl, rfl⟩
    · rintro ⟨a, ⟨i, rfl⟩, b, hb, rfl⟩
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact ⟨i, rfl⟩
  -- `Step 1c`: `∀ μ ∈ m, μ * ex = 0`.
  have hmex : ∀ μ ∈ m, μ * ex = 0 := by
    intro μ hμ
    have hMN1 : 1 ≤ MN := by
      rcases Nat.eq_zero_or_pos MN with h | h
      · exfalso
        rw [h, pow_zero, Ideal.one_eq_top] at hMN
        have h1 : (1 : quotPolysExt C Ps) ∈ (⊥ : Ideal (quotPolysExt C Ps)) := hMN Submodule.mem_top
        rw [Ideal.mem_bot] at h1
        have : (1 : C) = 0 := by
          have := congrArg (evalBar C Ps x hx) h1
          rwa [map_one, map_zero] at this
        exact one_ne_zero this
      · exact h
    have hμN : μ ∈ m ^ MN := by
      rwa [← hm_pow MN hMN1]
    have hexpow : ex ^ MN = ex := by
      have hidem : IsIdempotentElem ex := by rw [IsIdempotentElem, ← sq, hexidem]
      have : ∀ j, 1 ≤ j → ex ^ j = ex := by
        intro j hj
        induction j, hj using Nat.le_induction with
        | base => rw [pow_one]
        | succ n hn ih => rw [pow_succ, ih, ← sq, hexidem]
      exact this MN hMN1
    have hexspan : ex ∈ Ideal.span {ex} := Ideal.subset_span (Set.mem_singleton _)
    have hspan_pow : (Ideal.span {ex} : Ideal (quotPolysExt C Ps)) ^ MN = Ideal.span {ex} := by
      rw [Ideal.span_singleton_pow, hexpow]
    have hNpow : N ^ MN = m ^ MN * Ideal.span {ex} := by
      rw [hN_eq]
      rw [mul_pow m (Ideal.span {ex}) MN]
      rw [hspan_pow]
    have hmem : μ * ex ∈ N ^ MN := by
      rw [hNpow]
      exact Ideal.mul_mem_mul hμN hexspan
    have : μ * ex ∈ (⊥ : Ideal (quotPolysExt C Ps)) := hMN hmem
    rwa [Ideal.mem_bot] at this
  -- `ex ∈ S_x`.
  have hex_mem : ex ∈ evalAtPointSubmonoid C Ps x hx :=
    (mem_evalAtPointSubmonoid C Ps x hx ex).mpr (by rw [hex_eval1]; exact one_ne_zero)
  -- Work with the concrete localization.
  have : IsLocalization (evalAtPointSubmonoid C Ps x hx)
      (Localization (evalAtPointSubmonoid C Ps x hx)) := Localization.isLocalization
  -- Step 2: every element of `m` maps to `0` in `Ā_x`.
  have hzero_loc : ∀ μ ∈ m, algebraMap (quotPolysExt C Ps)
      (Localization (evalAtPointSubmonoid C Ps x hx)) μ = 0 := by
    intro μ hμ
    rw [IsLocalization.map_eq_zero_iff (evalAtPointSubmonoid C Ps x hx)
      (Localization (evalAtPointSubmonoid C Ps x hx))]
    exact ⟨⟨ex, hex_mem⟩, by rw [mul_comm]; exact hmex μ hμ⟩
  -- The composition `C → Ā → Ā_x` is the algebra map of `Ā_x`.
  have halg_comp : ∀ c : C, algebraMap C (localizationAtPoint C Ps x hx) c
      = algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx))
          (algebraMap C (quotPolysExt C Ps) c) := fun c => rfl
  -- Key reduction: for any `q : Ā`, `q` maps to `evalBar x q · 1` in `Ā_x`.
  have hreduce : ∀ q : quotPolysExt C Ps,
      algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)) q
        = algebraMap C (localizationAtPoint C Ps x hx) (evalBar C Ps x hx q) := by
    intro q
    have hdiff : q - algebraMap C (quotPolysExt C Ps) (evalBar C Ps x hx q) ∈ m := by
      rw [← hker, RingHom.mem_ker, map_sub, evalBar_algebraMap, sub_self]
    have := hzero_loc _ hdiff
    rw [map_sub, sub_eq_zero] at this
    rw [this, halg_comp]
  -- Step 3: `algebraMap C Ā_x` is bijective.
  have hbij : Function.Bijective (algebraMap C (localizationAtPoint C Ps x hx)) := by
    constructor
    · -- injective: nontrivial target + field source.
      have hnt : Nontrivial (localizationAtPoint C Ps x hx) := by
        show Nontrivial (Localization (evalAtPointSubmonoid C Ps x hx))
        refine ⟨1, 0, ?_⟩
        intro h
        have h1 : algebraMap (quotPolysExt C Ps)
            (Localization (evalAtPointSubmonoid C Ps x hx)) 1 = 0 := by rw [map_one]; exact h
        rw [IsLocalization.map_eq_zero_iff (evalAtPointSubmonoid C Ps x hx)
          (Localization (evalAtPointSubmonoid C Ps x hx))] at h1
        obtain ⟨⟨s, hsmem⟩, hs0⟩ := h1
        rw [mul_one] at hs0
        rw [mem_evalAtPointSubmonoid] at hsmem
        apply hsmem
        rw [show s = 0 from hs0, map_zero]
      exact (algebraMap C (localizationAtPoint C Ps x hx)).injective
    · -- surjective.
      intro z
      obtain ⟨⟨p, s⟩, hps⟩ := IsLocalization.surj (S := Localization (evalAtPointSubmonoid C Ps x hx))
        (evalAtPointSubmonoid C Ps x hx) z
      -- `s ∈ S_x`, so `evalBar x s ≠ 0`, hence a unit in `C`.
      have hs_ne : evalBar C Ps x hx (s : quotPolysExt C Ps) ≠ 0 :=
        (mem_evalAtPointSubmonoid C Ps x hx _).mp s.2
      -- `z * algMap s = algMap p` becomes, via `hreduce`, an equation over `C`.
      have hps' : z * algebraMap C (localizationAtPoint C Ps x hx)
          (evalBar C Ps x hx (s : quotPolysExt C Ps))
            = algebraMap C (localizationAtPoint C Ps x hx) (evalBar C Ps x hx p) := by
        rw [← hreduce, ← hreduce]; exact hps
      have hunit : IsUnit (algebraMap C (localizationAtPoint C Ps x hx)
          (evalBar C Ps x hx (s : quotPolysExt C Ps))) :=
        IsUnit.map _ ((isUnit_iff_ne_zero).mpr hs_ne)
      refine ⟨evalBar C Ps x hx p * (evalBar C Ps x hx (s : quotPolysExt C Ps))⁻¹, ?_⟩
      apply hunit.mul_right_cancel
      rw [← map_mul, mul_assoc, inv_mul_cancel₀ hs_ne, mul_one]
      exact hps'.symm
  show multiplicityOfZero C Ps x hx = 1
  rw [multiplicityOfZero]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr hbij

/-- **BPR Proposition 4.95, implication (b) ⟹ (a).** If `x` is a simple zero of the
zero-dimensional system `𝒫 = {P₁, …, P_k}`, then `x` is a non-singular zero of the extended
system `map(P₁), …, map(P_k)` over `C` (the Jacobian determinant at `x` is nonzero). -/
theorem simple_imp_nonsingular [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]
    (P : Fin k → MvPolynomial (Fin k) K) (hzd : IsZeroDimensional C (Finset.univ.image P))
    (x : Fin k → C) (hx : x ∈ zerOfFinset C (Finset.univ.image P))
    (hb : IsSimpleZero C (Finset.univ.image P) x hx) :
    IsNonsingularZero (fun i => MvPolynomial.map (algebraMap K C) (P i)) x := by
  classical
  set Ps := Finset.univ.image P with hPs
  set Pt : Fin k → MvPolynomial (Fin k) C :=
    fun i => MvPolynomial.map (algebraMap K C) (P i) with hPtdef
  set mk := Ideal.Quotient.mk (idealOfPolysExt C Ps) with hmkdef
  -- ============ Part 1: `x` is a common zero of the extended system ============
  have hPmem : ∀ j, P j ∈ Ps := fun j => Finset.mem_image_of_mem P (Finset.mem_univ j)
  have hzero : ∀ j, MvPolynomial.aeval x (Pt j) = 0 := by
    intro j
    rw [hPtdef]
    simp only
    rw [MvPolynomial.aeval_map_algebraMap]
    exact hx (P j) (hPmem j)
  -- ============ Part 2 setup: the idempotent `ex` at `x` ============
  obtain ⟨e, _hsum, _horth, hsq, heval1, heval0⟩ := proposition_4_92 (C := C) Ps hzd.2
  set ex : quotPolysExt C Ps := e x with hexdef
  have hidem : IsIdempotentElem ex := by rw [IsIdempotentElem, ← sq, hsq x (hzd.2.mem_toFinset.mpr hx)]
  have hexval : evalBar C Ps x hx ex = 1 := heval1 x hx
  have heyval : ∀ (y : Fin k → C) (hy : y ∈ zerOfFinset C Ps), y ≠ x → evalBar C Ps y hy ex = 0 :=
    fun y hy hne => heval0 x hx y hy (fun h => hne h.symm)
  -- The corner `ex·Ā` is isomorphic (as a ring) to `C`, hence reduced.
  obtain ⟨isoCorner⟩ := proposition_4_93 Ps x hx ex hidem hexval heyval
  obtain ⟨isoC⟩ := isSimpleZero_algEquiv C Ps x hx hb
  have isoCornerC : hidem.Corner ≃+* C := isoCorner.trans isoC.toRingEquiv
  have : IsReduced hidem.Corner :=
    isReduced_of_injective isoCornerC.toRingHom isoCornerC.injective
  -- ============ Step (i): `ex * mk (gen x i) = 0` in `Ā`, for each `i` ============
  have hgen_zero : ∀ i, ex * mk (gen x i) = 0 := by
    intro i
    set w : quotPolysExt C Ps := ex * mk (gen x i) with hwdef
    -- `w` vanishes at every zero, hence nilpotent.
    have hwnil : IsNilpotent w := by
      refine nilpotent_of_eval_zero Ps w ?_
      intro z hz
      rw [hwdef, map_mul]
      by_cases hzx : z = x
      · subst hzx
        have : evalBar C Ps z hz (mk (gen z i)) = 0 := by
          rw [hmkdef, evalBar_mk]
          show MvPolynomial.aeval z (gen z i) = 0
          simp [gen, map_sub]
        rw [this, mul_zero]
      · rw [heyval z hz hzx, zero_mul]
    -- `w` is in the corner.
    have hwmem : w ∈ Subsemigroup.corner ex := by
      rw [Subsemigroup.mem_corner_iff hidem]
      refine ⟨?_, ?_⟩
      · show ex * (ex * mk (gen x i)) = ex * mk (gen x i)
        rw [← mul_assoc, hidem.eq]
      · show (ex * mk (gen x i)) * ex = ex * mk (gen x i)
        rw [mul_comm ex (mk (gen x i)), mul_assoc, hidem.eq]
    -- the corner element `cw`.
    set cw : hidem.Corner := ⟨w, hwmem⟩ with hcwdef
    have coe_mul : ∀ a b : hidem.Corner, (a * b).1 = a.1 * b.1 := fun _ _ => rfl
    have coe_zero : (0 : hidem.Corner).1 = (0 : quotPolysExt C Ps) := rfl
    have coe_pow : ∀ (a : hidem.Corner) (n : ℕ), 1 ≤ n → (a ^ n).1 = a.1 ^ n := by
      intro a n hn
      induction n, hn using Nat.le_induction with
      | base => rw [pow_one, pow_one]
      | succ m hm ih => rw [pow_succ, pow_succ, coe_mul, ih]
    -- `cw` is nilpotent in the corner.
    have hcwnil : IsNilpotent cw := by
      obtain ⟨N, hN⟩ := hwnil
      refine ⟨N + 1, ?_⟩
      apply Subtype.ext
      rw [coe_pow cw (N + 1) (Nat.le_add_left 1 N), coe_zero]
      show w ^ (N + 1) = 0
      rw [pow_succ, hN, zero_mul]
    -- reduced ⇒ `cw = 0` ⇒ `w = 0`.
    have hcw0 : cw = 0 := hcwnil.eq_zero
    have : cw.1 = (0 : hidem.Corner).1 := by rw [hcw0]
    rwa [hcwdef, coe_zero] at this
  -- ============ Step (ii): extract cofactors ============
  -- `idealOfPolysExt C Ps = Ideal.span (Set.range Pt)`.
  have hideal_span : idealOfPolysExt C Ps = Ideal.span (Set.range Pt) := by
    rw [idealOfPolysExt, idealOfPolys, Finset.coe_image, hPs, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, ← Set.range_comp]
    rfl
  -- For each `i`, pick a lift `Ex` of `ex` and cofactors `A i`.
  obtain ⟨Ex, hEx⟩ := Ideal.Quotient.mk_surjective ex
  have hmemspan : ∀ i, Ex * (gen x i) ∈ Ideal.span (Set.range Pt) := by
    intro i
    rw [← hideal_span, ← Ideal.Quotient.eq_zero_iff_mem]
    show mk (Ex * gen x i) = 0
    rw [map_mul, hEx]
    exact hgen_zero i
  have hcofactor : ∀ i, ∃ A : Fin k → MvPolynomial (Fin k) C,
      ∑ j, A j * Pt j = Ex * (gen x i) := by
    intro i
    obtain ⟨A, hA⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (hmemspan i)
    refine ⟨A, ?_⟩
    rw [← hA]
    exact Finset.sum_congr rfl fun j _ => (smul_eq_mul _ _)
  choose A hA using hcofactor
  -- ============ Step (iii): differentiate and evaluate ============
  -- `aeval x Ex = 1`.
  have haevalEx : MvPolynomial.aeval x Ex = 1 := by
    have : evalBar C Ps x hx (mk Ex) = 1 := by rw [hEx]; exact hexval
    rwa [hmkdef, evalBar_mk] at this
  -- The Jacobian matrix `J j ℓ = aeval x (pderiv ℓ (Pt j))`.
  set J := jacobian Pt x with hJdef
  have hJval : ∀ j ℓ, J j ℓ = MvPolynomial.aeval x (MvPolynomial.pderiv ℓ (Pt j)) := fun _ _ => rfl
  -- The key relation `∑ j, aeval x (A i j) * J j ℓ = (if ℓ = i then 1 else 0)`.
  have hBJ : ∀ i ℓ, ∑ j, MvPolynomial.aeval x (A i j) * J j ℓ
      = (if ℓ = i then (1 : C) else 0) := by
    intro i ℓ
    -- apply `aeval x ∘ pderiv ℓ` to `∑ j, A i j * Pt j = Ex * gen x i`.
    have hd : MvPolynomial.aeval x (MvPolynomial.pderiv ℓ (∑ j, A i j * Pt j))
        = MvPolynomial.aeval x (MvPolynomial.pderiv ℓ (Ex * gen x i)) :=
      congrArg (fun p => MvPolynomial.aeval x (MvPolynomial.pderiv ℓ p)) (hA i)
    -- LHS
    have hLHS : MvPolynomial.aeval x (MvPolynomial.pderiv ℓ (∑ j, A i j * Pt j))
        = ∑ j, MvPolynomial.aeval x (A i j) * J j ℓ := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hzero j, mul_zero, zero_add, hJval]
    -- RHS
    have hRHS : MvPolynomial.aeval x (MvPolynomial.pderiv ℓ (Ex * gen x i))
        = (if ℓ = i then (1 : C) else 0) := by
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
      have hgenval : MvPolynomial.aeval x (gen x i) = 0 := by simp [gen, map_sub]
      rw [hgenval, mul_zero, zero_add, haevalEx, one_mul]
      -- `aeval x (pderiv ℓ (gen x i)) = if ℓ = i then 1 else 0`
      rw [gen, map_sub, MvPolynomial.pderiv_C, sub_zero]
      by_cases hℓi : ℓ = i
      · subst hℓi
        rw [MvPolynomial.pderiv_X_self, map_one, ite_eq_left rfl]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hℓi), map_zero, ite_eq_right hℓi]
    rw [hLHS, hRHS] at hd
    exact hd
  -- ============ Step (iv): `det J ≠ 0` ============
  set B : Matrix (Fin k) (Fin k) C := Matrix.of fun i j => MvPolynomial.aeval x (A i j) with hBdef
  have hBJ_one : B * J = 1 := by
    apply Matrix.ext
    intro i ℓ
    rw [Matrix.mul_apply]
    rw [show (∑ j, B i j * J j ℓ) = ∑ j, MvPolynomial.aeval x (A i j) * J j ℓ from rfl]
    rw [hBJ i ℓ, Matrix.one_apply]
    by_cases h : i = ℓ
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (fun he => h he.symm)]
  have hdetprod : B.det * J.det = 1 := by
    rw [← Matrix.det_mul, hBJ_one, Matrix.det_one]
  have hdet : J.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdetprod
    exact one_ne_zero hdetprod.symm
  -- ============ Conclusion ============
  exact ⟨hzero, hdet⟩

/-- **BPR Proposition 4.95.** For a zero-dimensional system `𝒫 = {P₁, …, P_k}` and a zero `x`,
the following are equivalent: (a) `x` is a non-singular zero of `𝒫`; (b) `x` is simple (multiplicity
`1`, `Ā_x = C`); (c) `M_x ⊆ Ideal(𝒫, C) + M_x²` (with `M_x` the ideal of `C[X₁, …, X_k]` vanishing
at `x`). -/
theorem proposition_4_95 [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]
    (P : Fin k → MvPolynomial (Fin k) K)
    (hzd : IsZeroDimensional C (Finset.univ.image P))
    (x : Fin k → C) (hx : x ∈ zerOfFinset C (Finset.univ.image P)) :
    List.TFAE
      [ IsNonsingularZero (fun i => MvPolynomial.map (algebraMap K C) (P i)) x,
        IsSimpleZero C (Finset.univ.image P) x hx,
        MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C))
          ≤ idealOfPolysExt C (Finset.univ.image P)
            + (MvPolynomial.vanishingIdeal C ({x} : Set (Fin k → C))) ^ 2 ] := by
  tfae_have 1 → 3 := fun ha => nonsingular_imp_cotangent P x ha
  tfae_have 3 → 2 := fun hc => cotangent_imp_simple P hzd x hx hc
  tfae_have 2 → 1 := fun hb => simple_imp_nonsingular P hzd x hx hb
  tfae_finish

end Azurite.BPR.Chapter4
