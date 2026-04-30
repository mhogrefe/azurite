import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.Lagrange
import Azurite.BasuPollackRoy.Chapter2.Section2_1

/-!
# BPR Theorem 2.11 a) ⇒ b): Real Closed ⟹ R[i] Algebraically Closed

**Theorem 2.11 (BPR).** If R is a real closed field, then
R[i] := R[X]/(X² + 1) is an algebraically closed field.
-/

namespace Azurite.BPR.Theorem2_11

open Polynomial Azurite.BPR

/-! ### R[i] — definitions from Notation 2.18 (Section2_1.lean)

`Ri`, `Ri.i`, `Ri.conj`, `Ri.conj_i`, `Ri.conj_conj`, `Ri.conj_injective`,
`Ri.i_sq`, `irred_X_sq_add_one`, and the `Fact Irreducible` instance are
brought into scope by `open Azurite.BPR` above.
-/

/-- Apply conjugation to the coefficients of a polynomial over R[i]. -/
noncomputable def conjPoly (R : Type*) [CommRing R] : (Ri R)[X] → (Ri R)[X] :=
  Polynomial.map (Ri.conj R)

/-! ### Combinatorial indexing -/

/-- The set of ordered pairs (i, j) with i < j from Fin p. -/
def strictPairs (p : ℕ) : Finset (Fin p × Fin p) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

private lemma card_strictPairs (p : ℕ) : (strictPairs p).card = p * (p - 1) / 2 := by
  have hmul : p * (p - 1) = p * p - p := Nat.mul_sub_one p p
  have hAB : (Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 < ij.2)).card =
      (Finset.univ.filter (fun ij : Fin p × Fin p => ij.2 < ij.1)).card :=
    Finset.card_bij (fun ij _ => Prod.swap ij)
      (fun ⟨a, b⟩ h => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; exact h)
      (fun ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h => by
        simp only [Prod.swap, Prod.mk.injEq] at h; exact Prod.ext h.2 h.1)
      (fun ⟨a, b⟩ h => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact ⟨⟨b, a⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h, rfl⟩)
  have hAnotA : (Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 < ij.2)).card +
      (Finset.univ.filter (fun ij : Fin p × Fin p => ¬ij.1 < ij.2)).card = p * p := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin p × Fin p))) (fun ij : Fin p × Fin p => ij.1 < ij.2)
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
    exact h
  have hB' : (Finset.univ.filter (fun ij : Fin p × Fin p => ¬ij.1 < ij.2)).filter
      (fun ij : Fin p × Fin p => ij.2 < ij.1) =
      Finset.univ.filter (fun ij : Fin p × Fin p => ij.2 < ij.1) := by
    ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]; omega
  have hD' : (Finset.univ.filter (fun ij : Fin p × Fin p => ¬ij.1 < ij.2)).filter
      (fun ij : Fin p × Fin p => ¬ij.2 < ij.1) =
      Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 = ij.2) := by
    ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact ⟨fun ⟨h1, h2⟩ => le_antisymm h2 h1, fun h => ⟨h ▸ le_refl _, h ▸ le_refl _⟩⟩
  have hBD : (Finset.univ.filter (fun ij : Fin p × Fin p => ij.2 < ij.1)).card +
      (Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 = ij.2)).card =
      (Finset.univ.filter (fun ij : Fin p × Fin p => ¬ij.1 < ij.2)).card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun ij : Fin p × Fin p => ¬ij.1 < ij.2))
      (fun ij : Fin p × Fin p => ij.2 < ij.1)
    rw [hB', hD'] at h; exact h
  have hDp : (Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 = ij.2)).card = p := by
    have h : (Finset.univ : Finset (Fin p)).card =
        (Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 = ij.2)).card :=
      Finset.card_bij (fun (i : Fin p) _ => ((i, i) : Fin p × Fin p))
        (fun i _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
        (fun a _ b _ h => congr_arg Prod.fst h)
        (fun ⟨a, b⟩ h => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
          exact ⟨a, Finset.mem_univ _, Prod.ext rfl h⟩)
    simp only [Finset.card_univ, Fintype.card_fin] at h; omega
  show (Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 < ij.2)).card = p * (p - 1) / 2
  omega

/-! ### The polynomials Q, D, F, G, H -/

variable {L : Type*} [Field L] {p : ℕ}

/-- γ_{ij}(Z) = x_i + x_j + Z · x_i · x_j ∈ L[Z].
    Here Z is the polynomial indeterminate. -/
noncomputable def gammaPoly (x : Fin p → L) (i j : Fin p) : L[X] :=
  Polynomial.C (x i + x j) + Polynomial.X * Polynomial.C (x i * x j)

/-- Q(Z, Y) = ∏_{i < j} (Y − γ_{ij}(Z)) ∈ L[Z][Y].
    The outer polynomial ring is in Y; coefficients are polynomials in Z. -/
noncomputable def QPolynomial (x : Fin p → L) : (L[X])[X] :=
  ∏ ij ∈ strictPairs p,
    (Polynomial.X - Polynomial.C (gammaPoly x ij.1 ij.2))

/-- D(Z) = ∏_{a ≠ b in strictPairs} (γ_a(Z) − γ_b(Z)) ∈ L[Z].
    This is (up to sign) the square of the standard discriminant of Q w.r.t. Y.
    D(z) ≠ 0 iff all γ_{ij}(z) are distinct. -/
noncomputable def discPoly (x : Fin p → L) : L[X] :=
  ∏ ab ∈ (strictPairs p).offDiag,
    (gammaPoly x ab.1.1 ab.1.2 - gammaPoly x ab.2.1 ab.2.2)

/-- F(Z, Y) = ∂Q/∂Y, the formal derivative of Q with respect to Y. -/
noncomputable def FPoly (x : Fin p → L) : (L[X])[X] :=
  Polynomial.derivative (QPolynomial x)

/-- G(Z, Y) = ∑_{i<j} (x_i + x_j) · ∏_{(k,l)≠(i,j)} (Y − γ_{kl}(Z)).
    Evaluating at a root γ_{ij} of Q extracts x_i + x_j. -/
noncomputable def GPoly (x : Fin p → L) : (L[X])[X] :=
  ∑ ij ∈ strictPairs p,
    Polynomial.C (Polynomial.C (x ij.1 + x ij.2)) *
    ∏ kl ∈ (strictPairs p).erase ij,
      (Polynomial.X - Polynomial.C (gammaPoly x kl.1 kl.2))

/-- H(Z, Y) = ∑_{i<j} (x_i · x_j) · ∏_{(k,l)≠(i,j)} (Y − γ_{kl}(Z)).
    Evaluating at a root γ_{ij} of Q extracts x_i · x_j. -/
noncomputable def HPoly (x : Fin p → L) : (L[X])[X] :=
  ∑ ij ∈ strictPairs p,
    Polynomial.C (Polynomial.C (x ij.1 * x ij.2)) *
    ∏ kl ∈ (strictPairs p).erase ij,
      (Polynomial.X - Polynomial.C (gammaPoly x kl.1 kl.2))

/-! ### Infrastructure lemmas -/

variable {R : Type*} [Field R]

/-- For any a ∈ R, there exists v ∈ R[i] with v² = a. -/
theorem sqrt_of_R_in_Ri [IsRealClosed R] (a : R) :
    ∃ v : Ri R, v ^ 2 = algebraMap R (Ri R) a := by
  rcases IsRealClosed.isSquare_or_isSquare_neg a with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact ⟨algebraMap R (Ri R) c, by
      rw [sq]; simp only [← map_mul, hc]⟩
  · refine ⟨algebraMap R (Ri R) c * Ri.i R, ?_⟩
    rw [mul_pow, Ri.i_sq]
    simp only [sq, ← map_mul, mul_neg, mul_one, ← map_neg]
    have : -(c * c) = a := by rw [← hc, neg_neg]
    simp only [this]

/-! ### Degree arithmetic -/

/-- If p = 2^m · n with m ≥ 1 and n odd, then p(p−1)/2 = 2^{m−1} · n' with n' odd. -/
theorem half_degree_odd_factor {m n : ℕ} (hm : 1 ≤ m) (hn : Odd n) (hp : 0 < n) :
    ∃ n' : ℕ, Odd n' ∧ 2 ^ m * n * (2 ^ m * n - 1) / 2 = 2 ^ (m - 1) * n' := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  subst hk
  simp only [Nat.succ_sub_one]
  refine ⟨n * (2 ^ (k + 1) * n - 1), ?_, ?_⟩
  · apply Odd.mul hn
    refine Nat.Even.sub_odd ?_ ?_ odd_one
    · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · exact Even.mul_right ⟨2 ^ k, by ring⟩ n
  · rw [show 2 ^ (k + 1) = 2 * 2 ^ k from by ring]
    rw [show 2 * 2 ^ k * n * (2 * 2 ^ k * n - 1) =
        2 * (2 ^ k * n * (2 * 2 ^ k * n - 1)) from by ring]
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    ring

/-! ### Conjugation properties -/

variable {R : Type*} [Field R]
/-- If conj(c) = c in R[i], then c ∈ range(algebraMap R (Ri R)).
    Proof: every c = mk(C a + C b * X). conj(c) = mk(C a - C b * X).
    conj(c) = c ⟹ mk(2 * C b * X) = 0, so (X²+1) ∣ 2bX.
    Since deg(X²+1) > deg(2bX), we get b = 0, i.e. c = algebraMap a. -/
theorem Ri.conj_fixed_mem_range [IsRealClosed R] (c : Ri R) (hc : (Ri.conj R) c = c) :
    c ∈ Set.range (algebraMap R (Ri R)) := by
  induction c using AdjoinRoot.induction_on with
  | ih p =>
    -- conj(mk p) = lift(of, -root, _)(mk p) = eval₂ (of) (-root) p (by lift_mk)
    -- mk p = eval₂ (of) (root) p (by aeval_eq, since mk = aeval root)
    -- From hc: eval₂ (of) (-root) p = eval₂ (of) root p = mk p
    -- Rewrite mk using aeval:
    rw [show AdjoinRoot.mk _ p = Polynomial.aeval (Ri.i R) p from
      (AdjoinRoot.aeval_eq p).symm]
    -- conj(aeval i p) = aeval (conj i) p = aeval (-i) p (AlgHom comp aeval)
    rw [show AdjoinRoot.mk _ p = Polynomial.aeval (Ri.i R) p from
      (AdjoinRoot.aeval_eq p).symm] at hc
    have hconj_aeval : (Ri.conj R) (Polynomial.aeval (Ri.i R) p) =
        Polynomial.aeval (-Ri.i R) p := by
      rw [← Polynomial.aeval_algHom_apply]
      exact congr_arg (fun x => Polynomial.aeval x p) (Ri.conj_i R)
    rw [hconj_aeval] at hc
    -- Now hc: aeval (-i) p = aeval i p
    -- Goal: aeval i p ∈ range(algebraMap)
    -- Use modByMonic to reduce p to degree < 2
    set f := (X : R[X]) ^ 2 + 1
    have hfm : f.Monic := monic_X_pow_add_C 1 (by norm_num : (2 : ℕ) ≠ 0)
    set r := p %ₘ f
    -- mk p = mk r, so aeval i p = aeval i r
    have haeval_eq : Polynomial.aeval (Ri.i R) p = Polynomial.aeval (Ri.i R) r := by
      have : AdjoinRoot.mk ((X : R[X])^2+1) p = AdjoinRoot.mk ((X : R[X])^2+1) r := by
        rw [AdjoinRoot.mk_eq_mk]
        exact ⟨p /ₘ f, by
          have := modByMonic_eq_sub_mul_div p f
          linear_combination -this⟩
      rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq] at this
      exact this
    rw [haeval_eq]
    -- r has natDegree ≤ 1
    have hr_deg : r.natDegree ≤ 1 := by
      have hrd : r.degree < f.degree := degree_modByMonic_lt p hfm
      have hf_deg : f.degree = 2 := by
        have hnat : f.natDegree = 2 := by
          simp [f]; rw [show (1 : R[X]) = C 1 from rfl]; exact natDegree_X_pow_add_C
        rw [Polynomial.degree_eq_natDegree (Irreducible.ne_zero (Fact.out : Irreducible f)), hnat]
        norm_num
      rw [hf_deg] at hrd
      -- hrd: r.degree < 2. Goal: r.natDegree ≤ 1.
      -- r.degree < ↑2 means r.natDegree < 2 (when r.degree ≠ ⊥)
      -- If r = 0 then natDegree = 0 ≤ 1. Otherwise degree = ↑natDegree < ↑2.
      by_cases hr : r = 0
      · simp [hr]
      · rw [Polynomial.degree_eq_natDegree hr] at hrd
        exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp (by exact_mod_cast hrd))
    -- Also need: aeval (-i) r = aeval i r (transferred from p)
    have haeval_neg_eq : Polynomial.aeval (-Ri.i R) r = Polynomial.aeval (Ri.i R) r := by
      -- aeval(-i) p = aeval(-i) r because p - r = f * q and aeval(-i) f = 0
      have haeval_neg_f : Polynomial.aeval (-Ri.i R) f = 0 := by
        simp [f, Polynomial.aeval_def, eval₂_add, eval₂_pow, eval₂_one, eval₂_X]
        linear_combination Ri.i_sq R
      have haeval_neg_eq_pr : Polynomial.aeval (-Ri.i R) p = Polynomial.aeval (-Ri.i R) r := by
        have hpr : p - r = f * (p /ₘ f) := by
          have := modByMonic_eq_sub_mul_div p f
          linear_combination -this
        have := congr_arg (Polynomial.aeval (-Ri.i R)) hpr
        simp [map_sub, map_mul, haeval_neg_f, zero_mul] at this
        linear_combination this
      rw [← haeval_neg_eq_pr, hc]
      exact haeval_eq
    -- For r of natDegree ≤ 1: r = C(r.coeff 0) + C(r.coeff 1) * X
    -- aeval x r = algebraMap(coeff 0) + algebraMap(coeff 1) * x for x = ±i
    -- From equality: 2 * algebraMap(coeff 1) * i = 0
    -- i ≠ 0, 2 ≠ 0, domain → coeff 1 = 0
    -- Hence aeval i r = algebraMap(coeff 0)
    -- aeval(-i) r = coeff_0 - coeff_1 * i, aeval(i) r = coeff_0 + coeff_1 * i
    -- Equal ⟹ 2 * coeff_1 * i = 0
    have hi_ne : Ri.i R ≠ 0 := by
      intro h
      have := Ri.i_sq R
      rw [h, zero_pow (by norm_num : 2 ≠ 0)] at this
      exact one_ne_zero (neg_eq_zero.mp this.symm)
    -- The coeff 1 vanishes because domain + i≠0 + 2≠0
    -- For now we construct the witness directly
    -- Decompose r = C(coeff 1) * X + C(coeff 0) (natDegree ≤ 1)
    have hr_decomp := Polynomial.eq_X_add_C_of_natDegree_le_one hr_deg
    -- Compute aeval i r and aeval (-i) r
    set a := r.coeff 0
    set b := r.coeff 1
    -- aeval x r = algebraMap b * x + algebraMap a
    have haeval_r : ∀ x : Ri R,
        Polynomial.aeval x r = algebraMap R (Ri R) b * x + algebraMap R (Ri R) a := by
      intro x
      conv_lhs => rw [hr_decomp]
      simp [Polynomial.aeval_def, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    -- From haeval_neg_eq: b * (-i) + a = b * i + a, i.e., 2 * b * i = 0
    have h2bi : algebraMap R (Ri R) b * Ri.i R = 0 := by
      have h1 := haeval_r (Ri.i R)
      have h2 := haeval_r (-Ri.i R)
      rw [h1, h2] at haeval_neg_eq
      -- haeval_neg_eq: b * (-i) + a = b * i + a
      -- So b * (-i) = b * i, hence b * i + b * i = 0, i.e. 2 * b * i = 0
      have hsub : algebraMap R (Ri R) b * (-Ri.i R) - algebraMap R (Ri R) b * Ri.i R = 0 := by
        linear_combination haeval_neg_eq
      rw [mul_neg, ← neg_add', ← two_mul, neg_eq_zero, mul_eq_zero, mul_eq_zero] at hsub
      rcases hsub with h | h | h
      · -- 2 = 0 in Ri R: impossible since IsRealClosed → CharZero
        exfalso
        have : (2 : Ri R) ≠ 0 := by
          intro h2
          apply (two_ne_zero : (2 : R) ≠ 0)
          exact (algebraMap R (Ri R)).injective
            (show (algebraMap R (Ri R)) 2 = (algebraMap R (Ri R)) 0 by
              rw [map_zero]; exact_mod_cast h2)
        exact this h
      · exact mul_eq_zero_of_left h _
      · exact absurd h hi_ne
    -- b * i = 0, i ≠ 0, so algebraMap b = 0 (domain), hence b = 0
    have hb_zero : algebraMap R (Ri R) b = 0 := by
      exact (mul_eq_zero.mp h2bi).resolve_right hi_ne
    -- aeval i r = algebraMap a
    rw [haeval_r (Ri.i R), hb_zero, zero_mul, zero_add]
    exact ⟨a, rfl⟩


/-- Conjugation fixes elements of R: conj (algebraMap R (Ri R) r) = algebraMap R (Ri R) r. -/
theorem Ri.conj_algebraMap [IsRealClosed R] (r : R) :
    (Ri.conj R) (algebraMap R (Ri R) r) = algebraMap R (Ri R) r :=
  (Ri.conj R).commutes r

/-- Polynomial evaluation commutes with conjugation:
    If P ∈ Ri[X] and z ∈ Ri, then conj(P(z)) = P̄(conj(z)). -/
theorem conj_eval_eq_eval_conj_map [IsRealClosed R]
    (P : (Ri R)[X]) (z : Ri R) :
    (Ri.conj R) (P.eval z) = (conjPoly R P).eval ((Ri.conj R) z) := by
  simp only [conjPoly, Polynomial.eval_map]
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, map_add, eval₂_add]
    rw [hp, hq]
  | monomial n a =>
    simp only [eval_monomial, map_mul, map_pow, eval₂_monomial, RingHom.coe_coe]

/-- If P ∈ R[i][X] has coefficients in R, then conjPoly(P) = P.
    (Since conj fixes R.) -/
theorem conjPoly_eq_self_of_mem_R [IsRealClosed R] (P : R[X]) :
    conjPoly R (P.map (algebraMap R (Ri R))) = P.map (algebraMap R (Ri R)) := by
  simp only [conjPoly, Polynomial.map_map]
  congr 1
  ext r
  exact Ri.conj_algebraMap r

/-- conjPoly is an involution: applying conjugation to coefficients twice gives back the original. -/
theorem conjPoly_conjPoly [IsRealClosed R] (P : (Ri R)[X]) :
    conjPoly R (conjPoly R P) = P := by
  simp only [conjPoly, Polynomial.map_map]
  have h : ((Ri.conj R : Ri R →+* Ri R).comp (Ri.conj R)) = RingHom.id (Ri R) :=
    RingHom.ext (fun z => Ri.conj_conj R z)
  rw [h, Polynomial.map_id]

/-- P · conjPoly(P) is fixed by conjPoly. -/
theorem conjPoly_mul_conjPoly_eq [IsRealClosed R] (P : (Ri R)[X]) :
    conjPoly R (P * conjPoly R P) = conjPoly R P * P := by
  simp only [conjPoly, Polynomial.map_mul, Polynomial.map_map]
  congr 1
  have h : ((Ri.conj R : Ri R →+* Ri R).comp (Ri.conj R)) = RingHom.id (Ri R) :=
    RingHom.ext (fun z => Ri.conj_conj R z)
  rw [h, Polynomial.map_id]

/-- Each coefficient of P · conjPoly(P) is fixed by conj. -/
theorem conj_coeff_mul_conjPoly [IsRealClosed R] (P : (Ri R)[X]) (n : ℕ) :
    (Ri.conj R) ((P * conjPoly R P).coeff n) = (P * conjPoly R P).coeff n := by
  have key : conjPoly R (P * conjPoly R P) = P * conjPoly R P := by
    rw [conjPoly_mul_conjPoly_eq, mul_comm]
  have := congr_arg (fun q => q.coeff n) key
  simp only [conjPoly, Polynomial.coeff_map] at this
  exact this

/-! ### Nonzero polynomial evaluation -/

/-- A nonzero polynomial over an infinite integral domain has a non-root.
    This is used to find z with D(z) ≠ 0. -/
theorem exists_eval_ne_zero {K : Type*} [CommRing K] [IsDomain K] [Infinite K]
    (P : K[X]) (hP : P ≠ 0) : ∃ x : K, P.eval x ≠ 0 := by
  by_contra h
  push Not at h
  exact hP (Polynomial.zero_of_eval_zero P h)

/-! ### Symmetric polynomial membership (Q, G, H ∈ R[Z][Y])

These use `proposition_2_16` from Section2_1: if P ∈ R[X] splits as ∏(X − xᵢ)
over C, then any symmetric polynomial in the xᵢ with coefficients in R
evaluates to an element of R.

The γ_{ij}(Z) = xᵢ + xⱼ + Z·xᵢxⱼ are symmetric in the roots; products and
sums of symmetric expressions remain symmetric. Therefore the coefficients of
Q, G, H (as polynomials in Y) lie in R[Z]. -/

variable {R : Type*} [Field R] {L : Type*} [Field L] [Algebra R L]

/-- A polynomial f ∈ L[X] lies in the image of R[X] → L[X] if and only if
    all its coefficients are in the image of algebraMap R L. -/
theorem poly_in_image_iff_coeffs_in_range
    (f : L[X]) :
    (∃ g : R[X], g.map (algebraMap R L) = f) ↔
    ∀ n : ℕ, f.coeff n ∈ Set.range (algebraMap R L) := by
  constructor
  · rintro ⟨g, rfl⟩ n
    exact ⟨g.coeff n, (Polynomial.coeff_map _ n).symm⟩
  · intro h
    choose c hc using h
    refine ⟨⟨⟨f.support, c, fun n => ?_⟩⟩, ?_⟩
    · simp only [Polynomial.mem_support_iff]
      constructor
      · intro hn
        rwa [← hc n, ← map_zero (algebraMap R L),
          (algebraMap R L).injective.ne_iff] at hn
      · intro hn
        rwa [← hc n, map_ne_zero_iff _ (algebraMap R L).injective]
    · ext n; simp [Polynomial.coeff_map, hc n]

/-- If a polynomial f ∈ L[X] evaluates into the range of `algebraMap R L` at every
    R-point, then each coefficient of f lies in the range.
    Requires R to be an infinite integral domain. -/
theorem eval_range_implies_coeff_range [Infinite R] [IsDomain R]
    (f : L[X])
    (hf : ∀ r : R, f.eval (algebraMap R L r) ∈ Set.range (algebraMap R L))
    (n : ℕ) : f.coeff n ∈ Set.range (algebraMap R L) := by
  classical
  -- Choose preimages: for each r, φ(r) ∈ R with algebraMap(φ(r)) = f.eval(algebraMap r)
  choose φ hφ using hf
  set d := f.natDegree
  -- Pick d+1 distinct R-elements via Infinite.natEmbedding
  set v : Fin (d + 1) → R := (Infinite.natEmbedding R) ∘ Fin.val
  have hv_inj : Set.InjOn v ↑(Finset.univ : Finset (Fin (d + 1))) := by
    intro i _ j _ hij
    exact Fin.ext ((Infinite.natEmbedding R).injective hij)
  -- Build Lagrange interpolant h ∈ R[X]
  set h := (Lagrange.interpolate Finset.univ v) (φ ∘ v)
  -- h has degree < d+1
  have hdeg_h : h.degree < ↑(d + 1) := by
    have := Lagrange.degree_interpolate_lt (φ ∘ v) hv_inj
    rwa [Finset.card_univ, Fintype.card_fin] at this
  -- h.eval(vᵢ) = φ(vᵢ)
  have heval_h : ∀ i : Fin (d + 1), eval (v i) h = φ (v i) :=
    fun i => Lagrange.eval_interpolate_at_node _ hv_inj (Finset.mem_univ i)
  -- Injectivity for the image finset
  have hav_inj : Set.InjOn (algebraMap R L ∘ v) ↑(Finset.univ : Finset (Fin (d + 1))) := by
    intro i _ j _ hij
    exact hv_inj (Finset.mem_univ i) (Finset.mem_univ j) ((algebraMap R L).injective hij)
  have hcard :
      ((Finset.univ : Finset (Fin (d + 1))).image (algebraMap R L ∘ v)).card = d + 1 := by
    rw [Finset.card_image_of_injOn hav_inj, Finset.card_univ, Fintype.card_fin]
  -- Degree bounds
  have hdf : f.degree < ↑(d + 1) :=
    lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le le_rfl)
  have hdmh : (map (algebraMap R L) h).degree < ↑(d + 1) :=
    lt_of_le_of_lt degree_map_le hdeg_h
  -- Show f = h.map(algebraMap) via finite polynomial identity
  have heq : f = map (algebraMap R L) h := by
    suffices f - map (algebraMap R L) h = 0 from sub_eq_zero.mp this
    apply eq_zero_of_degree_lt_of_eval_finset_eq_zero
      ((Finset.univ : Finset (Fin (d + 1))).image (algebraMap R L ∘ v))
    · rw [hcard]
      exact lt_of_le_of_lt (degree_sub_le _ _) (sup_lt_iff.mpr ⟨hdf, hdmh⟩)
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      simp only [Function.comp_apply, eval_sub, eval_map, sub_eq_zero]
      -- eval₂ (algebraMap R L) (algebraMap R L (v i)) h = algebraMap R L (eval (v i) h)
      rw [show eval₂ (algebraMap R L) (algebraMap R L (v i)) h =
        algebraMap R L (eval (v i) h) from by
          rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rfl]
      rw [heval_h i, hφ]
  -- Conclude: f.coeff n = algebraMap(h.coeff n) ∈ range
  rw [heq]; exact ⟨h.coeff n, (coeff_map _ n).symm⟩

/-- For a product ∏(Y − C(f_i)), each Y-coefficient (an element of L[Z]) has all
    its Z-coefficients expressible as elementary symmetric polynomials of
    the f_i's Z-coefficients. When those are symmetric in roots of P ∈ R[X],
    they lie in R by Prop 2.16.

    This is the core evaluation lemma: for fixed z ∈ R, the n-th Y-coefficient
    of ∏(Y − γ_{ij}(z)) is a symmetric function of x₁,…,xₚ. -/
theorem Q_eval_coeff_in_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) (r : R) :
    Polynomial.eval (algebraMap R L r) ((QPolynomial x).coeff n)
      ∈ Set.range (algebraMap R L) := by
  -- Define the MvPolynomial version of γ with z = r baked in as a constant
  set γMv : Fin p × Fin p → MvPolynomial (Fin p) R :=
    fun ij => MvPolynomial.X ij.1 + MvPolynomial.X ij.2 +
      MvPolynomial.C r * MvPolynomial.X ij.1 * MvPolynomial.X ij.2 with γMv_def
  -- Define QMv: the product over strictPairs in (MvPolynomial R)[Y]
  set QMv : (MvPolynomial (Fin p) R)[X] :=
    ∏ ij ∈ strictPairs p,
      (Polynomial.X - Polynomial.C (γMv ij)) with QMv_def
  -- Key fact: aeval x ∘ γMv = eval (algebraMap r) ∘ gammaPoly x
  have hγ : ∀ ij ∈ strictPairs p,
      (MvPolynomial.aeval x) (γMv ij) =
        Polynomial.eval (algebraMap R L r) (gammaPoly x ij.1 ij.2) := by
    intro ij _
    simp only [γMv_def, gammaPoly, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  -- Map (aeval x) QMv = map (eval z) (QPolynomial x) as polynomials in Y over L
  have hQ : Polynomial.map (MvPolynomial.aeval x).toRingHom QMv =
      Polynomial.map (Polynomial.evalRingHom (algebraMap R L r)) (QPolynomial x) := by
    simp only [QMv_def, QPolynomial]
    rw [Polynomial.map_prod, Polynomial.map_prod]
    apply Finset.prod_congr rfl; intro ij hij
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_evalRingHom]
    rw [hγ ij hij]
  -- Coefficients agree: eval z (coeff n Q) = aeval x (coeff n QMv)
  have hcoeff : Polynomial.eval (algebraMap R L r) ((QPolynomial x).coeff n) =
      (MvPolynomial.aeval x) (QMv.coeff n) := by
    have := congr_arg (fun q => q.coeff n) hQ
    simp only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    exact this.symm
  -- coeff n QMv is a symmetric MvPolynomial
  have hsymm : (QMv.coeff n).IsSymmetric := by
    intro σ
    have hrename_coeff : MvPolynomial.rename σ (QMv.coeff n) =
        (Polynomial.map (MvPolynomial.rename σ).toRingHom QMv).coeff n :=
      (Polynomial.coeff_map _ _).symm
    rw [hrename_coeff]
    suffices hpoly : Polynomial.map (MvPolynomial.rename σ).toRingHom QMv = QMv by rw [hpoly]
    simp only [QMv_def]
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    have hγ_rename : ∀ ij : Fin p × Fin p,
        MvPolynomial.rename σ (γMv ij) = γMv (σ ij.1, σ ij.2) := by
      intro ij
      simp only [γMv_def, map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
    simp_rw [hγ_rename]
    have hγ_comm : ∀ i j : Fin p, γMv (i, j) = γMv (j, i) := by
      intro i j; simp only [γMv_def]; ring
    apply Finset.prod_nbij (fun ij => if σ ij.1 < σ ij.2 then (σ ij.1, σ ij.2) else (σ ij.2, σ ij.1))
    · -- Maps into strictPairs
      intro ij hij
      simp only [strictPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
      split_ifs with h
      · exact h
      · exact lt_of_le_of_ne (not_lt.mp h) (fun heq => hij.ne (σ.injective heq.symm))
    · -- Injective
      intro ij₁ hij₁ ij₂ hij₂ heq
      simp only [strictPairs, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hij₁ hij₂
      have heq' : (if σ ij₁.1 < σ ij₁.2 then (σ ij₁.1, σ ij₁.2) else (σ ij₁.2, σ ij₁.1)) =
                  (if σ ij₂.1 < σ ij₂.2 then (σ ij₂.1, σ ij₂.2) else (σ ij₂.2, σ ij₂.1)) := heq
      split_ifs at heq' with h₁ h₂ h₂
      all_goals (obtain ⟨ha, hb⟩ := Prod.mk.inj heq')
      · exact Prod.ext (σ.injective ha) (σ.injective hb)
      · exfalso
        exact absurd (show ij₁.2 < ij₁.1 from σ.injective ha ▸ σ.injective hb ▸ hij₂) (not_lt.mpr hij₁.le)
      · exfalso
        exact absurd (show ij₂.2 < ij₂.1 from σ.injective ha ▸ σ.injective hb ▸ hij₁) (not_lt.mpr hij₂.le)
      · exact Prod.ext (σ.injective hb) (σ.injective ha)
    · -- Surjective onto strictPairs
      intro ij hij
      simp only [strictPairs, Finset.coe_filter, Set.mem_setOf_eq, Set.mem_image,
        Finset.mem_univ, true_and] at hij ⊢
      by_cases hord : σ.symm ij.1 < σ.symm ij.2
      · refine ⟨(σ.symm ij.1, σ.symm ij.2), hord, ?_⟩
        simp only [Equiv.apply_symm_apply]
        rw [if_pos hij]
      · have hord' : σ.symm ij.2 < σ.symm ij.1 :=
          lt_of_le_of_ne (not_lt.mp hord) (fun h => hij.ne (σ.symm.injective h).symm)
        refine ⟨(σ.symm ij.2, σ.symm ij.1), hord', ?_⟩
        simp only [Equiv.apply_symm_apply]
        rw [if_neg (not_lt.mpr hij.le)]
    · -- Values agree after sorting
      intro ij hij
      split_ifs with h
      · rfl
      · simp only [sub_right_inj]; exact congr_arg Polynomial.C (hγ_comm _ _)
  -- Apply proposition_2_16 from Section2_1
  rw [hcoeff]
  exact Azurite.BPR.proposition_2_16 P x hx _ hsymm

/-- Each coefficient of Q(Z,Y) (viewed as a polynomial in Y whose coefficients
    are in L[Z]) actually belongs to R[Z], provided the xᵢ are roots of a
    polynomial P ∈ R[X]. -/
theorem Q_coeff_mem_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) :
    ∃ q : R[X], q.map (algebraMap R L) = (QPolynomial x).coeff n := by
  rw [poly_in_image_iff_coeffs_in_range]
  intro m
  -- We need each Z-coefficient of f := (QPolynomial x).coeff n to be in R.
  -- Q_eval_coeff_in_R shows f.eval(algebraMap r) ∈ range for all r.
  -- eval_range_implies_coeff_range then gives all f.coeff in range.
  haveI : Infinite R := Infinite.of_injective (Nat.cast : ℕ → R) Nat.cast_injective
  exact eval_range_implies_coeff_range _ (Q_eval_coeff_in_R P x hx n) m

/-- The n-th Y-coefficient of G(Z,Y), evaluated at z = algebraMap r, lies in R.
    Proof mirrors Q_eval_coeff_in_R: MvPolynomial lifting + symmetry + proposition_2_16. -/
theorem G_eval_coeff_in_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) (r : R) :
    Polynomial.eval (algebraMap R L r) ((GPoly x).coeff n)
      ∈ Set.range (algebraMap R L) := by
  set γMv : Fin p × Fin p → MvPolynomial (Fin p) R :=
    fun ij => MvPolynomial.X ij.1 + MvPolynomial.X ij.2 +
      MvPolynomial.C r * MvPolynomial.X ij.1 * MvPolynomial.X ij.2 with γMv_def
  set sMv : Fin p × Fin p → MvPolynomial (Fin p) R :=
    fun ij => MvPolynomial.X ij.1 + MvPolynomial.X ij.2 with sMv_def
  set GMv : (MvPolynomial (Fin p) R)[X] :=
    ∑ ij ∈ strictPairs p,
      Polynomial.C (sMv ij) *
      ∏ kl ∈ (strictPairs p).erase ij,
        (Polynomial.X - Polynomial.C (γMv kl)) with GMv_def
  have hγ : ∀ ij ∈ strictPairs p,
      (MvPolynomial.aeval x) (γMv ij) =
        Polynomial.eval (algebraMap R L r) (gammaPoly x ij.1 ij.2) := by
    intro ij _
    simp only [γMv_def, gammaPoly, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hs_aeval : ∀ ij ∈ strictPairs p,
      (MvPolynomial.aeval x) (sMv ij) = x ij.1 + x ij.2 := by
    intro ij _; simp only [sMv_def, map_add, MvPolynomial.aeval_X]
  have hG : Polynomial.map (MvPolynomial.aeval x).toRingHom GMv =
      Polynomial.map (Polynomial.evalRingHom (algebraMap R L r)) (GPoly x) := by
    simp only [GMv_def, GPoly]
    rw [Polynomial.map_sum, Polynomial.map_sum]
    apply Finset.sum_congr rfl; intro ij hij
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C]
    congr 1
    · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, hs_aeval ij hij]
    · rw [Polynomial.map_prod, Polynomial.map_prod]
      apply Finset.prod_congr rfl; intro kl hkl
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_evalRingHom]
      rw [hγ kl (Finset.mem_of_mem_erase hkl)]
  have hcoeff : Polynomial.eval (algebraMap R L r) ((GPoly x).coeff n) =
      (MvPolynomial.aeval x) (GMv.coeff n) := by
    have := congr_arg (fun q => q.coeff n) hG
    simp only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    exact this.symm
  -- Symmetry: rename σ GMv = GMv. Strategy: show the polynomial (in Y) is invariant.
  have hsymm : (GMv.coeff n).IsSymmetric := by
    intro σ
    rw [show MvPolynomial.rename σ (GMv.coeff n) =
        (Polynomial.map (MvPolynomial.rename σ).toRingHom GMv).coeff n from
      (Polynomial.coeff_map _ _).symm]
    -- Suffices to show rename σ GMv = GMv as polynomials in Y
    suffices hpoly : Polynomial.map (MvPolynomial.rename σ).toRingHom GMv = GMv by rw [hpoly]
    -- GMv = Q.derivative * Lagrange_interpolant, but simpler: direct reindexing
    -- Key: σ acts on strictPairs via the "sort" bijection
    simp only [GMv_def]
    rw [Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    have hγ_rename : ∀ ij : Fin p × Fin p,
        MvPolynomial.rename σ (γMv ij) = γMv (σ ij.1, σ ij.2) := by
      intro ij
      simp only [γMv_def, map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
    have hs_rename : ∀ ij : Fin p × Fin p,
        MvPolynomial.rename σ (sMv ij) = sMv (σ ij.1, σ ij.2) := by
      intro ij; simp only [sMv_def, map_add, MvPolynomial.rename_X]
    simp_rw [hγ_rename, hs_rename]
    have hγ_comm : ∀ i j : Fin p, γMv (i, j) = γMv (j, i) := by
      intro i j; simp only [γMv_def]; ring
    have hs_comm : ∀ i j : Fin p, sMv (i, j) = sMv (j, i) := by
      intro i j; simp only [sMv_def]; ring
    -- Sort bijection: map (σ i, σ j) to the strictly-ordered version
    set φ : Fin p × Fin p → Fin p × Fin p :=
      fun ij => if σ ij.1 < σ ij.2 then (σ ij.1, σ ij.2) else (σ ij.2, σ ij.1) with φ_def
    -- φ maps strictPairs to strictPairs
    have hφ_mem : ∀ ij ∈ strictPairs p, φ ij ∈ strictPairs p := by
      intro ij hij
      simp only [strictPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
      simp only [φ]; split_ifs with h
      · exact h
      · exact lt_of_le_of_ne (not_lt.mp h) (fun heq => hij.ne (σ.injective heq.symm))
    -- φ is injective on strictPairs
    have hφ_inj : ∀ ij₁ ∈ strictPairs p, ∀ ij₂ ∈ strictPairs p,
        φ ij₁ = φ ij₂ → ij₁ = ij₂ := by
      intro ij₁ hij₁ ij₂ hij₂ heq
      have h₁ : ij₁.1 < ij₁.2 := (Finset.mem_filter.mp hij₁).2
      have h₂ : ij₂.1 < ij₂.2 := (Finset.mem_filter.mp hij₂).2
      simp only [φ] at heq
      split_ifs at heq with ha hb hb
      all_goals (obtain ⟨hc, hd⟩ := Prod.mk.inj heq)
      · exact Prod.ext (σ.injective hc) (σ.injective hd)
      · exfalso; exact absurd (σ.injective hc ▸ σ.injective hd ▸ h₂ :
          ij₁.2 < ij₁.1) (not_lt.mpr h₁.le)
      · exfalso; exact absurd (σ.injective hc ▸ σ.injective hd ▸ h₁ :
          ij₂.2 < ij₂.1) (not_lt.mpr h₂.le)
      · exact Prod.ext (σ.injective hd) (σ.injective hc)
    -- φ is surjective onto strictPairs
    have hφ_surj : ∀ ij ∈ strictPairs p, ∃ ij' ∈ strictPairs p, φ ij' = ij := by
      intro ij hij
      have hij_lt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
      by_cases hord : σ.symm ij.1 < σ.symm ij.2
      · refine ⟨(σ.symm ij.1, σ.symm ij.2),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hord⟩, ?_⟩
        simp only [φ, Equiv.apply_symm_apply, if_pos hij_lt]
      · have hord' : σ.symm ij.2 < σ.symm ij.1 :=
          lt_of_le_of_ne (not_lt.mp hord) (fun h => hij_lt.ne (σ.symm.injective h).symm)
        refine ⟨(σ.symm ij.2, σ.symm ij.1),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hord'⟩, ?_⟩
        simp only [φ, Equiv.apply_symm_apply, if_neg (not_lt.mpr hij_lt.le)]
    -- φ preserves γMv values (up to commutativity)
    have hφ_γ : ∀ ij, γMv (σ ij.1, σ ij.2) = γMv (φ ij) := by
      intro ij; simp only [φ]; split_ifs <;> [rfl; exact hγ_comm _ _]
    -- φ preserves sMv values (up to commutativity)
    have hφ_s : ∀ ij, sMv (σ ij.1, σ ij.2) = sMv (φ ij) := by
      intro ij; simp only [φ]; split_ifs <;> [rfl; exact hs_comm _ _]
    -- Reindex the sum
    apply Finset.sum_nbij φ hφ_mem
      (fun ij₁ hij₁ ij₂ hij₂ heq => hφ_inj ij₁ hij₁ ij₂ hij₂ heq)
      (fun ij hij => hφ_surj ij hij)
    -- Value equality for each summand
    intro ij hij
    rw [hφ_s ij]
    suffices hprod : ∏ kl ∈ (strictPairs p).erase ij, (Polynomial.X - Polynomial.C (γMv (σ kl.1, σ kl.2))) =
        ∏ kl ∈ (strictPairs p).erase (φ ij), (Polynomial.X - Polynomial.C (γMv kl)) by
      rw [hprod]
    -- Product over erase'd set: same reindexing
    apply Finset.prod_nbij φ
    · -- Maps into SP.erase (φ ij)
      intro kl hkl
      refine Finset.mem_erase.mpr ⟨?_, hφ_mem kl (Finset.mem_of_mem_erase hkl)⟩
      intro heq
      exact (Finset.ne_of_mem_erase hkl)
        (hφ_inj kl (Finset.mem_of_mem_erase hkl) ij hij heq)
    · -- Injective
      intro kl₁ hkl₁ kl₂ hkl₂ heq
      exact hφ_inj kl₁ (Finset.mem_of_mem_erase hkl₁) kl₂ (Finset.mem_of_mem_erase hkl₂) heq
    · -- Surjective
      intro kl hkl
      obtain ⟨kl', hkl'_mem, hkl'_eq⟩ := hφ_surj kl (Finset.mem_of_mem_erase hkl)
      refine ⟨kl', Finset.mem_erase.mpr ⟨?_, hkl'_mem⟩, hkl'_eq⟩
      intro heq
      exact (Finset.ne_of_mem_erase hkl) (hkl'_eq ▸ congr_arg φ heq)
    · -- Values
      intro kl _
      simp only [sub_right_inj]
      exact congr_arg Polynomial.C (hφ_γ kl)
  rw [hcoeff]
  exact Azurite.BPR.proposition_2_16 P x hx _ hsymm

/-- Each coefficient of G(Z,Y) belongs to R[Z]. -/
theorem G_coeff_mem_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) :
    ∃ q : R[X], q.map (algebraMap R L) = (GPoly x).coeff n := by
  rw [poly_in_image_iff_coeffs_in_range]; intro m
  haveI : Infinite R := Infinite.of_injective (Nat.cast : ℕ → R) Nat.cast_injective
  exact eval_range_implies_coeff_range _ (G_eval_coeff_in_R P x hx n) m

/-- The n-th Y-coefficient of H(Z,Y), evaluated at z = algebraMap r, lies in R.
    Same structure as G: MvPolynomial lifting + symmetry + proposition_2_16. -/
theorem H_eval_coeff_in_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) (r : R) :
    Polynomial.eval (algebraMap R L r) ((HPoly x).coeff n)
      ∈ Set.range (algebraMap R L) := by
  -- Identical structure to G_eval_coeff_in_R with sMv replaced by pMv (product)
  set γMv : Fin p × Fin p → MvPolynomial (Fin p) R :=
    fun ij => MvPolynomial.X ij.1 + MvPolynomial.X ij.2 +
      MvPolynomial.C r * MvPolynomial.X ij.1 * MvPolynomial.X ij.2 with γMv_def
  set pMv : Fin p × Fin p → MvPolynomial (Fin p) R :=
    fun ij => MvPolynomial.X ij.1 * MvPolynomial.X ij.2 with pMv_def
  set HMv : (MvPolynomial (Fin p) R)[X] :=
    ∑ ij ∈ strictPairs p,
      Polynomial.C (pMv ij) *
      ∏ kl ∈ (strictPairs p).erase ij,
        (Polynomial.X - Polynomial.C (γMv kl)) with HMv_def
  have hγ : ∀ ij ∈ strictPairs p,
      (MvPolynomial.aeval x) (γMv ij) =
        Polynomial.eval (algebraMap R L r) (gammaPoly x ij.1 ij.2) := by
    intro ij _
    simp only [γMv_def, gammaPoly, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hp_aeval : ∀ ij ∈ strictPairs p,
      (MvPolynomial.aeval x) (pMv ij) = x ij.1 * x ij.2 := by
    intro ij _; simp only [pMv_def, map_mul, MvPolynomial.aeval_X]
  have hH : Polynomial.map (MvPolynomial.aeval x).toRingHom HMv =
      Polynomial.map (Polynomial.evalRingHom (algebraMap R L r)) (HPoly x) := by
    simp only [HMv_def, HPoly]
    rw [Polynomial.map_sum, Polynomial.map_sum]
    apply Finset.sum_congr rfl; intro ij hij
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C]
    congr 1
    · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, hp_aeval ij hij]
    · rw [Polynomial.map_prod, Polynomial.map_prod]
      apply Finset.prod_congr rfl; intro kl hkl
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.coe_evalRingHom]
      rw [hγ kl (Finset.mem_of_mem_erase hkl)]
  have hcoeff : Polynomial.eval (algebraMap R L r) ((HPoly x).coeff n) =
      (MvPolynomial.aeval x) (HMv.coeff n) := by
    have := congr_arg (fun q => q.coeff n) hH
    simp only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    exact this.symm
  have hsymm : (HMv.coeff n).IsSymmetric := by
    intro σ
    rw [show MvPolynomial.rename σ (HMv.coeff n) =
        (Polynomial.map (MvPolynomial.rename σ).toRingHom HMv).coeff n from
      (Polynomial.coeff_map _ _).symm]
    suffices hpoly : Polynomial.map (MvPolynomial.rename σ).toRingHom HMv = HMv by rw [hpoly]
    simp only [HMv_def]
    rw [Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    have hγ_rename : ∀ ij : Fin p × Fin p,
        MvPolynomial.rename σ (γMv ij) = γMv (σ ij.1, σ ij.2) := by
      intro ij
      simp only [γMv_def, map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
    have hp_rename : ∀ ij : Fin p × Fin p,
        MvPolynomial.rename σ (pMv ij) = pMv (σ ij.1, σ ij.2) := by
      intro ij; simp only [pMv_def, map_mul, MvPolynomial.rename_X]
    simp_rw [hγ_rename, hp_rename]
    have hγ_comm : ∀ i j : Fin p, γMv (i, j) = γMv (j, i) := by
      intro i j; simp only [γMv_def]; ring
    have hp_comm : ∀ i j : Fin p, pMv (i, j) = pMv (j, i) := by
      intro i j; simp only [pMv_def]; ring
    set φ : Fin p × Fin p → Fin p × Fin p :=
      fun ij => if σ ij.1 < σ ij.2 then (σ ij.1, σ ij.2) else (σ ij.2, σ ij.1) with φ_def
    have hφ_mem : ∀ ij ∈ strictPairs p, φ ij ∈ strictPairs p := by
      intro ij hij
      simp only [strictPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
      simp only [φ]; split_ifs with h
      · exact h
      · exact lt_of_le_of_ne (not_lt.mp h) (fun heq => hij.ne (σ.injective heq.symm))
    have hφ_inj : ∀ ij₁ ∈ strictPairs p, ∀ ij₂ ∈ strictPairs p,
        φ ij₁ = φ ij₂ → ij₁ = ij₂ := by
      intro ij₁ hij₁ ij₂ hij₂ heq
      have h₁ : ij₁.1 < ij₁.2 := (Finset.mem_filter.mp hij₁).2
      have h₂ : ij₂.1 < ij₂.2 := (Finset.mem_filter.mp hij₂).2
      simp only [φ] at heq
      split_ifs at heq with ha hb hb
      all_goals (obtain ⟨hc, hd⟩ := Prod.mk.inj heq)
      · exact Prod.ext (σ.injective hc) (σ.injective hd)
      · exfalso; exact absurd (σ.injective hc ▸ σ.injective hd ▸ h₂ :
          ij₁.2 < ij₁.1) (not_lt.mpr h₁.le)
      · exfalso; exact absurd (σ.injective hc ▸ σ.injective hd ▸ h₁ :
          ij₂.2 < ij₂.1) (not_lt.mpr h₂.le)
      · exact Prod.ext (σ.injective hd) (σ.injective hc)
    have hφ_surj : ∀ ij ∈ strictPairs p, ∃ ij' ∈ strictPairs p, φ ij' = ij := by
      intro ij hij
      have hij_lt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
      by_cases hord : σ.symm ij.1 < σ.symm ij.2
      · refine ⟨(σ.symm ij.1, σ.symm ij.2),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hord⟩, ?_⟩
        simp only [φ, Equiv.apply_symm_apply, if_pos hij_lt]
      · have hord' : σ.symm ij.2 < σ.symm ij.1 :=
          lt_of_le_of_ne (not_lt.mp hord) (fun h => hij_lt.ne (σ.symm.injective h).symm)
        refine ⟨(σ.symm ij.2, σ.symm ij.1),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hord'⟩, ?_⟩
        simp only [φ, Equiv.apply_symm_apply, if_neg (not_lt.mpr hij_lt.le)]
    have hφ_γ : ∀ ij, γMv (σ ij.1, σ ij.2) = γMv (φ ij) := by
      intro ij; simp only [φ]; split_ifs <;> [rfl; exact hγ_comm _ _]
    have hφ_p : ∀ ij, pMv (σ ij.1, σ ij.2) = pMv (φ ij) := by
      intro ij; simp only [φ]; split_ifs <;> [rfl; exact hp_comm _ _]
    apply Finset.sum_nbij φ hφ_mem
      (fun ij₁ hij₁ ij₂ hij₂ heq => hφ_inj ij₁ hij₁ ij₂ hij₂ heq)
      (fun ij hij => hφ_surj ij hij)
    intro ij hij
    rw [hφ_p ij]
    suffices hprod : ∏ kl ∈ (strictPairs p).erase ij, (Polynomial.X - Polynomial.C (γMv (σ kl.1, σ kl.2))) =
        ∏ kl ∈ (strictPairs p).erase (φ ij), (Polynomial.X - Polynomial.C (γMv kl)) by
      rw [hprod]
    apply Finset.prod_nbij φ
    · intro kl hkl
      refine Finset.mem_erase.mpr ⟨?_, hφ_mem kl (Finset.mem_of_mem_erase hkl)⟩
      intro heq
      exact (Finset.ne_of_mem_erase hkl)
        (hφ_inj kl (Finset.mem_of_mem_erase hkl) ij hij heq)
    · intro kl₁ hkl₁ kl₂ hkl₂ heq
      exact hφ_inj kl₁ (Finset.mem_of_mem_erase hkl₁) kl₂ (Finset.mem_of_mem_erase hkl₂) heq
    · intro kl hkl
      obtain ⟨kl', hkl'_mem, hkl'_eq⟩ := hφ_surj kl (Finset.mem_of_mem_erase hkl)
      refine ⟨kl', Finset.mem_erase.mpr ⟨?_, hkl'_mem⟩, hkl'_eq⟩
      intro heq
      exact (Finset.ne_of_mem_erase hkl) (hkl'_eq ▸ congr_arg φ heq)
    · intro kl _
      simp only [sub_right_inj]
      exact congr_arg Polynomial.C (hφ_γ kl)
  rw [hcoeff]
  exact Azurite.BPR.proposition_2_16 P x hx _ hsymm

/-- Each coefficient of H(Z,Y) belongs to R[Z]. -/
theorem H_coeff_mem_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) :
    ∃ q : R[X], q.map (algebraMap R L) = (HPoly x).coeff n := by
  rw [poly_in_image_iff_coeffs_in_range]; intro m
  haveI : Infinite R := Infinite.of_injective (Nat.cast : ℕ → R) Nat.cast_injective
  exact eval_range_implies_coeff_range _ (H_eval_coeff_in_R P x hx n) m

/-! ### Evaluation at roots of Q -/

/-- Q vanishes at γ_{ij}: Q(Z, γ_{ij}(Z)) = 0, since γ_{ij} is a factor of Q. -/
theorem Q_eval_gamma (x : Fin p → L) (ij : Fin p × Fin p) (hij : ij ∈ strictPairs p) :
    Polynomial.eval (gammaPoly x ij.1 ij.2) (QPolynomial x) = 0 := by
  simp only [QPolynomial, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  exact ⟨ij, hij, by simp⟩

/-- General Lagrange evaluation: evaluating ∑_{i ∈ s} C(c_i) · ∏_{j ∈ s.erase i} (X - C(γ_j))
    at γ_m (where m ∈ s) gives c_m · ∏_{j ∈ s.erase m} (γ_m - γ_j).
    This works because for i ≠ m, the product includes j = m, giving factor (γ_m - γ_m) = 0. -/
theorem eval_lagrange_sum {A : Type*} [CommRing A] [DecidableEq ι]
    (s : Finset ι) (c : ι → A) (γ : ι → A)
    (m : ι) (hm : m ∈ s) :
    Polynomial.eval (γ m)
      (∑ i ∈ s, Polynomial.C (c i) * ∏ j ∈ s.erase i, (Polynomial.X - Polynomial.C (γ j))) =
    c m * ∏ j ∈ s.erase m, (γ m - γ j) := by
  rw [Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single m]
  · -- Main term
    simp [Polynomial.eval_mul, Polynomial.eval_prod]
  · -- Other terms vanish
    intro i hi him
    simp only [Polynomial.eval_mul]
    apply mul_eq_zero_of_right
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm him, hm⟩)
    simp
  · intro hm'; exact absurd hm hm'

/-- G(Z, γ_{ij}(Z)) = (x_i + x_j) · ∏_{(k,l)≠(i,j)} (γ_{ij} - γ_{kl}) in L[Z]. -/
theorem G_eval_gamma (x : Fin p → L) (ij : Fin p × Fin p) (hij : ij ∈ strictPairs p) :
    Polynomial.eval (gammaPoly x ij.1 ij.2) (GPoly x) =
    Polynomial.C (x ij.1 + x ij.2) *
      ∏ kl ∈ (strictPairs p).erase ij,
        (gammaPoly x ij.1 ij.2 - gammaPoly x kl.1 kl.2) := by
  simp only [GPoly]
  exact eval_lagrange_sum (strictPairs p)
    (fun kl => Polynomial.C (x kl.1 + x kl.2))
    (fun kl => gammaPoly x kl.1 kl.2) ij hij

/-- H(Z, γ_{ij}(Z)) = (x_i · x_j) · ∏_{(k,l)≠(i,j)} (γ_{ij} - γ_{kl}) in L[Z]. -/
theorem H_eval_gamma (x : Fin p → L) (ij : Fin p × Fin p) (hij : ij ∈ strictPairs p) :
    Polynomial.eval (gammaPoly x ij.1 ij.2) (HPoly x) =
    Polynomial.C (x ij.1 * x ij.2) *
      ∏ kl ∈ (strictPairs p).erase ij,
        (gammaPoly x ij.1 ij.2 - gammaPoly x kl.1 kl.2) := by
  simp only [HPoly]
  exact eval_lagrange_sum (strictPairs p)
    (fun kl => Polynomial.C (x kl.1 * x kl.2))
    (fun kl => gammaPoly x kl.1 kl.2) ij hij

/-- At the root γ_{ij} of Q, x_i is a root of the quadratic P·T²−G·T+H over L[Z],
    where P = ∏_{(k,l)≠(i,j)} (γ_{ij} − γ_{kl}).
    Proof: after substituting the Lagrange evaluations G_ij = C(s)·P, H_ij = C(p)·P,
    we get P·(x_i² − s·x_i + p) = 0, which vanishes because s = x_i+x_j, p = x_i·x_j. -/
theorem quadratic_root_xi (x : Fin p → L)
    (ij : Fin p × Fin p) :
    let P := ∏ kl ∈ (strictPairs p).erase ij,
          (gammaPoly x ij.1 ij.2 - gammaPoly x kl.1 kl.2)
    P * Polynomial.C (x ij.1) ^ 2 -
      (Polynomial.C (x ij.1 + x ij.2) * P) * Polynomial.C (x ij.1) +
      (Polynomial.C (x ij.1 * x ij.2) * P) = 0 := by
  simp only []
  have : Polynomial.C (x ij.1) ^ 2 - Polynomial.C (x ij.1 + x ij.2) * Polynomial.C (x ij.1) +
    Polynomial.C (x ij.1 * x ij.2) = 0 := by
    simp [map_add, map_mul]; ring
  calc _ = (∏ kl ∈ (strictPairs p).erase ij,
            (gammaPoly x ij.1 ij.2 - gammaPoly x kl.1 kl.2)) *
           (Polynomial.C (x ij.1) ^ 2 - Polynomial.C (x ij.1 + x ij.2) * Polynomial.C (x ij.1) +
             Polynomial.C (x ij.1 * x ij.2)) := by ring
       _ = _ * 0 := by rw [this]
       _ = 0 := by ring

/-- Similarly, x_j is a root of the same quadratic. -/
theorem quadratic_root_xj (x : Fin p → L)
    (ij : Fin p × Fin p) :
    let P := ∏ kl ∈ (strictPairs p).erase ij,
          (gammaPoly x ij.1 ij.2 - gammaPoly x kl.1 kl.2)
    P * Polynomial.C (x ij.2) ^ 2 -
      (Polynomial.C (x ij.1 + x ij.2) * P) * Polynomial.C (x ij.2) +
      (Polynomial.C (x ij.1 * x ij.2) * P) = 0 := by
  simp only []
  have : Polynomial.C (x ij.2) ^ 2 - Polynomial.C (x ij.1 + x ij.2) * Polynomial.C (x ij.2) +
    Polynomial.C (x ij.1 * x ij.2) = 0 := by
    simp [map_add, map_mul]; ring
  calc _ = (∏ kl ∈ (strictPairs p).erase ij,
            (gammaPoly x ij.1 ij.2 - gammaPoly x kl.1 kl.2)) *
           (Polynomial.C (x ij.2) ^ 2 - Polynomial.C (x ij.1 + x ij.2) * Polynomial.C (x ij.2) +
             Polynomial.C (x ij.1 * x ij.2)) := by ring
       _ = _ * 0 := by rw [this]
       _ = 0 := by ring

/-! ### F ∈ R[Z][Y] — follows from Q ∈ R[Z][Y] since F = ∂Q/∂Y -/

/-- Each coefficient of F(Z,Y) belongs to R[Z].
    Since F = derivative Q and Q ∈ R[Z][Y], this is immediate. -/
theorem F_coeff_mem_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) :
    ∃ q : R[X], q.map (algebraMap R L) = (FPoly x).coeff n := by
  -- F = derivative Q. coeff n of p' = (n+1) * coeff (n+1) of p
  simp only [FPoly, Polynomial.coeff_derivative]
  obtain ⟨q, hq⟩ := Q_coeff_mem_R P x hx (n + 1)
  refine ⟨Polynomial.C (↑n + 1 : R) * q, ?_⟩
  rw [Polynomial.map_mul, Polynomial.map_C, hq]
  simp [map_add, map_natCast, map_one, mul_comm]

/-! ### Degree and structure of Q -/

/-- Q(Z,Y) is monic as a polynomial in Y — it is a product of monic linear factors. -/
theorem monic_QPolynomial (x : Fin p → L) :
    (QPolynomial x).Monic := by
  exact Polynomial.monic_prod_of_monic _ _ (fun ij _ => Polynomial.monic_X_sub_C _)

/-- The Y-degree of Q equals the number of strict pairs = p(p-1)/2. -/
theorem natDegree_QPolynomial (x : Fin p → L) :
    (QPolynomial x).natDegree = (strictPairs p).card := by
  rw [QPolynomial, Polynomial.natDegree_prod]
  · simp
  · intro ij _; exact (Polynomial.monic_X_sub_C _).ne_zero

/-! ### Discriminant: D ≠ 0 -/

/-- If x : Fin p → L is injective (all roots distinct), then discPoly x ≠ 0. -/
theorem discPoly_ne_zero (x : Fin p → L)
    (hx_inj : Function.Injective x) :
    discPoly x ≠ 0 := by
  simp only [discPoly, Finset.prod_ne_zero_iff]
  intro ⟨a, b⟩ hab
  simp only [Finset.mem_offDiag] at hab
  obtain ⟨ha_mem, hb_mem, hab_ne⟩ := hab
  simp only [strictPairs, Finset.mem_filter, Finset.mem_univ, true_and] at ha_mem hb_mem
  simp only [gammaPoly]
  intro heq
  have hcoeff0 : x a.1 + x a.2 - (x b.1 + x b.2) = 0 := by
    have := congr_arg (fun p => Polynomial.coeff p 0) heq
    simp at this; exact this
  have hcoeff1 : x a.1 * x a.2 - x b.1 * x b.2 = 0 := by
    have := congr_arg (fun p => Polynomial.coeff p 1) heq
    simp at this; exact this
  have hsum : x a.1 + x a.2 = x b.1 + x b.2 := sub_eq_zero.mp hcoeff0
  have hprod : x a.1 * x a.2 = x b.1 * x b.2 := sub_eq_zero.mp hcoeff1
  -- x a.1 is a root of (T - x b.1)(T - x b.2)
  have hroot : (x a.1 - x b.1) * (x a.1 - x b.2) = 0 := by
    linear_combination x a.1 * hsum - hprod
  rcases mul_eq_zero.mp hroot with h | h
  · -- x a.1 = x b.1, so a.1 = b.1
    have ha1 : x a.1 = x b.1 := sub_eq_zero.mp h
    have heq1 : a.1 = b.1 := hx_inj ha1
    -- Then x a.2 = x b.2 from hsum
    have ha2 : x a.2 = x b.2 := by linear_combination hsum - ha1
    have heq2 : a.2 = b.2 := hx_inj ha2
    exact hab_ne (Prod.ext heq1 heq2)
  · -- x a.1 = x b.2, so a.1 = b.2
    have ha1 : x a.1 = x b.2 := sub_eq_zero.mp h
    have heq1 : a.1 = b.2 := hx_inj ha1
    -- Then x a.2 = x b.1 from hsum
    have ha2 : x a.2 = x b.1 := by linear_combination hsum - ha1
    have heq2 : a.2 = b.1 := hx_inj ha2
    -- But a.1 < a.2 = b.1 < b.2 = a.1, contradiction
    omega

/-- Since R is infinite and discPoly ≠ 0, there exists z with D(z) ≠ 0. -/
theorem exists_discPoly_eval_ne_zero [IsRealClosed R]
    {p : ℕ} (x : Fin p → L)
    (hx_inj : Function.Injective x) :
    ∃ z : R, Polynomial.eval (algebraMap R L z) (discPoly x) ≠ 0 := by
  haveI : Infinite R := Infinite.of_injective (Nat.cast : ℕ → R) Nat.cast_injective
  have hD : discPoly x ≠ 0 := discPoly_ne_zero x hx_inj
  by_contra h; push Not at h
  classical
  have hinj := (algebraMap R L).injective
  set d := (discPoly x).natDegree
  set emb := Infinite.natEmbedding R
  -- The d+1 elements emb 0, ..., emb d map to d+1 distinct roots
  have hcard : Finset.card ((Finset.range (d + 1)).image (fun i => algebraMap R L (emb i))) = d + 1 := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range (d + 1)
    · exact hinj.comp emb.injective
  -- Each of these is a root
  have hsub : ((Finset.range (d + 1)).image (fun i => algebraMap R L (emb i))).val ⊆
      (discPoly x).roots := by
    intro y hy
    rw [Finset.mem_val, Finset.mem_image] at hy
    obtain ⟨i, _, rfl⟩ := hy
    rw [Polynomial.mem_roots hD]
    exact h (emb i)
  -- So d + 1 ≤ natDegree = d, contradiction
  have hle : d + 1 ≤ d :=
    hcard ▸ Polynomial.card_le_degree_of_subset_roots hsub
  omega

/-! ### Separability of Q at a point -/

/-- Q(z, ·) = ∏ (X - C(γ_{ij}(z))) is separable iff all γ_{ij}(z) are distinct,
    i.e., when D(z) ≠ 0. For a Finset product. -/
theorem separable_Q_eval (x : Fin p → L) (z : L)
    (hdist : ∀ a ∈ strictPairs p, ∀ b ∈ strictPairs p,
      Polynomial.eval z (gammaPoly x a.1 a.2) = Polynomial.eval z (gammaPoly x b.1 b.2) → a = b) :
    ((QPolynomial x).map (Polynomial.evalRingHom z)).Separable := by
  simp only [QPolynomial, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.coe_evalRingHom]
  exact Polynomial.separable_prod_X_sub_C_iff'.mpr hdist

/-! ### D ∈ R[Z] -/

/-- Evaluating D(Z) at z = algebraMap r gives an R-value.
    This follows from the MvPolynomial lifting: D is the product of differences γ_a − γ_b
    over the off-diagonal of strictPairs, which forms a symmetric polynomial in the roots. -/
theorem D_eval_in_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (r : R) :
    Polynomial.eval (algebraMap R L r) (discPoly x) ∈ Set.range (algebraMap R L) := by
  -- Lift to MvPolynomial
  set γMv : Fin p × Fin p → MvPolynomial (Fin p) R :=
    fun ij => MvPolynomial.X ij.1 + MvPolynomial.X ij.2 +
      MvPolynomial.C r * MvPolynomial.X ij.1 * MvPolynomial.X ij.2 with γMv_def
  -- D = ∏ (γ_a - γ_b) over offDiag. Lift to MvPolynomial
  set DMv : MvPolynomial (Fin p) R :=
    ∏ ab ∈ (strictPairs p).offDiag, (γMv ab.1 - γMv ab.2) with DMv_def
  -- Check that evaluating DMv at the roots gives D evaluated at algebraMap r
  have hcoeff : Polynomial.eval (algebraMap R L r) (discPoly x) =
      MvPolynomial.aeval x DMv := by
    simp only [discPoly, DMv_def, map_prod, map_sub, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro ab _
    simp only [γMv_def, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      gammaPoly, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  -- DMv is symmetric (any permutation σ of roots gives σ · DMv = DMv)
  have hsymm : ∀ σ : Equiv.Perm (Fin p),
      MvPolynomial.rename σ DMv = DMv := by
    intro σ
    simp only [DMv_def, map_prod, map_sub]
    -- Under renaming by σ, γMv(i,j) becomes γMv(σi, σj).
    -- The product ∏ (γMv(a.1) - γMv(a.2)) over offDiag is unchanged because
    -- σ permutes the off-diagonal pairs.
    -- The key: γMv is equivariant
    have hγ_rename : ∀ ij : Fin p × Fin p,
        MvPolynomial.rename σ (γMv ij) = γMv (σ ij.1, σ ij.2) := by
      intro ij
      simp only [γMv_def, map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
    have hγ_comm : ∀ i j : Fin p, γMv (i, j) = γMv (j, i) := by
      intro i j; simp only [γMv_def]; ring
    -- Sort bijection on strictPairs
    set φ : Fin p × Fin p → Fin p × Fin p :=
      fun ij => if σ ij.1 < σ ij.2 then (σ ij.1, σ ij.2) else (σ ij.2, σ ij.1) with φ_def
    have hφ_mem : ∀ ij ∈ strictPairs p, φ ij ∈ strictPairs p := by
      intro ij hij
      simp only [strictPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
      simp only [φ]; split_ifs with h
      · exact h
      · exact lt_of_le_of_ne (not_lt.mp h) (fun heq => hij.ne (σ.injective heq.symm))
    have hφ_inj : ∀ ij₁ ∈ strictPairs p, ∀ ij₂ ∈ strictPairs p,
        φ ij₁ = φ ij₂ → ij₁ = ij₂ := by
      intro ij₁ hij₁ ij₂ hij₂ heq
      have h₁ : ij₁.1 < ij₁.2 := (Finset.mem_filter.mp hij₁).2
      have h₂ : ij₂.1 < ij₂.2 := (Finset.mem_filter.mp hij₂).2
      simp only [φ] at heq
      split_ifs at heq with ha hb hb
      all_goals (obtain ⟨hc, hd⟩ := Prod.mk.inj heq)
      · exact Prod.ext (σ.injective hc) (σ.injective hd)
      · exfalso; exact absurd (σ.injective hc ▸ σ.injective hd ▸ h₂ :
          ij₁.2 < ij₁.1) (not_lt.mpr h₁.le)
      · exfalso; exact absurd (σ.injective hc ▸ σ.injective hd ▸ h₁ :
          ij₂.2 < ij₂.1) (not_lt.mpr h₂.le)
      · exact Prod.ext (σ.injective hd) (σ.injective hc)
    have hφ_surj : ∀ ij ∈ strictPairs p, ∃ ij' ∈ strictPairs p, φ ij' = ij := by
      intro ij hij
      have hij_lt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
      by_cases hord : σ.symm ij.1 < σ.symm ij.2
      · refine ⟨(σ.symm ij.1, σ.symm ij.2),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hord⟩, ?_⟩
        simp only [φ, Equiv.apply_symm_apply, if_pos hij_lt]
      · have hord' : σ.symm ij.2 < σ.symm ij.1 :=
          lt_of_le_of_ne (not_lt.mp hord) (fun h => hij_lt.ne (σ.symm.injective h).symm)
        refine ⟨(σ.symm ij.2, σ.symm ij.1),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hord'⟩, ?_⟩
        simp only [φ, Equiv.apply_symm_apply, if_neg (not_lt.mpr hij_lt.le)]
    have hφ_γ : ∀ ij, γMv (σ ij.1, σ ij.2) = γMv (φ ij) := by
      intro ij; simp only [φ]; split_ifs <;> [rfl; exact hγ_comm _ _]
    -- Now build bijection on offDiag
    set ψ : (Fin p × Fin p) × (Fin p × Fin p) → (Fin p × Fin p) × (Fin p × Fin p) :=
      fun ab => (φ ab.1, φ ab.2) with ψ_def
    apply Finset.prod_nbij ψ
    · -- ψ maps offDiag to offDiag
      intro ab hab
      simp only [Finset.mem_offDiag] at hab ⊢
      simp only [ψ]
      exact ⟨hφ_mem ab.1 hab.1, hφ_mem ab.2 hab.2.1,
        fun heq => hab.2.2 (hφ_inj ab.1 hab.1 ab.2 hab.2.1 heq)⟩
    · -- ψ injective on offDiag
      intro ab₁ hab₁ ab₂ hab₂ heq
      rw [Finset.mem_coe, Finset.mem_offDiag] at hab₁ hab₂
      simp only [ψ] at heq
      obtain ⟨h1, h2⟩ := Prod.mk.inj heq
      exact Prod.ext (hφ_inj _ hab₁.1 _ hab₂.1 h1) (hφ_inj _ hab₁.2.1 _ hab₂.2.1 h2)
    · -- ψ surjective onto offDiag
      intro ab hab
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_offDiag] at hab ⊢
      obtain ⟨a', ha'_mem, ha'_eq⟩ := hφ_surj ab.1 hab.1
      obtain ⟨b', hb'_mem, hb'_eq⟩ := hφ_surj ab.2 hab.2.1
      exact ⟨(a', b'), ⟨ha'_mem, hb'_mem,
        fun heq => hab.2.2 (ha'_eq ▸ hb'_eq ▸ congr_arg φ heq)⟩,
        show ψ (a', b') = ab from Prod.ext ha'_eq hb'_eq⟩
    · -- Values match
      intro ab _
      simp only [ψ]
      rw [hγ_rename, hγ_rename, hφ_γ, hφ_γ]
  rw [hcoeff]
  exact Azurite.BPR.proposition_2_16 P x hx _ hsymm

/-- Each coefficient of D(Z) lies in R. -/
theorem D_coeff_mem_R [IsRealClosed R]
    {p : ℕ} (P : R[X]) (x : Fin p → L)
    (hx : P.map (algebraMap R L) = ∏ j : Fin p, (X - Polynomial.C (x j)))
    (n : ℕ) :
    (discPoly x).coeff n ∈ Set.range (algebraMap R L) := by
  haveI : Infinite R := Infinite.of_injective (Nat.cast : ℕ → R) Nat.cast_injective
  exact eval_range_implies_coeff_range _ (D_eval_in_R P x hx) n

/-! ### Square roots in R[i] -/

/-- In a real closed field, a² + b² is always a square.
    Proof: by isSquare_or_isSquare_neg, either a²+b² is a square (done) or
    -(a²+b²) is a square, say -(a²+b²) = c². Then a²+b²+c² = 0, but this
    is a sum of squares in a semireal ring (where -1 is not a sum of squares),
    so a = b = c = 0. -/
theorem isSquare_sum_sq [IsRealClosed R] (a b : R) : IsSquare (a ^ 2 + b ^ 2) := by
  rcases IsRealClosed.isSquare_or_isSquare_neg (a ^ 2 + b ^ 2) with h | h
  · exact h
  · obtain ⟨c, hc⟩ := h
    have h0 : a * a + b * b + c * c = 0 := by
      have : a ^ 2 + b ^ 2 + c * c = 0 := by linear_combination -hc
      rwa [sq, sq] at this
    -- If a = b = 0 then a²+b² = 0 is a square; use IsSquare 0 directly
    by_cases ha : a = 0
    · subst ha; simp only [zero_mul, zero_add] at h0 ⊢
      by_cases hb : b = 0
      · subst hb; simp
      · -- b ≠ 0, h0 : b*b + c*c = 0. Show -1 is IsSumSq → contradiction.
        exfalso; apply IsSemireal.not_isSumSq_neg_one (R := R)
        have key : (b * b + c * c) * (b⁻¹ * b⁻¹) = 0 := by rw [h0, zero_mul]
        have expand : (b * b + c * c) * (b⁻¹ * b⁻¹) =
          b * b⁻¹ * (b * b⁻¹) + (b⁻¹ * c) * (b⁻¹ * c) := by ring
        rw [expand, mul_inv_cancel₀ hb, one_mul] at key
        -- key : 1 + (b⁻¹*c)*(b⁻¹*c) = 0
        rw [show (-1 : R) = (b⁻¹ * c) * (b⁻¹ * c) from by linear_combination -key]
        exact IsSumSq.mul_self _
    · -- a ≠ 0
      exfalso; apply IsSemireal.not_isSumSq_neg_one (R := R)
      have key : (a * a + b * b + c * c) * (a⁻¹ * a⁻¹) = 0 := by rw [h0, zero_mul]
      have expand : (a * a + b * b + c * c) * (a⁻¹ * a⁻¹) =
        a * a⁻¹ * (a * a⁻¹) + (a⁻¹ * b) * (a⁻¹ * b) + (a⁻¹ * c) * (a⁻¹ * c) := by ring
      rw [expand, mul_inv_cancel₀ ha, one_mul] at key
      -- key : 1 + (a⁻¹*b)*(a⁻¹*b) + (a⁻¹*c)*(a⁻¹*c) = 0
      rw [show (-1 : R) = (a⁻¹ * b) * (a⁻¹ * b) + (a⁻¹ * c) * (a⁻¹ * c) from
        by linear_combination -key]
      exact IsSumSq.sq_add _ (IsSumSq.mul_self _)

/-- Every element of R[i] has a square root when R is real closed.
    For w = a + bi:
    - If b = 0: use isSquare_or_isSquare_neg on a
    - If b ≠ 0: use the formula with √(a²+b²) -/
theorem sqrt_exists_Ri [IsRealClosed R] (w : Ri R) : ∃ v : Ri R, v * v = w := by
  -- Decompose w = algebraMap a + algebraMap b * i (using modByMonic)
  induction w using AdjoinRoot.induction_on with
  | ih p =>
    set f := (X : R[X]) ^ 2 + 1
    have hfm : f.Monic := monic_X_pow_add_C 1 (by norm_num : (2 : ℕ) ≠ 0)
    set r := p %ₘ f
    -- aeval i p = aeval i r
    have haeval_eq : Polynomial.aeval (Ri.i R) p = Polynomial.aeval (Ri.i R) r := by
      have : AdjoinRoot.mk ((X : R[X])^2+1) p = AdjoinRoot.mk ((X : R[X])^2+1) r := by
        rw [AdjoinRoot.mk_eq_mk]
        exact ⟨p /ₘ f, by have := modByMonic_eq_sub_mul_div p f; linear_combination -this⟩
      rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq] at this; exact this
    rw [show AdjoinRoot.mk _ p = Polynomial.aeval (Ri.i R) p from (AdjoinRoot.aeval_eq p).symm,
        haeval_eq]
    -- r has natDegree ≤ 1
    have hr_deg : r.natDegree ≤ 1 := by
      have hrd : r.degree < f.degree := degree_modByMonic_lt p hfm
      have hf_deg : f.degree = 2 := by
        have hnat : f.natDegree = 2 := by
          simp [f]; rw [show (1 : R[X]) = C 1 from rfl]; exact natDegree_X_pow_add_C
        rw [Polynomial.degree_eq_natDegree (Irreducible.ne_zero (Fact.out : Irreducible f)), hnat]
        norm_num
      rw [hf_deg] at hrd
      by_cases hr : r = 0
      · simp [hr]
      · rw [Polynomial.degree_eq_natDegree hr] at hrd
        exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp (by exact_mod_cast hrd))
    -- r = C(coeff 1) * X + C(coeff 0)
    have hr_decomp := Polynomial.eq_X_add_C_of_natDegree_le_one hr_deg
    set a := r.coeff 0
    set b := r.coeff 1
    have haeval_r : ∀ x : Ri R,
        Polynomial.aeval x r = algebraMap R (Ri R) b * x + algebraMap R (Ri R) a := by
      intro x; conv_lhs => rw [hr_decomp]
      simp [Polynomial.aeval_def, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    rw [haeval_r]
    -- Goal: ∃ v, v * v = algebraMap b * i + algebraMap a
    by_cases hb : b = 0
    · -- Case b = 0: w = algebraMap a
      simp only [hb, map_zero, zero_mul, zero_add]
      obtain ⟨v, hv⟩ := sqrt_of_R_in_Ri (R := R) a
      exact ⟨v, by rw [← sq]; exact hv⟩
    · -- Case b ≠ 0: use isSquare_sum_sq
      obtain ⟨d, hd⟩ := isSquare_sum_sq a b
      -- hd : a^2 + b^2 = d * d
      -- Helper: given e with e*e = (a+d')/2 where d'*d' = a²+b² and e ≠ 0,
      -- construct the square root v = algebraMap e + algebraMap(b/(2e)) * i
      suffices hsuff : ∀ d' : R, a ^ 2 + b ^ 2 = d' * d' →
          IsSquare ((a + d') * 2⁻¹) →
          ∃ v, v * v = (algebraMap R (Ri R)) b * Ri.i R + (algebraMap R (Ri R)) a by
        -- Apply isSquare_or_isSquare_neg to (a+d)/2 and (a-d)/2
        rcases IsRealClosed.isSquare_or_isSquare_neg ((a + d) * 2⁻¹) with h₁ | h₁
        · exact hsuff d hd h₁
        · rcases IsRealClosed.isSquare_or_isSquare_neg ((a + -d) * 2⁻¹) with h₂ | h₂
          · exact hsuff (-d) (by rw [neg_mul_neg]; exact hd) h₂
          · -- Both negatives are squares: derive contradiction
            -- -(a+d)/2 = e₁² and -(a-d)/2 = e₂²
            -- Their product: e₁²·e₂² = (a+d)(a-d)/4 · (-1)² = (d²-a²)/4
            -- But d² = a²+b², so (d²-a²)/4 = b²/4
            -- So e₁²·e₂² = b²/4, meaning (e₁·e₂)² = (b/2)²
            -- But -(a+d)/2 · -(a-d)/2 = (a+d)(a-d)/4 = (a²-d²)/4 = -b²/4
            -- So (e₁·e₂)² = -b²/4 = -(b/2)². This gives -1 is a sum of squares.
            exfalso
            obtain ⟨e₁, he₁⟩ := h₁
            obtain ⟨e₂, he₂⟩ := h₂
            apply IsSemireal.not_isSumSq_neg_one (R := R)
            -- -((a+d)/2) * -((a-d)/2) = b²/4
            -- i.e., e₁*e₁ * e₂*e₂ = -(b*b/4)
            -- Wait: -((a+d)/2) * -((a-d)/2) = ((a+d)/2)*((a-d)/2)
            --   = (a²-d²)/4 = (a²-(a²+b²))/4 = -b²/4
            -- So (e₁*e₂)² = -b²/4 = -(b/2)²
            -- Hence -(b/2)² = (e₁*e₂)², so -1 = (e₁*e₂)² / (b/2)²
            --   = (e₁*e₂ * 2/b)² (since b ≠ 0)
            -- i.e. -1 = (2*e₁*e₂/b)²
            have hprod : e₁ * e₁ * (e₂ * e₂) = -(b * 2⁻¹) * (b * 2⁻¹) := by
              have := he₁; have := he₂
              -- he₁: e₁*e₁ = -((a+d)*2⁻¹), he₂: e₂*e₂ = -((a+(-d))*2⁻¹)
              have : e₁ * e₁ * (e₂ * e₂) = -((a+d)*2⁻¹) * -((a + -d)*2⁻¹) := by
                rw [he₁, he₂]
              rw [this]
              have : (a + d) * 2⁻¹ * ((a + -d) * 2⁻¹) = (a * a - d * d) * (2⁻¹ * 2⁻¹) := by ring
              rw [neg_mul_neg, this]
              have hdd : d * d = a ^ 2 + b ^ 2 := hd.symm
              have : a * a - d * d = -(b * b) := by linear_combination -hdd
              rw [this]; ring
            -- So (e₁*e₂)² = -(b/2)². Get -1 = (2*e₁*e₂*b⁻¹)²
            have hb2_ne : b * 2⁻¹ ≠ 0 := by
              intro h; simp [mul_eq_zero, hb] at h
            rw [show (-1 : R) = (e₁ * e₂ * (b * 2⁻¹)⁻¹) * (e₁ * e₂ * (b * 2⁻¹)⁻¹) from by
              field_simp
              have := hprod
              nlinarith [hprod,
                          show (b * 2⁻¹) ^ 2 = b ^ 2 * 2⁻¹ ^ 2 from by ring,
                          show e₁ ^ 2 * e₂ ^ 2 = e₁ * e₁ * (e₂ * e₂) from by ring]]
            exact IsSumSq.mul_self _
      -- Prove the sufficiency: given e with e*e = (a+d')/2, construct v
      intro d' hd' ⟨e, he⟩
      -- e * e = (a + d') * 2⁻¹
      by_cases he0 : e = 0
      · -- e = 0 means (a+d')/2 = 0, so a = -d'. Then d'² = a²+b² = d'²+b² → b²=0 → b=0.
        exfalso; apply hb
        have ha : a + d' = 0 := by
          have h1 : (a + d') * 2⁻¹ = 0 := by rw [he, he0, zero_mul]
          exact (mul_eq_zero.mp h1).resolve_right (inv_ne_zero two_ne_zero)
        have hd'a : d' = -a := by linarith
        rw [hd'a] at hd'
        have : b ^ 2 = 0 := by linear_combination hd'
        exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp this
      · -- e ≠ 0: take v = algebraMap e + algebraMap(b/(2*e)) * i
        refine ⟨algebraMap R (Ri R) e + algebraMap R (Ri R) (b * (2 * e)⁻¹) * Ri.i R, ?_⟩
        -- v * v = (e + (b/(2e))*i)² = e² - (b/(2e))² + 2*e*(b/(2e))*i
        --       = e² - b²/(4e²) + b*i
        -- Need: e² - b²/(4e²) = a and 2*e*(b/(2e)) = b
        -- e² = (a+d')/2 and b²/(4e²) = b²·2/(4(a+d')) = b²/(2(a+d'))
        -- e² - b²/(4e²) = (a+d')/2 - b²/(2(a+d'))
        --   = ((a+d')² - b²) / (2(a+d'))
        --   = (a²+2ad'+d'²-b²) / (2(a+d'))
        --   = (a²+2ad'+a²+b²-b²) / (2(a+d'))   [d'²=a²+b²]
        --   = (2a²+2ad') / (2(a+d'))
        --   = 2a(a+d') / (2(a+d'))
        --   = a ✓
        -- And 2*e*(b/(2e)) = b ✓
        have hi2 := Ri.i_sq R
        -- Step 1: Consolidate algebraMap terms
        have hcoeff : algebraMap R (Ri R) e * algebraMap R (Ri R) (b * (2 * e)⁻¹) =
            algebraMap R (Ri R) (b * 2⁻¹) := by
          rw [← map_mul]; congr 1; field_simp
        -- Step 2: The square expands as (e + c*i)² = e² - c² + 2ec*i where c = b/(2e)
        set c := b * (2 * e)⁻¹
        -- v * v = (alg e + alg c * i) * (alg e + alg c * i)
        -- = alg(e²) + alg(e*c)*i + alg(c*e)*i + alg(c²)*i²
        -- = alg(e²) + 2*alg(e*c)*i - alg(c²)
        -- = (alg(e²) - alg(c²)) + 2*alg(e*c)*i
        have hexpand : (algebraMap R (Ri R) e + algebraMap R (Ri R) c * Ri.i R) *
            (algebraMap R (Ri R) e + algebraMap R (Ri R) c * Ri.i R) =
            (algebraMap R (Ri R) (e * e) - algebraMap R (Ri R) (c * c)) +
            algebraMap R (Ri R) (e * c + e * c) * Ri.i R := by
          simp only [← map_sub]
          have : Ri.i R * Ri.i R = -(1 : Ri R) := by rw [← sq]; exact hi2
          ring_nf
          rw [show Ri.i R ^ 2 = -(1 : Ri R) from hi2]
          simp only [map_mul, map_sub, map_pow, map_ofNat]; ring
        rw [hexpand]
        -- Step 3: Show the imaginary coefficient matches
        have him : e * c + e * c = b := by
          simp only [c]; field_simp; ring
        -- Step 4: Show the real part matches: e*e - c*c = a
        have hre : e * e - c * c = a := by
          simp only [c]
          -- e*e = (a+d')/2.  c*c = b²/(4e²) = b²/(2(a+d'))
          -- e*e - c*c = (a+d')/2 - b²/(2(a+d'))
          --   = ((a+d')² - b²) / (2(a+d'))
          -- d'² = a²+b² → (a+d')² = a²+2ad'+d'² = 2a²+2ad'+b²
          -- (a+d')² - b² = 2a²+2ad' = 2a(a+d')
          -- So e*e - c*c = 2a(a+d')/(2(a+d')) = a
          field_simp at he ⊢
          have h1 : d' = 2 * e ^ 2 - a := by linarith
          rw [h1] at hd'
          linear_combination -hd'
        simp only [← map_sub, him, hre]; ring

/-- The derivative of QPolynomial is the sum of products (Leibniz rule for linear factors). -/
private lemma derivative_QPolynomial_eq {L : Type*} [Field L] {p : ℕ} (x : Fin p → L) :
    (QPolynomial x).derivative = ∑ ij ∈ strictPairs p, ∏ kl ∈ (strictPairs p).erase ij,
      (Polynomial.X - Polynomial.C (gammaPoly x kl.1 kl.2)) := by
  simp only [QPolynomial]
  rw [Polynomial.derivative_prod_finset]
  congr 1; ext ij
  simp [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C]

/-- eval γ_{ij₀} (FPoly x) = ∏_{kl ≠ ij₀} (γ_{ij₀} - γ_{kl}) -/
private lemma F_eval_gamma {L : Type*} [Field L] {p : ℕ} (x : Fin p → L)
    (ij₀ : Fin p × Fin p) (hij₀ : ij₀ ∈ strictPairs p) :
    Polynomial.eval (gammaPoly x ij₀.1 ij₀.2) (FPoly x) =
    ∏ kl ∈ (strictPairs p).erase ij₀,
      (gammaPoly x ij₀.1 ij₀.2 - gammaPoly x kl.1 kl.2) := by
  have h := eval_lagrange_sum (strictPairs p) (fun _ => (1 : L[X]))
    (fun kl => gammaPoly x kl.1 kl.2) ij₀ hij₀
  simp only [Polynomial.C_1, one_mul] at h
  rw [← h]; congr 1
  exact derivative_QPolynomial_eq x

/-! ### Layer 1: Core induction

Every monic separable P ∈ R[X] of degree 2^m · n (n odd) has a root in R[i],
proven by strong induction on m. -/

/-- Base case: odd-degree polynomial over R has a root in R (hence in R[i]). -/
theorem odd_degree_has_root_Ri [IsRealClosed R]
    (P : R[X]) (hodd : Odd P.natDegree) :
    ∃ x : Ri R, Polynomial.eval₂ (algebraMap R (Ri R)) x P = 0 := by
  -- Real closed: odd degree → root in R
  obtain ⟨r, hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hodd
  exact ⟨algebraMap R (Ri R) r, by
    rw [← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply,
      show Polynomial.aeval r P = 0 from Polynomial.IsRoot.def.mp hr, map_zero]⟩

/-- Helper: extract roots of a monic separable splitting polynomial as a Fin-indexed
    injective function, with the product factorization. -/
private theorem exists_roots_fin {L : Type*} [Field L] (f : L[X]) (d : ℕ)
    (hsplit : f.Splits) (hmonic : f.Monic) (hsep : f.Separable)
    (hdeg : f.natDegree = d) :
    ∃ x : Fin d → L, Function.Injective x ∧
      f = ∏ j : Fin d, (X - C (x j)) := by
  subst hdeg
  set rl := f.roots.toList
  have hlen : rl.length = f.natDegree := by
    rw [Multiset.length_toList, hsplit.natDegree_eq_card_roots]
  have hnd : rl.Nodup := by
    rw [← Multiset.coe_nodup, Multiset.coe_toList]
    exact Polynomial.nodup_roots hsep
  refine ⟨fun i => rl[i.val]'(by omega), ?_, ?_⟩
  · -- Injective: from Nodup
    intro i j hij
    simp only at hij
    have hi' : i.val < rl.length := by omega
    have hj' : j.val < rl.length := by omega
    have : (⟨i.val, hi'⟩ : Fin rl.length) = ⟨j.val, hj'⟩ :=
      hnd.get_inj_iff.mp (by simpa [List.get_eq_getElem] using hij)
    exact Fin.ext (Fin.mk.inj this)
  · -- Product: multiset product → list product → Fin product
    have hprod := hsplit.eq_prod_roots_of_monic hmonic
    conv_lhs => rw [hprod]
    rw [← Multiset.prod_map_toList, ← List.prod_ofFn]
    congr 1
    apply List.ext_getElem
      (by simp [Multiset.length_toList, hsplit.natDegree_eq_card_roots])
      (fun i h1 h2 => by simp [List.getElem_map]; rfl)

/-- The core induction: every monic separable P ∈ R[X] of degree 2^m · n (n odd)
    has a root in Ri R, by induction on m.

    When m = 0: odd degree → root in R ⊆ R[i].
    When m ≥ 1: construct Q(z,·) of degree p(p-1)/2 where p = deg P.
    Since p = 2^m · n, we have p(p-1)/2 = 2^{m-1} · n' (n' odd).
    By IH, Q(z,·) has a root γ ∈ R[i]. Then recover roots of P from γ
    via a quadratic over R[i] using the square root from sqrt_exists_Ri. -/
theorem core_induction [IsRealClosed R]
    (m : ℕ) (n : ℕ) (hn : Odd n) (P : R[X])
    (hmonic : P.Monic) (hdeg : P.natDegree = 2 ^ m * n)
    (hsep : P.Separable) :
    ∃ x : Ri R, Polynomial.aeval x P = 0 := by
  induction m generalizing n P with
  | zero =>
    simp at hdeg
    have hodd : Odd P.natDegree := by rw [hdeg]; exact hn
    obtain ⟨x, hx⟩ := odd_degree_has_root_Ri P hodd
    exact ⟨x, by rwa [Polynomial.aeval_def]⟩
  | succ m' ih =>
    -- ---- Setup: splitting field where P and X²+1 both split ----
    set p := P.natDegree with hp_def
    have hn_pos : 0 < n := Nat.pos_of_ne_zero (Odd.pos hn).ne'
    have hp_pos : 0 < p := by rw [hdeg]; positivity
    -- ---- Step 1: Splitting field of P * (X² + 1) ----
    -- L = splitting field where both P and X²+1 split
    let L := (P * (X ^ 2 + 1 : R[X])).SplittingField
    have hPQ_splits : ((P * (X ^ 2 + 1)).map (algebraMap R L)).Splits :=
      Polynomial.SplittingField.splits (P * (X ^ 2 + 1))
    have hP_ne : P.map (algebraMap R L) ≠ 0 := Polynomial.map_ne_zero hmonic.ne_zero
    have hXi_ne : (X ^ 2 + 1 : R[X]).map (algebraMap R L) ≠ 0 :=
      Polynomial.map_ne_zero (monic_X_pow_add_C 1 (by norm_num : (2 : ℕ) ≠ 0)).ne_zero
    rw [Polynomial.map_mul] at hPQ_splits
    have ⟨hP_splits, hXi_splits⟩ :=
      (Polynomial.splits_mul_iff hP_ne hXi_ne).mp hPQ_splits
    -- ---- Step 2: Root of X²+1 in L, embedding φ : Ri R → L ----
    have hXi_deg : ((X ^ 2 + 1 : R[X]).map (algebraMap R L)).degree ≠ 0 := by
      simp only [Polynomial.degree_map_eq_of_injective (algebraMap R L).injective]
      have h1 : (X ^ 2 + 1 : R[X]) ≠ 0 := by
        have : (X ^ 2 + 1 : R[X]).natDegree = 2 := by compute_degree!
        exact fun h => by simp [h] at this
      rw [Polynomial.degree_eq_natDegree h1,
          show Polynomial.natDegree (X ^ 2 + 1 : R[X]) = 2 from by compute_degree!]
      norm_num
    obtain ⟨ι, hι_root⟩ := hXi_splits.exists_eval_eq_zero hXi_deg
    have hι : Polynomial.eval₂ (algebraMap R L) ι (X ^ 2 + 1) = 0 := by
      rwa [Polynomial.eval_map] at hι_root
    let φ : Ri R →+* L := AdjoinRoot.lift (algebraMap R L) ι hι
    have hφ_inj : Function.Injective φ := RingHom.injective _
    have hφ_alg : ∀ r : R, φ (algebraMap R (Ri R) r) = algebraMap R L r :=
      fun r => by rw [AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.lift_of hι
    -- ---- Step 3: Extract roots of P as Fin p → L ----
    have hPL_monic : (P.map (algebraMap R L)).Monic := hmonic.map _
    have hPL_sep : (P.map (algebraMap R L)).Separable := hsep.map
    have hPL_deg : (P.map (algebraMap R L)).natDegree = p :=
      (hmonic.natDegree_map (algebraMap R L)).trans rfl
    obtain ⟨x, hx_inj, hx⟩ := exists_roots_fin (P.map (algebraMap R L)) p
      hP_splits hPL_monic hPL_sep hPL_deg
    -- ---- Step 4: Choose z₀ with D(z₀) ≠ 0 ----
    obtain ⟨z₀, hz₀⟩ := exists_discPoly_eval_ne_zero (R := R) x hx_inj
    -- ---- Step 5: Pull back Q(z₀, ·) to R[X] ----
    -- Each coeff of QPolynomial x is in R[Z] (as a polynomial in Z)
    -- Evaluating at algebraMap R L z₀ gives an element of L in range of algebraMap
    -- So Q(z₀, ·) ∈ R[Y]
    have hQ_in_R : ∃ Q_R : R[X],
        Q_R.map (algebraMap R L) =
          (QPolynomial x).map (Polynomial.evalRingHom (algebraMap R L z₀)) := by
      rw [poly_in_image_iff_coeffs_in_range]
      intro k
      rw [Polynomial.coeff_map]
      obtain ⟨q_k, hq_k⟩ := Q_coeff_mem_R P x hx k
      exact ⟨Polynomial.eval z₀ q_k, by
        rw [← hq_k]; simp [Polynomial.eval_map]⟩
    obtain ⟨Q_R, hQ_R⟩ := hQ_in_R
    -- ---- Step 6: Properties of Q_R ----
    -- Q_R is monic
    have hQ_R_monic : Q_R.Monic := by
      have : (Q_R.map (algebraMap R L)).Monic := by
        rw [hQ_R]; exact (monic_QPolynomial x).map (Polynomial.evalRingHom _)
      exact Polynomial.monic_of_injective (algebraMap R L).injective this
    -- natDegree Q_R
    have hQ_R_ndeg : Q_R.natDegree = (strictPairs p).card := by
      have h1 := hQ_R_monic.natDegree_map (algebraMap R L)
      rw [hQ_R] at h1
      rw [← h1]
      rw [(monic_QPolynomial x).natDegree_map, natDegree_QPolynomial]
    -- Degree decomposition: p*(p-1)/2 = 2^{m'} * n' with n' odd
    have hcard : (strictPairs p).card = p * (p - 1) / 2 := card_strictPairs p
    obtain ⟨n', hn'_odd, hdeg_eq⟩ := half_degree_odd_factor
      (show 1 ≤ m' + 1 from by omega) hn hn_pos
    have hQ_R_deg : Q_R.natDegree = 2 ^ m' * n' := by
      rw [hQ_R_ndeg, hcard, hdeg]; exact hdeg_eq
    -- Q_R is separable
    have hQ_R_sep : Q_R.Separable := by
      rw [← Polynomial.separable_map (algebraMap R L)]
      rw [hQ_R]
      refine separable_Q_eval x ((algebraMap R L) z₀) ?_
      intro a ha b hb heq
      by_contra hab
      apply hz₀
      simp only [discPoly, Polynomial.eval_prod]
      have hmem : (a, b) ∈ (strictPairs p).offDiag := by
        rw [Finset.mem_offDiag]; exact ⟨ha, hb, hab⟩
      refine Finset.prod_eq_zero hmem ?_
      simp only [Polynomial.eval_sub, heq, sub_self]
    -- ---- Step 7: Apply IH to Q_R ----
    obtain ⟨γ, hγ⟩ := ih n' hn'_odd Q_R hQ_R_monic hQ_R_deg hQ_R_sep
    -- ---- Step 8: Transfer γ to L, find which root of Q it maps to ----
    -- φ(γ) is a root of Q(z₀, ·) in L
    have hcomp : φ.comp (algebraMap R (Ri R)) = algebraMap R L := by
      ext r; exact hφ_alg r
    have hγ_L : Polynomial.eval (φ γ) ((QPolynomial x).map
        (Polynomial.evalRingHom (algebraMap R L z₀))) = 0 := by
      have h1 : Polynomial.eval (φ γ) (Q_R.map (algebraMap R L)) = 0 := by
        have : φ (Polynomial.aeval γ Q_R) = 0 := by rw [hγ, map_zero]
        rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp] at this
        rwa [Polynomial.eval_map]
      rwa [hQ_R] at h1
    -- φ(γ) equals some γ_{ij₀}(z₀) for ij₀ ∈ strictPairs p
    -- Since Q(z₀, ·) = ∏ ij, (Y - γ_{ij}(z₀)) and all roots are distinct
    set z₀' := (algebraMap R L) z₀ with hz₀'_def
    obtain ⟨ij₀, hij₀, hφγ_eq⟩ : ∃ ij₀ ∈ strictPairs p, φ γ = Polynomial.eval z₀' (gammaPoly x ij₀.1 ij₀.2) := by
      simp only [QPolynomial, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C, Polynomial.coe_evalRingHom] at hγ_L
      rw [Polynomial.eval_prod] at hγ_L
      obtain ⟨ij₀, hij₀, heq⟩ := (Finset.prod_eq_zero_iff (M₀ := L)).mp hγ_L
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heq
      exact ⟨ij₀, hij₀, sub_eq_zero.mp heq⟩
    have interchange : ∀ (Q' : (L[X])[X]) (f' : L[X]),
        Polynomial.eval (Polynomial.eval z₀' f') (Q'.map (Polynomial.evalRingHom z₀')) =
        Polynomial.eval z₀' (Polynomial.eval f' Q') := by
      intro Q' f'
      induction Q' using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.map_add, Polynomial.eval_add, hp, hq]
      | monomial n a =>
        simp only [Polynomial.map_monomial, Polynomial.eval_monomial, Polynomial.coe_evalRingHom]
        rw [← Polynomial.eval_pow, ← Polynomial.eval_mul]
    have eval_pullback : ∀ (q_k : R[X]),
        (algebraMap R L) (Polynomial.eval z₀ q_k) = Polynomial.eval₂ (algebraMap R L) z₀' q_k := by
      intro q_k; rw [hz₀'_def, ← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]; rfl
    have coeff_pullback : ∀ (Poly_L : (L[X])[X]),
        (∀ k, ∃ q : R[X], q.map (algebraMap R L) = Poly_L.coeff k) →
        ∃ Poly_R : R[X], Poly_R.map (algebraMap R L) = Poly_L.map (Polynomial.evalRingHom z₀') := by
      intro Poly_L hcoeffs
      rw [poly_in_image_iff_coeffs_in_range]; intro k; rw [Polynomial.coeff_map]
      simp only [Polynomial.coe_evalRingHom]
      obtain ⟨q_k, hq_k⟩ := hcoeffs k
      exact ⟨Polynomial.eval z₀ q_k, by rw [eval_pullback, ← Polynomial.eval_map, hq_k]⟩
    obtain ⟨G_R, hG_R⟩ := coeff_pullback _ (G_coeff_mem_R P x hx)
    obtain ⟨H_R, hH_R⟩ := coeff_pullback _ (H_coeff_mem_R P x hx)
    obtain ⟨F_R, hF_R⟩ := coeff_pullback _ (F_coeff_mem_R P x hx)
    have φ_aeval : ∀ (w : Ri R) (f : R[X]),
        φ (Polynomial.aeval w f) = Polynomial.eval (φ w) (f.map (algebraMap R L)) := by
      intro w f; rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, Polynomial.eval_map]
    set γ₀ := Polynomial.eval z₀' (gammaPoly x ij₀.1 ij₀.2) with hγ₀_def
    have hφG : φ (Polynomial.aeval γ G_R) = (x ij₀.1 + x ij₀.2) * φ (Polynomial.aeval γ F_R) := by
      rw [φ_aeval γ G_R, hG_R, hφγ_eq, interchange, G_eval_gamma x ij₀ hij₀]
      rw [φ_aeval γ F_R, hF_R, hφγ_eq, interchange, F_eval_gamma x ij₀ hij₀]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
    have hφH : φ (Polynomial.aeval γ H_R) = (x ij₀.1 * x ij₀.2) * φ (Polynomial.aeval γ F_R) := by
      rw [φ_aeval γ H_R, hH_R, hφγ_eq, interchange, H_eval_gamma x ij₀ hij₀]
      rw [φ_aeval γ F_R, hF_R, hφγ_eq, interchange, F_eval_gamma x ij₀ hij₀]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
    have hF_ne : Polynomial.aeval γ F_R ≠ 0 := by
      intro hF0
      have h0 : φ (Polynomial.aeval γ F_R) = 0 := by rw [hF0, map_zero]
      rw [φ_aeval, hF_R, hφγ_eq, interchange, F_eval_gamma x ij₀ hij₀] at h0
      rw [Polynomial.eval_prod] at h0
      obtain ⟨kl, hkl_mem, hkl_eq⟩ := (Finset.prod_eq_zero_iff (M₀ := L)).mp h0
      rw [Polynomial.eval_sub] at hkl_eq
      have hkl_sp := Finset.mem_erase.mp hkl_mem
      apply hz₀; simp only [discPoly, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (i := (ij₀, kl))
        (by rw [Finset.mem_offDiag]; exact ⟨hij₀, hkl_sp.2, hkl_sp.1.symm⟩)
        (by simp only [Polynomial.eval_sub, hkl_eq])
    have hφF_ne : φ (Polynomial.aeval γ F_R) ≠ 0 := (map_ne_zero_iff φ hφ_inj).mpr hF_ne
    set s := Polynomial.aeval γ G_R * (Polynomial.aeval γ F_R)⁻¹
    set t := Polynomial.aeval γ H_R * (Polynomial.aeval γ F_R)⁻¹
    have hφs : φ s = x ij₀.1 + x ij₀.2 := by
      simp only [s, map_mul, map_inv₀, hφG, mul_assoc, mul_inv_cancel₀ hφF_ne, mul_one]
    have hφt : φ t = x ij₀.1 * x ij₀.2 := by
      simp only [t, map_mul, map_inv₀, hφH, mul_assoc, mul_inv_cancel₀ hφF_ne, mul_one]
    obtain ⟨d, hd⟩ := sqrt_exists_Ri (R := R) (s ^ 2 - 4 * t)
    have h2_ne : (2 : Ri R) ≠ 0 := by
      intro h2; apply (two_ne_zero : (2 : R) ≠ 0)
      exact (algebraMap R (Ri R)).injective
        (show (algebraMap R (Ri R)) 2 = (algebraMap R (Ri R)) 0 by rw [map_zero]; exact_mod_cast h2)
    have hφ_2 : φ 2 = (2 : L) := by
      show φ ((algebraMap R (Ri R)) 2) = (algebraMap R L) 2; rw [hφ_alg]
    have hφ_4 : φ 4 = (4 : L) := by
      show φ ((algebraMap R (Ri R)) 4) = (algebraMap R L) 4; rw [hφ_alg]
    set y := (s + d) * (2 : Ri R)⁻¹
    have hφd_sq : φ d * φ d = (x ij₀.1 - x ij₀.2) ^ 2 := by
      have := congr_arg φ hd
      rw [map_mul, map_sub, map_mul, map_pow, hφs, hφt, hφ_4] at this
      rw [this]; ring
    have hφy : φ y = (x ij₀.1 + x ij₀.2 + φ d) * (2 : L)⁻¹ := by
      simp only [y, map_mul, map_add, hφs, map_inv₀, hφ_2]
    have hφy_root : (φ y - x ij₀.1) * (φ y - x ij₀.2) = 0 := by
      rw [hφy]
      have hlhs : ((x ij₀.1 + x ij₀.2 + φ d) * (2 : L)⁻¹ - x ij₀.1) *
                  ((x ij₀.1 + x ij₀.2 + φ d) * (2 : L)⁻¹ - x ij₀.2) =
                  (φ d * φ d - (x ij₀.1 - x ij₀.2) ^ 2) * ((2 : L)⁻¹) ^ 2 := by ring
      rw [hlhs, hφd_sq, sub_self, zero_mul]
    have hP_root : ∀ j : Fin p, Polynomial.eval (x j) (P.map (algebraMap R L)) = 0 := by
      intro j; rw [hx, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j)
        (by simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C])
    have root_from_φ : ∀ (w : Ri R) (j : Fin p), φ w = x j → Polynomial.aeval w P = 0 := by
      intro w j hwj
      apply hφ_inj
      rw [φ_aeval, Polynomial.eval_map, map_zero, (Polynomial.eval_map _ _).symm, hwj]
      exact hP_root j
    rcases mul_eq_zero.mp hφy_root with h | h
    · exact ⟨y, root_from_φ y ij₀.1 (sub_eq_zero.mp h)⟩
    · exact ⟨y, root_from_φ y ij₀.2 (sub_eq_zero.mp h)⟩

/-! ### Layer 2: Reductions -/

/-- Every monic polynomial over R has a root in R[i].
    If P is separable, decompose degree and apply core_induction.
    If not, extract a monic irreducible factor (which is separable in char 0)
    and apply core_induction to it; any root of the factor is a root of P. -/
theorem monic_has_root_Ri [IsRealClosed R]
    (P : R[X]) (hdeg : P.natDegree ≠ 0) :
    ∃ x : Ri R, Polynomial.aeval x P = 0 := by
  -- Extract a monic irreducible factor of P
  have hnu : ¬ IsUnit P := fun h => hdeg (Polynomial.natDegree_eq_zero_of_isUnit h)
  obtain ⟨q, hq_monic, hq_irr, hq_dvd⟩ := Polynomial.exists_monic_irreducible_factor P hnu
  -- q is separable (characteristic zero, irreducible)
  have hq_sep : q.Separable := hq_irr.separable
  -- q has positive degree (irreducible → not unit → degree ≥ 1)
  have hq_deg : q.natDegree ≠ 0 :=
    Nat.pos_of_ne_zero (hq_monic.natDegree_pos_of_not_isUnit hq_irr.1).ne' |>.ne'
  -- Decompose degree of q as 2^m * n with n odd
  obtain ⟨m, n', hn', hd⟩ := Nat.exists_eq_two_pow_mul_odd hq_deg
  -- Apply core_induction to q
  obtain ⟨x, hx⟩ := core_induction m n' hn' q hq_monic hd hq_sep
  -- A root of q is a root of P (since q | P)
  exact ⟨x, by obtain ⟨r, hr⟩ := hq_dvd; rw [hr, map_mul, hx, zero_mul]⟩

/-- Every monic irreducible polynomial over R[i] has a root in R[i].
    Key idea: P · P̄ ∈ R[X] (product with conjugate has real coefficients).
    A root of P·P̄ in R[i] is a root of either P or P̄, and roots of P̄
    are conjugates of roots of P. -/
theorem Ri_poly_has_root [IsRealClosed R]
    (P : (Ri R)[X]) (hmonic : P.Monic) (hirr : Irreducible P) :
    ∃ x : Ri R, Polynomial.eval x P = 0 := by
  -- Pbar = conjugate of P
  set Pbar := Polynomial.map (Ri.conj R : Ri R →+* Ri R) P with hPbar_def
  -- P * Pbar is invariant under conjugation, so it lifts to R[X]
  have hPP_real : ∃ Q : R[X], Polynomial.map (algebraMap R (Ri R)) Q = P * Pbar := by
    rw [← Polynomial.mem_lifts]
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have := conj_coeff_mul_conjPoly P n
    simp only [conjPoly] at this
    exact Ri.conj_fixed_mem_range _ this
  obtain ⟨Q, hQ⟩ := hPP_real
  -- Q is monic with positive degree
  have hQ_deg : Q.natDegree ≠ 0 := by
    intro h0
    -- If natDegree Q = 0, then map Q has natDegree 0 too (algebraMap injective)
    have : (P * Pbar).natDegree = 0 := by
      rw [← hQ, Polynomial.natDegree_map_eq_of_injective (algebraMap R (Ri R)).injective]; exact h0
    -- But deg(P * Pbar) = deg P + deg Pbar, and deg P ≥ 1 (irreducible → not unit)
    have hP_deg : P.natDegree ≥ 1 := Irreducible.natDegree_pos hirr
    have hPbar_deg : Pbar.natDegree = P.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (Ri.conj_injective R) P
    have hPbar_monic : Pbar.Monic := Polynomial.Monic.map _ hmonic
    have hdeg_mul : (P * Pbar).natDegree = P.natDegree + Pbar.natDegree :=
      Polynomial.Monic.natDegree_mul hmonic hPbar_monic
    omega
  -- By monic_has_root_Ri, Q has a root x in R[i]
  obtain ⟨x, hx⟩ := monic_has_root_Ri Q hQ_deg
  -- aeval x Q = 0 means eval₂ (algebraMap ...) x Q = 0
  rw [Polynomial.aeval_def] at hx
  -- So eval x (P * Pbar) = 0
  have hPP : Polynomial.eval x (P * Pbar) = 0 := by
    rw [← hQ, Polynomial.eval_map]; exact hx
  rw [Polynomial.eval_mul] at hPP
  -- Either eval x P = 0 or eval x Pbar = 0
  rcases mul_eq_zero.mp hPP with h | h
  · exact ⟨x, h⟩
  · -- eval x Pbar = 0 means eval₂ conj x P = 0
    -- By eval₂_hom at (conj x): eval₂ conj (conj(conj x)) P = conj(eval (conj x) P)
    -- Since conj² = id: conj(conj x) = x, so eval₂ conj x P = conj(eval (conj x) P)
    -- Therefore conj(eval (conj x) P) = 0, so eval (conj x) P = 0
    rw [Polynomial.eval_map] at h
    have h_eval : (Ri.conj R : Ri R →+* Ri R) (Polynomial.eval ((Ri.conj R) x) P) = 0 := by
      have hinv : (Ri.conj R : Ri R →+* Ri R) ((Ri.conj R) x) = x := Ri.conj_conj R x
      rw [← Polynomial.eval₂_hom, hinv]; exact h
    have hinj : Function.Injective (Ri.conj R : Ri R →+* Ri R) := Ri.conj_injective R
    exact ⟨(Ri.conj R) x, hinj (by rw [h_eval, map_zero])⟩

/-- Theorem 2.11 (a) ⇒ (b): If R is real closed, then R[i] is algebraically closed. -/
theorem isAlgClosed_Ri [IsRealClosed R] : IsAlgClosed (Ri R) :=
  IsAlgClosed.of_exists_root _ Ri_poly_has_root

end Azurite.BPR.Theorem2_11
