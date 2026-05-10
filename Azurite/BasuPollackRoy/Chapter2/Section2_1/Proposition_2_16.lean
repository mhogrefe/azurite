import Azurite.BasuPollackRoy.Chapter2.Section2_1.Lemma_2_12
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_13
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-! # BPR Section 2.1 — Proposition 2.16: Symmetric polynomials in roots stay in `K`

> Let `P ∈ K[X]` be monic of degree `k`, and let `x₁, …, xₖ` be its roots
> (with multiplicities) in a field extension `C ⊇ K`. If `Q(X₁, …, Xₖ) ∈
> K[X₁, …, Xₖ]` is symmetric, then `Q(x₁, …, xₖ) ∈ K`.

**Proof (BPR).** Let `eᵢ = Eᵢ(x₁, …, xₖ)`. By Lemma 2.12 the `eᵢ` are
(up to sign) coefficients of `P`, so each `eᵢ ∈ K`. By Proposition 2.13
`Q = R(E₁, …, Eₖ)` for some `R ∈ K[T₁, …, Tₖ]`, hence
`Q(x₁, …, xₖ) = R(e₁, …, eₖ) ∈ K`.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial in
/-- **BPR Proposition 2.16.** Let `P ∈ K[X]` be monic of degree `k`, and let
    `x₁,…,xₖ` be its roots (with multiplicities) in a field extension `C ⊇ K`.
    If `Q(X₁,…,Xₖ) ∈ K[X₁,…,Xₖ]` is symmetric, then `Q(x₁,…,xₖ) ∈ K`.

    **Proof (BPR):** Let `eᵢ = Eᵢ(x₁,…,xₖ)`. Since the `eᵢ` are (up to sign)
    coefficients of `P` by Lemma 2.12, we have `eᵢ ∈ K`. By Proposition 2.13,
    `Q = R(E₁,…,Eₖ)` for some `R ∈ K[T₁,…,Tₖ]`. Thus
    `Q(x₁,…,xₖ) = R(e₁,…,eₖ) ∈ K`. -/
theorem proposition_2_16 {K C : Type*} [Field K] [Field C] [Algebra K C]
    {k : ℕ} (P : Polynomial K)
    (x : Fin k → C)
    (hx : P.map (algebraMap K C) = ∏ j : Fin k, (Polynomial.X - Polynomial.C (x j)))
    (Q : MvPolynomial (Fin k) K) (hQ : Q.IsSymmetric) :
    MvPolynomial.aeval x Q ∈ Set.range (algebraMap K C) := by
  -- Step 1: By Prop 2.13, Q = R(E₁,...,Eₖ) for some R ∈ K[T₁,...,Tₖ]
  obtain ⟨R, hR⟩ := proposition_2_13 Q hQ
  -- Step 2: Rewrite Q and compose the evaluations:
  --   aeval x Q = aeval x (aeval(esymm) R) = aeval(aeval x ∘ esymm) R
  rw [← hR]
  show (MvPolynomial.aeval x).comp
    (MvPolynomial.bind₁ (fun i : Fin k => MvPolynomial.esymm (Fin k) K (↑i + 1))) R ∈ _
  rw [MvPolynomial.aeval_comp_bind₁]
  -- Step 3: Each eᵢ ∈ K by Vieta. Extract preimages:
  --   aeval x (esymm K (i+1)) = algebraMap K C (eᵢ) for some eᵢ : K
  suffices h : ∀ i : Fin k, ∃ e : K,
      algebraMap K C e = MvPolynomial.aeval x (MvPolynomial.esymm (Fin k) K (↑i + 1)) by
    -- Choose the K-valued preimages
    choose e he using h
    -- Step 4: aeval(algebraMap K C ∘ e) R = algebraMap K C (eval e R)
    refine ⟨MvPolynomial.eval e R, ?_⟩
    have heq : (fun i : Fin k => MvPolynomial.aeval x (MvPolynomial.esymm (Fin k) K (↑i + 1))) =
        fun i => algebraMap K C (e i) := funext (fun i => (he i).symm)
    rw [heq]
    simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp, Function.comp_def]
  -- Step 3 proof: use Vieta to show each esymm eval is a coefficient of P
  intro i
  -- aeval x (esymm K (i+1)) = (univ.val.map x).esymm (i+1)
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  -- By Vieta (lemma_2_12 over C): the RHS is (-1)^(i+1) * coeff of ∏(X-C(xⱼ))
  have h2_12 := @lemma_2_12 C _ k x (i.val + 1) (by omega)
  -- From hx, comparing coefficients: coeff of ∏(X-C(xⱼ)) = algebraMap K C (P.coeff _)
  have hcoeff : (∏ j : Fin k, (Polynomial.X - Polynomial.C (x j))).coeff (k - (i.val + 1)) =
      algebraMap K C (P.coeff (k - (i.val + 1))) := by
    rw [← hx, Polynomial.coeff_map]
  rw [hcoeff] at h2_12
  -- h2_12 : algebraMap(coeff) = (-1)^(i+1) * esymm
  -- So esymm = (-1)^(i+1) · algebraMap(coeff), since (-1)^n · (-1)^n = 1
  refine ⟨(-1) ^ (i.val + 1) * P.coeff (k - (i.val + 1)), ?_⟩
  rw [map_mul, map_pow, map_neg, map_one, h2_12, ← mul_assoc,
      ← pow_add, ← Nat.two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

end Azurite.BPR
