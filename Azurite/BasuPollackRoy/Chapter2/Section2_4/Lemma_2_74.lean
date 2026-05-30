import Azurite.BasuPollackRoy.Chapter2.Section2_4.Corollary_2_73
import Azurite.BasuPollackRoy.Chapter2.Section2_4.Exercise_2_13

/-!
# BPR Lemma 2.74

Let `Z = Zer(P, R)` be finite and `σ` a sign condition on `𝒬`. Whether or
not `Reali(σ, Z) = ∅` is determined by the degrees of the polynomials in
the signed pseudo-remainder sequences `SRemS(P, P'𝒬^α)` and the signs of
their leading coefficients, for all `α ∈ A = {0,1,2}^𝒬`.

## Formalization

For each `α`, the degrees and leading-coefficient signs determine the
sign-variation counts at `±∞`, whose difference is `TaQ(𝒬^α, P)`
(Theorem 2.61, `theorem_2_61`). The remaining algebra is fully assembled
here:

* `signMatrixQ_mulVec_card` — over `ℚ`, `Mₛ · c(Σ, Z) = TaQ(𝒬^A, P)`
  (the `Fin (3^s)`-indexed, rational form of Corollary 2.73; derived from
  the index-free `tarskiQuery_familyPow_eq_sum`, `signMatrix_toFn_eq_pow`,
  and the bijection `signFn`).
* `card_eq_inv_mulVec` — inverting `Mₛ` (Exercise 2.13, `signMatrix_isUnit`)
  gives `c(Σ, Z) = Mₛ⁻¹ · TaQ(𝒬^A, P)`, so each `c(σ, Z)` is a fixed
  `ℚ`-linear combination (the `σ`-row `r_σ` of `Mₛ⁻¹`) of the Tarski
  queries.
* `realizationOver_nonempty_iff_card_pos` — `Reali(σ, Z) ≠ ∅ ⟺ c(σ, Z) > 0`.

Combining these, `lemma_2_74` states
`Reali(σ, Z) ≠ ∅ ⟺ 0 < (Mₛ⁻¹ · TaQ(𝒬^A, P))_σ`: the emptiness of
`Reali(σ, Z)` is a function of the Tarski-query vector alone, hence of the
degrees and leading-coefficient signs.
-/

open scoped Polynomial Matrix

namespace Azurite.BPR

open Polynomial

namespace SignCondition

variable {ι : Type*} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype ι]

omit [IsStrictOrderedRing R] in
/-- **The emptiness criterion of BPR Lemma 2.74.** For `P ≠ 0`, the
realization `Reali(σ, Z)` is non-empty if and only if its cardinality
`c(σ, Z)` is positive. -/
theorem realizationOver_nonempty_iff_card_pos {σ : SignCondition ι} {P : R[X]}
    {Q : ι → R[X]} (hP : P ≠ 0) :
    (σ.realizationOver P Q).Nonempty ↔ 0 < (σ.realizationOverFinset P Q).card := by
  rw [Finset.card_pos]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_realizationOverFinset hP).mpr hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_realizationOverFinset hP).mp hx⟩

end SignCondition

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The lex enumeration `signFn s` packaged as an equivalence
`Fin (3^s) ≃ {0,1,-1}^{Fin s}`. -/
noncomputable def signEquiv (s : Nat) : Fin (3 ^ s) ≃ SignCondition (Fin s) :=
  Equiv.ofBijective (signFn s) ⟨signFn_injective s, signFn_surjective s⟩

/-- The `Fin (3^s)`-indexed form of `Mₛ · c(Σ, Z) = TaQ(𝒬^A, P)` over `ℤ`,
derived directly from the index-free `tarskiQuery_familyPow_eq_sum`,
`signMatrix_toFn_eq_pow`, and the bijection `signFn`. -/
theorem signMatrix_mulVec_card (s : Nat) (P : R[X]) (Q : Fin s → R[X]) :
    Matrix.mulVec (fun i j => ((signMatrix s).toFn i j : ℤ))
        (fun j => ((SignCondition.realizationOverFinset (signFn s j) P Q).card : ℤ))
      = fun i => tarskiQuery (familyPow Q (expFn s i)) P := by
  funext i
  rw [tarskiQuery_familyPow_eq_sum P Q (expFn s i) Finset.univ (fun x _ => Finset.mem_univ _)]
  rw [← Equiv.sum_comp (signEquiv s)
    (fun σ => (SignCondition.pow σ (expFn s i) : ℤ) * ((σ.realizationOverFinset P Q).card : ℤ))]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [signMatrix_toFn_eq_pow]
  rfl

/-- **Corollary 2.73 over `ℚ`, `Fin (3^s)`-indexed.**
`Mₛ · c(Σ, Z) = TaQ(𝒬^A, P)`, with `Mₛ = signMatrixQ s` the rational
matrix of signs. -/
theorem signMatrixQ_mulVec_card (s : Nat) (P : R[X]) (Q : Fin s → R[X]) :
    signMatrixQ s *ᵥ (fun j => ((SignCondition.realizationOverFinset (signFn s j) P Q).card : ℚ))
      = fun i => (tarskiQuery (familyPow Q (expFn s i)) P : ℚ) := by
  funext i
  have hZ := congrFun (signMatrix_mulVec_card s P Q) i
  simp only [Matrix.mulVec, dotProduct, signMatrixQ, Matrix.map_apply] at hZ ⊢
  have := congrArg (fun z : ℤ => (z : ℚ)) hZ
  push_cast at this ⊢
  convert this using 2

/-- **`c(Σ, Z) = Mₛ⁻¹ · TaQ(𝒬^A, P)`.** Each count `c(σ, Z)` is the
`σ`-row of `Mₛ⁻¹` dotted with the Tarski-query vector — the determination
at the heart of Lemma 2.74. -/
theorem card_eq_inv_mulVec (s : Nat) (P : R[X]) (Q : Fin s → R[X]) :
    (fun j => ((SignCondition.realizationOverFinset (signFn s j) P Q).card : ℚ))
      = (signMatrixQ s)⁻¹ *ᵥ (fun i => (tarskiQuery (familyPow Q (expFn s i)) P : ℚ)) := by
  have hdet : IsUnit (signMatrixQ s).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (signMatrix_isUnit s)
  rw [← signMatrixQ_mulVec_card s P Q, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
    Matrix.one_mulVec]

/-- **BPR Lemma 2.74.** Whether `Reali(σ, Z)` is empty is determined by the
Tarski-query vector `TaQ(𝒬^A, P)` (hence, via Theorem 2.61, by the degrees
and leading-coefficient signs of the signed pseudo-remainder sequences):
`Reali(σ, Z) ≠ ∅` if and only if the `σ`-component of `Mₛ⁻¹ · TaQ(𝒬^A, P)`
is positive. -/
theorem lemma_2_74 (s : Nat) (P : R[X]) (Q : Fin s → R[X]) (hP : P ≠ 0) (j : Fin (3 ^ s)) :
    (SignCondition.realizationOver (signFn s j) P Q).Nonempty
      ↔ 0 < ((signMatrixQ s)⁻¹ *ᵥ
          (fun i => (tarskiQuery (familyPow Q (expFn s i)) P : ℚ))) j := by
  rw [SignCondition.realizationOver_nonempty_iff_card_pos hP,
    ← congrFun (card_eq_inv_mulVec s P Q) j]
  exact_mod_cast Iff.rfl

end Azurite.BPR
