import Azurite.BasuPollackRoy.Chapter8.Section8_2.Proposition_8_14
import Azurite.BasuPollackRoy.Chapter8.Section8_1.Definition_8_4
import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMatrixMvListProd
import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMvMul
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic

/-!
# BPR §8.2.1 Proposition 8.15: degree and bitsize of a determinant

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.2.

**Proposition 8.15.** Let `M` be an `n × n` matrix with entries that are
polynomials in `Y₁, …, Y_k` of degrees `≤ d` and integer coefficients of bitsize
`≤ τ`. Then `det(M)`, as a polynomial in `Y₁, …, Y_k`, has degree `≤ d·n` and
coefficients of bitsize `≤ n (τ + bit(n) + k·bit(d+1))`.

The degree bound is Proposition 8.14. For the bitsize, by the Leibniz expansion
`det(M) = ∑_{σ ∈ Sₙ} sign(σ) ∏ᵢ m_{σ(i),i}`: each product of `n` entries has
coefficients of bitsize `≤ n(τ + k·bit(d))` by Remark 8.10
(`MvPolynomial.bitsize_coeff_list_prod_le_bpr_exact`), and summing the `n!` signed
terms adds `bit(n! − 1) ≤ n·bit(n)` (via `Int.size_finset_sum_le'`). With
`bit(d) ≤ bit(d+1)` this gives BPR's bound `n(τ + bit(n) + k·bit(d+1))`.

Here `bit(N) = Int.size N = N.natAbs.size` (BPR Definition 8.4).
-/

namespace Azurite.BPR

open MvPolynomial

variable {n k : ℕ}

/-- **BPR Proposition 8.15.** For an `n × n` matrix (`n ≥ 1`) of polynomials in
`Y₁, …, Y_k` of total degree `≤ d` with integer coefficients of bitsize `≤ τ`, the
determinant has total degree `≤ d·n` and coefficient bitsizes
`≤ n (τ + bit(n) + k·bit(d+1))`. -/
theorem proposition_8_15 (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin k) ℤ)) {d τ : ℕ}
    (hn : 0 < n)
    (hd : ∀ i j, (M i j).totalDegree ≤ d)
    (hτ : ∀ i j r, Int.size ((M i j).coeff r) ≤ τ) :
    M.det.totalDegree ≤ d * n ∧
    ∀ r, Int.size (M.det.coeff r) ≤ n * (τ + Nat.size n + k * Nat.size (d + 1)) := by
  refine ⟨proposition_8_14 M hd, fun r => ?_⟩
  -- Forall₂ over uniform `ofFn`/`replicate` lists.
  have mk_forall2 : ∀ {γ : Type} (c : γ) (Rel : MvPolynomial (Fin k) ℤ → γ → Prop)
      (g : Fin n → MvPolynomial (Fin k) ℤ),
      (∀ i, Rel (g i) c) → List.Forall₂ Rel (List.ofFn g) (List.replicate n c) := by
    intro γ c Rel g hg
    rw [List.forall₂_iff_get]
    refine ⟨by rw [List.length_ofFn, List.length_replicate], fun i h₁ h₂ => ?_⟩
    rw [List.get_ofFn, List.get_eq_getElem, List.getElem_replicate]
    exact hg _
  -- Per-permutation bound via Remark 8.10.
  have hper : ∀ σ : Equiv.Perm (Fin n),
      ((∏ i, M (σ i) i).coeff r).natAbs.size ≤ n * τ + k * (n * Nat.size d) := by
    intro σ
    have hne : List.ofFn (fun i => M (σ i) i) ≠ [] :=
      List.ne_nil_of_length_pos (by rw [List.length_ofFn]; exact hn)
    have hτ2 := mk_forall2 τ (fun P t => ∀ r, (P.coeff r).natAbs.size ≤ t)
      (fun i => M (σ i) i) (fun i r => hτ (σ i) i r)
    have hp2 := mk_forall2 d (fun P p => P.totalDegree ≤ p)
      (fun i => M (σ i) i) (fun i => hd (σ i) i)
    have hmain := MvPolynomial.bitsize_coeff_list_prod_le_bpr_exact k
      (List.ofFn (fun i => M (σ i) i)) (List.replicate n τ) (List.replicate n d) hne hτ2 hp2 r
    rw [List.prod_ofFn] at hmain
    rw [List.sum_replicate, List.map_replicate, List.sum_replicate] at hmain
    simpa [smul_eq_mul] using hmain
  -- Sum over `Sₙ` via the Leibniz expansion.
  show (M.det.coeff r).natAbs.size ≤ _
  rw [Matrix.det_apply, MvPolynomial.coeff_sum]
  refine (Int.size_finset_sum_le' (B := n * τ + k * (n * Nat.size d)) ?_).trans ?_
  · intro σ _
    -- The sign factor is `±1`, so it does not change the bitsize.
    have key : ((Equiv.Perm.sign σ • ∏ i, M (σ i) i).coeff r).natAbs
        = ((∏ i, M (σ i) i).coeff r).natAbs := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        simp [h, MvPolynomial.coeff_neg, Int.natAbs_neg]
    rw [key]
    exact hper σ
  · rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    have hfact : Nat.size (n.factorial - 1) ≤ n * Nat.size n := by
      apply Nat.size_le.mpr
      calc n.factorial - 1 < n.factorial := Nat.sub_lt (Nat.factorial_pos n) Nat.one_pos
        _ ≤ n ^ n := Nat.factorial_le_pow n
        _ ≤ 2 ^ (n * Nat.size n) := by
            calc n ^ n ≤ (2 ^ Nat.size n) ^ n :=
                  Nat.pow_le_pow_left (le_of_lt (Nat.lt_size_self n)) n
              _ = 2 ^ (n * Nat.size n) := by rw [← pow_mul, Nat.mul_comm]
    have hd1 : Nat.size d ≤ Nat.size (d + 1) := Nat.size_le_size (Nat.le_succ d)
    calc n * τ + k * (n * Nat.size d) + Nat.size (n.factorial - 1)
        ≤ n * τ + k * (n * Nat.size (d + 1)) + n * Nat.size n := by gcongr
      _ = n * (τ + Nat.size n + k * Nat.size (d + 1)) := by ring

end Azurite.BPR
