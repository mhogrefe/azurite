import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMatrixMvMul

/-!
# BPR §8.1: Degree and coefficient bitsize of a product of several matrices
            over `ℤ[Y₁, …, Y_k]`

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

An unnumbered BPR fact accompanying Algorithm 8.14: with `A = ℤ[Y]`,
`Y = Y₁, …, Y_k`, if every entry of each matrix in a non-empty list
`Ms = [M_1, …, M_m]` of `n × n` matrices over `MvPolynomial (Fin k) ℤ`
has total degree (in `Y`) bounded by `p` and coefficient bitsize bounded
by `τ`, then every entry of the product `M_1 ⋯ M_m` has:

* total degree bounded by `m · p`;
* coefficient bitsize bounded by
  `m · τ + k · m · Nat.size (m · p + 1) + m · Nat.size (Fintype.card ν)`.

BPR's stated bound (with per-matrix `p_l, τ_l`) is tighter on the
polynomial term — `k · (Nat.size(p_1 + 1) + ⋯ + Nat.size(p_m + 1))`
versus our `k · m · Nat.size(m · p + 1)` — and is obtainable by a
"flat expansion" / `k`-induction proof using `MvPolynomial.finSuccEquiv`.
The iterated proof below applies the binary matrix-product bound
(`Matrix.bitsize_coeff_mvMul_le`) at each step with uniform bounds,
which is straightforward but produces a polynomial term that grows
multiplicatively with the number of matrices.
-/

namespace Azurite.BPR

/-- Total degree of a non-empty list product of matrices over a
    multivariate polynomial ring is bounded by `Ms.length * p` when every
    entry of every matrix has total degree at most `p`. -/
theorem Matrix.totalDegree_mvList_prod_le {k : ℕ} {ν : Type _} [Fintype ν] [DecidableEq ν]
    {Ms : List (Matrix ν ν (MvPolynomial (Fin k) ℤ))} {p : ℕ}
    (h_ne : Ms ≠ [])
    (hM_deg : ∀ M ∈ Ms, ∀ i j, (M i j).totalDegree ≤ p) :
    ∀ i j, ((Ms.prod) i j).totalDegree ≤ Ms.length * p := by
  induction Ms with
  | nil => exact absurd rfl h_ne
  | cons M rest ih =>
    intro i j
    have hM_head : ∀ i' j', (M i' j').totalDegree ≤ p :=
      fun i' j' => hM_deg M List.mem_cons_self i' j'
    have hM_rest : ∀ M' ∈ rest, ∀ i' j', (M' i' j').totalDegree ≤ p :=
      fun M' hM' i' j' => hM_deg M' (List.mem_cons_of_mem _ hM') i' j'
    by_cases h_rest : rest = []
    · subst h_rest
      rw [List.prod_cons, List.prod_nil, mul_one]
      have := hM_head i j
      have h1 : (1 : ℕ) * p = p := by ring
      have h2 : ([M] : List (Matrix ν ν (MvPolynomial (Fin k) ℤ))).length = 1 := rfl
      rw [h2]; omega
    · have ih_rest := ih h_rest hM_rest
      rw [List.prod_cons]
      have h_mul : ((M * rest.prod) i j) = ∑ s, M i s * rest.prod s j :=
        Matrix.mul_apply
      rw [h_mul]
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
      apply Finset.sup_le
      intro s _
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have h1 : (M i s).totalDegree ≤ p := hM_head i s
      have h2 : (rest.prod s j).totalDegree ≤ rest.length * p := ih_rest s j
      show (M i s).totalDegree + (rest.prod s j).totalDegree ≤ (rest.length + 1) * p
      have : p + rest.length * p = (rest.length + 1) * p := by ring
      omega

/-- **BPR §8.1 (unnumbered lemma).** Multiplying a non-empty list of `m`
    matrices over `MvPolynomial (Fin k) ℤ`, all of whose entries have total
    degree bounded by `p` and coefficient bitsizes bounded by `τ`, produces
    a matrix whose entries have coefficient bitsizes bounded by
    `m · τ + k · m · Nat.size (m · p + 1) + m · Nat.size (Fintype.card ν)`. -/
theorem Matrix.bitsize_coeff_mvList_prod_le {k : ℕ} {ν : Type _}
    [Fintype ν] [DecidableEq ν]
    {Ms : List (Matrix ν ν (MvPolynomial (Fin k) ℤ))} (h_ne : Ms ≠ [])
    {τ p : ℕ}
    (hM_size : ∀ M ∈ Ms, ∀ i j r, ((M i j).coeff r).natAbs.size ≤ τ)
    (hM_deg : ∀ M ∈ Ms, ∀ i j, (M i j).totalDegree ≤ p) :
    ∀ i j r, (((Ms.prod) i j).coeff r).natAbs.size ≤
      Ms.length * τ + k * Ms.length * Nat.size (Ms.length * p + 1) +
        Ms.length * Nat.size (Fintype.card ν) := by
  induction Ms with
  | nil => exact absurd rfl h_ne
  | cons M rest ih =>
    intro i j r
    have hM_head_size : ∀ i' j' r', ((M i' j').coeff r').natAbs.size ≤ τ :=
      fun i' j' r' => hM_size M List.mem_cons_self i' j' r'
    have hM_head_deg : ∀ i' j', (M i' j').totalDegree ≤ p :=
      fun i' j' => hM_deg M List.mem_cons_self i' j'
    have hM_rest_size : ∀ M' ∈ rest, ∀ i' j' r',
        ((M' i' j').coeff r').natAbs.size ≤ τ :=
      fun M' hM' i' j' r' => hM_size M' (List.mem_cons_of_mem _ hM') i' j' r'
    have hM_rest_deg : ∀ M' ∈ rest, ∀ i' j', (M' i' j').totalDegree ≤ p :=
      fun M' hM' i' j' => hM_deg M' (List.mem_cons_of_mem _ hM') i' j'
    by_cases h_rest : rest = []
    · subst h_rest
      rw [List.prod_cons, List.prod_nil, mul_one]
      have h_bound := hM_head_size i j r
      have h_len : ([M] : List (Matrix ν ν (MvPolynomial (Fin k) ℤ))).length = 1 := rfl
      rw [h_len]
      omega
    · have ih_rest := ih h_rest hM_rest_size hM_rest_deg
      have h_deg_rest := Matrix.totalDegree_mvList_prod_le h_rest hM_rest_deg
      set τ_rest := rest.length * τ + k * rest.length * Nat.size (rest.length * p + 1) +
        rest.length * Nat.size (Fintype.card ν) with hτ_rest_def
      have hM_size_rest_prod : ∀ i' j' r',
          ((rest.prod i' j').coeff r').natAbs.size ≤ τ_rest := ih_rest
      have hM_deg_rest_prod :
          ∀ i' j', (rest.prod i' j').totalDegree ≤ rest.length * p := h_deg_rest
      rw [List.prod_cons]
      have h_bound := Matrix.bitsize_coeff_mvMul_le
        (M := M) (N := rest.prod) (τ := τ) (σ := τ_rest)
        (p := p) (q := rest.length * p)
        hM_head_size hM_size_rest_prod hM_head_deg hM_deg_rest_prod i j r
      refine h_bound.trans ?_
      rw [show (M :: rest).length = rest.length + 1 from rfl]
      rw [hτ_rest_def]
      -- LHS: τ + (rest.length * τ + k · rest.length · size(rest.length · p + 1) +
      --      rest.length · size(n)) + k · size(p + rest.length · p) + size(n)
      -- RHS: (rest.length + 1) · τ + k · (rest.length + 1) · size((rest.length + 1) · p + 1)
      --      + (rest.length + 1) · size(n)
      set n_size := Nat.size (Fintype.card ν)
      set s_rest := Nat.size (rest.length * p + 1)
      set s_step := Nat.size (p + rest.length * p)
      set s_full := Nat.size ((rest.length + 1) * p + 1)
      -- Key inequalities: s_rest ≤ s_full and s_step ≤ s_full.
      have h_s_rest : s_rest ≤ s_full := by
        apply Nat.size_le_size
        have : rest.length * p ≤ (rest.length + 1) * p := Nat.mul_le_mul_right _ (Nat.le_succ _)
        omega
      have h_s_step : s_step ≤ s_full := by
        apply Nat.size_le_size
        have h : p + rest.length * p = (rest.length + 1) * p := by ring
        omega
      have h_k1 : k * rest.length * s_rest ≤ k * rest.length * s_full :=
        Nat.mul_le_mul_left _ h_s_rest
      have h_k2 : k * s_step ≤ k * s_full := Nat.mul_le_mul_left _ h_s_step
      -- Combine. We're left with:
      --   τ + rest.length * τ + (k * rest.length * s_rest) + rest.length * n_size +
      --     k * s_step + n_size ≤
      --   (rest.length + 1) * τ + k * (rest.length + 1) * s_full +
      --     (rest.length + 1) * n_size.
      have h_full :
          τ + rest.length * τ + (k * rest.length * s_rest) + rest.length * n_size +
            k * s_step + n_size ≤
          (rest.length + 1) * τ + k * (rest.length + 1) * s_full +
            (rest.length + 1) * n_size := by
        have e1 : (rest.length + 1) * τ = rest.length * τ + τ := by ring
        have e2 : k * (rest.length + 1) * s_full = k * rest.length * s_full + k * s_full := by ring
        have e3 : (rest.length + 1) * n_size = rest.length * n_size + n_size := by ring
        omega
      -- The goal is exactly h_full after a few rewrites.
      linarith [h_full]

end Azurite.BPR
