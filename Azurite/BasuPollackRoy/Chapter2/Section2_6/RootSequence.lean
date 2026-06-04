import Azurite.BasuPollackRoy.Chapter2.Section2_6.RecursionStepNeg

/-! # BPR §2.6 — the recursion state of the Puiseux root construction

To iterate the Puiseux construction we package the per-step invariant into a `RecState`: a
polynomial `Q` together with an odd `mult` such that `o(Q.coeff mult) = 0`, `o(Q.coeff i) > 0` for
`i < mult`, and `o(Q.coeff i) ≥ 0` for all `i` — exactly the order structure produced by Lemma
2.95. From `P` (odd degree, nonzero constant term) the first step bootstraps into a `RecState`
(`exists_initial_RecState`); from a `RecState` with nonzero constant term the negative-slope step
produces the next one with non-increasing multiplicity and `β > 0` (`RecState.exists_next`). The
barrier is `Q.coeff 0 = 0`. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- **A valid recursion state**: a recentered polynomial `poly` with the order structure of Lemma
2.95 for the odd multiplicity `mult`. -/
structure RecState (R : Type*) [Field R] where
  /-- The current (recentered) polynomial `Pᵢ`. -/
  poly : Polynomial (PuiseuxSeries R)
  /-- The current multiplicity `rᵢ` (odd, non-increasing along the recursion). -/
  mult : ℕ
  /-- `rᵢ` is odd. -/
  odd_mult : Odd mult
  /-- Column `rᵢ` is at height `0`: `o(b_{rᵢ}) = 0`. -/
  coeff_mult_order : puiseuxOrder R (poly.coeff mult) = (0 : WithTop ℚ)
  /-- Columns below `rᵢ` are strictly positive: `o(b_i) > 0` for `i < rᵢ`. -/
  coeff_lt_order : ∀ i, i < mult → 0 < puiseuxOrder R (poly.coeff i)
  /-- All columns are nonnegative: `o(b_i) ≥ 0`. -/
  coeff_ge_order : ∀ i, (0 : WithTop ℚ) ≤ puiseuxOrder R (poly.coeff i)

variable [IsRealClosed R]

/-- **Bootstrap.** From `P` of odd degree with nonzero constant term, the first recursion step
produces a recentered `P₁ = substPoly P x ξ β` that is a valid `RecState`, with the order-jump
bound `o(P(ε^ξ(x + y))) > β` for `o(y) > 0`. -/
theorem exists_initial_RecState {P : Polynomial (PuiseuxSeries R)} (hodd : Odd P.natDegree)
    (h0 : P.coeff 0 ≠ 0) :
    ∃ (x : R) (ξ β : ℚ) (s : RecState R), x ≠ 0 ∧ s.poly = substPoly P x ξ β ∧
      (∀ y : PuiseuxSeries R, 0 < puiseuxOrder R y →
        (β : WithTop ℚ) <
          puiseuxOrder R (P.eval (puiseuxMonomial ξ * (constPuiseux x + y)))) := by
  obtain ⟨x, ξ, β, r, hx0, hodd', ha1, ha2, ha3, hb⟩ := recursion_step h0 hodd
  exact ⟨x, ξ, β,
    { poly := substPoly P x ξ β, mult := r, odd_mult := hodd', coeff_mult_order := ha3,
      coeff_lt_order := ha2, coeff_ge_order := ha1 }, hx0, rfl, hb⟩

/-- **One continuation step.** From a valid state with nonzero constant term, the negative-slope
step produces the next valid state, with non-increasing multiplicity, `β > 0`, and the order jump
`o(Pᵢ(ε^ξ(x + y))) > β`. -/
theorem RecState.exists_next (s : RecState R) (h0 : s.poly.coeff 0 ≠ 0) :
    ∃ (x : R) (ξ β : ℚ) (A B : ℕ × ℚ) (s' : RecState R),
      x ≠ 0 ∧ s'.mult ≤ s.mult ∧ 0 < β ∧ 0 < ξ ∧ s'.poly = substPoly s.poly x ξ β ∧
      A.1 < B.1 ∧ B.1 ≤ s.mult ∧
      puiseuxOrder R (s.poly.coeff A.1) = (A.2 : WithTop ℚ) ∧
      puiseuxOrder R (s.poly.coeff B.1) = (B.2 : WithTop ℚ) ∧
      ξ = -(newtonSlope A B) ∧ β = A.2 + (A.1 : ℚ) * ξ ∧
      s'.mult = (charPoly s.poly A B).rootMultiplicity x ∧
      (∀ y : PuiseuxSeries R, 0 < puiseuxOrder R y →
        (β : WithTop ℚ) <
          puiseuxOrder R (s.poly.eval (puiseuxMonomial ξ * (constPuiseux x + y)))) := by
  obtain ⟨x, ξ, β, A, B, hx0, hABlt, hBr, hβpos, hξpos, hcolA, hcolB, hξeq, hβeq, hodd', hrle, ha1,
      ha2, ha3, hb⟩ :=
    recursion_step_neg s.odd_mult h0 s.coeff_mult_order s.coeff_lt_order s.coeff_ge_order
  exact ⟨x, ξ, β, A, B,
    { poly := substPoly s.poly x ξ β, mult := (charPoly s.poly A B).rootMultiplicity x,
      odd_mult := hodd', coeff_mult_order := ha3, coeff_lt_order := ha2, coeff_ge_order := ha1 },
    hx0, hrle, hβpos, hξpos, rfl, hABlt, hBr, hcolA, hcolB, hξeq, hβeq, rfl, hb⟩

/-- Bundled output of one continuation step: the new root coefficient `x`, exponent increment `ξ`,
order increment `β`, the chosen edge `edgeA edgeB`, the next state, and the step's properties. -/
structure StepResult (s : RecState R) where
  x : R
  xi : ℚ
  beta : ℚ
  edgeA : ℕ × ℚ
  edgeB : ℕ × ℚ
  next : RecState R
  x_ne : x ≠ 0
  mult_le : next.mult ≤ s.mult
  beta_pos : 0 < beta
  xi_pos : 0 < xi
  next_poly : next.poly = substPoly s.poly x xi beta
  edge_lt : edgeA.1 < edgeB.1
  edge_le : edgeB.1 ≤ s.mult
  colA : puiseuxOrder R (s.poly.coeff edgeA.1) = (edgeA.2 : WithTop ℚ)
  colB : puiseuxOrder R (s.poly.coeff edgeB.1) = (edgeB.2 : WithTop ℚ)
  xi_eq : xi = -(newtonSlope edgeA edgeB)
  beta_eq : beta = edgeA.2 + (edgeA.1 : ℚ) * xi
  next_mult_eq : next.mult = (charPoly s.poly edgeA edgeB).rootMultiplicity x
  order_jump : ∀ y : PuiseuxSeries R, 0 < puiseuxOrder R y →
    (beta : WithTop ℚ) <
      puiseuxOrder R (s.poly.eval (puiseuxMonomial xi * (constPuiseux x + y)))

theorem RecState.nonempty_stepResult (s : RecState R) (h0 : s.poly.coeff 0 ≠ 0) :
    Nonempty (StepResult s) := by
  obtain ⟨x, ξ, β, A, B, s', hx0, hrle, hβpos, hξpos, hpoly, hABlt, hBr, hcolA, hcolB, hξeq, hβeq,
    hmeq, hb⟩ := s.exists_next h0
  exact ⟨⟨x, ξ, β, A, B, s', hx0, hrle, hβpos, hξpos, hpoly, hABlt, hBr, hcolA, hcolB, hξeq, hβeq,
    hmeq, hb⟩⟩

open Classical in
/-- One step of the recursion as a total function: at the barrier `coeff 0 = 0` it returns junk and
freezes the state; otherwise it returns a chosen `StepResult`'s data and next state. -/
noncomputable def RecState.step (s : RecState R) : R × ℚ × ℚ × RecState R :=
  if h : s.poly.coeff 0 = 0 then (0, 0, 0, s)
  else
    let sr := Classical.choice (s.nonempty_stepResult h)
    (sr.x, sr.xi, sr.beta, sr.next)

/-- Away from the barrier, `step` returns the data of a genuine `StepResult`. -/
theorem RecState.step_spec (s : RecState R) (h : s.poly.coeff 0 ≠ 0) :
    ∃ sr : StepResult s, s.step = (sr.x, sr.xi, sr.beta, sr.next) :=
  ⟨Classical.choice (s.nonempty_stepResult h), by rw [RecState.step, dif_neg h]⟩

@[simp] theorem RecState.step_barrier (s : RecState R) (h : s.poly.coeff 0 = 0) :
    s.step = (0, 0, 0, s) := by rw [RecState.step, dif_pos h]

/-- The multiplicity is non-increasing under `step` (it freezes at the barrier). -/
theorem RecState.step_mult_le (s : RecState R) : (s.step).2.2.2.mult ≤ s.mult := by
  by_cases h : s.poly.coeff 0 = 0
  · rw [RecState.step_barrier s h]
  · obtain ⟨sr, hsr⟩ := s.step_spec h
    rw [hsr]; exact sr.mult_le

/-- **The state sequence.** Iterating `step` from an initial state. -/
noncomputable def stateSeq (s0 : RecState R) : ℕ → RecState R
  | 0 => s0
  | n + 1 => ((stateSeq s0 n).step).2.2.2

/-- The `n`-th root coefficient `x_{n+1}` produced going from state `n` to state `n+1`. -/
noncomputable def xSeq (s0 : RecState R) (n : ℕ) : R := ((stateSeq s0 n).step).1

/-- The `n`-th exponent increment `ξ_{n+1}`. -/
noncomputable def xiSeq (s0 : RecState R) (n : ℕ) : ℚ := ((stateSeq s0 n).step).2.1

/-- The `n`-th order increment `β_{n+1}`. -/
noncomputable def betaSeq (s0 : RecState R) (n : ℕ) : ℚ := ((stateSeq s0 n).step).2.2.1

/-- The multiplicity is non-increasing along the state sequence. -/
theorem stateSeq_mult_antitone (s0 : RecState R) : Antitone (fun n => (stateSeq s0 n).mult) := by
  apply antitone_nat_of_succ_le
  intro n
  show (stateSeq s0 (n + 1)).mult ≤ (stateSeq s0 n).mult
  exact RecState.step_mult_le _

/-- Away from the barrier, the step produces a nonzero `x`, positive `β`, and the recentered next
polynomial. -/
theorem RecState.step_props (s : RecState R) (h : s.poly.coeff 0 ≠ 0) :
    (s.step).1 ≠ 0 ∧ 0 < (s.step).2.2.1 ∧
      (s.step).2.2.2.poly = substPoly s.poly (s.step).1 (s.step).2.1 (s.step).2.2.1 := by
  obtain ⟨sr, hsr⟩ := s.step_spec h
  rw [hsr]; exact ⟨sr.x_ne, sr.beta_pos, sr.next_poly⟩

/-- Away from the barrier, the step's exponent increment `ξ` is positive. -/
theorem RecState.step_xi_pos (s : RecState R) (h : s.poly.coeff 0 ≠ 0) : 0 < (s.step).2.1 := by
  obtain ⟨sr, hsr⟩ := s.step_spec h
  rw [hsr]; exact sr.xi_pos

/-- Under the never-barrier hypothesis, every root coefficient `xₙ` is nonzero. -/
theorem xSeq_ne_zero (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (n : ℕ) :
    xSeq s0 n ≠ 0 := ((stateSeq s0 n).step_props (hnb n)).1

/-- Under the never-barrier hypothesis, every exponent increment `ξₙ` is positive. -/
theorem xiSeq_pos (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (n : ℕ) :
    0 < xiSeq s0 n := (stateSeq s0 n).step_xi_pos (hnb n)

/-- Under the never-barrier hypothesis, every order increment `βₙ` is positive. -/
theorem betaSeq_pos (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (n : ℕ) :
    0 < betaSeq s0 n := ((stateSeq s0 n).step_props (hnb n)).2.1

/-- Away from the barrier, the step satisfies the order jump of Lemma 2.95(b). -/
theorem RecState.step_order_jump (s : RecState R) (h : s.poly.coeff 0 ≠ 0)
    (y : PuiseuxSeries R) (hy : 0 < puiseuxOrder R y) :
    ((s.step).2.2.1 : WithTop ℚ) <
      puiseuxOrder R
        (s.poly.eval (puiseuxMonomial (s.step).2.1 * (constPuiseux (s.step).1 + y))) := by
  obtain ⟨sr, hsr⟩ := s.step_spec h
  rw [hsr]; exact sr.order_jump y hy

/-- An antitone `ℕ → ℕ` sequence is eventually constant. -/
theorem antitone_nat_eventually_const {f : ℕ → ℕ} (hf : Antitone f) :
    ∃ N, ∀ n, N ≤ n → f n = f N := by
  obtain ⟨N, hN⟩ := Nat.sInf_mem (Set.range_nonempty f)
  exact ⟨N, fun n hn => le_antisymm (hf hn) (by rw [hN]; exact Nat.sInf_le ⟨n, rfl⟩)⟩

/-- **The multiplicity stabilizes.** Eventually `(stateSeq s0 n).mult` is a constant value `r`. -/
theorem stateSeq_mult_eventually_const (s0 : RecState R) :
    ∃ N, ∀ n, N ≤ n → (stateSeq s0 n).mult = (stateSeq s0 N).mult :=
  antitone_nat_eventually_const (stateSeq_mult_antitone s0)

end Azurite.BPR
