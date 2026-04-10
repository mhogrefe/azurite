import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Polynomial
import Azurite.BasuPollackRoy.Chapter1.Section1_1
import Azurite.BasuPollackRoy.Chapter1.Section1_2

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 1: Algebraically Closed Fields
## Section 1.3: Projection Theorem for Constructible Sets

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006.

### Overview

The goal of this section is the **projection theorem**: the image of
a constructible set under a coordinate projection is again
constructible. Equivalently, the theory of algebraically closed
fields admits quantifier elimination.

A basic constructible set `S ⊂ C^{k+1}` can be described as

  S = { z ∈ C^{k+1} | ⋀_{P ∈ 𝓟} P(z) = 0 ∧ ⋀_{Q ∈ 𝓠} Q(z) ≠ 0 }

with `𝓟, 𝓠` finite subsets of `C[Y₁, …, Y_k, X]`, and its projection
`π(S)` — obtained by forgetting the last coordinate — is

  π(S) = { y ∈ C^k | ∃ x ∈ C, ⋀_{P ∈ 𝓟} P(y, x) = 0 ∧
                              ⋀_{Q ∈ 𝓠} Q(y, x) ≠ 0 }.

We consider the polynomials in `𝓟` and `𝓠` as polynomials in the
single variable `X` with the variables `(Y₁, …, Y_k)` appearing as
parameters. For a specialization of `Y` to `y = (y₁, …, y_k) ∈ C^k`,
we write `P_y(X)` for `P(y₁, …, y_k, X)`. Hence,

  π(S) = { y ∈ C^k | ∃ x ∈ C, ⋀_{P ∈ 𝓟} P_y(x) = 0 ∧
                              ⋀_{Q ∈ 𝓠} Q_y(x) ≠ 0 }.

### Representation via `Formula`

Following Section 1.1, a constructible set is represented as (the
`C`-realization of) a `Formula` over `Fin (k+1)`-many variables with
atoms of the form `P = 0` or `P ≠ 0` (`FieldAtom`). A *basic*
constructible set, as above, corresponds to a basic formula — a
conjunction of atoms in the sense of `Formula.IsBasicFormula`.

With this representation, the projection `π` is naturally defined
for any formula `Φ` in `Fin (k+1)`-many variables, producing a
subset of `C^k`: `y ∈ π(Φ)` iff some extension `(y, x) ∈ C^{k+1}`
satisfies `Φ`.

### Convention on the variable order

We order the `k+1` variables as `(Y₁, …, Y_k, X)` — the last
variable `X` is the one that gets eliminated by `π`. In Lean we use
`Fin (k+1)`, identifying:

* `Fin.castSucc i` (for `i : Fin k`) with the parameter `Y_{i+1}`;
* `Fin.last k` with the eliminated variable `X`.

Given `y : Fin k → C` and `x : C`, the concatenation `Fin.snoc y x`
is the assignment `z : Fin (k+1) → C` with
`z (Fin.castSucc i) = y i` and `z (Fin.last k) = x`.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ} {C : Type*} [Field C] [IsAlgClosed C]

/-!
### Specialization `P_y(X)`

Given `P ∈ C[Y₁, …, Y_k, X]` and a point `y ∈ C^k`, the specialization
`specialize y P : C[X]` is the univariate polynomial obtained by
substituting `Y_i ↦ y_i` while leaving `X` symbolic. This implements
BPR's notation `P_y(X)`.
-/

/-- BPR notation `P_y(X)`: specialize the first `k` variables of
`P ∈ C[Y₁, …, Y_k, X]` at `y ∈ C^k`, leaving the last variable `X`
symbolic. Concretely, `Y_i ↦ y_i` and `X ↦ X`. -/
noncomputable def specialize (y : Fin k → C)
    (P : MvPolynomial (Fin (k+1)) C) : Polynomial C :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i : Fin (k+1) =>
      Fin.lastCases (motive := fun _ => Polynomial C)
        Polynomial.X
        (fun j : Fin k => Polynomial.C (y j))
        i) P

omit [IsAlgClosed C] in
@[simp] theorem specialize_C (y : Fin k → C) (c : C) :
    specialize y (MvPolynomial.C c : MvPolynomial (Fin (k+1)) C) =
      Polynomial.C c := by
  simp [specialize]

omit [IsAlgClosed C] in
@[simp] theorem specialize_X_last (y : Fin k → C) :
    specialize y (MvPolynomial.X (Fin.last k) :
      MvPolynomial (Fin (k+1)) C) = Polynomial.X := by
  simp [specialize]

omit [IsAlgClosed C] in
@[simp] theorem specialize_X_castSucc (y : Fin k → C) (j : Fin k) :
    specialize y (MvPolynomial.X j.castSucc :
      MvPolynomial (Fin (k+1)) C) = Polynomial.C (y j) := by
  simp [specialize]

omit [IsAlgClosed C] in
/-- Evaluating the specialization `P_y(X)` at `x` recovers
`P(y₁, …, y_k, x)`, i.e. `MvPolynomial.eval (Fin.snoc y x) P`. This
is the key compatibility relating BPR's `P_y(X)` notation to direct
multivariate evaluation at a concatenated point. -/
theorem eval_specialize (y : Fin k → C) (x : C)
    (P : MvPolynomial (Fin (k+1)) C) :
    Polynomial.eval x (specialize y P) =
      MvPolynomial.eval (Fin.snoc y x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [specialize]
  | add p q hp hq =>
    simp only [specialize, MvPolynomial.eval₂_add, Polynomial.eval_add,
      MvPolynomial.eval_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i ih =>
    simp only [specialize, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, MvPolynomial.eval_mul,
      MvPolynomial.eval_X, Polynomial.eval_mul] at ih ⊢
    rw [ih]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]

/-!
### The projection `π`

A basic constructible set `S ⊂ C^{k+1}` is (the `C`-realization of)
a *basic formula* over `Fin (k+1)`-many variables — see
`Formula.IsBasicFormula` in Section 1.1. We define its projection
`π(S) ⊂ C^k`, which forgets the last coordinate.

The projection is defined for an arbitrary formula `Φ` over
`Fin (k+1)` variables: `y ∈ Φ.proj` iff some extension
`Fin.snoc y x` to `C^{k+1}` satisfies `Φ`. In the basic case
described above, this agrees with BPR's form using `specialize`
(established atom-wise in `realization_eq_zero` / `realization_ne_zero`
from Section 1.1 together with `eval_specialize` above).
-/

namespace Formula

/-- BPR's projection `π(S)`: for a formula `Φ` describing a set in
`C^{k+1}`, `Φ.proj` is the subset of `C^k` consisting of points `y`
such that some extension `Fin.snoc y x : Fin (k+1) → C` lies in
`Φ`'s realization. -/
noncomputable def proj
    (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) C)) :
    Set (Fin k → C) :=
  { y | ∃ x : C, Fin.snoc y x ∈ Φ.realization (C := C) }

/-!
### Fibers `S_y`

When `S ⊂ C^{k+1}` is a basic constructible set described by `(𝓟, 𝓠)`
and `y ∈ C^k`, BPR introduces the fiber

  S_y := { x ∈ C | ⋀_{P ∈ 𝓟} P_y(x) = 0 ∧ ⋀_{Q ∈ 𝓠} Q_y(x) ≠ 0 } ⊂ C,

obtained by specializing the parameters `Y` to `y` and then asking
which `x ∈ C` satisfy the resulting univariate conditions. The
projection is recovered as `y ∈ π(S) ↔ S_y ≠ ∅`.

In our `Formula` representation, the fiber over `y` is simply the
set of `x ∈ C` for which `Fin.snoc y x` satisfies the formula:
specialization is then a *consequence* of `eval_specialize` rather
than the definition.
-/

/-- BPR's fiber `S_y`: for a formula `Φ` describing a set in
`C^{k+1}` and a point `y : Fin k → C`, `Φ.fiber y` is the subset of
`C` consisting of those `x` such that `Fin.snoc y x` satisfies `Φ`.
-/
noncomputable def fiber
    (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) C))
    (y : Fin k → C) : Set C :=
  { x : C | Fin.snoc y x ∈ Φ.realization (C := C) }

omit [IsAlgClosed C] in
/-- A point `y ∈ C^k` lies in the projection `π(S)` iff the fiber
`S_y` is nonempty. -/
theorem mem_proj_iff_fiber_nonempty
    (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) C))
    (y : Fin k → C) :
    y ∈ Φ.proj ↔ (Φ.fiber y).Nonempty :=
  Iff.rfl

end Formula

/-!
### Signed pseudo-remainder `PRem(P, Q)`

Let `P = a_p X^p + ⋯ + a_0`, `Q = b_q X^q + ⋯ + b_0 ∈ D[X]`, where
`D` is a subring of `C`. The only denominators appearing in the
Euclidean division of `P` by `Q` are powers `b_q^i` with `i ≤ p - q + 1`,
so multiplying `P` by `b_q^{p - q + 1}` already clears all
denominators and produces a remainder that lives in `D[X]`.

The **signed pseudo-remainder** `PRem(P, Q)` is defined as the
remainder in the Euclidean division of `b_q^d · P` by `Q`, where `d`
is the *smallest even integer* `≥ p - q + 1` (with the convention
that `d = 0` when `p < q`). Taking `d` even guarantees that the sign
of `b_q^d` is `+1` regardless of the sign of `b_q` — a property that
will matter in Chapter 2 for real closed fields. Since `d ≥ p - q + 1`,
the division of `b_q^d · P` by `Q` can still be performed in `D` and
`PRem(P, Q) ∈ D[X]`.

Following Section 1.2's `Quo`/`Rem`, we define `PRem(P, Q) : K[X]`
(living a priori in the fraction field `K = Frac(D)`) and record
separately that the result descends to `D[X]`.
-/

variable {D : Type*} [CommRing D] [IsDomain D]
variable {K : Type*} [Field K] [Algebra D K] [IsFractionRing D K]

/-- `smallestEvenGe n`: the smallest even natural number `≥ n`. -/
def smallestEvenGe (n : ℕ) : ℕ := n + n % 2

theorem smallestEvenGe_even (n : ℕ) : Even (smallestEvenGe n) := by
  rw [smallestEvenGe, Nat.even_iff]; omega

theorem le_smallestEvenGe (n : ℕ) : n ≤ smallestEvenGe n := by
  rw [smallestEvenGe]; omega

/-- `pRemExp P Q`: the exponent `d` used to scale `P` in the signed
pseudo-remainder — the smallest even natural number greater than or
equal to `natDegree P - natDegree Q + 1`, with the convention that
`d = 0` when `natDegree P < natDegree Q`. -/
def pRemExp (P Q : Polynomial D) : ℕ :=
  smallestEvenGe (if P.natDegree < Q.natDegree then 0
                  else P.natDegree - Q.natDegree + 1)

omit [IsDomain D] in
theorem pRemExp_even (P Q : Polynomial D) : Even (pRemExp P Q) :=
  smallestEvenGe_even _

omit [IsDomain D] in
theorem pRemExp_ge (P Q : Polynomial D) (h : Q.natDegree ≤ P.natDegree) :
    P.natDegree - Q.natDegree + 1 ≤ pRemExp P Q := by
  rw [pRemExp, if_neg (Nat.not_lt.mpr h)]
  exact le_smallestEvenGe _

/-- BPR's **signed pseudo-remainder** `PRem(P, Q)`: the remainder in
the Euclidean division of `b_q^d · P` by `Q`, where `b_q` is the
leading coefficient of `Q` and `d = pRemExp P Q` is the smallest
even integer `≥ natDegree P - natDegree Q + 1`. Defined in `Polynomial K`
via the Euclidean division of Section 1.2; `PRem(P, Q)` in fact
descends to `Polynomial D` (to be shown separately). -/
noncomputable def PRem (K : Type*) [Field K] [Algebra D K]
    [IsFractionRing D K] (P Q : Polynomial D) : Polynomial K :=
  Rem K (Polynomial.C (Q.leadingCoeff ^ pRemExp P Q) * P) Q

omit [IsDomain D] in
/-- The degree bound on `PRem(P, Q)` inherited from Euclidean
division: when `Q ≠ 0`, `PRem(P, Q)` has degree strictly less than
`Q` (after mapping to `K[X]`). -/
theorem degree_pRem_lt (P Q : Polynomial D) (hQ : Q ≠ 0) :
    (PRem K P Q).degree < (Q.map (algebraMap D K)).degree := by
  unfold PRem
  exact degree_rem_lt _ _ hQ

/-!
### `PRem` descends to `D[X]`

We now show that the signed pseudo-remainder `PRem(P, Q)`, defined a
priori in `K[X]`, in fact lies in the image of `D[X]` under the
canonical embedding. The proof proceeds in two steps:

1. An auxiliary existence statement: for every `n ≥ p - q + 1` (with
   the standard `0` convention when `p < q`), there exist `A, R ∈ D[X]`
   with `b_q^n · P = A · Q + R` and `deg R < deg Q`, where the
   computation is done entirely in `D[X]`. This is the classical
   *pseudo-division*: iteratively eliminate the leading term of `P`
   by subtracting `a_p · X^{p-q} · Q` after scaling `P` by `b_q`.
2. Specializing `n = pRemExp P Q` and mapping to `K[X]`, the
   uniqueness of Euclidean division identifies the `D[X]`-remainder
   `R` with `PRem(P, Q)`.
-/

/-- Pseudo-division in `D[X]`: for any exponent `n` at least
`p - q + 1` (with the convention that the bound is `0` when `p < q`),
there exist `A, R ∈ D[X]` with `b_q^n · P = A · Q + R` and
`deg R < deg Q`. The proof is by strong induction on `natDegree P`. -/
theorem pRem_exists_aux (Q : Polynomial D) (hQ : Q ≠ 0) :
    ∀ (p : ℕ) (P : Polynomial D), P.natDegree < p →
    ∀ (n : ℕ),
    (if P.natDegree < Q.natDegree then 0
     else P.natDegree - Q.natDegree + 1) ≤ n →
    ∃ A R : Polynomial D,
      Polynomial.C (Q.leadingCoeff ^ n) * P = A * Q + R ∧
      R.degree < Q.degree := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro P hPdeg n hn
    -- Case 1: P = 0
    by_cases hP : P = 0
    · refine ⟨0, 0, by simp [hP], ?_⟩
      rw [Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])
    -- Case 2: deg P < deg Q
    by_cases hdeg : P.natDegree < Q.natDegree
    · refine ⟨0, Polynomial.C (Q.leadingCoeff ^ n) * P, by ring, ?_⟩
      have hbn : (Q.leadingCoeff ^ n) ≠ 0 :=
        pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hQ)
      have hnat : (Polynomial.C (Q.leadingCoeff ^ n) * P).natDegree = P.natDegree :=
        Polynomial.natDegree_C_mul hbn
      exact Polynomial.degree_lt_degree (hnat ▸ hdeg)
    -- Case 3: deg P ≥ deg Q, P ≠ 0 — reduce
    have hdeg' : Q.natDegree ≤ P.natDegree := Nat.not_lt.mp hdeg
    have ha_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
    have hb_ne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    rw [if_neg hdeg] at hn
    have hn1 : 1 ≤ n := by omega
    -- The reduced polynomial P' = C(b)*P - C(a)*X^(pP-qQ)*Q
    set P' : Polynomial D :=
      Polynomial.C Q.leadingCoeff * P -
        Polynomial.C P.leadingCoeff * Polynomial.X ^ (P.natDegree - Q.natDegree) * Q
      with hP'def
    -- Fundamental equation: C(b)*P = C(a)*X^(pP-qQ)*Q + P'
    have hfund : Polynomial.C Q.leadingCoeff * P =
        Polynomial.C P.leadingCoeff * Polynomial.X ^ (P.natDegree - Q.natDegree) * Q + P' := by
      rw [hP'def]; ring
    -- Get A', R' for C(b^(n-1)) * P'
    obtain ⟨A', R', hAR', hdR'⟩ : ∃ A' R' : Polynomial D,
        Polynomial.C (Q.leadingCoeff ^ (n - 1)) * P' = A' * Q + R' ∧
          R'.degree < Q.degree := by
      by_cases hP' : P' = 0
      · refine ⟨0, 0, by simp [hP'], ?_⟩
        rw [Polynomial.degree_zero]
        exact bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])
      · -- P' ≠ 0: show natDegree P' < P.natDegree, then apply ih
        have hsub : P.natDegree - Q.natDegree + Q.natDegree = P.natDegree :=
          Nat.sub_add_cancel hdeg'
        have hP'_natDeg : P'.natDegree < P.natDegree := by
          have hLdeg : (Polynomial.C Q.leadingCoeff * P).degree =
              (Polynomial.C P.leadingCoeff *
                Polynomial.X ^ (P.natDegree - Q.natDegree) * Q).degree := by
            rw [Polynomial.degree_C_mul hb_ne,
                mul_assoc,
                Polynomial.degree_C_mul ha_ne,
                Polynomial.degree_mul, Polynomial.degree_X_pow,
                Polynomial.degree_eq_natDegree hQ,
                Polynomial.degree_eq_natDegree hP]
            norm_cast
            omega
          have hLne : Polynomial.C Q.leadingCoeff * P ≠ 0 :=
            mul_ne_zero (fun h => hb_ne (Polynomial.C_eq_zero.mp h)) hP
          have hLeadEq : (Polynomial.C Q.leadingCoeff * P).leadingCoeff =
              (Polynomial.C P.leadingCoeff *
                Polynomial.X ^ (P.natDegree - Q.natDegree) * Q).leadingCoeff := by
            rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
                Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
                Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X_pow]
            ring
          have hP'_deg_lt : P'.degree < (Polynomial.C Q.leadingCoeff * P).degree :=
            Polynomial.degree_sub_lt hLdeg hLne hLeadEq
          rw [Polynomial.degree_C_mul hb_ne,
              Polynomial.degree_eq_natDegree hP',
              Polynomial.degree_eq_natDegree hP] at hP'_deg_lt
          exact_mod_cast hP'_deg_lt
        -- Apply IH with m = P.natDegree (< p) and exponent n-1
        have hbound : (if P'.natDegree < Q.natDegree then 0
                       else P'.natDegree - Q.natDegree + 1) ≤ n - 1 := by
          split_ifs with h
          · omega
          · simp only [not_lt] at h
            omega
        exact ih P.natDegree hPdeg P' hP'_natDeg (n - 1) hbound
    -- Reconstruct A and R for the original problem
    refine ⟨A' + Polynomial.C (Q.leadingCoeff ^ (n - 1) * P.leadingCoeff) *
            Polynomial.X ^ (P.natDegree - Q.natDegree), R', ?_, hdR'⟩
    -- C(b^n) * P = C(b^(n-1)) * (C(b) * P)
    --            = C(b^(n-1)) * (C(a) * X^(pP-qQ) * Q + P')
    --            = (A' + C(b^(n-1) * a) * X^(pP-qQ)) * Q + R'
    have hbn : Q.leadingCoeff ^ n =
        Q.leadingCoeff ^ (n - 1) * Q.leadingCoeff := by
      conv_lhs => rw [show n = (n - 1) + 1 from by omega]
      rw [pow_succ]
    calc Polynomial.C (Q.leadingCoeff ^ n) * P
        = Polynomial.C (Q.leadingCoeff ^ (n - 1)) *
          (Polynomial.C Q.leadingCoeff * P) := by
          rw [hbn, Polynomial.C_mul]; ring
      _ = Polynomial.C (Q.leadingCoeff ^ (n - 1)) *
          (Polynomial.C P.leadingCoeff * Polynomial.X ^ (P.natDegree - Q.natDegree)
            * Q + P') := by rw [hfund]
      _ = (A' + Polynomial.C (Q.leadingCoeff ^ (n - 1) * P.leadingCoeff) *
            Polynomial.X ^ (P.natDegree - Q.natDegree)) * Q + R' := by
          rw [Polynomial.C_mul]
          linear_combination hAR'

/-- The signed pseudo-remainder `PRem(P, Q)` lies in `D[X]`: there
exists `R : D[X]` whose image in `K[X]` equals `PRem K P Q`. -/
theorem PRem_descends (P Q : Polynomial D) (hQ : Q ≠ 0) :
    ∃ R : Polynomial D, R.map (algebraMap D K) = PRem K P Q := by
  have hbound : (if P.natDegree < Q.natDegree then 0
                 else P.natDegree - Q.natDegree + 1) ≤ pRemExp P Q := by
    split_ifs with h
    · exact Nat.zero_le _
    · exact pRemExp_ge P Q (Nat.not_lt.mp h)
  obtain ⟨A, R, hAR, hdR⟩ :=
    pRem_exists_aux Q hQ (P.natDegree + 1) P (Nat.lt_succ_self _)
      (pRemExp P Q) hbound
  refine ⟨R, ?_⟩
  -- Map the equation to K[X]
  have hmap := congrArg (Polynomial.map (algebraMap D K)) hAR
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C] at hmap
  -- PRem K P Q = (C(b^d) * P).map % Q.map
  unfold PRem Rem
  simp only [Polynomial.map_mul, Polynomial.map_C]
  -- Want: R.map = ((C(b^d).map * P.map)) % Q.map
  have hQmap_ne : Q.map (algebraMap D K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (IsFractionRing.injective D K)).mpr hQ
  have hdR_map : (R.map (algebraMap D K)).degree < (Q.map (algebraMap D K)).degree := by
    rwa [Polynomial.degree_map_eq_of_injective (IsFractionRing.injective D K),
         Polynomial.degree_map_eq_of_injective (IsFractionRing.injective D K)]
  -- Use EuclideanDomain.mod_eq_zero and Polynomial.sub_mod
  have hdvd : Q.map (algebraMap D K) ∣
      (Polynomial.C ((algebraMap D K) (Q.leadingCoeff ^ pRemExp P Q)) *
        P.map (algebraMap D K)) - R.map (algebraMap D K) :=
    ⟨A.map (algebraMap D K), by linear_combination hmap⟩
  have hmod_sub : ((Polynomial.C ((algebraMap D K) (Q.leadingCoeff ^ pRemExp P Q)) *
      P.map (algebraMap D K)) - R.map (algebraMap D K)) %
        Q.map (algebraMap D K) = 0 :=
    EuclideanDomain.mod_eq_zero.mpr hdvd
  rw [Polynomial.sub_mod, sub_eq_zero] at hmod_sub
  rw [hmod_sub, (Polynomial.mod_eq_self_iff hQmap_ne).mpr hdR_map]

end Azurite.BPR
