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

  S = { z ∈ C^{k+1} | ⋀_{P ∈ 𝓟} P(z) = 0 ∧ ⋀_{Q ∈ 𝓠} Q(z) ≠ 0}

with `𝓟, 𝓠` finite subsets of `C[Y₁, …, Y_k, X]`, and its projection
`π(S)` — obtained by forgetting the last coordinate — is

  π(S) = { y ∈ C^k | ∃ x ∈ C, ⋀_{P ∈ 𝓟} P(y, x) = 0 ∧
                              ⋀_{Q ∈ 𝓠} Q(y, x) ≠ 0}.

We consider the polynomials in `𝓟` and `𝓠` as polynomials in the
single variable `X` with the variables `(Y₁, …, Y_k)` appearing as
parameters. For a specialization of `Y` to `y = (y₁, …, y_k) ∈ C^k`,
we write `P_y(X)` for `P(y₁, …, y_k, X)`. Hence,

  π(S) = { y ∈ C^k | ∃ x ∈ C, ⋀_{P ∈ 𝓟} P_y(x) = 0 ∧
                              ⋀_{Q ∈ 𝓠} Q_y(x) ≠ 0}.

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

  S_y := { x ∈ C | ⋀_{P ∈ 𝓟} P_y(x) = 0 ∧ ⋀_{Q ∈ 𝓠} Q_y(x) ≠ 0} ⊂ C,

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

/-!
### Truncation `Tru_i(Q)`

BPR's **Notation 1.16**: for `Q = b_q X^q + ⋯ + b_0 ∈ D[X]` and
`0 ≤ i ≤ q`, the *truncation of `Q` at `i`* is

  Tru_i(Q) = b_i X^i + ⋯ + b_0,

obtained from `Q` by dropping all monomial terms of degree `> i`.
We extend the definition to arbitrary `i : ℕ` by the same formula;
when `i ≥ natDegree Q` the result coincides with `Q`.
-/

/-- BPR's **truncation** `Tru_i(Q)` (Notation 1.16): for
`Q = b_q X^q + ⋯ + b_0 ∈ R[X]`, the polynomial obtained by
dropping every monomial term of degree `> i`. Concretely,
`Tru_i(Q) = b_i X^i + ⋯ + b_0`. Stated over an arbitrary semiring
`R`; BPR's original statement takes `R = D` a domain. -/
noncomputable def truncate {R : Type*} [Semiring R] (i : ℕ)
    (Q : Polynomial R) : Polynomial R :=
  ∑ j ∈ Finset.range (i + 1), Polynomial.monomial j (Q.coeff j)

/-- Coefficient characterization of `truncate`: the `j`-th coefficient
of `Tru_i(Q)` is `Q.coeff j` when `j ≤ i`, and `0` otherwise. -/
@[simp] theorem coeff_truncate {R : Type*} [Semiring R] (i : ℕ)
    (Q : Polynomial R) (j : ℕ) :
    (truncate i Q).coeff j = if j ≤ i then Q.coeff j else 0 := by
  rw [truncate, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range,
    Nat.lt_succ_iff]

/-- The `natDegree` of a truncation is at most `i`. -/
theorem natDegree_truncate_le {R : Type*} [Semiring R] (i : ℕ)
    (Q : Polynomial R) : (truncate i Q).natDegree ≤ i := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_truncate, if_neg (Nat.not_le.mpr hj)]

/-!
### Set of truncations `Tru(Q)`

BPR's **set of truncations** of a non-zero polynomial
`Q ∈ D[Y_1, …, Y_k][X]` is the finite subset of `D[Y_1, …, Y_k][X]`
defined recursively by

  Tru(Q) = {Q}                             if lcof(Q) ∈ D or deg_X(Q) = 0,
            {Q} ∪ Tru(Tru_{deg_X(Q)−1}(Q)) otherwise.

We extend to `Q = 0` by setting `Tru(0) = ∅`.

The recursion terminates because `natDegree (truncate (natDegree Q − 1) Q)`
is strictly less than `natDegree Q` whenever `natDegree Q > 0`.
-/

section Tru
open Classical

/-- BPR's **set of truncations** `Tru(Q)` for
`Q ∈ D[Y_1, …, Y_k][X]`. Returns the empty set when `Q = 0`;
`{Q}` when `lcof(Q) ∈ D` or `deg_X(Q) = 0`; and
`{Q} ∪ Tru(Tru_{deg_X(Q)-1}(Q))` otherwise. -/
noncomputable def Tru :
    Polynomial (MvPolynomial (Fin k) D) →
    Set (Polynomial (MvPolynomial (Fin k) D))
  | Q =>
    if Q = 0 then ∅
    else if (∃ d : D, Q.leadingCoeff = MvPolynomial.C d) ∨ Q.natDegree = 0 then
      {Q}
    else
      {Q} ∪ Tru (truncate (Q.natDegree - 1) Q)
termination_by Q => Q.natDegree
decreasing_by
  show (truncate (Q.natDegree - 1) Q).natDegree < Q.natDegree
  have hQpos : 0 < Q.natDegree := by
    rename_i _ hb
    push Not at hb
    exact Nat.pos_of_ne_zero hb.2
  have h := natDegree_truncate_le (Q.natDegree - 1) Q
  omega

end Tru

/-!
### Tree of possible signed pseudo-remainder sequences `TRems(P, Q)`

The **tree of possible signed pseudo-remainder sequences** of two
polynomials `P, Q ∈ D[Y₁, …, Y_k][X]`, denoted `TRems(P, Q)`, is
a (rose) tree defined as follows:

* The **root** contains `P`.
* The **children of the root** are labelled by the elements of `Tru(Q)`.
* Each node `N` stores a polynomial `Pol(N) ∈ D[Y₁, …, Y_k][X]`.
* `N` is a **leaf** (no children) when `Pol(N) = 0`.
* If `N` is not a leaf, the children of `N` are labelled by the
  truncations of `−PRem(Pol(p(N)), Pol(N))`, where `p(N)` is
  `N`'s parent.
-/

/-- Rose tree: a node labelled by `α` with a list of subtrees. -/
inductive RoseTree (α : Type*) where
  | node : α → List (RoseTree α) → RoseTree α

/-- The label at the root of a `RoseTree`. -/
def RoseTree.root : RoseTree α → α
  | .node a _ => a

section TRems

open Classical

omit [IsDomain D] in
/-- `Tru Q` is always a finite set. -/
theorem Tru_finite (Q : Polynomial (MvPolynomial (Fin k) D)) :
    (Tru Q).Finite := by
  rw [Tru]
  split_ifs
  · exact Set.finite_empty
  · exact Set.finite_singleton _
  · exact (Set.finite_singleton _).union (Tru_finite _)
termination_by Q.natDegree
decreasing_by
  show (truncate (Q.natDegree - 1) Q).natDegree < Q.natDegree
  have hQpos : 0 < Q.natDegree := by
    rename_i _ hb
    push Not at hb
    exact Nat.pos_of_ne_zero hb.2
  have h := natDegree_truncate_le (Q.natDegree - 1) Q
  omega

omit [IsDomain D] in
/-- Elements of `Tru Q` have `natDegree ≤ Q.natDegree`. -/
theorem natDegree_mem_Tru_le {Q Q' : Polynomial (MvPolynomial (Fin k) D)}
    (hQ' : Q' ∈ Tru Q) : Q'.natDegree ≤ Q.natDegree := by
  by_cases h0 : Q = 0
  · subst h0; rw [Tru, if_pos rfl] at hQ'; exact hQ'.elim
  · rw [Tru, if_neg h0] at hQ'
    by_cases hbase : (∃ d : D, Q.leadingCoeff = MvPolynomial.C d) ∨ Q.natDegree = 0
    · rw [if_pos hbase, Set.mem_singleton_iff] at hQ'; subst hQ'; exact le_refl _
    · rw [if_neg hbase, Set.mem_union, Set.mem_singleton_iff] at hQ'
      rcases hQ' with rfl | hQ'
      · exact le_refl _
      · have := natDegree_mem_Tru_le hQ'
        have := natDegree_truncate_le (Q.natDegree - 1) Q
        omega
termination_by Q.natDegree
decreasing_by
  show (truncate (Q.natDegree - 1) Q).natDegree < Q.natDegree
  have hQpos : 0 < Q.natDegree := by
    push Not at hbase; exact Nat.pos_of_ne_zero hbase.2
  have := natDegree_truncate_le (Q.natDegree - 1) Q; omega

/-- The signed pseudo-remainder of `P` and `Q` in `D[Y₁,…,Y_k][X]`,
descended from the fraction field. Returns `0` when `Q = 0`. -/
noncomputable def pRemMv
    (P Q : Polynomial (MvPolynomial (Fin k) D)) :
    Polynomial (MvPolynomial (Fin k) D) :=
  if hQ : Q = 0 then 0
  else (@PRem_descends (MvPolynomial (Fin k) D) _ _
    (FractionRing (MvPolynomial (Fin k) D)) _ _ _ P Q hQ).choose

/-- The descended `pRemMv` maps to `PRem` under `algebraMap`. -/
theorem pRemMv_spec
    (P Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0) :
    (pRemMv P Q).map (algebraMap (MvPolynomial (Fin k) D)
      (FractionRing (MvPolynomial (Fin k) D))) =
      PRem (FractionRing (MvPolynomial (Fin k) D)) P Q := by
  unfold pRemMv; rw [dif_neg hQ]
  exact (@PRem_descends (MvPolynomial (Fin k) D) _ _
    (FractionRing (MvPolynomial (Fin k) D)) _ _ _ P Q hQ).choose_spec

/-- The descended pseudo-remainder has degree strictly less than the
divisor when the divisor is nonzero. -/
theorem degree_pRemMv_lt
    (P Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0) :
    (pRemMv P Q).degree < Q.degree := by
  unfold pRemMv; rw [dif_neg hQ]
  have hinj := IsFractionRing.injective (MvPolynomial (Fin k) D)
    (FractionRing (MvPolynomial (Fin k) D))
  have hspec := (@PRem_descends (MvPolynomial (Fin k) D) _ _
    (FractionRing (MvPolynomial (Fin k) D)) _ _ _ P Q hQ).choose_spec
  rw [← Polynomial.degree_map_eq_of_injective hinj,
      ← Polynomial.degree_map_eq_of_injective hinj Q, hspec]
  exact @degree_pRem_lt (MvPolynomial (Fin k) D) _
    (FractionRing (MvPolynomial (Fin k) D)) _ _ _ P Q hQ

/-- Build the subtree of `TRems` rooted at `curPol`, whose parent
holds `parentPol`. Terminates because `natDegree` strictly decreases
through `PRem` and `Tru`. -/
noncomputable def mkTRemsNode
    (parentPol curPol : Polynomial (MvPolynomial (Fin k) D)) :
    RoseTree (Polynomial (MvPolynomial (Fin k) D)) :=
  if curPol = 0 then .node curPol []
  else
    let next := -(pRemMv parentPol curPol)
    let children := (Tru_finite next).toFinset.toList
    .node curPol (children.attach.map fun ⟨child, _hmem⟩ =>
      mkTRemsNode curPol child)
termination_by curPol.natDegree
decreasing_by
  rename_i h_ne
  have hmem_tru : child ∈ Tru next :=
    (Set.Finite.mem_toFinset _).mp ((Finset.mem_toList).mp _hmem)
  by_cases h4 : pRemMv parentPol curPol = 0
  · -- next = 0 ⇒ Tru next = ∅, contradicting hmem_tru
    have hn0 : next = 0 := show -(pRemMv parentPol curPol) = 0 by rw [h4, neg_zero]
    rw [hn0, Tru, if_pos rfl] at hmem_tru; exact hmem_tru.elim
  · have h1 := natDegree_mem_Tru_le hmem_tru
    have h5 := Polynomial.natDegree_lt_natDegree h4
      (degree_pRemMv_lt parentPol curPol h_ne)
    have h6 : next.natDegree = (pRemMv parentPol curPol).natDegree :=
      Polynomial.natDegree_neg _
    omega

/-- BPR's **tree of possible signed pseudo-remainder sequences**
`TRems(P, Q)` for `P, Q ∈ D[Y₁, …, Y_k][X]`.

The root contains `P`; its children are the elements of `Tru(Q)`;
each deeper level unfolds via `Tru(−PRem(…))`. A node whose
polynomial is `0` is a leaf. -/
noncomputable def TRems
    (P Q : Polynomial (MvPolynomial (Fin k) D)) :
    RoseTree (Polynomial (MvPolynomial (Fin k) D)) :=
  .node P ((Tru_finite Q).toFinset.toList.map (mkTRemsNode P))

end TRems

/-!
### Example 1.17

For `P = X⁴ + aX² + bX + c` and `Q = 4X³ + 2aX + b` (the derivative
of `P`), the tree `TRems(P, Q)` has 10 nodes and 4 leaves.
The computable version `Azurite.AzPolynomial.tremsTree` reproduces
this example with every node verified by `#guard` tests in
`Azurite/AzPolynomial/TRems.lean`.
-/

/-!
### Notation 1.18: Degree as a formula

For `Q ∈ D[Y₁, …, Y_k][X]`, the **degree formula** `degFormula Q i`
is a quantifier-free formula in the variables `Y₁, …, Y_k` whose
`C`-realization is the set of `y ∈ C^k` such that the specialized
polynomial `Q_y(X)` has degree `i` (where `i ∈ WithBot ℕ`, with
`⊥` representing degree `−∞`, i.e. `Q_y = 0`).

Concretely:
- `degFormula Q ⊥` is the conjunction `⋀_{j=0}^{natDeg Q} (coeff Q j = 0)`.
- `degFormula Q (some n)` is `coeff Q n ≠ 0 ∧ ⋀_{j=n+1}^{natDeg Q} (coeff Q j = 0)`.
- `degEqFormula Q₁ Q₂` is `⋁_i (degFormula Q₁ i ∧ degFormula Q₂ i)`.
-/

section DegFormula

variable {D : Type*} [CommRing D] [IsDomain D]
omit [IsDomain D]

/-- BPR Notation 1.18: `deg_X(Q) = i` as a formula in `Fin k` variables.

For `Q ∈ D[Y₁,…,Yₖ][X]`:
- `i = ⊥` means all coefficients vanish (degree = −∞, i.e., `Q_y = 0`)
- `i = some n` means `coeff Q n ≠ 0` and all higher coefficients vanish -/
noncomputable def degFormula
    (Q : Polynomial (MvPolynomial (Fin k) D)) (i : WithBot ℕ) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  match i with
  | ⊥ => Formula.conjList ((List.range (Q.natDegree + 1)).map fun j =>
      Formula.eq_zero (Q.coeff j))
  | some n => .and
      (Formula.ne_zero (Q.coeff n))
      (Formula.conjList ((List.range (Q.natDegree - n)).map fun j =>
        Formula.eq_zero (Q.coeff (n + 1 + j))))

/-- BPR Notation 1.18: `deg_X(Q₁) = deg_X(Q₂)` as a formula.

This is the finite disjunction over all possible degree values
`i ∈ {⊥, 0, 1, …, max(natDeg Q₁, natDeg Q₂)}` of
`degFormula Q₁ i ∧ degFormula Q₂ i`. -/
noncomputable def degEqFormula
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  let m := max Q₁.natDegree Q₂.natDegree
  Formula.disjList (
    ((degFormula Q₁ ⊥).and (degFormula Q₂ ⊥)) ::
    (List.range (m + 1)).map fun i =>
      (degFormula Q₁ (some i)).and (degFormula Q₂ (some i)))

/-! #### Degree characterization lemma -/

private theorem degree_eq_coe_iff
    {R : Type*} [Semiring R] (p : Polynomial R) (n : ℕ) :
    p.degree = ↑n ↔ p.coeff n ≠ 0 ∧ ∀ m, n < m → p.coeff m = 0 := by
  constructor
  · intro h
    exact ⟨by rw [← Polynomial.natDegree_eq_of_degree_eq_some h]
              exact Polynomial.leadingCoeff_ne_zero.mpr (by intro h0; simp [h0] at h),
           fun m hm => (Polynomial.degree_le_iff_coeff_zero p n).mp (le_of_eq h) m
              (by exact_mod_cast hm)⟩
  · intro ⟨hne, hhi⟩
    exact le_antisymm
      ((Polynomial.degree_le_iff_coeff_zero p n).mpr
        fun m hm => hhi m (by exact_mod_cast hm))
      (Polynomial.le_degree_of_ne_zero hne)

/-- Coefficients above `natDegree` vanish: a convenient shorthand. -/
private theorem coeff_eq_zero_of_natDegree_lt
    {R : Type*} [Semiring R] (Q : Polynomial R) {n : ℕ}
    (h : Q.natDegree < n) : Q.coeff n = 0 := by
  have := Polynomial.degree_le_natDegree (p := Q)
  exact (Polynomial.degree_le_iff_coeff_zero Q Q.natDegree).mp this n
    (by exact_mod_cast h)

/-! #### Helper: coefficient vanishing above `natDegree` under ring homs -/

private theorem map_eq_zero_iff
    {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (Q : Polynomial R) :
    Q.map f = 0 ↔ ∀ n ≤ Q.natDegree, f (Q.coeff n) = 0 := by
  constructor
  · intro h n _
    have := congr_arg (fun p => Polynomial.coeff p n) h
    simp [Polynomial.coeff_map] at this
    exact this
  · intro h
    ext n
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hn : n ≤ Q.natDegree
    · exact h n hn
    · have : Q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt Q (by omega)
      simp [this]

private theorem map_degree_eq_coe_iff
    {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (Q : Polynomial R) (n : ℕ) :
    (Q.map f).degree = ↑n ↔
      f (Q.coeff n) ≠ 0 ∧ ∀ m, n < m → m ≤ Q.natDegree → f (Q.coeff m) = 0 := by
  rw [degree_eq_coe_iff]
  simp only [Polynomial.coeff_map]
  constructor
  · exact fun ⟨hne, hhi⟩ => ⟨hne, fun m hm _ => hhi m hm⟩
  · intro ⟨hne, hhi⟩
    exact ⟨hne, fun m hm => by
      by_cases hm' : m ≤ Q.natDegree
      · exact hhi m hm hm'
      · have : Q.coeff m = 0 := coeff_eq_zero_of_natDegree_lt Q (by omega)
        simp [this]⟩

/-! #### Realization of `degFormula` -/

/-- The realization of `degFormula Q i` is the set of `y ∈ C^k` where
the specialized polynomial `Q.map (aeval y)` has degree `i`.

This is the formal counterpart of BPR's claim that `Reali(deg_X(Q) = i)`
partitions `C^k` according to the degree of `Q_y`. -/
theorem realization_degFormula
    {C : Type*} [Field C] [Algebra D C]
    (Q : Polynomial (MvPolynomial (Fin k) D)) (i : WithBot ℕ) :
    (degFormula Q i).realization (C := C) =
      { y | (Q.map (MvPolynomial.aeval y).toRingHom).degree = i } := by
  match i with
  | ⊥ =>
    ext y
    simp only [degFormula, Formula.realization_conjList, Set.mem_setOf_eq,
      List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Formula.realization_eq_zero]
    rw [Polynomial.degree_eq_bot, map_eq_zero_iff]
    constructor
    · exact fun h n hn => h n (by omega)
    · exact fun h n hn => h n (by omega)
  | some n =>
    ext y
    simp only [degFormula, Formula.realization_and, Formula.realization_ne_zero,
      Formula.realization_conjList, Set.mem_inter_iff, Set.mem_setOf_eq,
      List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Formula.realization_eq_zero]
    rw [show (some n : WithBot ℕ) = (↑n : WithBot ℕ) from rfl,
        map_degree_eq_coe_iff]
    constructor
    · intro ⟨hne, hhi⟩
      exact ⟨hne, fun m hm hm' => by
        have hlt : m - (n + 1) < Q.natDegree - n := by omega
        have := hhi (m - (n + 1)) hlt
        rwa [show n + 1 + (m - (n + 1)) = m by omega] at this⟩
    · intro ⟨hne, hhi⟩
      exact ⟨hne, fun j hj => hhi (n + 1 + j) (by omega) (by omega)⟩

/-- The realization of `degEqFormula Q₁ Q₂` is the set of `y ∈ C^k`
where `Q₁_y` and `Q₂_y` have the same degree. -/
theorem realization_degEqFormula
    {C : Type*} [Field C] [Algebra D C]
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    (degEqFormula Q₁ Q₂).realization (C := C) =
      { y | (Q₁.map (MvPolynomial.aeval y).toRingHom).degree =
            (Q₂.map (MvPolynomial.aeval y).toRingHom).degree } := by
  ext y
  simp only [degEqFormula, Formula.realization_disjList, Set.mem_setOf_eq,
    List.mem_cons, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, rfl | ⟨i, _, rfl⟩, hmem⟩ <;>
    simp only [Formula.realization_and, Set.mem_inter_iff,
      realization_degFormula, Set.mem_setOf_eq] at hmem <;>
    exact hmem.1.trans hmem.2.symm
  · intro h
    match hd : (Q₁.map (MvPolynomial.aeval y).toRingHom).degree with
    | ⊥ =>
      refine ⟨_, Or.inl rfl, ?_⟩
      simp only [Formula.realization_and, Set.mem_inter_iff,
        realization_degFormula, Set.mem_setOf_eq]
      exact ⟨hd, h.symm.trans hd⟩
    | some n =>
      refine ⟨_, Or.inr ⟨n, ?_, rfl⟩, ?_⟩
      · simp only [Nat.lt_succ_iff]
        have hnd := Polynomial.natDegree_eq_of_degree_eq_some hd
        have hle : (Q₁.map (MvPolynomial.aeval y).toRingHom).natDegree ≤ Q₁.natDegree :=
          Polynomial.natDegree_map_le
        exact le_trans (by omega : n ≤ Q₁.natDegree) (le_max_left _ _)
      · simp only [Formula.realization_and, Set.mem_inter_iff,
          realization_degFormula, Set.mem_setOf_eq]
        exact ⟨hd, h.symm.trans hd⟩

/-! #### Partition property -/

/-- The `degFormula` family partitions `C^k`: every `y` satisfies
exactly one `degFormula Q i`. (Covering part.) -/
theorem degFormula_covering
    {C : Type*} [Field C] [Algebra D C]
    (Q : Polynomial (MvPolynomial (Fin k) D)) (y : Fin k → C) :
    ∃ i : WithBot ℕ, y ∈ (degFormula Q i).realization (C := C) := by
  simp only [realization_degFormula, Set.mem_setOf_eq]
  exact ⟨_, rfl⟩

/-- The `degFormula` family partitions `C^k`: distinct degree values
give disjoint realizations. (Disjointness part.) -/
theorem degFormula_disjoint
    {C : Type*} [Field C] [Algebra D C]
    (Q : Polynomial (MvPolynomial (Fin k) D)) (i j : WithBot ℕ) (hij : i ≠ j) :
    (degFormula Q i).realization (C := C) ∩
      (degFormula Q j).realization (C := C) = ∅ := by
  simp only [realization_degFormula]
  ext y; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro h; rw [h]; exact hij

end DegFormula

end Azurite.BPR
