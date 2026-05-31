import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_34
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_59
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_61

/-! # Sturm–Tarski machinery transfers along order-preserving embeddings

The signed remainder sequence, the sign-variation count `Var`, and the
sign-variation-at-a-point function `varAt` are all built out of *signs* of
field elements and out of Euclidean polynomial division. Both of these are
preserved by a field embedding `σ : K → K'`:

* Euclidean division commutes with `map σ` (`Polynomial.map_mod`), so the
  signed remainder sequence does too (`SRemS_map`, `SRemSList_map`);
* an order-preserving embedding preserves signs, so `Var` and `varAt` are
  unchanged when the underlying list/polynomials are pushed forward
  (`Var_map`, `varAt_map`, `varBetween_map`).

These are the foundational bricks for transferring Sturm–Tarski root counts
between two real closed fields related by an order-preserving embedding, used
in the proof that the real closure of an ordered field is unique.
-/

namespace Azurite.BPR

open _root_.Polynomial

variable {K K' : Type*} [Field K] [Field K']

namespace ExtendedPoint

/-- Transport an extended point along a ring hom, fixing the two infinities. -/
def map (σ : K →+* K') : ExtendedPoint K → ExtendedPoint K'
  | .finite a => .finite (σ a)
  | .posInf => .posInf
  | .negInf => .negInf

@[simp] lemma map_finite (σ : K →+* K') (a : K) :
    (ExtendedPoint.finite a).map σ = .finite (σ a) := rfl
@[simp] lemma map_posInf (σ : K →+* K') : (ExtendedPoint.posInf).map σ = .posInf := rfl
@[simp] lemma map_negInf (σ : K →+* K') : (ExtendedPoint.negInf).map σ = .negInf := rfl

end ExtendedPoint

/-! ## Signed remainder sequences transfer along field embeddings -/

/-- The signed remainder sequence commutes with `map σ`: since Euclidean
division does (`Polynomial.map_mod`), each step of the recursion is preserved. -/
theorem SRemS_map (σ : K →+* K') (P Q : K[X]) (n : ℕ) :
    SRemS (P.map σ) (Q.map σ) n = (SRemS P Q n).map σ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | m + 2 =>
      rw [SRemS, SRemS]
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      by_cases hz : SRemS P Q (m + 1) = 0
      · simp [h1, hz]
      · have : SRemS (P.map σ) (Q.map σ) (m + 1) ≠ 0 := by
          rw [h1]; simpa [Polynomial.map_eq_zero_iff σ.injective] using hz
        simp only [this, hz, if_false]
        rw [h0, h1, ← map_mod, Polynomial.map_neg]

/-- The list form of `SRemS_map`. -/
theorem SRemSList_map (σ : K →+* K') (P Q : K[X]) (n : ℕ) :
    SRemSList (P.map σ) (Q.map σ) n = (SRemSList P Q n).map (Polynomial.map σ) := by
  unfold SRemSList
  rw [List.map_map]
  exact List.map_congr_left (fun i _ => SRemS_map σ P Q i)

/-! ## `evalPoly`, `Var` and `varAt` transfer along order-preserving embeddings -/

private lemma leadingCoeff_map_inj (σ : K →+* K') (P : K[X]) :
    (P.map σ).leadingCoeff = σ P.leadingCoeff := by
  rw [leadingCoeff, leadingCoeff, natDegree_map_eq_of_injective σ.injective, coeff_map]

/-- Evaluation at an extended point commutes with `map σ` (for `σ` a field
embedding; injectivity is needed at `±∞` to preserve the leading coefficient
and degree). -/
lemma evalPoly_map (σ : K →+* K') (P : K[X]) (ep : ExtendedPoint K) :
    ExtendedPoint.evalPoly (P.map σ) (ep.map σ) = σ (ExtendedPoint.evalPoly P ep) := by
  cases ep with
  | finite a => simp [ExtendedPoint.evalPoly, eval_map_apply]
  | posInf => simp [ExtendedPoint.evalPoly]
  | negInf =>
    simp only [ExtendedPoint.map_negInf, ExtendedPoint.evalPoly,
      natDegree_map_eq_of_injective σ.injective, leadingCoeff_map_inj,
      map_mul, map_pow, map_neg, map_one]

variable [LinearOrder K] [LinearOrder K']

/-- `varNonzero` is unchanged by a strictly monotone embedding: the only test
performed is the sign of adjacent products, which `σ` preserves. -/
lemma varNonzero_map (σ : K →+* K') (hσ : StrictMono σ) :
    ∀ l : List K, varNonzero (l.map σ) = varNonzero l
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      have ih := varNonzero_map σ hσ (b :: rest)
      simp only [List.map_cons, varNonzero_cons_cons] at ih ⊢
      have hif : (σ a * σ b < 0) ↔ (a * b < 0) := by
        rw [← map_mul, ← map_zero σ, hσ.lt_iff_lt]
      rw [ih, if_congr hif rfl rfl]

/-- `Var` is unchanged by a strictly monotone embedding. -/
lemma Var_map (σ : K →+* K') (hσ : StrictMono σ) (l : List K) :
    Var (l.map σ) = Var l := by
  unfold Var
  rw [List.filter_map, varNonzero_map σ hσ]
  congr 1
  apply List.filter_congr
  intro x _
  simp [map_eq_zero_iff σ σ.injective]

/-- The sign-variation count of a polynomial sequence at an extended point is
unchanged when the sequence and the point are pushed forward along an
order-preserving embedding. -/
lemma varAt_map (σ : K →+* K') (hσ : StrictMono σ) (L : List K[X]) (ep : ExtendedPoint K) :
    varAt (L.map (Polynomial.map σ)) (ep.map σ) = varAt L ep := by
  have key : (L.map (Polynomial.map σ)).map (ExtendedPoint.evalPoly · (ep.map σ))
           = (L.map (ExtendedPoint.evalPoly · ep)).map σ := by
    simp only [List.map_map]
    exact List.map_congr_left (fun P _ => evalPoly_map σ P ep)
  unfold varAt
  rw [key, Var_map σ hσ]

/-- `varAt` at `−∞` is unchanged by an order-preserving embedding (specialized
form whose statement keeps the point as the bare constructor, so it rewrites
cleanly). -/
lemma varAt_map_negInf (σ : K →+* K') (hσ : StrictMono σ) (L : List K[X]) :
    varAt (L.map (Polynomial.map σ)) ExtendedPoint.negInf = varAt L ExtendedPoint.negInf :=
  varAt_map σ hσ L ExtendedPoint.negInf

/-- `varAt` at `+∞` is unchanged by an order-preserving embedding. -/
lemma varAt_map_posInf (σ : K →+* K') (hσ : StrictMono σ) (L : List K[X]) :
    varAt (L.map (Polynomial.map σ)) ExtendedPoint.posInf = varAt L ExtendedPoint.posInf :=
  varAt_map σ hσ L ExtendedPoint.posInf

/-- `varBetween` is unchanged by an order-preserving embedding. -/
lemma varBetween_map (σ : K →+* K') (hσ : StrictMono σ) (L : List K[X])
    (a b : ExtendedPoint K) :
    varBetween (L.map (Polynomial.map σ)) (a.map σ) (b.map σ) = varBetween L a b := by
  unfold varBetween
  rw [varAt_map σ hσ, varAt_map σ hσ]

/-! ## Tarski queries transfer along order-preserving embeddings -/

private lemma evalPoly_negInf_ne_zero {R : Type*} [Field R] (P : R[X]) (hP : P ≠ 0) :
    ExtendedPoint.evalPoly P .negInf ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hP)

private lemma evalPoly_posInf_ne_zero {R : Type*} [Field R] (P : R[X]) (hP : P ≠ 0) :
    ExtendedPoint.evalPoly P .posInf ≠ 0 := leadingCoeff_ne_zero.mpr hP

/-- Over a field with the intermediate value property, the full-line Tarski
query of pushed-forward `F`-polynomials equals the purely `F`-side `varBetween`
of the signed remainder sequence — a quantity that depends only on the
coefficients of `P` and `Q`. -/
lemma tarskiQuery_map_eq_varBetween
    {F R : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hR : HasIntermediateValueProperty R) (ι : F →+* R) (hι : StrictMono ι)
    (P Q : F[X]) (hP : P ≠ 0) :
    tarskiQuery (Q.map ι) (P.map ι) =
      varBetween (SRemSList P (P.derivative * Q) ((P.derivative * Q).natDegree + 2))
        .negInf .posInf := by
  have hPι : P.map ι ≠ 0 := by simpa [Polynomial.map_eq_zero_iff ι.injective] using hP
  have hpoly : (P.map ι).derivative * Q.map ι = (P.derivative * Q).map ι := by
    rw [derivative_map, Polynomial.map_mul]
  have hdeg : ((P.map ι).derivative * Q.map ι).natDegree = (P.derivative * Q).natDegree := by
    rw [hpoly, natDegree_map_eq_of_injective ι.injective]
  rw [tarskiQuery, ← theorem_2_61 hR (P.map ι) (Q.map ι) hPι .negInf .posInf (by trivial)
    (evalPoly_negInf_ne_zero _ hPι) (evalPoly_posInf_ne_zero _ hPι)]
  rw [hdeg, hpoly, SRemSList_map]
  unfold varBetween
  rw [varAt_map_negInf ι hι, varAt_map_posInf ι hι]

/-- **Sturm–Tarski transfer.** For `P, Q ∈ F[X]` with `P ≠ 0` and two
order-preserving embeddings of the ordered field `F` into fields `R, R'` with
the intermediate value property, the full-line Tarski queries agree: both sides
reduce to the same `F`-side signed-remainder-sequence sign count, computed from
the coefficients of `P` and `Q`. This is the engine behind the uniqueness of
the real closure. -/
theorem tarskiQuery_transfer
    {F R R' : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field R'] [LinearOrder R'] [IsStrictOrderedRing R']
    (hR : HasIntermediateValueProperty R) (hR' : HasIntermediateValueProperty R')
    (ι : F →+* R) (hι : StrictMono ι) (τ : F →+* R') (hτ : StrictMono τ)
    (P Q : F[X]) (hP : P ≠ 0) :
    tarskiQuery (Q.map ι) (P.map ι) = tarskiQuery (Q.map τ) (P.map τ) := by
  rw [tarskiQuery_map_eq_varBetween hR ι hι P Q hP,
      tarskiQuery_map_eq_varBetween hR' τ hτ P Q hP]

/-- The full-line Tarski query of the constant `1` counts the distinct roots:
every root contributes `sign(1) = +1`. -/
lemma tarskiQuery_one {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (P : R[X]) : tarskiQuery (1 : R[X]) P = (P.roots.toFinset.card : ℤ) := by
  classical
  have hfilter : P.roots.toFinset.filter
      (· ∈ ExtendedPoint.openInterval (R := R) .negInf .posInf) = P.roots.toFinset :=
    Finset.filter_true_of_mem (fun x _ => Set.mem_univ x)
  simp only [tarskiQuery, tarskiQueryOn, eval_one, sign_one, SignType.coe_one,
    Finset.sum_const, nsmul_eq_mul, mul_one, hfilter]

/-- **Distinct root counts transfer.** A polynomial over the ordered field `F`
has the same number of distinct roots in any two order-preserving extensions
with the intermediate value property. (Instance of `tarskiQuery_transfer` with
`Q = 1`.) -/
lemma card_roots_transfer
    {F R R' : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field R'] [LinearOrder R'] [IsStrictOrderedRing R']
    (hR : HasIntermediateValueProperty R) (hR' : HasIntermediateValueProperty R')
    (ι : F →+* R) (hι : StrictMono ι) (τ : F →+* R') (hτ : StrictMono τ)
    (P : F[X]) (hP : P ≠ 0) :
    (P.map ι).roots.toFinset.card = (P.map τ).roots.toFinset.card := by
  have h := tarskiQuery_transfer hR hR' ι hι τ hτ P 1 hP
  simp only [Polynomial.map_one, tarskiQuery_one] at h
  exact_mod_cast h

end Azurite.BPR
