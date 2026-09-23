import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveDifferentiable
import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveTopology
import Azurite.BasuPollackRoy.Chapter4.Section4_7.ChartTransition
import Azurite.BasuPollackRoy.Chapter3.Section3_5.SClassClosure
import Azurite.BasuPollackRoy.Chapter3.Section3_5.InverseSmoothness
import Azurite.BasuPollackRoy.Chapter3.Section3_5.Theorem_3_25

/-!
# BPR §4.7, Theorem 4.104 — infrastructure for the Projective Implicit Function Theorem

Theorem 4.104 is the projective analogue of the affine implicit function theorem (Theorem 3.25),
obtained by reducing to the affine theorem in a single pair of charts via the realification
`Cⁿ = R^{2n}`. This file develops the reusable smoothness toolkit underlying that reduction:

* `isSFunction_evalMvPoly` — a real polynomial evaluation is `𝒮^m`;
* `isSFunction_comp_reindex` — the domain-reindexing chain rule for `𝒮^m`;
* `Ri.reL_inv` / `Ri.imL_inv` — the real and imaginary parts of a reciprocal in `Ri R`;
* the field algebra of `IsSFunctionC` / `IsSFunctionCC` (constants, coordinates, real/imaginary
  parts, `+`, `-`, `*`, and `⁻¹` where nonvanishing);
* `isSFunctionCC_transitionMap_coord` / `isSClassMap_transitionMap` — **the crux**: each chart
  transition map `φⱼ⁻¹ ∘ φᵢ` is `𝒮^m` on the (realified) overlap, which makes the classes `𝒮^m`
  chart-independent and bridges the affine theorem across charts.
-/

namespace Azurite.BPR.Chapter4

open Azurite.BPR (IsSFunction IsSemialgContinuousOn HasPartialDerivAtIn)

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Evaluation of a real polynomial is `𝒮^m` -/

/-- Evaluation `w ↦ eval w Q` of a fixed real multivariate polynomial is of class `𝒮^m` on any
semialgebraic set, for every order `m`. (Built from coordinates, constants, sums, products.) -/
theorem isSFunction_evalMvPoly {n : ℕ} {U : Set (Fin n → R)} (hU : IsSemialgebraicSet U)
    (Q : MvPolynomial (Fin n) R) (m : ℕ) :
    IsSFunction m U (fun w => eval w Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simpa only [eval_C] using Azurite.BPR.isSFunction_const hU a m
  | add P P' ihP ihP' =>
    simpa only [eval_add] using Azurite.BPR.IsSFunction.add' hU ihP ihP'
  | mul_X P j ih =>
    have : (fun w : Fin n → R => eval w (P * X j))
        = fun w => (eval w P) * (fun w => w j) w := by
      funext w; rw [eval_mul, eval_X]
    rw [this]
    exact Azurite.BPR.IsSFunction.mul' hU ih (Azurite.BPR.isSFunction_coord hU j m)

/-- **Domain reindexing for `𝒮^ℓ`.** If `c ∈ 𝒮^ℓ(U)` on an open semialgebraic `U ⊆ R^p` and
`σ : Fin q → Fin p`, then `w ↦ c (w ∘ σ)` is `𝒮^ℓ` on the (semialgebraic) preimage
`{w | w ∘ σ ∈ U}`. Built from the chain rule, since each component `w ↦ (w ∘ σ) m = w (σ m)` is a
coordinate. -/
theorem isSFunction_comp_reindex {p q ℓ : ℕ} [Nonempty (Fin p)] {U : Set (Fin p → R)}
    (hUopen : IsOpen U) (hUsa : IsSemialgebraicSet U) (σ : Fin p → Fin q)
    {c : (Fin p → R) → R} (hc : IsSFunction ℓ U c) :
    IsSFunction ℓ {w : Fin q → R | (fun m => w (σ m)) ∈ U} (fun w => c (fun m => w (σ m))) := by
  set V : Set (Fin q → R) := {w : Fin q → R | (fun m => w (σ m)) ∈ U} with hV
  have hVsa : IsSemialgebraicSet V :=
    Azurite.BPR.IsSemialgebraicSet.comap σ hUsa
  have hmaps : Set.MapsTo (fun w : Fin q → R => fun m => w (σ m)) V U := fun w hw => hw
  exact Azurite.BPR.isSFunction_comp hVsa hUopen hmaps hc
    (fun m => Azurite.BPR.isSFunction_coord hVsa (σ m) ℓ)

/-! ### Real and imaginary parts of a reciprocal in `Ri R` -/

set_option linter.unusedSectionVars false in
/-- The conjugate-product identity for scalars `a, b : R`. -/
theorem Ri.of_mul_conj (a b : R) :
    (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a
        + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b * Ri.i R)
      * (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) a
        - AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) b * Ri.i R)
      = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (a * a + b * b) := by
  have hi2 : Ri.i R ^ 2 = -1 := Ri.i_sq R
  rw [map_add, map_mul, map_mul]
  ring_nf
  rw [hi2]; ring

/-- For `c ∈ Ri R`, `c * (of (Re c) - of (Im c)·i) = of (Re c² + Im c²)`. -/
theorem Ri.mul_conj_eq (c : Ri R) :
    c * (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
          - AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R)
      = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R)
          (Ri.reL c * Ri.reL c + Ri.imL c * Ri.imL c) := by
  conv_lhs => lhs; rw [show c = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
      + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R from
        (Ri.of_reL_add_of_imL_mul_i c).symm]
  exact Ri.of_mul_conj (Ri.reL c) (Ri.imL c)

/-- The reciprocal `c⁻¹` written as `conj(c) · (Re c² + Im c²)⁻¹`. -/
theorem Ri.inv_eq_conj_mul (c : Ri R) (hc : c ≠ 0) :
    c⁻¹ = (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
          - AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R)
        * AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R)
            (Ri.reL c * Ri.reL c + Ri.imL c * Ri.imL c)⁻¹ := by
  set q := Ri.reL c * Ri.reL c + Ri.imL c * Ri.imL c with hq
  have hqne : q ≠ 0 := by
    intro h0
    apply hc
    rw [reL_eq_zero_and_imL_eq_zero_iff]
    constructor <;> nlinarith [mul_self_nonneg (Ri.reL c), mul_self_nonneg (Ri.imL c)]
  have hmul : c * ((AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
          - AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R)
        * AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) q⁻¹) = 1 := by
    rw [← mul_assoc, Ri.mul_conj_eq, ← map_mul, mul_inv_cancel₀ hqne, map_one]
  exact inv_eq_of_mul_eq_one_right hmul

/-- The real part of `c⁻¹` is `Re c · (Re c² + Im c²)⁻¹`. -/
theorem Ri.reL_inv (c : Ri R) (hc : c ≠ 0) :
    Ri.reL (c⁻¹) = Ri.reL c * (Ri.reL c * Ri.reL c + Ri.imL c * Ri.imL c)⁻¹ := by
  rw [Ri.inv_eq_conj_mul c hc]
  rw [show (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
        - AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R)
        * AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R)
            (Ri.reL c * Ri.reL c + Ri.imL c * Ri.imL c)⁻¹
      = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R)
          (Ri.reL c * (Ri.reL c * Ri.reL c + Ri.imL c * Ri.imL c)⁻¹)
        + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R)
          (-(Ri.imL c) * (Ri.reL c * Ri.reL c + Ri.imL c * Ri.imL c)⁻¹) * Ri.i R from by
      simp only [map_neg, map_mul]; ring]
  rw [Ri.reL_lin]

/-- The imaginary part of `c⁻¹` is `-Im c · (Re c² + Im c²)⁻¹`. -/
theorem Ri.imL_inv (c : Ri R) (hc : c ≠ 0) :
    Ri.imL (c⁻¹) = -(Ri.imL c) * (Ri.reL c * Ri.reL c + Ri.imL c * Ri.imL c)⁻¹ := by
  rw [Ri.inv_eq_conj_mul c hc]
  rw [show (AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.reL c)
        - AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R) (Ri.imL c) * Ri.i R)
        * AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R)
            (Ri.reL c * Ri.reL c + Ri.imL c * Ri.imL c)⁻¹
      = AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R)
          (Ri.reL c * (Ri.reL c * Ri.reL c + Ri.imL c * Ri.imL c)⁻¹)
        + AdjoinRoot.of (Polynomial.X ^ 2 + 1 : Polynomial R)
          (-(Ri.imL c) * (Ri.reL c * Ri.reL c + Ri.imL c * Ri.imL c)⁻¹) * Ri.i R from by
      simp only [map_neg, map_mul]; ring]
  rw [Ri.imL_lin]

/-! ### Field algebra of `IsSFunctionC` / `IsSFunctionCC`

We record that, on a semialgebraic domain (realified to a semialgebraic subset of `R^{2n}`), the
classes `IsSFunctionC` (real-valued, `𝒮^m`) and `IsSFunctionCC` (`C`-valued, `𝒮^m`) are closed
under the relevant operations: constants, coordinates, real/imaginary parts, addition,
multiplication, and reciprocals where the value is nonzero. This is the toolkit that makes the
chart-transition maps `𝒮^m`. -/

variable {n : ℕ}

/-- A real-valued `IsSFunctionC` function is `𝒮^m` provided its realified domain is semialgebraic
(the underlying `IsSFunction` carries the data). -/
theorem isSFunctionC_iff {m : ℕ} {U : Set (Fin n → Ri R)} {c : (Fin n → Ri R) → R} :
    IsSFunctionC m U c ↔ IsSFunction m (realEquiv '' U) (fun w => c (realEquiv.symm w)) :=
  Iff.rfl

/-- Constants are `IsSFunctionC` for every order. -/
theorem isSFunctionC_const {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) (a : R) :
    IsSFunctionC m U (fun _ => a) :=
  Azurite.BPR.isSFunction_const hU a m

/-- The real part of the `a`-th coordinate is `IsSFunctionC`. -/
theorem isSFunctionC_reL_coord {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) (a : Fin n) :
    IsSFunctionC m U (fun z => Ri.reL (z a)) := by
  have heq : (fun w : Fin (n + n) → R => Ri.reL ((realEquiv.symm w) a))
      = fun w => w (Fin.castAdd n a) := by
    funext w; rw [reL_symm_apply]
  rw [isSFunctionC_iff, heq]
  exact Azurite.BPR.isSFunction_coord hU (Fin.castAdd n a) m

/-- The imaginary part of the `a`-th coordinate is `IsSFunctionC`. -/
theorem isSFunctionC_imL_coord {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) (a : Fin n) :
    IsSFunctionC m U (fun z => Ri.imL (z a)) := by
  have heq : (fun w : Fin (n + n) → R => Ri.imL ((realEquiv.symm w) a))
      = fun w => w (Fin.natAdd n a) := by
    funext w; rw [imL_symm_apply]
  rw [isSFunctionC_iff, heq]
  exact Azurite.BPR.isSFunction_coord hU (Fin.natAdd n a) m

/-- Sum closure for `IsSFunctionC`. -/
theorem IsSFunctionC.add {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) {c d : (Fin n → Ri R) → R}
    (hc : IsSFunctionC m U c) (hd : IsSFunctionC m U d) :
    IsSFunctionC m U (fun z => c z + d z) :=
  Azurite.BPR.IsSFunction.add' hU hc hd

/-- Negation closure for `IsSFunctionC`. -/
theorem IsSFunctionC.neg {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) {c : (Fin n → Ri R) → R}
    (hc : IsSFunctionC m U c) :
    IsSFunctionC m U (fun z => -(c z)) :=
  Azurite.BPR.IsSFunction.neg' hU hc

/-- Subtraction closure for `IsSFunctionC`. -/
theorem IsSFunctionC.sub {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) {c d : (Fin n → Ri R) → R}
    (hc : IsSFunctionC m U c) (hd : IsSFunctionC m U d) :
    IsSFunctionC m U (fun z => c z - d z) := by
  have heq : (fun z : Fin n → Ri R => c z - d z) = fun z => c z + (-(d z)) := by
    funext z; ring
  rw [heq]
  exact hc.add hU (hd.neg hU)

/-- Product closure for `IsSFunctionC`. -/
theorem IsSFunctionC.mul {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) {c d : (Fin n → Ri R) → R}
    (hc : IsSFunctionC m U c) (hd : IsSFunctionC m U d) :
    IsSFunctionC m U (fun z => c z * d z) :=
  Azurite.BPR.IsSFunction.mul' hU hc hd

/-- Reciprocal closure for `IsSFunctionC`, where the function is nonvanishing on `U`. -/
theorem IsSFunctionC.inv {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) {c : (Fin n → Ri R) → R}
    (hc : IsSFunctionC m U c) (hne : ∀ z ∈ U, c z ≠ 0) :
    IsSFunctionC m U (fun z => (c z)⁻¹) := by
  refine Azurite.BPR.IsSFunction.inv' hU hc ?_
  rintro w ⟨z, hz, rfl⟩
  rw [Equiv.symm_apply_apply]
  exact hne z hz

/-- `IsSFunctionCC`: constants. -/
theorem isSFunctionCC_const {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) (a : Ri R) :
    IsSFunctionCC m U (fun _ => a) :=
  ⟨isSFunctionC_const hU _, isSFunctionC_const hU _⟩

/-- `IsSFunctionCC`: the `a`-th coordinate function. -/
theorem isSFunctionCC_coord {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) (a : Fin n) :
    IsSFunctionCC m U (fun z => z a) :=
  ⟨isSFunctionC_reL_coord hU a, isSFunctionC_imL_coord hU a⟩

/-- `IsSFunctionCC`: addition. -/
theorem IsSFunctionCC.add {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) {c d : (Fin n → Ri R) → Ri R}
    (hc : IsSFunctionCC m U c) (hd : IsSFunctionCC m U d) :
    IsSFunctionCC m U (fun z => c z + d z) := by
  refine ⟨?_, ?_⟩
  · have heq : (fun z : Fin n → Ri R => Ri.reL (c z + d z))
        = fun z => Ri.reL (c z) + Ri.reL (d z) := by funext z; rw [map_add]
    rw [heq]; exact hc.1.add hU hd.1
  · have heq : (fun z : Fin n → Ri R => Ri.imL (c z + d z))
        = fun z => Ri.imL (c z) + Ri.imL (d z) := by funext z; rw [map_add]
    rw [heq]; exact hc.2.add hU hd.2

/-- `IsSFunctionCC`: multiplication (real and imaginary parts via `reL_mul`/`imL_mul`). -/
theorem IsSFunctionCC.mul {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) {c d : (Fin n → Ri R) → Ri R}
    (hc : IsSFunctionCC m U c) (hd : IsSFunctionCC m U d) :
    IsSFunctionCC m U (fun z => c z * d z) := by
  refine ⟨?_, ?_⟩
  · have heq : (fun z : Fin n → Ri R => Ri.reL (c z * d z))
        = fun z => Ri.reL (c z) * Ri.reL (d z) - Ri.imL (c z) * Ri.imL (d z) := by
      funext z; rw [reL_mul]
    rw [heq]
    exact (hc.1.mul hU hd.1).sub hU (hc.2.mul hU hd.2)
  · have heq : (fun z : Fin n → Ri R => Ri.imL (c z * d z))
        = fun z => Ri.reL (c z) * Ri.imL (d z) + Ri.imL (c z) * Ri.reL (d z) := by
      funext z; rw [imL_mul]
    rw [heq]
    exact (hc.1.mul hU hd.2).add hU (hc.2.mul hU hd.1)

/-- `IsSFunctionCC`: reciprocal where nonvanishing. The reciprocal is
`c⁻¹ = (Re c - i Im c)/(Re c² + Im c²)` with nonvanishing denominator `|c|²`. -/
theorem IsSFunctionCC.inv {m : ℕ} {U : Set (Fin n → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) {c : (Fin n → Ri R) → Ri R}
    (hc : IsSFunctionCC m U c) (hne : ∀ z ∈ U, c z ≠ 0) :
    IsSFunctionCC m U (fun z => (c z)⁻¹) := by
  -- the squared modulus `Re c ^2 + Im c ^2` is `𝒮^m` and nonvanishing
  set q : (Fin n → Ri R) → R := fun z => Ri.reL (c z) * Ri.reL (c z) + Ri.imL (c z) * Ri.imL (c z)
    with hq
  have hqS : IsSFunctionC m U q := (hc.1.mul hU hc.1).add hU (hc.2.mul hU hc.2)
  have hqne : ∀ z ∈ U, q z ≠ 0 := by
    intro z hz
    rw [hq]
    have hcz : c z ≠ 0 := hne z hz
    -- `Re c ^2 + Im c ^2 = 0 → c = 0`
    intro h0
    apply hcz
    rw [reL_eq_zero_and_imL_eq_zero_iff]
    have hre : Ri.reL (c z) * Ri.reL (c z) ≥ 0 := mul_self_nonneg _
    have him : Ri.imL (c z) * Ri.imL (c z) ≥ 0 := mul_self_nonneg _
    constructor
    · nlinarith [mul_self_nonneg (Ri.reL (c z)), mul_self_nonneg (Ri.imL (c z))]
    · nlinarith [mul_self_nonneg (Ri.reL (c z)), mul_self_nonneg (Ri.imL (c z))]
  have hqinv : IsSFunctionC m U (fun z => (q z)⁻¹) := hqS.inv hU hqne
  refine ⟨?_, ?_⟩
  · -- `Re (c⁻¹) = Re c · q⁻¹`
    have heq : (fun w : Fin (n + n) → R => Ri.reL ((c (realEquiv.symm w))⁻¹))
        = fun w => Ri.reL (c (realEquiv.symm w)) * (q (realEquiv.symm w))⁻¹ := by
      funext w
      rcases eq_or_ne (c (realEquiv.symm w)) 0 with h0 | hcz
      · simp [h0]
      · rw [Ri.reL_inv _ hcz]
    rw [isSFunctionC_iff, heq]
    exact (hc.1.mul hU hqinv : IsSFunctionC m U (fun z => Ri.reL (c z) * (q z)⁻¹))
  · -- `Im (c⁻¹) = -Im c · q⁻¹`
    have heq : (fun w : Fin (n + n) → R => Ri.imL ((c (realEquiv.symm w))⁻¹))
        = fun w => -(Ri.imL (c (realEquiv.symm w))) * (q (realEquiv.symm w))⁻¹ := by
      funext w
      rcases eq_or_ne (c (realEquiv.symm w)) 0 with h0 | hcz
      · simp [h0]
      · rw [Ri.imL_inv _ hcz]
    rw [isSFunctionC_iff, heq]
    exact ((hc.2.neg hU).mul hU hqinv : IsSFunctionC m U (fun z => -(Ri.imL (c z)) * (q z)⁻¹))

/-! ### Transition smoothness (the crux infrastructure)

The chart-transition map `φⱼ⁻¹ ∘ φᵢ = transitionMap i j` is `𝒮^m` on the (realified) overlap: each
output coordinate is `num / denom` of homogeneous coordinates, where `num` and `denom` are each
either the constant `1` or one of the affine coordinates `x_a` (both `IsSFunctionCC`), and the
denominator is nonzero on the overlap. -/

variable {k : ℕ}

/-- The `c`-th entry of `insertNth i 1 x` is `IsSFunctionCC` on any (realified-)semialgebraic
domain: it is the constant `1` (when `c = i`) or a coordinate (when `c = i.succAbove a`). -/
theorem isSFunctionCC_insertNth_one {m : ℕ} {U : Set (Fin k → Ri R)}
    (hU : IsSemialgebraicSet (realEquiv '' U)) (i c : Fin (k + 1)) :
    IsSFunctionCC m U (fun x => (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) c) := by
  refine Fin.succAboveCases i ?_ (fun a => ?_) c
  · have heq : (fun x : Fin k → Ri R =>
        (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) i) = fun _ => (1 : Ri R) := by
      funext x; rw [Fin.insertNth_apply_same]
    rw [heq]; exact isSFunctionCC_const hU 1
  · have heq : (fun x : Fin k → Ri R =>
        (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) (i.succAbove a))
        = fun x => x a := by
      funext x; rw [Fin.insertNth_apply_succAbove]
    rw [heq]; exact isSFunctionCC_coord hU a

/-- Each output coordinate of the transition map `transitionMap i j` is `IsSFunctionCC` on the
(realified) overlap `φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ)`. -/
theorem isSFunctionCC_transitionMap_coord {m : ℕ} (i j : Fin (k + 1)) (b : Fin k) :
    IsSFunctionCC m (chartOverlap i j : Set (Fin k → Ri R))
      (fun x => transitionMap i j x b) := by
  have hU : IsSemialgebraicSet (realEquiv '' (chartOverlap i j : Set (Fin k → Ri R))) :=
    isSemialgebraicSetC_chartOverlap i j
  -- the denominator `(insertNth i 1 x) j` is nonzero on the overlap
  have hden : IsSFunctionCC m (chartOverlap i j : Set (Fin k → Ri R))
      (fun x => (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j) :=
    isSFunctionCC_insertNth_one hU i j
  have hnum : IsSFunctionCC m (chartOverlap i j : Set (Fin k → Ri R))
      (fun x => (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) (j.succAbove b)) :=
    isSFunctionCC_insertNth_one hU i (j.succAbove b)
  have hdenne : ∀ x ∈ (chartOverlap i j : Set (Fin k → Ri R)),
      (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j ≠ 0 := by
    intro x hx
    rw [chartOverlap_eq, Set.mem_ofPred_eq] at hx
    exact hx
  have heq : (fun x : Fin k → Ri R => transitionMap i j x b)
      = fun x => (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) (j.succAbove b)
          * ((Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j)⁻¹ := by
    funext x; rw [transitionMap, div_eq_mul_inv]
  rw [heq]
  exact hnum.mul hU (hden.inv hU hdenne)

/-! ### Transition-invariance of the `𝒮^m` classes on projective space

Combining the per-coordinate transition smoothness above with the domain-reindexing chain rule
`isSFunction_comp_reindex`, the chart-change of `𝒮^m` data is again `𝒮^m`: this is what makes
`IsSClassMapP` / `IsSFunctionPP` chart-independent and is the bridge needed to transport the affine
implicit function theorem (Theorem 3.25) between charts in Theorem 4.104. -/

/-- The transition map `transitionMap i j` is `𝒮^m` on the (realified) overlap, packaged as an
`IsSFunctionCC` for each output coordinate. (Restatement of
`isSFunctionCC_transitionMap_coord` emphasizing it as the chart-change smoothness datum.) -/
theorem isSClassMap_transitionMap {m : ℕ} (i j : Fin (k + 1)) :
    ∀ b : Fin k, IsSFunctionCC m (chartOverlap i j : Set (Fin k → Ri R))
      (fun x => transitionMap i j x b) :=
  fun b => isSFunctionCC_transitionMap_coord i j b

/-! ### STEP 1 — projection over a complex block is semialgebraic over `C` -/

/-- The permutation crossing the two real-layouts of an `append`: `realEquiv (append a b)` has the
real-block layout `[Re a | Re b | Im a | Im b]`, whereas `append (realEquiv a) (realEquiv b)` has
`[Re a | Im a | Re b | Im b]`. `appendReindex` reorders the second into the first. -/
def appendReindex (k ℓ : ℕ) : Fin ((k + ℓ) + (k + ℓ)) → Fin ((k + k) + (ℓ + ℓ)) :=
  fun i => Fin.addCases
    (fun u : Fin (k + ℓ) => Fin.addCases
      (fun a : Fin k => Fin.castAdd (ℓ + ℓ) (Fin.castAdd k a))
      (fun b : Fin ℓ => Fin.natAdd (k + k) (Fin.castAdd ℓ b)) u)
    (fun u : Fin (k + ℓ) => Fin.addCases
      (fun a : Fin k => Fin.castAdd (ℓ + ℓ) (Fin.natAdd k a))
      (fun b : Fin ℓ => Fin.natAdd (k + k) (Fin.natAdd ℓ b)) u)
    i

set_option linter.unusedSectionVars false in
/-- The key re-block identity: realifying an `append` equals the `append` of the realifications,
post-composed with the reordering `appendReindex`. -/
theorem realEquiv_append {k ℓ : ℕ} (a : Fin k → Ri R) (b : Fin ℓ → Ri R) :
    realEquiv (Fin.append a b)
      = Fin.append (realEquiv a) (realEquiv b) ∘ appendReindex k ℓ := by
  funext i
  refine Fin.addCases (fun u => ?_) (fun u => ?_) i
  · -- the `castAdd` (real) block of `realEquiv (append a b)`
    rw [realEquiv_apply_castAdd]
    refine Fin.addCases (fun A => ?_) (fun B => ?_) u
    · simp only [Function.comp_apply, appendReindex, Fin.addCases_left, Fin.append_left,
        realEquiv_apply_castAdd]
    · simp only [Function.comp_apply, appendReindex, Fin.addCases_left, Fin.addCases_right,
        Fin.append_right, realEquiv_apply_castAdd]
  · -- the `natAdd` (imaginary) block of `realEquiv (append a b)`
    rw [realEquiv_apply_natAdd]
    refine Fin.addCases (fun A => ?_) (fun B => ?_) u
    · simp only [Function.comp_apply, appendReindex, Fin.addCases_right, Fin.addCases_left,
        Fin.append_left, realEquiv_apply_natAdd]
    · simp only [Function.comp_apply, appendReindex, Fin.addCases_right, Fin.append_right,
        realEquiv_apply_natAdd]

set_option linter.unusedSectionVars false in
/-- **STEP 1.** Projection over a complex block preserves semialgebraicity over `C`: for
`W ⊆ C^{k+ℓ}` semialgebraic over `C`, the projection `{x | ∃ y, append x y ∈ W}` is semialgebraic
over `C`. -/
theorem IsSemialgebraicSetC.exists_append {k ℓ : ℕ} {W : Set (Fin (k + ℓ) → Ri R)}
    (hW : IsSemialgebraicSetC W) :
    IsSemialgebraicSetC {x : Fin k → Ri R | ∃ y : Fin ℓ → Ri R, Fin.append x y ∈ W} := by
  -- realified comap of `W` along the reindexing
  have hcomap : IsSemialgebraicSet
      {u : Fin ((k + k) + (ℓ + ℓ)) → R | u ∘ appendReindex k ℓ ∈ realEquiv '' W} :=
    IsSemialgebraicSet.comap (appendReindex k ℓ) hW
  rw [IsSemialgebraicSetC]
  have hset : realEquiv '' {x : Fin k → Ri R | ∃ y : Fin ℓ → Ri R, Fin.append x y ∈ W}
      = {w : Fin (k + k) → R | ∃ v : Fin (ℓ + ℓ) → R,
          Fin.append w v ∈ {u : Fin ((k + k) + (ℓ + ℓ)) → R |
            u ∘ appendReindex k ℓ ∈ realEquiv '' W}} := by
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨y, hxy⟩, rfl⟩
      refine ⟨realEquiv y, ?_⟩
      show (Fin.append (realEquiv x) (realEquiv y)) ∘ appendReindex k ℓ ∈ realEquiv '' W
      refine ⟨Fin.append x y, hxy, ?_⟩
      rw [realEquiv_append]
    · rintro ⟨v, hv⟩
      obtain ⟨z, hzW, hzu⟩ :
          ∃ z ∈ W, realEquiv z = (Fin.append w v) ∘ appendReindex k ℓ := hv
      refine ⟨realEquiv.symm w, ⟨realEquiv.symm v, ?_⟩, by rw [Equiv.apply_symm_apply]⟩
      have hkey : realEquiv (Fin.append (realEquiv.symm w) (realEquiv.symm v))
          = Fin.append w v ∘ appendReindex k ℓ := by
        rw [realEquiv_append, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      have heq : realEquiv (Fin.append (realEquiv.symm w) (realEquiv.symm v)) = realEquiv z := by
        rw [hkey, hzu]
      have := realEquiv.injective heq
      rwa [this]
  rw [hset]
  exact hcomap.exists_append_right

/-! ### STEP 2 — preimage under a semialgebraic-over-`C` map -/

set_option linter.unusedSectionVars false in
/-- `(append x y) ∘ castAdd = x` for complex tuples. -/
theorem append_comp_castAdd' {k ℓ : ℕ} (x : Fin k → Ri R) (y : Fin ℓ → Ri R) :
    Fin.append x y ∘ Fin.castAdd ℓ = x := by funext i; simp [Fin.append_left]

set_option linter.unusedSectionVars false in
/-- `(append x y) ∘ natAdd = y` for complex tuples. -/
theorem append_comp_natAdd' {k ℓ : ℕ} (x : Fin k → Ri R) (y : Fin ℓ → Ri R) :
    Fin.append x y ∘ Fin.natAdd k = y := by funext j; simp [Fin.append_right]

set_option linter.unusedSectionVars false in
/-- **STEP 2.** For a map `f` semialgebraic over `C` on `D` and a target `S` semialgebraic over `C`,
the relative preimage `{x ∈ D | f x ∈ S} = D ∩ f ⁻¹' S` is semialgebraic over `C`. -/
theorem IsSemialgebraicFunctionC.preimage {k ℓ : ℕ} {D : Set (Fin k → Ri R)}
    {f : (Fin k → Ri R) → (Fin ℓ → Ri R)} (hf : IsSemialgebraicFunctionC D f)
    {S : Set (Fin ℓ → Ri R)} (hS : IsSemialgebraicSetC S) :
    IsSemialgebraicSetC {x : Fin k → Ri R | x ∈ D ∧ f x ∈ S} := by
  have hgraph : IsSemialgebraicSetC
      (complexFunGraph D f ∩ {p : Fin (k + ℓ) → Ri R | p ∘ Fin.natAdd k ∈ S}) :=
    IsSemialgebraicSetC.inter hf (IsSemialgebraicSetC.comap (Fin.natAdd k) hS)
  have hproj := IsSemialgebraicSetC.exists_append hgraph
  have hset : {x : Fin k → Ri R | x ∈ D ∧ f x ∈ S}
      = {x : Fin k → Ri R | ∃ y : Fin ℓ → Ri R,
          Fin.append x y ∈ (complexFunGraph D f ∩ {p | p ∘ Fin.natAdd k ∈ S})} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_complexFunGraph]
    constructor
    · rintro ⟨hxD, hfxS⟩
      refine ⟨f x, ⟨?_, ?_⟩, ?_⟩
      · rw [append_comp_castAdd']; exact hxD
      · rw [append_comp_castAdd', append_comp_natAdd']
      · rw [append_comp_natAdd']; exact hfxS
    · rintro ⟨y, ⟨hxD, hfx⟩, hyS⟩
      rw [append_comp_castAdd'] at hxD hfx
      rw [append_comp_natAdd'] at hfx hyS
      exact ⟨hxD, hfx ▸ hyS⟩
  rw [hset]; exact hproj

/-! ### STEP 3 — the chart image of a semialgebraic-over-`C` set is semialgebraic and open in `ℙ_k(C)` -/

variable {k : ℕ}

/-- The projective set carved out of chart `i₀` by an affine condition `U₀ ⊆ Cᵏ`: the points of
`𝒰_{i₀}` whose `i₀`-chart coordinates lie in `U₀`. -/
def chartImageP (i₀ : Fin (k + 1)) (U₀ : Set (Fin k → Ri R)) :
    Set (complexProjectiveSpace R k) :=
  {p : complexProjectiveSpace R k | p ∈ chartSet i₀ ∧ chartInv i₀ p ∈ U₀}

set_option linter.unusedSectionVars false in
/-- `chartMap m x ∈ chartSet i₀ ↔ x ∈ chartOverlap m i₀`. -/
theorem chartMap_mem_chartSet_iff (m i₀ : Fin (k + 1)) (x : Fin k → Ri R) :
    chartMap m x ∈ (chartSet i₀ : Set (complexProjectiveSpace R k))
      ↔ x ∈ (chartOverlap m i₀ : Set (Fin k → Ri R)) := by
  rw [chartOverlap, Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨Set.mem_range_self x, h⟩
  · intro h; exact h.2

set_option linter.unusedSectionVars false in
/-- The chart-`m` pullback of `chartImageP i₀ U₀`: it is the overlap `φₘ⁻¹(𝒰ₘ ∩ 𝒰_{i₀})` intersected
with the preimage of `U₀` under the transition map `φ_{i₀}⁻¹ ∘ φₘ`. -/
theorem chartMap_preimage_chartImageP (i₀ m : Fin (k + 1)) (U₀ : Set (Fin k → Ri R)) :
    chartMap m ⁻¹' (chartImageP i₀ U₀ ∩ chartSet m)
      = {x : Fin k → Ri R |
          x ∈ (chartOverlap m i₀ : Set (Fin k → Ri R)) ∧ transitionMap m i₀ x ∈ U₀} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_inter_iff, chartImageP, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hi₀, hU₀⟩, _⟩
    refine ⟨(chartMap_mem_chartSet_iff m i₀ x).mp hi₀, ?_⟩
    rw [transitionMap_eq_chartInv_chartMap]; exact hU₀
  · rintro ⟨hov, hU₀⟩
    refine ⟨⟨(chartMap_mem_chartSet_iff m i₀ x).mpr hov, ?_⟩, Set.mem_range_self x⟩
    rw [← transitionMap_eq_chartInv_chartMap]; exact hU₀

set_option linter.unusedSectionVars false in
/-- **STEP 3 (semialgebraic).** If `U₀ ⊆ Cᵏ` is semialgebraic over `C`, then `chartImageP i₀ U₀` is a
semialgebraic subset of `ℙ_k(C)`. -/
theorem isSemialgebraicSetP_chartImageP (i₀ : Fin (k + 1)) {U₀ : Set (Fin k → Ri R)}
    (hU₀ : IsSemialgebraicSetC U₀) :
    IsSemialgebraicSetP (chartImageP i₀ U₀) := by
  intro m
  rw [chartMap_preimage_chartImageP]
  have := (isSemialgebraicFunctionC_transitionMap m i₀).preimage (D := chartOverlap m i₀) hU₀
  exact this

/-- `realEquiv` as a homeomorphism `Cᵏ ≃ₜ R^{2k}` (the `Cᵏ` topology is, by definition, induced along
`realEquiv`). -/
noncomputable def realEquivₜ : (Fin k → Ri R) ≃ₜ (Fin (k + k) → R) :=
  (realEquiv).toHomeomorphOfIsInducing (Topology.IsInducing.mk rfl)

set_option linter.unusedSectionVars false in
@[simp] theorem realEquivₜ_apply (z : Fin k → Ri R) : realEquivₜ z = realEquiv z := rfl

set_option linter.unusedSectionVars false in
/-- A complex set is open iff its realification is open. -/
theorem isOpenC_iff_isOpen_realEquiv {S : Set (Fin k → Ri R)} :
    IsOpen S ↔ IsOpen (realEquiv '' S) := by
  rw [← Homeomorph.isOpen_image (realEquivₜ)]
  have himg : (realEquivₜ : (Fin k → Ri R) → (Fin (k + k) → R)) '' S = realEquiv '' S := by
    ext w; simp only [Set.mem_image, realEquivₜ_apply]
  rw [himg]

set_option linter.unusedSectionVars false in
/-- The realified transition map is continuous on the realified overlap (its components are the
order-`0` `IsSFunctionC` data, which carry `ContinuousOn`). -/
theorem continuousOn_realEquiv_transitionMap (m i₀ : Fin (k + 1)) :
    ContinuousOn (fun w : Fin (k + k) → R => realEquiv (transitionMap m i₀ (realEquiv.symm w)))
      (realEquiv '' (chartOverlap m i₀ : Set (Fin k → Ri R))) := by
  set D := realEquiv '' (chartOverlap m i₀ : Set (Fin k → Ri R)) with hD
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: the domain `Fin 0 → R` is a singleton, so any map on it is continuous
    subst hk0
    refine Set.Subsingleton.continuousOn (fun a _ b _ => ?_) _
    exact funext fun i => absurd i.isLt (by omega)
  · have hne : Nonempty (Fin (k + k)) := ⟨⟨0, by omega⟩⟩
    -- continuity reduces to continuity of each output coordinate (ball topology)
    refine continuousOn_of_components (fun c => ?_)
    -- output coordinate `c` is either a real part (`castAdd` block) or imaginary part (`natAdd` block)
    refine Fin.addCases (fun a => ?_) (fun a => ?_) c
    · -- real part of `transitionMap` coordinate `a`
      have hcc : IsSFunctionCC 0 (chartOverlap m i₀ : Set (Fin k → Ri R))
          (fun x => transitionMap m i₀ x a) := isSFunctionCC_transitionMap_coord m i₀ a
      have hsc := Azurite.BPR.IsSFunction.isSemialgContinuousOn hcc.1
      have hcont : ContinuousOn
          (fun w => (fun _ : Fin 1 => Ri.reL (transitionMap m i₀ (realEquiv.symm w) a))) D :=
        hsc.2
      refine hcont.congr (fun w _ => ?_)
      funext s; rw [realEquiv_apply_castAdd]
    · -- imaginary part of `transitionMap` coordinate `a`
      have hcc : IsSFunctionCC 0 (chartOverlap m i₀ : Set (Fin k → Ri R))
          (fun x => transitionMap m i₀ x a) := isSFunctionCC_transitionMap_coord m i₀ a
      have hsc := Azurite.BPR.IsSFunction.isSemialgContinuousOn hcc.2
      have hcont : ContinuousOn
          (fun w => (fun _ : Fin 1 => Ri.imL (transitionMap m i₀ (realEquiv.symm w) a))) D :=
        hsc.2
      refine hcont.congr (fun w _ => ?_)
      funext s; rw [realEquiv_apply_natAdd]

set_option linter.unusedSectionVars false in
/-- **STEP 3 (open).** If `U₀ ⊆ Cᵏ` is open, then `chartImageP i₀ U₀` is open in `ℙ_k(C)`. -/
theorem isOpen_chartImageP (i₀ : Fin (k + 1)) {U₀ : Set (Fin k → Ri R)}
    (hU₀ : IsOpen U₀) :
    IsOpen (chartImageP i₀ U₀ : Set (complexProjectiveSpace R k)) := by
  rw [isOpenP_iff]
  intro m
  rw [chartMap_preimage_chartImageP]
  -- the pullback realifies to: (realified overlap) ∩ (realified transition)⁻¹' (realified U₀)
  set Dov := realEquiv '' (chartOverlap m i₀ : Set (Fin k → Ri R)) with hDov
  have hDovOpen : IsOpen Dov :=
    isOpenC_iff_isOpen_realEquiv.mp (isOpen_chartOverlap m i₀)
  have hU₀real : IsOpen (realEquiv '' U₀) := isOpenC_iff_isOpen_realEquiv.mp hU₀
  rw [isOpenC_iff_isOpen_realEquiv]
  have hset : realEquiv '' {x : Fin k → Ri R |
        x ∈ (chartOverlap m i₀ : Set (Fin k → Ri R)) ∧ transitionMap m i₀ x ∈ U₀}
      = Dov ∩ (fun w => realEquiv (transitionMap m i₀ (realEquiv.symm w))) ⁻¹' (realEquiv '' U₀) := by
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨x, ⟨hov, hU⟩, rfl⟩
      refine ⟨⟨x, hov, rfl⟩, ?_⟩
      rw [Equiv.symm_apply_apply]
      exact ⟨transitionMap m i₀ x, hU, rfl⟩
    · rintro ⟨⟨x, hov, hxw⟩, hpre⟩
      refine ⟨realEquiv.symm w, ⟨?_, ?_⟩, by rw [Equiv.apply_symm_apply]⟩
      · rw [← hxw, Equiv.symm_apply_apply]; exact hov
      · obtain ⟨z, hzU, hz⟩ := hpre
        rwa [← (realEquiv.injective hz)]
  rw [hset]
  exact (continuousOn_realEquiv_transitionMap m i₀).isOpen_inter_preimage hDovOpen hU₀real

/-! ### STEP 4 — chart transport of `𝒮^m` maps -/

/-- The `c`-th real coordinate of the realified value of a `C`-valued map. -/
private theorem IsSFunctionCC.realComp {p q : ℕ} {V : Set (Fin p → Ri R)}
    {g : (Fin p → Ri R) → (Fin q → Ri R)}
    (hg : ∀ b : Fin q, IsSFunctionCC m V (fun z => g z b)) (c : Fin (q + q)) :
    IsSFunction m (realEquiv '' V)
      (fun w => realEquiv (g (realEquiv.symm w)) c) := by
  refine Fin.addCases (fun a => ?_) (fun a => ?_) c
  · have heq : (fun w => realEquiv (g (realEquiv.symm w)) (Fin.castAdd q a))
        = (fun w => Ri.reL (g (realEquiv.symm w) a)) := by
      funext w; rw [realEquiv_apply_castAdd]
    rw [heq]; exact (hg a).1
  · have heq : (fun w => realEquiv (g (realEquiv.symm w)) (Fin.natAdd q a))
        = (fun w => Ri.imL (g (realEquiv.symm w) a)) := by
      funext w; rw [realEquiv_apply_natAdd]
    rw [heq]; exact (hg a).2

set_option linter.unusedSectionVars false in
/-- **STEP 4 (composition).** Composition of `C`-valued `𝒮^m` maps. If `g : Cᵖ → C^q` has all
components `𝒮^m` on `V`, `h : C^q → C^r` has all components `𝒮^m` on `U` (an open realified domain),
`g` maps `V` into `U`, and `V` is semialgebraic over `C`, then `h ∘ g` has all components `𝒮^m`. -/
theorem IsSFunctionCC.comp {p q r : ℕ} [Nonempty (Fin (q + q))]
    {V : Set (Fin p → Ri R)} {U : Set (Fin q → Ri R)}
    (hVsa : IsSemialgebraicSetC V) (hUopen : IsOpen (realEquiv '' U))
    {g : (Fin p → Ri R) → (Fin q → Ri R)} {h : (Fin q → Ri R) → (Fin r → Ri R)}
    (hmaps : Set.MapsTo g V U)
    (hg : ∀ b : Fin q, IsSFunctionCC m V (fun z => g z b))
    (hh : ∀ b : Fin r, IsSFunctionCC m U (fun z => h z b)) :
    ∀ b : Fin r, IsSFunctionCC m V (fun z => h (g z) b) := by
  -- realified `g`
  set Rg : (Fin (p + p) → R) → (Fin (q + q) → R) :=
    fun w => realEquiv (g (realEquiv.symm w)) with hRg
  have hRgmaps : Set.MapsTo Rg (realEquiv '' V) (realEquiv '' U) := by
    rintro w ⟨z, hzV, rfl⟩
    rw [hRg]
    simp only [Equiv.symm_apply_apply]
    exact ⟨g z, hmaps hzV, rfl⟩
  have hRgcomp : ∀ c : Fin (q + q), IsSFunction m (realEquiv '' V) (fun w => Rg w c) :=
    fun c => IsSFunctionCC.realComp hg c
  intro b
  refine ⟨?_, ?_⟩
  · -- real part of `h (g z) b`
    have hhc : IsSFunction m (realEquiv '' U) (fun u => Ri.reL (h (realEquiv.symm u) b)) :=
      (hh b).1
    have hcomp := isSFunction_comp hVsa hUopen hRgmaps hhc hRgcomp
    have heq : (fun w => Ri.reL (h (realEquiv.symm (Rg w)) b))
        = (fun w => Ri.reL (h (g (realEquiv.symm w)) b)) := by
      funext w; rw [hRg, Equiv.symm_apply_apply]
    rw [heq] at hcomp; exact hcomp
  · -- imaginary part of `h (g z) b`
    have hhc : IsSFunction m (realEquiv '' U) (fun u => Ri.imL (h (realEquiv.symm u) b)) :=
      (hh b).2
    have hcomp := isSFunction_comp hVsa hUopen hRgmaps hhc hRgcomp
    have heq : (fun w => Ri.imL (h (realEquiv.symm (Rg w)) b))
        = (fun w => Ri.imL (h (g (realEquiv.symm w)) b)) := by
      funext w; rw [hRg, Equiv.symm_apply_apply]
    rw [heq] at hcomp; exact hcomp

set_option linter.unusedSectionVars false in
/-- A complex map whose realification has each real coordinate `𝒮^m` has each complex coordinate
`𝒮^m`. This bridges the affine §3.5 output (`2ℓ` real components) to the complex `IsSFunctionCC`
classes. -/
theorem isSFunctionCC_of_realComponents {p q : ℕ} {D : Set (Fin p → Ri R)}
    {f : (Fin p → Ri R) → (Fin q → Ri R)}
    (hf : ∀ c : Fin (q + q), IsSFunction m (realEquiv '' D)
      (fun w => realEquiv (f (realEquiv.symm w)) c)) :
    ∀ b : Fin q, IsSFunctionCC m D (fun z => f z b) := by
  intro b
  refine ⟨?_, ?_⟩
  · have hc := hf (Fin.castAdd q b)
    have heq : (fun w => realEquiv (f (realEquiv.symm w)) (Fin.castAdd q b))
        = (fun w => Ri.reL (f (realEquiv.symm w) b)) := by
      funext w; rw [realEquiv_apply_castAdd]
    rw [heq] at hc; exact hc
  · have hc := hf (Fin.natAdd q b)
    have heq : (fun w => realEquiv (f (realEquiv.symm w)) (Fin.natAdd q b))
        = (fun w => Ri.imL (f (realEquiv.symm w) b)) := by
      funext w; rw [realEquiv_apply_natAdd]
    rw [heq] at hc; exact hc

set_option linter.unusedSectionVars false in
/-- `IsSFunctionCC` restricts to a (realified-semialgebraic) subset. -/
theorem IsSFunctionCC.mono_set {p : ℕ} {V V' : Set (Fin p → Ri R)}
    (hV : IsSemialgebraicSetC V) (hVV : V ⊆ V') {c : (Fin p → Ri R) → Ri R}
    (hc : IsSFunctionCC m V' c) : IsSFunctionCC m V c := by
  have himg : realEquiv '' V ⊆ realEquiv '' V' := Set.image_mono hVV
  exact ⟨hc.1.mono_set hV himg, hc.2.mono_set hV himg⟩

/-! ### STEP 4 — `IsSClassMapP` chart transport -/

/-- The projective map assembled from a complex chart-`(i₀,j₀)` representation `ϕ₀ : Cᵏ → Cˡ`:
`ϕ p = φ_{j₀}(ϕ₀(φ_{i₀}⁻¹ p))`. -/
noncomputable def liftProjMap {k ℓ : ℕ} (i₀ : Fin (k + 1)) (j₀ : Fin (ℓ + 1))
    (ϕ₀ : (Fin k → Ri R) → (Fin ℓ → Ri R)) :
    complexProjectiveSpace R k → complexProjectiveSpace R ℓ :=
  fun p => chartMap j₀ (ϕ₀ (chartInv i₀ p))

set_option linter.unusedSectionVars false in
/-- The chart-`(i,j)` representation of `liftProjMap i₀ j₀ ϕ₀`, on the part of chart `i` whose image
under `φ_i` lands in `𝒰_{i₀}`: `φ_j⁻¹ ∘ ϕ ∘ φ_i = (φ_j⁻¹∘φ_{j₀}) ∘ ϕ₀ ∘ (φ_{i₀}⁻¹∘φ_i)`, i.e.
`transitionMap j₀ j ∘ ϕ₀ ∘ transitionMap i i₀`. -/
theorem chartInv_liftProjMap_chartMap {k ℓ : ℕ} (i₀ : Fin (k + 1)) (j₀ : Fin (ℓ + 1))
    (ϕ₀ : (Fin k → Ri R) → (Fin ℓ → Ri R)) (i : Fin (k + 1)) (j : Fin (ℓ + 1))
    (z : Fin k → Ri R) (b : Fin ℓ) :
    chartInv j (liftProjMap i₀ j₀ ϕ₀ (chartMap i z)) b
      = transitionMap j₀ j (ϕ₀ (transitionMap i i₀ z)) b := by
  rw [liftProjMap]
  rw [show chartInv i₀ (chartMap i z) = transitionMap i i₀ z from
    (transitionMap_eq_chartInv_chartMap i i₀ z).symm]
  rw [transitionMap_eq_chartInv_chartMap j₀ j (ϕ₀ (transitionMap i i₀ z))]

set_option linter.unusedSectionVars false in
/-- **STEP 4 (transport).** Let `ϕ₀ : Cᵏ → Cˡ` be a complex chart-`(i₀,j₀)` representation, all of
whose coordinate functions are `𝒮^m` on an open semialgebraic `U₀`, and form the projective map
`ϕ = liftProjMap i₀ j₀ ϕ₀` with `U = chartImageP i₀ U₀`. If `ϕ` maps `U` into `V`, and for every
pair of charts `(i,j)` the chart-`(i,j)` domain is semialgebraic over `C`, then `ϕ` is of class
`𝒮^m` (`IsSClassMapP m U V ϕ`). The chart-`(i,j)` representation is the conjugation
`transitionMap j₀ j ∘ ϕ₀ ∘ transitionMap i i₀`, smooth by `IsSFunctionCC.comp`. -/
theorem isSClassMapP_liftProjMap {k ℓ : ℕ} (i₀ : Fin (k + 1)) (j₀ : Fin (ℓ + 1))
    {U₀ : Set (Fin k → Ri R)} (hU₀open : IsOpen (realEquiv '' U₀))
    (hU₀sa : IsSemialgebraicSetC U₀)
    {ϕ₀ : (Fin k → Ri R) → (Fin ℓ → Ri R)}
    (hϕ₀ : ∀ b : Fin ℓ, IsSFunctionCC m U₀ (fun z => ϕ₀ z b))
    {V : Set (complexProjectiveSpace R ℓ)}
    (hmaps : Set.MapsTo (liftProjMap i₀ j₀ ϕ₀) (chartImageP i₀ U₀) V)
    (hDom : ∀ (i : Fin (k + 1)) (j : Fin (ℓ + 1)), IsSemialgebraicSetC
      (chartMap i ⁻¹' (chartImageP i₀ U₀ ∩ chartSet i)
        ∩ (fun z => liftProjMap i₀ j₀ ϕ₀ (chartMap i z)) ⁻¹' chartSet j)) :
    IsSClassMapP m (chartImageP i₀ U₀) V (liftProjMap i₀ j₀ ϕ₀) := by
  classical
  refine ⟨hmaps, fun i j b => ?_⟩
  have : Nonempty (Fin (ℓ + ℓ)) := ⟨⟨b.val, by have := b.isLt; omega⟩⟩
  set ϕ := liftProjMap i₀ j₀ ϕ₀ with hϕ
  set Dom := chartMap i ⁻¹' (chartImageP i₀ U₀ ∩ chartSet i)
    ∩ (fun z => ϕ (chartMap i z)) ⁻¹' chartSet j with hDomdef
  have hDomSA : IsSemialgebraicSetC Dom := hDom i j
  -- `Dom ⊆ chartOverlap i i₀`
  have hsub : Dom ⊆ (chartOverlap i i₀ : Set (Fin k → Ri R)) := by
    intro z hz
    have hzU : chartMap i z ∈ chartImageP i₀ U₀ := hz.1.1
    rw [← chartMap_mem_chartSet_iff]; exact hzU.1
  -- MapsTo `transition i i₀` into `U₀`
  have hmaps1 : Set.MapsTo (transitionMap i i₀) Dom U₀ := by
    intro z hz
    have hzU : chartMap i z ∈ chartImageP i₀ U₀ := hz.1.1
    rw [transitionMap_eq_chartInv_chartMap]; exact hzU.2
  -- inner composition `ϕ₀ ∘ transition i i₀` is `𝒮^m` on `Dom`
  have htrans1 : ∀ b : Fin k, IsSFunctionCC m Dom (fun z => transitionMap i i₀ z b) :=
    fun b => (isSClassMap_transitionMap i i₀ b).mono_set hDomSA hsub
  have hinner : ∀ b : Fin ℓ, IsSFunctionCC m Dom (fun z => ϕ₀ (transitionMap i i₀ z) b) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · -- `k = 0`: `transition i i₀ z : C⁰` is the empty tuple, so the function is constant in `z`
      subst hk0
      intro b
      have hconst : (fun z : Fin 0 → Ri R => ϕ₀ (transitionMap i i₀ z) b)
          = (fun _ => ϕ₀ (transitionMap i i₀ (fun z => z.elim0)) b) := by
        funext z
        congr 1
        funext w; exact w.elim0
      rw [hconst]
      exact isSFunctionCC_const hDomSA _
    · have : Nonempty (Fin (k + k)) := ⟨⟨0, by omega⟩⟩
      exact IsSFunctionCC.comp hDomSA hU₀open hmaps1 htrans1 hϕ₀
  -- MapsTo `ϕ₀ ∘ transition i i₀` into `chartOverlap j₀ j`
  have hmaps2 : Set.MapsTo (fun z => ϕ₀ (transitionMap i i₀ z)) Dom
      (chartOverlap j₀ j : Set (Fin ℓ → Ri R)) := by
    intro z hz
    have hzj : ϕ (chartMap i z) ∈ chartSet j := hz.2
    have hrep : ϕ (chartMap i z) = chartMap j₀ (ϕ₀ (transitionMap i i₀ z)) := by
      rw [hϕ, liftProjMap]
      rw [show chartInv i₀ (chartMap i z) = transitionMap i i₀ z from
        (transitionMap_eq_chartInv_chartMap i i₀ z).symm]
    rw [hrep] at hzj
    rw [← chartMap_mem_chartSet_iff]; exact hzj
  -- outer composition with `transition j₀ j`
  have htrans2 : ∀ b : Fin ℓ, IsSFunctionCC m (chartOverlap j₀ j : Set (Fin ℓ → Ri R))
      (fun w => transitionMap j₀ j w b) := isSClassMap_transitionMap j₀ j
  have houter : ∀ b : Fin ℓ, IsSFunctionCC m Dom
      (fun z => transitionMap j₀ j (ϕ₀ (transitionMap i i₀ z)) b) :=
    IsSFunctionCC.comp hDomSA (isOpenC_iff_isOpen_realEquiv.mp (isOpen_chartOverlap j₀ j))
      hmaps2 hinner htrans2
  -- rewrite back to the chart representation
  have hfeq : (fun z => chartInv j (ϕ (chartMap i z)) b)
      = (fun z => transitionMap j₀ j (ϕ₀ (transitionMap i i₀ z)) b) := by
    funext z; rw [hϕ, chartInv_liftProjMap_chartMap]
  rw [hfeq]
  exact houter b

/-! ### STEP 5a — bridge lemmas: composition and affine→complex graphs over `C` -/

set_option linter.unusedSectionVars false in
/-- **STEP 5a.1 (composition over `C`).** The complex analogue of `proposition_2_84`: if
`f : Cᵏ → Cˡ` is semialgebraic over `C` on `A`, `g : Cˡ → C^m` is semialgebraic over `C` on `B`, and
`f` maps `A` into `B`, then `g ∘ f` is semialgebraic over `C` on `A`. The graph of `g ∘ f` is the
`C`-projection (over the intermediate `Cˡ` block) of the intersection of the two cylindered graphs,
which is semialgebraic over `C` by `IsSemialgebraicSetC.exists_append`. -/
theorem IsSemialgebraicFunctionC.comp {k ℓ m : ℕ}
    {A : Set (Fin k → Ri R)} {B : Set (Fin ℓ → Ri R)}
    {f : (Fin k → Ri R) → (Fin ℓ → Ri R)} {g : (Fin ℓ → Ri R) → (Fin m → Ri R)}
    (hf : IsSemialgebraicFunctionC A f) (hg : IsSemialgebraicFunctionC B g)
    (hmaps : Set.MapsTo f A B) :
    IsSemialgebraicFunctionC A (g ∘ f) := by
  classical
  -- The two coordinate reindexings into the `(x, w, y)` layout of `C^{(k+m)+ℓ}`.
  set gF : Fin (k + ℓ) → Fin ((k + m) + ℓ) :=
    Fin.addCases (fun i : Fin k => Fin.castAdd ℓ (Fin.castAdd m i))
      (fun jy : Fin ℓ => Fin.natAdd (k + m) jy) with hgF
  set gG : Fin (ℓ + m) → Fin ((k + m) + ℓ) :=
    Fin.addCases (fun jy : Fin ℓ => Fin.natAdd (k + m) jy)
      (fun j : Fin m => Fin.castAdd ℓ (Fin.natAdd k j)) with hgG
  have hcF : ∀ (p : Fin (k + m) → Ri R) (y : Fin ℓ → Ri R),
      (Fin.append p y) ∘ gF = Fin.append (p ∘ Fin.castAdd m) y := by
    intro p y; rw [hgF]; funext i
    induction i using Fin.addCases with
    | left i => simp only [Function.comp_apply, Fin.addCases_left, Fin.append_left]
    | right jy => simp only [Function.comp_apply, Fin.addCases_right, Fin.append_right]
  have hcG : ∀ (p : Fin (k + m) → Ri R) (y : Fin ℓ → Ri R),
      (Fin.append p y) ∘ gG = Fin.append y (p ∘ Fin.natAdd k) := by
    intro p y; rw [hgG]; funext i
    induction i using Fin.addCases with
    | left jy =>
      simp only [Function.comp_apply, Fin.addCases_left, Fin.append_right, Fin.append_left]
    | right j =>
      simp only [Function.comp_apply, Fin.addCases_right, Fin.append_left, Fin.append_right]
  have hFpart : IsSemialgebraicSetC
      {v : Fin ((k + m) + ℓ) → Ri R | v ∘ gF ∈ complexFunGraph A f} :=
    IsSemialgebraicSetC.comap gF hf
  have hGpart : IsSemialgebraicSetC
      {v : Fin ((k + m) + ℓ) → Ri R | v ∘ gG ∈ complexFunGraph B g} :=
    IsSemialgebraicSetC.comap gG hg
  have hproj := IsSemialgebraicSetC.exists_append (hFpart.inter hGpart)
  rw [IsSemialgebraicFunctionC]
  have hthis : complexFunGraph A (g ∘ f) =
      {p : Fin (k + m) → Ri R | ∃ y : Fin ℓ → Ri R, Fin.append p y ∈
        ({v | v ∘ gF ∈ complexFunGraph A f} ∩ {v | v ∘ gG ∈ complexFunGraph B g})} := by
    ext p
    simp only [mem_complexFunGraph, Set.mem_ofPred_eq, Set.mem_inter_iff, hcF, hcG,
      append_comp_castAdd', append_comp_natAdd', Function.comp_apply]
    constructor
    · rintro ⟨hA, hw⟩
      exact ⟨f (p ∘ Fin.castAdd m), ⟨hA, rfl⟩, hmaps hA, hw⟩
    · rintro ⟨y, ⟨hA, hyf⟩, _hyB, hwg⟩
      exact ⟨hA, by rw [hwg, hyf]⟩
  rw [hthis]; exact hproj

set_option linter.unusedSectionVars false in
/-- **Domain restriction of a semialgebraic-over-`C` map.** If `f` is semialgebraic over `C` on `A`
and `A' ⊆ A` is semialgebraic over `C`, then `f` is semialgebraic over `C` on `A'`. The graph over
`A'` is the graph over `A` intersected with the cylinder over `A'`. -/
theorem IsSemialgebraicFunctionC.mono {k ℓ : ℕ} {A A' : Set (Fin k → Ri R)}
    {f : (Fin k → Ri R) → (Fin ℓ → Ri R)} (hf : IsSemialgebraicFunctionC A f)
    (hA' : IsSemialgebraicSetC A') (hsub : A' ⊆ A) :
    IsSemialgebraicFunctionC A' f := by
  rw [IsSemialgebraicFunctionC]
  have hcyl : IsSemialgebraicSetC {p : Fin (k + ℓ) → Ri R | p ∘ Fin.castAdd ℓ ∈ A'} :=
    IsSemialgebraicSetC.comap (Fin.castAdd ℓ) hA'
  have hset : complexFunGraph A' f
      = complexFunGraph A f ∩ {p : Fin (k + ℓ) → Ri R | p ∘ Fin.castAdd ℓ ∈ A'} := by
    ext p
    simp only [mem_complexFunGraph, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hA'p, hfp⟩; exact ⟨⟨hsub hA'p, hfp⟩, hA'p⟩
    · rintro ⟨⟨_, hfp⟩, hA'p⟩; exact ⟨hA'p, hfp⟩
  rw [hset]; exact hf.inter hcyl

/-- The inverse reordering of `appendReindex k ℓ`: it sends the `[Re x | Im x | Re y | Im y]` layout
(`R^{(k+k)+(ℓ+ℓ)}`) back to the `[Re | Im]` layout (`R^{(k+ℓ)+(k+ℓ)}`) of `realEquiv` on `C^{k+ℓ}`. -/
def appendUnreindex (k ℓ : ℕ) : Fin ((k + k) + (ℓ + ℓ)) → Fin ((k + ℓ) + (k + ℓ)) :=
  fun i => Fin.addCases
    (fun u : Fin (k + k) => Fin.addCases
      (fun a : Fin k => Fin.castAdd (k + ℓ) (Fin.castAdd ℓ a))
      (fun a : Fin k => Fin.natAdd (k + ℓ) (Fin.castAdd ℓ a)) u)
    (fun u : Fin (ℓ + ℓ) => Fin.addCases
      (fun b : Fin ℓ => Fin.castAdd (k + ℓ) (Fin.natAdd k b))
      (fun b : Fin ℓ => Fin.natAdd (k + ℓ) (Fin.natAdd k b)) u)
    i

set_option linter.unusedSectionVars false in
/-- `appendReindex k ℓ ∘ appendUnreindex k ℓ = id`: the two block reorderings are inverse. -/
theorem appendReindex_appendUnreindex (k ℓ : ℕ) (i : Fin ((k + k) + (ℓ + ℓ))) :
    appendReindex k ℓ (appendUnreindex k ℓ i) = i := by
  refine Fin.addCases (fun u => ?_) (fun u => ?_) i
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) u
    · simp only [appendUnreindex, Fin.addCases_left, appendReindex, Fin.addCases_left]
    · simp only [appendUnreindex, Fin.addCases_left, Fin.addCases_right, appendReindex,
        Fin.addCases_right]
  · refine Fin.addCases (fun b => ?_) (fun b => ?_) u
    · simp only [appendUnreindex, Fin.addCases_right, Fin.addCases_left, appendReindex,
        Fin.addCases_left, Fin.addCases_right]
    · simp only [appendUnreindex, Fin.addCases_right, appendReindex, Fin.addCases_right]

set_option linter.unusedSectionVars false in
/-- **STEP 5a.2 (affine → complex graph).** If `ϕ_aff : R^{2k} → R^{2ℓ}` is semialgebraic on
`U_aff ⊆ R^{2k}` (the realified affine implicit function from `theorem_3_25`), then its complex
realification `ϕ₀ z = realEquiv.symm (ϕ_aff (realEquiv z))` is semialgebraic over `C` on the complex
domain `realEquiv.symm '' U_aff`. The complex graph realifies to the comap of `funGraph U_aff ϕ_aff`
along the block-reordering `appendUnreindex`. -/
theorem isSemialgebraicFunctionC_realEquiv_symm {k ℓ : ℕ} {U_aff : Set (Fin (k + k) → R)}
    {ϕ_aff : (Fin (k + k) → R) → (Fin (ℓ + ℓ) → R)}
    (hϕ : IsSemialgebraicFunction U_aff ϕ_aff) :
    IsSemialgebraicFunctionC (realEquiv.symm '' U_aff)
      (fun z : Fin k → Ri R => realEquiv.symm (ϕ_aff (realEquiv z))) := by
  set D : Set (Fin k → Ri R) := realEquiv.symm '' U_aff with hD
  set ϕ₀ : (Fin k → Ri R) → (Fin ℓ → Ri R) :=
    fun z => realEquiv.symm (ϕ_aff (realEquiv z)) with hϕ₀
  rw [IsSemialgebraicFunctionC, IsSemialgebraicSetC]
  -- comap of `funGraph U_aff ϕ_aff` along `appendUnreindex`
  have hcomap : IsSemialgebraicSet
      {u : Fin ((k + ℓ) + (k + ℓ)) → R | u ∘ appendUnreindex k ℓ ∈ funGraph U_aff ϕ_aff} :=
    IsSemialgebraicSet.comap (appendUnreindex k ℓ) hϕ
  -- the realified complex graph equals this comap
  have hset : realEquiv '' (complexFunGraph D ϕ₀)
      = {u : Fin ((k + ℓ) + (k + ℓ)) → R | u ∘ appendUnreindex k ℓ ∈ funGraph U_aff ϕ_aff} := by
    ext u
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [mem_complexFunGraph] at hp
      obtain ⟨hpD, hpf⟩ := hp
      set x : Fin k → Ri R := p ∘ Fin.castAdd ℓ with hx
      set y : Fin ℓ → Ri R := p ∘ Fin.natAdd k with hy
      have hpapp : p = Fin.append x y := by
        rw [hx, hy]; exact (Fin.append_castAdd_natAdd).symm
      -- key: `realEquiv p ∘ appendUnreindex = append (realEquiv x) (realEquiv y)`
      have hkey : realEquiv p ∘ appendUnreindex k ℓ = Fin.append (realEquiv x) (realEquiv y) := by
        rw [hpapp, realEquiv_append]
        funext i
        rw [Function.comp_apply, Function.comp_apply, appendReindex_appendUnreindex]
      rw [Set.mem_ofPred_eq, hkey, mem_funGraph]
      refine ⟨?_, ?_⟩
      · -- `realEquiv x ∈ U_aff`
        rw [Azurite.BPR.append_comp_castAdd]
        obtain ⟨w, hwU, hwx⟩ := hpD
        have : realEquiv x = w := by rw [← hwx, Equiv.apply_symm_apply]
        rw [this]; exact hwU
      · -- `realEquiv y = ϕ_aff (realEquiv x)`
        rw [Azurite.BPR.append_comp_castAdd, Azurite.BPR.append_comp_natAdd]
        have hyval : y = ϕ₀ x := hpf
        rw [hyval, hϕ₀, Equiv.apply_symm_apply]
    · intro hu
      rw [Set.mem_ofPred_eq, mem_funGraph] at hu
      refine ⟨realEquiv.symm u, ?_, by rw [Equiv.apply_symm_apply]⟩
      rw [mem_complexFunGraph]
      set p : Fin (k + ℓ) → Ri R := realEquiv.symm u with hp
      set x : Fin k → Ri R := p ∘ Fin.castAdd ℓ with hx
      set y : Fin ℓ → Ri R := p ∘ Fin.natAdd k with hy
      have hpapp : p = Fin.append x y := by
        rw [hx, hy]; exact (Fin.append_castAdd_natAdd).symm
      have hkey : realEquiv p ∘ appendUnreindex k ℓ = Fin.append (realEquiv x) (realEquiv y) := by
        rw [hpapp, realEquiv_append]
        funext i
        rw [Function.comp_apply, Function.comp_apply, appendReindex_appendUnreindex]
      have hpu : realEquiv p = u := by rw [hp, Equiv.apply_symm_apply]
      rw [hpu] at hkey
      -- decode the two `funGraph` conditions in `[Re x|Im x|Re y|Im y]` layout
      obtain ⟨hxU, hyf⟩ := hu
      rw [hkey, Azurite.BPR.append_comp_castAdd] at hxU
      rw [hkey, Azurite.BPR.append_comp_castAdd, Azurite.BPR.append_comp_natAdd] at hyf
      refine ⟨?_, ?_⟩
      · -- `x ∈ D`
        rw [hD]; exact ⟨realEquiv x, hxU, by rw [Equiv.symm_apply_apply]⟩
      · -- `y = ϕ₀ x`
        show y = realEquiv.symm (ϕ_aff (realEquiv x))
        rw [← hyf, Equiv.symm_apply_apply]
  rw [hset]; exact hcomap

/-! ### STEP 5b — Theorem 4.104, the Projective Implicit Function Theorem -/

set_option linter.unusedSectionVars false in
/-- **BPR Theorem 4.104 (Projective Implicit Function Theorem).** Let `x₀ ∈ ℙ_k(C)` and
`y₀ ∈ ℙ_ℓ(C)` lie in the affine charts `φ_{i₀}` and `φ_{j₀}`. Suppose the `2ℓ` real component
functions `F` of the defining equations, read in the chart `(i₀, j₀)` and realified to the
`(2k)+(2ℓ)` block layout of `theorem_3_25`, are of class `𝒮^m` on an open semialgebraic neighborhood
`W'` of the realified base point, vanish there, have semialgebraic-continuous partial derivatives `g`
(also `𝒮^m`), and the `y`-Jacobian is invertible. Then there are open semialgebraic neighborhoods
`U ∋ x₀`, `V ∋ y₀` and a map `ϕ : ℙ_k(C) → ℙ_ℓ(C)` of class `𝒮^m` with `ϕ x₀ = y₀`, such that for
`(x, y) ∈ U × V`, the realified defining equations vanish at the chart coordinates of `(x, y)` iff
`y = ϕ x`.

The proof reduces to the affine implicit function theorem `theorem_3_25` in the single chart
`(i₀, j₀)` via the realification `Cⁿ = R^{2n}`, then transports the resulting affine data
`(U_aff, V_aff, ϕ_aff)` to projective space through the charts: `U = chartImageP i₀ (realEquiv.symm ''
U_aff)`, `V = chartImageP j₀ (realEquiv.symm '' V_aff)`, and `ϕ = liftProjMap i₀ j₀ ϕ₀` with
`ϕ₀ = realEquiv.symm ∘ ϕ_aff ∘ realEquiv`. -/
theorem theorem_4_104 {k ℓ : ℕ} (m : ℕ)
    (x₀ : complexProjectiveSpace R k) (y₀ : complexProjectiveSpace R ℓ)
    (i₀ : Fin (k + 1)) (j₀ : Fin (ℓ + 1))
    (hx₀ : x₀ ∈ chartSet i₀) (hy₀ : y₀ ∈ chartSet j₀)
    (W' : Set (Fin ((k + k) + (ℓ + ℓ)) → R)) (hW'open : IsOpen W') (hW'sa : IsSemialgebraicSet W')
    (F : Fin (ℓ + ℓ) → (Fin ((k + k) + (ℓ + ℓ)) → R) → R)
    (g : Fin (ℓ + ℓ) → Fin ((k + k) + (ℓ + ℓ)) → (Fin ((k + k) + (ℓ + ℓ)) → R) → R)
    (hz₀W : Fin.append (realEquiv (chartInv i₀ x₀)) (realEquiv (chartInv j₀ y₀)) ∈ W')
    (hF : ∀ l, IsSemialgContinuousOn W' (F l))
    (hdiff : ∀ l j, ∀ z ∈ W', HasPartialDerivAtIn (F l) W' j z (g l j z))
    (hgsc : ∀ l j, IsSemialgContinuousOn W' (g l j))
    (hF0 : ∀ l, F l (Fin.append (realEquiv (chartInv i₀ x₀)) (realEquiv (chartInv j₀ y₀))) = 0)
    (hdet : IsUnit (Matrix.of fun l j : Fin (ℓ + ℓ) =>
      g l (Fin.natAdd (k + k) j)
        (Fin.append (realEquiv (chartInv i₀ x₀)) (realEquiv (chartInv j₀ y₀)))).det)
    (hgS : ∀ l j, IsSFunction m W' (g l j)) :
    ∃ (U : Set (complexProjectiveSpace R k)) (V : Set (complexProjectiveSpace R ℓ))
      (ϕ : complexProjectiveSpace R k → complexProjectiveSpace R ℓ),
      IsSemialgebraicSetP U ∧ IsOpen U ∧ x₀ ∈ U ∧
      IsSemialgebraicSetP V ∧ IsOpen V ∧ y₀ ∈ V ∧
      IsSClassMapP m U V ϕ ∧ ϕ x₀ = y₀ ∧
      (∀ x ∈ U, ∀ y ∈ V,
        ((∀ l, F l (Fin.append (realEquiv (chartInv i₀ x)) (realEquiv (chartInv j₀ y))) = 0)
          ↔ y = ϕ x)) := by
  classical
  -- abbreviate the realified base point coordinates
  set x₀a : Fin (k + k) → R := realEquiv (chartInv i₀ x₀) with hx₀a
  set y₀a : Fin (ℓ + ℓ) → R := realEquiv (chartInv j₀ y₀) with hy₀a
  -- apply the affine implicit function theorem in the chart `(i₀, j₀)`
  obtain ⟨Ua, Va, ϕa, hUasa, hUaopen, hx₀Ua, hVasa, hVaopen, hy₀Va, hϕasa, hϕacont,
      hϕamaps, hϕax₀, hprodUV, himpl, hϕaS⟩ :=
    Azurite.BPR.theorem_3_25 (k := k + k) (ℓ := ℓ + ℓ) (W' := W') (x₀ := x₀a) (y₀ := y₀a)
      (f := F) (g := g) hW'open hW'sa hz₀W hF hdiff hgsc hF0 hdet m hgS
  -- transport to projective space
  set U₀ : Set (Fin k → Ri R) := realEquiv.symm '' Ua with hU₀
  set V₀ : Set (Fin ℓ → Ri R) := realEquiv.symm '' Va with hV₀
  set ϕ₀ : (Fin k → Ri R) → (Fin ℓ → Ri R) :=
    fun z => realEquiv.symm (ϕa (realEquiv z)) with hϕ₀
  set U : Set (complexProjectiveSpace R k) := chartImageP i₀ U₀ with hUdef
  set V : Set (complexProjectiveSpace R ℓ) := chartImageP j₀ V₀ with hVdef
  set ϕ : complexProjectiveSpace R k → complexProjectiveSpace R ℓ := liftProjMap i₀ j₀ ϕ₀ with hϕdef
  -- realification identities
  have hreUa : realEquiv '' U₀ = Ua := by rw [hU₀, Equiv.image_symm_image]
  have hreVa : realEquiv '' V₀ = Va := by rw [hV₀, Equiv.image_symm_image]
  -- `U₀, V₀` semialgebraic over `C` and open
  have hU₀sa : IsSemialgebraicSetC U₀ := by rw [IsSemialgebraicSetC, hreUa]; exact hUasa
  have hV₀sa : IsSemialgebraicSetC V₀ := by rw [IsSemialgebraicSetC, hreVa]; exact hVasa
  have hU₀open : IsOpen (realEquiv '' U₀) := by rw [hreUa]; exact hUaopen
  have hV₀open : IsOpen (realEquiv '' V₀) := by rw [hreVa]; exact hVaopen
  -- chart-coordinate membership criteria for `U`, `V`
  have hmemU : ∀ p : complexProjectiveSpace R k,
      p ∈ U ↔ p ∈ chartSet i₀ ∧ realEquiv (chartInv i₀ p) ∈ Ua := by
    intro p
    rw [hUdef, chartImageP, Set.mem_ofPred_eq, hU₀]
    refine and_congr_right (fun _ => ?_)
    constructor
    · rintro ⟨w, hwU, hwp⟩; rw [← hwp, Equiv.apply_symm_apply]; exact hwU
    · intro h; exact ⟨realEquiv (chartInv i₀ p), h, by rw [Equiv.symm_apply_apply]⟩
  have hmemV : ∀ q : complexProjectiveSpace R ℓ,
      q ∈ V ↔ q ∈ chartSet j₀ ∧ realEquiv (chartInv j₀ q) ∈ Va := by
    intro q
    rw [hVdef, chartImageP, Set.mem_ofPred_eq, hV₀]
    refine and_congr_right (fun _ => ?_)
    constructor
    · rintro ⟨w, hwV, hwq⟩; rw [← hwq, Equiv.apply_symm_apply]; exact hwV
    · intro h; exact ⟨realEquiv (chartInv j₀ q), h, by rw [Equiv.symm_apply_apply]⟩
  -- `ϕ₀` semialgebraic over `C` on `U₀`
  have hϕ₀sa : IsSemialgebraicFunctionC U₀ ϕ₀ := by
    rw [hϕ₀, hU₀]; exact isSemialgebraicFunctionC_realEquiv_symm hϕasa
  -- `ϕ₀`'s coordinates are `𝒮^m` on `U₀`
  have hϕ₀coords : ∀ b : Fin ℓ, IsSFunctionCC m U₀ (fun z => ϕ₀ z b) := by
    apply isSFunctionCC_of_realComponents
    intro c
    -- `realEquiv (ϕ₀ (realEquiv.symm w)) c = ϕa w c`
    have heq : (fun w => realEquiv (ϕ₀ (realEquiv.symm w)) c)
        = (fun w => ϕa w c) := by
      funext w
      show realEquiv (realEquiv.symm (ϕa (realEquiv (realEquiv.symm w)))) c = ϕa w c
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [heq, hreUa]
    exact (hϕaS c).mono (Nat.le_succ m)
  -- `ϕ` maps `U` into `V`
  have hϕmaps : Set.MapsTo ϕ U V := by
    intro p hp
    rw [hmemU] at hp
    obtain ⟨hpi₀, hpUa⟩ := hp
    -- `chartInv i₀ p ∈ U₀`, so `ϕa (realEquiv (chartInv i₀ p)) ∈ Va`
    have hcoordU : chartInv i₀ p ∈ U₀ := by
      rw [hU₀]; exact ⟨realEquiv (chartInv i₀ p), hpUa, by rw [Equiv.symm_apply_apply]⟩
    have hϕaVa : ϕa (realEquiv (chartInv i₀ p)) ∈ Va :=
      hϕamaps hpUa
    rw [hmemV]
    -- `ϕ p = chartMap j₀ (ϕ₀ (chartInv i₀ p)) ∈ chartSet j₀`
    have hϕp : ϕ p = chartMap j₀ (ϕ₀ (chartInv i₀ p)) := by rw [hϕdef, liftProjMap]
    refine ⟨by rw [hϕp]; exact Set.mem_range_self _, ?_⟩
    -- compute `chartInv j₀ (ϕ p) = ϕ₀ (chartInv i₀ p)`
    have hcij : chartInv j₀ (ϕ p) = ϕ₀ (chartInv i₀ p) := by
      rw [hϕp, chartInv_chartMap]
    rw [hcij, hϕ₀, Equiv.apply_symm_apply]; exact hϕaVa
  -- the per-chart domain is semialgebraic over `C` (the `hDom` hypothesis of `isSClassMapP_liftProjMap`)
  have hDom : ∀ (i : Fin (k + 1)) (j : Fin (ℓ + 1)), IsSemialgebraicSetC
      (chartMap i ⁻¹' (chartImageP i₀ U₀ ∩ chartSet i)
        ∩ (fun z => liftProjMap i₀ j₀ ϕ₀ (chartMap i z)) ⁻¹' chartSet j) := by
    intro i j
    -- the domain `A := {z | z ∈ overlap i i₀ ∧ transition i i₀ z ∈ U₀}` (= the first factor)
    set A : Set (Fin k → Ri R) := {z : Fin k → Ri R |
        z ∈ (chartOverlap i i₀ : Set (Fin k → Ri R)) ∧ transitionMap i i₀ z ∈ U₀} with hA
    have hfac1 : IsSemialgebraicSetC A := by
      have := (isSemialgebraicFunctionC_transitionMap i i₀).preimage hU₀sa
      rw [hA]; convert this using 2
    -- on `A`, `transition i i₀` maps into `U₀`, so `ϕ₀ ∘ transition` is semialgebraic over `C`
    have hsubA : A ⊆ (chartOverlap i i₀ : Set (Fin k → Ri R)) := fun z hz => hz.1
    have htransA : IsSemialgebraicFunctionC A (transitionMap i i₀) :=
      (isSemialgebraicFunctionC_transitionMap i i₀).mono hfac1 hsubA
    have hmaps1 : Set.MapsTo (transitionMap i i₀) A U₀ := fun z hz => hz.2
    have hψ : IsSemialgebraicFunctionC A (fun z => ϕ₀ (transitionMap i i₀ z)) :=
      IsSemialgebraicFunctionC.comp htransA hϕ₀sa hmaps1
    -- second factor (relative to `A`): `{z ∈ A | ϕ₀ (transition i i₀ z) ∈ overlap j₀ j}`
    have hfac2 : IsSemialgebraicSetC {z : Fin k → Ri R |
        z ∈ A ∧ ϕ₀ (transitionMap i i₀ z) ∈ (chartOverlap j₀ j : Set (Fin ℓ → Ri R))} :=
      hψ.preimage (isSemialgebraicSetC_chartOverlap j₀ j)
    -- the target set equals the `hfac2` set
    have hseteq : (chartMap i ⁻¹' (chartImageP i₀ U₀ ∩ chartSet i)
        ∩ (fun z => liftProjMap i₀ j₀ ϕ₀ (chartMap i z)) ⁻¹' chartSet j)
        = {z : Fin k → Ri R |
            z ∈ A ∧ ϕ₀ (transitionMap i i₀ z) ∈ (chartOverlap j₀ j : Set (Fin ℓ → Ri R))} := by
      rw [chartMap_preimage_chartImageP]
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, hA]
      have hrep : liftProjMap i₀ j₀ ϕ₀ (chartMap i z)
          = chartMap j₀ (ϕ₀ (transitionMap i i₀ z)) := by
        rw [liftProjMap, ← transitionMap_eq_chartInv_chartMap]
      constructor
      · rintro ⟨⟨hov, hU⟩, hj⟩
        rw [hrep, chartMap_mem_chartSet_iff] at hj
        exact ⟨⟨hov, hU⟩, hj⟩
      · rintro ⟨⟨hov, hU⟩, hj⟩
        rw [hrep, chartMap_mem_chartSet_iff]
        exact ⟨⟨hov, hU⟩, hj⟩
    rw [hseteq]; exact hfac2
  -- `ϕ` is of class `𝒮^m`
  have hϕclass : IsSClassMapP m U V ϕ := by
    rw [hUdef, hVdef, hϕdef]
    exact isSClassMapP_liftProjMap i₀ j₀ hU₀open hU₀sa hϕ₀coords
      (by rw [← hUdef, ← hVdef, ← hϕdef]; exact hϕmaps) hDom
  -- assemble the conclusion
  refine ⟨U, V, ϕ, ?_, ?_, ?_, ?_, ?_, ?_, hϕclass, ?_, ?_⟩
  · rw [hUdef]; exact isSemialgebraicSetP_chartImageP i₀ hU₀sa
  · rw [hUdef]; exact isOpen_chartImageP i₀ (isOpenC_iff_isOpen_realEquiv.mpr hU₀open)
  · rw [hmemU]; exact ⟨hx₀, hx₀Ua⟩
  · rw [hVdef]; exact isSemialgebraicSetP_chartImageP j₀ hV₀sa
  · rw [hVdef]; exact isOpen_chartImageP j₀ (isOpenC_iff_isOpen_realEquiv.mpr hV₀open)
  · rw [hmemV]; exact ⟨hy₀, hy₀Va⟩
  · -- `ϕ x₀ = y₀`
    have hϕx₀ : ϕ x₀ = chartMap j₀ (ϕ₀ (chartInv i₀ x₀)) := by rw [hϕdef, liftProjMap]
    rw [hϕx₀]
    have hcij : ϕ₀ (chartInv i₀ x₀) = realEquiv.symm (ϕa x₀a) := by
      rw [hϕ₀, hx₀a]
    rw [hcij, hϕax₀]
    -- `chartMap j₀ (realEquiv.symm y₀a) = chartMap j₀ (chartInv j₀ y₀) = y₀`
    rw [hy₀a, Equiv.symm_apply_apply]
    have hy₀rep : y₀.rep j₀ ≠ 0 := by rw [chartSet_eq] at hy₀; exact hy₀
    exact chartMap_chartInv j₀ y₀ hy₀rep
  · -- the implicit equivalence
    intro x hx y hy
    rw [hmemU] at hx
    rw [hmemV] at hy
    obtain ⟨hxi₀, hxUa⟩ := hx
    obtain ⟨hyj₀, hyVa⟩ := hy
    -- realified coordinates of `x`, `y`
    set xa : Fin (k + k) → R := realEquiv (chartInv i₀ x) with hxa
    set ya : Fin (ℓ + ℓ) → R := realEquiv (chartInv j₀ y) with hya
    -- apply the affine implicit equivalence at `(xa, ya)`
    have haff := himpl xa hxUa ya hyVa
    rw [haff]
    -- transport `ya = ϕa xa` to `y = ϕ x`
    constructor
    · intro hya_eq
      -- `chartInv j₀ y = realEquiv.symm (ϕa xa) = ϕ₀ (chartInv i₀ x)`
      have hcoord : chartInv j₀ y = ϕ₀ (chartInv i₀ x) := by
        have h1 : chartInv j₀ y = realEquiv.symm ya := by rw [hya, Equiv.symm_apply_apply]
        rw [h1, hya_eq, hϕ₀, hxa]
      have hyjrep : y.rep j₀ ≠ 0 := by rw [chartSet_eq] at hyj₀; exact hyj₀
      have hyrep : y = chartMap j₀ (chartInv j₀ y) :=
        (chartMap_chartInv j₀ y hyjrep).symm
      have hϕx : ϕ x = chartMap j₀ (ϕ₀ (chartInv i₀ x)) := by rw [hϕdef, liftProjMap]
      rw [hyrep, hcoord, ← hϕx]
    · intro hy_eq
      -- from `y = ϕ x = chartMap j₀ (ϕ₀ (chartInv i₀ x))`, read off `chartInv j₀ y`
      have hϕx : ϕ x = chartMap j₀ (ϕ₀ (chartInv i₀ x)) := by rw [hϕdef, liftProjMap]
      have hcij : chartInv j₀ y = ϕ₀ (chartInv i₀ x) := by
        rw [hy_eq, hϕx, chartInv_chartMap]
      have : ya = realEquiv (ϕ₀ (chartInv i₀ x)) := by rw [hya, hcij]
      rw [this, hϕ₀, hxa, Equiv.apply_symm_apply]

end Azurite.BPR.Chapter4
