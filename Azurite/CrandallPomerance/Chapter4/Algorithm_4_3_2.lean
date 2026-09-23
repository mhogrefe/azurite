/-
  Crandall–Pomerance, Algorithm 4.3.2 (finding a principal
  generator): the Euclidean algorithm in `Z_n[x]`, where the only
  obstruction is inverting a leading coefficient — and any failure to
  invert exhibits a nontrivial factor of `n`.

  Given `n > 1` and `f, g ∈ Z_n[x]` with `g` monic, the algorithm
  returns either a nontrivial factor of `n`, or a monic
  `h = gcd(f, g)` in the sense of Definition 4.3.1: the ideal
  `(f, g)` equals the ideal `(h)`.  Each round makes `f` monic by
  multiplying with the inverse of its leading coefficient `c` — found
  by the extended Euclidean algorithm (the book's Algorithm 2.1.4;
  our computable rails are `AzInt.egcd` / `AzZMod.inv`) exactly when
  `gcd(c, n) = 1`, while otherwise `gcd(c, n)` is a nontrivial factor
  of `n`, since `c ≠ 0` forces `gcd(c, n) < n`.  Then the pair
  `(f, g)` becomes `(g mod f, f)`: division with remainder by a monic
  polynomial needs no invertibility at all.

  The book's precondition "`f = 0` or `deg f ≤ deg g`" is only for
  the running-time analysis; correctness needs no relation between
  the degrees, and we do not assume one.

  Formalized as `gcdOrFactor : ℕ ⊕ (ZMod n)[X]` by well-founded
  recursion on `deg f`, with the specification split into
  `gcdOrFactor_factor` (an `inl` verdict is a nontrivial divisor of
  `n`) and `gcdOrFactor_gcd` (an `inr` verdict is monic and generates
  the pair ideal).  `isCoprime_iff_of_gcdOrFactor` ties back to
  Definition 4.3.1 — `f, g` are coprime exactly when the computed
  generator is a unit — and `gcdOrFactor_ne_inl_of_prime` records
  that over a prime modulus the algorithm never fails.
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

namespace Azurite

namespace CP

open Polynomial

/-! ### Span bookkeeping for the two Euclidean moves -/

/-- Scaling one generator by a unit does not change a pair ideal. -/
private theorem span_pair_isUnit_mul {R : Type*} [CommRing R] {v : R}
    (hv : IsUnit v) (f g : R) :
    Ideal.span {v * f, g} = Ideal.span {f, g} := by
  apply le_antisymm
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Ideal.mul_mem_left _ v (Ideal.subset_span (by simp)),
      Ideal.subset_span (by simp)⟩
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · obtain ⟨u, rfl⟩ := hv
      have hf : f = ↑u⁻¹ * (↑u * f) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      exact hf ▸ Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.subset_span (by simp)

/-- The Euclidean step: replacing `g` by `g mod f` (and swapping)
preserves the pair ideal. -/
private theorem span_pair_modByMonic {R : Type*} [CommRing R]
    (f g : R[X]) :
    Ideal.span {g %ₘ f, f} = Ideal.span {f, g} := by
  have hdiv : g %ₘ f + f * (g /ₘ f) = g := modByMonic_add_div g f
  apply le_antisymm
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · have h2 : g - f * (g /ₘ f) ∈ Ideal.span ({f, g} : Set R[X]) :=
        Ideal.sub_mem _ (Ideal.subset_span (by simp))
          (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      have hr : g %ₘ f = g - f * (g /ₘ f) := by linear_combination hdiv
      rw [hr]
      exact h2
    · exact Ideal.subset_span (by simp)
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · exact Ideal.subset_span (by simp)
    · have h2 : g %ₘ f + f * (g /ₘ f)
          ∈ Ideal.span ({g %ₘ f, f} : Set R[X]) :=
        Ideal.add_mem _ (Ideal.subset_span (by simp))
          (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      rw [hdiv] at h2
      exact h2

/-- Normalizing by the inverse of a unit leading coefficient yields a
monic polynomial. -/
private theorem monic_inverse_mul {R : Type*} [CommRing R]
    {f : R[X]} (hf : f ≠ 0) (hc : IsUnit f.leadingCoeff) :
    (C (Ring.inverse f.leadingCoeff) * f).Monic := by
  have : Nontrivial R :=
    ⟨f.leadingCoeff, 0, fun h => hf (leadingCoeff_eq_zero.mp h)⟩
  rw [Monic, leadingCoeff_mul']
  · rw [leadingCoeff_C]
    exact Ring.inverse_mul_cancel _ hc
  · rw [leadingCoeff_C, Ring.inverse_mul_cancel _ hc]
    exact one_ne_zero

/-- A residue whose value is coprime to the modulus is a unit
(including the degenerate modulus `0`, where the value is the absolute
value). -/
private theorem isUnit_of_val_gcd_eq_one : ∀ {n : ℕ} {c : ZMod n},
    Nat.gcd (ZMod.val c) n = 1 → IsUnit c := by
  intro n c hc
  match n, c, hc with
  | 0, c, hc =>
    rw [Nat.gcd_zero_right] at hc
    exact Int.isUnit_iff_natAbs_eq.mpr hc
  | m + 1, c, hc =>
    have hu : IsUnit ((ZMod.val c : ℕ) : ZMod (m + 1)) :=
      (ZMod.isUnit_iff_coprime _ _).mpr hc
    rwa [ZMod.natCast_rightInverse c] at hu

/-! ### The algorithm -/

set_option maxHeartbeats 1600000 in
/-- **Algorithm 4.3.2 (finding a principal generator)**: attempt to
compute a monic gcd in `Z_n[x]` by the Euclidean algorithm,
normalizing each leading coefficient by the inverse computed via the
extended Euclidean algorithm; report the nontrivial factor
`gcd(c, n)` of `n` if a leading coefficient `c` is not invertible. -/
noncomputable def gcdOrFactor (n : ℕ) (f g : Polynomial (ZMod n)) :
    ℕ ⊕ Polynomial (ZMod n) :=
  if _hf : f = 0 then .inr g
  else if _hc : Nat.gcd f.leadingCoeff.val n = 1 then
    gcdOrFactor n (g %ₘ (C (Ring.inverse f.leadingCoeff) * f))
      (C (Ring.inverse f.leadingCoeff) * f)
  else .inl (Nat.gcd f.leadingCoeff.val n)
termination_by (if f = 0 then 0 else f.natDegree + 1 : ℕ)
decreasing_by
  have hmono := monic_inverse_mul _hf (isUnit_of_val_gcd_eq_one _hc)
  have : Nontrivial (Polynomial (ZMod n)) := nontrivial_of_ne f 0 _hf
  have : Nontrivial (ZMod n) := Polynomial.nontrivial_iff.mp inferInstance
  have hdeg : (g %ₘ (C (Ring.inverse f.leadingCoeff) * f)).degree
      < f.degree := by
    calc (g %ₘ (C (Ring.inverse f.leadingCoeff) * f)).degree
        < (C (Ring.inverse f.leadingCoeff) * f).degree :=
          degree_modByMonic_lt g hmono
    _ ≤ f.degree := by
        refine le_trans (degree_mul_le _ _) ?_
        refine le_trans (add_le_add degree_C_le le_rfl) ?_
        rw [zero_add]
  rw [ite_eq_right _hf]
  by_cases hr : g %ₘ (C (Ring.inverse f.leadingCoeff) * f) = 0
  · rw [ite_eq_left hr]
    omega
  · rw [ite_eq_right hr]
    have := Polynomial.natDegree_lt_natDegree hr hdeg
    omega

/-! ### The specification -/

/-- A factor verdict of Algorithm 4.3.2 is a nontrivial divisor of
`n`. -/
theorem gcdOrFactor_factor {n : ℕ} (hn : 1 < n)
    {f g : Polynomial (ZMod n)} {d : ℕ}
    (hd : gcdOrFactor n f g = .inl d) : d ∣ n ∧ 1 < d ∧ d < n := by
  have : NeZero n := ⟨by omega⟩
  induction f, g using gcdOrFactor.induct n with
  | case1 g =>
    rw [gcdOrFactor, dite_eq_left rfl] at hd
    exact absurd hd (by simp)
  | case2 f g hf hc ih =>
    rw [gcdOrFactor, dite_eq_right hf, dite_eq_left hc] at hd
    exact ih hd
  | case3 f g hf hc =>
    rw [gcdOrFactor, dite_eq_right hf, dite_eq_right hc] at hd
    obtain rfl : Nat.gcd f.leadingCoeff.val n = d := by simpa using hd
    have hc0 : f.leadingCoeff ≠ 0 := fun h => hf (leadingCoeff_eq_zero.mp h)
    have hval0 : f.leadingCoeff.val ≠ 0 := fun h =>
      hc0 ((ZMod.val_eq_zero _).mp h)
    have hdvdn : Nat.gcd f.leadingCoeff.val n ∣ n := Nat.gcd_dvd_right _ _
    have hg0 : Nat.gcd f.leadingCoeff.val n ≠ 0 := by
      intro h0
      rw [Nat.gcd_eq_zero_iff] at h0
      omega
    have hgle : Nat.gcd f.leadingCoeff.val n ≤ f.leadingCoeff.val :=
      Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
    have hvlt : f.leadingCoeff.val < n := ZMod.val_lt _
    exact ⟨hdvdn, by omega, by omega⟩

/-- A gcd verdict of Algorithm 4.3.2 is monic and generates the pair
ideal — it IS `gcd(f, g)` in the sense of Definition 4.3.1. -/
theorem gcdOrFactor_gcd {n : ℕ} {f g : Polynomial (ZMod n)}
    (hg : g.Monic) {h : Polynomial (ZMod n)}
    (hh : gcdOrFactor n f g = .inr h) :
    h.Monic ∧ Ideal.span {f, g} = Ideal.span {h} := by
  induction f, g using gcdOrFactor.induct n with
  | case1 g =>
    rw [gcdOrFactor, dite_eq_left rfl] at hh
    obtain rfl : g = h := by simpa using hh
    exact ⟨hg, Submodule.span_insert_zero⟩
  | case2 f g hf hc ih =>
    rw [gcdOrFactor, dite_eq_right hf, dite_eq_left hc] at hh
    obtain ⟨hmono, hspan⟩ := ih
      (monic_inverse_mul hf (isUnit_of_val_gcd_eq_one hc)) hh
    refine ⟨hmono, ?_⟩
    rw [← hspan, span_pair_modByMonic,
      span_pair_isUnit_mul (isUnit_C.mpr
        (IsUnit.of_mul_eq_one f.leadingCoeff
          (Ring.inverse_mul_cancel _ (isUnit_of_val_gcd_eq_one hc))))]
  | case3 f g hf hc =>
    rw [gcdOrFactor, dite_eq_right hf, dite_eq_right hc] at hh
    exact absurd hh (by simp)

/-- Definition 4.3.1 through the algorithm: `f` and `g` are coprime in
`Z_n[x]` exactly when the computed principal generator is a unit. -/
theorem isCoprime_iff_of_gcdOrFactor {n : ℕ}
    {f g h : Polynomial (ZMod n)} (hg : g.Monic)
    (hh : gcdOrFactor n f g = .inr h) : IsCoprime f g ↔ IsUnit h := by
  obtain ⟨-, hspan⟩ := gcdOrFactor_gcd hg hh
  rw [← Ideal.sup_eq_top_iff_isCoprime, ← Ideal.span_insert, hspan,
    Ideal.span_singleton_eq_top]

/-- Over a prime modulus the algorithm never fails: every nonzero
leading coefficient is invertible. -/
theorem gcdOrFactor_ne_inl_of_prime {p : ℕ} (hp : p.Prime)
    (f g : Polynomial (ZMod p)) (d : ℕ) :
    gcdOrFactor p f g ≠ .inl d := by
  have := Fact.mk hp
  induction f, g using gcdOrFactor.induct p with
  | case1 g =>
    rw [gcdOrFactor, dite_eq_left rfl]
    simp
  | case2 f g hf hc ih =>
    rw [gcdOrFactor, dite_eq_right hf, dite_eq_left hc]
    exact ih
  | case3 f g hf hc =>
    exfalso
    apply hc
    have hc0 : f.leadingCoeff ≠ 0 :=
      fun h => hf (leadingCoeff_eq_zero.mp h)
    have hval0 : f.leadingCoeff.val ≠ 0 := fun h =>
      hc0 ((ZMod.val_eq_zero _).mp h)
    have hvlt : f.leadingCoeff.val < p := ZMod.val_lt _
    rw [Nat.gcd_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr
      (fun hdvd => hval0 (Nat.eq_zero_of_dvd_of_lt hdvd hvlt))

end CP

end Azurite
