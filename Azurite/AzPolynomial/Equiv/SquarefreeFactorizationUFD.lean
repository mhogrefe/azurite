import Azurite.AzPolynomial.Equiv.SquarefreeFactorization
import Azurite.AzPolynomial.Equiv.CharZeroSquarefree

/-!
# Yun's square-free factorization over a characteristic-zero UFD: the product identity

The correctness of the computable Yun algorithm (`squarefreeFactorization`, GCL
Algorithm 8.2) is developed over a *field* in
`Azurite.AzPolynomial.Equiv.SquarefreeFactorization`, via the abstract mirror
`yunPoly` on `Polynomial K` (Mathlib's monic-normalized gcd and Euclidean
division `/`).

This file generalizes the **product identity** to a coefficient ring `R` that is
only a characteristic-zero UFD (`[CommRing R] [IsDomain R]
[UniqueFactorizationMonoid R] [StrongNormalizedGCDMonoid R] [CharZero R]`), *not*
necessarily a field. Two obstacles are handled:

* `Polynomial R` for a non-field `R` has **no** `HDiv`/`/`. The "divide by the
  gcd" step is reformulated with a choice-based exact division `edivExact`
  (the unique cofactor in the domain `Polynomial R`).
* squarefree `⇒` coprime-with-derivative is *false* over a non-field UFD; but for
  the **primitive** multiplicity classes it holds elementarily
  (`primitive_squarefree_irreducible_not_dvd_derivative`, the shipped enabler in
  `Equiv.CharZeroSquarefree`). Accordingly the `YunFamily` classes are carried as
  **primitive + normalized** rather than monic.

The bridge from the computable algorithm to the abstract `yunPoly` is re-proven
over `R`: the exact quotient `exactDivQuoRem` computes `edivExact` (both are the
unique cofactor of `toPoly (gcd …) ∣ toPoly …`, and the gcd always divides), and
the computable `GcdImpl.gcd` matching Mathlib's `GCDMonoid.gcd` is supplied as a
hypothesis (`hgcd_law`) — discharged instance-by-instance downstream.

The field development is untouched; `squarefreeFactorization_prod` there remains
the specialization.

Deferred (product path only, this round): the squarefreeness and
pairwise-coprimality output theorems over `R`.
-/

namespace Azurite.AzPolynomial.UFD

open Polynomial

set_option linter.unusedSectionVars false

/-! ### Choice-based exact division in a domain -/

open Classical in
/-- Exact division in a commutative ring: the (chosen) cofactor when `g ∣ w`,
else `0`. In a domain the cofactor is unique; only the identity `q · g = w` is
needed for the loop. -/
noncomputable def edivExact {S : Type _} [CommRing S] (w g : S) : S :=
  if h : g ∣ w then h.choose else 0

theorem edivExact_mul {S : Type _} [CommRing S] {w g : S} (h : g ∣ w) :
    edivExact w g * g = w := by
  rw [edivExact, dite_eq_left h, mul_comm]; exact h.choose_spec.symm

theorem edivExact_eq_of_mul {S : Type _} [CommRing S] [IsDomain S] {w g q : S}
    (hg0 : g ≠ 0) (h : w = g * q) : edivExact w g = q := by
  have hdvd : g ∣ w := ⟨q, h⟩
  have h1 : edivExact w g * g = w := edivExact_mul hdvd
  have h2 : edivExact w g * g = q * g := by rw [h1, h]; ring
  exact mul_right_cancel₀ hg0 h2

variable {R : Type _} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [StrongNormalizedGCDMonoid R] [CharZero R]

/-! ### Primitivity helpers -/

/-- A finite product of primitive polynomials is primitive (Gauss). -/
theorem isPrimitive_finset_prod {ι : Type _} (s : Finset ι) (A : ι → R[X])
    (h : ∀ j ∈ s, (A j).IsPrimitive) : (∏ j ∈ s, A j).IsPrimitive := by
  classical
  induction s using Finset.induction with
  | empty => simp [Polynomial.isPrimitive_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- A power of a primitive polynomial is primitive. -/
theorem isPrimitive_pow (p : R[X]) (hp : p.IsPrimitive) : ∀ k, (p ^ k).IsPrimitive
  | 0 => by rw [pow_zero]; exact Polynomial.isPrimitive_one
  | k + 1 => by rw [pow_succ]; exact (isPrimitive_pow p hp k).mul hp

/-- A primitive, normalized, constant polynomial is `1`. -/
theorem primitive_normalized_natDegree_zero_eq_one {p : R[X]} (hp : p.IsPrimitive)
    (hn : _root_.normalize p = p) (h : p.natDegree = 0) : p = 1 := by
  have hC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h
  have hu : IsUnit p := hC ▸ (hp _ (hC ▸ dvd_refl p)).map Polynomial.C
  rw [← hn]; exact normalize_eq_one.mpr hu

/-! ### The Yun sum -/

/-- The "Yun sum" `∑_{j ∈ s} (c j)·(A j)'·∏_{k ∈ s, k ≠ j} A k`: the shape of the
`z` iterate of the Yun loop over the squarefree class family `A`. -/
noncomputable def ysum (A : ℕ → R[X]) (s : Finset ℕ) (c : ℕ → ℕ) : R[X] :=
  ∑ j ∈ s, (c j : R[X]) * Polynomial.derivative (A j) * ∏ k ∈ s.erase j, A k

theorem ysum_def (A : ℕ → R[X]) (s : Finset ℕ) (c : ℕ → ℕ) :
    ysum A s c
      = ∑ j ∈ s, (c j : R[X]) * Polynomial.derivative (A j) * ∏ k ∈ s.erase j, A k := rfl

/-- Pulling the vanishing-coefficient element out of a Yun sum. -/
theorem ysum_erase {A : ℕ → R[X]} {s : Finset ℕ} {c : ℕ → ℕ} {i : ℕ}
    (hi : i ∈ s) (hci : c i = 0) :
    ysum A s c = A i * ysum A (s.erase i) c := by
  rw [ysum_def, ysum_def, ← Finset.add_sum_erase _ _ hi, hci]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
  have hi' : i ∈ s.erase j := Finset.mem_erase.mpr ⟨fun h => hji h.symm, hi⟩
  rw [← Finset.mul_prod_erase _ _ hi', Finset.erase_right_comm]
  ring

/-- Subtracting the derivative of the product decrements every coefficient of a
Yun sum. -/
theorem ysum_sub_derivative {A : ℕ → R[X]} {s : Finset ℕ} {c c' : ℕ → ℕ}
    (hc : ∀ j ∈ s, 1 ≤ c j) (hc' : ∀ j ∈ s, c' j = c j - 1) :
    ysum A s c - Polynomial.derivative (∏ j ∈ s, A j) = ysum A s c' := by
  rw [ysum_def, ysum_def, Polynomial.derivative_prod_finset, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hcast : (c' j : R[X]) = (c j : R[X]) - 1 := by
    rw [hc' j hj, Nat.cast_sub (hc j hj), Nat.cast_one]
  rw [hcast]; ring

/-! ### The squarefree class family (primitive + normalized) -/

/-- The hypotheses feeding the Yun loop invariant: `A j` are the primitive,
normalized, squarefree, pairwise coprime multiplicity classes of the input, with
the top class `A m` nontrivial. -/
structure YunFamily (A : ℕ → R[X]) (m : ℕ) : Prop where
  primitive : ∀ j, (A j).IsPrimitive
  normalized : ∀ j, _root_.normalize (A j) = A j
  squarefree : ∀ j, Squarefree (A j)
  coprime : ∀ ⦃j k : ℕ⦄, j ≠ k → ∀ ⦃p : R[X]⦄, Irreducible p → p ∣ A j → p ∣ A k → False
  one_le : 1 ≤ m
  top_ne_one : A m ≠ 1

theorem YunFamily.natDegree_zero_eq_one {A : ℕ → R[X]} {m : ℕ}
    (hF : YunFamily A m) (j : ℕ) (h : (A j).natDegree = 0) : A j = 1 :=
  primitive_normalized_natDegree_zero_eq_one (hF.primitive j) (hF.normalized j) h

theorem YunFamily.top_natDegree_ne_zero {A : ℕ → R[X]} {m : ℕ}
    (hF : YunFamily A m) : (A m).natDegree ≠ 0 := fun h =>
  hF.top_ne_one (hF.natDegree_zero_eq_one m h)

/-- An irreducible factor of a class has positive degree (a constant irreducible
would divide the primitive class, hence be a unit). -/
theorem YunFamily.irr_factor_natDegree_ne_zero {A : ℕ → R[X]} {m : ℕ}
    (hF : YunFamily A m) {p : R[X]} (hp : Irreducible p) {j₀ : ℕ} (hpj₀ : p ∣ A j₀) :
    p.natDegree ≠ 0 := by
  intro h0
  have hpp : p.IsPrimitive := isPrimitive_of_dvd (hF.primitive j₀) hpj₀
  have hC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
  exact hp.not_isUnit (hC ▸ ((hpp _ (hC ▸ dvd_refl p)).map Polynomial.C))

/-- **Workhorse**: an irreducible factor of a class member does not divide a Yun
sum whose coefficient at that member is nonzero (characteristic zero: the
coefficient survives; primitive-squarefree: the derivative factor survives, via
the char-0-UFD enabler; coprimality: the other classes survive). -/
theorem YunFamily.not_dvd_ysum {A : ℕ → R[X]} {m : ℕ}
    (hF : YunFamily A m) {s : Finset ℕ} {c : ℕ → ℕ} {p : R[X]} (hp : Irreducible p)
    {j₀ : ℕ} (hj₀ : j₀ ∈ s) (hpj₀ : p ∣ A j₀) (hc : c j₀ ≠ 0) :
    ¬ p ∣ ysum A s c := by
  intro hdvd
  have hprime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
  have hrest : p ∣ ∑ j ∈ s.erase j₀,
      (c j : R[X]) * Polynomial.derivative (A j) * ∏ k ∈ s.erase j, A k := by
    refine Finset.dvd_sum fun j hj => ?_
    obtain ⟨hjne, hjs⟩ := Finset.mem_erase.mp hj
    have hj₀' : j₀ ∈ s.erase j := Finset.mem_erase.mpr ⟨fun h => hjne h.symm, hj₀⟩
    exact Dvd.dvd.mul_left (hpj₀.trans (Finset.dvd_prod_of_mem _ hj₀')) _
  have hterm : p ∣ (c j₀ : R[X]) * Polynomial.derivative (A j₀) * ∏ k ∈ s.erase j₀, A k := by
    have hsplit : (c j₀ : R[X]) * Polynomial.derivative (A j₀) * ∏ k ∈ s.erase j₀, A k
        = ysum A s c - ∑ j ∈ s.erase j₀,
            (c j : R[X]) * Polynomial.derivative (A j) * ∏ k ∈ s.erase j, A k := by
      rw [ysum_def, ← Finset.add_sum_erase _ _ hj₀]; ring
    rw [hsplit]; exact dvd_sub hdvd hrest
  rcases hprime.dvd_mul.mp hterm with hd | hd
  · rcases hprime.dvd_mul.mp hd with hd' | hd'
    · -- `p` (positive degree) cannot divide the nonzero constant coefficient
      have hne0 : ((c j₀ : R[X])) ≠ 0 := Nat.cast_ne_zero.mpr hc
      have hle := Polynomial.natDegree_le_of_dvd hd' hne0
      rw [Polynomial.natDegree_natCast] at hle
      exact hF.irr_factor_natDegree_ne_zero hp hpj₀ (Nat.le_zero.mp hle)
    · -- `p` cannot divide the derivative: `A j₀` is primitive squarefree (char 0)
      exact primitive_squarefree_irreducible_not_dvd_derivative
        (hF.primitive j₀) (hF.squarefree j₀) hp hpj₀ hd'
  · -- `p` cannot divide the other classes
    obtain ⟨k, hk, hpk⟩ := hprime.exists_mem_finset_dvd hd
    exact hF.coprime (Finset.mem_erase.mp hk).1 hp hpk hpj₀

/-- The gcd of the classes' product with a Yun sum with all-nonzero coefficients
is `1`. -/
theorem YunFamily.gcd_prod_ysum {A : ℕ → R[X]} {m : ℕ}
    (hF : YunFamily A m) {s : Finset ℕ} {c : ℕ → ℕ} (hc : ∀ j ∈ s, c j ≠ 0) :
    GCDMonoid.gcd (∏ j ∈ s, A j) (ysum A s c) = 1 := by
  have hWne : (∏ j ∈ s, A j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => (hF.primitive j).ne_zero)
  have hne : GCDMonoid.gcd (∏ j ∈ s, A j) (ysum A s c) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hWne (gcd_dvd_left _ _)
  have hu : IsUnit (GCDMonoid.gcd (∏ j ∈ s, A j) (ysum A s c)) := by
    by_contra hu
    obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hu hne
    obtain ⟨j₀, hj₀, hpj₀⟩ :=
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp).exists_mem_finset_dvd
        (hpd.trans (gcd_dvd_left _ _))
    exact hF.not_dvd_ysum hp hj₀ hpj₀ (hc j₀ hj₀) (hpd.trans (gcd_dvd_right _ _))
  rw [← _root_.normalize_gcd]
  exact normalize_eq_one.mpr hu

/-- A Yun sum is nonzero as soon as one nontrivial class has a nonzero
coefficient. -/
theorem YunFamily.ysum_ne_zero {A : ℕ → R[X]} {m : ℕ}
    (hF : YunFamily A m) {s : Finset ℕ} {c : ℕ → ℕ} {j₀ : ℕ} (hj₀ : j₀ ∈ s)
    (hA : A j₀ ≠ 1) (hc : c j₀ ≠ 0) : ysum A s c ≠ 0 := by
  intro h0
  have hnu : ¬IsUnit (A j₀) := fun hu =>
    hA (by rw [← hF.normalized j₀]; exact normalize_eq_one.mpr hu)
  obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hnu (hF.primitive j₀).ne_zero
  exact hF.not_dvd_ysum hp hj₀ hpd hc (h0 ▸ dvd_zero p)

/-! ### Interval helpers -/

theorem Icc_eq_insert_Icc {i m : ℕ} (h : i ≤ m) :
    Finset.Icc i m = insert i (Finset.Icc (i + 1) m) := by
  ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega

theorem notMem_Icc_succ (i m : ℕ) : i ∉ Finset.Icc (i + 1) m := by
  simp only [Finset.mem_Icc]; omega

theorem Icc_erase_left' (i m : ℕ) :
    (Finset.Icc i m).erase i = Finset.Icc (i + 1) m := by
  ext j; simp only [Finset.mem_erase, Finset.mem_Icc]; omega

theorem Ico_one_succ_eq_Icc (m : ℕ) : Finset.Ico 1 (1 + m) = Finset.Icc 1 m := by
  ext j; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega

/-! ### The abstract Yun loop (via `GCDMonoid.gcd` and `edivExact`) -/

open Classical in
/-- Abstract mirror of the Yun loop on `Polynomial R`: Mathlib's normalized gcd
and the choice-based exact division `edivExact`. -/
noncomputable def yunLoopPoly : (fuel : ℕ) → (i : ℕ) → (w z : R[X]) →
    (acc : List (R[X] × ℕ)) → List (R[X] × ℕ)
  | 0, i, w, _, acc => acc ++ [(w, i)]
  | fuel + 1, i, w, z, acc =>
    if z = 0 then acc ++ [(w, i)]
    else
      let g := GCDMonoid.gcd w z
      yunLoopPoly fuel (i + 1) (edivExact w g)
        (edivExact z g - Polynomial.derivative (edivExact w g))
        (if g.natDegree = 0 then acc else acc ++ [(g, i)])

/-- Abstract mirror of Yun's square-free factorization on `Polynomial R`. -/
noncomputable def yunPoly (a : R[X]) : List (R[X] × ℕ) :=
  if a.natDegree = 0 then []
  else
    let c := GCDMonoid.gcd a (Polynomial.derivative a)
    if c.natDegree = 0 then [(a, 1)]
    else yunLoopPoly a.natDegree 1 (edivExact a c)
      (edivExact (Polynomial.derivative a) c - Polynomial.derivative (edivExact a c)) []

theorem yunLoopPoly_zero (i : ℕ) (w z : R[X]) (acc : List (R[X] × ℕ)) :
    yunLoopPoly 0 i w z acc = acc ++ [(w, i)] := rfl

theorem yunLoopPoly_succ_zero (fuel i : ℕ) (w : R[X]) (acc : List (R[X] × ℕ)) :
    yunLoopPoly (fuel + 1) i w 0 acc = acc ++ [(w, i)] := by
  rw [yunLoopPoly, ite_eq_left rfl]

theorem yunLoopPoly_succ_ne_zero (fuel i : ℕ) (w z : R[X])
    (acc : List (R[X] × ℕ)) (hz : z ≠ 0) :
    yunLoopPoly (fuel + 1) i w z acc =
      yunLoopPoly fuel (i + 1) (edivExact w (GCDMonoid.gcd w z))
        (edivExact z (GCDMonoid.gcd w z)
          - Polynomial.derivative (edivExact w (GCDMonoid.gcd w z)))
        (if (GCDMonoid.gcd w z).natDegree = 0 then acc
          else acc ++ [(GCDMonoid.gcd w z, i)]) := by
  rw [yunLoopPoly, ite_eq_right hz]

/-- The terminal emission `(A m, m)` in closed list form. -/
theorem YunFamily.out_top {A : ℕ → R[X]} {m : ℕ} (hF : YunFamily A m)
    (acc : List (R[X] × ℕ)) :
    acc ++ [(A m, m)]
      = acc ++ (((List.range' m (m + 1 - m)).filter fun j => (A j).natDegree ≠ 0).map
          fun j => (A j, j)) := by
  have h1 : m + 1 - m = 1 := by omega
  rw [h1]
  simp [List.range', hF.top_natDegree_ne_zero]

/-- **The Yun loop invariant**: started at counter `i ≤ m` on
`w = ∏_{j ∈ [i, m]} A j` and the corresponding Yun sum (with enough fuel), the
loop emits exactly the nontrivial classes `(A j, j)`, `j ∈ [i, m]`, in order. -/
theorem YunFamily.yunLoopPoly_eq {A : ℕ → R[X]} {m : ℕ} (hF : YunFamily A m) :
    ∀ (fuel i : ℕ) (acc : List (R[X] × ℕ)), i ≤ m → m - i ≤ fuel →
      yunLoopPoly fuel i (∏ j ∈ Finset.Icc i m, A j)
          (ysum A (Finset.Icc i m) fun j => j - i) acc
        = acc ++ (((List.range' i (m + 1 - i)).filter fun j => (A j).natDegree ≠ 0).map
            fun j => (A j, j)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc hle hfuel
    have heq : i = m := by omega
    subst heq
    rw [yunLoopPoly_zero, Finset.Icc_self, Finset.prod_singleton]
    exact hF.out_top acc
  | succ fuel ih =>
    intro i acc hle hfuel
    by_cases heq : i = m
    · subst heq
      have hz : (ysum A (Finset.Icc i i) fun j => j - i) = 0 := by
        rw [ysum_def, Finset.Icc_self, Finset.sum_singleton, Nat.sub_self, Nat.cast_zero,
          zero_mul, zero_mul]
      rw [hz, yunLoopPoly_succ_zero, Finset.Icc_self, Finset.prod_singleton]
      exact hF.out_top acc
    · have hlt : i < m := lt_of_le_of_ne hle heq
      have himem : i ∈ Finset.Icc i m := Finset.mem_Icc.mpr ⟨le_refl i, hle⟩
      have hAine : A i ≠ 0 := (hF.primitive i).ne_zero
      have hw : (∏ j ∈ Finset.Icc i m, A j) = A i * ∏ j ∈ Finset.Icc (i + 1) m, A j := by
        rw [Icc_eq_insert_Icc hle, Finset.prod_insert (notMem_Icc_succ i m)]
      have hz : (ysum A (Finset.Icc i m) fun j => j - i)
          = A i * ysum A (Finset.Icc (i + 1) m) fun j => j - i := by
        rw [ysum_erase (c := fun j => j - i) himem (Nat.sub_self i), Icc_erase_left']
      have hmmem : m ∈ Finset.Icc (i + 1) m := Finset.mem_Icc.mpr ⟨hlt, le_refl m⟩
      have hzne : (ysum A (Finset.Icc i m) fun j => j - i) ≠ 0 := by
        rw [hz]
        exact mul_ne_zero hAine (hF.ysum_ne_zero hmmem hF.top_ne_one (by omega))
      have hgcd : GCDMonoid.gcd (∏ j ∈ Finset.Icc i m, A j)
          (ysum A (Finset.Icc i m) fun j => j - i) = A i := by
        rw [hw, hz, _root_.gcd_mul_left,
          hF.gcd_prod_ysum (fun j hj => by
            have := (Finset.mem_Icc.mp hj).1
            omega),
          mul_one, hF.normalized i]
      rw [yunLoopPoly_succ_ne_zero _ _ _ _ _ hzne, hgcd]
      have hwq : edivExact (∏ j ∈ Finset.Icc i m, A j) (A i)
          = ∏ j ∈ Finset.Icc (i + 1) m, A j :=
        edivExact_eq_of_mul hAine hw
      have hzq : edivExact (ysum A (Finset.Icc i m) fun j => j - i) (A i)
          = ysum A (Finset.Icc (i + 1) m) fun j => j - i :=
        edivExact_eq_of_mul hAine hz
      rw [hwq, hzq,
        ysum_sub_derivative (c' := fun j => j - (i + 1))
          (fun j hj => by
            have := (Finset.mem_Icc.mp hj).1
            omega)
          (fun j hj => by omega),
        ih (i + 1) _ (by omega) (by omega)]
      have hn1 : m + 1 - i = (m - i) + 1 := by omega
      have hn2 : m + 1 - (i + 1) = m - i := by omega
      rw [hn1, hn2, List.range'_succ]
      by_cases hAi : (A i).natDegree = 0
      · rw [ite_eq_left hAi, List.filter_cons_of_neg (by simp [hAi])]
      · rw [ite_eq_right hAi, List.filter_cons_of_pos (by simp [hAi]), List.map_cons]
        simp

/-! ### Existence of the squarefree class decomposition -/

/-- **Squarefree multiplicity decomposition** of a nonconstant primitive
normalized polynomial: grouping the normalized irreducible factors by
multiplicity yields `a = ∏_{j ∈ [1, m]} (A j)^j` with `A j` primitive,
normalized, squarefree, pairwise coprime and `A m ≠ 1` (also `m ≤ deg a`). -/
theorem exists_yunFamily {a : R[X]} (hprim : a.IsPrimitive) (hnorm : _root_.normalize a = a)
    (h0 : a.natDegree ≠ 0) :
    ∃ (m : ℕ) (A : ℕ → R[X]), YunFamily A m ∧
      a = ∏ j ∈ Finset.Icc 1 m, A j ^ j ∧ m ≤ a.natDegree := by
  classical
  have ha0 : a ≠ 0 := hprim.ne_zero
  set f := UniqueFactorizationMonoid.normalizedFactors a with hfdef
  have hirr : ∀ p ∈ f, Irreducible p := fun p hp =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hnormf : ∀ p ∈ f, _root_.normalize p = p := fun p hp =>
    UniqueFactorizationMonoid.normalize_normalized_factor p hp
  have hprimf : ∀ p ∈ f, p.IsPrimitive := fun p hp =>
    isPrimitive_of_dvd hprim (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)
  have hprod : f.prod = a := by
    rw [hfdef, UniqueFactorizationMonoid.prod_normalizedFactors_eq ha0, hnorm]
  have hfne : f ≠ 0 := by
    intro h
    rw [h, Multiset.prod_zero] at hprod
    exact h0 (by rw [← hprod, Polynomial.natDegree_one])
  obtain ⟨p₀, hp₀⟩ := Multiset.exists_mem_of_ne_zero hfne
  set m := f.toFinset.sup (fun p => f.count p) with hmdef
  have hmemF : ∀ {n : ℕ} {p : R[X]},
      p ∈ f.toFinset.filter (fun q => f.count q = n) → p ∈ f :=
    fun h => Multiset.mem_toFinset.mp (Finset.mem_filter.mp h).1
  have hprimC : ∀ n, (∏ p ∈ f.toFinset.filter fun q => f.count q = n, p).IsPrimitive := fun n =>
    isPrimitive_finset_prod _ (fun p => p) fun p hp => hprimf p (hmemF hp)
  have hnormC : ∀ n, _root_.normalize (∏ p ∈ f.toFinset.filter fun q => f.count q = n, p)
      = ∏ p ∈ f.toFinset.filter fun q => f.count q = n, p := fun n => by
    rw [← coe_normalizeHom, map_prod]
    simp only [coe_normalizeHom]
    exact Finset.prod_congr rfl fun p hp => hnormf p (hmemF hp)
  have hm1 : 1 ≤ m :=
    le_trans (Multiset.count_pos.mpr hp₀)
      (Finset.le_sup (f := fun p => f.count p) (Multiset.mem_toFinset.mpr hp₀))
  have hnf : ∀ n, UniqueFactorizationMonoid.normalizedFactors
        (∏ p ∈ f.toFinset.filter fun q => f.count q = n, p)
      = (f.toFinset.filter fun q => f.count q = n).val := by
    intro n
    have hval : (∏ p ∈ f.toFinset.filter (fun q => f.count q = n), p)
        = (f.toFinset.filter fun q => f.count q = n).val.prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hval, UniqueFactorizationMonoid.normalizedFactors_prod_eq _
      (fun q hq => hirr q (hmemF (Finset.mem_val.mp hq)))]
    rw [Multiset.map_congr rfl fun q hq => hnormf q (hmemF (Finset.mem_val.mp hq)),
      Multiset.map_id']
  have hsq : ∀ n, Squarefree (∏ p ∈ f.toFinset.filter fun q => f.count q = n, p) := by
    intro n
    rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors (hprimC n).ne_zero,
      hnf n]
    exact (f.toFinset.filter fun q => f.count q = n).nodup
  have hcop : ∀ ⦃j k : ℕ⦄, j ≠ k → ∀ ⦃p : R[X]⦄, Irreducible p →
      p ∣ (∏ q ∈ f.toFinset.filter fun q => f.count q = j, q) →
      p ∣ (∏ q ∈ f.toFinset.filter fun q => f.count q = k, q) → False := by
    intro j k hjk p hp hpj hpk
    have hprime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
    obtain ⟨q, hq, hpq⟩ := hprime.exists_mem_finset_dvd hpj
    obtain ⟨q', hq', hpq'⟩ := hprime.exists_mem_finset_dvd hpk
    have h1 : Associated p q := hp.associated_of_dvd (hirr q (hmemF hq)) hpq
    have h2 : Associated p q' := hp.associated_of_dvd (hirr q' (hmemF hq')) hpq'
    have h3 : q = q' := by
      rw [← hnormf q (hmemF hq), ← hnormf q' (hmemF hq')]
      exact normalize_eq_normalize_iff_associated.mpr (h1.symm.trans h2)
    exact hjk (by
      rw [← (Finset.mem_filter.mp hq).2, ← (Finset.mem_filter.mp hq').2, h3])
  obtain ⟨pM, hpMF, hpMc⟩ :=
    Finset.exists_mem_eq_sup f.toFinset ⟨p₀, Multiset.mem_toFinset.mpr hp₀⟩
      fun p => f.count p
  have hpMmem : pM ∈ f.toFinset.filter fun q => f.count q = m :=
    Finset.mem_filter.mpr ⟨hpMF, hpMc.symm⟩
  have htop : (∏ p ∈ f.toFinset.filter fun q => f.count q = m, p) ≠ 1 := by
    intro h1
    exact (hirr pM (Multiset.mem_toFinset.mp hpMF)).not_isUnit
      (isUnit_of_dvd_one (h1 ▸ Finset.dvd_prod_of_mem _ hpMmem))
  have hprodid : a = ∏ n ∈ Finset.Icc 1 m,
      (∏ p ∈ f.toFinset.filter fun q => f.count q = n, p) ^ n := by
    have hmap : ∀ p ∈ f.toFinset, f.count p ∈ Finset.Icc 1 m := fun p hp =>
      Finset.mem_Icc.mpr
        ⟨Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp),
          Finset.le_sup (f := fun p => f.count p) hp⟩
    have hfib := Finset.prod_fiberwise_of_maps_to hmap fun p => p ^ f.count p
    rw [← hprod, Finset.prod_multiset_count, ← hfib]
    refine Finset.prod_congr rfl fun n hn => ?_
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
  have hdegAm : 0 < (∏ p ∈ f.toFinset.filter fun q => f.count q = m, p).natDegree := by
    rcases Nat.eq_zero_or_pos
        (∏ p ∈ f.toFinset.filter fun q => f.count q = m, p).natDegree with h | h
    · exact absurd (primitive_normalized_natDegree_zero_eq_one (hprimC m) (hnormC m) h) htop
    · exact h
  have hmle : m ≤ a.natDegree := by
    have hdvd : (∏ p ∈ f.toFinset.filter fun q => f.count q = m, p) ^ m ∣ a := by
      rw [hprodid]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hm1, le_refl m⟩)
    have hb := Polynomial.natDegree_le_of_dvd hdvd ha0
    rw [Polynomial.natDegree_pow] at hb
    exact le_trans (Nat.le_mul_of_pos_right m hdegAm) hb
  exact ⟨m, fun n => ∏ p ∈ f.toFinset.filter fun q => f.count q = n, p,
    ⟨hprimC, hnormC, hsq, hcop, hm1, htop⟩, hprodid, hmle⟩

/-! ### The closed form of `yunPoly` -/

/-- **Closed form**: for nonconstant primitive normalized `a` over a
characteristic-zero UFD, `yunPoly a` is exactly the list of nontrivial
multiplicity classes `(A j, j)`, `j ∈ [1, m]`, in increasing order of `j`. -/
theorem yunPoly_closed_form {a : R[X]} (hprim : a.IsPrimitive)
    (hnorm : _root_.normalize a = a) (h0 : a.natDegree ≠ 0) :
    ∃ (m : ℕ) (A : ℕ → R[X]), YunFamily A m ∧
      a = ∏ j ∈ Finset.Icc 1 m, A j ^ j ∧
      yunPoly a = ((List.range' 1 m).filter fun j => (A j).natDegree ≠ 0).map
        fun j => (A j, j) := by
  obtain ⟨m, A, hF, hprodid, hmdeg⟩ := exists_yunFamily hprim hnorm h0
  refine ⟨m, A, hF, hprodid, ?_⟩
  set CC := ∏ j ∈ Finset.Icc 1 m, A j ^ (j - 1) with hCCdef
  have hCCprim : CC.IsPrimitive :=
    isPrimitive_finset_prod _ _ fun j _ => isPrimitive_pow _ (hF.primitive j) _
  have hCCnorm : _root_.normalize CC = CC := by
    rw [hCCdef, ← coe_normalizeHom, map_prod]
    simp only [coe_normalizeHom]
    exact Finset.prod_congr rfl fun j _ => by
      rw [← coe_normalizeHom, map_pow]
      simp only [coe_normalizeHom]
      rw [hF.normalized j]
  have hCCne : CC ≠ 0 := hCCprim.ne_zero
  -- `a = CC · ∏ A j` and `a' = CC · (Yun sum with coefficients j)`
  have hsplit : a = CC * ∏ j ∈ Finset.Icc 1 m, A j := by
    rw [hprodid, hCCdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have h1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [← pow_succ]
    congr 1
    omega
  have hderiv : Polynomial.derivative a = CC * ysum A (Finset.Icc 1 m) fun j => j := by
    rw [hprodid, Polynomial.derivative_prod_finset, ysum_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [Polynomial.derivative_pow, Polynomial.C_eq_natCast]
    have hCCsplit : CC = A j ^ (j - 1) * ∏ k ∈ (Finset.Icc 1 m).erase j, A k ^ (k - 1) :=
      (Finset.mul_prod_erase _ (fun k => A k ^ (k - 1)) hj).symm
    have hesplit : (∏ k ∈ (Finset.Icc 1 m).erase j, A k ^ k)
        = (∏ k ∈ (Finset.Icc 1 m).erase j, A k ^ (k - 1))
            * ∏ k ∈ (Finset.Icc 1 m).erase j, A k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k hk => ?_
      have h1k : 1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk)).1
      rw [← pow_succ]
      congr 1
      omega
    rw [hesplit, hCCsplit]
    ring
  -- hence `gcd a a' = CC`
  have hc : GCDMonoid.gcd a (Polynomial.derivative a) = CC := by
    rw [hderiv, hsplit, _root_.gcd_mul_left,
      hF.gcd_prod_ysum (fun j hj => by
        have := (Finset.mem_Icc.mp hj).1
        omega),
      mul_one, hCCnorm]
  have hyun : yunPoly a
      = if (GCDMonoid.gcd a (Polynomial.derivative a)).natDegree = 0 then [(a, 1)]
        else yunLoopPoly a.natDegree 1 (edivExact a (GCDMonoid.gcd a (Polynomial.derivative a)))
          (edivExact (Polynomial.derivative a) (GCDMonoid.gcd a (Polynomial.derivative a))
            - Polynomial.derivative
                (edivExact a (GCDMonoid.gcd a (Polynomial.derivative a)))) [] := by
    rw [yunPoly, ite_eq_right h0]
  by_cases hCC0 : CC.natDegree = 0
  · -- `m = 1`: the input is already squarefree
    have hCC1 : CC = 1 := primitive_normalized_natDegree_zero_eq_one hCCprim hCCnorm hCC0
    have hm1 : m = 1 := by
      by_contra hm
      have hdvd : A m ∣ CC := by
        refine dvd_trans (dvd_pow_self (A m) ?_)
          (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hF.one_le, le_refl m⟩))
        have := hF.one_le
        omega
      have hu : IsUnit (A m) := isUnit_of_dvd_one (hCC1 ▸ hdvd)
      exact hF.top_ne_one (by rw [← hF.normalized m]; exact normalize_eq_one.mpr hu)
    subst hm1
    have ha1 : A 1 = a := by
      rw [hprodid, Finset.Icc_self, Finset.prod_singleton, pow_one]
    have hd1 : (A 1).natDegree ≠ 0 := by
      rw [ha1]; exact h0
    rw [hyun, hc, ite_eq_left hCC0, show List.range' 1 1 = [1] from rfl,
      List.filter_cons_of_pos (by simp [hd1]), List.filter_nil, List.map_cons, List.map_nil,
      ha1]
  · -- the loop runs: feed the invariant
    have haq : edivExact a CC = ∏ j ∈ Finset.Icc 1 m, A j :=
      edivExact_eq_of_mul hCCne hsplit
    have hdq : edivExact (Polynomial.derivative a) CC = ysum A (Finset.Icc 1 m) fun j => j :=
      edivExact_eq_of_mul hCCne hderiv
    rw [hyun, hc, ite_eq_right hCC0, haq, hdq,
      ysum_sub_derivative (c' := fun j => j - 1)
        (fun j hj => (Finset.mem_Icc.mp hj).1) (fun j hj => rfl),
      hF.yunLoopPoly_eq a.natDegree 1 [] hF.one_le (by omega),
      Nat.add_sub_cancel, List.nil_append]

/-! ### Products over the emitted list -/

theorem filter_map_pow_prod {A : ℕ → R[X]} (htriv : ∀ j, (A j).natDegree = 0 → A j = 1) :
    ∀ (n i : ℕ),
      (((List.range' i n).filter fun j => (A j).natDegree ≠ 0).map fun j => A j ^ j).prod
        = ∏ j ∈ Finset.Ico i (i + n), A j ^ j := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ihn =>
    intro i
    rw [List.range'_succ,
      Finset.prod_eq_prod_Ico_succ_bot (by omega) (fun j => A j ^ j),
      show i + (n + 1) = (i + 1) + n by omega]
    by_cases hAi : (A i).natDegree = 0
    · rw [List.filter_cons_of_neg (by simp [hAi]), ihn (i + 1),
        htriv i hAi, one_pow, one_mul]
    · rw [List.filter_cons_of_pos (by simp [hAi]), List.map_cons, List.prod_cons, ihn (i + 1)]

/-! ### The product identity for `yunPoly` -/

/-- **Yun's algorithm, product identity** (abstract): the emitted powers multiply
back to the primitive normalized input. -/
theorem yunPoly_prod {a : R[X]} (hprim : a.IsPrimitive) (hnorm : _root_.normalize a = a) :
    ((yunPoly a).map fun gi => gi.1 ^ gi.2).prod = a := by
  by_cases h0 : a.natDegree = 0
  · rw [yunPoly, ite_eq_left h0, primitive_normalized_natDegree_zero_eq_one hprim hnorm h0]
    simp
  · obtain ⟨m, A, hF, hprodid, hclosed⟩ := yunPoly_closed_form hprim hnorm h0
    rw [hclosed, List.map_map,
      show ((fun gi : R[X] × ℕ => gi.1 ^ gi.2) ∘ fun j => (A j, j)) = fun j => A j ^ j
        from rfl,
      filter_map_pow_prod (fun j => hF.natDegree_zero_eq_one j) m 1, Ico_one_succ_eq_Icc,
      ← hprodid]

/-! ### Unit-invariance of `yunPoly` and the `Associated` product identity

The `hnorm` hypothesis of `yunPoly_prod` is a genuine obstacle for a merely
*primitive* input `a` (its leading coefficient need not be a normalized element),
so the exact product identity `∏ = a` fails. It is replaced by the `Associated`
form `Associated (∏ …) a`. Note the *exact* unit invariance `yunPoly (u·a) =
yunPoly a` is **false**: the terminal emission carries the raw running polynomial,
so the top multiplicity class `A_m` absorbs the unit — and with exponent `m`,
scaling by `u^m`, only *associated* to the original. The proof therefore threads
the scaling through the product `Pm` and closes with `Associated`. -/

/-- Exact division scales by a left multiplier over a domain (`g ∣ w`, `g ≠ 0`). -/
theorem edivExact_left_mul {S : Type _} [CommRing S] [IsDomain S] {w g : S} (v : S)
    (hdvd : g ∣ w) (hg0 : g ≠ 0) : edivExact (v * w) g = v * edivExact w g := by
  refine edivExact_eq_of_mul hg0 ?_
  have h1 : edivExact w g * g = w := edivExact_mul hdvd
  calc v * w = v * (edivExact w g * g) := by rw [h1]
    _ = g * (v * edivExact w g) := by ring

/-- Multiplying both gcd arguments by `C` of a unit leaves the normalized gcd
unchanged. -/
theorem gcd_C_mul {c : R} (hc : IsUnit c) (w z : R[X]) :
    GCDMonoid.gcd (Polynomial.C c * w) (Polynomial.C c * z) = GCDMonoid.gcd w z := by
  rw [_root_.gcd_mul_left, normalize_eq_one.mpr (hc.map Polynomial.C), one_mul]

/-- `C` of a unit times a primitive polynomial is primitive. -/
theorem isPrimitive_C_mul {u : R} (hu : IsUnit u) {p : R[X]} (hp : p.IsPrimitive) :
    (Polynomial.C u * p).IsPrimitive :=
  fun r hr => hp r ((IsUnit.dvd_mul_left (hu.map Polynomial.C)).mp hr)

/-- Product of the emitted factors, each raised to its multiplicity. -/
noncomputable def Pm (l : List (R[X] × ℕ)) : R[X] := (l.map fun gi => gi.1 ^ gi.2).prod

theorem Pm_append (l₁ l₂ : List (R[X] × ℕ)) : Pm (l₁ ++ l₂) = Pm l₁ * Pm l₂ := by
  simp [Pm, List.map_append, List.prod_append]

/-- Two units become associated after a common left factor. -/
theorem assoc_units_mul_left {M x y : R[X]} (hx : IsUnit x) (hy : IsUnit y) :
    Associated (M * x) (M * y) :=
  Associated.mul_left M ((associated_one_iff_isUnit.mpr hx).trans
    (associated_one_iff_isUnit.mpr hy).symm)

/-- **Loop-level unit invariance (product form)**: scaling both loop arguments by
`C` of a unit `c` multiplies the emitted product by a unit associated to `C c`. -/
theorem yunLoopPoly_C_mul_prod_assoc {c : R} (hc : IsUnit c) :
    ∀ (fuel i : ℕ) (w z : R[X]) (acc : List (R[X] × ℕ)),
      Associated (Pm (yunLoopPoly fuel i (Polynomial.C c * w) (Polynomial.C c * z) acc))
        (Polynomial.C c * Pm (yunLoopPoly fuel i w z acc)) := by
  have hCc0 : (Polynomial.C c : R[X]) ≠ 0 := by simpa [Polynomial.C_eq_zero] using hc.ne_zero
  have huC : IsUnit (Polynomial.C c : R[X]) := hc.map Polynomial.C
  have hterm : ∀ (i : ℕ) (w : R[X]) (acc : List (R[X] × ℕ)),
      Associated (Pm (acc ++ [(Polynomial.C c * w, i)]))
        (Polynomial.C c * Pm (acc ++ [(w, i)])) := by
    intro i w acc
    rw [Pm_append, Pm_append]
    simp only [Pm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [mul_pow]
    have e1 : Pm acc * (Polynomial.C c ^ i * w ^ i)
        = (Pm acc * w ^ i) * Polynomial.C c ^ i := by rw [Pm]; ring
    have e2 : Polynomial.C c * (Pm acc * w ^ i) = (Pm acc * w ^ i) * Polynomial.C c := by
      rw [Pm]; ring
    rw [show (List.map (fun gi : R[X] × ℕ => gi.1 ^ gi.2) acc).prod = Pm acc from rfl, e1, e2]
    exact assoc_units_mul_left (huC.pow i) huC
  intro fuel
  induction fuel with
  | zero => intro i w z acc; rw [yunLoopPoly_zero, yunLoopPoly_zero]; exact hterm i w acc
  | succ fuel ih =>
    intro i w z acc
    by_cases hz : z = 0
    · subst hz; rw [mul_zero, yunLoopPoly_succ_zero, yunLoopPoly_succ_zero]; exact hterm i w acc
    · have hCz : Polynomial.C c * z ≠ 0 := mul_ne_zero hCc0 hz
      rw [yunLoopPoly_succ_ne_zero _ _ _ _ _ hCz, yunLoopPoly_succ_ne_zero _ _ _ _ _ hz]
      have hg : GCDMonoid.gcd (Polynomial.C c * w) (Polynomial.C c * z)
          = GCDMonoid.gcd w z := gcd_C_mul hc w z
      have hg0 : GCDMonoid.gcd w z ≠ 0 := fun h => hz ((gcd_eq_zero_iff _ _).mp h).2
      rw [hg, edivExact_left_mul _ (gcd_dvd_left w z) hg0,
        edivExact_left_mul _ (gcd_dvd_right w z) hg0, Polynomial.derivative_C_mul,
        show Polynomial.C c * edivExact z (GCDMonoid.gcd w z)
            - Polynomial.C c * Polynomial.derivative (edivExact w (GCDMonoid.gcd w z))
          = Polynomial.C c * (edivExact z (GCDMonoid.gcd w z)
            - Polynomial.derivative (edivExact w (GCDMonoid.gcd w z))) from by ring]
      exact ih (i + 1) _ _ _

/-- **`yunPoly`-level unit invariance (product form)**: `Pm (yunPoly (C c · a))`
is associated to `C c · Pm (yunPoly a)`. -/
theorem yunPoly_C_mul_prod_assoc {c : R} (hc : IsUnit c) (a : R[X]) :
    Associated (Pm (yunPoly (Polynomial.C c * a))) (Polynomial.C c * Pm (yunPoly a)) := by
  have huC : IsUnit (Polynomial.C c : R[X]) := hc.map Polynomial.C
  have hnd : (Polynomial.C c * a).natDegree = a.natDegree := Polynomial.natDegree_C_mul hc.ne_zero
  by_cases h0 : a.natDegree = 0
  · rw [yunPoly, yunPoly, hnd, ite_eq_left h0, ite_eq_left h0]
    simp only [Pm, List.map_nil, List.prod_nil, mul_one]
    exact (associated_one_iff_isUnit.mpr huC).symm
  · have ha0 : a ≠ 0 := fun h => h0 (by rw [h, Polynomial.natDegree_zero])
    set c0 := GCDMonoid.gcd a (Polynomial.derivative a) with hc0def
    have hc0ne : c0 ≠ 0 := fun h => ha0 ((gcd_eq_zero_iff _ _).mp h).1
    have hcda : c0 ∣ a := gcd_dvd_left _ _
    have hcdd : c0 ∣ Polynomial.derivative a := gcd_dvd_right _ _
    by_cases hcz : c0.natDegree = 0
    · rw [yunPoly, hnd, ite_eq_right h0, Polynomial.derivative_C_mul, gcd_C_mul hc a _,
        ← hc0def, ite_eq_left hcz, yunPoly, ite_eq_right h0, ← hc0def, ite_eq_left hcz]
      simp only [Pm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
      exact Associated.refl _
    · have hya : yunPoly a = yunLoopPoly a.natDegree 1 (edivExact a c0)
          (edivExact (Polynomial.derivative a) c0 - Polynomial.derivative (edivExact a c0)) [] := by
        rw [yunPoly, ite_eq_right h0, ← hc0def, ite_eq_right hcz]
      rw [yunPoly, hnd, ite_eq_right h0, Polynomial.derivative_C_mul, gcd_C_mul hc a _,
        ← hc0def, ite_eq_right hcz,
        edivExact_left_mul (Polynomial.C c) hcda hc0ne,
        edivExact_left_mul (Polynomial.C c) hcdd hc0ne,
        Polynomial.derivative_C_mul,
        show Polynomial.C c * edivExact (Polynomial.derivative a) c0
            - Polynomial.C c * Polynomial.derivative (edivExact a c0)
          = Polynomial.C c * (edivExact (Polynomial.derivative a) c0
            - Polynomial.derivative (edivExact a c0)) from by ring, hya]
      exact yunLoopPoly_C_mul_prod_assoc hc a.natDegree 1 _ _ []

set_option maxHeartbeats 1600000 in
/-- **Yun's algorithm, product identity up to associates** (abstract): for a
merely *primitive* input (no normalization), the emitted powers multiply back to
the input *up to a unit*. -/
theorem yunPoly_prod_associated {a : R[X]} (hprim : a.IsPrimitive) :
    Associated (Pm (yunPoly a)) a := by
  obtain ⟨u, hu⟩ := _root_.normalize_associated a
  set b := _root_.normalize a with hbdef
  obtain ⟨d, hd, hdC⟩ := Polynomial.isUnit_iff.mp (u⁻¹).isUnit
  obtain ⟨d', hd', hd'C⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hbinv : b = a * ↑u⁻¹ := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  have ha_eq : a = Polynomial.C d' * b := by rw [hd'C, mul_comm]; exact hu.symm
  have hb_eq : b = Polynomial.C d * a := by rw [hdC, mul_comm]; exact hbinv
  have hbprim : b.IsPrimitive := by rw [hb_eq]; exact isPrimitive_C_mul hd hprim
  have hbnorm : _root_.normalize b = b := by rw [hbdef, normalize_idem]
  have hbprod : Pm (yunPoly b) = b := yunPoly_prod hbprim hbnorm
  rw [ha_eq]
  have key : Polynomial.C d' * Pm (yunPoly b) = Polynomial.C d' * b := by rw [hbprod]
  exact key ▸ yunPoly_C_mul_prod_assoc hd' b

/-! ### Squarefreeness and pairwise coprimality for `yunPoly` -/

/-- Distinct Yun classes are relatively prime. Over a (non-Bézout) UFD the
correct notion is `IsRelPrime` (every common divisor is a unit), read directly
off the `YunFamily.coprime` "no shared irreducible factor" field — not the
field-only `IsCoprime`. -/
theorem YunFamily.isRelPrime' {A : ℕ → R[X]} {m : ℕ} (hF : YunFamily A m)
    {j k : ℕ} (hjk : j ≠ k) : IsRelPrime (A j) (A k) := by
  intro d hdj hdk
  by_contra hu
  have hAj0 : A j ≠ 0 := (hF.squarefree j).ne_zero
  have hd0 : d ≠ 0 := fun h => hAj0 (by simpa [h] using hdj)
  obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hu hd0
  exact hF.coprime hjk hp (hpd.trans hdj) (hpd.trans hdk)

/-- **Yun's algorithm, squarefreeness** (abstract): every emitted factor is
squarefree, primitive and nonconstant. -/
theorem yunPoly_squarefree {a : R[X]} (hprim : a.IsPrimitive) (hnorm : _root_.normalize a = a) :
    ∀ gi ∈ yunPoly a, Squarefree gi.1 ∧ gi.1.IsPrimitive ∧ gi.1.natDegree ≠ 0 := by
  intro gi hgi
  by_cases h0 : a.natDegree = 0
  · rw [yunPoly, ite_eq_left h0] at hgi
    simp at hgi
  · obtain ⟨m, A, hF, -, hclosed⟩ := yunPoly_closed_form hprim hnorm h0
    rw [hclosed] at hgi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hgi
    obtain ⟨-, hdeg⟩ := List.mem_filter.mp hj
    exact ⟨hF.squarefree j, hF.primitive j, by simpa using hdeg⟩

/-- **Yun's algorithm, pairwise coprimality** (abstract): distinct multiplicity
classes share no factor (`IsRelPrime`) — in particular the output polynomials
are pairwise distinct (never `[(p, 2), (p, 3)]` for `p⁵`). -/
theorem yunPoly_pairwise_coprime {a : R[X]} (hprim : a.IsPrimitive)
    (hnorm : _root_.normalize a = a) :
    (yunPoly a).Pairwise (fun gi gj => IsRelPrime gi.1 gj.1) := by
  by_cases h0 : a.natDegree = 0
  · rw [yunPoly, ite_eq_left h0]
    exact List.Pairwise.nil
  · obtain ⟨m, A, hF, -, hclosed⟩ := yunPoly_closed_form hprim hnorm h0
    rw [hclosed, List.pairwise_map]
    refine List.Pairwise.filter _ ?_
    refine List.Pairwise.imp ?_ (List.pairwise_lt_range' ..)
    intro j k hjk
    exact hF.isRelPrime' (Nat.ne_of_lt hjk)

/-! ### Normalization-free squarefreeness / coprimality

`yunPoly_squarefree` / `yunPoly_pairwise_coprime` require the input to be
`normalize`-fixed. The multivariate recursion feeds `finSuccEquiv (primitivePart P)`,
which is only *primitive* — its leading coefficient carries an unpinned unit
(`primitivePart` mirrors Mathlib's `primPart`, which is not `normalize`-fixed).
The following variants drop `hnorm`: `a = C d' · normalize a` for a unit `d'`,
and `yunPoly (C d' · b)` is *positionally associate* to `yunPoly b` (the loop
emits identical normalized gcds; only the trailing cofactor carries the unit).
`Squarefree` and `IsRelPrime` are associate-invariant, so they transfer. -/

/-- `Forall₂` yields, for each left element, an associate right element. -/
theorem forall2_mem_left {α β : Type _} {r : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ r l1 l2) : ∀ x ∈ l1, ∃ y ∈ l2, r x y := by
  induction h with
  | nil => intro x hx; simp at hx
  | cons hxy hrest ih =>
    intro x hx; rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hxy⟩
    · obtain ⟨y, hy, hry⟩ := ih x hx; exact ⟨y, List.mem_cons_of_mem _ hy, hry⟩

/-- Transfer of `Pairwise` across a `Forall₂`, given the relations are compatible. -/
theorem forall2_pairwise {α β : Type _} {r : α → β → Prop} {s1 : α → α → Prop}
    {s2 : β → β → Prop} {l1 : List α} {l2 : List β} (hf : List.Forall₂ r l1 l2)
    (hrs : ∀ a b a' b', r a a' → r b b' → s2 a' b' → s1 a b) :
    l2.Pairwise s2 → l1.Pairwise s1 := by
  induction hf with
  | nil => intro _; exact List.Pairwise.nil
  | cons hxy hrest ih =>
    intro hp
    rw [List.pairwise_cons] at hp
    refine List.pairwise_cons.mpr ⟨fun b hb => ?_, ih hp.2⟩
    obtain ⟨b', hb', hrb⟩ := forall2_mem_left hrest b hb
    exact hrs _ _ _ _ hxy hrb (hp.1 b' hb')

omit [IsDomain R] [UniqueFactorizationMonoid R] [StrongNormalizedGCDMonoid R] [CharZero R] in
/-- Primitivity is associate-invariant. -/
theorem associated_isPrimitive {p q : R[X]} (h : Associated p q) (hp : p.IsPrimitive) :
    q.IsPrimitive := fun r hr => hp r (hr.trans h.symm.dvd)

/-- **Loop-level positional-associate invariance**: scaling the loop arguments by
`C` of a unit `c` produces a factor list positionally associate to the unscaled one. -/
theorem yunLoopPoly_C_mul_forall2 {c : R} (hc : IsUnit c) :
    ∀ (fuel i : ℕ) (w z : R[X]) (acc acc' : List (R[X] × ℕ)),
      List.Forall₂ (fun x y => Associated x.1 y.1) acc acc' →
      List.Forall₂ (fun x y => Associated x.1 y.1)
        (yunLoopPoly fuel i (Polynomial.C c * w) (Polynomial.C c * z) acc)
        (yunLoopPoly fuel i w z acc') := by
  have hCc0 : (Polynomial.C c : R[X]) ≠ 0 := by simpa [Polynomial.C_eq_zero] using hc.ne_zero
  have huC : IsUnit (Polynomial.C c : R[X]) := hc.map Polynomial.C
  have hCw : ∀ w : R[X], Associated (Polynomial.C c * w) w := by
    intro w
    have h1 : Associated (Polynomial.C c * w) (1 * w) :=
      (associated_one_iff_isUnit.mpr huC).mul_right w
    rwa [one_mul] at h1
  intro fuel
  induction fuel with
  | zero =>
    intro i w z acc acc' hacc
    rw [yunLoopPoly_zero, yunLoopPoly_zero]
    exact List.rel_append hacc (List.Forall₂.cons (hCw w) List.Forall₂.nil)
  | succ fuel ih =>
    intro i w z acc acc' hacc
    by_cases hz : z = 0
    · subst hz; rw [mul_zero, yunLoopPoly_succ_zero, yunLoopPoly_succ_zero]
      exact List.rel_append hacc (List.Forall₂.cons (hCw w) List.Forall₂.nil)
    · have hCz : Polynomial.C c * z ≠ 0 := mul_ne_zero hCc0 hz
      rw [yunLoopPoly_succ_ne_zero _ _ _ _ _ hCz, yunLoopPoly_succ_ne_zero _ _ _ _ _ hz]
      have hg : GCDMonoid.gcd (Polynomial.C c * w) (Polynomial.C c * z) = GCDMonoid.gcd w z :=
        gcd_C_mul hc w z
      have hg0 : GCDMonoid.gcd w z ≠ 0 := fun h => hz ((gcd_eq_zero_iff _ _).mp h).2
      rw [hg, edivExact_left_mul _ (gcd_dvd_left w z) hg0,
        edivExact_left_mul _ (gcd_dvd_right w z) hg0, Polynomial.derivative_C_mul,
        show Polynomial.C c * edivExact z (GCDMonoid.gcd w z)
            - Polynomial.C c * Polynomial.derivative (edivExact w (GCDMonoid.gcd w z))
          = Polynomial.C c * (edivExact z (GCDMonoid.gcd w z)
            - Polynomial.derivative (edivExact w (GCDMonoid.gcd w z))) from by ring]
      apply ih
      by_cases hgd : (GCDMonoid.gcd w z).natDegree = 0
      · rw [ite_eq_left hgd, ite_eq_left hgd]; exact hacc
      · rw [ite_eq_right hgd, ite_eq_right hgd]
        exact List.rel_append hacc (List.Forall₂.cons (Associated.refl _) List.Forall₂.nil)

/-- **`yunPoly`-level positional-associate invariance**: `yunPoly (C c · a)` is
positionally associate to `yunPoly a`. -/
theorem yunPoly_C_mul_forall2 {c : R} (hc : IsUnit c) (a : R[X]) :
    List.Forall₂ (fun x y => Associated x.1 y.1) (yunPoly (Polynomial.C c * a)) (yunPoly a) := by
  have huC : IsUnit (Polynomial.C c : R[X]) := hc.map Polynomial.C
  have hCw : ∀ w : R[X], Associated (Polynomial.C c * w) w := by
    intro w
    have h1 : Associated (Polynomial.C c * w) (1 * w) :=
      (associated_one_iff_isUnit.mpr huC).mul_right w
    rwa [one_mul] at h1
  have hnd : (Polynomial.C c * a).natDegree = a.natDegree := Polynomial.natDegree_C_mul hc.ne_zero
  by_cases h0 : a.natDegree = 0
  · rw [yunPoly, yunPoly, hnd, ite_eq_left h0, ite_eq_left h0]; exact List.Forall₂.nil
  · have ha0 : a ≠ 0 := fun h => h0 (by rw [h, Polynomial.natDegree_zero])
    set c0 := GCDMonoid.gcd a (Polynomial.derivative a) with hc0def
    have hc0ne : c0 ≠ 0 := fun h => ha0 ((gcd_eq_zero_iff _ _).mp h).1
    have hcda : c0 ∣ a := gcd_dvd_left _ _
    have hcdd : c0 ∣ Polynomial.derivative a := gcd_dvd_right _ _
    by_cases hcz : c0.natDegree = 0
    · rw [yunPoly, hnd, ite_eq_right h0, Polynomial.derivative_C_mul, gcd_C_mul hc a _,
        ← hc0def, ite_eq_left hcz, yunPoly, ite_eq_right h0, ← hc0def, ite_eq_left hcz]
      exact List.Forall₂.cons (hCw a) List.Forall₂.nil
    · have hya : yunPoly a = yunLoopPoly a.natDegree 1 (edivExact a c0)
          (edivExact (Polynomial.derivative a) c0 - Polynomial.derivative (edivExact a c0)) [] := by
        rw [yunPoly, ite_eq_right h0, ← hc0def, ite_eq_right hcz]
      rw [yunPoly, hnd, ite_eq_right h0, Polynomial.derivative_C_mul, gcd_C_mul hc a _,
        ← hc0def, ite_eq_right hcz,
        edivExact_left_mul (Polynomial.C c) hcda hc0ne,
        edivExact_left_mul (Polynomial.C c) hcdd hc0ne,
        Polynomial.derivative_C_mul,
        show Polynomial.C c * edivExact (Polynomial.derivative a) c0
            - Polynomial.C c * Polynomial.derivative (edivExact a c0)
          = Polynomial.C c * (edivExact (Polynomial.derivative a) c0
            - Polynomial.derivative (edivExact a c0)) from by ring, hya]
      exact yunLoopPoly_C_mul_forall2 hc a.natDegree 1 _ _ [] [] List.Forall₂.nil

/-- A primitive `a` is positionally associate (via `a = C d' · normalize a`) to a
primitive, `normalize`-fixed `b`; the workhorse for the normalize-free variants. -/
private theorem yunPoly_assoc_normalize {a : R[X]} (hprim : a.IsPrimitive) :
    ∃ b : R[X], b.IsPrimitive ∧ _root_.normalize b = b ∧
      List.Forall₂ (fun x y => Associated x.1 y.1) (yunPoly a) (yunPoly b) := by
  obtain ⟨u, hu⟩ := _root_.normalize_associated a
  set b := _root_.normalize a with hbdef
  obtain ⟨d', hd', hd'C⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have ha_eq : a = Polynomial.C d' * b := by rw [hd'C, mul_comm]; exact hu.symm
  refine ⟨b, associated_isPrimitive (_root_.normalize_associated a).symm hprim,
    by rw [hbdef, normalize_idem], by rw [ha_eq]; exact yunPoly_C_mul_forall2 hd' b⟩

/-- **Squarefreeness (normalize-free)**: for a merely *primitive* input, every
`yunPoly` factor is squarefree and primitive. -/
theorem yunPoly_squarefree' {a : R[X]} (hprim : a.IsPrimitive) :
    ∀ gi ∈ yunPoly a, Squarefree gi.1 ∧ gi.1.IsPrimitive := by
  obtain ⟨b, hbprim, hbnorm, hf⟩ := yunPoly_assoc_normalize hprim
  intro gi hgi
  obtain ⟨gj, hgj, hassoc⟩ := forall2_mem_left hf gi hgi
  obtain ⟨hsq, hpr, -⟩ := yunPoly_squarefree hbprim hbnorm gj hgj
  exact ⟨(hassoc.squarefree_iff).mpr hsq, associated_isPrimitive hassoc.symm hpr⟩

/-- **Pairwise coprimality (normalize-free)**: for a merely *primitive* input, the
`yunPoly` factors are pairwise `IsRelPrime`. -/
theorem yunPoly_pairwise_coprime' {a : R[X]} (hprim : a.IsPrimitive) :
    (yunPoly a).Pairwise (fun gi gj => IsRelPrime gi.1 gj.1) := by
  obtain ⟨b, hbprim, hbnorm, hf⟩ := yunPoly_assoc_normalize hprim
  refine forall2_pairwise hf (fun p q p' q' hpp hqq hs => ?_)
    (yunPoly_pairwise_coprime hbprim hbnorm)
  exact (hs.of_dvd_left hpp.dvd).of_dvd_right hqq.dvd

/-! ### The bridge to the computable algorithm -/

section Bridge

variable [DecidableEq R] [Azurite.ExactDiv R] [GcdImpl R] [PolynomialDerivative R]

/-- Quotient bridge over a domain: the synthetic exact quotient computes
`edivExact`, when the divisor divides (both are the unique cofactor). -/
theorem toPoly_exactDivQuoRem_edivExact (A B : AzPolynomial R)
    (hB : AzPolynomial.toPoly B ≠ 0) (hdvd : AzPolynomial.toPoly B ∣ AzPolynomial.toPoly A) :
    AzPolynomial.toPoly (exactDivQuoRem A B).1
      = edivExact (AzPolynomial.toPoly A) (AzPolynomial.toPoly B) := by
  obtain ⟨C, hC⟩ := hdvd
  have h1 : AzPolynomial.toPoly (exactDivQuoRem A B).1 = C := by
    refine toPoly_exactDivQuoRem_fst_of_euclidean A B C 0 hB ?_ ?_
    · rw [add_zero, hC]; ring
    · rw [Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (fun h => hB (Polynomial.degree_eq_bot.mp h))
  have h2 : edivExact (AzPolynomial.toPoly A) (AzPolynomial.toPoly B) = C :=
    edivExact_eq_of_mul hB hC
  rw [h1, h2]

/-- **Bridge for the Yun loop**: the represented run of the computable loop is the
abstract run, provided the computable gcd matches `GCDMonoid.gcd`. -/
theorem toPoly_yunLoop
    (hgcd_law : ∀ P Q : AzPolynomial R, AzPolynomial.toPoly (gcd P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
    (fuel i : ℕ) (w z : AzPolynomial R) (acc : List (AzPolynomial R × ℕ)) :
    (yunLoop fuel i w z acc).map (fun gi => (AzPolynomial.toPoly gi.1, gi.2))
      = yunLoopPoly fuel i (AzPolynomial.toPoly w) (AzPolynomial.toPoly z)
          (acc.map (fun gi => (AzPolynomial.toPoly gi.1, gi.2))) := by
  induction fuel generalizing i w z acc with
  | zero => simp [yunLoop, yunLoopPoly]
  | succ m ih =>
    rw [yunLoop, yunLoopPoly]
    by_cases hz : z = 0
    · have hz' : AzPolynomial.toPoly z = 0 := by rw [hz, toPoly_zero]
      rw [ite_eq_left hz, ite_eq_left hz']
      simp
    · have hzt : AzPolynomial.toPoly z ≠ 0 := toPoly_ne_zero hz
      rw [ite_eq_right hz, ite_eq_right hzt]
      have hgcd : AzPolynomial.toPoly (gcd w z)
          = GCDMonoid.gcd (AzPolynomial.toPoly w) (AzPolynomial.toPoly z) := hgcd_law w z
      have hg0 : AzPolynomial.toPoly (gcd w z) ≠ 0 := by
        rw [hgcd]; intro h; exact hzt ((gcd_eq_zero_iff _ _).mp h).2
      have hdw : AzPolynomial.toPoly (gcd w z) ∣ AzPolynomial.toPoly w := by
        rw [hgcd]; exact gcd_dvd_left _ _
      have hdz : AzPolynomial.toPoly (gcd w z) ∣ AzPolynomial.toPoly z := by
        rw [hgcd]; exact gcd_dvd_right _ _
      rw [ih]
      congr 1
      · rw [toPoly_exactDivQuoRem_edivExact w (gcd w z) hg0 hdw, hgcd]
      · rw [toPoly_sub, toPoly_derivative,
          toPoly_exactDivQuoRem_edivExact z (gcd w z) hg0 hdz,
          toPoly_exactDivQuoRem_edivExact w (gcd w z) hg0 hdw, hgcd]
      · rw [show (gcd w z).natDegree = (AzPolynomial.toPoly (gcd w z)).natDegree from
              (AzPolynomial.natDegree_toPoly _).symm, hgcd]
        by_cases hdeg : (GCDMonoid.gcd (AzPolynomial.toPoly w)
            (AzPolynomial.toPoly z)).natDegree = 0
        · rw [ite_eq_left hdeg, ite_eq_left hdeg]
        · rw [ite_eq_right hdeg, ite_eq_right hdeg]
          simp [hgcd]

/-- **Bridge for Yun's algorithm**: the represented output of the computable core
run is the abstract `yunPoly` of the represented polynomial. -/
theorem toPoly_squarefreeFactorizationCore
    (hgcd_law : ∀ P Q : AzPolynomial R, AzPolynomial.toPoly (gcd P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
    (a : AzPolynomial R) :
    (squarefreeFactorizationCore a).map (fun gi => (AzPolynomial.toPoly gi.1, gi.2))
      = yunPoly (AzPolynomial.toPoly a) := by
  rw [squarefreeFactorizationCore, yunPoly, AzPolynomial.natDegree_toPoly]
  by_cases h0 : a.natDegree = 0
  · rw [ite_eq_left h0, ite_eq_left h0]; rfl
  · rw [ite_eq_right h0, ite_eq_right h0]
    have hgcd : AzPolynomial.toPoly (gcd a (derivative a))
        = GCDMonoid.gcd (AzPolynomial.toPoly a)
            (Polynomial.derivative (AzPolynomial.toPoly a)) := by
      rw [hgcd_law, toPoly_derivative]
    have hc : (gcd a (derivative a)).natDegree
        = (GCDMonoid.gcd (AzPolynomial.toPoly a)
            (Polynomial.derivative (AzPolynomial.toPoly a))).natDegree := by
      rw [← hgcd, AzPolynomial.natDegree_toPoly]
    by_cases hcd : (gcd a (derivative a)).natDegree = 0
    · have hcd' : (GCDMonoid.gcd (AzPolynomial.toPoly a)
          (Polynomial.derivative (AzPolynomial.toPoly a))).natDegree = 0 := by
        rw [← hc]; exact hcd
      rw [ite_eq_left hcd, ite_eq_left hcd']; rfl
    · have hcd' : ¬ (GCDMonoid.gcd (AzPolynomial.toPoly a)
          (Polynomial.derivative (AzPolynomial.toPoly a))).natDegree = 0 := by
        rw [← hc]; exact hcd
      rw [ite_eq_right hcd, ite_eq_right hcd']
      have ha0 : AzPolynomial.toPoly a ≠ 0 := by
        intro h; apply h0
        rw [← AzPolynomial.natDegree_toPoly, h, Polynomial.natDegree_zero]
      have hg0 : AzPolynomial.toPoly (gcd a (derivative a)) ≠ 0 := by
        rw [hgcd]; intro h; exact ha0 ((gcd_eq_zero_iff _ _).mp h).1
      have hda : AzPolynomial.toPoly (gcd a (derivative a)) ∣ AzPolynomial.toPoly a := by
        rw [hgcd]; exact gcd_dvd_left _ _
      have hdd : AzPolynomial.toPoly (gcd a (derivative a))
          ∣ AzPolynomial.toPoly (derivative a) := by
        rw [hgcd, toPoly_derivative]; exact gcd_dvd_right _ _
      rw [toPoly_yunLoop hgcd_law]
      congr 1
      · rw [toPoly_exactDivQuoRem_edivExact _ _ hg0 hda, hgcd]
      · rw [toPoly_sub, toPoly_derivative,
          toPoly_exactDivQuoRem_edivExact _ _ hg0 hdd,
          toPoly_exactDivQuoRem_edivExact _ _ hg0 hda, hgcd, toPoly_derivative]

variable [LinearOrder R]

/-- The sorted output is a permutation of the core run. -/
theorem sf_perm (a : AzPolynomial R) :
    List.Perm (squarefreeFactorization a) (squarefreeFactorizationCore a) :=
  List.mergeSort_perm _ _

/-- **Product identity** (GCL Algorithm 8.2, correctness 1) over a
characteristic-zero UFD: for a primitive normalized input, the product of the
output polynomials raised to their exponents is the original polynomial. The gcd
lawfulness `hgcd_law` (the computable `GcdImpl.gcd` equals Mathlib's normalized
`GCDMonoid.gcd`) is supplied as a hypothesis. -/
theorem squarefreeFactorization_prod
    (hgcd_law : ∀ P Q : AzPolynomial R, AzPolynomial.toPoly (gcd P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
    (a : AzPolynomial R) (hprim : (AzPolynomial.toPoly a).IsPrimitive)
    (hnorm : _root_.normalize (AzPolynomial.toPoly a) = AzPolynomial.toPoly a) :
    ((squarefreeFactorization a).map
      (fun gi => AzPolynomial.toPoly gi.1 ^ gi.2)).prod = AzPolynomial.toPoly a := by
  rw [((sf_perm a).map (fun gi : AzPolynomial R × ℕ =>
    AzPolynomial.toPoly gi.1 ^ gi.2)).prod_eq]
  have h := congrArg (fun l => (l.map (fun gi : R[X] × ℕ => gi.1 ^ gi.2)).prod)
    (toPoly_squarefreeFactorizationCore hgcd_law a)
  simp only [List.map_map] at h
  rw [← yunPoly_prod hprim hnorm, ← h]
  rfl

/-- **Product identity up to associates** (GCL Algorithm 8.2) over a
characteristic-zero UFD: for a merely *primitive* input (dropping the
normalization hypothesis of `squarefreeFactorization_prod`), the product of the
output polynomials raised to their exponents is the input *up to a unit*. -/
theorem squarefreeFactorization_prod_associated
    (hgcd_law : ∀ P Q : AzPolynomial R, AzPolynomial.toPoly (gcd P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
    (a : AzPolynomial R) (hprim : (AzPolynomial.toPoly a).IsPrimitive) :
    Associated ((squarefreeFactorization a).map
      (fun gi => AzPolynomial.toPoly gi.1 ^ gi.2)).prod (AzPolynomial.toPoly a) := by
  rw [((sf_perm a).map (fun gi : AzPolynomial R × ℕ =>
    AzPolynomial.toPoly gi.1 ^ gi.2)).prod_eq]
  have hlist : (List.map (fun gi : AzPolynomial R × ℕ => AzPolynomial.toPoly gi.1 ^ gi.2)
      (squarefreeFactorizationCore a)).prod = Pm (yunPoly (AzPolynomial.toPoly a)) := by
    rw [show (fun gi : AzPolynomial R × ℕ => AzPolynomial.toPoly gi.1 ^ gi.2)
        = (fun p : R[X] × ℕ => p.1 ^ p.2) ∘ (fun gi : AzPolynomial R × ℕ =>
          (AzPolynomial.toPoly gi.1, gi.2)) from rfl,
      ← List.map_map, toPoly_squarefreeFactorizationCore hgcd_law a, Pm]
  rw [hlist]
  exact yunPoly_prod_associated hprim

/-- Membership-level view of the bridge, for the sorted output. -/
theorem sf_mem_yunPoly
    (hgcd_law : ∀ P Q : AzPolynomial R, AzPolynomial.toPoly (gcd P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
    {a : AzPolynomial R} {gi : AzPolynomial R × ℕ}
    (h : gi ∈ squarefreeFactorization a) :
    (AzPolynomial.toPoly gi.1, gi.2) ∈ yunPoly (AzPolynomial.toPoly a) := by
  rw [← toPoly_squarefreeFactorizationCore hgcd_law a]
  exact List.mem_map_of_mem ((sf_perm a).mem_iff.mp h)

/-- **Squarefreeness** (GCL Algorithm 8.2, correctness 2) over a characteristic-zero
UFD: every output polynomial is squarefree — moreover primitive and nonconstant. -/
theorem squarefreeFactorization_squarefree
    (hgcd_law : ∀ P Q : AzPolynomial R, AzPolynomial.toPoly (gcd P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
    (a : AzPolynomial R) (hprim : (AzPolynomial.toPoly a).IsPrimitive)
    (hnorm : _root_.normalize (AzPolynomial.toPoly a) = AzPolynomial.toPoly a) :
    ∀ gi ∈ squarefreeFactorization a,
      Squarefree (AzPolynomial.toPoly gi.1) ∧ (AzPolynomial.toPoly gi.1).IsPrimitive
        ∧ (AzPolynomial.toPoly gi.1).natDegree ≠ 0 :=
  fun _ hgi => yunPoly_squarefree hprim hnorm _ (sf_mem_yunPoly hgcd_law hgi)

/-- **Pairwise coprimality** (GCL Algorithm 8.2, correctness 3) over a
characteristic-zero UFD: distinct output entries carry relatively-prime
polynomials (`IsRelPrime`; over a non-Bézout UFD this replaces the field
version's `IsCoprime`) — in particular the polynomials are pairwise distinct,
so a power `p⁵` is always the single pair `(p, 5)`, never split. -/
theorem squarefreeFactorization_pairwise_coprime
    (hgcd_law : ∀ P Q : AzPolynomial R, AzPolynomial.toPoly (gcd P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
    (a : AzPolynomial R) (hprim : (AzPolynomial.toPoly a).IsPrimitive)
    (hnorm : _root_.normalize (AzPolynomial.toPoly a) = AzPolynomial.toPoly a) :
    (squarefreeFactorization a).Pairwise
      (fun gi gj => IsRelPrime (AzPolynomial.toPoly gi.1) (AzPolynomial.toPoly gj.1)) := by
  have habs := yunPoly_pairwise_coprime hprim hnorm
  rw [← toPoly_squarefreeFactorizationCore hgcd_law a, List.pairwise_map] at habs
  exact ((sf_perm a).pairwise_iff (fun h => h.symm)).mpr habs

/-- **Squarefreeness (normalize-free)**: same as `squarefreeFactorization_squarefree`
but for a merely *primitive* input (no `hnorm`) — the form the multivariate
recursion needs, since `finSuccEquiv (primitivePart P)` is primitive, not
`normalize`-fixed. -/
theorem squarefreeFactorization_squarefree'
    (hgcd_law : ∀ P Q : AzPolynomial R, AzPolynomial.toPoly (gcd P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
    (a : AzPolynomial R) (hprim : (AzPolynomial.toPoly a).IsPrimitive) :
    ∀ gi ∈ squarefreeFactorization a,
      Squarefree (AzPolynomial.toPoly gi.1) ∧ (AzPolynomial.toPoly gi.1).IsPrimitive :=
  fun _ hgi => yunPoly_squarefree' hprim _ (sf_mem_yunPoly hgcd_law hgi)

/-- **Pairwise coprimality (normalize-free)**: same as
`squarefreeFactorization_pairwise_coprime` but for a merely *primitive* input. -/
theorem squarefreeFactorization_pairwise_coprime'
    (hgcd_law : ∀ P Q : AzPolynomial R, AzPolynomial.toPoly (gcd P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
    (a : AzPolynomial R) (hprim : (AzPolynomial.toPoly a).IsPrimitive) :
    (squarefreeFactorization a).Pairwise
      (fun gi gj => IsRelPrime (AzPolynomial.toPoly gi.1) (AzPolynomial.toPoly gj.1)) := by
  have habs := yunPoly_pairwise_coprime' hprim
  rw [← toPoly_squarefreeFactorizationCore hgcd_law a, List.pairwise_map] at habs
  exact ((sf_perm a).pairwise_iff (fun h => h.symm)).mpr habs

end Bridge

end Azurite.AzPolynomial.UFD
