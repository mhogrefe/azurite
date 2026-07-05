import Azurite.AzPolynomial.SquarefreeFactorization
import Azurite.AzPolynomial.Equiv.Compare
import Azurite.AzPolynomial.Equiv.Derivative
import Azurite.AzPolynomial.Equiv.ExactDiv
import Azurite.AzPolynomial.Equiv.Gcd

/-!
# Correctness of Yun's square-free factorization: the bridge

The computable `squarefreeFactorization` (GCL Algorithm 8.2) is identified,
over a field, with the abstract mirror `yunPoly` on `Polynomial K`
(Mathlib's normalized gcd and Euclidean division):
`toPoly_squarefreeFactorization`.

The mathematical content (product identity, squarefreeness of the factors,
strictly increasing exponents — over characteristic zero) is proven for the
abstract `yunPoly` and transported to the computable algorithm through the
bridge.
-/

namespace Azurite.AzPolynomial

open Polynomial

attribute [local instance 0] Azurite.BPR.gcdMonoidPolynomial

variable {K : Type _} [Field K] [DecidableEq K]

/-- Abstract mirror of the Yun loop on `Polynomial K`: Mathlib's normalized
(monic) gcd and Euclidean division `/`. -/
noncomputable def yunLoopPoly : (fuel : ℕ) → (i : ℕ) → (w z : K[X]) →
    (acc : List (K[X] × ℕ)) → List (K[X] × ℕ)
  | 0, i, w, _, acc => acc ++ [(w, i)]
  | fuel + 1, i, w, z, acc =>
    if z = 0 then acc ++ [(w, i)]
    else
      let g := GCDMonoid.gcd w z
      yunLoopPoly fuel (i + 1) (w / g) (z / g - Polynomial.derivative (w / g))
        (if g.natDegree = 0 then acc else acc ++ [(g, i)])

/-- Abstract mirror of Yun's square-free factorization on `Polynomial K`. -/
noncomputable def yunPoly (a : K[X]) : List (K[X] × ℕ) :=
  if a.natDegree = 0 then []
  else
    let c := GCDMonoid.gcd a (Polynomial.derivative a)
    if c.natDegree = 0 then [(a, 1)]
    else yunLoopPoly a.natDegree 1 (a / c)
      (Polynomial.derivative a / c - Polynomial.derivative (a / c)) []

/-! ### The bridge -/

/-- Quotient bridge over a field: the synthetic exact division computes the
Euclidean quotient, unconditionally (nonzero divisor). -/
private theorem toPoly_exactQuo (A B : AzPolynomial K) (hB : AzPolynomial.toPoly B ≠ 0) :
    AzPolynomial.toPoly (exactDivQuoRem A B).1
      = AzPolynomial.toPoly A / AzPolynomial.toPoly B := by
  refine toPoly_exactDivQuoRem_fst_of_euclidean A B _
    (AzPolynomial.toPoly A % AzPolynomial.toPoly B) hB ?_ ?_
  · have h := EuclideanDomain.div_add_mod (AzPolynomial.toPoly A) (AzPolynomial.toPoly B)
    linear_combination -h
  · exact EuclideanDomain.mod_lt _ hB

/-- **Bridge for the Yun loop**: the represented run of the computable loop
is the abstract run. -/
theorem toPoly_yunLoop [PolynomialDerivative K] (fuel i : ℕ)
    (w z : AzPolynomial K) (acc : List (AzPolynomial K × ℕ)) :
    (yunLoop fuel i w z acc).map (fun gi => (AzPolynomial.toPoly gi.1, gi.2))
      = yunLoopPoly fuel i (AzPolynomial.toPoly w) (AzPolynomial.toPoly z)
          (acc.map (fun gi => (AzPolynomial.toPoly gi.1, gi.2))) := by
  induction fuel generalizing i w z acc with
  | zero => simp [yunLoop, yunLoopPoly]
  | succ m ih =>
    rw [yunLoop, yunLoopPoly]
    by_cases hz : z = 0
    · rw [if_pos hz, if_pos (by rw [hz, toPoly_zero])]
      simp
    · rw [if_neg hz, if_neg (fun h => hz (toPoly_inj.mp (h.trans toPoly_zero.symm)))]
      have hgcd : AzPolynomial.toPoly (gcd w z)
          = GCDMonoid.gcd (AzPolynomial.toPoly w) (AzPolynomial.toPoly z) :=
        toPoly_gcd_field w z
      have hg0 : AzPolynomial.toPoly (gcd w z) ≠ 0 := by
        rw [hgcd]
        intro h
        exact toPoly_ne_zero hz ((gcd_eq_zero_iff _ _).mp h).2
      rw [ih]
      congr 1
      · rw [toPoly_exactQuo w (gcd w z) hg0, hgcd]
      · rw [toPoly_sub, toPoly_derivative, toPoly_exactQuo z (gcd w z) hg0,
          toPoly_exactQuo w (gcd w z) hg0, hgcd]
      · rw [show (gcd w z).natDegree = (AzPolynomial.toPoly (gcd w z)).natDegree from
            (AzPolynomial.natDegree_toPoly _).symm, hgcd]
        by_cases hdeg : (GCDMonoid.gcd (AzPolynomial.toPoly w)
            (AzPolynomial.toPoly z)).natDegree = 0
        · rw [if_pos hdeg, if_pos hdeg]
        · rw [if_neg hdeg, if_neg hdeg]
          simp [hgcd]

/-- **Bridge for Yun's algorithm**: the represented output of the computable
core run (multiplicity order) is the abstract `yunPoly` of the represented
polynomial. -/
theorem toPoly_squarefreeFactorizationCore [PolynomialDerivative K] (a : AzPolynomial K) :
    (squarefreeFactorizationCore a).map (fun gi => (AzPolynomial.toPoly gi.1, gi.2))
      = yunPoly (AzPolynomial.toPoly a) := by
  rw [squarefreeFactorizationCore, yunPoly, AzPolynomial.natDegree_toPoly]
  by_cases h0 : a.natDegree = 0
  · rw [if_pos h0, if_pos h0]
    rfl
  · rw [if_neg h0, if_neg h0]
    have hgcd : AzPolynomial.toPoly (gcd a (derivative a))
        = GCDMonoid.gcd (AzPolynomial.toPoly a)
            (Polynomial.derivative (AzPolynomial.toPoly a)) := by
      rw [toPoly_gcd_field, toPoly_derivative]
    have hc : (gcd a (derivative a)).natDegree
        = (GCDMonoid.gcd (AzPolynomial.toPoly a)
            (Polynomial.derivative (AzPolynomial.toPoly a))).natDegree := by
      rw [← hgcd, AzPolynomial.natDegree_toPoly]
    by_cases hcd : (gcd a (derivative a)).natDegree = 0
    · rw [if_pos hcd, if_pos (by rw [← hc]; exact hcd)]
      rfl
    · rw [if_neg hcd, if_neg (by rw [← hc]; exact hcd)]
      have ha0 : AzPolynomial.toPoly a ≠ 0 := by
        intro h
        apply h0
        rw [← AzPolynomial.natDegree_toPoly, h, Polynomial.natDegree_zero]
      have hg0 : AzPolynomial.toPoly (gcd a (derivative a)) ≠ 0 := by
        rw [hgcd]
        intro h
        exact ha0 ((gcd_eq_zero_iff _ _).mp h).1
      rw [toPoly_yunLoop]
      congr 1
      · rw [toPoly_exactQuo _ _ hg0, hgcd]
      · rw [toPoly_sub, toPoly_derivative, toPoly_exactQuo _ _ hg0, toPoly_exactQuo _ _ hg0,
          hgcd, toPoly_derivative]

/-! ### Correctness of `yunPoly` over a field of characteristic zero

The input `a` is decomposed into its squarefree multiplicity classes
`a = ∏_{j ∈ [1, m]} (A j)^j` (`A j` monic, squarefree, pairwise coprime, `A m ≠ 1`),
and the loop invariant is: at counter `i` the state is
`w = ∏_{j ∈ [i, m]} A j` and `z = ∑_{j ∈ [i, m]} (j - i)·(A j)'·∏_{k ∈ [i, m], k ≠ j} A k`.
-/

/-! #### Interval helpers -/

private theorem Icc_eq_insert_Icc {i m : ℕ} (h : i ≤ m) :
    Finset.Icc i m = insert i (Finset.Icc (i + 1) m) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

private theorem notMem_Icc_succ (i m : ℕ) : i ∉ Finset.Icc (i + 1) m := by
  simp only [Finset.mem_Icc]
  omega

private theorem Icc_erase_left' (i m : ℕ) :
    (Finset.Icc i m).erase i = Finset.Icc (i + 1) m := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_Icc]
  omega

private theorem Ico_one_succ_eq_Icc (m : ℕ) : Finset.Ico 1 (1 + m) = Finset.Icc 1 m := by
  ext j
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

/-! #### The Yun sum -/

/-- The "Yun sum" `∑_{j ∈ s} (c j)·(A j)'·∏_{k ∈ s, k ≠ j} A k`: the shape of the
`z` iterate of the Yun loop over the squarefree class family `A`. -/
private noncomputable def ysum (A : ℕ → K[X]) (s : Finset ℕ) (c : ℕ → ℕ) : K[X] :=
  ∑ j ∈ s, (c j : K[X]) * Polynomial.derivative (A j) * ∏ k ∈ s.erase j, A k

omit [DecidableEq K] in
private theorem ysum_def (A : ℕ → K[X]) (s : Finset ℕ) (c : ℕ → ℕ) :
    ysum A s c
      = ∑ j ∈ s, (c j : K[X]) * Polynomial.derivative (A j) * ∏ k ∈ s.erase j, A k :=
  rfl

omit [DecidableEq K] in
/-- Pulling the vanishing-coefficient element out of a Yun sum. -/
private theorem ysum_erase {A : ℕ → K[X]} {s : Finset ℕ} {c : ℕ → ℕ} {i : ℕ}
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

omit [DecidableEq K] in
/-- Subtracting the derivative of the product decrements every coefficient of
a Yun sum. -/
private theorem ysum_sub_derivative {A : ℕ → K[X]} {s : Finset ℕ} {c c' : ℕ → ℕ}
    (hc : ∀ j ∈ s, 1 ≤ c j) (hc' : ∀ j ∈ s, c' j = c j - 1) :
    ysum A s c - Polynomial.derivative (∏ j ∈ s, A j) = ysum A s c' := by
  rw [ysum_def, ysum_def, Polynomial.derivative_prod_finset, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hcast : (c' j : K[X]) = (c j : K[X]) - 1 := by
    rw [hc' j hj, Nat.cast_sub (hc j hj), Nat.cast_one]
  rw [hcast]
  ring

/-! #### The squarefree class family -/

/-- The hypotheses feeding the Yun loop invariant: `A j` are the monic,
squarefree, pairwise coprime multiplicity classes of the input, with the
top class `A m` nontrivial. -/
private structure YunFamily (A : ℕ → K[X]) (m : ℕ) : Prop where
  monic : ∀ j, (A j).Monic
  squarefree : ∀ j, Squarefree (A j)
  coprime : ∀ ⦃j k : ℕ⦄, j ≠ k → ∀ ⦃p : K[X]⦄, Irreducible p → p ∣ A j → p ∣ A k → False
  one_le : 1 ≤ m
  top_ne_one : A m ≠ 1

omit [DecidableEq K] in
private theorem YunFamily.top_natDegree_ne_zero {A : ℕ → K[X]} {m : ℕ}
    (hF : YunFamily A m) : (A m).natDegree ≠ 0 := fun h =>
  hF.top_ne_one (Polynomial.eq_one_of_monic_natDegree_zero (hF.monic m) h)

omit [DecidableEq K] in
/-- **Workhorse**: an irreducible factor of a class member does not divide a Yun
sum whose coefficient at that member is nonzero (characteristic zero:
the coefficient survives; separability: the derivative factor survives;
coprimality: the other classes survive). -/
private theorem YunFamily.not_dvd_ysum [CharZero K] {A : ℕ → K[X]} {m : ℕ}
    (hF : YunFamily A m) {s : Finset ℕ} {c : ℕ → ℕ} {p : K[X]} (hp : Irreducible p)
    {j₀ : ℕ} (hj₀ : j₀ ∈ s) (hpj₀ : p ∣ A j₀) (hc : c j₀ ≠ 0) :
    ¬ p ∣ ysum A s c := by
  intro hdvd
  have hprime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
  -- `p` divides every summand other than the one at `j₀`
  have hrest : p ∣ ∑ j ∈ s.erase j₀,
      (c j : K[X]) * Polynomial.derivative (A j) * ∏ k ∈ s.erase j, A k := by
    refine Finset.dvd_sum fun j hj => ?_
    obtain ⟨hjne, hjs⟩ := Finset.mem_erase.mp hj
    have hj₀' : j₀ ∈ s.erase j := Finset.mem_erase.mpr ⟨fun h => hjne h.symm, hj₀⟩
    exact Dvd.dvd.mul_left (hpj₀.trans (Finset.dvd_prod_of_mem _ hj₀')) _
  -- hence `p` divides the summand at `j₀`
  have hterm : p ∣ (c j₀ : K[X]) * Polynomial.derivative (A j₀) * ∏ k ∈ s.erase j₀, A k := by
    have hsplit : (c j₀ : K[X]) * Polynomial.derivative (A j₀) * ∏ k ∈ s.erase j₀, A k
        = ysum A s c - ∑ j ∈ s.erase j₀,
            (c j : K[X]) * Polynomial.derivative (A j) * ∏ k ∈ s.erase j, A k := by
      rw [ysum_def, ← Finset.add_sum_erase _ _ hj₀]
      ring
    rw [hsplit]
    exact dvd_sub hdvd hrest
  rcases hprime.dvd_mul.mp hterm with hd | hd
  · rcases hprime.dvd_mul.mp hd with hd' | hd'
    · -- `p` cannot divide the nonzero constant coefficient
      have hu : IsUnit ((c j₀ : K[X])) := by
        rw [← Polynomial.C_eq_natCast]
        exact Polynomial.isUnit_C.mpr
          (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hc))
      exact hp.not_isUnit (isUnit_of_dvd_unit hd' hu)
    · -- `p` cannot divide the derivative: `A j₀` is separable (squarefree, char 0)
      have hsep : (A j₀).Separable :=
        PerfectField.separable_iff_squarefree.mpr (hF.squarefree j₀)
      exact hp.not_isUnit (hsep.isUnit_of_dvd' hpj₀ hd')
  · -- `p` cannot divide the other classes
    obtain ⟨k, hk, hpk⟩ := hprime.exists_mem_finset_dvd hd
    exact hF.coprime (Finset.mem_erase.mp hk).1 hp hpk hpj₀

/-- The gcd of the classes' product with a Yun sum with all-nonzero coefficients
is `1`. -/
private theorem YunFamily.gcd_prod_ysum [CharZero K] {A : ℕ → K[X]} {m : ℕ}
    (hF : YunFamily A m) {s : Finset ℕ} {c : ℕ → ℕ} (hc : ∀ j ∈ s, c j ≠ 0) :
    GCDMonoid.gcd (∏ j ∈ s, A j) (ysum A s c) = 1 := by
  have hW : (∏ j ∈ s, A j).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => hF.monic j
  have hne : GCDMonoid.gcd (∏ j ∈ s, A j) (ysum A s c) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hW.ne_zero (gcd_dvd_left _ _)
  have hu : IsUnit (GCDMonoid.gcd (∏ j ∈ s, A j) (ysum A s c)) := by
    by_contra hu
    obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hu hne
    obtain ⟨j₀, hj₀, hpj₀⟩ :=
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hp).exists_mem_finset_dvd
        (hpd.trans (gcd_dvd_left _ _))
    exact hF.not_dvd_ysum hp hj₀ hpj₀ (hc j₀ hj₀) (hpd.trans (gcd_dvd_right _ _))
  rw [← _root_.normalize_gcd]
  exact normalize_eq_one.mpr hu

omit [DecidableEq K] in
/-- A Yun sum is nonzero as soon as one nontrivial class has a nonzero
coefficient. -/
private theorem YunFamily.ysum_ne_zero [CharZero K] {A : ℕ → K[X]} {m : ℕ}
    (hF : YunFamily A m) {s : Finset ℕ} {c : ℕ → ℕ} {j₀ : ℕ} (hj₀ : j₀ ∈ s)
    (hA : A j₀ ≠ 1) (hc : c j₀ ≠ 0) : ysum A s c ≠ 0 := by
  intro h0
  have hnu : ¬IsUnit (A j₀) := fun hu =>
    hA (Polynomial.eq_one_of_monic_natDegree_zero (hF.monic j₀)
      (Polynomial.natDegree_eq_zero_of_isUnit hu))
  obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hnu (hF.monic j₀).ne_zero
  exact hF.not_dvd_ysum hp hj₀ hpd hc (h0 ▸ dvd_zero p)

/-! #### The loop invariant -/

private theorem yunLoopPoly_zero (i : ℕ) (w z : K[X]) (acc : List (K[X] × ℕ)) :
    yunLoopPoly 0 i w z acc = acc ++ [(w, i)] := rfl

private theorem yunLoopPoly_succ_zero (fuel i : ℕ) (w : K[X]) (acc : List (K[X] × ℕ)) :
    yunLoopPoly (fuel + 1) i w 0 acc = acc ++ [(w, i)] := by
  rw [yunLoopPoly, if_pos rfl]

private theorem yunLoopPoly_succ_ne_zero (fuel i : ℕ) (w z : K[X])
    (acc : List (K[X] × ℕ)) (hz : z ≠ 0) :
    yunLoopPoly (fuel + 1) i w z acc =
      yunLoopPoly fuel (i + 1) (w / GCDMonoid.gcd w z)
        (z / GCDMonoid.gcd w z - Polynomial.derivative (w / GCDMonoid.gcd w z))
        (if (GCDMonoid.gcd w z).natDegree = 0 then acc
          else acc ++ [(GCDMonoid.gcd w z, i)]) := by
  rw [yunLoopPoly, if_neg hz]

omit [DecidableEq K] in
/-- The terminal emission `(A m, m)` in closed list form. -/
private theorem YunFamily.out_top {A : ℕ → K[X]} {m : ℕ} (hF : YunFamily A m)
    (acc : List (K[X] × ℕ)) :
    acc ++ [(A m, m)]
      = acc ++ (((List.range' m (m + 1 - m)).filter fun j => (A j).natDegree ≠ 0).map
          fun j => (A j, j)) := by
  have h1 : m + 1 - m = 1 := by omega
  rw [h1]
  simp [List.range', hF.top_natDegree_ne_zero]

/-- **The Yun loop invariant**: started at counter `i ≤ m` on
`w = ∏_{j ∈ [i, m]} A j` and the corresponding Yun sum (with enough fuel), the
loop emits exactly the nontrivial classes `(A j, j)`, `j ∈ [i, m]`, in order. -/
private theorem YunFamily.yunLoopPoly_eq [CharZero K] {A : ℕ → K[X]} {m : ℕ}
    (hF : YunFamily A m) :
    ∀ (fuel i : ℕ) (acc : List (K[X] × ℕ)), i ≤ m → m - i ≤ fuel →
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
      have hAine : A i ≠ 0 := (hF.monic i).ne_zero
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
          mul_one, (hF.monic i).normalize_eq_self]
      rw [yunLoopPoly_succ_ne_zero _ _ _ _ _ hzne, hgcd]
      have hwq : (∏ j ∈ Finset.Icc i m, A j) / A i = ∏ j ∈ Finset.Icc (i + 1) m, A j :=
        (EuclideanDomain.eq_div_of_mul_eq_right hAine hw.symm).symm
      have hzq : (ysum A (Finset.Icc i m) fun j => j - i) / A i
          = ysum A (Finset.Icc (i + 1) m) fun j => j - i :=
        (EuclideanDomain.eq_div_of_mul_eq_right hAine hz.symm).symm
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
      · rw [if_pos hAi, List.filter_cons_of_neg (by simp [hAi])]
      · rw [if_neg hAi, List.filter_cons_of_pos (by simp [hAi]), List.map_cons]
        simp

/-! #### Existence of the squarefree class decomposition -/

/-- **Squarefree multiplicity decomposition** of a nonconstant monic polynomial:
grouping the (monic) normalized irreducible factors by multiplicity yields
`a = ∏_{j ∈ [1, m]} (A j)^j` with `A j` monic, squarefree, pairwise coprime and
`A m ≠ 1` (also `m ≤ deg a`, which feeds the loop's fuel bound). -/
private theorem exists_yunFamily {a : K[X]} (ha : a.Monic) (h0 : a.natDegree ≠ 0) :
    ∃ (m : ℕ) (A : ℕ → K[X]), YunFamily A m ∧
      a = ∏ j ∈ Finset.Icc 1 m, A j ^ j ∧ m ≤ a.natDegree := by
  classical
  have ha0 : a ≠ 0 := ha.ne_zero
  set f := UniqueFactorizationMonoid.normalizedFactors a with hfdef
  have hirr : ∀ p ∈ f, Irreducible p := fun p hp =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hnorm : ∀ p ∈ f, _root_.normalize p = p := fun p hp =>
    UniqueFactorizationMonoid.normalize_normalized_factor p hp
  have hmon : ∀ p ∈ f, p.Monic := by
    intro p hp
    have h := Polynomial.monic_normalize (hirr p hp).ne_zero
    rwa [hnorm p hp] at h
  have hprod : f.prod = a := by
    rw [hfdef, UniqueFactorizationMonoid.prod_normalizedFactors_eq ha0, ha.normalize_eq_self]
  have hfne : f ≠ 0 := by
    intro h
    rw [h, Multiset.prod_zero] at hprod
    exact h0 (by rw [← hprod, Polynomial.natDegree_one])
  obtain ⟨p₀, hp₀⟩ := Multiset.exists_mem_of_ne_zero hfne
  set m := f.toFinset.sup (fun p => f.count p) with hmdef
  have hmemF : ∀ {n : ℕ} {p : K[X]},
      p ∈ f.toFinset.filter (fun q => f.count q = n) → p ∈ f :=
    fun h => Multiset.mem_toFinset.mp (Finset.mem_filter.mp h).1
  have hmono : ∀ n, (∏ p ∈ f.toFinset.filter fun q => f.count q = n, p).Monic := fun n =>
    Polynomial.monic_prod_of_monic _ _ fun p hp => hmon p (hmemF hp)
  have hm1 : 1 ≤ m :=
    le_trans (Multiset.count_pos.mpr hp₀)
      (Finset.le_sup (f := fun p => f.count p) (Multiset.mem_toFinset.mpr hp₀))
  -- squarefreeness: the normalized factors of each class product are the class itself
  have hnf : ∀ n, UniqueFactorizationMonoid.normalizedFactors
        (∏ p ∈ f.toFinset.filter fun q => f.count q = n, p)
      = (f.toFinset.filter fun q => f.count q = n).val := by
    intro n
    have hval : (∏ p ∈ f.toFinset.filter (fun q => f.count q = n), p)
        = (f.toFinset.filter fun q => f.count q = n).val.prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hval, UniqueFactorizationMonoid.normalizedFactors_prod_eq _
      (fun q hq => hirr q (hmemF (Finset.mem_val.mp hq)))]
    rw [Multiset.map_congr rfl fun q hq => hnorm q (hmemF (Finset.mem_val.mp hq)),
      Multiset.map_id']
  have hsq : ∀ n, Squarefree (∏ p ∈ f.toFinset.filter fun q => f.count q = n, p) := by
    intro n
    rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors (hmono n).ne_zero,
      hnf n]
    exact (f.toFinset.filter fun q => f.count q = n).nodup
  -- pairwise coprimality: distinct classes share no irreducible factor
  have hcop : ∀ ⦃j k : ℕ⦄, j ≠ k → ∀ ⦃p : K[X]⦄, Irreducible p →
      p ∣ (∏ q ∈ f.toFinset.filter fun q => f.count q = j, q) →
      p ∣ (∏ q ∈ f.toFinset.filter fun q => f.count q = k, q) → False := by
    intro j k hjk p hp hpj hpk
    have hprime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
    obtain ⟨q, hq, hpq⟩ := hprime.exists_mem_finset_dvd hpj
    obtain ⟨q', hq', hpq'⟩ := hprime.exists_mem_finset_dvd hpk
    have h1 : Associated p q := hp.associated_of_dvd (hirr q (hmemF hq)) hpq
    have h2 : Associated p q' := hp.associated_of_dvd (hirr q' (hmemF hq')) hpq'
    have h3 : q = q' := by
      rw [← hnorm q (hmemF hq), ← hnorm q' (hmemF hq')]
      exact normalize_eq_normalize_iff_associated.mpr (h1.symm.trans h2)
    exact hjk (by
      rw [← (Finset.mem_filter.mp hq).2, ← (Finset.mem_filter.mp hq').2, h3])
  -- the top class is nontrivial: the sup is attained
  obtain ⟨pM, hpMF, hpMc⟩ :=
    Finset.exists_mem_eq_sup f.toFinset ⟨p₀, Multiset.mem_toFinset.mpr hp₀⟩
      fun p => f.count p
  have hpMmem : pM ∈ f.toFinset.filter fun q => f.count q = m :=
    Finset.mem_filter.mpr ⟨hpMF, hpMc.symm⟩
  have htop : (∏ p ∈ f.toFinset.filter fun q => f.count q = m, p) ≠ 1 := by
    intro h1
    exact (hirr pM (Multiset.mem_toFinset.mp hpMF)).not_isUnit
      (isUnit_of_dvd_one (h1 ▸ Finset.dvd_prod_of_mem _ hpMmem))
  -- the product identity: group the factors by multiplicity
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
  -- the fuel bound
  have hdegAm : 0 < (∏ p ∈ f.toFinset.filter fun q => f.count q = m, p).natDegree := by
    rcases Nat.eq_zero_or_pos
        (∏ p ∈ f.toFinset.filter fun q => f.count q = m, p).natDegree with h | h
    · exact absurd (Polynomial.eq_one_of_monic_natDegree_zero (hmono m) h) htop
    · exact h
  have hmle : m ≤ a.natDegree := by
    have hdvd : (∏ p ∈ f.toFinset.filter fun q => f.count q = m, p) ^ m ∣ a := by
      rw [hprodid]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hm1, le_refl m⟩)
    have hb := Polynomial.natDegree_le_of_dvd hdvd ha0
    rw [Polynomial.natDegree_pow] at hb
    exact le_trans (Nat.le_mul_of_pos_right m hdegAm) hb
  exact ⟨m, fun n => ∏ p ∈ f.toFinset.filter fun q => f.count q = n, p,
    ⟨hmono, hsq, hcop, hm1, htop⟩, hprodid, hmle⟩

/-! #### The closed form of `yunPoly` -/

/-- **Closed form**: for nonconstant monic `a` over a characteristic-zero field,
`yunPoly a` is exactly the list of nontrivial multiplicity classes
`(A j, j)`, `j ∈ [1, m]`, in increasing order of `j`. -/
private theorem yunPoly_closed_form [CharZero K] {a : K[X]} (ha : a.Monic)
    (h0 : a.natDegree ≠ 0) :
    ∃ (m : ℕ) (A : ℕ → K[X]), YunFamily A m ∧
      a = ∏ j ∈ Finset.Icc 1 m, A j ^ j ∧
      yunPoly a = ((List.range' 1 m).filter fun j => (A j).natDegree ≠ 0).map
        fun j => (A j, j) := by
  obtain ⟨m, A, hF, hprodid, hmdeg⟩ := exists_yunFamily ha h0
  refine ⟨m, A, hF, hprodid, ?_⟩
  set CC := ∏ j ∈ Finset.Icc 1 m, A j ^ (j - 1) with hCCdef
  have hCCmonic : CC.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => (hF.monic j).pow _
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
      mul_one, hCCmonic.normalize_eq_self]
  have hyun : yunPoly a
      = if (GCDMonoid.gcd a (Polynomial.derivative a)).natDegree = 0 then [(a, 1)]
        else yunLoopPoly a.natDegree 1 (a / GCDMonoid.gcd a (Polynomial.derivative a))
          (Polynomial.derivative a / GCDMonoid.gcd a (Polynomial.derivative a)
            - Polynomial.derivative (a / GCDMonoid.gcd a (Polynomial.derivative a))) [] := by
    rw [yunPoly, if_neg h0]
  by_cases hCC0 : CC.natDegree = 0
  · -- `m = 1`: the input is already squarefree
    have hCC1 : CC = 1 := Polynomial.eq_one_of_monic_natDegree_zero hCCmonic hCC0
    have hm1 : m = 1 := by
      by_contra hm
      have hdvd : A m ∣ CC := by
        refine dvd_trans (dvd_pow_self (A m) ?_)
          (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hF.one_le, le_refl m⟩))
        have := hF.one_le
        omega
      have hu : IsUnit (A m) := isUnit_of_dvd_one (hCC1 ▸ hdvd)
      exact hF.top_ne_one (Polynomial.eq_one_of_monic_natDegree_zero (hF.monic m)
        (Polynomial.natDegree_eq_zero_of_isUnit hu))
    subst hm1
    have ha1 : A 1 = a := by
      rw [hprodid, Finset.Icc_self, Finset.prod_singleton, pow_one]
    have hd1 : (A 1).natDegree ≠ 0 := by
      rw [ha1]
      exact h0
    rw [hyun, hc, if_pos hCC0, show List.range' 1 1 = [1] from rfl,
      List.filter_cons_of_pos (by simp [hd1]), List.filter_nil, List.map_cons, List.map_nil,
      ha1]
  · -- the loop runs: feed the invariant
    have hCCne : CC ≠ 0 := hCCmonic.ne_zero
    have haq : a / CC = ∏ j ∈ Finset.Icc 1 m, A j :=
      (EuclideanDomain.eq_div_of_mul_eq_right hCCne hsplit.symm).symm
    have hdq : Polynomial.derivative a / CC = ysum A (Finset.Icc 1 m) fun j => j :=
      (EuclideanDomain.eq_div_of_mul_eq_right hCCne hderiv.symm).symm
    rw [hyun, hc, if_neg hCC0, haq, hdq,
      ysum_sub_derivative (c' := fun j => j - 1)
        (fun j hj => (Finset.mem_Icc.mp hj).1) (fun j hj => rfl),
      hF.yunLoopPoly_eq a.natDegree 1 [] hF.one_le (by omega),
      Nat.add_sub_cancel, List.nil_append]

/-! #### Products over the emitted list -/

omit [DecidableEq K] in
private theorem filter_map_pow_prod {A : ℕ → K[X]} (hmono : ∀ j, (A j).Monic) :
    ∀ (n i : ℕ),
      (((List.range' i n).filter fun j => (A j).natDegree ≠ 0).map fun j => A j ^ j).prod
        = ∏ j ∈ Finset.Ico i (i + n), A j ^ j := by
  intro n
  induction n with
  | zero =>
    intro i
    simp
  | succ n ihn =>
    intro i
    rw [List.range'_succ,
      Finset.prod_eq_prod_Ico_succ_bot (by omega) (fun j => A j ^ j),
      show i + (n + 1) = (i + 1) + n by omega]
    by_cases hAi : (A i).natDegree = 0
    · rw [List.filter_cons_of_neg (by simp [hAi]), ihn (i + 1),
        Polynomial.eq_one_of_monic_natDegree_zero (hmono i) hAi, one_pow, one_mul]
    · rw [List.filter_cons_of_pos (by simp [hAi]), List.map_cons, List.prod_cons, ihn (i + 1)]

/-! #### The three correctness theorems -/

/-- **Yun's algorithm, product identity**: the emitted powers multiply back to
the (monic) input. -/
theorem yunPoly_prod [CharZero K] {a : K[X]} (ha : a.Monic) :
    ((yunPoly a).map fun gi => gi.1 ^ gi.2).prod = a := by
  by_cases h0 : a.natDegree = 0
  · rw [yunPoly, if_pos h0, Polynomial.eq_one_of_monic_natDegree_zero ha h0]
    simp
  · obtain ⟨m, A, hF, hprodid, hclosed⟩ := yunPoly_closed_form ha h0
    rw [hclosed, List.map_map,
      show ((fun gi : K[X] × ℕ => gi.1 ^ gi.2) ∘ fun j => (A j, j)) = fun j => A j ^ j
        from rfl,
      filter_map_pow_prod hF.monic m 1, Ico_one_succ_eq_Icc, ← hprodid]

/-- **Yun's algorithm, squarefreeness**: every emitted factor is squarefree,
monic and nonconstant. -/
theorem yunPoly_squarefree [CharZero K] {a : K[X]} (ha : a.Monic) :
    ∀ gi ∈ yunPoly a, Squarefree gi.1 ∧ gi.1.Monic ∧ gi.1.natDegree ≠ 0 := by
  intro gi hgi
  by_cases h0 : a.natDegree = 0
  · rw [yunPoly, if_pos h0] at hgi
    simp at hgi
  · obtain ⟨m, A, hF, -, hclosed⟩ := yunPoly_closed_form ha h0
    rw [hclosed] at hgi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hgi
    obtain ⟨-, hdeg⟩ := List.mem_filter.mp hj
    exact ⟨hF.squarefree j, hF.monic j, by simpa using hdeg⟩

/-- **Yun's algorithm, exponents (pairwise form)**: the emitted multiplicities
are strictly increasing. -/
theorem yunPoly_exponents_pairwise [CharZero K] {a : K[X]} (ha : a.Monic) :
    ((yunPoly a).map Prod.snd).Pairwise (· < ·) := by
  by_cases h0 : a.natDegree = 0
  · rw [yunPoly, if_pos h0]
    simp
  · obtain ⟨m, A, hF, -, hclosed⟩ := yunPoly_closed_form ha h0
    rw [hclosed, List.map_map,
      show (Prod.snd ∘ fun j => (A j, j)) = @id ℕ from rfl, List.map_id]
    exact List.Pairwise.filter _ List.pairwise_lt_range'

/-- **Yun's algorithm, exponents**: the emitted multiplicities form a strictly
increasing chain. -/
theorem yunPoly_exponents [CharZero K] {a : K[X]} (ha : a.Monic) :
    ((yunPoly a).map Prod.snd).IsChain (· < ·) := by
  rw [List.isChain_iff_pairwise]
  exact yunPoly_exponents_pairwise ha

/-! ### The computable algorithm's correctness (through the bridge) -/

/-- Coprimality of distinct Yun classes, as `IsCoprime` over the field. -/
private theorem YunFamily.isCoprime' {A : ℕ → K[X]} {m : ℕ} (hF : YunFamily A m)
    {j k : ℕ} (hjk : j ≠ k) : IsCoprime (A j) (A k) := by
  rw [← EuclideanDomain.gcd_isUnit_iff]
  by_contra hu
  have hg0 : EuclideanDomain.gcd (A j) (A k) ≠ 0 := fun h =>
    (hF.monic j).ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  obtain ⟨p, hp, hpdvd⟩ := WfDvdMonoid.exists_irreducible_factor hu hg0
  exact hF.coprime hjk hp (hpdvd.trans (EuclideanDomain.gcd_dvd_left _ _))
    (hpdvd.trans (EuclideanDomain.gcd_dvd_right _ _))

/-- **Pairwise coprimality of the abstract output**: distinct multiplicity
classes share no factor — in particular the output polynomials are pairwise
distinct (never `[(p, 2), (p, 3)]` for `p⁵`). -/
theorem yunPoly_pairwise_coprime [CharZero K] {a : K[X]} (ha : a.Monic) :
    (yunPoly a).Pairwise (fun gi gj => IsCoprime gi.1 gj.1) := by
  by_cases h0 : a.natDegree = 0
  · rw [yunPoly, if_pos h0]
    exact List.Pairwise.nil
  · obtain ⟨m, A, hF, -, hclosed⟩ := yunPoly_closed_form ha h0
    rw [hclosed, List.pairwise_map]
    refine List.Pairwise.filter _ ?_
    refine List.Pairwise.imp ?_ (List.pairwise_lt_range' ..)
    intro j k hjk
    exact hF.isCoprime' (Nat.ne_of_lt hjk)

variable [LinearOrder K] [PolynomialDerivative K]

/-- The sorted output is a permutation of the core run. -/
private theorem sf_perm (a : AzPolynomial K) :
    List.Perm (squarefreeFactorization a) (squarefreeFactorizationCore a) :=
  List.mergeSort_perm _ _

/-- Membership-level view of the bridge, for the sorted output. -/
private theorem sf_mem_yunPoly {a : AzPolynomial K} {gi : AzPolynomial K × ℕ}
    (h : gi ∈ squarefreeFactorization a) :
    (AzPolynomial.toPoly gi.1, gi.2) ∈ yunPoly (AzPolynomial.toPoly a) := by
  rw [← toPoly_squarefreeFactorizationCore a]
  exact List.mem_map_of_mem ((sf_perm a).mem_iff.mp h)

/-- **Product identity** (GCL Algorithm 8.2, correctness 1): for a monic
input, the product of the output polynomials raised to their exponents is
the original polynomial. -/
theorem squarefreeFactorization_prod [CharZero K]
    (a : AzPolynomial K) (ha : (AzPolynomial.toPoly a).Monic) :
    ((squarefreeFactorization a).map
      (fun gi => AzPolynomial.toPoly gi.1 ^ gi.2)).prod = AzPolynomial.toPoly a := by
  rw [((sf_perm a).map (fun gi : AzPolynomial K × ℕ =>
    AzPolynomial.toPoly gi.1 ^ gi.2)).prod_eq]
  have h := congrArg (fun l => (l.map (fun gi : K[X] × ℕ => gi.1 ^ gi.2)).prod)
    (toPoly_squarefreeFactorizationCore a)
  simp only [List.map_map] at h
  rw [← yunPoly_prod ha, ← h]
  rfl

/-- **Squarefreeness** (correctness 2): every output polynomial is
squarefree — moreover monic and nonconstant. -/
theorem squarefreeFactorization_squarefree [CharZero K]
    (a : AzPolynomial K) (ha : (AzPolynomial.toPoly a).Monic) :
    ∀ gi ∈ squarefreeFactorization a,
      Squarefree (AzPolynomial.toPoly gi.1) ∧ (AzPolynomial.toPoly gi.1).Monic
        ∧ (AzPolynomial.toPoly gi.1).natDegree ≠ 0 :=
  fun _ hgi => yunPoly_squarefree ha _ (sf_mem_yunPoly hgi)

/-- **Pairwise coprimality** (correctness 3a): distinct output entries carry
coprime polynomials — in particular the polynomials are pairwise distinct,
so a power `p⁵` is always the single pair `(p, 5)`, never split as
`[(p, 2), (p, 3)]`. -/
theorem squarefreeFactorization_pairwise_coprime [CharZero K]
    (a : AzPolynomial K) (ha : (AzPolynomial.toPoly a).Monic) :
    (squarefreeFactorization a).Pairwise
      (fun gi gj => IsCoprime (AzPolynomial.toPoly gi.1) (AzPolynomial.toPoly gj.1)) := by
  have habs := yunPoly_pairwise_coprime ha
  rw [← toPoly_squarefreeFactorizationCore a, List.pairwise_map] at habs
  exact ((sf_perm a).pairwise_iff (fun h => h.symm)).mpr habs

/-- **Canonically ordered** (correctness 3b): the output polynomials are
strictly increasing in the canonical polynomial order (degree, then
top-down lexicographic) — factor lists ascend, and the output has no
duplicates. -/
theorem squarefreeFactorization_sorted [CharZero K]
    (a : AzPolynomial K) (ha : (AzPolynomial.toPoly a).Monic) :
    ((squarefreeFactorization a).map Prod.fst).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  -- weak sortedness from the merge sort …
  have hle : (squarefreeFactorization a).Pairwise (fun gi gj => gi.1 ≤ gj.1) := by
    have h := List.pairwise_mergeSort
      (le := fun gi gj : AzPolynomial K × ℕ => decide (gi.1 ≤ gj.1))
      (fun x y z hxy hyz => by
        rw [decide_eq_true_eq] at hxy hyz ⊢
        exact le_trans hxy hyz)
      (fun x y => by
        rcases le_total x.1 y.1 with h | h <;> simp [h])
      (squarefreeFactorizationCore a)
    refine (List.Pairwise.imp ?_ h)
    intro x y hxy
    rwa [decide_eq_true_eq] at hxy
  -- … strengthened to strictness by distinctness (coprime nonconstants)
  have hco := squarefreeFactorization_pairwise_coprime a ha
  refine (hle.and hco).imp_of_mem ?_
  intro x y hx hy hxy
  obtain ⟨hle', hcop⟩ := hxy
  rcases lt_or_eq_of_le hle' with h | h
  · exact h
  · exfalso
    have hsq := squarefreeFactorization_squarefree a ha x hx
    rw [h] at hcop
    have hunit : IsUnit (AzPolynomial.toPoly y.1) := hcop.isUnit_of_dvd' dvd_rfl dvd_rfl
    exact hsq.2.2 (by rw [h]; exact Polynomial.natDegree_eq_zero_of_isUnit hunit)

end Azurite.AzPolynomial
