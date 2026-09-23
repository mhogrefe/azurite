/-
  **Correctness of the dedicated cyclotomic arithmetic**: `reduceCyc` lands in the
  residue class of its input (`toAdjoin_reduceCyc`), hence `cycMul a b = a * b`
  (`cycMul_eq`, via the lifted `AzNat` product mapped back along `ofAzNatRingHom`),
  the wrapper `CycF` is a monoid transported from `CycT`, and the fixed-window
  power `cycPow a u = a ^ u.toNat` (`cycPow_eq`).
-/
import Azurite.AzPolyMod.CycArith
import Azurite.AzPolyMod.Equiv.Cyclotomic
import Azurite.Algorithm.Equiv.SlidingWindowPowAzNat
import Azurite.Algorithm.Equiv.WindowPowAzNat
import Azurite.AzZMod.CastHom
import Azurite.CohenLenstra.Tables

namespace Azurite

namespace AzPolyMod

open _root_.Azurite.AzPolynomial Polynomial Finset

variable {n : AzNat} {p k : ℕ} [Fact (1 < n.toNat)] (hp : p.Prime) (hk : 0 < k)

/-- `zetaCoeff` as a difference of indicators, for `i < m`, `l < p^k`. -/
theorem zetaCoeff_eq_sub {R : Type _} [CommRing R] {i l : ℕ} (hi : i < (p - 1) * p ^ (k - 1)) :
    ((CL.zetaCoeff p k l i : ℤ) : R)
      = (if l = i then 1 else 0)
        - (if (p - 1) * p ^ (k - 1) ≤ l ∧ l % p ^ (k - 1) = i % p ^ (k - 1) then 1 else 0) := by
  unfold CL.zetaCoeff
  by_cases hl : l < (p - 1) * p ^ (k - 1)
  · have h2 : ¬ ((p - 1) * p ^ (k - 1) ≤ l ∧ l % p ^ (k - 1) = i % p ^ (k - 1)) := fun h => by omega
    rw [ite_eq_left hl, ite_eq_right h2, sub_zero]
    by_cases h : l = i
    · rw [ite_eq_left h.symm, ite_eq_left h]; simp
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]; simp
  · have h1 : ¬ l = i := by omega
    rw [ite_eq_right hl, ite_eq_right h1, zero_sub]
    by_cases h : i % p ^ (k - 1) = l % p ^ (k - 1)
    · rw [ite_eq_left h, ite_eq_left ⟨by omega, h.symm⟩]; simp
    · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.2.symm)]; simp

include hp hk in
/-- **The additive reduction lands in the residue class of its input.** -/
theorem toAdjoin_reduceCyc (c : AzPolynomial (AzZMod n)) :
    toAdjoin (reduceCyc n p k c)
      = AdjoinRoot.mk (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) (AzPolynomial.toPoly c) := by
  have hf := monic_toPoly_cyclotomicPrimePow (AzZMod n) p k
  have hz := eval₂_root_cyclotomic_int n p k hp hk
  have hz1 := CL.pow_eq_one_of_cyclotomic hz
  set m := (p - 1) * p ^ (k - 1) with hm
  set P := p ^ (k - 1) with hP
  set N := c.coeffs.size with hN
  -- the right side as a double sum
  have hR : AdjoinRoot.mk (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) (AzPolynomial.toPoly c)
      = ∑ i ∈ range m, (∑ j ∈ range N,
          AdjoinRoot.of (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) (c.coeff j)
            * ((CL.zetaCoeff p k (j % p ^ k) i : ℤ) : _))
          * AdjoinRoot.root (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) ^ i := by
    rw [toPoly_eq_sum_coeff c le_rfl, map_sum]
    simp only [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    have hterm : ∀ j ∈ range N,
        AdjoinRoot.of (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) (c.coeff j)
            * AdjoinRoot.root (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) ^ j
          = ∑ i ∈ range m,
            AdjoinRoot.of (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) (c.coeff j)
              * ((CL.zetaCoeff p k (j % p ^ k) i : ℤ) : _)
              * AdjoinRoot.root (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) ^ i := by
      intro j _
      have hpow : AdjoinRoot.root (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) ^ j
          = AdjoinRoot.root (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) ^ (j % p ^ k) := by
        conv_lhs => rw [← Nat.div_add_mod j (p ^ k)]
        rw [pow_add, pow_mul, hz1, one_pow, one_mul]
      rw [hpow, ← CL.sum_zetaCoeff hp hk hz (Nat.mod_lt _ (pow_pos hp.pos k)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  rw [hR, reduceCyc, toAdjoin_ofCoeffFn hf]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < m := Finset.mem_range.mp hi
  congr 1
  simp only [map_sub, map_sum]
  rw [Finset.sum_filter, Finset.sum_filter]
  have : ∀ j ∈ range N,
      AdjoinRoot.of (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) (c.coeff j)
          * ((CL.zetaCoeff p k (j % p ^ k) i : ℤ) : _)
      = (if j % p ^ k = i then
          AdjoinRoot.of (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) (c.coeff j) else 0)
        - (if m ≤ j % p ^ k ∧ j % p ^ k % P = i % P then
          AdjoinRoot.of (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) (c.coeff j) else 0) := by
    intro j _
    rw [zetaCoeff_eq_sub (k := k) hi', mul_sub, mul_ite, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]

/-- Reducing the coefficients is mapping the polynomial along `ofAzNatRingHom`. -/
theorem toPoly_reduceCoeffs (P : AzPolynomial AzNat) :
    AzPolynomial.toPoly (reduceCoeffs n P)
      = (AzPolynomial.toPoly P).map (AzZMod.ofAzNatRingHom (m := n)) := by
  rw [reduceCoeffs, toPoly_normalize_ofFn _ (fun j => AzZMod.ofAzNat n (P.coeff j)),
    toPoly_eq_sum_coeff P le_rfl, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  rfl

/-- The lifted coefficients map back to the original polynomial. -/
theorem toPoly_map_liftNat (a : CycT n p k) :
    (AzPolynomial.toPoly (liftNat n p k a)).map (AzZMod.ofAzNatRingHom (m := n))
      = AzPolynomial.toPoly a.val := by
  rw [liftNat, toPoly_normalize_ofFn _ (fun j => (a.val.coeff j).val), Polynomial.map_sum,
    toPoly_eq_sum_coeff a.val le_rfl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  congr 2
  exact AzZMod.ofAzNat_val _

include hp hk in
/-- **The dedicated multiplication is the ring multiplication.** -/
theorem cycMul_eq (a b : CycT n p k) : cycMul n p k a b = a * b := by
  apply toAdjoin_injective (monic_toPoly_cyclotomicPrimePow (AzZMod n) p k)
    (monic_toPoly_cyclotomicPrimePow (AzZMod n) p k).ne_zero
  rw [cycMul, toAdjoin_reduceCyc hp hk, toPoly_reduceCoeffs, toPoly_mul, Polynomial.map_mul,
    toPoly_map_liftNat, toPoly_map_liftNat, map_mul, toAdjoin_mul
    (monic_toPoly_cyclotomicPrimePow (AzZMod n) p k) (monic_toPoly_cyclotomicPrimePow (AzZMod n) p k).ne_zero]
  rfl

include hp hk in
/-- The wrapper is a monoid, transported from `CycT` (its multiplication being `cycMul`). -/
@[instance_reducible] noncomputable def cycFMonoid : Monoid (CycF n p k) :=
  Function.Injective.monoid (ofF n p k) (fun _ _ h => h) rfl (fun _ _ => cycMul_eq hp hk _ _)
    (fun _ _ => rfl)

include hp hk in
/-- **`cycPow` is the monoid power.** -/
theorem cycPow_eq (a : CycT n p k) (u : AzNat) : cycPow n p k a u = a ^ u.toNat := by
  let := cycFMonoid (n := n) hp hk
  exact Azurite.windowPowAzNat_eq_pow (toF n p k a) u

end AzPolyMod

end Azurite
