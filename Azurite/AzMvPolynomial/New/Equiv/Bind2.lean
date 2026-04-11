import Azurite.AzMvPolynomial.New.Bind2
import Azurite.AzMvPolynomial.New.Equiv.Mul
import Azurite.AzMvPolynomial.New.Equiv.Add
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Equivalence: `AzMvPolynomialNew.bind₂` ↔ `MvPolynomial.bind₂`
-/

namespace Azurite
open AzMvPolynomialNew

variable {R S : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  [CommSemiring S] [NoZeroDivisors S] [DecidableEq S]
  {n : ℕ} {ord : MonomialOrder}

-- ═══════════════════════════════════════════════════════════════════
-- Step 1: toMvPoly of MonicMonomialNew.toAzMvPoly
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors S] in
theorem toMvPoly_monicToAzMvPoly_new (m : MonicMonomialNew n ord) :
    toMvPoly (m.toAzMvPoly : AzMvPolynomialNew n S ord) =
    MvPolynomial.monomial m.toFinsupp 1 := by
  unfold MonicMonomialNew.toAzMvPoly
  split
  · next h =>
    simp only [toMvPoly_zero_new]
    rw [show (1 : S) = 0 from h, MvPolynomial.monomial_zero]
  · next h =>
    show toMvPoly (AzMvPolynomialNew.ofMonomial ⟨⟨1, h⟩, m⟩) = _
    simp [AzMvPolynomialNew.toMvPoly, AzMvPolynomialNew.ofMonomial, MonomialNew.toMvPoly]

-- ═══════════════════════════════════════════════════════════════════
-- Step 2: MonomialNew.bind₂
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors R] [DecidableEq R] in
/-- For a single monomial, bind₂ computes f(coeff) * (monic monomial as polynomial). -/
theorem toMvPoly_monomial_bind₂_new (f : R → AzMvPolynomialNew n S ord)
    (m : MonomialNew n R ord) :
    toMvPoly (m.bind₂ f) =
    toMvPoly (f m.coeff.val) * MvPolynomial.monomial m.monic.toFinsupp 1 := by
  show toMvPoly (f m.coeff.val * m.monic.toAzMvPoly) = _
  have hmul := toMvPoly_mul_new (f m.coeff.val) (m.monic.toAzMvPoly (S := S))
  rw [hmul, toMvPoly_monicToAzMvPoly_new]

-- ═══════════════════════════════════════════════════════════════════
-- Step 3: Full AzMvPolynomialNew.bind₂ (foldl)
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors R] [DecidableEq R] in
private theorem toMvPoly_foldl_bind₂_new
    (l : List (MonomialNew n R ord)) (f : R → AzMvPolynomialNew n S ord)
    (acc : AzMvPolynomialNew n S ord) :
    toMvPoly (l.foldl (fun acc m => acc + m.bind₂ f) acc) =
    toMvPoly acc +
    (l.map (fun m => toMvPoly (m.bind₂ f))).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    have hadd := toMvPoly_add_new acc (hd.bind₂ f)
    rw [hadd]; ring

-- ═══════════════════════════════════════════════════════════════════
-- Step 4: Forward equivalence (toMvPoly)
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors R] [DecidableEq R] in
/-- Forward equivalence: `toMvPoly (p.bind₂ f)` agrees with `bind₂` applied
    to `toMvPoly p`, when `f` is a ring homomorphism. -/
@[simp] theorem toMvPoly_bind₂_new (f : R →+* MvPolynomial (Fin n) S)
    (p : AzMvPolynomialNew n R ord) :
    toMvPoly (p.bind₂ (fun r => AzMvPolynomialNew.ofMvPoly (f r))) =
    (MvPolynomial.bind₂ f) (toMvPoly p) := by
  show toMvPoly (p.terms.foldl (fun acc m => acc + m.bind₂ (fun r => ofMvPoly (f r))) 0) = _
  rw [← Array.foldl_toList, toMvPoly_foldl_bind₂_new]
  have hzero : toMvPoly (0 : AzMvPolynomialNew n S ord) = (0 : MvPolynomial (Fin n) S) :=
    toMvPoly_zero_new
  rw [hzero, zero_add]
  simp only [toMvPoly_monomial_bind₂_new, toMvPoly_ofMvPoly_new]
  rw [toMvPoly_eq_list_sum]
  have hsums := map_list_sum (MvPolynomial.bind₂ f)
    (p.terms.toList.map MonomialNew.toMvPoly)
  rw [List.map_map] at hsums
  simp only [Function.comp_def] at hsums
  simp only [MonomialNew.toMvPoly, MvPolynomial.bind₂_monomial] at hsums
  exact hsums.symm

-- ═══════════════════════════════════════════════════════════════════
-- Step 5: Backward equivalence (ofMvPoly)
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors R] [DecidableEq R] in
@[simp] theorem ofMvPoly_bind₂_new (f : R →+* MvPolynomial (Fin n) S)
    (p : MvPolynomial (Fin n) R) :
    (AzMvPolynomialNew.ofMvPoly p : AzMvPolynomialNew n R ord).bind₂
      (fun r => AzMvPolynomialNew.ofMvPoly (f r)) =
    AzMvPolynomialNew.ofMvPoly ((MvPolynomial.bind₂ f) p) :=
  toMvPoly_injective_new (by rw [toMvPoly_bind₂_new]; simp only [toMvPoly_ofMvPoly_new])

end Azurite
