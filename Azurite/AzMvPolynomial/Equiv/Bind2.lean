import Azurite.AzMvPolynomial.Bind2
import Azurite.AzMvPolynomial.Equiv.Mul
import Azurite.AzMvPolynomial.Equiv.Add
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Equivalence: `AzMvPolynomial.bind₂` ↔ `MvPolynomial.bind₂`
-/

namespace Azurite
open AzMvPolynomial

variable {R S : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  [CommSemiring S] [NoZeroDivisors S] [DecidableEq S]
  {n : ℕ} {ord : MonomialOrder}

-- ═══════════════════════════════════════════════════════════════════
-- Step 1: toMvPoly of MonicMonomial.toAzMvPoly
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors S] in
theorem toMvPoly_monicToAzMvPoly (m : MonicMonomial n ord) :
    toMvPoly (m.toAzMvPoly : AzMvPolynomial n S ord) =
    MvPolynomial.monomial m.toFinsupp 1 := by
  unfold MonicMonomial.toAzMvPoly
  split
  · next h =>
    simp only [toMvPoly_zero]
    rw [show (1 : S) = 0 from h, MvPolynomial.monomial_zero]
  · next h =>
    show toMvPoly (AzMvPolynomial.ofMonomial ⟨⟨1, h⟩, m⟩) = _
    simp [AzMvPolynomial.toMvPoly, AzMvPolynomial.ofMonomial, Monomial.toMvPoly]

-- ═══════════════════════════════════════════════════════════════════
-- Step 2: Monomial.bind₂
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors R] [DecidableEq R] in
/-- For a single monomial, bind₂ computes f(coeff) * (monic monomial as polynomial). -/
theorem toMvPoly_monomial_bind₂  (f : R → AzMvPolynomial n S ord)
    (m : Monomial n R ord) :
    toMvPoly (m.bind₂ f) =
    toMvPoly (f m.coeff.val) * MvPolynomial.monomial m.monic.toFinsupp 1 := by
  show toMvPoly (f m.coeff.val * m.monic.toAzMvPoly) = _
  have hmul := toMvPoly_mul (f m.coeff.val) (m.monic.toAzMvPoly (S := S))
  rw [hmul, toMvPoly_monicToAzMvPoly]

-- ═══════════════════════════════════════════════════════════════════
-- Step 3: Full AzMvPolynomial.bind₂ (foldl)
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors R] [DecidableEq R] in
private theorem toMvPoly_foldl_bind₂
    (l : List (Monomial n R ord)) (f : R → AzMvPolynomial n S ord)
    (acc : AzMvPolynomial n S ord) :
    toMvPoly (l.foldl (fun acc m => acc + m.bind₂ f) acc) =
    toMvPoly acc +
    (l.map (fun m => toMvPoly (m.bind₂ f))).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    have hadd := toMvPoly_add acc (hd.bind₂ f)
    rw [hadd]; ring

-- ═══════════════════════════════════════════════════════════════════
-- Step 4: Forward equivalence (toMvPoly)
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors R] [DecidableEq R] in
/-- Forward equivalence: `toMvPoly (p.bind₂ f)` agrees with `bind₂` applied
    to `toMvPoly p`, when `f` is a ring homomorphism. -/
@[simp] theorem toMvPoly_bind₂  (f : R →+* MvPolynomial (Fin n) S)
    (p : AzMvPolynomial n R ord) :
    toMvPoly (p.bind₂ (fun r => AzMvPolynomial.ofMvPoly (f r))) =
    (MvPolynomial.bind₂ f) (toMvPoly p) := by
  show toMvPoly (p.terms.foldl (fun acc m => acc + m.bind₂ (fun r => ofMvPoly (f r))) 0) = _
  rw [← Array.foldl_toList, toMvPoly_foldl_bind₂ ]
  have hzero : toMvPoly (0 : AzMvPolynomial n S ord) = (0 : MvPolynomial (Fin n) S) :=
    toMvPoly_zero
  rw [hzero, zero_add]
  simp only [toMvPoly_monomial_bind₂ , toMvPoly_ofMvPoly]
  rw [toMvPoly_eq_list_sum]
  have hsums := map_list_sum (MvPolynomial.bind₂ f)
    (p.terms.toList.map Monomial.toMvPoly)
  rw [List.map_map] at hsums
  simp only [Function.comp_def] at hsums
  simp only [Monomial.toMvPoly, MvPolynomial.bind₂_monomial] at hsums
  exact hsums.symm

-- ═══════════════════════════════════════════════════════════════════
-- Step 5: Backward equivalence (ofMvPoly)
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors R] [DecidableEq R] in
@[simp] theorem ofMvPoly_bind₂  (f : R →+* MvPolynomial (Fin n) S)
    (p : MvPolynomial (Fin n) R) :
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial n R ord).bind₂
      (fun r => AzMvPolynomial.ofMvPoly (f r)) =
    AzMvPolynomial.ofMvPoly ((MvPolynomial.bind₂ f) p) :=
  toMvPoly_injective (by rw [toMvPoly_bind₂ ]; simp only [toMvPoly_ofMvPoly])

end Azurite
