import Azurite.AzMvPolynomial.New.Bind1
import Azurite.AzMvPolynomial.New.Equiv.Pow
import Azurite.AzMvPolynomial.New.Equiv.SMul
import Azurite.AzMvPolynomial.New.Equiv.Add
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Equivalence: `AzMvPolynomialNew.bind₁` ↔ `MvPolynomial.bind₁`
-/

namespace Azurite
open AzMvPolynomialNew

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

-- ═══════════════════════════════════════════════════════════════════
-- tailProd helper
-- ═══════════════════════════════════════════════════════════════════

/-- Tail product from index `i` onwards. -/
noncomputable def tailProdNew (m : MonicMonomialNew n ord)
    (g : Fin n → MvPolynomial (Fin n) R) (i : ℕ) : MvPolynomial (Fin n) R :=
  ∏ j ∈ Finset.univ.filter (fun (j : Fin n) => j.val ≥ i),
    g j ^ m.exponents[j]

omit [NoZeroDivisors R] [DecidableEq R] in
theorem tailProdNew_base (m : MonicMonomialNew n ord)
    (g : Fin n → MvPolynomial (Fin n) R) (i : ℕ) (hi : i ≥ n) :
    tailProdNew m g i = (1 : MvPolynomial (Fin n) R) := by
  unfold tailProdNew; apply Finset.prod_eq_one
  intro j hj; simp [Finset.mem_filter] at hj; omega

omit [NoZeroDivisors R] [DecidableEq R] in
theorem tailProdNew_step (m : MonicMonomialNew n ord)
    (g : Fin n → MvPolynomial (Fin n) R) (i : ℕ) (hi : i < n) :
    tailProdNew m g i =
    g (⟨i, hi⟩ : Fin n) ^ m.exponents[(⟨i, hi⟩ : Fin n)] *
    tailProdNew m g (i + 1) := by
  unfold tailProdNew
  have hsplit : Finset.univ.filter (fun (j : Fin n) => j.val ≥ i) =
      insert (⟨i, hi⟩ : Fin n) (Finset.univ.filter (fun j => j.val ≥ i + 1)) := by
    ext ⟨j, hj⟩; simp [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff]; omega
  have hnotmem : (⟨i, hi⟩ : Fin n) ∉ Finset.univ.filter (fun j : Fin n => j.val ≥ i + 1) := by
    simp [Finset.mem_filter]
  rw [hsplit, Finset.prod_insert hnotmem]

omit [NoZeroDivisors R] [DecidableEq R] in
theorem tailProdNew_zero_eq_prod_univ (m : MonicMonomialNew n ord)
    (g : Fin n → MvPolynomial (Fin n) R) :
    tailProdNew m g 0 = ∏ j : Fin n, g j ^ m.exponents[j] := by
  unfold tailProdNew; congr 1; ext j; simp

-- ═══════════════════════════════════════════════════════════════════
-- monicBind₁AuxNew invariant
-- ═══════════════════════════════════════════════════════════════════

private theorem vector_getElem_nat_eq_fin_new {α : Type _} {n : ℕ} (v : Vector α n)
    (i : ℕ) (hi : i < n) : v[i] = v[(⟨i, hi⟩ : Fin n)] := by
  rfl

theorem toMvPoly_monicBind₁AuxNew
    (m : MonicMonomialNew n ord) (f : Fin n → AzMvPolynomialNew n R ord)
    (i : ℕ) (acc : AzMvPolynomialNew n R ord) :
    toMvPoly (monicBind₁AuxNew m f i acc) =
    toMvPoly acc * tailProdNew m (fun v => toMvPoly (f v)) i := by
  suffices h : ∀ (k i : ℕ) (acc : AzMvPolynomialNew n R ord),
      n - i = k →
      toMvPoly (monicBind₁AuxNew m f i acc) =
      toMvPoly acc * tailProdNew m (fun v => toMvPoly (f v)) i from
    h (n - i) i acc rfl
  intro k
  induction k with
  | zero =>
    intro i acc hk
    unfold monicBind₁AuxNew
    simp [show ¬(i < n) from by omega, tailProdNew_base m _ i (by omega : i ≥ n)]
  | succ k ih =>
    intro i acc hk
    unfold monicBind₁AuxNew
    split
    · next hi =>
      rw [ih (i + 1) _ (by omega)]
      have hmul := toMvPoly_mul_new acc (AzMvPolynomialNew.pow (f ⟨i, hi⟩) m.exponents[i])
      rw [hmul, toMvPoly_pow_new]
      rw [tailProdNew_step m _ i hi]
      rw [vector_getElem_nat_eq_fin_new m.exponents i hi]
      ring
    · next hi => simp [tailProdNew_base m _ i (Nat.le_of_not_lt hi)]

-- ═══════════════════════════════════════════════════════════════════
-- Fin-product ↔ Finsupp-support-product
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors R] [DecidableEq R] in
theorem prod_fin_eq_prod_support_new (m : MonicMonomialNew n ord)
    (g : Fin n → MvPolynomial (Fin n) R) :
    (∏ j : Fin n, g j ^ m.exponents[j]) =
    ∏ v ∈ m.toFinsupp.support, g v ^ (m.toFinsupp v) := by
  have hrewrite : ∀ v : Fin n, g v ^ m.exponents[v] = g v ^ m.toFinsupp v := by
    intro v; rfl
  simp_rw [hrewrite]
  symm; apply Finset.prod_subset (Finset.subset_univ _)
  intro v _ hv
  simp only [Finsupp.mem_support_iff, not_not] at hv
  rw [hv, pow_zero]

-- ═══════════════════════════════════════════════════════════════════
-- MonicMonomialNew.bind₁
-- ═══════════════════════════════════════════════════════════════════

theorem toMvPoly_monicBind₁_new (m : MonicMonomialNew n ord)
    (f : Fin n → AzMvPolynomialNew n R ord) :
    toMvPoly (m.bind₁ f) =
    ∏ v ∈ m.toFinsupp.support, toMvPoly (f v) ^ (m.toFinsupp v) := by
  show toMvPoly (monicBind₁AuxNew m f 0 1) = _
  rw [toMvPoly_monicBind₁AuxNew]
  have hone : toMvPoly (1 : AzMvPolynomialNew n R ord) = (1 : MvPolynomial (Fin n) R) :=
    toMvPoly_one_new
  rw [hone, one_mul, tailProdNew_zero_eq_prod_univ]
  exact prod_fin_eq_prod_support_new m (fun v => toMvPoly (f v))

-- ═══════════════════════════════════════════════════════════════════
-- MonomialNew.bind₁
-- ═══════════════════════════════════════════════════════════════════

theorem toMvPoly_monomial_bind₁_new (m : MonomialNew n R ord)
    (f : Fin n → AzMvPolynomialNew n R ord) :
    toMvPoly (m.bind₁ f) =
    (MvPolynomial.bind₁ (fun v => toMvPoly (f v))) m.toMvPoly := by
  show toMvPoly (m.coeff.val • m.monic.bind₁ f) = _
  have hsmul := toMvPoly_smul_new m.coeff.val (m.monic.bind₁ f)
  rw [hsmul, toMvPoly_monicBind₁_new, Algebra.smul_def, MvPolynomial.algebraMap_eq,
      MonomialNew.toMvPoly, MvPolynomial.bind₁_monomial]

-- ═══════════════════════════════════════════════════════════════════
-- Full AzMvPolynomialNew.bind₁
-- ═══════════════════════════════════════════════════════════════════

private theorem toMvPoly_foldl_bind₁_new
    (l : List (MonomialNew n R ord)) (f : Fin n → AzMvPolynomialNew n R ord)
    (acc : AzMvPolynomialNew n R ord) :
    toMvPoly (l.foldl (fun acc m => acc + m.bind₁ f) acc) =
    toMvPoly acc +
    (l.map (fun m => toMvPoly (m.bind₁ f))).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    have hadd := toMvPoly_add_new acc (hd.bind₁ f)
    rw [hadd]; ring

@[simp] theorem toMvPoly_bind₁_new (p : AzMvPolynomialNew n R ord)
    (f : Fin n → AzMvPolynomialNew n R ord) :
    toMvPoly (p.bind₁ f) =
    (MvPolynomial.bind₁ (fun v => toMvPoly (f v))) (toMvPoly p) := by
  show toMvPoly (p.terms.foldl (fun acc m => acc + m.bind₁ f) 0) = _
  rw [← Array.foldl_toList, toMvPoly_foldl_bind₁_new]
  have hzero : toMvPoly (0 : AzMvPolynomialNew n R ord) = (0 : MvPolynomial (Fin n) R) :=
    toMvPoly_zero_new
  rw [hzero, zero_add]
  simp only [toMvPoly_monomial_bind₁_new]
  rw [toMvPoly_eq_list_sum]
  have := map_list_sum (MvPolynomial.bind₁ (fun v => toMvPoly (f v)))
            (p.terms.toList.map MonomialNew.toMvPoly)
  rw [List.map_map] at this
  simp only [Function.comp_def] at this
  exact this.symm

@[simp] theorem ofMvPoly_bind₁_new (p : MvPolynomial (Fin n) R)
    (g : Fin n → MvPolynomial (Fin n) R) :
    (AzMvPolynomialNew.ofMvPoly p : AzMvPolynomialNew n R ord).bind₁
      (fun v => AzMvPolynomialNew.ofMvPoly (g v)) =
    AzMvPolynomialNew.ofMvPoly ((MvPolynomial.bind₁ g) p) :=
  toMvPoly_injective_new (by rw [toMvPoly_bind₁_new]; simp only [toMvPoly_ofMvPoly_new])

end Azurite
