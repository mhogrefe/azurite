import Azurite.AzMvPolynomial.Bind1
import Azurite.AzMvPolynomial.Equiv.Pow
import Azurite.AzMvPolynomial.Equiv.SMul
import Azurite.AzMvPolynomial.Equiv.Add
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Equivalence: `AzMvPolynomial.bind₁` ↔ `MvPolynomial.bind₁`
-/

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

-- ═══════════════════════════════════════════════════════════════════
-- tailProd helper
-- ═══════════════════════════════════════════════════════════════════

/-- Tail product from index `i` onwards. -/
noncomputable def tailProd (m : MonicMonomial n ord)
    (g : Fin n → MvPolynomial (Fin n) R) (i : ℕ) : MvPolynomial (Fin n) R :=
  ∏ j ∈ Finset.univ.filter (fun (j : Fin n) => j.val ≥ i),
    g j ^ m.exponents[j]

omit [NoZeroDivisors R] [DecidableEq R] in
theorem tailProd_base (m : MonicMonomial n ord)
    (g : Fin n → MvPolynomial (Fin n) R) (i : ℕ) (hi : i ≥ n) :
    tailProd m g i = (1 : MvPolynomial (Fin n) R) := by
  unfold tailProd; apply Finset.prod_eq_one
  intro j hj; simp [Finset.mem_filter] at hj; omega

omit [NoZeroDivisors R] [DecidableEq R] in
theorem tailProd_step (m : MonicMonomial n ord)
    (g : Fin n → MvPolynomial (Fin n) R) (i : ℕ) (hi : i < n) :
    tailProd m g i =
    g (⟨i, hi⟩ : Fin n) ^ m.exponents[(⟨i, hi⟩ : Fin n)] *
    tailProd m g (i + 1) := by
  unfold tailProd
  have hsplit : Finset.univ.filter (fun (j : Fin n) => j.val ≥ i) =
      insert (⟨i, hi⟩ : Fin n) (Finset.univ.filter (fun j => j.val ≥ i + 1)) := by
    ext ⟨j, hj⟩; simp [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff]; omega
  have hnotmem : (⟨i, hi⟩ : Fin n) ∉ Finset.univ.filter (fun j : Fin n => j.val ≥ i + 1) := by
    simp [Finset.mem_filter]
  rw [hsplit, Finset.prod_insert hnotmem]

omit [NoZeroDivisors R] [DecidableEq R] in
theorem tailProd_zero_eq_prod_univ (m : MonicMonomial n ord)
    (g : Fin n → MvPolynomial (Fin n) R) :
    tailProd m g 0 = ∏ j : Fin n, g j ^ m.exponents[j] := by
  unfold tailProd; congr 1; ext j; simp

-- ═══════════════════════════════════════════════════════════════════
-- monicBind₁Aux invariant
-- ═══════════════════════════════════════════════════════════════════

private theorem vector_getElem_nat_eq_fin {α : Type _} {n : ℕ} (v : Vector α n)
    (i : ℕ) (hi : i < n) : v[i] = v[(⟨i, hi⟩ : Fin n)] := by
  rfl

theorem toMvPoly_monicBind₁Aux
    (m : MonicMonomial n ord) (f : Fin n → AzMvPolynomial n R ord)
    (i : ℕ) (acc : AzMvPolynomial n R ord) :
    toMvPoly (monicBind₁Aux m f i acc) =
    toMvPoly acc * tailProd m (fun v => toMvPoly (f v)) i := by
  suffices h : ∀ (k i : ℕ) (acc : AzMvPolynomial n R ord),
      n - i = k →
      toMvPoly (monicBind₁Aux m f i acc) =
      toMvPoly acc * tailProd m (fun v => toMvPoly (f v)) i from
    h (n - i) i acc rfl
  intro k
  induction k with
  | zero =>
    intro i acc hk
    unfold monicBind₁Aux
    simp [show ¬(i < n) from by omega, tailProd_base m _ i (by omega : i ≥ n)]
  | succ k ih =>
    intro i acc hk
    unfold monicBind₁Aux
    split
    · next hi =>
      rw [ih (i + 1) _ (by omega)]
      have hmul := toMvPoly_mul acc (AzMvPolynomial.pow (f ⟨i, hi⟩) m.exponents[i])
      rw [hmul, toMvPoly_pow]
      rw [tailProd_step m _ i hi]
      rw [vector_getElem_nat_eq_fin m.exponents i hi]
      ring
    · next hi => simp [tailProd_base m _ i (Nat.le_of_not_lt hi)]

-- ═══════════════════════════════════════════════════════════════════
-- Fin-product ↔ Finsupp-support-product
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors R] [DecidableEq R] in
theorem prod_fin_eq_prod_support (m : MonicMonomial n ord)
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
-- MonicMonomial.bind₁
-- ═══════════════════════════════════════════════════════════════════

theorem toMvPoly_monicBind₁  (m : MonicMonomial n ord)
    (f : Fin n → AzMvPolynomial n R ord) :
    toMvPoly (m.bind₁ f) =
    ∏ v ∈ m.toFinsupp.support, toMvPoly (f v) ^ (m.toFinsupp v) := by
  show toMvPoly (monicBind₁Aux m f 0 1) = _
  rw [toMvPoly_monicBind₁Aux]
  have hone : toMvPoly (1 : AzMvPolynomial n R ord) = (1 : MvPolynomial (Fin n) R) :=
    toMvPoly_one
  rw [hone, one_mul, tailProd_zero_eq_prod_univ]
  exact prod_fin_eq_prod_support m (fun v => toMvPoly (f v))

-- ═══════════════════════════════════════════════════════════════════
-- Monomial.bind₁
-- ═══════════════════════════════════════════════════════════════════

theorem toMvPoly_monomial_bind₁  (m : Monomial n R ord)
    (f : Fin n → AzMvPolynomial n R ord) :
    toMvPoly (m.bind₁ f) =
    (MvPolynomial.bind₁ (fun v => toMvPoly (f v))) m.toMvPoly := by
  show toMvPoly (m.coeff.val • m.monic.bind₁ f) = _
  have hsmul := toMvPoly_smul m.coeff.val (m.monic.bind₁ f)
  rw [hsmul, toMvPoly_monicBind₁ , Algebra.smul_def, MvPolynomial.algebraMap_eq,
      Monomial.toMvPoly, MvPolynomial.bind₁_monomial]

-- ═══════════════════════════════════════════════════════════════════
-- Full AzMvPolynomial.bind₁
-- ═══════════════════════════════════════════════════════════════════

private theorem toMvPoly_foldl_bind₁ 
    (l : List (Monomial n R ord)) (f : Fin n → AzMvPolynomial n R ord)
    (acc : AzMvPolynomial n R ord) :
    toMvPoly (l.foldl (fun acc m => acc + m.bind₁ f) acc) =
    toMvPoly acc +
    (l.map (fun m => toMvPoly (m.bind₁ f))).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    have hadd := toMvPoly_add acc (hd.bind₁ f)
    rw [hadd]; ring

@[simp] theorem toMvPoly_bind₁  (p : AzMvPolynomial n R ord)
    (f : Fin n → AzMvPolynomial n R ord) :
    toMvPoly (p.bind₁ f) =
    (MvPolynomial.bind₁ (fun v => toMvPoly (f v))) (toMvPoly p) := by
  show toMvPoly (p.terms.foldl (fun acc m => acc + m.bind₁ f) 0) = _
  rw [← Array.foldl_toList, toMvPoly_foldl_bind₁ ]
  have hzero : toMvPoly (0 : AzMvPolynomial n R ord) = (0 : MvPolynomial (Fin n) R) :=
    toMvPoly_zero
  rw [hzero, zero_add]
  simp only [toMvPoly_monomial_bind₁ ]
  rw [toMvPoly_eq_list_sum]
  have := map_list_sum (MvPolynomial.bind₁ (fun v => toMvPoly (f v)))
            (p.terms.toList.map Monomial.toMvPoly)
  rw [List.map_map] at this
  simp only [Function.comp_def] at this
  exact this.symm

@[simp] theorem ofMvPoly_bind₁  (p : MvPolynomial (Fin n) R)
    (g : Fin n → MvPolynomial (Fin n) R) :
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial n R ord).bind₁
      (fun v => AzMvPolynomial.ofMvPoly (g v)) =
    AzMvPolynomial.ofMvPoly ((MvPolynomial.bind₁ g) p) :=
  toMvPoly_injective (by rw [toMvPoly_bind₁ ]; simp only [toMvPoly_ofMvPoly])

end Azurite
