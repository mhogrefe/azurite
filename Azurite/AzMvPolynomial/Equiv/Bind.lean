import Azurite.AzMvPolynomial.Bind
import Azurite.AzMvPolynomial.Equiv.Pow
import Azurite.AzMvPolynomial.Equiv.SMul
import Azurite.AzMvPolynomial.Equiv.Add
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Equivalence: AzMvPolynomial.bind₁ ↔ MvPolynomial.bind₁
-/

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

-- ═══════════════════════════════════════════════════════════════════
-- tailProd helper
-- ═══════════════════════════════════════════════════════════════════

/-- Tail product from index `i` onwards. Uses `Fin n` indices for both
    the product and the exponent access. -/
noncomputable def tailProd (m : MonicMonomial σ ord)
    (g : σ → MvPolynomial σ R) (i : ℕ) : MvPolynomial σ R :=
  ∏ j ∈ Finset.univ.filter (fun (j : Fin n) => j.val ≥ i),
    g (Var.ofFin j) ^ m.exponents[j]

omit [NoZeroDivisors R] [DecidableEq R] in
theorem tailProd_base (m : MonicMonomial σ ord)
    (g : σ → MvPolynomial σ R) (i : ℕ) (hi : i ≥ n) :
    tailProd m g i = (1 : MvPolynomial σ R) := by
  unfold tailProd; apply Finset.prod_eq_one
  intro j hj; simp [Finset.mem_filter] at hj; omega

omit [NoZeroDivisors R] [DecidableEq R] in
theorem tailProd_step (m : MonicMonomial σ ord)
    (g : σ → MvPolynomial σ R) (i : ℕ) (hi : i < n) :
    tailProd m g i =
    g (Var.ofFin (⟨i, hi⟩ : Fin n)) ^ m.exponents[(⟨i, hi⟩ : Fin n)] *
    tailProd m g (i + 1) := by
  unfold tailProd
  have hsplit : Finset.univ.filter (fun (j : Fin n) => j.val ≥ i) =
      insert (⟨i, hi⟩ : Fin n) (Finset.univ.filter (fun j => j.val ≥ i + 1)) := by
    ext ⟨j, hj⟩; simp [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff]; omega
  have hnotmem : (⟨i, hi⟩ : Fin n) ∉ Finset.univ.filter (fun j : Fin n => j.val ≥ i + 1) := by
    simp [Finset.mem_filter]
  rw [hsplit, Finset.prod_insert hnotmem]

omit [NoZeroDivisors R] [DecidableEq R] in
theorem tailProd_zero_eq_prod_univ (m : MonicMonomial σ ord)
    (g : σ → MvPolynomial σ R) :
    tailProd m g 0 = ∏ j : Fin n, g (Var.ofFin j) ^ m.exponents[j] := by
  unfold tailProd; congr 1; ext j; simp

-- ═══════════════════════════════════════════════════════════════════
-- monicBind₁Aux invariant
-- ═══════════════════════════════════════════════════════════════════

/-- For Vector, `v[i]` (Nat-indexed with auto proof) = `v[⟨i, hi⟩]` (Fin-indexed). -/
private theorem vector_getElem_nat_eq_fin {α : Type _} {n : ℕ} (v : Vector α n)
    (i : ℕ) (hi : i < n) : v[i] = v[(⟨i, hi⟩ : Fin n)] := by
  rfl

theorem toMvPoly_monicBind₁Aux
    (m : MonicMonomial σ ord) (f : σ → AzMvPolynomial σ R ord)
    (i : ℕ) (acc : AzMvPolynomial σ R ord) :
    toMvPoly (monicBind₁Aux m f i acc) =
    toMvPoly acc * tailProd m (fun v => toMvPoly (f v)) i := by
  suffices h : ∀ (k i : ℕ) (acc : AzMvPolynomial σ R ord),
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
      -- toMvPoly_mul gives us: toMvPoly (a * b) = a.toMvPoly * b.toMvPoly
      have hmul := toMvPoly_mul acc (AzMvPolynomial.pow (f (Var.ofFin ⟨i, hi⟩)) m.exponents[i])
      rw [hmul, toMvPoly_pow]
      -- Now: acc.toMvPoly * toMvPoly(f _) ^ e[i] * tailProd ... (i+1)
      --    = acc.toMvPoly * tailProd ... i
      rw [tailProd_step m _ i hi]
      -- Unify m.exponents[i] with m.exponents[⟨i,hi⟩]
      rw [vector_getElem_nat_eq_fin m.exponents i hi]
      ring
    · next hi => simp [tailProd_base m _ i (Nat.le_of_not_lt hi)]

-- ═══════════════════════════════════════════════════════════════════
-- Fin-product ↔ Finsupp-support-product
-- ═══════════════════════════════════════════════════════════════════

omit [NoZeroDivisors R] [DecidableEq R] in
theorem prod_fin_eq_prod_support (m : MonicMonomial σ ord)
    (g : σ → MvPolynomial σ R) :
    (∏ j : Fin n, g (Var.ofFin j) ^ m.exponents[j]) =
    ∏ v ∈ m.toFinsupp.support, g v ^ (m.toFinsupp v) := by
  have hinj := @Var.ofFin_injective σ n _ _
  have himg : (∏ j : Fin n, g (Var.ofFin j) ^ m.exponents[j])
      = ∏ v ∈ Finset.univ.image (@Var.ofFin σ n _ _), g v ^ (m.toFinsupp v) := by
    rw [Finset.prod_image (fun a _ b _ hab => hinj hab)]
    congr 1; ext j
    simp [MonicMonomial.toFinsupp, Finsupp.onFinset_apply, Var.toFin_ofFin]
  rw [himg]; symm; apply Finset.prod_subset
  · intro v hv
    rw [Finset.mem_image]; exact ⟨Var.toFin v, Finset.mem_univ _, Var.ofFin_toFin v⟩
  · intro v _ hv; simp only [Finsupp.mem_support_iff, not_not] at hv; rw [hv, pow_zero]

-- ═══════════════════════════════════════════════════════════════════
-- MonicMonomial.bind₁
-- ═══════════════════════════════════════════════════════════════════

theorem toMvPoly_monicBind₁ (m : MonicMonomial σ ord)
    (f : σ → AzMvPolynomial σ R ord) :
    toMvPoly (m.bind₁ f) =
    ∏ v ∈ m.toFinsupp.support, toMvPoly (f v) ^ (m.toFinsupp v) := by
  show toMvPoly (monicBind₁Aux m f 0 1) = _
  rw [toMvPoly_monicBind₁Aux]
  have hone : toMvPoly (1 : AzMvPolynomial σ R ord) = (1 : MvPolynomial σ R) := toMvPoly_one
  rw [hone, one_mul, tailProd_zero_eq_prod_univ]
  exact prod_fin_eq_prod_support m (fun v => toMvPoly (f v))

-- ═══════════════════════════════════════════════════════════════════
-- Monomial.bind₁
-- ═══════════════════════════════════════════════════════════════════

theorem toMvPoly_monomial_bind₁ (m : Monomial σ R ord)
    (f : σ → AzMvPolynomial σ R ord) :
    toMvPoly (m.bind₁ f) =
    (MvPolynomial.bind₁ (fun v => toMvPoly (f v))) m.toMvPoly := by
  show toMvPoly (m.coeff.val • m.monic.bind₁ f) = _
  have hsmul := toMvPoly_smul m.coeff.val (m.monic.bind₁ f)
  rw [hsmul, toMvPoly_monicBind₁, Algebra.smul_def, MvPolynomial.algebraMap_eq,
      Monomial.toMvPoly, MvPolynomial.bind₁_monomial]

-- ═══════════════════════════════════════════════════════════════════
-- Full AzMvPolynomial.bind₁
-- ═══════════════════════════════════════════════════════════════════

private theorem toMvPoly_foldl_bind₁
    (l : List (Monomial σ R ord)) (f : σ → AzMvPolynomial σ R ord)
    (acc : AzMvPolynomial σ R ord) :
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

@[simp] theorem toMvPoly_bind₁ (p : AzMvPolynomial σ R ord)
    (f : σ → AzMvPolynomial σ R ord) :
    toMvPoly (p.bind₁ f) =
    (MvPolynomial.bind₁ (fun v => toMvPoly (f v))) (toMvPoly p) := by
  show toMvPoly (p.terms.foldl (fun acc m => acc + m.bind₁ f) 0) = _
  rw [← Array.foldl_toList, toMvPoly_foldl_bind₁]
  have hzero : toMvPoly (0 : AzMvPolynomial σ R ord) = (0 : MvPolynomial σ R) := toMvPoly_zero
  rw [hzero, zero_add]
  -- LHS: (terms.toList.map (fun m => bind₁ g (m.toMvPoly))).sum
  -- RHS: bind₁ g (toMvPoly p) = bind₁ g ((terms.toList.map toMvPoly).sum)
  simp only [toMvPoly_monomial_bind₁]
  rw [toMvPoly_eq_list_sum]
  -- Goal: (map (fun m => bind₁ g (m.toMvPoly)) terms).sum = bind₁ g ((map toMvPoly terms).sum)
  -- bind₁ g distributes over sums (it's an AlgHom), and map distributes
  have := map_list_sum (MvPolynomial.bind₁ (fun v => toMvPoly (f v)))
            (p.terms.toList.map Monomial.toMvPoly)
  rw [List.map_map] at this
  simp only [Function.comp_def] at this
  exact this.symm

@[simp] theorem ofMvPoly_bind₁ (p : MvPolynomial σ R)
    (g : σ → MvPolynomial σ R) :
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial σ R ord).bind₁
      (fun v => AzMvPolynomial.ofMvPoly (g v)) =
    AzMvPolynomial.ofMvPoly ((MvPolynomial.bind₁ g) p) :=
  toMvPoly_injective (by rw [toMvPoly_bind₁]; simp only [toMvPoly_ofMvPoly])

end Azurite
