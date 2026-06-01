import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_84
import Azurite.BasuPollackRoy.Chapter2.Section2_5.PolynomialIsSemialgebraic

/-! # BPR Proposition 2.85: semialgebraic functions form a ring

Let `A ⊆ Rᵏ` be a semialgebraic set. The semialgebraic functions `A → R` form a ring under
pointwise operations. Following BPR, `f + g` is the composition of the pairing `(f, g) : A → R²`
with `+ : R² → R`, and `f · g` with `· : R² → R` (Proposition 2.84); these last two are
polynomial functions. We model functions `A → R` as total maps `(Fin k → R) → (Fin 1 → R)` and
exhibit the semialgebraic ones as a `Subring` of the pointwise function ring.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [IsRealClosed R] in
/-- A polynomial function is semialgebraic on any semialgebraic domain `A`. -/
theorem polyFun_isSemialgebraicFunction_on {k : ℕ} {A : Set (Fin k → R)}
    (hA : IsSemialgebraicSet A) (P : MvPolynomial (Fin k) R) :
    IsSemialgebraicFunction A (polyFun P) := by
  show IsSemialgebraicSet (funGraph A (polyFun P))
  have heq : funGraph A (polyFun P)
      = funGraph (Set.univ : Set (Fin k → R)) (polyFun P) ∩ {z | z ∘ Fin.castAdd 1 ∈ A} := by
    ext z
    simp only [mem_funGraph, Set.mem_univ, true_and, Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  rw [heq]
  exact (polyFun_isSemialgebraicFunction P).inter (IsSemialgebraicSet.comap (Fin.castAdd 1) hA)

/-- Addition `R² → R` as a (polynomial) function. -/
noncomputable def addFun : (Fin 2 → R) → (Fin 1 → R) := polyFun (X 0 + X 1)

/-- Multiplication `R² → R` as a (polynomial) function. -/
noncomputable def mulFun : (Fin 2 → R) → (Fin 1 → R) := polyFun (X 0 * X 1)

/-- Negation `R → R` as a (polynomial) function. -/
noncomputable def negFun : (Fin 1 → R) → (Fin 1 → R) := polyFun (-(X 0))

omit [IsRealClosed R] in
/-- **The pairing `(f, g) : A → R²` is semialgebraic** when `f, g : A → R` are. Its graph is
the intersection of the graphs of `f` and `g`, each pulled back into `R^{k+2}`. -/
theorem pair_isSemialgebraicFunction {k : ℕ} {A : Set (Fin k → R)}
    {f g : (Fin k → R) → (Fin 1 → R)}
    (hf : IsSemialgebraicFunction A f) (hg : IsSemialgebraicFunction A g) :
    IsSemialgebraicFunction A (fun (x : Fin k → R) (j : Fin 2) => if j = 0 then f x 0 else g x 0) := by
  set gf : Fin (k + 1) → Fin (k + 2) :=
    Fin.addCases (fun i : Fin k => Fin.castAdd 2 i) (fun _ : Fin 1 => Fin.natAdd k 0) with hgf
  set gg : Fin (k + 1) → Fin (k + 2) :=
    Fin.addCases (fun i : Fin k => Fin.castAdd 2 i) (fun _ : Fin 1 => Fin.natAdd k 1) with hgg
  have hgf_cast : ∀ z : Fin (k + 2) → R, (z ∘ gf) ∘ Fin.castAdd 1 = z ∘ Fin.castAdd 2 := by
    intro z; funext i; show z (gf (Fin.castAdd 1 i)) = z (Fin.castAdd 2 i)
    simp only [hgf, Fin.addCases_left]
  have hgg_cast : ∀ z : Fin (k + 2) → R, (z ∘ gg) ∘ Fin.castAdd 1 = z ∘ Fin.castAdd 2 := by
    intro z; funext i; show z (gg (Fin.castAdd 1 i)) = z (Fin.castAdd 2 i)
    simp only [hgg, Fin.addCases_left]
  have hgf_nat : ∀ z : Fin (k + 2) → R,
      (z ∘ gf) ∘ Fin.natAdd k = fun _ : Fin 1 => z (Fin.natAdd k 0) := by
    intro z; funext j; show z (gf (Fin.natAdd k j)) = z (Fin.natAdd k 0)
    simp only [hgf, Fin.addCases_right]
  have hgg_nat : ∀ z : Fin (k + 2) → R,
      (z ∘ gg) ∘ Fin.natAdd k = fun _ : Fin 1 => z (Fin.natAdd k 1) := by
    intro z; funext j; show z (gg (Fin.natAdd k j)) = z (Fin.natAdd k 1)
    simp only [hgg, Fin.addCases_right]
  have memf : ∀ z : Fin (k + 2) → R, (z ∘ gf ∈ funGraph A f) ↔
      (z ∘ Fin.castAdd 2 ∈ A ∧ z (Fin.natAdd k 0) = f (z ∘ Fin.castAdd 2) 0) := by
    intro z
    rw [mem_funGraph, hgf_cast, hgf_nat]
    refine and_congr_right (fun _ => ?_)
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext j; rw [Subsingleton.elim j 0]; exact h
  have memg : ∀ z : Fin (k + 2) → R, (z ∘ gg ∈ funGraph A g) ↔
      (z ∘ Fin.castAdd 2 ∈ A ∧ z (Fin.natAdd k 1) = g (z ∘ Fin.castAdd 2) 0) := by
    intro z
    rw [mem_funGraph, hgg_cast, hgg_nat]
    refine and_congr_right (fun _ => ?_)
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext j; rw [Subsingleton.elim j 0]; exact h
  show IsSemialgebraicSet
    (funGraph A (fun (x : Fin k → R) (j : Fin 2) => if j = 0 then f x 0 else g x 0))
  have hgraph : funGraph A (fun (x : Fin k → R) (j : Fin 2) => if j = 0 then f x 0 else g x 0)
      = {z | z ∘ gf ∈ funGraph A f} ∩ {z | z ∘ gg ∈ funGraph A g} := by
    ext z
    rw [mem_funGraph, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_setOf_eq, memf, memg]
    constructor
    · rintro ⟨hA, hfg⟩
      have h0 := congrFun hfg 0
      have h1 := congrFun hfg 1
      simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)] at h0 h1
      exact ⟨⟨hA, h0⟩, hA, h1⟩
    · rintro ⟨⟨hA, h0⟩, _, h1⟩
      refine ⟨hA, ?_⟩
      rw [funext_iff, Fin.forall_fin_two]
      simp only [Function.comp_apply, if_neg (by decide : (1 : Fin 2) ≠ 0)]
      exact ⟨h0, h1⟩
  rw [hgraph]
  exact (IsSemialgebraicSet.comap gf hf).inter (IsSemialgebraicSet.comap gg hg)

variable {k : ℕ} {A : Set (Fin k → R)} {f g : (Fin k → R) → (Fin 1 → R)}

/-- Sum of semialgebraic functions is semialgebraic: `f + g = (+) ∘ (f, g)`. -/
theorem IsSemialgebraicFunction.add
    (hf : IsSemialgebraicFunction A f) (hg : IsSemialgebraicFunction A g) :
    IsSemialgebraicFunction A (f + g) := by
  have heq : f + g
      = addFun ∘ (fun (x : Fin k → R) (j : Fin 2) => if j = 0 then f x 0 else g x 0) := by
    funext x i; rw [Subsingleton.elim i 0]
    show (f x + g x) 0 = addFun (fun j => if j = 0 then f x 0 else g x 0) 0
    simp only [Pi.add_apply, addFun, polyFun, map_add, MvPolynomial.eval_X, if_true,
      if_neg (by decide : (1 : Fin 2) ≠ 0)]
  rw [heq]
  exact proposition_2_84 (pair_isSemialgebraicFunction hf hg)
    (polyFun_isSemialgebraicFunction (X 0 + X 1)) (Set.mapsTo_univ _ _)

/-- Product of semialgebraic functions is semialgebraic: `f · g = (·) ∘ (f, g)`. -/
theorem IsSemialgebraicFunction.mul
    (hf : IsSemialgebraicFunction A f) (hg : IsSemialgebraicFunction A g) :
    IsSemialgebraicFunction A (f * g) := by
  have heq : f * g
      = mulFun ∘ (fun (x : Fin k → R) (j : Fin 2) => if j = 0 then f x 0 else g x 0) := by
    funext x i; rw [Subsingleton.elim i 0]
    show (f x * g x) 0 = mulFun (fun j => if j = 0 then f x 0 else g x 0) 0
    simp only [Pi.mul_apply, mulFun, polyFun, map_mul, MvPolynomial.eval_X, if_true,
      if_neg (by decide : (1 : Fin 2) ≠ 0)]
  rw [heq]
  exact proposition_2_84 (pair_isSemialgebraicFunction hf hg)
    (polyFun_isSemialgebraicFunction (X 0 * X 1)) (Set.mapsTo_univ _ _)

/-- Negation of a semialgebraic function is semialgebraic: `-f = (- ·) ∘ f`. -/
theorem IsSemialgebraicFunction.neg (hf : IsSemialgebraicFunction A f) :
    IsSemialgebraicFunction A (-f) := by
  have heq : -f = negFun ∘ f := by
    funext x i; rw [Subsingleton.elim i 0]
    show (-f x) 0 = negFun (f x) 0
    simp only [Pi.neg_apply, negFun, polyFun, map_neg, MvPolynomial.eval_X]
  rw [heq]
  exact proposition_2_84 hf (polyFun_isSemialgebraicFunction (-(X 0))) (Set.mapsTo_univ _ _)

omit [IsRealClosed R] in
/-- The zero function is semialgebraic (on a semialgebraic domain). -/
theorem isSemialgebraicFunction_zero (hA : IsSemialgebraicSet A) :
    IsSemialgebraicFunction A (0 : (Fin k → R) → (Fin 1 → R)) := by
  have heq : (0 : (Fin k → R) → (Fin 1 → R)) = polyFun (0 : MvPolynomial (Fin k) R) := by
    funext x i; simp [polyFun]
  rw [heq]; exact polyFun_isSemialgebraicFunction_on hA _

omit [IsRealClosed R] in
/-- The constant-one function is semialgebraic (on a semialgebraic domain). -/
theorem isSemialgebraicFunction_one (hA : IsSemialgebraicSet A) :
    IsSemialgebraicFunction A (1 : (Fin k → R) → (Fin 1 → R)) := by
  have heq : (1 : (Fin k → R) → (Fin 1 → R)) = polyFun (1 : MvPolynomial (Fin k) R) := by
    funext x i; simp [polyFun]
  rw [heq]; exact polyFun_isSemialgebraicFunction_on hA _

/-- **BPR Proposition 2.85.** For a semialgebraic set `A ⊆ Rᵏ`, the semialgebraic functions
`A → R` form a ring (a subring of the pointwise function ring). -/
def semialgebraicFunctions (hA : IsSemialgebraicSet A) :
    Subring ((Fin k → R) → (Fin 1 → R)) where
  carrier := {f | IsSemialgebraicFunction A f}
  zero_mem' := isSemialgebraicFunction_zero hA
  one_mem' := isSemialgebraicFunction_one hA
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  neg_mem' hf := hf.neg

end Azurite.BPR
