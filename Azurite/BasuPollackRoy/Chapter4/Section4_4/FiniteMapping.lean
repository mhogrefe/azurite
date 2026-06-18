import Azurite.BasuPollackRoy.Chapter4.Section4_4.Definition_4_73
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots

/-!
# BPR §4.4.2: finite mappings

Let `𝒫 ⊆ K[X₁, …, X_k]` and `𝒬 ⊆ K[X₁, …, X_{k-1}]` be finite sets of polynomials, and `C` a
field extension of `K`. The projection `π : C^k → C^{k-1}` forgetting the distinguished
coordinate is a *finite mapping* from `Zer(𝒫, C^k)` onto `Zer(𝒬, C^{k-1})` if its restriction
to `Zer(𝒫, C^k)` is surjective onto `Zer(𝒬, C^{k-1})` and `𝒫` contains a polynomial quasi-monic
in the distinguished variable.

Following Lemma 4.74, we single out `X₀` (Mathlib's `finSuccEquiv` distinguishes the first
variable), so `π = Fin.tail` forgets the first coordinate and "quasi-monic in `X₀`" means
`IsQuasiMonic (finSuccEquiv K n P)`. Since `P` is quasi-monic, the specialization `P(X₀, y)` is a
nonzero univariate polynomial for each `y`, so every fiber `π⁻¹(y) ∩ Zer(𝒫, C^k)` is finite.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {n : ℕ} {K : Type*} [Field K]

/-- `Zer(𝒫, C^k)`: the common zeros in `C^k` of a finite set `𝒫 ⊆ K[X₁, …, X_k]`, where `C` is a
`K`-algebra. -/
def zerOfFinset (C : Type*) [CommRing C] [Algebra K C] {k : ℕ}
    (Ps : Finset (MvPolynomial (Fin k) K)) : Set (Fin k → C) :=
  {x | ∀ p ∈ Ps, aeval x p = 0}

/-- **BPR Definition (finite mapping).** The projection `π = Fin.tail : C^{n+1} → C^n` forgetting
the first coordinate is a *finite mapping* from `Zer(𝒫, C^{n+1})` onto `Zer(𝒬, C^n)` if its
restriction to `Zer(𝒫, C^{n+1})` is surjective onto `Zer(𝒬, C^n)`, and `𝒫` contains a polynomial
quasi-monic in `X₀`. -/
def IsFiniteMapping (C : Type*) [Field C] [Algebra K C]
    (Ps : Finset (MvPolynomial (Fin (n + 1)) K)) (Qs : Finset (MvPolynomial (Fin n) K)) : Prop :=
  Set.SurjOn (Fin.tail : (Fin (n + 1) → C) → (Fin n → C)) (zerOfFinset C Ps) (zerOfFinset C Qs) ∧
    ∃ P ∈ Ps, IsQuasiMonic (finSuccEquiv K n P)

variable {C : Type*} [Field C] [Algebra K C]

/-- Evaluating `P` at `(t, y)` equals evaluating, at `t`, the univariate polynomial obtained from
`finSuccEquiv K n P` by substituting `y` into the coefficients. -/
private theorem aeval_cons_eq (y : Fin n → C) (t : C) (P : MvPolynomial (Fin (n + 1)) K) :
    aeval (Fin.cons t y) P =
      Polynomial.eval t (Polynomial.map (MvPolynomial.aeval y).toRingHom (finSuccEquiv K n P)) := by
  have key : (MvPolynomial.aeval (Fin.cons t y) :
        MvPolynomial (Fin (n + 1)) K →ₐ[K] C).toRingHom =
      (Polynomial.evalRingHom t).comp ((Polynomial.mapRingHom (MvPolynomial.aeval y).toRingHom).comp
        (finSuccEquiv K n).toAlgHom.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [finSuccEquiv_apply]
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [finSuccEquiv_X_zero]
      · simp [finSuccEquiv_X_succ]
  have := DFunLike.congr_fun key P
  simpa [Polynomial.coe_mapRingHom] using this

/-- **The fibers of a finite mapping are finite.** For every `y`, the fiber `π⁻¹(y) ∩ Zer(𝒫)` is
contained in the (finite) zero set of the nonzero univariate polynomial `P(X₀, y)`, hence is
finite. -/
theorem isFiniteMapping_fiber_finite {Ps : Finset (MvPolynomial (Fin (n + 1)) K)}
    {Qs : Finset (MvPolynomial (Fin n) K)} (h : IsFiniteMapping C Ps Qs) (y : Fin n → C) :
    ((Fin.tail : (Fin (n + 1) → C) → (Fin n → C)) ⁻¹' {y} ∩ zerOfFinset C Ps).Finite := by
  classical
  obtain ⟨P, hPmem, hPqm⟩ := h.2
  obtain ⟨c, hc⟩ := hPqm.2
  have hcne : c ≠ 0 := hPqm.leadingCoeff_const_ne_zero c hc
  set Py : Polynomial C :=
    Polynomial.map (MvPolynomial.aeval y).toRingHom (finSuccEquiv K n P) with hPy
  -- `Py` is nonzero: its coefficient at the leading degree is `algebraMap c ≠ 0`.
  have hPyne : Py ≠ 0 := by
    intro h0
    have hcoeff : Py.coeff (finSuccEquiv K n P).natDegree = algebraMap K C c := by
      rw [hPy, Polynomial.coeff_map, ← Polynomial.leadingCoeff, hc]
      simp
    rw [h0, Polynomial.coeff_zero] at hcoeff
    exact hcne ((map_eq_zero_iff _ (algebraMap K C).injective).mp hcoeff.symm)
  -- The fiber injects (via `x ↦ x 0`) into the finite root set of `Py`.
  refine Set.Finite.of_finite_image (f := fun x => x 0) ?_ ?_
  · refine Set.Finite.subset (Polynomial.finite_setOf_isRoot hPyne) ?_
    rintro _ ⟨x, ⟨hxtail, hxzer⟩, rfl⟩
    have hxy : Fin.cons (x 0) y = x := by
      rw [← Set.mem_singleton_iff.mp (Set.mem_preimage.mp hxtail)]
      exact Fin.cons_self_tail x
    show Py.eval (x 0) = 0
    rw [hPy, ← aeval_cons_eq y (x 0) P, hxy]
    exact hxzer P hPmem
  · rintro x ⟨hxtail, -⟩ x' ⟨hx'tail, -⟩ hxx
    have hx : Fin.cons (x 0) y = x := by
      rw [← Set.mem_singleton_iff.mp (Set.mem_preimage.mp hxtail)]; exact Fin.cons_self_tail x
    have hx' : Fin.cons (x' 0) y = x' := by
      rw [← Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx'tail)]; exact Fin.cons_self_tail x'
    have hxx' : x 0 = x' 0 := hxx
    rw [← hx, ← hx', hxx']

end Azurite.BPR.Chapter4
