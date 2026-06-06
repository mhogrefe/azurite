import Azurite.BasuPollackRoy.Chapter3.Section3_2.ConvexExamples
import Azurite.BasuPollackRoy.Chapter3.Section3_1.SemialgebraicHomeomorphism

/-! # BPR §3.2 — products of convex sets

The Cartesian product of two convex sets is convex. As consequences, `R^n` (a product of `R`'s) and
the open cube `(0,1)^k` (a product of open intervals) are convex. -/

namespace Azurite.BPR

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
/-- **The Cartesian product of two convex sets is convex.** -/
theorem isConvex_setProd {C : Set (Fin k → R)} {D : Set (Fin ℓ → R)}
    (hC : IsConvex C) (hD : IsConvex D) : IsConvex (setProd C D) := by
  intro x hx y hy l hl
  obtain ⟨hxC, hxD⟩ := hx
  obtain ⟨hyC, hyD⟩ := hy
  refine ⟨?_, ?_⟩
  · have h : ((1 - l) • x + l • y) ∘ Fin.castAdd ℓ
        = (1 - l) • (x ∘ Fin.castAdd ℓ) + l • (y ∘ Fin.castAdd ℓ) := by
      funext j; simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply]
    rw [h]; exact hC hxC hyC l hl
  · have h : ((1 - l) • x + l • y) ∘ Fin.natAdd k
        = (1 - l) • (x ∘ Fin.natAdd k) + l • (y ∘ Fin.natAdd k) := by
      funext j; simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply]
    rw [h]; exact hD hxD hyD l hl

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] in
/-- `R^{k+ℓ}` is the product `R^k × R^ℓ`. -/
theorem setProd_univ_univ :
    setProd (Set.univ : Set (Fin k → R)) (Set.univ : Set (Fin ℓ → R)) = Set.univ := by
  ext z; simp [setProd]

/-- **`R^n` is convex** (as a product of full spaces). -/
theorem isConvex_univ_prod : IsConvex (Set.univ : Set (Fin (k + ℓ) → R)) := by
  rw [← setProd_univ_univ]; exact isConvex_setProd isConvex_univ isConvex_univ

/-- The **open cube** `(0,1)^k ⊆ R^k`. -/
def openCube (k : ℕ) (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    Set (Fin k → R) :=
  {v | ∀ i, v i ∈ Set.Ioo (0 : R) 1}

/-- **The open cube `(0,1)^k` is convex.** -/
theorem isConvex_openCube : IsConvex (openCube k R) := by
  intro x hx y hy l hl
  simp only [openCube, Set.mem_setOf_eq] at hx hy ⊢
  intro i
  have hconv : Convex R (Set.Ioo (0 : R) 1) := convex_iff_ordConnected.mpr Set.ordConnected_Ioo
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  exact hconv (hx i) (hy i) (by linarith [hl.2]) hl.1 (by ring)

end Azurite.BPR
