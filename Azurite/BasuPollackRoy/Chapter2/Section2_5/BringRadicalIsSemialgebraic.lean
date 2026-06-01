import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunction
import Azurite.BasuPollackRoy.Chapter2.Section2_3.FiberFormula

/-! # The Bring radical is semialgebraic

(Not in BPR.) The *Bring radical* (ultraradical) `BR(a)` is the unique real root of the
quintic `y^5 + y + a = 0`. Equivalently it is the inverse of the strictly decreasing bijection
`y ↦ -(y^5 + y)` of a real closed field (strict monotone, and surjective by the intermediate
value property). Its graph `{(a, y) | y^5 + y + a = 0}` is the zero set of `X_2^5 + X_2 + X_1`,
hence algebraic, so the Bring radical is semialgebraic.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The map `y ↦ -(y^5 + y)` is a bijection of a real closed field. -/
theorem bringMap_bijective : Function.Bijective (fun y : R => -(y ^ 5 + y)) := by
  refine ⟨?_, ?_⟩
  · have hmono : StrictMono (fun y : R => y ^ 5 + y) := fun a b hab =>
      add_lt_add ((Odd.strictMono_pow (by decide : Odd 5)) hab) hab
    intro a b h
    exact hmono.injective (neg_injective h)
  · intro a
    set M : R := |a| + 1 with hM
    have habs : (0 : R) ≤ |a| := abs_nonneg a
    have hM1 : (1 : R) ≤ M := by rw [hM]; linarith
    have hMk : M ≤ M ^ 5 := le_self_pow₀ hM1 (by norm_num)
    have haM : a < M := by rw [hM]; have := le_abs_self a; linarith
    have hnaM : -M < a := by rw [hM]; have := neg_abs_le a; linarith
    set P : Polynomial R := Polynomial.X ^ 5 + Polynomial.X + Polynomial.C a with hP
    have hPeval : ∀ t : R, Polynomial.eval t P = t ^ 5 + t + a := by intro t; rw [hP]; simp
    have hPM : 0 < Polynomial.eval M P := by rw [hPeval]; linarith
    have hPnM : Polynomial.eval (-M) P < 0 := by
      rw [hPeval, (by decide : Odd 5).neg_pow]; linarith
    obtain ⟨y, _, _, hy⟩ :=
      hasIVP_of_isRealClosed P (-M) M (by linarith) (mul_neg_of_neg_of_pos hPnM hPM)
    rw [hPeval] at hy
    exact ⟨y, by show -(y ^ 5 + y) = a; linarith⟩

/-- The bijection `y ↦ -(y^5 + y)` of `R`. -/
noncomputable def bringEquiv : R ≃ R := Equiv.ofBijective _ bringMap_bijective

/-- The **Bring radical** `BR : R → R`, the inverse of `y ↦ -(y^5 + y)`, valued in `Fin 1 → R`. -/
noncomputable def bringRadical : (Fin 1 → R) → (Fin 1 → R) :=
  fun a _ => (bringEquiv).symm (a 0)

/-- **The Bring radical is semialgebraic.** Its graph is the zero set of `X_2^5 + X_2 + X_1`. -/
theorem bringRadical_isSemialgebraicFunction :
    IsSemialgebraicFunction (Set.univ : Set (Fin 1 → R)) (bringRadical (R := R)) := by
  set Q : MvPolynomial (Fin 2) R := X 1 ^ 5 + X 1 + X 0 with hQ
  have hQeval : ∀ z : Fin 2 → R, MvPolynomial.eval z Q = z 1 ^ 5 + z 1 + z 0 := by
    intro z; rw [hQ]; simp
  have hcidx : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := Fin.ext rfl
  have hnidx : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := Fin.ext rfl
  have hgraph : funGraph (Set.univ : Set (Fin 1 → R)) bringRadical
      = {z : Fin 2 → R | MvPolynomial.eval z Q = 0} := by
    ext z
    rw [mem_funGraph]
    simp only [Set.mem_univ, true_and, Set.mem_setOf_eq, hQeval]
    have hkey : (z ∘ Fin.natAdd 1 = bringRadical (z ∘ Fin.castAdd 1)) ↔
        z 1 = (bringEquiv).symm (z 0) := by
      constructor
      · intro h
        simpa [bringRadical, Function.comp_apply, hcidx, hnidx] using congrFun h 0
      · intro h
        funext i; rw [Subsingleton.elim i 0]
        simpa [bringRadical, Function.comp_apply, hcidx, hnidx] using h
    rw [hkey, Equiv.eq_symm_apply]
    simp only [bringEquiv, Equiv.ofBijective_apply]
    constructor <;> intro h <;> linarith
  show IsSemialgebraicSet (funGraph (Set.univ : Set (Fin 1 → R)) bringRadical)
  rw [hgraph]
  exact IsSemialgebraicSet.eqZero Q

end Azurite.BPR
