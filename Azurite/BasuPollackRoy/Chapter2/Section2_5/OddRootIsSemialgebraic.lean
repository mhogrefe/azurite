import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunction
import Azurite.BasuPollackRoy.Chapter2.Section2_3.FiberFormula

/-! # The odd root function is semialgebraic

(Not in BPR.) For `k` odd (hence `≥ 1`), the map `y ↦ y^k` is a bijection of a real closed
field `R` (strictly monotone, and surjective by the intermediate value property), so the
`k`-th root `x ↦ x^{1/k}` is a well-defined function `R → R`. Its graph
`{(x, y) | y^k = x}` is the zero set of `X_2^k - X_1`, hence algebraic, so the `k`-th root
is semialgebraic.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- For `k` odd, `y ↦ y^k` is surjective on a real closed field: `Y^k - x` changes sign
between `-M` and `M` for `M = |x| + 1`, so the intermediate value property gives a root. -/
theorem oddPow_surjective {k : ℕ} (hodd : Odd k) :
    Function.Surjective (fun y : R => y ^ k) := by
  intro x
  have hk : k ≠ 0 := hodd.pos.ne'
  set M : R := |x| + 1 with hM
  have habs : (0 : R) ≤ |x| := abs_nonneg x
  have hM1 : (1 : R) ≤ M := by rw [hM]; linarith
  have hMk : M ≤ M ^ k := le_self_pow₀ hM1 hk
  have hxM : x < M := by rw [hM]; have := le_abs_self x; linarith
  have hnxM : -M < x := by rw [hM]; have := neg_abs_le x; linarith
  set P : Polynomial R := Polynomial.X ^ k - Polynomial.C x with hP
  have hPeval : ∀ t : R, Polynomial.eval t P = t ^ k - x := by
    intro t; rw [hP]; simp
  have hPM : 0 < Polynomial.eval M P := by rw [hPeval]; linarith
  have hPnM : Polynomial.eval (-M) P < 0 := by
    rw [hPeval, hodd.neg_pow]; linarith
  obtain ⟨y, _, _, hy⟩ :=
    hasIVP_of_isRealClosed P (-M) M (by linarith) (mul_neg_of_neg_of_pos hPnM hPM)
  rw [hPeval] at hy
  exact ⟨y, by simpa using sub_eq_zero.mp hy⟩

/-- The bijection `y ↦ y^k` of `R` (`k` odd). -/
noncomputable def oddPowEquiv {k : ℕ} (hodd : Odd k) : R ≃ R :=
  Equiv.ofBijective (fun y : R => y ^ k)
    ⟨(Odd.strictMono_pow hodd).injective, oddPow_surjective hodd⟩

/-- The `k`-th root function `R → R` (`k` odd), valued in `Fin 1 → R`. -/
noncomputable def oddRoot {k : ℕ} (hodd : Odd k) : (Fin 1 → R) → (Fin 1 → R) :=
  fun x _ => (oddPowEquiv hodd).symm (x 0)

/-- **The odd-root function `x ↦ x^{1/k}` is semialgebraic.** Its graph is the zero set of
`X_2^k - X_1`. -/
theorem oddRoot_isSemialgebraicFunction {k : ℕ} (hodd : Odd k) :
    IsSemialgebraicFunction (Set.univ : Set (Fin 1 → R)) (oddRoot hodd) := by
  set Q : MvPolynomial (Fin 2) R := MvPolynomial.X 1 ^ k - MvPolynomial.X 0 with hQ
  have hQeval : ∀ z : Fin 2 → R, MvPolynomial.eval z Q = z 1 ^ k - z 0 := by
    intro z; rw [hQ]; simp
  have hcidx : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := Fin.ext rfl
  have hnidx : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := Fin.ext rfl
  have hgraph : funGraph (Set.univ : Set (Fin 1 → R)) (oddRoot hodd)
      = {z : Fin 2 → R | MvPolynomial.eval z Q = 0} := by
    ext z
    rw [mem_funGraph]
    simp only [Set.mem_univ, true_and, Set.mem_setOf_eq, hQeval, sub_eq_zero]
    have hkey : (z ∘ Fin.natAdd 1 = oddRoot hodd (z ∘ Fin.castAdd 1)) ↔
        z 1 = (oddPowEquiv hodd).symm (z 0) := by
      constructor
      · intro h
        have h0 := congrFun h 0
        simpa [oddRoot, Function.comp_apply, hcidx, hnidx] using h0
      · intro h
        funext i; rw [Subsingleton.elim i 0]
        simpa [oddRoot, Function.comp_apply, hcidx, hnidx] using h
    rw [hkey, Equiv.eq_symm_apply, oddPowEquiv]
    exact Iff.rfl
  show IsSemialgebraicSet (funGraph (Set.univ : Set (Fin 1 → R)) (oddRoot hodd))
  rw [hgraph]
  exact IsSemialgebraicSet.eqZero Q

end Azurite.BPR
