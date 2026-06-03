import Azurite.BasuPollackRoy.Chapter2.Section2_6.Lemma_2_97
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Div

/-! # BPR §2.6 — degrees of the characteristic polynomial

For an edge `E = [A, B]` whose endpoints are column points (`A.1 < B.1`), the characteristic
polynomial `Q = Q(P, E, X)` has `natDegree = B.1` (top column `B.1` has nonzero initial
coefficient) and `natTrailingDegree = A.1` (bottom column `A.1`). Hence `Q` is nonzero and the
multiplicity of any root is at most `B.1`. This bounds the multiplicity of the chosen root by the
right endpoint of the edge — the input to "multiplicities are non-increasing" in the Puiseux
construction (when the edge is selected over `[0, rᵢ]`). -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- The right endpoint contributes a nonzero top coefficient, so `Q ≠ 0`. -/
theorem charPoly_ne_zero {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} (hABlt : A.1 < B.1)
    (hcolB : puiseuxOrder R (P.coeff B.1) = (B.2 : WithTop ℚ)) : charPoly P A B ≠ 0 := by
  classical
  have hBmem : B.1 ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_of_lt hABlt, le_refl _⟩,
      colOnLine_right hABlt.ne hcolB⟩
  have hBne : (charPoly P A B).coeff B.1 ≠ 0 := by
    rw [charPoly_coeff, if_pos hBmem]
    exact initCoeff_ne_zero_of_colOnLine (colOnLine_right hABlt.ne hcolB)
  exact fun h => hBne (by rw [h, coeff_zero])

/-- **`Q` has degree `B.1`.** -/
theorem charPoly_natDegree_eq {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} (hABlt : A.1 < B.1)
    (hcolB : puiseuxOrder R (P.coeff B.1) = (B.2 : WithTop ℚ)) :
    (charPoly P A B).natDegree = B.1 := by
  classical
  have hBmem : B.1 ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_of_lt hABlt, le_refl _⟩,
      colOnLine_right hABlt.ne hcolB⟩
  have hBne : (charPoly P A B).coeff B.1 ≠ 0 := by
    rw [charPoly_coeff, if_pos hBmem]
    exact initCoeff_ne_zero_of_colOnLine (colOnLine_right hABlt.ne hcolB)
  exact le_antisymm (charPoly_natDegree_le P A B) (le_natDegree_of_ne_zero hBne)

/-- **`Q` has trailing degree `A.1`.** -/
theorem charPoly_natTrailingDegree_eq {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ}
    (hABlt : A.1 < B.1) (hcolA : puiseuxOrder R (P.coeff A.1) = (A.2 : WithTop ℚ))
    (hcolB : puiseuxOrder R (P.coeff B.1) = (B.2 : WithTop ℚ)) :
    (charPoly P A B).natTrailingDegree = A.1 := by
  classical
  have hAmem : A.1 ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl _, le_of_lt hABlt⟩, colOnLine_left hcolA⟩
  have hAne : (charPoly P A B).coeff A.1 ≠ 0 := by
    rw [charPoly_coeff, if_pos hAmem]
    exact initCoeff_ne_zero_of_colOnLine (colOnLine_left (B := B) hcolA)
  refine le_antisymm (natTrailingDegree_le_of_ne_zero hAne)
    (le_natTrailingDegree (charPoly_ne_zero hABlt hcolB) ?_)
  intro m hm
  rw [charPoly_coeff, if_neg]
  intro hmem
  exact absurd (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).1 (by omega)

/-- **The multiplicity of a root of `Q` is at most `B.1`.** When the edge lies over `[0, rᵢ]`
(so `B.1 ≤ rᵢ`), this gives `r_{i+1} ≤ rᵢ`: multiplicities are non-increasing. -/
theorem charPoly_rootMultiplicity_le {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ}
    (hABlt : A.1 < B.1) (hcolB : puiseuxOrder R (P.coeff B.1) = (B.2 : WithTop ℚ)) (x : R) :
    (charPoly P A B).rootMultiplicity x ≤ B.1 := by
  have hle := natDegree_le_of_dvd (pow_rootMultiplicity_dvd (charPoly P A B) x)
    (charPoly_ne_zero hABlt hcolB)
  rwa [natDegree_pow, natDegree_X_sub_C, mul_one, charPoly_natDegree_eq hABlt hcolB] at hle

end Azurite.BPR
