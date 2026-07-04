import Azurite.BasuPollackRoy.Chapter10.Section10_1.Proposition_10_8
import Azurite.BasuPollackRoy.Chapter10.Section10_1.Proposition_10_9

/-!
# BPR Proposition 10.11: measure and length bounds for integer factors

For `P, Q ∈ ℤ[X]` with `Q ∣ P` and `P ≠ 0` (viewed in `C[X]` through the
integer cast):

* `proposition_10_11_measure` — `Mea(Q) ≤ Mea(P)`: the leading coefficient of
  `Q` divides that of `P`, so `|lc Q| ≤ |lc P|` (a nonzero integer cofactor
  has absolute value at least `1`), and every root of `Q` is a root of `P`
  (as multisets, `Polynomial.roots.le_of_dvd`), so the `max`-product only
  grows (`prod_max_mono`);
* `proposition_10_11_length` — `Len(Q) ≤ 2^q·∥P∥` where `q = deg Q`: chain
  `Len(Q) ≤ 2^q·Mea(Q)` (Proposition 10.8), `Mea(Q) ≤ Mea(P)` (first part),
  `Mea(P) ≤ ∥P∥` (Proposition 10.9, Landau).

That both bounds depend only on `P`'s data — not on which factor `Q` is —
is what makes them usable to bound the coefficients of any potential factor.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR Proposition 10.11, first part.** For `P, Q ∈ ℤ[X]` with `Q ∣ P`
and `P ≠ 0`, `Mea(Q) ≤ Mea(P)`. -/
theorem proposition_10_11_measure {P Q : ℤ[X]} (hP : P ≠ 0) (hQP : Q ∣ P) :
    polyMeasure (Q.map (Int.castRingHom (Ri R)))
      ≤ polyMeasure (P.map (Int.castRingHom (Ri R))) := by
  haveI : CharZero (Ri R) :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective R (Ri R))
  have hcast : Function.Injective (Int.castRingHom (Ri R)) := fun a b h => by simpa using h
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hP (zero_dvd_iff.mp hQP)
  have hP' : P.map (Int.castRingHom (Ri R)) ≠ 0 := (Polynomial.map_ne_zero_iff hcast).mpr hP
  obtain ⟨S, hPQS⟩ := hQP
  have hS0 : S ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hPQS
    exact hP hPQS
  -- `lc Q ∣ lc P` in ℤ gives `|lc Q| ≤ |lc P|`
  have hlcZ : |Q.leadingCoeff| ≤ |P.leadingCoeff| := by
    rw [hPQS, Polynomial.leadingCoeff_mul, abs_mul]
    calc |Q.leadingCoeff| = |Q.leadingCoeff| * 1 := (mul_one _).symm
      _ ≤ |Q.leadingCoeff| * |S.leadingCoeff| :=
          mul_le_mul_of_nonneg_left
            (Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hS0)) (abs_nonneg _)
  have hlcmap : ∀ T : ℤ[X], (T.map (Int.castRingHom (Ri R))).leadingCoeff
      = ((T.leadingCoeff : ℤ) : Ri R) := by
    intro T
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_map_eq_of_injective hcast,
      Polynomial.coeff_map]
    rfl
  have hlc : Ri.abs (Q.map (Int.castRingHom (Ri R))).leadingCoeff
      ≤ Ri.abs (P.map (Int.castRingHom (Ri R))).leadingCoeff := by
    rw [hlcmap, hlcmap, Ri.abs_intCast, Ri.abs_intCast]
    exact_mod_cast hlcZ
  -- every root of `Q` is a root of `P`, with multiplicity
  have hroots : (Q.map (Int.castRingHom (Ri R))).roots
      ≤ (P.map (Int.castRingHom (Ri R))).roots :=
    Polynomial.roots.le_of_dvd hP' (Polynomial.map_dvd _ ⟨S, hPQS⟩)
  rw [polyMeasure, polyMeasure]
  apply mul_le_mul hlc (prod_max_mono hroots)
    (le_trans zero_le_one (one_le_prod_max _)) (Ri.abs_nonneg' _)

/-- **BPR Proposition 10.11, second part.** For `P, Q ∈ ℤ[X]` with `Q ∣ P`
and `P ≠ 0`, `Len(Q) ≤ 2^q·∥P∥` where `q = deg Q`. Follows from
Propositions 10.8 and 10.9 through the first part. -/
theorem proposition_10_11_length {P Q : ℤ[X]} (hP : P ≠ 0) (hQP : Q ∣ P) :
    polyLength (Q.map (Int.castRingHom (Ri R)))
      ≤ 2 ^ Q.natDegree * polyNorm (P.map (Int.castRingHom (Ri R))) := by
  haveI : CharZero (Ri R) :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective R (Ri R))
  have hcast : Function.Injective (Int.castRingHom (Ri R)) := fun a b h => by simpa using h
  have hdeg : (Q.map (Int.castRingHom (Ri R))).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hcast Q
  calc polyLength (Q.map (Int.castRingHom (Ri R)))
      ≤ 2 ^ (Q.map (Int.castRingHom (Ri R))).natDegree
          * polyMeasure (Q.map (Int.castRingHom (Ri R))) :=
        proposition_10_8 _
    _ = 2 ^ Q.natDegree * polyMeasure (Q.map (Int.castRingHom (Ri R))) := by rw [hdeg]
    _ ≤ 2 ^ Q.natDegree * polyMeasure (P.map (Int.castRingHom (Ri R))) :=
        mul_le_mul_of_nonneg_left (proposition_10_11_measure hP hQP) (by positivity)
    _ ≤ 2 ^ Q.natDegree * polyNorm (P.map (Int.castRingHom (Ri R))) :=
        mul_le_mul_of_nonneg_left (proposition_10_9 _) (by positivity)

end Azurite.BPR
