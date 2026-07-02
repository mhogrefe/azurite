import Azurite.AzPolynomial.Equiv.CauchyIndexSubresMap
import Azurite.AzPolynomial.Equiv.CauchyIndex
import Azurite.AzPolynomial.Equiv.TarskiQuery
import Azurite.AzPolynomial.Equiv.QuoRem
import Azurite.AzPolynomial.SRemS
import Azurite.AzRat.Equiv.RingEquiv
import Azurite.AzRat.Equiv.Order

/-!
# Transport of `cauchyIndexOnSRem` / `tarskiQueryOnSRem` across an order embedding

The signed-*remainder* Cauchy index and Tarski query use field division, so they
run over a field (e.g. `AzRat`), not over `AzInt` directly — the `AzInt` entry
points `cauchyIndexOnIntSRem` / `tarskiQueryOnIntSRem` first map `AzInt → AzRat`. This
file transports the whole-line computation across an order-preserving field
homomorphism `g : K →+* R` into a real closed field `R`:

* the signed remainder sequence `sRemSList` commutes with `g` (`sRemSList_map`,
  via Mathlib's `%`-commutation `Polynomial.map_mod`);
* `varAt` at `±∞` is a sign-variation count of leading coefficients, invariant
  under the sign-preserving `g` (`Var_map` + `evalPolyExt_map_*`).

Hence `cauchyIndexOnSRem Q P (-∞) (+∞) = Ind` over `R` even when the coefficients only
live in a smaller ordered field `K` (`cauchyIndexOnSRem_negInf_posInf_map_eq_BPR`,
`tarskiQueryOnSRem_negInf_posInf_map_eq_BPR`), specialized to the `AzInt`
entry points (`cauchyIndexOnIntSRem` / `tarskiQueryOnIntSRem`).
-/

open Polynomial

namespace Azurite.AzPolynomial

open Azurite.BPR (ExtendedPoint)

section Transport
variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [DecidableEq K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [DecidableEq L]

omit [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L] [IsStrictOrderedRing L] in
/-- The signed remainder `.rem` commutes with a field homomorphism. -/
theorem rem_map (g : K →+* L) (P Q : AzPolynomial K) :
    (P.rem Q).map g = (P.map g).rem (Q.map g) := by
  apply toPoly_inj.mp
  rcases eq_or_ne (AzPolynomial.toPoly Q) 0 with hQ0 | hQm
  · have hQ : Q = 0 := toPoly_inj.mp (by rw [hQ0, toPoly_zero])
    subst hQ
    rw [toPoly_map, (map_eq_zero_iff_of_injective g g.injective 0).mpr rfl,
      show P.rem 0 = P by simp [rem, quoRem],
      show (P.map g).rem 0 = P.map g by simp [rem, quoRem], toPoly_map]
  · have hQfm : AzPolynomial.toPoly (Q.map g) ≠ 0 := by
      rw [toPoly_map]; exact (Polynomial.map_ne_zero_iff g.injective).mpr hQm
    rw [toPoly_map, toPoly_rem P Q hQm, toPoly_rem (P.map g) (Q.map g) hQfm, toPoly_map, toPoly_map,
      Polynomial.map_mod]

omit [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L] [IsStrictOrderedRing L] in
/-- One signed-remainder step commutes with a field homomorphism. -/
theorem sRemSStep_map (g : K →+* L) (a b : AzPolynomial K) :
    sRemSStep (a.map g) (b.map g) = (sRemSStep a b).map g := by
  have hmz : (0 : AzPolynomial K).map g = 0 := (map_eq_zero_iff_of_injective g g.injective 0).mpr rfl
  by_cases hb : b = 0
  · subst hb; simp [sRemSStep, hmz]
  · rw [sRemSStep, sRemSStep,
      if_neg (fun h => hb ((map_eq_zero_iff_of_injective g g.injective b).mp h)),
      if_neg hb, map_neg', rem_map]

omit [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L] [IsStrictOrderedRing L] in
/-- The signed remainder builder commutes with a field homomorphism. -/
theorem sRemSBuild_map (g : K →+* L) (n : ℕ) (a b : AzPolynomial K) :
    sRemSBuild n (a.map g) (b.map g) = (sRemSBuild n a b).map (·.map g) := by
  induction n generalizing a b with
  | zero => simp [sRemSBuild]
  | succ m ih => rw [sRemSBuild, sRemSBuild, List.map_cons, sRemSStep_map, ih]

omit [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L] [IsStrictOrderedRing L] in
/-- The signed remainder sequence list commutes with a field homomorphism. -/
theorem sRemSList_map (g : K →+* L) (P Q : AzPolynomial K) (n : ℕ) :
    sRemSList (P.map g) (Q.map g) n = (sRemSList P Q n).map (·.map g) :=
  sRemSBuild_map g n P Q

omit [LinearOrder K] [IsStrictOrderedRing K] [DecidableEq K] in
/-- The coefficient array is empty iff the polynomial is zero. -/
theorem coeffs_size_eq_zero_iff (S : AzPolynomial K) : S.coeffs.size = 0 ↔ S = 0 :=
  ⟨fun h => AzPolynomial.ext (by rw [Array.size_eq_zero_iff.mp h]; rfl), fun h => by rw [h]; rfl⟩

omit [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L] [IsStrictOrderedRing L] in
theorem coeffs_size_map (g : K →+* L) (hg : Function.Injective g) (P : AzPolynomial K) :
    (P.map g).coeffs.size = P.coeffs.size := by
  by_cases hP : P = 0
  · subst hP; simp [(map_eq_zero_iff_of_injective g hg 0).mpr rfl]
  · have h1 := natDegree_map_of_injective g hg P
    unfold AzPolynomial.natDegree at h1
    have hs1 : 1 ≤ P.coeffs.size :=
      Nat.one_le_iff_ne_zero.mpr (fun h => hP ((coeffs_size_eq_zero_iff P).mp h))
    have hs2 : 1 ≤ (P.map g).coeffs.size := Nat.one_le_iff_ne_zero.mpr
      (fun h => hP ((map_eq_zero_iff_of_injective g hg P).mp ((coeffs_size_eq_zero_iff (P.map g)).mp h)))
    omega

omit [IsStrictOrderedRing K] [DecidableEq K] [IsStrictOrderedRing L] [DecidableEq L] in
/-- `varNonzero` (raw sign-change count) is invariant under a strictly monotone hom. -/
theorem varNonzero_map (g : K →+* L) (hg : StrictMono g) : ∀ l : List K,
    Azurite.BPR.varNonzero (l.map g) = Azurite.BPR.varNonzero l
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    have hlt : (g a * g b < 0) ↔ (a * b < 0) := by rw [← map_mul, ← map_zero g]; exact hg.lt_iff_lt
    rw [List.map_cons, List.map_cons, Azurite.BPR.varNonzero_cons_cons,
      Azurite.BPR.varNonzero_cons_cons, ← List.map_cons, varNonzero_map g hg (b :: rest)]
    congr 1
    exact if_congr hlt rfl rfl

omit [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
/-- `Var` (sign-variation count) is invariant under a strictly monotone hom. -/
theorem Var_map (g : K →+* L) (hg : StrictMono g) (l : List K) :
    Azurite.BPR.Var (l.map g) = Azurite.BPR.Var l := by
  unfold Azurite.BPR.Var
  have hfilter : (l.map g).filter (· ≠ 0) = (l.filter (· ≠ 0)).map g := by
    rw [List.filter_map]; congr 1
    apply List.filter_congr; intro x _
    simp only [Function.comp_apply, ne_eq, ← map_zero g, hg.injective.eq_iff]
  rw [hfilter, varNonzero_map g hg]

omit [LinearOrder K] [IsStrictOrderedRing K] [DecidableEq K] [LinearOrder L] [IsStrictOrderedRing L] in
/-- `evalPolyExt` at `+∞` (the leading coefficient) commutes with an injective hom. -/
theorem evalPolyExt_map_posInf (g : K →+* L) (hg : Function.Injective g) (P : AzPolynomial K) :
    evalPolyExt (P.map g) .posInf = g (evalPolyExt P .posInf) := by
  simp only [evalPolyExt, leadingCoeff_map_of_injective g hg]

omit [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L] [IsStrictOrderedRing L] in
/-- `evalPolyExt` at `−∞` (`±` leading coefficient by parity) commutes with an injective hom. -/
theorem evalPolyExt_map_negInf (g : K →+* L) (hg : Function.Injective g) (P : AzPolynomial K) :
    evalPolyExt (P.map g) .negInf = g (evalPolyExt P .negInf) := by
  simp only [evalPolyExt, coeffs_size_map g hg, leadingCoeff_map_of_injective g hg]
  split_ifs <;> simp [map_neg]

omit [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
/-- `varAt` at an extended point transported by a strictly monotone hom, provided the
endpoint evaluations commute (holds at `±∞`). -/
theorem varAt_map (g : K →+* L) (hg : StrictMono g) (L' : List (AzPolynomial K))
    (xL : ExtendedPoint L) (xK : ExtendedPoint K)
    (hx : ∀ P : AzPolynomial K, evalPolyExt (P.map g) xL = g (evalPolyExt P xK)) :
    varAt (L'.map (·.map g)) xL = varAt L' xK := by
  unfold varAt
  rw [List.map_map, ← Var_map g hg (L'.map (fun P => evalPolyExt P xK)), List.map_map]
  congr 1
  apply List.map_congr_left
  intro P _
  exact hx P

omit [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
/-- **Whole-line transport of `cauchyIndexOnSRem`.** The signed-remainder Cauchy index is
unchanged when the coefficients are pushed along a strictly monotone field hom. -/
theorem cauchyIndexOnSRem_map_negInf_posInf (g : K →+* L) (hg : StrictMono g) (Q P : AzPolynomial K) :
    cauchyIndexOnSRem (Q.map g) (P.map g) .negInf .posInf = cauchyIndexOnSRem Q P .negInf .posInf := by
  show (varAt (sRemSList (P.map g) (Q.map g) ((Q.map g).coeffs.size + 2)) .negInf : ℤ)
      - (varAt (sRemSList (P.map g) (Q.map g) ((Q.map g).coeffs.size + 2)) .posInf : ℤ)
    = (varAt (sRemSList P Q (Q.coeffs.size + 2)) .negInf : ℤ)
      - (varAt (sRemSList P Q (Q.coeffs.size + 2)) .posInf : ℤ)
  rw [coeffs_size_map g hg.injective Q, sRemSList_map g P Q (Q.coeffs.size + 2),
    varAt_map g hg _ .negInf .negInf (evalPolyExt_map_negInf g hg.injective),
    varAt_map g hg _ .posInf .posInf (evalPolyExt_map_posInf g hg.injective)]

/-- **Whole-line transport of `tarskiQueryOnSRem`.** -/
theorem tarskiQueryOnSRem_map_negInf_posInf (g : K →+* L) (hg : StrictMono g) (Q P : AzPolynomial K) :
    tarskiQueryOnSRem (Q.map g) (P.map g) .negInf .posInf = tarskiQueryOnSRem Q P .negInf .posInf := by
  show (varAt (sRemSList (P.map g) ((P.map g).derivative * Q.map g)
        (((P.map g).derivative * Q.map g).coeffs.size + 2)) .negInf : ℤ)
      - (varAt (sRemSList (P.map g) ((P.map g).derivative * Q.map g)
        (((P.map g).derivative * Q.map g).coeffs.size + 2)) .posInf : ℤ)
    = (varAt (sRemSList P (P.derivative * Q) ((P.derivative * Q).coeffs.size + 2)) .negInf : ℤ)
      - (varAt (sRemSList P (P.derivative * Q) ((P.derivative * Q).coeffs.size + 2)) .posInf : ℤ)
  rw [show (P.map g).derivative * Q.map g = (P.derivative * Q).map g from by
      rw [map_mul', map_derivative'],
    coeffs_size_map g hg.injective, sRemSList_map g P (P.derivative * Q) _,
    varAt_map g hg _ .negInf .negInf (evalPolyExt_map_negInf g hg.injective),
    varAt_map g hg _ .posInf .posInf (evalPolyExt_map_posInf g hg.injective)]

variable [IsRealClosed L]

omit [IsStrictOrderedRing K] in
/-- **Correctness of `cauchyIndexOnSRem` over a subfield.** For coefficients in an ordered
field `K`, mapped by a strictly monotone hom `g` into a real closed field `L`, the
whole-line signed-remainder Cauchy index equals `Ind` of the pushed polynomials. -/
theorem cauchyIndexOnSRem_negInf_posInf_map_eq_BPR (g : K →+* L) (hg : StrictMono g)
    (Q P : AzPolynomial K) :
    cauchyIndexOnSRem Q P .negInf .posInf
      = Azurite.BPR.cauchyIndex ((AzPolynomial.toPoly Q).map g) ((AzPolynomial.toPoly P).map g) := by
  rw [← cauchyIndexOnSRem_map_negInf_posInf g hg, cauchyIndexOnSRem_negInf_posInf_eq_BPR,
    toPoly_map, toPoly_map]

/-- **Correctness of `tarskiQueryOnSRem` over a subfield.** -/
theorem tarskiQueryOnSRem_negInf_posInf_map_eq_BPR (g : K →+* L) (hg : StrictMono g)
    (Q P : AzPolynomial K) :
    tarskiQueryOnSRem Q P .negInf .posInf
      = Azurite.BPR.tarskiQuery ((AzPolynomial.toPoly Q).map g) ((AzPolynomial.toPoly P).map g) := by
  rw [← tarskiQueryOnSRem_map_negInf_posInf g hg, tarskiQueryOnSRem_negInf_posInf_eq_BPR,
    toPoly_map, toPoly_map]

end Transport

/-! ### Specialization to the `AzInt` entry points

`cauchyIndexOnIntSRem` / `tarskiQueryOnIntSRem` compute over `AzRat` (after
`mapAzIntToAzRat`), so their whole-line correctness is the general transport at
`K = AzRat` with the order embedding `AzRat → ℚ → R`. The statements are phrased
over `(toPoly ·).map (AzInt → ℤ → R)` — the same right-hand side shape as the
subresultant corollaries `cauchyIndex_azInt_eq_BPR` /
`tarskiQuery_azInt_eq_BPR` — via the bridge
`toPoly_mapAzIntToAzRat_map`. -/

section Int

/-- Coefficientwise, `mapAzIntToAzRat` is `AzInt.toAzRat`. -/
theorem coeff_mapAzIntToAzRat (Q : AzPolynomial AzInt) (n : ℕ) :
    (mapAzIntToAzRat Q).coeff n = (Q.coeff n).toAzRat := by
  have h0 : (0 : AzInt).toAzRat = 0 := AzRat.toRat_injective (by
    rw [AzRat.toRat_toAzRat_int, AzInt.toInt_zero, AzRat.toRat_zero, Int.cast_zero])
  show ((Q.coeffs.map AzInt.toAzRat)[n]?).getD 0 = _
  rw [Array.getElem?_map]
  rcases h : Q.coeffs[n]? with _ | v
  · simp [AzPolynomial.coeff, h, h0]
  · simp [AzPolynomial.coeff, h]

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R] [IsRealClosed R]

omit [DecidableEq R] [IsRealClosed R] in
/-- Pushing the `AzInt → AzRat` lift into `R` along `AzRat → ℚ → R` is the same as
pushing the `AzInt` polynomial along `AzInt → ℤ → R`. -/
theorem toPoly_mapAzIntToAzRat_map (Q : AzPolynomial AzInt) :
    (AzPolynomial.toPoly (mapAzIntToAzRat Q)).map ((Rat.castHom R).comp AzRat.toRatRingHom)
      = (AzPolynomial.toPoly Q).map ((Int.castRingHom R).comp AzInt.toIntRingHom) := by
  ext n
  simp only [Polynomial.coeff_map, AzPolynomial.coeff_toPoly, RingHom.comp_apply,
    AzRat.toRatRingHom_apply, AzInt.toIntRingHom_apply, Int.coe_castRingHom]
  rw [coeff_mapAzIntToAzRat, AzRat.toRat_toAzRat_int]
  exact Rat.cast_intCast _

omit [DecidableEq R] [IsRealClosed R] in
/-- The order embedding `AzRat → ℚ → R` (strictly monotone ring hom). -/
private theorem azRatCast_strictMono :
    StrictMono ((Rat.castHom R).comp AzRat.toRatRingHom) := fun a b h =>
  Rat.cast_strictMono (by simpa using AzRat.orderIsoRat.strictMono h)

/-- **Whole-line correctness of `cauchyIndexOnIntSRem` over `AzInt`.** The
signed-remainder Cauchy index computed over the integers equals the Cauchy index
of the polynomials pushed into any real closed field `R` (via `AzInt → ℤ → R`,
matching `cauchyIndex_azInt_eq_BPR`). -/
theorem cauchyIndexOnIntSRem_negInf_posInf_eq_BPR (Q P : AzPolynomial AzInt) :
    cauchyIndexOnIntSRem Q P .negInf .posInf
      = Azurite.BPR.cauchyIndex
          ((AzPolynomial.toPoly Q).map ((Int.castRingHom R).comp AzInt.toIntRingHom))
          ((AzPolynomial.toPoly P).map ((Int.castRingHom R).comp AzInt.toIntRingHom)) := by
  rw [← toPoly_mapAzIntToAzRat_map, ← toPoly_mapAzIntToAzRat_map]
  exact cauchyIndexOnSRem_negInf_posInf_map_eq_BPR _ azRatCast_strictMono _ _

/-- **Whole-line correctness of `tarskiQueryOnIntSRem` over `AzInt`.** -/
theorem tarskiQueryOnIntSRem_negInf_posInf_eq_BPR (Q P : AzPolynomial AzInt) :
    tarskiQueryOnIntSRem Q P .negInf .posInf
      = Azurite.BPR.tarskiQuery
          ((AzPolynomial.toPoly Q).map ((Int.castRingHom R).comp AzInt.toIntRingHom))
          ((AzPolynomial.toPoly P).map ((Int.castRingHom R).comp AzInt.toIntRingHom)) := by
  rw [← toPoly_mapAzIntToAzRat_map, ← toPoly_mapAzIntToAzRat_map]
  exact tarskiQueryOnSRem_negInf_posInf_map_eq_BPR _ azRatCast_strictMono _ _

end Int

end Azurite.AzPolynomial
