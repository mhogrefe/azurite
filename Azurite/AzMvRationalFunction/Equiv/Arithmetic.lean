import Azurite.AzMvRationalFunction.Arithmetic
import Azurite.AzMvRationalFunction.Equiv.Basic
import Azurite.AzMvRationalFunction.Equiv.Parse
import Azurite.AzMvPolynomial.Equiv.GcdCofactor
import Azurite.AzMvPolynomial.Equiv.IntContentMul
import Azurite.AzMvPolynomial.Equiv.ContentDescent
import Azurite.AzRat.Equiv.Unary
import Azurite.AzRat.Equiv.Mul
import Azurite.AzRat.Equiv.Pow

/-!
# Correctness of the `AzMvRationalFunction` arithmetic

`toMvRatFunc` is compatible with negation, reciprocal, multiplication and
division: it maps `-r`/`r⁻¹`/`r * s`/`r / s` to the corresponding operation in
`ℚ(x⃗) = FractionRing (MvPolynomial (Fin n) ℚ)` (`0⁻¹ = 0`, `r / 0 = 0`). In
particular the cross-gcd multiplication's decidable invariant checks always
pass — the fallback `0` branch is unreachable. The pullback `ofMvRatFunc`
intertwines them too. Mirrors the univariate
`AzRationalFunction/Equiv/Arithmetic.lean`, but coprimality of the reduced
parts is proved with `IsRelPrime` over `MvPolynomial (Fin n) ℚ` (not `IsCoprime`,
which fails for `n ≥ 2` since `ℚ[x⃗]` is not Bézout).
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- **Negation is correct**: `toMvRatFunc (-r) = -(toMvRatFunc r)`. -/
theorem toMvRatFunc_neg (r : AzMvRationalFunction n ord) :
    toMvRatFunc (-r) = -(toMvRatFunc r) := by
  show toMvRatFunc (neg r) = _
  rw [toMvRatFunc, toMvRatFunc]
  show algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ))
      (Azurite.AzRat.toRat (-r.factor)) * _ = _
  rw [Azurite.AzRat.toRat_neg, map_neg, neg_mul]
  rfl

/-- **Reciprocal is correct**: `toMvRatFunc r⁻¹ = (toMvRatFunc r)⁻¹`
(`0⁻¹ = 0` on both sides). -/
theorem toMvRatFunc_inv (r : AzMvRationalFunction n ord) :
    toMvRatFunc r⁻¹ = (toMvRatFunc r)⁻¹ := by
  show toMvRatFunc (inv r) = _
  rw [inv]
  by_cases h : r.factor = 0
  · rw [dif_pos h]
    have hr : toMvRatFunc r = 0 := by
      rw [toMvRatFunc, h]
      have h0 : Azurite.AzRat.toRat 0 = 0 := rfl
      rw [h0, map_zero, zero_mul]
    rw [hr, inv_zero, toMvRatFunc_zero]
  · rw [dif_neg h, toMvRatFunc, toMvRatFunc]
    show algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ))
          (Azurite.AzRat.toRat r.factor⁻¹)
        * (algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
              (toMvPolyQ r.den)
            / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
              (toMvPolyQ r.num)) = _
    rw [Azurite.AzRat.toRat_inv, map_inv₀, mul_inv, inv_div]

/-- `ofMvRatFunc` version: pulling back a negation. -/
theorem ofMvRatFunc_neg (f : FractionRing (MvPolynomial (Fin n) ℚ)) :
    ofMvRatFunc (-f) = -(ofMvRatFunc f : AzMvRationalFunction n ord) :=
  toMvRatFunc_injective (by
    rw [toMvRatFunc_ofMvRatFunc, toMvRatFunc_neg, toMvRatFunc_ofMvRatFunc])

/-- `ofMvRatFunc` version: pulling back an inverse. -/
theorem ofMvRatFunc_inv (f : FractionRing (MvPolynomial (Fin n) ℚ)) :
    ofMvRatFunc f⁻¹ = (ofMvRatFunc f : AzMvRationalFunction n ord)⁻¹ :=
  toMvRatFunc_injective (by
    rw [toMvRatFunc_ofMvRatFunc, toMvRatFunc_inv, toMvRatFunc_ofMvRatFunc])

/-! ### Multiplication and division -/

/-- Resolve `mul` once the guard conjuncts are known to hold (so the fallback
`0` branch is skipped). -/
private theorem mul_eq_of_guard (r s : AzMvRationalFunction n ord)
    (hrs : ¬(r.factor = 0 ∨ s.factor = 0))
    (h1 : (Azurite.ExactDiv.exactDiv r.num (signNorm (AzMvPolynomial.gcd r.num s.den))
        * Azurite.ExactDiv.exactDiv s.num (signNorm (AzMvPolynomial.gcd s.num r.den))).intContent = 1)
    (h2 : (Azurite.ExactDiv.exactDiv r.den (signNorm (AzMvPolynomial.gcd s.num r.den))
        * Azurite.ExactDiv.exactDiv s.den (signNorm (AzMvPolynomial.gcd r.num s.den))).intContent = 1)
    (h3 : (0 : AzInt) < (Azurite.ExactDiv.exactDiv r.num (signNorm (AzMvPolynomial.gcd r.num s.den))
        * Azurite.ExactDiv.exactDiv s.num (signNorm (AzMvPolynomial.gcd s.num r.den))).leadingCoeff)
    (h4 : (0 : AzInt) < (Azurite.ExactDiv.exactDiv r.den (signNorm (AzMvPolynomial.gcd s.num r.den))
        * Azurite.ExactDiv.exactDiv s.den (signNorm (AzMvPolynomial.gcd r.num s.den))).leadingCoeff)
    (h5 : AzMvPolynomial.coprime
        (Azurite.ExactDiv.exactDiv r.num (signNorm (AzMvPolynomial.gcd r.num s.den))
          * Azurite.ExactDiv.exactDiv s.num (signNorm (AzMvPolynomial.gcd s.num r.den)))
        (Azurite.ExactDiv.exactDiv r.den (signNorm (AzMvPolynomial.gcd s.num r.den))
          * Azurite.ExactDiv.exactDiv s.den (signNorm (AzMvPolynomial.gcd r.num s.den))) = true)
    (h6 : r.factor * s.factor = 0 →
        Azurite.ExactDiv.exactDiv r.num (signNorm (AzMvPolynomial.gcd r.num s.den))
          * Azurite.ExactDiv.exactDiv s.num (signNorm (AzMvPolynomial.gcd s.num r.den)) = 1
        ∧ Azurite.ExactDiv.exactDiv r.den (signNorm (AzMvPolynomial.gcd s.num r.den))
          * Azurite.ExactDiv.exactDiv s.den (signNorm (AzMvPolynomial.gcd r.num s.den)) = 1) :
    mul r s = ⟨r.factor * s.factor,
      Azurite.ExactDiv.exactDiv r.num (signNorm (AzMvPolynomial.gcd r.num s.den))
        * Azurite.ExactDiv.exactDiv s.num (signNorm (AzMvPolynomial.gcd s.num r.den)),
      Azurite.ExactDiv.exactDiv r.den (signNorm (AzMvPolynomial.gcd s.num r.den))
        * Azurite.ExactDiv.exactDiv s.den (signNorm (AzMvPolynomial.gcd r.num s.den)),
      h1, h2, h3, h4, h5, h6⟩ := by
  simp only [mul, if_neg hrs]
  rw [dif_pos (⟨h1, h2, h3, h4, h5, h6⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)]

set_option maxHeartbeats 1600000 in
/-- **Multiplication is correct**: `toMvRatFunc (r * s) = toMvRatFunc r * toMvRatFunc s`
— in particular the cross-gcd constructor's invariant checks always pass (the
fallback `0` branch is unreachable). -/
theorem toMvRatFunc_mul (r s : AzMvRationalFunction n ord) :
    toMvRatFunc (r * s) = toMvRatFunc r * toMvRatFunc s := by
  show toMvRatFunc (mul r s) = _
  by_cases hr : r.factor = 0
  · have hmz : mul r s = 0 := by rw [mul, if_pos (Or.inl hr)]
    have hr0 : toMvRatFunc r = 0 := by
      rw [toMvRatFunc, hr, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    rw [hmz, toMvRatFunc_zero, hr0, zero_mul]
  by_cases hs : s.factor = 0
  · have hmz : mul r s = 0 := by rw [mul, if_pos (Or.inr hs)]
    have hs0 : toMvRatFunc s = 0 := by
      rw [toMvRatFunc, hs, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    rw [hmz, toMvRatFunc_zero, hs0, mul_zero]
  have hnd : ¬(r.factor = 0 ∨ s.factor = 0) := fun h0 => h0.elim hr hs
  have hf0 : r.factor * s.factor ≠ 0 := by
    intro h0
    have h1 := congrArg Azurite.AzRat.toRat h0
    rw [Azurite.AzRat.toRat_mul, Azurite.AzRat.toRat_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hr (Azurite.AzRat.toRat_injective (by rw [h2, Azurite.AzRat.toRat_zero]))
    · exact hs (Azurite.AzRat.toRat_injective (by rw [h2, Azurite.AzRat.toRat_zero]))
  -- the two cross gcds (sign-normalized) and their four cofactors
  set G₁ := signNorm (AzMvPolynomial.gcd r.num s.den) with hG₁def
  set G₂ := signNorm (AzMvPolynomial.gcd s.num r.den) with hG₂def
  set A := Azurite.ExactDiv.exactDiv r.num G₁ with hAdef
  set B := Azurite.ExactDiv.exactDiv s.num G₂ with hBdef
  set C := Azurite.ExactDiv.exactDiv r.den G₂ with hCdef
  set D := Azurite.ExactDiv.exactDiv s.den G₁ with hDdef
  have hG₁a : G₁ ∣ r.num := (signNorm_dvd _).trans (gcd_dvd_left r.num s.den)
  have hG₁d : G₁ ∣ s.den := (signNorm_dvd _).trans (gcd_dvd_right r.num s.den)
  have hG₂a : G₂ ∣ s.num := (signNorm_dvd _).trans (gcd_dvd_left s.num r.den)
  have hG₂d : G₂ ∣ r.den := (signNorm_dvd _).trans (gcd_dvd_right s.num r.den)
  have hG₁0 : G₁ ≠ 0 := signNorm_ne_zero (gcd_ne_zero_left (num_ne_zero r))
  have hG₂0 : G₂ ≠ 0 := signNorm_ne_zero (gcd_ne_zero_left (num_ne_zero s))
  have hAid : A * G₁ = r.num := Azurite.ExactDiv.exactDiv_mul_self r.num G₁ hG₁a hG₁0
  have hBid : B * G₂ = s.num := Azurite.ExactDiv.exactDiv_mul_self s.num G₂ hG₂a hG₂0
  have hCid : C * G₂ = r.den := Azurite.ExactDiv.exactDiv_mul_self r.den G₂ hG₂d hG₂0
  have hDid : D * G₁ = s.den := Azurite.ExactDiv.exactDiv_mul_self s.den G₁ hG₁d hG₁0
  have hAdvd : A ∣ r.num := ⟨G₁, hAid.symm⟩
  have hBdvd : B ∣ s.num := ⟨G₂, hBid.symm⟩
  have hCdvd : C ∣ r.den := ⟨G₂, hCid.symm⟩
  have hDdvd : D ∣ s.den := ⟨G₁, hDid.symm⟩
  have hA0 : A ≠ 0 := fun h0 => num_ne_zero r (zero_dvd_iff.mp (h0 ▸ hAdvd))
  have hB0 : B ≠ 0 := fun h0 => num_ne_zero s (zero_dvd_iff.mp (h0 ▸ hBdvd))
  have hC0 : C ≠ 0 := fun h0 => den_ne_zero r (zero_dvd_iff.mp (h0 ▸ hCdvd))
  have hD0 : D ≠ 0 := fun h0 => den_ne_zero s (zero_dvd_iff.mp (h0 ▸ hDdvd))
  -- guard: contents (Gauss: products of primitive cofactors of primitives)
  have hncont : (A * B).intContent = 1 := by
    rw [intContent_mul, intContent_exactDiv_eq_one hG₁a hG₁0 r.num_primitive,
      intContent_exactDiv_eq_one hG₂a hG₂0 s.num_primitive, mul_one]
  have hdcont : (C * D).intContent = 1 := by
    rw [intContent_mul, intContent_exactDiv_eq_one hG₂d hG₂0 r.den_primitive,
      intContent_exactDiv_eq_one hG₁d hG₁0 s.den_primitive, mul_one]
  -- guard: positive leading coefficients
  have hAlc : 0 < A.leadingCoeff := leadingCoeff_exactDiv_pos hG₁a hG₁0
    (leadingCoeff_signNorm_pos (gcd_ne_zero_left (num_ne_zero r))) r.num_lc_pos
  have hBlc : 0 < B.leadingCoeff := leadingCoeff_exactDiv_pos hG₂a hG₂0
    (leadingCoeff_signNorm_pos (gcd_ne_zero_left (num_ne_zero s))) s.num_lc_pos
  have hClc : 0 < C.leadingCoeff := leadingCoeff_exactDiv_pos hG₂d hG₂0
    (leadingCoeff_signNorm_pos (gcd_ne_zero_left (num_ne_zero s))) r.den_lc_pos
  have hDlc : 0 < D.leadingCoeff := leadingCoeff_exactDiv_pos hG₁d hG₁0
    (leadingCoeff_signNorm_pos (gcd_ne_zero_left (num_ne_zero r))) s.den_lc_pos
  have hnlc : (0 : AzInt) < (A * B).leadingCoeff := by
    rw [leadingCoeff_mul hA0 hB0]; exact mul_pos hAlc hBlc
  have hdlc : (0 : AzInt) < (C * D).leadingCoeff := by
    rw [leadingCoeff_mul hC0 hD0]; exact mul_pos hClc hDlc
  -- guard: coprimality, via the four cross pairs (IsRelPrime over `ℚ[x⃗]`)
  have hr_rel : IsRelPrime (toMvPolyQ r.num) (toMvPolyQ r.den) := by
    rw [toMvPolyQ_eq_ratImg, toMvPolyQ_eq_ratImg]
    exact coprime_isRelPrime r.reduced
  have hs_rel : IsRelPrime (toMvPolyQ s.num) (toMvPolyQ s.den) := by
    rw [toMvPolyQ_eq_ratImg, toMvPolyQ_eq_ratImg]
    exact coprime_isRelPrime s.reduced
  -- A ⊥ C (both divide r's coprime parts); B ⊥ D (both divide s's)
  have hAC : IsRelPrime (toMvPolyQ A) (toMvPolyQ C) :=
    (hr_rel.of_dvd_left (map_dvd toMvPolyQHom hAdvd)).of_dvd_right (map_dvd toMvPolyQHom hCdvd)
  have hBD : IsRelPrime (toMvPolyQ B) (toMvPolyQ D) :=
    (hs_rel.of_dvd_left (map_dvd toMvPolyQHom hBdvd)).of_dvd_right (map_dvd toMvPolyQHom hDdvd)
  -- A ⊥ D (cofactors of the same gcd G₁); B ⊥ C (cofactors of the same gcd G₂)
  have hAD : IsRelPrime (toMvPolyQ A) (toMvPolyQ D) := by
    rw [toMvPolyQ_eq_ratImg, toMvPolyQ_eq_ratImg]
    exact coprime_isRelPrime (coprime_exactDiv_signNorm (num_ne_zero r) (den_ne_zero s))
  have hBC : IsRelPrime (toMvPolyQ B) (toMvPolyQ C) := by
    rw [toMvPolyQ_eq_ratImg, toMvPolyQ_eq_ratImg]
    exact coprime_isRelPrime (coprime_exactDiv_signNorm (num_ne_zero s) (den_ne_zero r))
  have hcop : AzMvPolynomial.coprime (A * B) (C * D) = true := by
    apply coprime_of_isRelPrime
    rw [← toMvPolyQ_eq_ratImg (A * B), ← toMvPolyQ_eq_ratImg (C * D), toMvPolyQ_mul, toMvPolyQ_mul]
    exact (hAC.mul_right hAD).mul_left (hBC.mul_right hBD)
  -- the represented value: cancel the two gcds in the fraction field
  have hAidQ : toMvPolyQ A * toMvPolyQ G₁ = toMvPolyQ r.num := by rw [← toMvPolyQ_mul, hAid]
  have hBidQ : toMvPolyQ B * toMvPolyQ G₂ = toMvPolyQ s.num := by rw [← toMvPolyQ_mul, hBid]
  have hCidQ : toMvPolyQ C * toMvPolyQ G₂ = toMvPolyQ r.den := by rw [← toMvPolyQ_mul, hCid]
  have hDidQ : toMvPolyQ D * toMvPolyQ G₁ = toMvPolyQ s.den := by rw [← toMvPolyQ_mul, hDid]
  set φ := algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ)) with hφdef
  have hcancel : ∀ (c : MvPolynomial (Fin n) ℚ), φ c ≠ 0 → ∀ (u v : MvPolynomial (Fin n) ℚ),
      φ (c * u) / φ (c * v) = φ u / φ v := by
    intro c hc u v
    rw [map_mul, map_mul, mul_div_mul_left _ _ hc]
  have hφG0 : φ (toMvPolyQ G₁ * toMvPolyQ G₂) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr (toMvPolyQ_ne_zero hG₁0))
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr (toMvPolyQ_ne_zero hG₂0))
  have hnQ : toMvPolyQ r.num * toMvPolyQ s.num
      = (toMvPolyQ G₁ * toMvPolyQ G₂) * toMvPolyQ (A * B) := by
    rw [← hAidQ, ← hBidQ, toMvPolyQ_mul]; ring
  have hdQ : toMvPolyQ r.den * toMvPolyQ s.den
      = (toMvPolyQ G₁ * toMvPolyQ G₂) * toMvPolyQ (C * D) := by
    rw [← hCidQ, ← hDidQ, toMvPolyQ_mul]; ring
  have hfrac : φ (toMvPolyQ r.num) / φ (toMvPolyQ r.den)
        * (φ (toMvPolyQ s.num) / φ (toMvPolyQ s.den))
      = φ (toMvPolyQ (A * B)) / φ (toMvPolyQ (C * D)) := by
    rw [div_mul_div_comm, ← map_mul, ← map_mul, hnQ, hdQ, hcancel _ hφG0]
  have hmain : algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ))
        (Azurite.AzRat.toRat (r.factor * s.factor))
        * (φ (toMvPolyQ (A * B)) / φ (toMvPolyQ (C * D)))
      = toMvRatFunc r * toMvRatFunc s := by
    rw [toMvRatFunc, toMvRatFunc, Azurite.AzRat.toRat_mul, map_mul, ← hfrac]; ring
  rw [mul_eq_of_guard r s hnd hncont hdcont hnlc hdlc hcop (fun h0 => absurd h0 hf0)]
  show algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ))
      (Azurite.AzRat.toRat (r.factor * s.factor))
      * (φ (toMvPolyQ (A * B)) / φ (toMvPolyQ (C * D))) = _
  exact hmain

/-- **Division is correct**: `toMvRatFunc (r / s) = toMvRatFunc r / toMvRatFunc s`
(`r / 0 = 0` on both sides). -/
theorem toMvRatFunc_div (r s : AzMvRationalFunction n ord) :
    toMvRatFunc (r / s) = toMvRatFunc r / toMvRatFunc s := by
  show toMvRatFunc (r * s⁻¹) = _
  rw [toMvRatFunc_mul, toMvRatFunc_inv, div_eq_mul_inv]

/-- `ofMvRatFunc` version: pulling back a product. -/
theorem ofMvRatFunc_mul (f g : FractionRing (MvPolynomial (Fin n) ℚ)) :
    ofMvRatFunc (f * g) = (ofMvRatFunc f : AzMvRationalFunction n ord) * ofMvRatFunc g :=
  toMvRatFunc_injective (by
    rw [toMvRatFunc_ofMvRatFunc, toMvRatFunc_mul, toMvRatFunc_ofMvRatFunc, toMvRatFunc_ofMvRatFunc])

/-- `ofMvRatFunc` version: pulling back a quotient. -/
theorem ofMvRatFunc_div (f g : FractionRing (MvPolynomial (Fin n) ℚ)) :
    ofMvRatFunc (f / g) = (ofMvRatFunc f : AzMvRationalFunction n ord) / ofMvRatFunc g :=
  toMvRatFunc_injective (by
    rw [toMvRatFunc_ofMvRatFunc, toMvRatFunc_div, toMvRatFunc_ofMvRatFunc, toMvRatFunc_ofMvRatFunc])

/-! ### Bridges for addition

The `add` algorithm decomposes the rational factors into `AzInt` numerator
and denominator components, cross-multiplies into a combined polynomial
numerator, and re-extracts the content (as a `signedIntContent`/`primPos`
pair). Coprimality of the reduced parts is proved with `IsRelPrime` over
`ℚ[x⃗]` (not `IsCoprime`, which fails for `n ≥ 2`). -/

/-- The signed numerator component of an `AzRat`, as an `AzInt`
(the `a₁`/`a₂` of `add`). -/
private abbrev ratNum (q : Azurite.AzRat) : AzInt := ⟨q.sign, q.num, q.zero_sign⟩

/-- The (positive) denominator component of an `AzRat`, as an `AzInt`
(the `b₁`/`b₂` of `add`). -/
private abbrev ratDen (q : Azurite.AzRat) : AzInt := ⟨true, q.den, fun _ => rfl⟩

private theorem ratNum_def (q : Azurite.AzRat) :
    (⟨q.sign, q.num, q.zero_sign⟩ : AzInt) = ratNum q := rfl

private theorem ratDen_def (q : Azurite.AzRat) :
    (⟨true, q.den, fun _ => rfl⟩ : AzInt) = ratDen q := rfl

private theorem ratDen_toInt (q : Azurite.AzRat) :
    (ratDen q).toInt = (q.den.toNat : ℤ) := rfl

private theorem ratDen_toInt_pos (q : Azurite.AzRat) : 0 < (ratDen q).toInt := by
  rw [ratDen_toInt]
  have h : q.den.toNat ≠ 0 := fun h0 =>
    q.den_nz (Azurite.AzNat.toNat_injective (h0.trans Azurite.AzNat.toNat_zero.symm))
  omega

/-- The represented rational, through the `add` components: `±num / den`. -/
private theorem toRat_factored (q : Azurite.AzRat) :
    Azurite.AzRat.toRat q = ((ratNum q).toInt : ℚ) / ((ratDen q).toInt : ℚ) := by
  have h1 : ((ratNum q).toInt : ℚ) = ((Azurite.AzRat.toRat q).num : ℚ) := rfl
  have h2 : ((ratDen q).toInt : ℚ) = ((Azurite.AzRat.toRat q).den : ℚ) :=
    Int.cast_natCast q.den.toNat
  rw [h1, h2, Rat.num_div_den]

private theorem ratNum_toInt_ne_zero {q : Azurite.AzRat} (hq : q ≠ 0) :
    (ratNum q).toInt ≠ 0 := by
  intro h0
  apply hq
  apply Azurite.AzRat.toRat_injective
  rw [Azurite.AzRat.toRat_zero, toRat_factored, h0, Int.cast_zero, zero_div]

/-- `ℚ[x⃗]`-image of a sum. -/
private theorem toMvPolyQ_add (p q : AzMvPolynomial n AzInt ord) :
    toMvPolyQ (p + q) = toMvPolyQ p + toMvPolyQ q := map_add toMvPolyQHom p q

/-- The coefficient hom on `AzInt` is the `ℤ`-cast of `toInt` (definitionally). -/
private theorem coeffQ_toInt' (a : AzInt) : coeffQ a = (a.toInt : ℚ) := rfl

/-- Images of nonzero polynomials stay nonzero in the fraction field. -/
private theorem algebraMap_ne_zero_of_ne {p : MvPolynomial (Fin n) ℚ} (hp : p ≠ 0) :
    algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ)) p ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hp

/-- `signNorm` preserves the total degree (it only possibly negates). -/
private theorem signNorm_totalDegree (P : AzMvPolynomial n AzInt ord) :
    (signNorm P).totalDegree = P.totalDegree := by
  rw [signNorm]
  split
  · rfl
  · rw [totalDegree_toMvPoly, totalDegree_toMvPoly, toMvPoly_neg, MvPolynomial.totalDegree_neg]

/-- The `primPos` factorization, at the `ℚ[x⃗]` level. -/
private theorem primPos_toMvPolyQ (P : AzMvPolynomial n AzInt ord) :
    MvPolynomial.C ((signedIntContent P).toInt : ℚ) * toMvPolyQ (primPos P) = toMvPolyQ P := by
  have h := congrArg toMvPolyQ (primPos_factorization P)
  rwa [toMvPolyQ_mul, toMvPolyQ_C, coeffQ_toInt'] at h

/-- `primPos P ∣ P` (the signed content is the complementary factor). -/
private theorem primPos_dvd (P : AzMvPolynomial n AzInt ord) : primPos P ∣ P :=
  ⟨AzMvPolynomial.C (signedIntContent P), by rw [mul_comm]; exact (primPos_factorization P).symm⟩

/-! #### The `add` intermediates, named -/

/-- The fast-path combined numerator of `add` (coprime denominator parts). -/
private abbrev fastT (r s : AzMvRationalFunction n ord) : AzMvPolynomial n AzInt ord :=
  (ratNum r.factor * ratDen s.factor) • (r.num * s.den)
    + (ratNum s.factor * ratDen r.factor) • (s.num * r.den)

/-- The `D₁/G` cofactor of the Knuth path. -/
private abbrev slowD₁ (r s : AzMvRationalFunction n ord) : AzMvPolynomial n AzInt ord :=
  Azurite.ExactDiv.exactDiv r.den (signNorm (AzMvPolynomial.gcd r.den s.den))

/-- The `D₂/G` cofactor of the Knuth path. -/
private abbrev slowD₂ (r s : AzMvRationalFunction n ord) : AzMvPolynomial n AzInt ord :=
  Azurite.ExactDiv.exactDiv s.den (signNorm (AzMvPolynomial.gcd r.den s.den))

/-- The Knuth-path combined numerator before the `H`-reduction. -/
private abbrev slowT₀ (r s : AzMvRationalFunction n ord) : AzMvPolynomial n AzInt ord :=
  (ratNum r.factor * ratDen s.factor) • (r.num * slowD₂ r s)
    + (ratNum s.factor * ratDen r.factor) • (s.num * slowD₁ r s)

/-- The second small gcd `H = signNorm (gcd T₀ G)` of the Knuth path. -/
private abbrev slowH (r s : AzMvRationalFunction n ord) : AzMvPolynomial n AzInt ord :=
  signNorm (AzMvPolynomial.gcd (slowT₀ r s) (signNorm (AzMvPolynomial.gcd r.den s.den)))

/-- The reduced numerator `T₀/H` of the Knuth path. -/
private abbrev slowT (r s : AzMvRationalFunction n ord) : AzMvPolynomial n AzInt ord :=
  Azurite.ExactDiv.exactDiv (slowT₀ r s) (slowH r s)

/-- The `D₂/H` cofactor of the Knuth path. -/
private abbrev slowD₂H (r s : AzMvRationalFunction n ord) : AzMvPolynomial n AzInt ord :=
  Azurite.ExactDiv.exactDiv s.den (slowH r s)

private theorem fastT_def (r s : AzMvRationalFunction n ord) :
    (ratNum r.factor * ratDen s.factor) • (r.num * s.den)
      + (ratNum s.factor * ratDen r.factor) • (s.num * r.den) = fastT r s := rfl

private theorem slowD₁_def (r s : AzMvRationalFunction n ord) :
    Azurite.ExactDiv.exactDiv r.den (signNorm (AzMvPolynomial.gcd r.den s.den)) = slowD₁ r s := rfl

private theorem slowD₂_def (r s : AzMvRationalFunction n ord) :
    Azurite.ExactDiv.exactDiv s.den (signNorm (AzMvPolynomial.gcd r.den s.den)) = slowD₂ r s := rfl

private theorem slowT₀_def (r s : AzMvRationalFunction n ord) :
    (ratNum r.factor * ratDen s.factor) • (r.num * slowD₂ r s)
      + (ratNum s.factor * ratDen r.factor) • (s.num * slowD₁ r s) = slowT₀ r s := rfl

private theorem slowH_def (r s : AzMvRationalFunction n ord) :
    signNorm (AzMvPolynomial.gcd (slowT₀ r s) (signNorm (AzMvPolynomial.gcd r.den s.den)))
      = slowH r s := rfl

private theorem slowT_def (r s : AzMvRationalFunction n ord) :
    Azurite.ExactDiv.exactDiv (slowT₀ r s) (slowH r s) = slowT r s := rfl

private theorem slowD₂H_def (r s : AzMvRationalFunction n ord) :
    Azurite.ExactDiv.exactDiv s.den (slowH r s) = slowD₂H r s := rfl

/-- The `ℚ[x⃗]` image of the fast-path numerator. -/
private theorem toMvPolyQ_fastT (r s : AzMvRationalFunction n ord) :
    toMvPolyQ (fastT r s)
      = MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
          * (toMvPolyQ r.num * toMvPolyQ s.den)
        + MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
          * (toMvPolyQ s.num * toMvPolyQ r.den) := by
  show toMvPolyQ ((ratNum r.factor * ratDen s.factor) • (r.num * s.den)
    + (ratNum s.factor * ratDen r.factor) • (s.num * r.den)) = _
  rw [toMvPolyQ_add, toMvPolyQ_smul, toMvPolyQ_smul, toMvPolyQ_mul, toMvPolyQ_mul,
    Azurite.AzInt.toInt_mul, Azurite.AzInt.toInt_mul, Int.cast_mul, Int.cast_mul]

/-- The `ℚ[x⃗]` image of the Knuth-path numerator `T₀`. -/
private theorem toMvPolyQ_slowT₀ (r s : AzMvRationalFunction n ord) :
    toMvPolyQ (slowT₀ r s)
      = MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
          * (toMvPolyQ r.num * toMvPolyQ (slowD₂ r s))
        + MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
          * (toMvPolyQ s.num * toMvPolyQ (slowD₁ r s)) := by
  show toMvPolyQ ((ratNum r.factor * ratDen s.factor) • (r.num * slowD₂ r s)
    + (ratNum s.factor * ratDen r.factor) • (s.num * slowD₁ r s)) = _
  rw [toMvPolyQ_add, toMvPolyQ_smul, toMvPolyQ_smul, toMvPolyQ_mul, toMvPolyQ_mul,
    Azurite.AzInt.toInt_mul, Azurite.AzInt.toInt_mul, Int.cast_mul, Int.cast_mul]

/-- **The sum, over a common denominator**: `toMvRatFunc r + toMvRatFunc s` as a
single `ℚ(x⃗)` fraction of `ℚ[x⃗]` images. -/
private theorem sum_eq (r s : AzMvRationalFunction n ord) :
    toMvRatFunc r + toMvRatFunc s
      = algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
              * (toMvPolyQ r.num * toMvPolyQ s.den)
            + MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
              * (toMvPolyQ s.num * toMvPolyQ r.den))
        / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (MvPolynomial.C (((ratDen r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
            * (toMvPolyQ r.den * toMvPolyQ s.den)) := by
  have hβ₁ : ((ratDen r.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos r.factor).ne'
  have hβ₂ : ((ratDen s.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos s.factor).ne'
  have h1 : toMvRatFunc r
      = algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (MvPolynomial.C (((ratNum r.factor).toInt : ℚ)) * toMvPolyQ r.num)
        / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (MvPolynomial.C (((ratDen r.factor).toInt : ℚ)) * toMvPolyQ r.den) := by
    rw [toMvRatFunc, toRat_factored, map_div₀, algebraMapQ_C, algebraMapQ_C,
      div_mul_div_comm, ← map_mul, ← map_mul]
  have h2 : toMvRatFunc s
      = algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (MvPolynomial.C (((ratNum s.factor).toInt : ℚ)) * toMvPolyQ s.num)
        / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (MvPolynomial.C (((ratDen s.factor).toInt : ℚ)) * toMvPolyQ s.den) := by
    rw [toMvRatFunc, toRat_factored, map_div₀, algebraMapQ_C, algebraMapQ_C,
      div_mul_div_comm, ← map_mul, ← map_mul]
  have hφ1 : algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
      (MvPolynomial.C (((ratDen r.factor).toInt : ℚ)) * toMvPolyQ r.den) ≠ 0 :=
    algebraMap_ne_zero_of_ne (mul_ne_zero
      (fun h => hβ₁ (MvPolynomial.C_eq_zero.mp h)) (toMvPolyQ_den_ne_zero r))
  have hφ2 : algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
      (MvPolynomial.C (((ratDen s.factor).toInt : ℚ)) * toMvPolyQ s.den) ≠ 0 :=
    algebraMap_ne_zero_of_ne (mul_ne_zero
      (fun h => hβ₂ (MvPolynomial.C_eq_zero.mp h)) (toMvPolyQ_den_ne_zero s))
  rw [h1, h2, div_add_div _ _ hφ1 hφ2, ← map_mul, ← map_mul, ← map_mul, ← map_add]
  have hnum : MvPolynomial.C (((ratNum r.factor).toInt : ℚ)) * toMvPolyQ r.num
        * (MvPolynomial.C (((ratDen s.factor).toInt : ℚ)) * toMvPolyQ s.den)
      + MvPolynomial.C (((ratDen r.factor).toInt : ℚ)) * toMvPolyQ r.den
        * (MvPolynomial.C (((ratNum s.factor).toInt : ℚ)) * toMvPolyQ s.num)
      = MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
          * (toMvPolyQ r.num * toMvPolyQ s.den)
        + MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
          * (toMvPolyQ s.num * toMvPolyQ r.den) := by
    rw [MvPolynomial.C_mul, MvPolynomial.C_mul]
    ring
  have hden : MvPolynomial.C (((ratDen r.factor).toInt : ℚ)) * toMvPolyQ r.den
        * (MvPolynomial.C (((ratDen s.factor).toInt : ℚ)) * toMvPolyQ s.den)
      = MvPolynomial.C (((ratDen r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
          * (toMvPolyQ r.den * toMvPolyQ s.den) := by
    rw [MvPolynomial.C_mul]
    ring
  rw [hnum, hden]

set_option maxHeartbeats 1600000 in
/-- **Addition is correct**: `toMvRatFunc (r + s) = toMvRatFunc r + toMvRatFunc s`
— in particular the Knuth constructor's invariant checks always pass (the
fallback `0` branch is unreachable). Coprimality is via `IsRelPrime` over
`ℚ[x⃗]`. -/
theorem toMvRatFunc_add (r s : AzMvRationalFunction n ord) :
    toMvRatFunc (r + s) = toMvRatFunc r + toMvRatFunc s := by
  classical
  show toMvRatFunc (add r s) = _
  by_cases hr : r.factor = 0
  · have h0 : add r s = s := by rw [add, if_pos hr]
    have hr0 : toMvRatFunc r = 0 := by
      rw [toMvRatFunc, hr, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    rw [h0, hr0, zero_add]
  by_cases hs : s.factor = 0
  · have h0 : add r s = r := by rw [add, if_neg hr, if_pos hs]
    have hs0 : toMvRatFunc s = 0 := by
      rw [toMvRatFunc, hs, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    rw [h0, hs0, add_zero]
  -- shared scalar and coprimality facts
  have hα₁ : ((ratNum r.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratNum_toInt_ne_zero hr)
  have hα₂ : ((ratNum s.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratNum_toInt_ne_zero hs)
  have hβ₁ : ((ratDen r.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos r.factor).ne'
  have hβ₂ : ((ratDen s.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos s.factor).ne'
  have hc₁ : ((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ) ≠ 0 :=
    mul_ne_zero hα₁ hβ₂
  have hc₂ : ((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ) ≠ 0 :=
    mul_ne_zero hα₂ hβ₁
  have hbb0 : (ratDen r.factor * ratDen s.factor).toInt ≠ 0 := by
    rw [Azurite.AzInt.toInt_mul]
    exact mul_ne_zero (ratDen_toInt_pos r.factor).ne' (ratDen_toInt_pos s.factor).ne'
  have hbbAz : ratDen r.factor * ratDen s.factor ≠ 0 :=
    fun h => hbb0 (by rw [h, Azurite.AzInt.toInt_zero])
  have hND₁ : IsRelPrime (toMvPolyQ r.num) (toMvPolyQ r.den) := isRelPrime_num_den r
  have hND₂ : IsRelPrime (toMvPolyQ s.num) (toMvPolyQ s.den) := isRelPrime_num_den s
  have hCc₁ : IsUnit (MvPolynomial.C (((ratNum r.factor).toInt : ℚ)
      * ((ratDen s.factor).toInt : ℚ)) : MvPolynomial (Fin n) ℚ) :=
    (isUnit_iff_ne_zero.mpr hc₁).map MvPolynomial.C
  have hCc₂ : IsUnit (MvPolynomial.C (((ratNum s.factor).toInt : ℚ)
      * ((ratDen r.factor).toInt : ℚ)) : MvPolynomial (Fin n) ℚ) :=
    (isUnit_iff_ne_zero.mpr hc₂).map MvPolynomial.C
  have hφR : algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
      (MvPolynomial.C (((ratDen r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
        * (toMvPolyQ r.den * toMvPolyQ s.den)) ≠ 0 :=
    algebraMap_ne_zero_of_ne (mul_ne_zero
      (fun h => (mul_ne_zero hβ₁ hβ₂) (MvPolynomial.C_eq_zero.mp h))
      (mul_ne_zero (toMvPolyQ_den_ne_zero r) (toMvPolyQ_den_ne_zero s)))
  by_cases hdeg : (signNorm (AzMvPolynomial.gcd r.den s.den)).totalDegree = 0
  · -- ═══ fast path: coprime denominator parts ═══
    have hcop_dd : AzMvPolynomial.coprime r.den s.den = true := by
      rw [AzMvPolynomial.coprime, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
      exact ⟨gcd_ne_zero_left (den_ne_zero r), by rw [← signNorm_totalDegree]; exact hdeg⟩
    have hDD : IsRelPrime (toMvPolyQ r.den) (toMvPolyQ s.den) := by
      rw [toMvPolyQ_eq_ratImg, toMvPolyQ_eq_ratImg]
      exact coprime_isRelPrime hcop_dd
    by_cases hT : fastT r s = 0
    · -- the combination vanishes: both sides are `0`
      have hres : add r s = 0 := by
        simp only [add, if_neg hr, if_neg hs, ratNum_def, ratDen_def, fastT_def,
          if_pos hdeg]
        rw [if_pos hT]
      rw [hres, toMvRatFunc_zero, sum_eq r s, ← toMvPolyQ_fastT r s, hT, toMvPolyQ_zero,
        map_zero, zero_div]
    · -- guard discharge and value
      have hTD₁ : IsRelPrime (toMvPolyQ (fastT r s)) (toMvPolyQ r.den) := by
        have hbase : IsRelPrime
            (MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
              * (toMvPolyQ r.num * toMvPolyQ s.den)) (toMvPolyQ r.den) :=
          hCc₁.isRelPrime_left.mul_left (hND₁.mul_left hDD.symm)
        have h1 := hbase.add_mul_right_left
          (MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
            * toMvPolyQ s.num)
        have hshape : toMvPolyQ (fastT r s)
            = MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
                * (toMvPolyQ r.num * toMvPolyQ s.den)
              + (MvPolynomial.C (((ratNum s.factor).toInt : ℚ)
                  * ((ratDen r.factor).toInt : ℚ)) * toMvPolyQ s.num) * toMvPolyQ r.den := by
          rw [toMvPolyQ_fastT]; ring
        rw [← hshape] at h1
        exact h1
      have hTD₂ : IsRelPrime (toMvPolyQ (fastT r s)) (toMvPolyQ s.den) := by
        have hbase : IsRelPrime
            (MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
              * (toMvPolyQ s.num * toMvPolyQ r.den)) (toMvPolyQ s.den) :=
          hCc₂.isRelPrime_left.mul_left (hND₂.mul_left hDD)
        have h1 := hbase.add_mul_right_left
          (MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
            * toMvPolyQ r.num)
        have hshape : toMvPolyQ (fastT r s)
            = MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
                * (toMvPolyQ s.num * toMvPolyQ r.den)
              + (MvPolynomial.C (((ratNum r.factor).toInt : ℚ)
                  * ((ratDen s.factor).toInt : ℚ)) * toMvPolyQ r.num) * toMvPolyQ s.den := by
          rw [toMvPolyQ_fastT]; ring
        rw [← hshape] at h1
        exact h1
      have hcop : AzMvPolynomial.coprime (primPos (fastT r s)) (r.den * s.den) = true := by
        apply coprime_of_isRelPrime
        rw [← toMvPolyQ_eq_ratImg (primPos (fastT r s)), ← toMvPolyQ_eq_ratImg (r.den * s.den),
          toMvPolyQ_mul]
        exact (hTD₁.mul_right hTD₂).of_dvd_left (map_dvd toMvPolyQHom (primPos_dvd (fastT r s)))
      have h1g : (primPos (fastT r s)).intContent = 1 := intContent_primPos hT
      have h2g : (r.den * s.den).intContent = 1 := by
        rw [intContent_mul, r.den_primitive, s.den_primitive,
          mul_one]
      have h3g : (0 : AzInt) < (primPos (fastT r s)).leadingCoeff := leadingCoeff_primPos_pos hT
      have h4g : (0 : AzInt) < (r.den * s.den).leadingCoeff := by
        rw [leadingCoeff_mul (den_ne_zero r) (den_ne_zero s)]
        exact mul_pos r.den_lc_pos s.den_lc_pos
      have h6g : AzRat.ofAzInts (signedIntContent (fastT r s))
          (ratDen r.factor * ratDen s.factor) = 0
          → primPos (fastT r s) = 1 ∧ r.den * s.den = 1 :=
        fun h0 => absurd h0 (ofAzInts_ne_zero (signedIntContent_ne_zero hT) hbbAz)
      have hres : add r s = ⟨AzRat.ofAzInts (signedIntContent (fastT r s))
          (ratDen r.factor * ratDen s.factor),
          primPos (fastT r s), r.den * s.den, h1g, h2g, h3g, h4g, hcop, h6g⟩ := by
        simp only [add, if_neg hr, if_neg hs, ratNum_def, ratDen_def, fastT_def, if_pos hdeg]
        rw [if_neg hT, dif_pos (⟨h1g, h2g, h3g, h4g, hcop, h6g⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)]
      have hφL : algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (MvPolynomial.C (((ratDen r.factor * ratDen s.factor).toInt : ℚ))
            * toMvPolyQ (r.den * s.den)) ≠ 0 :=
        algebraMap_ne_zero_of_ne (mul_ne_zero
          (fun h => hbb0 (Int.cast_eq_zero.mp (MvPolynomial.C_eq_zero.mp h)))
          (by rw [toMvPolyQ_mul]
              exact mul_ne_zero (toMvPolyQ_den_ne_zero r) (toMvPolyQ_den_ne_zero s)))
      have hpoly : (MvPolynomial.C ((signedIntContent (fastT r s)).toInt : ℚ)
            * toMvPolyQ (primPos (fastT r s)))
            * (MvPolynomial.C (((ratDen r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
              * (toMvPolyQ r.den * toMvPolyQ s.den))
          = (MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
              * (toMvPolyQ r.num * toMvPolyQ s.den)
            + MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
              * (toMvPolyQ s.num * toMvPolyQ r.den))
            * (MvPolynomial.C (((ratDen r.factor * ratDen s.factor).toInt : ℚ))
              * toMvPolyQ (r.den * s.den)) := by
        rw [primPos_toMvPolyQ, ← toMvPolyQ_fastT, toMvPolyQ_mul,
          Azurite.AzInt.toInt_mul, Int.cast_mul]
      rw [hres]
      show algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ))
          (Azurite.AzRat.toRat (AzRat.ofAzInts (signedIntContent (fastT r s))
            (ratDen r.factor * ratDen s.factor)))
          * (algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
              (toMvPolyQ (primPos (fastT r s)))
            / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
              (toMvPolyQ (r.den * s.den))) = _
      rw [Azurite.AzRat.toRat_ofAzInts, sum_eq r s, map_div₀, algebraMapQ_C, algebraMapQ_C,
        div_mul_div_comm, ← map_mul, ← map_mul, div_eq_div_iff hφL hφR, ← map_mul, ← map_mul]
      exact congrArg _ hpoly
  · -- ═══ Knuth path: reduce by `G = signNorm (gcd D₁ D₂)`, then `H = signNorm (gcd T₀ G)` ═══
    have hGa : signNorm (AzMvPolynomial.gcd r.den s.den) ∣ r.den :=
      (signNorm_dvd _).trans (gcd_dvd_left _ _)
    have hGb : signNorm (AzMvPolynomial.gcd r.den s.den) ∣ s.den :=
      (signNorm_dvd _).trans (gcd_dvd_right _ _)
    have hG0 : signNorm (AzMvPolynomial.gcd r.den s.den) ≠ 0 :=
      signNorm_ne_zero (gcd_ne_zero_left (den_ne_zero r))
    have hGlc : 0 < leadingCoeff (signNorm (AzMvPolynomial.gcd r.den s.den)) :=
      leadingCoeff_signNorm_pos (gcd_ne_zero_left (den_ne_zero r))
    have hD₁id : slowD₁ r s * signNorm (AzMvPolynomial.gcd r.den s.den) = r.den :=
      Azurite.ExactDiv.exactDiv_mul_self r.den _ hGa hG0
    have hD₂id : slowD₂ r s * signNorm (AzMvPolynomial.gcd r.den s.den) = s.den :=
      Azurite.ExactDiv.exactDiv_mul_self s.den _ hGb hG0
    have hD₁0 : slowD₁ r s ≠ 0 := fun h0 => den_ne_zero r (by rw [← hD₁id, h0, zero_mul])
    have hD₂0 : slowD₂ r s ≠ 0 := fun h0 => den_ne_zero s (by rw [← hD₂id, h0, zero_mul])
    have hD₁idQ : toMvPolyQ (slowD₁ r s) * toMvPolyQ (signNorm (AzMvPolynomial.gcd r.den s.den))
        = toMvPolyQ r.den := by rw [← toMvPolyQ_mul, hD₁id]
    have hD₂idQ : toMvPolyQ (slowD₂ r s) * toMvPolyQ (signNorm (AzMvPolynomial.gcd r.den s.den))
        = toMvPolyQ s.den := by rw [← toMvPolyQ_mul, hD₂id]
    have hND₁' : IsRelPrime (toMvPolyQ r.num) (toMvPolyQ (slowD₁ r s)) :=
      hND₁.of_dvd_right (map_dvd toMvPolyQHom ⟨_, hD₁id.symm⟩)
    have hND₂' : IsRelPrime (toMvPolyQ s.num) (toMvPolyQ (slowD₂ r s)) :=
      hND₂.of_dvd_right (map_dvd toMvPolyQHom ⟨_, hD₂id.symm⟩)
    have hDD' : IsRelPrime (toMvPolyQ (slowD₁ r s)) (toMvPolyQ (slowD₂ r s)) := by
      rw [toMvPolyQ_eq_ratImg, toMvPolyQ_eq_ratImg]
      exact coprime_isRelPrime (coprime_exactDiv_signNorm (den_ne_zero r) (den_ne_zero s))
    have hPfac : MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
          * (toMvPolyQ r.num * toMvPolyQ s.den)
        + MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
          * (toMvPolyQ s.num * toMvPolyQ r.den)
        = toMvPolyQ (signNorm (AzMvPolynomial.gcd r.den s.den)) * toMvPolyQ (slowT₀ r s) := by
      rw [← hD₁idQ, ← hD₂idQ, toMvPolyQ_slowT₀]; ring
    by_cases hT₀ : slowT₀ r s = 0
    · -- the combination vanishes: both sides are `0`
      have hres : add r s = 0 := by
        simp only [add, if_neg hr, if_neg hs, ratNum_def, ratDen_def, slowD₁_def,
          slowD₂_def, slowT₀_def, if_neg hdeg, if_pos hT₀]
        rw [if_pos trivial]
      rw [hres, toMvRatFunc_zero, sum_eq r s, hPfac, hT₀, toMvPolyQ_zero, mul_zero,
        map_zero, zero_div]
    · -- guard discharge and value
      have hHdvdT₀ : slowH r s ∣ slowT₀ r s := (signNorm_dvd _).trans (gcd_dvd_left _ _)
      have hHdvdG : slowH r s ∣ signNorm (AzMvPolynomial.gcd r.den s.den) :=
        (signNorm_dvd _).trans (gcd_dvd_right _ _)
      have hH0 : slowH r s ≠ 0 := signNorm_ne_zero (gcd_ne_zero_left hT₀)
      have hHlc : 0 < leadingCoeff (slowH r s) :=
        leadingCoeff_signNorm_pos (gcd_ne_zero_left hT₀)
      have hTid : slowT r s * slowH r s = slowT₀ r s :=
        Azurite.ExactDiv.exactDiv_mul_self (slowT₀ r s) _ hHdvdT₀ hH0
      have hT'0 : slowT r s ≠ 0 := fun h0 => hT₀ (by rw [← hTid, h0, zero_mul])
      have hHdvds : slowH r s ∣ s.den := hHdvdG.trans hGb
      have hD₂Hid : slowD₂H r s * slowH r s = s.den :=
        Azurite.ExactDiv.exactDiv_mul_self s.den _ hHdvds hH0
      have hD₂H0 : slowD₂H r s ≠ 0 := fun h0 => den_ne_zero s (by rw [← hD₂Hid, h0, zero_mul])
      have hGaz_id : Azurite.ExactDiv.exactDiv (signNorm (AzMvPolynomial.gcd r.den s.den))
            (slowH r s) * slowH r s = signNorm (AzMvPolynomial.gcd r.den s.den) :=
        Azurite.ExactDiv.exactDiv_mul_self _ _ hHdvdG hH0
      have hslowD₂H_eq : slowD₂H r s = slowD₂ r s
          * Azurite.ExactDiv.exactDiv (signNorm (AzMvPolynomial.gcd r.den s.den)) (slowH r s) := by
        apply mul_right_cancel₀ hH0
        rw [hD₂Hid, mul_assoc, hGaz_id, hD₂id]
      have hTidQ : toMvPolyQ (slowT r s) * toMvPolyQ (slowH r s) = toMvPolyQ (slowT₀ r s) := by
        rw [← toMvPolyQ_mul, hTid]
      have hD₂Hidentity : toMvPolyQ (slowD₂H r s) * toMvPolyQ (slowH r s) = toMvPolyQ s.den := by
        rw [← toMvPolyQ_mul, hD₂Hid]
      have hD₂Hsplit : toMvPolyQ (slowD₂H r s)
          = toMvPolyQ (slowD₂ r s)
            * toMvPolyQ (Azurite.ExactDiv.exactDiv
                (signNorm (AzMvPolynomial.gcd r.den s.den)) (slowH r s)) := by
        rw [hslowD₂H_eq, toMvPolyQ_mul]
      have hT'G'az : IsRelPrime (toMvPolyQ (slowT r s))
          (toMvPolyQ (Azurite.ExactDiv.exactDiv
            (signNorm (AzMvPolynomial.gcd r.den s.den)) (slowH r s))) := by
        rw [toMvPolyQ_eq_ratImg, toMvPolyQ_eq_ratImg]
        exact coprime_isRelPrime (coprime_exactDiv_signNorm hT₀ hG0)
      have hT₀D₁ : IsRelPrime (toMvPolyQ (slowT₀ r s)) (toMvPolyQ (slowD₁ r s)) := by
        have hbase : IsRelPrime
            (MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
              * (toMvPolyQ r.num * toMvPolyQ (slowD₂ r s))) (toMvPolyQ (slowD₁ r s)) :=
          hCc₁.isRelPrime_left.mul_left (hND₁'.mul_left hDD'.symm)
        have h1 := hbase.add_mul_right_left
          (MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
            * toMvPolyQ s.num)
        have hshape : toMvPolyQ (slowT₀ r s)
            = MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
                * (toMvPolyQ r.num * toMvPolyQ (slowD₂ r s))
              + (MvPolynomial.C (((ratNum s.factor).toInt : ℚ)
                  * ((ratDen r.factor).toInt : ℚ)) * toMvPolyQ s.num) * toMvPolyQ (slowD₁ r s) := by
          rw [toMvPolyQ_slowT₀]; ring
        rw [← hshape] at h1
        exact h1
      have hT₀D₂ : IsRelPrime (toMvPolyQ (slowT₀ r s)) (toMvPolyQ (slowD₂ r s)) := by
        have hbase : IsRelPrime
            (MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
              * (toMvPolyQ s.num * toMvPolyQ (slowD₁ r s))) (toMvPolyQ (slowD₂ r s)) :=
          hCc₂.isRelPrime_left.mul_left (hND₂'.mul_left hDD')
        have h1 := hbase.add_mul_right_left
          (MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
            * toMvPolyQ r.num)
        have hshape : toMvPolyQ (slowT₀ r s)
            = MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
                * (toMvPolyQ s.num * toMvPolyQ (slowD₁ r s))
              + (MvPolynomial.C (((ratNum r.factor).toInt : ℚ)
                  * ((ratDen s.factor).toInt : ℚ)) * toMvPolyQ r.num) * toMvPolyQ (slowD₂ r s) := by
          rw [toMvPolyQ_slowT₀]; ring
        rw [← hshape] at h1
        exact h1
      have hT'dvd : slowT r s ∣ slowT₀ r s := ⟨slowH r s, hTid.symm⟩
      have hT'D₁ := hT₀D₁.of_dvd_left (map_dvd toMvPolyQHom hT'dvd)
      have hT'D₂ := hT₀D₂.of_dvd_left (map_dvd toMvPolyQHom hT'dvd)
      have hT'D₂H : IsRelPrime (toMvPolyQ (slowT r s)) (toMvPolyQ (slowD₂H r s)) := by
        rw [hD₂Hsplit]; exact hT'D₂.mul_right hT'G'az
      have hcop : AzMvPolynomial.coprime (primPos (slowT r s))
          (slowD₁ r s * slowD₂H r s) = true := by
        apply coprime_of_isRelPrime
        rw [← toMvPolyQ_eq_ratImg (primPos (slowT r s)),
          ← toMvPolyQ_eq_ratImg (slowD₁ r s * slowD₂H r s), toMvPolyQ_mul]
        exact (hT'D₁.mul_right hT'D₂H).of_dvd_left
          (map_dvd toMvPolyQHom (primPos_dvd (slowT r s)))
      have h1g : (primPos (slowT r s)).intContent = 1 := intContent_primPos hT'0
      have h2g : (slowD₁ r s * slowD₂H r s).intContent = 1 := by
        rw [intContent_mul, intContent_exactDiv_eq_one hGa hG0 r.den_primitive,
          intContent_exactDiv_eq_one hHdvds hH0 s.den_primitive, mul_one]
      have h3g : (0 : AzInt) < (primPos (slowT r s)).leadingCoeff := leadingCoeff_primPos_pos hT'0
      have h4g : (0 : AzInt) < (slowD₁ r s * slowD₂H r s).leadingCoeff := by
        rw [leadingCoeff_mul hD₁0 hD₂H0]
        exact mul_pos (leadingCoeff_exactDiv_pos hGa hG0 hGlc r.den_lc_pos)
          (leadingCoeff_exactDiv_pos hHdvds hH0 hHlc s.den_lc_pos)
      have h6g : AzRat.ofAzInts (signedIntContent (slowT r s))
          (ratDen r.factor * ratDen s.factor) = 0
          → primPos (slowT r s) = 1 ∧ slowD₁ r s * slowD₂H r s = 1 :=
        fun h0 => absurd h0 (ofAzInts_ne_zero (signedIntContent_ne_zero hT'0) hbbAz)
      have hres : add r s = ⟨AzRat.ofAzInts (signedIntContent (slowT r s))
          (ratDen r.factor * ratDen s.factor),
          primPos (slowT r s), slowD₁ r s * slowD₂H r s, h1g, h2g, h3g, h4g, hcop, h6g⟩ := by
        simp only [add, if_neg hr, if_neg hs, ratNum_def, ratDen_def, slowD₁_def,
          slowD₂_def, slowT₀_def, slowH_def, slowT_def, slowD₂H_def, if_neg hdeg, if_neg hT₀]
        rw [if_neg hT'0, dif_pos (⟨h1g, h2g, h3g, h4g, hcop, h6g⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)]
      have hφL : algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (MvPolynomial.C (((ratDen r.factor * ratDen s.factor).toInt : ℚ))
            * toMvPolyQ (slowD₁ r s * slowD₂H r s)) ≠ 0 :=
        algebraMap_ne_zero_of_ne (mul_ne_zero
          (fun h => hbb0 (Int.cast_eq_zero.mp (MvPolynomial.C_eq_zero.mp h)))
          (by rw [toMvPolyQ_mul]
              exact mul_ne_zero (toMvPolyQ_ne_zero hD₁0) (toMvPolyQ_ne_zero hD₂H0)))
      have hpoly : (MvPolynomial.C ((signedIntContent (slowT r s)).toInt : ℚ)
            * toMvPolyQ (primPos (slowT r s)))
            * (MvPolynomial.C (((ratDen r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
              * (toMvPolyQ r.den * toMvPolyQ s.den))
          = (MvPolynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
              * (toMvPolyQ r.num * toMvPolyQ s.den)
            + MvPolynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
              * (toMvPolyQ s.num * toMvPolyQ r.den))
            * (MvPolynomial.C (((ratDen r.factor * ratDen s.factor).toInt : ℚ))
              * toMvPolyQ (slowD₁ r s * slowD₂H r s)) := by
        rw [primPos_toMvPolyQ, hPfac, ← hTidQ, ← hD₁idQ, ← hD₂Hidentity, toMvPolyQ_mul,
          Azurite.AzInt.toInt_mul, Int.cast_mul]
        ring
      rw [hres]
      show algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ))
          (Azurite.AzRat.toRat (AzRat.ofAzInts (signedIntContent (slowT r s))
            (ratDen r.factor * ratDen s.factor)))
          * (algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
              (toMvPolyQ (primPos (slowT r s)))
            / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
              (toMvPolyQ (slowD₁ r s * slowD₂H r s))) = _
      rw [Azurite.AzRat.toRat_ofAzInts, sum_eq r s, map_div₀, algebraMapQ_C, algebraMapQ_C,
        div_mul_div_comm, ← map_mul, ← map_mul, div_eq_div_iff hφL hφR, ← map_mul, ← map_mul]
      exact congrArg _ hpoly

/-- **Subtraction is correct**:
`toMvRatFunc (r - s) = toMvRatFunc r - toMvRatFunc s`. -/
theorem toMvRatFunc_sub (r s : AzMvRationalFunction n ord) :
    toMvRatFunc (r - s) = toMvRatFunc r - toMvRatFunc s := by
  show toMvRatFunc (r + -s) = _
  rw [toMvRatFunc_add, toMvRatFunc_neg, sub_eq_add_neg]

/-- `ofMvRatFunc` version: pulling back a sum. -/
theorem ofMvRatFunc_add (f g : FractionRing (MvPolynomial (Fin n) ℚ)) :
    ofMvRatFunc (f + g) = (ofMvRatFunc f : AzMvRationalFunction n ord) + ofMvRatFunc g :=
  toMvRatFunc_injective (by
    rw [toMvRatFunc_ofMvRatFunc, toMvRatFunc_add, toMvRatFunc_ofMvRatFunc, toMvRatFunc_ofMvRatFunc])

/-- `ofMvRatFunc` version: pulling back a difference. -/
theorem ofMvRatFunc_sub (f g : FractionRing (MvPolynomial (Fin n) ℚ)) :
    ofMvRatFunc (f - g) = (ofMvRatFunc f : AzMvRationalFunction n ord) - ofMvRatFunc g :=
  toMvRatFunc_injective (by
    rw [toMvRatFunc_ofMvRatFunc, toMvRatFunc_sub, toMvRatFunc_ofMvRatFunc, toMvRatFunc_ofMvRatFunc])

/-! ### Exponentiation -/

end Azurite.AzMvRationalFunction

namespace Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- `intContent` of a power is the power of the `intContent` (Gauss, iterated). -/
theorem intContent_pow {P : AzMvPolynomial n AzInt ord} (m : ℕ) :
    intContent (P ^ m) = intContent P ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ k ih => rw [pow_succ, pow_succ, intContent_mul, ih]

/-- `leadingCoeff` of a power is the power of the `leadingCoeff`. -/
theorem leadingCoeff_pow {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) (m : ℕ) :
    leadingCoeff (P ^ m) = leadingCoeff P ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ k ih => rw [pow_succ, pow_succ, leadingCoeff_mul (pow_ne_zero k hP) hP, ih]

end Azurite.AzMvPolynomial

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- The `ℚ[x⃗]`-image commutes with powers. -/
theorem toMvPolyQ_pow (P : AzMvPolynomial n AzInt ord) (m : ℕ) :
    toMvPolyQ (P ^ m) = toMvPolyQ P ^ m := map_pow toMvPolyQHom P m

set_option maxHeartbeats 1600000 in
/-- **Exponentiation by `ℕ` is correct**: `toMvRatFunc (pow r m) = toMvRatFunc r ^ m`
— in particular the componentwise constructor's invariant checks always pass
(the fallback `0` branch is unreachable). -/
theorem toMvRatFunc_pow (r : AzMvRationalFunction n ord) (m : ℕ) :
    toMvRatFunc (pow r m) = toMvRatFunc r ^ m := by
  have h1g : (r.num ^ m).intContent = 1 := by
    rw [intContent_pow, r.num_primitive, one_pow]
  have h2g : (r.den ^ m).intContent = 1 := by
    rw [intContent_pow, r.den_primitive, one_pow]
  have h3g : (0 : AzInt) < (r.num ^ m).leadingCoeff := by
    rw [leadingCoeff_pow (num_ne_zero r)]; exact pow_pos r.num_lc_pos m
  have h4g : (0 : AzInt) < (r.den ^ m).leadingCoeff := by
    rw [leadingCoeff_pow (den_ne_zero r)]; exact pow_pos r.den_lc_pos m
  have h5g : AzMvPolynomial.coprime (r.num ^ m) (r.den ^ m) = true := by
    apply coprime_of_isRelPrime
    rw [← toMvPolyQ_eq_ratImg, ← toMvPolyQ_eq_ratImg, toMvPolyQ_pow, toMvPolyQ_pow]
    have hrel : IsRelPrime (toMvPolyQ r.num) (toMvPolyQ r.den) := by
      rw [toMvPolyQ_eq_ratImg, toMvPolyQ_eq_ratImg]
      exact coprime_isRelPrime r.reduced
    exact hrel.pow
  have h6g : r.factor.pow m = 0 → r.num ^ m = 1 ∧ r.den ^ m = 1 := by
    intro h0
    have h1 := congrArg Azurite.AzRat.toRat h0
    rw [Azurite.AzRat.toRat_pow, Azurite.AzRat.toRat_zero] at h1
    have hm0 : m ≠ 0 := by intro hm; subst hm; rw [pow_zero] at h1; exact one_ne_zero h1
    have hf0 : r.factor = 0 :=
      Azurite.AzRat.toRat_injective (by
        rw [(pow_eq_zero_iff hm0).mp h1, Azurite.AzRat.toRat_zero])
    obtain ⟨hn1, hd1⟩ := r.zero_norm hf0
    rw [hn1, hd1]; exact ⟨one_pow m, one_pow m⟩
  have hres : pow r m
      = ⟨r.factor.pow m, r.num ^ m, r.den ^ m, h1g, h2g, h3g, h4g, h5g, h6g⟩ := by
    simp only [pow]
    rw [dif_pos (⟨h1g, h2g, h3g, h4g, h5g, h6g⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)]
  rw [hres]
  show algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ))
        (Azurite.AzRat.toRat (r.factor.pow m))
      * (algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
            (toMvPolyQ (r.num ^ m))
        / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
            (toMvPolyQ (r.den ^ m))) = _
  rw [toMvRatFunc, Azurite.AzRat.toRat_pow, toMvPolyQ_pow, toMvPolyQ_pow, map_pow, map_pow,
    map_pow, ← div_pow, ← mul_pow]

/-- **Exponentiation by `ℤ` is correct**: `toMvRatFunc (zpow r z) = toMvRatFunc r ^ z`
(`zpow` of a negative exponent is the reciprocal of the positive power). -/
theorem toMvRatFunc_zpow (r : AzMvRationalFunction n ord) (z : ℤ) :
    toMvRatFunc (zpow r z) = toMvRatFunc r ^ z := by
  rw [zpow]
  by_cases hz : 0 ≤ z
  · rw [if_pos hz, toMvRatFunc_pow, ← zpow_natCast, Int.toNat_of_nonneg hz]
  · rw [if_neg hz, toMvRatFunc_inv, toMvRatFunc_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega), ← zpow_neg, neg_neg]

/-- `ofMvRatFunc` version: pulling back a `ℕ`-power. -/
theorem ofMvRatFunc_pow (f : FractionRing (MvPolynomial (Fin n) ℚ)) (m : ℕ) :
    ofMvRatFunc (f ^ m) = pow (ofMvRatFunc f : AzMvRationalFunction n ord) m :=
  toMvRatFunc_injective (by
    rw [toMvRatFunc_ofMvRatFunc, toMvRatFunc_pow, toMvRatFunc_ofMvRatFunc])

/-- `ofMvRatFunc` version: pulling back a `ℤ`-power. -/
theorem ofMvRatFunc_zpow (f : FractionRing (MvPolynomial (Fin n) ℚ)) (z : ℤ) :
    ofMvRatFunc (f ^ z) = zpow (ofMvRatFunc f : AzMvRationalFunction n ord) z :=
  toMvRatFunc_injective (by
    rw [toMvRatFunc_ofMvRatFunc, toMvRatFunc_zpow, toMvRatFunc_ofMvRatFunc])

end Azurite.AzMvRationalFunction
