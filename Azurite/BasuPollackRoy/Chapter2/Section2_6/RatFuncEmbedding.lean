import Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxSeries
import Azurite.BasuPollackRoy.Chapter2.Section2_1.OrderZeroPlus

/-! # BPR §2.6 — `K(ε)` with the `0₊` order embeds in `K⟨⟨ε⟩⟩`

The field of rational functions `K(ε) = RatFunc K`, equipped with the `0₊` order
(`Azurite.BPR.ZeroPlus`, BPR Notation 2.5), is an ordered subfield of the field of Puiseux
series `K⟨⟨ε⟩⟩`, via the Laurent expansion about `0`.

The key fact is that the `0₊` order matches the Laurent/Puiseux order: a rational function is
positive in `0₊` exactly when the initial (lowest-order) coefficient of its Laurent expansion
is positive. We establish this by computing the leading coefficient of the Laurent series of a
polynomial: it is the polynomial's *trailing* coefficient (the lowest-degree nonzero one),
which is exactly what `0₊`-positivity is about.
-/

open Polynomial HahnSeries

namespace Azurite.BPR

variable {F : Type*} [Field F]

/-- The coefficient of the Laurent-series coercion of a polynomial `P`, at index `n : ℤ`. -/
theorem coe_poly_coeff (P : F[X]) (n : ℤ) :
    (((P : PowerSeries F) : LaurentSeries F)).coeff n = if n < 0 then 0 else P.coeff n.natAbs := by
  rw [PowerSeries.coeff_coe]
  split <;> simp [Polynomial.coeff_coe]

/-- **The order of the Laurent expansion of a nonzero polynomial is its trailing degree.** -/
theorem coe_poly_order (P : F[X]) (hP : P ≠ 0) :
    (((P : PowerSeries F) : LaurentSeries F)).order = (P.natTrailingDegree : ℤ) := by
  have hcoeff : (((P : PowerSeries F) : LaurentSeries F)).coeff (P.natTrailingDegree : ℤ)
      = P.trailingCoeff := by
    rw [coe_poly_coeff, if_neg (by simp)]; simp [Polynomial.trailingCoeff]
  have hcoeff_ne : (((P : PowerSeries F) : LaurentSeries F)).coeff (P.natTrailingDegree : ℤ) ≠ 0 := by
    rw [hcoeff]; exact mt Polynomial.trailingCoeff_eq_zero.mp hP
  have hne : ((P : PowerSeries F) : LaurentSeries F) ≠ 0 :=
    HahnSeries.ne_zero_of_coeff_ne_zero hcoeff_ne
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hcoeff_ne) ?_
  rw [HahnSeries.le_order_iff_forall hne]
  intro j hj
  rw [coe_poly_coeff]
  split
  · rfl
  · rename_i hjnn
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega)

/-- **The leading coefficient of the Laurent expansion of a nonzero polynomial is its trailing
coefficient.** -/
theorem coe_poly_leadingCoeff (P : F[X]) (hP : P ≠ 0) :
    (((P : PowerSeries F) : LaurentSeries F)).leadingCoeff = P.trailingCoeff := by
  rw [HahnSeries.leadingCoeff_eq, coe_poly_order P hP, coe_poly_coeff, if_neg (by simp)]
  simp [Polynomial.trailingCoeff]

/-- The leading coefficient of an inverse in `LaurentSeries F` is the inverse of the leading
coefficient. -/
theorem leadingCoeff_inv {a : LaurentSeries F} (ha : a ≠ 0) :
    a⁻¹.leadingCoeff = a.leadingCoeff⁻¹ := by
  have h : a.leadingCoeff * a⁻¹.leadingCoeff = 1 := by
    rw [← HahnSeries.leadingCoeff_mul, mul_inv_cancel₀ ha, HahnSeries.leadingCoeff_one]
  exact (inv_eq_of_mul_eq_one_right h).symm

/-- The leading coefficient of a quotient in `LaurentSeries F` is the quotient of the leading
coefficients. -/
theorem leadingCoeff_div (a : LaurentSeries F) {b : LaurentSeries F} (hb : b ≠ 0) :
    (a / b).leadingCoeff = a.leadingCoeff / b.leadingCoeff := by
  rw [div_eq_mul_inv, HahnSeries.leadingCoeff_mul, leadingCoeff_inv hb, div_eq_mul_inv]

/-- The Laurent coercion of a nonzero polynomial is nonzero. -/
theorem coe_poly_ne_zero {P : F[X]} (hP : P ≠ 0) :
    ((P : PowerSeries F) : LaurentSeries F) ≠ 0 :=
  HahnSeries.leadingCoeff_ne_zero.mp (by
    rw [coe_poly_leadingCoeff P hP]; exact mt Polynomial.trailingCoeff_eq_zero.mp hP)

/-- **The leading coefficient of the Laurent expansion of a rational function** is the ratio of
the trailing coefficients of its numerator and denominator. -/
theorem coe_ratFunc_leadingCoeff {r : RatFunc F} (hr : r ≠ 0) :
    ((r : LaurentSeries F)).leadingCoeff = r.num.trailingCoeff / r.denom.trailingCoeff := by
  have hnum := RatFunc.num_ne_zero hr
  have hden := RatFunc.denom_ne_zero r
  have hcoe : (r : LaurentSeries F)
      = ((r.num : PowerSeries F) : LaurentSeries F) / ((r.denom : PowerSeries F) : LaurentSeries F) := by
    conv_lhs => rw [← RatFunc.num_div_denom r,
      show (algebraMap F[X] (RatFunc F) r.num) = (r.num : RatFunc F) from rfl,
      show (algebraMap F[X] (RatFunc F) r.denom) = (r.denom : RatFunc F) from rfl]
    rw [map_div₀, ← RatFunc.coe_coe, ← RatFunc.coe_coe]
  rw [hcoe, leadingCoeff_div _ (coe_poly_ne_zero hden),
    coe_poly_leadingCoeff r.num hnum, coe_poly_leadingCoeff r.denom hden]

/-! ## Embedding `K(ε)` into the Puiseux series `K⟨⟨ε⟩⟩`

The Laurent expansion `K(ε) → K((ε)) = LaurentSeries F`, followed by the exponent-preserving
inclusion `puiseuxEmb F 1 : K((ε)) → K⟨⟨ε⟩⟩` (`ε^{1/1} = ε`), realizes `K(ε)` as a subfield of
`K⟨⟨ε⟩⟩`.
-/

/-- **`embDomain` along an order embedding preserves the leading coefficient.** The leading
coefficient is the coefficient at the (mapped) least exponent. -/
theorem leadingCoeff_embDomain {f : ℤ ↪o ℚ} (x : HahnSeries ℤ F) :
    (HahnSeries.embDomain f x).leadingCoeff = x.leadingCoeff := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hne : HahnSeries.embDomain f x ≠ 0 := by
      simpa using (HahnSeries.embDomain_injective (f := f)).ne hx
    have horder : (HahnSeries.embDomain f x).order = f x.order := by
      have h := HahnSeries.orderTop_embDomain (f := f) (x := x)
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne,
        ← HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.map_coe] at h
      exact_mod_cast h
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, horder,
      HahnSeries.embDomain_coeff]

/-- The Puiseux embedding `puiseuxEmb F q` preserves leading coefficients. -/
theorem puiseuxEmb_leadingCoeff (q : ℕ+) (x : HahnSeries ℤ F) :
    (puiseuxEmb F q x).leadingCoeff = x.leadingCoeff := by
  rw [puiseuxEmb, HahnSeries.embDomainRingHom_apply]
  exact leadingCoeff_embDomain x

/-- The Laurent expansion of a rational function, viewed in `K⟨⟨ε⟩⟩` (it is a Laurent series in
`ε^{1/1} = ε`). -/
theorem coe_mem_puiseuxSeries (r : RatFunc F) :
    puiseuxEmb F 1 (r : LaurentSeries F) ∈ PuiseuxSeries F := by
  rw [mem_puiseuxSeries_iff]
  exact ⟨1, RingHom.mem_fieldRange.mpr ⟨(r : LaurentSeries F), rfl⟩⟩

/-- **The embedding of `K(ε)` into `K⟨⟨ε⟩⟩`** via Laurent expansion about `0`. -/
noncomputable def ratFuncToPuiseux (r : RatFunc F) : PuiseuxSeries F :=
  ⟨puiseuxEmb F 1 (r : LaurentSeries F), coe_mem_puiseuxSeries r⟩

@[simp] theorem ratFuncToPuiseux_coe (r : RatFunc F) :
    (ratFuncToPuiseux r : HahnSeries ℚ F) = puiseuxEmb F 1 (r : LaurentSeries F) := rfl

theorem ratFuncToPuiseux_zero : ratFuncToPuiseux (0 : RatFunc F) = 0 := by
  apply Subtype.ext; simp

theorem ratFuncToPuiseux_one : ratFuncToPuiseux (1 : RatFunc F) = 1 := by
  apply Subtype.ext; simp [map_one]

theorem ratFuncToPuiseux_add (r s : RatFunc F) :
    ratFuncToPuiseux (r + s) = ratFuncToPuiseux r + ratFuncToPuiseux s := by
  apply Subtype.ext; simp [Subfield.coe_add, map_add]

theorem ratFuncToPuiseux_mul (r s : RatFunc F) :
    ratFuncToPuiseux (r * s) = ratFuncToPuiseux r * ratFuncToPuiseux s := by
  apply Subtype.ext; simp [Subfield.coe_mul, map_mul]

theorem ratFuncToPuiseux_sub (r s : RatFunc F) :
    ratFuncToPuiseux (r - s) = ratFuncToPuiseux r - ratFuncToPuiseux s := by
  apply Subtype.ext; simp [map_sub]

/-- The embedding `K(ε) ↪ K⟨⟨ε⟩⟩` as a ring homomorphism. -/
noncomputable def ratFuncToPuiseuxHom (F : Type*) [Field F] : RatFunc F →+* PuiseuxSeries F where
  toFun := ratFuncToPuiseux
  map_one' := ratFuncToPuiseux_one
  map_mul' := ratFuncToPuiseux_mul
  map_zero' := ratFuncToPuiseux_zero
  map_add' := ratFuncToPuiseux_add

@[simp] theorem ratFuncToPuiseuxHom_apply (r : RatFunc F) :
    ratFuncToPuiseuxHom F r = ratFuncToPuiseux r := rfl

/-! ## The `0₊` order matches the Laurent leading coefficient

When `F` is an ordered field, the `0₊` order on `K(ε) = RatFunc F` (BPR Notation 2.5,
`Azurite.BPR.ZeroPlus`) agrees with the sign of the leading coefficient of the Laurent
expansion. This is the order-compatibility that makes `K(ε)` an *ordered* subfield of the
Puiseux series `K⟨⟨ε⟩⟩`.
-/

section Ordered

variable [LinearOrder F] [IsStrictOrderedRing F]

open ZeroPlus

/-- **The `0₊` order is the sign of the Laurent leading coefficient.** A rational function is
positive in the `0₊` order exactly when the leading coefficient of its Laurent expansion about
`0` is positive. -/
theorem rfPos_iff_leadingCoeff_pos (r : RatFunc F) :
    rfPos r ↔ 0 < (r : LaurentSeries F).leadingCoeff := by
  by_cases hr : r = 0
  · subst hr
    simp only [show ((0 : RatFunc F) : LaurentSeries F) = 0 from by simp,
      HahnSeries.leadingCoeff_zero, lt_self_iff_false, iff_false]
    simp [rfPos, polyPos]
  · rw [rfPos_def, coe_ratFunc_leadingCoeff hr, Polynomial.trailingCoeff_mul,
      and_iff_right hr, div_pos_iff, mul_pos_iff]

/-- **`0₊`-positivity of `K(ε)` agrees with Puiseux positivity.** The leading coefficient of the
Laurent expansion is the Puiseux initial coefficient `In`, whose sign is the `0₊` order. -/
theorem rfPos_iff_pos {r s : RatFunc F} (h : r < s) :
    0 < ((s : LaurentSeries F) - (r : LaurentSeries F)).leadingCoeff := by
  rw [rf_lt_def] at h
  have := (rfPos_iff_leadingCoeff_pos (s - r)).mp h
  rwa [map_sub] at this

/-- **The Laurent-expansion embedding `K(ε) → K⟨⟨ε⟩⟩` is strictly monotone** in the `0₊` order:
the `0₊` order on `K(ε)` is exactly the restriction of the Puiseux order. -/
theorem ratFuncToPuiseux_strictMono :
    StrictMono (ratFuncToPuiseux : RatFunc F → PuiseuxSeries F) := by
  intro r s hrs
  rw [← sub_pos, ← ratFuncToPuiseux_sub, puiseux_pos_iff]
  show 0 < HahnSeries.leadingCoeff ((ratFuncToPuiseux (s - r) : PuiseuxSeries F) : HahnSeries ℚ F)
  rw [ratFuncToPuiseux_coe, puiseuxEmb_leadingCoeff, ← rfPos_iff_leadingCoeff_pos]
  exact rf_lt_def.mp hrs

/-- The embedding `K(ε) → K⟨⟨ε⟩⟩` is injective. -/
theorem ratFuncToPuiseux_injective :
    Function.Injective (ratFuncToPuiseux : RatFunc F → PuiseuxSeries F) :=
  ratFuncToPuiseux_strictMono.injective

/-- **The Laurent-expansion embedding is an order embedding** `K(ε) ↪o K⟨⟨ε⟩⟩`: the `0₊` order
on `K(ε)` is the order induced from the Puiseux order. -/
theorem ratFuncToPuiseux_lt_iff {r s : RatFunc F} :
    ratFuncToPuiseux r < ratFuncToPuiseux s ↔ r < s :=
  ratFuncToPuiseux_strictMono.lt_iff_lt

end Ordered

end Azurite.BPR
