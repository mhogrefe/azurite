import Azurite.BasuPollackRoy.Chapter2.Section2_6.RatFuncEmbedding
import Mathlib.RingTheory.HahnSeries.Binomial
import Mathlib.RingTheory.HahnSeries.HEval
import Mathlib.FieldTheory.IsRealClosed.Basic

/-! # BPR §2.6 Lemma 2.93 — positive elements of `R⟨⟨ε⟩⟩` are squares

For `R` a real closed field, every positive element of the ordered field of Puiseux series
`R⟨⟨ε⟩⟩` is a square. Following BPR: write a positive `ā = a_k ε^{k/q}(1 + b̄)` with `a_k > 0`
and `o(b̄) > 0`; the square root of `1 + b̄` is the Taylor expansion `(1 + b̄)^{1/2}`, and since
`R` is real closed `√a_k ∈ R`, so `√a_k · ε^{k/(2q)} · (1 + b̄)^{1/2}` is a square root of `ā`.

The Taylor expansion `(1 + b̄)^{1/2}` is realized by Mathlib's `PowerSeries.heval` (evaluation of
the binomial power series at the positive-order series `b̄`), with `(1+X)^{1/2}` squaring to
`1 + X` via `binomialSeries_add`. The construction is carried out one denominator `q` lower (the
`(1+b̄)^{1/2}` part needs no finer exponents), and only the leading monomial requires the finer
denominator `2q`; this keeps everything inside the bounded-denominator subfield `R⟨⟨ε⟩⟩`.
-/

namespace Azurite.BPR

open HahnSeries PowerSeries

variable {R : Type*} [Field R]

/-- `puiseuxEmb` of a single term scales the exponent by `1/q`. -/
theorem puiseuxEmb_single (q : ℕ+) (g : ℤ) (r : R) :
    puiseuxEmb R q (HahnSeries.single g r) = HahnSeries.single (puiseuxExpHom q g) r := by
  rw [puiseuxEmb, HahnSeries.embDomainRingHom_apply, HahnSeries.embDomain_single]; rfl

variable [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A positive element of a real closed field is a square. -/
theorem isSquare_of_pos {x : R} (hx : 0 < x) : IsSquare x := by
  rcases IsRealClosed.isSquare_or_isSquare_neg x with h | h
  · exact h
  · obtain ⟨t, ht⟩ := h; exfalso; nlinarith [mul_self_nonneg t]

/-- **BPR Lemma 2.93.** A positive element of `R⟨⟨ε⟩⟩` is the square of an element of
`R⟨⟨ε⟩⟩`. -/
theorem lemma_2_93 {a : PuiseuxSeries R} (ha : 0 < a) : IsSquare a := by
  -- Pull `a` back to a Laurent series `a'` in `ε^{1/q}` (denominator `q`).
  have ha2 := a.2
  rw [mem_puiseuxSeries_iff] at ha2
  obtain ⟨q, hq⟩ := ha2
  rw [puiseuxSubfield, RingHom.mem_fieldRange] at hq
  obtain ⟨a', ha'⟩ := hq
  -- The leading coefficient `k = In(a')` is positive.
  have hlc : 0 < a'.leadingCoeff := by
    have h := (puiseux_pos_iff a).mp ha
    simp only [puiseuxInitCoeff] at h
    rwa [← ha', puiseuxEmb_leadingCoeff] at h
  set k := a'.leadingCoeff with hk
  have hk_ne : k ≠ 0 := ne_of_gt hlc
  have ha'_ne : a' ≠ 0 := fun h => hk_ne (by rw [hk, h, HahnSeries.leadingCoeff_zero])
  set γ := a'.order with hγ
  -- `d' := ε^{-k/q} a'` has order `0` and leading coefficient `1`, so `b' := d' - 1` is small.
  have hd_lead : (HahnSeries.single (-γ) k⁻¹ * a').leadingCoeff = 1 := by
    rw [HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_of_single, inv_mul_cancel₀ hk_ne]
  have hd_ord : (HahnSeries.single (-γ) k⁻¹ * a').orderTop = 0 := by
    rw [HahnSeries.orderTop_mul, HahnSeries.orderTop_single (inv_ne_zero hk_ne),
      ← HahnSeries.order_eq_orderTop_of_ne_zero ha'_ne, ← hγ, ← WithTop.coe_add]
    simp
  set b' := HahnSeries.single (-γ) k⁻¹ * a' - 1 with hb'def
  have hb'_pos : 0 < b'.orderTop :=
    (HahnSeries.orderTop_self_sub_one_pos_iff _).mpr ⟨hd_ord, hd_lead⟩
  -- `c' := (1 + b')^{1/2}` satisfies `c'^2 = 1 + b'`.
  set c' := PowerSeries.heval b' (PowerSeries.binomialSeries R (1 / 2 : R)) with hc'def
  have hc'2 : c' ^ 2 = 1 + b' := by
    have h2 : (1 / 2 : R) + 1 / 2 = 1 := by norm_num
    rw [hc'def, sq, ← map_mul, ← PowerSeries.binomialSeries_add, h2, ← Nat.cast_one (R := R),
      PowerSeries.binomialSeries_nat, pow_one, map_add, map_one, PowerSeries.heval_X b' hb'_pos]
  -- `a' = ε^{k/q} k · d' = single γ k · (1 + b')`.
  have hsum1 : (1 : HahnSeries ℤ R) + b' = HahnSeries.single (-γ) k⁻¹ * a' := by
    rw [hb'def]; ring
  have hdecomp : HahnSeries.single γ k * (1 + b') = a' := by
    rw [hsum1, ← mul_assoc, HahnSeries.single_mul_single, add_neg_cancel,
      mul_inv_cancel₀ hk_ne, HahnSeries.single_zero_one, one_mul]
  -- `√k ∈ R`.
  obtain ⟨s, hs⟩ := isSquare_of_pos hlc
  -- Assemble the square root `cval = ε^{k/(2q)} √k · (1 + b')^{1/2}` at denominator `2q`.
  set q2 : ℕ+ := 2 * q with hq2
  set cval : HahnSeries ℚ R :=
    puiseuxEmb R q2 (HahnSeries.single γ s) * puiseuxEmb R q c' with hcval
  have hmem : cval ∈ PuiseuxSeries R := by
    rw [mem_puiseuxSeries_iff]
    refine ⟨q2, (puiseuxSubfield R q2).mul_mem ?_ ?_⟩
    · rw [puiseuxSubfield, RingHom.mem_fieldRange]; exact ⟨_, rfl⟩
    · exact puiseuxSubfield_mono R (dvd_mul_left q 2)
        (by rw [puiseuxSubfield, RingHom.mem_fieldRange]; exact ⟨c', rfl⟩)
  -- The monomial squares correctly across the two denominators.
  have hexp : puiseuxExpHom q2 (γ + γ) = puiseuxExpHom q γ := by
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast q.ne_zero
    simp only [puiseuxExpHom_apply, hq2]; push_cast; field_simp; ring
  have e1 : puiseuxEmb R q2 (HahnSeries.single γ s) * puiseuxEmb R q2 (HahnSeries.single γ s)
      = puiseuxEmb R q (HahnSeries.single γ k) := by
    rw [← map_mul, HahnSeries.single_mul_single, ← hs, puiseuxEmb_single, puiseuxEmb_single, hexp]
  have key : cval * cval = puiseuxEmb R q a' := by
    rw [hcval]
    calc puiseuxEmb R q2 (HahnSeries.single γ s) * puiseuxEmb R q c'
          * (puiseuxEmb R q2 (HahnSeries.single γ s) * puiseuxEmb R q c')
        = puiseuxEmb R q2 (HahnSeries.single γ s) * puiseuxEmb R q2 (HahnSeries.single γ s)
          * (puiseuxEmb R q c' * puiseuxEmb R q c') := by ring
      _ = puiseuxEmb R q (HahnSeries.single γ k) * (puiseuxEmb R q c' * puiseuxEmb R q c') := by
            rw [e1]
      _ = puiseuxEmb R q (HahnSeries.single γ k * (c' * c')) := by rw [← map_mul, ← map_mul]
      _ = puiseuxEmb R q (HahnSeries.single γ k * (1 + b')) := by rw [← sq, hc'2]
      _ = puiseuxEmb R q a' := by rw [hdecomp]
  refine ⟨⟨cval, hmem⟩, ?_⟩
  apply Subtype.ext
  rw [Subfield.coe_mul]
  show (a : HahnSeries ℚ R) = cval * cval
  rw [← ha', key]

end Azurite.BPR
