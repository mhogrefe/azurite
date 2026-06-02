import Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxSeries
import Azurite.BasuPollackRoy.Chapter2.Section2_1.InfinitesimalUnbounded
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # BPR §2.6 — `ε` is infinitesimal; `K⟨⟨ε⟩⟩` is non-archimedean

In the ordered field of Puiseux series `K⟨⟨ε⟩⟩`, the element `ε` (the Puiseux series
`ε^1 = single 1 1`) is **infinitesimal over `K`** (`Azurite.BPR.IsInfinitesimalOver`): it is
positive and smaller than every positive constant `a ∈ K`, since `a - ε > 0` (its initial,
lowest-order coefficient is `a > 0`). Consequently `K⟨⟨ε⟩⟩` is **non-archimedean**: no natural
multiple `n • ε` reaches `1`.

To phrase "infinitesimal over `K`" we equip `K⟨⟨ε⟩⟩` with the `K`-algebra structure given by
the constant embedding `k ↦ k` (`puiseuxC`, `HahnSeries.C` corestricted to the Puiseux
subfield).
-/

namespace Azurite.BPR

open HahnSeries

variable {K : Type*} [Field K]

/-- The constant `HahnSeries.C k` is a Puiseux series (a Laurent series in `ε^{1/1} = ε`). -/
theorem C_mem_puiseuxSeries (k : K) : (HahnSeries.C k : HahnSeries ℚ K) ∈ PuiseuxSeries K := by
  rw [mem_puiseuxSeries_iff]
  exact ⟨1, RingHom.mem_fieldRange.mpr ⟨HahnSeries.C k, by
    simp [puiseuxEmb, HahnSeries.embDomainRingHom_apply]⟩⟩

/-- **The constant embedding `K → K⟨⟨ε⟩⟩`**, sending `k` to the constant Puiseux series `k`. -/
noncomputable def puiseuxC : K →+* PuiseuxSeries K where
  toFun k := ⟨HahnSeries.C k, C_mem_puiseuxSeries k⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [map_mul]
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp [map_add]

@[simp] theorem puiseuxC_coe (k : K) : (puiseuxC k : HahnSeries ℚ K) = HahnSeries.C k := rfl

/-- `K⟨⟨ε⟩⟩` is a `K`-algebra via the constant embedding. -/
noncomputable instance : Algebra K (PuiseuxSeries K) := puiseuxC.toAlgebra

theorem algebraMap_puiseux_coe (k : K) :
    (algebraMap K (PuiseuxSeries K) k : HahnSeries ℚ K) = HahnSeries.C k := by
  rw [RingHom.algebraMap_toAlgebra]; rfl

/-- **The infinitesimal `ε ∈ K⟨⟨ε⟩⟩`**: the Puiseux series `ε^1`. -/
noncomputable def puiseuxEps : PuiseuxSeries K :=
  ⟨HahnSeries.single 1 1, by
    rw [mem_puiseuxSeries_iff]
    exact ⟨1, RingHom.mem_fieldRange.mpr ⟨HahnSeries.single 1 1, by
      rw [puiseuxEmb, HahnSeries.embDomainRingHom_apply, HahnSeries.embDomain_single]
      norm_num⟩⟩⟩

@[simp] theorem puiseuxEps_coe :
    ((puiseuxEps : PuiseuxSeries K) : HahnSeries ℚ K) = HahnSeries.single 1 1 := rfl

/-- `ε^1 = n • ε` viewed in `HahnSeries ℚ K` is the single term `n` at exponent `1`. -/
theorem nsmul_single_one (n : ℕ) :
    (n • HahnSeries.single (1 : ℚ) (1 : K)) = HahnSeries.single (1 : ℚ) (n : K) := by
  rw [nsmul_eq_mul, ← map_natCast (HahnSeries.C) n, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]

/-- Every single term at the positive exponent `1` has positive order. -/
theorem zero_lt_orderTop_single_one (c : K) :
    (0 : WithTop ℚ) < HahnSeries.orderTop (HahnSeries.single (1 : ℚ) c) := by
  by_cases h : c = 0 <;> simp [HahnSeries.orderTop_single, h]

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- **`ε` is positive** in `K⟨⟨ε⟩⟩` (its initial coefficient is `1 > 0`). -/
theorem puiseuxEps_pos : 0 < (puiseuxEps : PuiseuxSeries K) := by
  rw [puiseux_pos_iff]
  simp only [puiseuxInitCoeff, puiseuxEps_coe, leadingCoeff_of_single]
  exact one_pos

/-- **`ε` is smaller than every positive constant**: `ε < a` for `0 < a ∈ K`, since the
initial coefficient of `a - ε` is `a > 0`. -/
theorem puiseuxEps_lt_algebraMap {a : K} (ha : 0 < a) :
    (puiseuxEps : PuiseuxSeries K) < algebraMap K (PuiseuxSeries K) a := by
  rw [← sub_pos, puiseux_pos_iff]
  have hCa : HahnSeries.orderTop (HahnSeries.C a : HahnSeries ℚ K) = 0 := by
    rw [HahnSeries.C_apply]; simp [HahnSeries.orderTop_single, ne_of_gt ha]
  have hlt : HahnSeries.orderTop (HahnSeries.C a : HahnSeries ℚ K)
      < HahnSeries.orderTop (-(HahnSeries.single (1 : ℚ) (1 : K))) := by
    rw [hCa, HahnSeries.orderTop_neg]; exact zero_lt_orderTop_single_one 1
  simp only [puiseuxInitCoeff, Subfield.coe_sub, algebraMap_puiseux_coe, puiseuxEps_coe]
  rw [sub_eq_add_neg, HahnSeries.leadingCoeff_add_eq_left hlt, HahnSeries.C_apply,
    leadingCoeff_of_single]
  exact ha

/-- **`ε` is infinitesimal over `K`** (BPR Definition; `Azurite.BPR.IsInfinitesimalOver`):
it is nonzero and `|ε| < a` for every positive `a ∈ K`. -/
theorem isInfinitesimalOver_puiseuxEps :
    IsInfinitesimalOver K (puiseuxEps : PuiseuxSeries K) := by
  refine ⟨ne_of_gt puiseuxEps_pos, fun a ha => ?_⟩
  rw [abs_of_pos puiseuxEps_pos]
  exact puiseuxEps_lt_algebraMap ha

/-- No natural multiple of `ε` reaches `1`: `n • ε < 1` for all `n` (the initial coefficient of
`1 - n • ε` is `1 > 0`). -/
theorem puiseuxEps_nsmul_lt_one (n : ℕ) :
    (n • puiseuxEps : PuiseuxSeries K) < 1 := by
  rw [← sub_pos, puiseux_pos_iff]
  have hlt : HahnSeries.orderTop (1 : HahnSeries ℚ K)
      < HahnSeries.orderTop (-(HahnSeries.single (1 : ℚ) (n : K))) := by
    rw [HahnSeries.orderTop_one, HahnSeries.orderTop_neg]
    exact zero_lt_orderTop_single_one _
  simp only [puiseuxInitCoeff, Subfield.coe_sub, Subfield.coe_one,
    AddSubmonoidClass.coe_nsmul, puiseuxEps_coe, nsmul_single_one]
  rw [sub_eq_add_neg, HahnSeries.leadingCoeff_add_eq_left hlt, HahnSeries.leadingCoeff_one]
  exact one_pos

/-- **`K⟨⟨ε⟩⟩` is non-archimedean.** Since `ε` is a positive infinitesimal, no natural multiple
`n • ε` can reach `1`, contradicting the archimedean property. -/
theorem not_archimedean_puiseuxSeries : ¬ Archimedean (PuiseuxSeries K) := by
  intro h
  obtain ⟨n, hn⟩ := h.arch 1 puiseuxEps_pos
  exact absurd (lt_of_le_of_lt hn (puiseuxEps_nsmul_lt_one n)) (lt_irrefl 1)

end Ordered

end Azurite.BPR
