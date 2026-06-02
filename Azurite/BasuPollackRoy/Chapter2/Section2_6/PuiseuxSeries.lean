import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.Algebra.Order.Field.Subfield

/-! # BPR §2.6 — the field of Puiseux series `K⟨⟨ε⟩⟩`

A **Puiseux series** in `ε` with coefficients in a field `K` is a formal Laurent series in
`ε^{1/q}` for some positive integer `q`, i.e. a series `∑_{i ≥ k} aᵢ ε^{i/q}`. The field of
Puiseux series `K⟨⟨ε⟩⟩` is the union `⋃_q K((ε^{1/q}))`.

We realize this inside `HahnSeries ℚ K` (Hahn series with rational exponents, which is a
field). For each positive `q`, the field `K((ε^{1/q})) = LaurentSeries K = HahnSeries ℤ K`
embeds into `HahnSeries ℚ K` by scaling exponents `n ↦ n/q` (`puiseuxSubfield K q`). The field
of Puiseux series is the supremum of these subfields:

`PuiseuxSeries K := ⨆_{q} puiseuxSubfield K q : Subfield (HahnSeries ℚ K)`.

Being a supremum of subfields, it is a subfield of the field `HahnSeries ℚ K`, hence itself a
field. (The bounded-denominator condition — exponents in `(1/q)ℤ` for a *single* `q` — is what
distinguishes Puiseux series from arbitrary `HahnSeries ℚ K`.)
-/

namespace Azurite.BPR

open HahnSeries

/-- **Functoriality of `embDomain`**: embedding along `e₁` then `e₂` is embedding along
`e₁.trans e₂`. (Not in Mathlib.) -/
theorem embDomain_trans {Γ Γ' Γ'' R : Type*} [PartialOrder Γ] [PartialOrder Γ'] [PartialOrder Γ'']
    [Zero R] (e₁ : Γ ↪o Γ') (e₂ : Γ' ↪o Γ'') (x : HahnSeries Γ R) :
    embDomain (e₁.trans e₂) x = embDomain e₂ (embDomain e₁ x) := by
  ext r
  by_cases h : r ∈ Set.range (e₁.trans e₂)
  · obtain ⟨a, rfl⟩ := h
    rw [embDomain_coeff]
    show x.coeff a = (embDomain e₂ (embDomain e₁ x)).coeff (e₂ (e₁ a))
    rw [embDomain_coeff, embDomain_coeff]
  · rw [embDomain_notin_image_support (fun hc => h (Set.image_subset_range _ _ hc))]
    by_cases h₂ : r ∈ Set.range e₂
    · obtain ⟨s, rfl⟩ := h₂
      rw [embDomain_coeff]
      by_cases h₁ : s ∈ Set.range e₁
      · obtain ⟨t, rfl⟩ := h₁
        exact absurd ⟨t, rfl⟩ h
      · exact (embDomain_notin_image_support
          (fun hc => h₁ (Set.image_subset_range _ _ hc))).symm
    · exact (embDomain_notin_image_support
        (fun hc => h₂ (Set.image_subset_range _ _ hc))).symm

variable (K : Type*) [Field K]

/-- The exponent-scaling homomorphism `ℤ →+ ℚ`, `n ↦ n / q`, used to view a Laurent series in
`ε^{1/q}` (exponents in `ℤ`) as a Hahn series with rational exponents (in `(1/q)ℤ`). -/
def puiseuxExpHom (q : ℕ+) : ℤ →+ ℚ where
  toFun n := (n : ℚ) / (q : ℚ)
  map_zero' := by simp
  map_add' a b := by push_cast; ring

@[simp] theorem puiseuxExpHom_apply (q : ℕ+) (n : ℤ) :
    puiseuxExpHom q n = (n : ℚ) / (q : ℚ) := rfl

theorem puiseuxExpHom_injective (q : ℕ+) : Function.Injective (puiseuxExpHom q) := by
  intro a b hab
  simp only [puiseuxExpHom_apply] at hab
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast q.ne_zero
  field_simp at hab
  exact_mod_cast hab

theorem puiseuxExpHom_le (q : ℕ+) (a b : ℤ) :
    puiseuxExpHom q a ≤ puiseuxExpHom q b ↔ a ≤ b := by
  simp only [puiseuxExpHom_apply]
  have hq : (0 : ℚ) < (q : ℚ) := by exact_mod_cast q.pos
  rw [div_le_div_iff_of_pos_right hq]
  exact_mod_cast Iff.rfl

/-- The ring embedding `K((ε^{1/q})) = HahnSeries ℤ K → HahnSeries ℚ K` scaling exponents by
`1/q`. -/
noncomputable def puiseuxEmb (q : ℕ+) : HahnSeries ℤ K →+* HahnSeries ℚ K :=
  HahnSeries.embDomainRingHom (puiseuxExpHom q) (puiseuxExpHom_injective q) (puiseuxExpHom_le q)

/-- The subfield of `HahnSeries ℚ K` of Laurent series in `ε^{1/q}` (the image of the
embedding `puiseuxEmb`). -/
noncomputable def puiseuxSubfield (q : ℕ+) : Subfield (HahnSeries ℚ K) :=
  (puiseuxEmb K q).fieldRange

/-- **The field of Puiseux series `K⟨⟨ε⟩⟩`**: the union (supremum) over all positive `q` of the
subfields of Laurent series in `ε^{1/q}`. As a supremum of subfields of the field
`HahnSeries ℚ K`, it is a subfield, hence a field. -/
noncomputable def PuiseuxSeries : Subfield (HahnSeries ℚ K) :=
  ⨆ q : ℕ+, puiseuxSubfield K q

/-- `K⟨⟨X⟩⟩` denotes the field of Puiseux series (as a type). -/
scoped notation:9000 K "⟨⟨X⟩⟩" => (PuiseuxSeries K : Type _)

/-- **`K⟨⟨ε⟩⟩` is a field** (it is a subfield of the field `HahnSeries ℚ K`). -/
theorem puiseuxSeries_isField : IsField (PuiseuxSeries K) :=
  Field.toIsField (PuiseuxSeries K)

/-- The subfields `puiseuxSubfield K q` are monotone in `q` under divisibility: a Laurent
series in `ε^{1/q₁}` is a Laurent series in `ε^{1/q}` whenever `q₁ ∣ q`. -/
theorem puiseuxSubfield_mono {q₁ q : ℕ+} (h : q₁ ∣ q) :
    puiseuxSubfield K q₁ ≤ puiseuxSubfield K q := by
  obtain ⟨m₀, hm₀⟩ := h
  have hm0pos : (0 : ℤ) < (m₀ : ℤ) := by exact_mod_cast m₀.pos
  have hm0 : (m₀ : ℤ) ≠ 0 := ne_of_gt hm0pos
  set rfn : ℤ →+ ℤ :=
    { toFun := fun n => (m₀ : ℤ) * n, map_zero' := by simp, map_add' := fun a b => by ring }
    with hrfn
  have rfn_inj : Function.Injective rfn := fun a b hab => by
    simp only [hrfn, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mul_right_inj' hm0] at hab; exact hab
  have rfn_le : ∀ a b : ℤ, rfn a ≤ rfn b ↔ a ≤ b := fun a b => by
    simp only [hrfn, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact ⟨fun h => le_of_mul_le_mul_left h hm0pos, fun h => mul_le_mul_of_nonneg_left h hm0pos.le⟩
  -- factorization `puiseuxEmb q₁ = puiseuxEmb q ∘ (refine by m₀)`.
  have hfact : ∀ a : HahnSeries ℤ K,
      puiseuxEmb K q (embDomainRingHom rfn rfn_inj rfn_le a) = puiseuxEmb K q₁ a := by
    intro a
    simp only [puiseuxEmb, embDomainRingHom_apply]
    rw [← embDomain_trans]
    congr 1
    refine RelEmbedding.ext (fun n => ?_)
    show puiseuxExpHom q (rfn n) = puiseuxExpHom q₁ n
    simp only [hrfn, AddMonoidHom.coe_mk, ZeroHom.coe_mk, puiseuxExpHom_apply]
    have hqe : (q : ℚ) = (q₁ : ℚ) * (m₀ : ℚ) := by exact_mod_cast hm₀
    rw [hqe]; push_cast; field_simp
  intro y hy
  rw [puiseuxSubfield, RingHom.mem_fieldRange] at hy
  obtain ⟨a, rfl⟩ := hy
  rw [puiseuxSubfield, RingHom.mem_fieldRange]
  exact ⟨embDomainRingHom rfn rfn_inj rfn_le a, hfact a⟩

/-- The family of subfields is directed (their lcm dominates any two), so the supremum
defining `K⟨⟨ε⟩⟩` is a genuine union. -/
theorem directed_puiseuxSubfield : Directed (· ≤ ·) (puiseuxSubfield K) := fun q₁ q₂ =>
  ⟨q₁ * q₂, puiseuxSubfield_mono K (dvd_mul_right q₁ q₂),
    puiseuxSubfield_mono K (dvd_mul_left q₂ q₁)⟩

/-- **Membership in `K⟨⟨ε⟩⟩`**: a Hahn series is a Puiseux series iff it is a Laurent series in
`ε^{1/q}` for *some* positive integer `q`. -/
theorem mem_puiseuxSeries_iff {x : HahnSeries ℚ K} :
    x ∈ PuiseuxSeries K ↔ ∃ q : ℕ+, x ∈ puiseuxSubfield K q := by
  rw [PuiseuxSeries, Subfield.mem_iSup_of_directed (directed_puiseuxSubfield K)]

/-! ### Order and initial coefficient -/

/-- The **order** `o(ā) ∈ ℚ ∪ {∞}` of a Puiseux series: the least exponent `r₁` appearing
(with `o(0) = ∞`). It is the `orderTop` of the underlying Hahn series. -/
noncomputable def puiseuxOrder (a : PuiseuxSeries K) : WithTop ℚ :=
  HahnSeries.orderTop (a : HahnSeries ℚ K)

/-- The **initial coefficient** `In(ā) ∈ K` of a Puiseux series: the coefficient `a₁` of the
least exponent (`In(0) = 0`). -/
noncomputable def puiseuxInitCoeff (a : PuiseuxSeries K) : K :=
  HahnSeries.leadingCoeff (a : HahnSeries ℚ K)

variable {K}

@[simp] theorem puiseuxOrder_zero : puiseuxOrder K (0 : PuiseuxSeries K) = ⊤ := by
  simp [puiseuxOrder]

/-- The order is additive on products: `o(ā b̄) = o(ā) + o(b̄)`. -/
theorem puiseuxOrder_mul (a b : PuiseuxSeries K) :
    puiseuxOrder K (a * b) = puiseuxOrder K a + puiseuxOrder K b := by
  show HahnSeries.orderTop ((a * b : PuiseuxSeries K) : HahnSeries ℚ K) = _
  rw [Subfield.coe_mul, HahnSeries.orderTop_mul]
  rfl

/-- The order of a sum is at least the minimum of the orders:
`o(ā + b̄) ≥ min(o(ā), o(b̄))`. -/
theorem min_le_puiseuxOrder_add (a b : PuiseuxSeries K) :
    min (puiseuxOrder K a) (puiseuxOrder K b) ≤ puiseuxOrder K (a + b) := by
  show min _ _ ≤ HahnSeries.orderTop ((a + b : PuiseuxSeries K) : HahnSeries ℚ K)
  rw [Subfield.coe_add]
  exact HahnSeries.min_orderTop_le_orderTop_add

/-- When the orders differ, the order of a sum equals the minimum:
`o(ā + b̄) = min(o(ā), o(b̄))` if `o(ā) ≠ o(b̄)`. -/
theorem puiseuxOrder_add_of_ne (a b : PuiseuxSeries K)
    (h : puiseuxOrder K a ≠ puiseuxOrder K b) :
    puiseuxOrder K (a + b) = min (puiseuxOrder K a) (puiseuxOrder K b) := by
  show HahnSeries.orderTop ((a + b : PuiseuxSeries K) : HahnSeries ℚ K) = _
  rw [Subfield.coe_add]
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [HahnSeries.orderTop_add_eq_left hlt, min_eq_left hlt.le]; rfl
  · rw [HahnSeries.orderTop_add_eq_right hgt, min_eq_right hgt.le]; rfl

/-! ### Ordered field structure (when `K` is ordered) -/

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

open scoped HahnSeries in
/-- When `K` is an ordered field, `K⟨⟨ε⟩⟩` is a linearly ordered field: the order is pulled
back from the lexicographic order on `HahnSeries ℚ K`. -/
noncomputable instance puiseuxLinearOrder : LinearOrder (PuiseuxSeries K) :=
  LinearOrder.lift' (fun a => toLex (a : HahnSeries ℚ K))
    (fun _ _ hab => Subtype.ext (by simpa using congrArg ofLex hab))

noncomputable instance : IsStrictOrderedRing (PuiseuxSeries K) :=
  Function.Injective.isStrictOrderedRing (fun a => toLex (a : HahnSeries ℚ K))
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) Iff.rfl Iff.rfl

omit [IsStrictOrderedRing K] in
/-- **BPR's order on `K⟨⟨ε⟩⟩`**: a Puiseux series is positive exactly when its initial
coefficient is positive. -/
theorem puiseux_pos_iff (a : PuiseuxSeries K) : 0 < a ↔ 0 < puiseuxInitCoeff K a :=
  HahnSeries.leadingCoeff_pos_iff.symm

end Ordered

end Azurite.BPR
