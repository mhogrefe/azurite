import Azurite.BasuPollackRoy.Chapter3.Section3_3.Proposition_3_18

/-! # BPR §3.4 — the limit `lim_ε` on the germ field

For a germ `x ∈ R⟨ε⟩` bounded by an element of `R` (i.e. `x ∈ boundedGerms`), its **limit**
`lim_ε(x) ∈ R` is the standard part: the unique `a ∈ R` with `x − a` infinitesimal. Concretely it is
transported from the Puiseux side `puiseuxLim` through the order isomorphism
`R⟨ε⟩ ≅ algebraicPuiseux R` of Theorem 3.14, and packaged as a ring homomorphism
`limEps : boundedGerms →+* R`.

The defining property is the characterization `limEps_eq_iff`: `lim_ε(x) = a` iff `x − a` is
infinitesimal (below every positive standard element). The forward direction `limEps_infinitesimal`
generalizes the estimate in Proposition 3.18. -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A germ is **infinitesimal** if its absolute value is below every positive standard element. -/
def IsInfinitesimal (x : SemialgGerm R) : Prop :=
  ∀ r : R, 0 < r → |x| < algebraMap R (SemialgGerm R) r

/-- The constant embedding `R → R⟨ε⟩` is strictly monotone. -/
theorem algebraMap_lt_algebraMap_of_lt {a b : R} (h : a < b) :
    algebraMap R (SemialgGerm R) a < algebraMap R (SemialgGerm R) b := by
  rw [← constGermRep_germ a, ← constGermRep_germ b]
  exact germ_lt_of_eventually ⟨1, one_pos, fun s _ _ => h⟩

/-- `ε = idGerm` is infinitesimal: it is below every positive standard element. -/
theorem idGerm_lt_algebraMap {r : R} (hr : 0 < r) :
    (idGerm : SemialgGerm R) < algebraMap R (SemialgGerm R) r := by
  rw [← constGermRep_germ r]
  refine germ_lt_of_eventually ⟨r, hr, fun s hs hsr => ?_⟩
  show idGermRep.toFun (constPt s) < (constGermRep r).toFun (constPt s)
  rw [idGermRep_toFun]
  exact hsr

/-- The constant embedding `R → R⟨ε⟩` is monotone. -/
theorem algebraMap_le_algebraMap_of_le {a b : R} (h : a ≤ b) :
    algebraMap R (SemialgGerm R) a ≤ algebraMap R (SemialgGerm R) b := by
  rcases h.lt_or_eq with h | h
  · exact (algebraMap_lt_algebraMap_of_lt h).le
  · rw [h]

/-- `|algebraMap x| = algebraMap |x|`. -/
theorem abs_algebraMap (x : R) :
    |algebraMap R (SemialgGerm R) x| = algebraMap R (SemialgGerm R) |x| := by
  rcases le_total 0 x with hx | hx
  · have h0 : (0 : SemialgGerm R) ≤ algebraMap R (SemialgGerm R) x := by
      rw [← map_zero (algebraMap R (SemialgGerm R))]; exact algebraMap_le_algebraMap_of_le hx
    rw [abs_of_nonneg hx, abs_of_nonneg h0]
  · have h0 : algebraMap R (SemialgGerm R) x ≤ 0 := by
      rw [← map_zero (algebraMap R (SemialgGerm R))]; exact algebraMap_le_algebraMap_of_le hx
    rw [abs_of_nonpos hx, abs_of_nonpos h0, map_neg]

/-- A germ infinitesimally close to a standard element is bounded. -/
theorem mem_boundedGerms_of_infinitesimal {x : SemialgGerm R} {a : R}
    (h : IsInfinitesimal (x - algebraMap R (SemialgGerm R) a)) : x ∈ boundedGerms := by
  refine ⟨|a| + 1, by positivity, ?_⟩
  have h1' : |x - algebraMap R (SemialgGerm R) a| < algebraMap R (SemialgGerm R) 1 := h 1 one_pos
  have hsplit := abs_add_le (x - algebraMap R (SemialgGerm R) a) (algebraMap R (SemialgGerm R) a)
  rw [sub_add_cancel, abs_algebraMap] at hsplit
  calc |x| ≤ |x - algebraMap R (SemialgGerm R) a| + algebraMap R (SemialgGerm R) |a| := hsplit
    _ < algebraMap R (SemialgGerm R) 1 + algebraMap R (SemialgGerm R) |a| := by linarith
    _ = algebraMap R (SemialgGerm R) (|a| + 1) := by rw [← map_add]; congr 1; ring

/-- The fixed `R(ε)`-algebra isomorphism `R⟨ε⟩ ≅ algebraicPuiseux R` (Theorem 3.14). -/
noncomputable def germPuiseuxEquiv : SemialgGerm R ≃ₐ[RatFunc R] algebraicPuiseux R :=
  theorem_3_14.some

/-- The restriction of `germPuiseuxEquiv` to the bounded subrings, as a ring homomorphism. -/
noncomputable def boundedGermToPuiseuxBounded :
    (boundedGerms : Subring (SemialgGerm R)) →+* puiseuxBounded R where
  toFun x := ⟨germPuiseuxEquiv x.1,
    (mem_boundedGerms_iff_mem_puiseuxBounded germPuiseuxEquiv x.1).mp x.2⟩
  map_one' := Subtype.ext (by simp only [OneMemClass.coe_one]; exact map_one _)
  map_mul' a b := Subtype.ext (by simp only [MulMemClass.coe_mul]; exact map_mul _ _ _)
  map_zero' := Subtype.ext (by simp only [ZeroMemClass.coe_zero]; exact map_zero _)
  map_add' a b := Subtype.ext (by simp only [AddMemClass.coe_add]; exact map_add _ _ _)

/-- **`lim_ε`**, the limit map on bounded germs, as a ring homomorphism `boundedGerms →+* R`. -/
noncomputable def limEps : (boundedGerms : Subring (SemialgGerm R)) →+* R :=
  (puiseuxLim R).comp boundedGermToPuiseuxBounded

theorem limEps_apply (x : (boundedGerms : Subring (SemialgGerm R))) :
    limEps x = puiseuxLim R ⟨germPuiseuxEquiv x.1,
      (mem_boundedGerms_iff_mem_puiseuxBounded germPuiseuxEquiv x.1).mp x.2⟩ := rfl

/-- **`lim_ε(x) = a` ⟹ `x − a` is infinitesimal.** (Proposition 3.18's estimate, intrinsic form.) -/
theorem limEps_infinitesimal (x : (boundedGerms : Subring (SemialgGerm R))) :
    IsInfinitesimal ((x : SemialgGerm R) - algebraMap R (SemialgGerm R) (limEps x)) := by
  have : IsRealClosed (SemialgGerm R) := isRealClosed_semialgGerm
  intro r hr
  set e := germPuiseuxEquiv (R := R)
  set hmem := (mem_boundedGerms_iff_mem_puiseuxBounded e x.1).mp x.2 with hmem_def
  have hord : 0 < puiseuxOrder R
      (((e x.1 : algebraicPuiseux R) : PuiseuxSeries R) - constPuiseux (limEps x)) :=
    (puiseuxLim_eq_iff ⟨e x.1, hmem⟩ (limEps x)).mp (limEps_apply x).symm
  obtain ⟨h1, h2⟩ := aP_infinitesimal (e x.1) (limEps x) hord r hr
  rw [abs_lt]
  have hediff : e ((x : SemialgGerm R) - algebraMap R (SemialgGerm R) (limEps x))
      = e x.1 - algebraMap R (algebraicPuiseux R) (limEps x) := by
    rw [map_sub, algEquiv_algebraMap]
  exact ⟨by rw [← algEquiv_lt_iff e, map_neg, algEquiv_algebraMap, hediff]; exact h1,
    by rw [← algEquiv_lt_iff e, algEquiv_algebraMap, hediff]; exact h2⟩

/-- **`x − a` infinitesimal ⟹ `lim_ε(x) = a`.** -/
theorem limEps_eq_of_infinitesimal (x : (boundedGerms : Subring (SemialgGerm R))) (a : R)
    (hinf : IsInfinitesimal ((x : SemialgGerm R) - algebraMap R (SemialgGerm R) a)) :
    limEps x = a := by
  have : IsRealClosed (SemialgGerm R) := isRealClosed_semialgGerm
  set e := germPuiseuxEquiv (R := R)
  set hmem := (mem_boundedGerms_iff_mem_puiseuxBounded e x.1).mp x.2 with hmem_def
  rw [limEps_apply, puiseuxLim_eq_iff]
  apply puiseuxOrder_pos_of_infinitesimal
  intro r hr
  have hi := hinf r hr
  rw [abs_lt] at hi
  -- transfer the two-sided bound to `algebraicPuiseux` via `e`.
  have key1 : -(algebraMap R (algebraicPuiseux R) r)
      < e x.1 - algebraMap R (algebraicPuiseux R) a := by
    rw [← algEquiv_algebraMap e a, ← algEquiv_algebraMap e r, ← map_neg, ← map_sub, algEquiv_lt_iff]
    exact hi.1
  have key2 : e x.1 - algebraMap R (algebraicPuiseux R) a
      < algebraMap R (algebraicPuiseux R) r := by
    rw [← algEquiv_algebraMap e a, ← algEquiv_algebraMap e r, ← map_sub, algEquiv_lt_iff]
    exact hi.2
  -- coerce to `PuiseuxSeries`.
  have hcoeR : ((algebraMap R (algebraicPuiseux R) r : algebraicPuiseux R) : PuiseuxSeries R)
      = algebraMap R (PuiseuxSeries R) r := by
    rw [algebraMap_algebraicPuiseux_coe, algebraMap_eq_constPuiseux]
  have hcoeA : ((algebraMap R (algebraicPuiseux R) a : algebraicPuiseux R) : PuiseuxSeries R)
      = constPuiseux a := algebraMap_algebraicPuiseux_coe a
  have hz : ((e x.1 - algebraMap R (algebraicPuiseux R) a : algebraicPuiseux R) : PuiseuxSeries R)
      = ((e x.1 : algebraicPuiseux R) : PuiseuxSeries R) - constPuiseux a := by
    rw [AddSubgroupClass.coe_sub, hcoeA]
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · have := key1; rwa [← Subtype.coe_lt_coe, NegMemClass.coe_neg, hcoeR, hz] at this
  · have := key2; rwa [← Subtype.coe_lt_coe, hcoeR, hz] at this

/-- **`lim_ε` characterization.** -/
theorem limEps_eq_iff (x : (boundedGerms : Subring (SemialgGerm R))) (a : R) :
    limEps x = a ↔ IsInfinitesimal ((x : SemialgGerm R) - algebraMap R (SemialgGerm R) a) :=
  ⟨fun h => h ▸ limEps_infinitesimal x, limEps_eq_of_infinitesimal x a⟩

end Azurite.BPR
