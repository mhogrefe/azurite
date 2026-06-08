import Azurite.BasuPollackRoy.Chapter3.Section3_3.Proposition_3_13
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_84

/-! # BPR §3.3 — Notation 3.15: composition with germs

Given a germ `ϕ` of semialgebraic continuous functions at the right of the origin with representative
`f` on `(0, t)`, and a semialgebraic continuous function `g` defined on a set `S` containing the
trajectory of `f`, the composite `g ∘ ϕ` is the germ of the semialgebraic continuous function
`g ∘ f` on `(0, t)` (`germComp`). It is independent of the chosen representative `f` of `ϕ`
(`germComp_congr`), and composing a representative `f` with the germ `ε = idGerm` of the identity
returns `ϕ` (`germComp_idGerm`, since `ε` is the germ of the identity map). -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The representative `g ∘ f` of the composite germ: `(g ∘ f)(u) = g(f(u))`, defined on `f`'s
interval `(0, t)`. The composite is semialgebraic and continuous because `f` and `g` are
(Proposition 2.84 and continuity of composition), once the trajectory of `f` lands in `g`'s
domain `S`. -/
noncomputable def compRep (g : (Fin 1 → R) → R) {S : Set (Fin 1 → R)}
    (hg : IsSemialgContinuousOn S g) (f : SemialgGermRep R)
    (hmaps : Set.MapsTo (scalarFun f.toFun) (rightNbhd f.bound) S) : SemialgGermRep R where
  bound := f.bound
  bound_pos := f.bound_pos
  toFun := fun u => g (constPt (f.toFun u))
  isSemialgContinuous :=
    ⟨proposition_2_84 f.isSemialgContinuous.1 hg.1 hmaps, hg.2.comp f.isSemialgContinuous.2 hmaps⟩

@[simp] theorem compRep_toFun (g : (Fin 1 → R) → R) {S : Set (Fin 1 → R)}
    (hg : IsSemialgContinuousOn S g) (f : SemialgGermRep R)
    (hmaps : Set.MapsTo (scalarFun f.toFun) (rightNbhd f.bound) S) (u : Fin 1 → R) :
    (compRep g hg f hmaps).toFun u = g (constPt (f.toFun u)) := rfl

/-- **Notation 3.15: the composite germ `g ∘ ϕ`.** For a representative `f` of `ϕ` whose trajectory
lands in the domain `S` of the semialgebraic continuous function `g`, this is the germ of `g ∘ f`. -/
noncomputable def germComp (g : (Fin 1 → R) → R) {S : Set (Fin 1 → R)}
    (hg : IsSemialgContinuousOn S g) (f : SemialgGermRep R)
    (hmaps : Set.MapsTo (scalarFun f.toFun) (rightNbhd f.bound) S) : SemialgGerm R :=
  (compRep g hg f hmaps).germ

/-- **`g ∘ ϕ` is independent of the representative `f` of `ϕ`.** Two equivalent representatives agree
near `0`, so the composites `g ∘ f` agree near `0` and define the same germ. -/
theorem germComp_congr (g : (Fin 1 → R) → R) {S : Set (Fin 1 → R)}
    (hg : IsSemialgContinuousOn S g) {f₁ f₂ : SemialgGermRep R}
    (hmaps₁ : Set.MapsTo (scalarFun f₁.toFun) (rightNbhd f₁.bound) S)
    (hmaps₂ : Set.MapsTo (scalarFun f₂.toFun) (rightNbhd f₂.bound) S)
    (hequiv : f₁ ≈ f₂) :
    germComp g hg f₁ hmaps₁ = germComp g hg f₂ hmaps₂ := by
  obtain ⟨t, ht, hagree⟩ := hequiv
  refine Quotient.sound ⟨t, ht, fun s hs hst => ?_⟩
  show g (constPt (f₁.toFun (constPt s))) = g (constPt (f₂.toFun (constPt s)))
  rw [hagree s hs hst]

/-- A representative of `ε = idGerm` on `(0, min 1 t)`, small enough to fit inside `f`'s domain so
that `f ∘ ε` is defined. -/
noncomputable def idRepLE (f : SemialgGermRep R) : SemialgGermRep R where
  bound := min 1 f.bound
  bound_pos := lt_min one_pos f.bound_pos
  toFun := fun u => u 0
  isSemialgContinuous :=
    (idGermRep : SemialgGermRep R).isSemialgContinuous.mono
      (isSemialgebraicSet_rightNbhd _) (rightNbhd_subset (min_le_left _ _))

/-- `idRepLE f` represents `ε = idGerm`. -/
theorem idRepLE_germ (f : SemialgGermRep R) : (idRepLE f).germ = idGerm :=
  Quotient.sound ⟨1, one_pos, fun _ _ _ => rfl⟩

/-- The trajectory of `idRepLE f` lands in `f`'s domain, so `f ∘ ε` is defined. -/
theorem idRepLE_mapsTo (f : SemialgGermRep R) :
    Set.MapsTo (scalarFun (idRepLE f).toFun) (rightNbhd (idRepLE f).bound) (rightNbhd f.bound) := by
  intro u hu
  obtain ⟨hpos, hlt⟩ := hu
  exact ⟨hpos, lt_of_lt_of_le hlt (min_le_right _ _)⟩

/-- **`f ∘ ε = ϕ`** (BPR Notation 3.15, second remark): composing the function underlying a
representative `f` of `ϕ` with the germ `ε = idGerm` of the identity map returns `ϕ`. -/
theorem germComp_idGerm (f : SemialgGermRep R) :
    germComp f.toFun f.isSemialgContinuous (idRepLE f) (idRepLE_mapsTo f) = f.germ :=
  Quotient.sound ⟨min 1 f.bound, lt_min one_pos f.bound_pos, fun _ _ _ => rfl⟩

end Azurite.BPR
