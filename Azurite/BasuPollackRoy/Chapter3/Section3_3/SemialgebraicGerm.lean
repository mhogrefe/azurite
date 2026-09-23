import Azurite.BasuPollackRoy.Chapter3.Section3_3.SemialgebraicPolynomial

/-! # BPR §3.3 — germs of semialgebraic continuous functions at the right of the origin

A *germ at the right of the origin* is the common behaviour, arbitrarily close to `0`, of a
semialgebraic continuous function `R → R` defined on an interval `(0, t)`, `t > 0`. Two such functions
define the same germ when they agree on some common interval `(0, t)`:
`f₁ ≃ f₂ ⟺ ∃ t > 0, ∀ t' ∈ (0, t), f₁(t') = f₂(t')`.

We model a representative as a total function `c : R^1 → R` carrying a bound `t > 0` and a witness that
`c` is semialgebraic and continuous on `(0, t)` (`IsSemialgContinuousOn`); the value of the underlying
real function at a point `s` is `c (constPt s)`. The set of germs is the quotient by the agreement
relation above. -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The right-neighborhood `(0, t)` of the origin in `R`, viewed as a subset of `R^1`. -/
def rightNbhd (t : R) : Set (Fin 1 → R) := {u | 0 < u 0 ∧ u 0 < t}

omit [IsRealClosed R] in
/-- The interval `(0, t) ⊆ R^1` is semialgebraic. -/
theorem isSemialgebraicSet_rightNbhd (t : R) : IsSemialgebraicSet (rightNbhd t) := by
  have he : rightNbhd t
      = {u | 0 < MvPolynomial.eval u (MvPolynomial.X 0)}
        ∩ {u | MvPolynomial.eval u (MvPolynomial.X 0 - MvPolynomial.C t) < 0} := by
    ext u
    simp only [rightNbhd, Set.mem_ofPred_eq, Set.mem_inter_iff, MvPolynomial.eval_X, map_sub,
      MvPolynomial.eval_C, sub_lt_zero]
  rw [he]; exact (IsSemialgebraicSet.gtZero _).inter (IsSemialgebraicSet.ltZero _)

/-- A **representative of a germ at the right of the origin**: a function `R^1 → R` that is
semialgebraic and continuous on some interval `(0, t)`, `t > 0`. -/
structure SemialgGermRep (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] where
  /-- the right endpoint of the interval `(0, t)` of definition -/
  bound : R
  /-- the interval `(0, t)` is non-degenerate -/
  bound_pos : 0 < bound
  /-- the underlying total function (only its values on `(0, t)` matter) -/
  toFun : (Fin 1 → R) → R
  /-- the function is semialgebraic and continuous on `(0, t)` -/
  isSemialgContinuous : IsSemialgContinuousOn (rightNbhd bound) toFun

/-- Two representatives define the **same germ** if they agree on a common interval `(0, t)`. -/
def SemialgGermRep.Equiv (f g : SemialgGermRep R) : Prop :=
  ∃ t : R, 0 < t ∧ ∀ s : R, 0 < s → s < t → f.toFun (constPt s) = g.toFun (constPt s)

theorem SemialgGermRep.equiv_refl (f : SemialgGermRep R) : f.Equiv f :=
  ⟨f.bound, f.bound_pos, fun _ _ _ => rfl⟩

theorem SemialgGermRep.equiv_symm {f g : SemialgGermRep R} (h : f.Equiv g) : g.Equiv f := by
  obtain ⟨t, ht, hfg⟩ := h
  exact ⟨t, ht, fun s hs hst => (hfg s hs hst).symm⟩

theorem SemialgGermRep.equiv_trans {f g h : SemialgGermRep R} (hfg : f.Equiv g) (hgh : g.Equiv h) :
    f.Equiv h := by
  obtain ⟨t₁, ht₁, H₁⟩ := hfg
  obtain ⟨t₂, ht₂, H₂⟩ := hgh
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, fun s hs hst => ?_⟩
  rw [H₁ s hs (lt_of_lt_of_le hst (min_le_left _ _)),
    H₂ s hs (lt_of_lt_of_le hst (min_le_right _ _))]

/-- Agreement on a common interval `(0, t)` is an equivalence relation on representatives. -/
instance semialgGermSetoid (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Setoid (SemialgGermRep R) where
  r := SemialgGermRep.Equiv
  iseqv := ⟨SemialgGermRep.equiv_refl, SemialgGermRep.equiv_symm, SemialgGermRep.equiv_trans⟩

/-- The **set of germs of semialgebraic continuous functions at the right of the origin**: the
semialgebraic continuous functions defined on some interval `(0, t)`, modulo agreement near `0`. -/
abbrev SemialgGerm (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Type _ := Quotient (semialgGermSetoid R)

/-- The germ of a representative. -/
def SemialgGermRep.germ (f : SemialgGermRep R) : SemialgGerm R := Quotient.mk _ f

end Azurite.BPR
