import Azurite.BasuPollackRoy.Chapter3.Section3_3.SemialgebraicGermField

/-! # BPR §3.3 — the germ field is an ordered field

The sign of a germ of a semialgebraic continuous function at the right of the origin is well defined:
by the one-dimensional structure of semialgebraic sets, a representative is, near `0⁺`, eventually
positive, eventually zero, or eventually negative (and exactly one of these). Declaring a germ
positive when it is eventually positive gives a positive cone making `SemialgGerm R` an ordered
field (`LinearOrder` + `IsStrictOrderedRing`).

This is the ordered-field part of BPR Proposition 3.11; the real-closedness (the intermediate value
property) is treated separately. -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Positivity of a representative -/

/-- A representative is **positive** if it is eventually positive near `0⁺`. -/
def SemialgGermRep.IsPos (f : SemialgGermRep R) : Prop :=
  ∃ t, 0 < t ∧ ∀ s : R, 0 < s → s < t → 0 < f.toFun (constPt s)

theorem SemialgGermRep.IsPos.welldef {f g : SemialgGermRep R} (h : f ≈ g) :
    f.IsPos ↔ g.IsPos := by
  obtain ⟨t, ht, H⟩ := h
  constructor
  · rintro ⟨tf, htf, Hf⟩
    refine ⟨min t tf, lt_min ht htf, fun s hs hst => ?_⟩
    rw [← H s hs (lt_of_lt_of_le hst (min_le_left _ _))]
    exact Hf s hs (lt_of_lt_of_le hst (min_le_right _ _))
  · rintro ⟨tg, htg, Hg⟩
    refine ⟨min t tg, lt_min ht htg, fun s hs hst => ?_⟩
    rw [H s hs (lt_of_lt_of_le hst (min_le_left _ _))]
    exact Hg s hs (lt_of_lt_of_le hst (min_le_right _ _))

theorem SemialgGermRep.not_isPos_zero : ¬ (SemialgGermRep.zero : SemialgGermRep R).IsPos := by
  rintro ⟨t, ht, H⟩
  have := H (t / 2) (by linarith) (by linarith)
  simp only [SemialgGermRep.zero_toFun, Pi.zero_apply] at this
  exact lt_irrefl 0 this

theorem SemialgGermRep.IsPos.add {f g : SemialgGermRep R} (hf : f.IsPos) (hg : g.IsPos) :
    (f.add g).IsPos := by
  obtain ⟨tf, htf, Hf⟩ := hf
  obtain ⟨tg, htg, Hg⟩ := hg
  refine ⟨min tf tg, lt_min htf htg, fun s hs hst => ?_⟩
  simp only [SemialgGermRep.add_toFun, Pi.add_apply]
  have h1 := Hf s hs (lt_of_lt_of_le hst (min_le_left _ _))
  have h2 := Hg s hs (lt_of_lt_of_le hst (min_le_right _ _))
  linarith

theorem SemialgGermRep.IsPos.mul {f g : SemialgGermRep R} (hf : f.IsPos) (hg : g.IsPos) :
    (f.mul g).IsPos := by
  obtain ⟨tf, htf, Hf⟩ := hf
  obtain ⟨tg, htg, Hg⟩ := hg
  refine ⟨min tf tg, lt_min htf htg, fun s hs hst => ?_⟩
  simp only [SemialgGermRep.mul_toFun, Pi.mul_apply]
  exact mul_pos (Hf s hs (lt_of_lt_of_le hst (min_le_left _ _)))
    (Hg s hs (lt_of_lt_of_le hst (min_le_right _ _)))

theorem SemialgGermRep.IsPos.not_neg {f : SemialgGermRep R} (hf : f.IsPos) :
    ¬ (f.neg).IsPos := by
  rintro ⟨tn, htn, Hn⟩
  obtain ⟨tf, htf, Hf⟩ := hf
  have hm : 0 < min tf tn := lt_min htf htn
  have h1 := Hf (min tf tn / 2) (by linarith) (by linarith [min_le_left tf tn])
  have h2 := Hn (min tf tn / 2) (by linarith) (by linarith [min_le_right tf tn])
  simp only [SemialgGermRep.neg_toFun, Pi.neg_apply] at h2
  linarith

/-- **Sign trichotomy.** Every representative is eventually positive, eventually zero, or eventually
negative. -/
theorem SemialgGermRep.trichotomy (f : SemialgGermRep R) :
    f.IsPos ∨ f ≈ SemialgGermRep.zero ∨ (f.neg).IsPos := by
  have hApos : IsSemialgebraicSet (rightNbhd f.bound ∩
      (scalarFun f.toFun) ⁻¹' {v : Fin 1 → R | 0 < MvPolynomial.eval v (MvPolynomial.X 0)}) :=
    (proposition_2_83 f.isSemialgContinuous.1).2 (IsSemialgebraicSet.gtZero _)
  have hAneg : IsSemialgebraicSet (rightNbhd f.bound ∩
      (scalarFun f.toFun) ⁻¹' {v : Fin 1 → R | MvPolynomial.eval v (MvPolynomial.X 0) < 0}) :=
    (proposition_2_83 f.isSemialgContinuous.1).2 (IsSemialgebraicSet.ltZero _)
  have hmemPos : ∀ s : R, s ∈ constPt ⁻¹' (rightNbhd f.bound ∩
      (scalarFun f.toFun) ⁻¹' {v : Fin 1 → R | 0 < MvPolynomial.eval v (MvPolynomial.X 0)}) ↔
      (0 < s ∧ s < f.bound) ∧ 0 < f.toFun (constPt s) := fun s => by
    simp only [Set.mem_preimage, Set.mem_inter_iff, rightNbhd, Set.mem_ofPred_eq,
      MvPolynomial.eval_X, scalarFun, constPt]
  have hmemNeg : ∀ s : R, s ∈ constPt ⁻¹' (rightNbhd f.bound ∩
      (scalarFun f.toFun) ⁻¹' {v : Fin 1 → R | MvPolynomial.eval v (MvPolynomial.X 0) < 0}) ↔
      (0 < s ∧ s < f.bound) ∧ f.toFun (constPt s) < 0 := fun s => by
    simp only [Set.mem_preimage, Set.mem_inter_iff, rightNbhd, Set.mem_ofPred_eq,
      MvPolynomial.eval_X, scalarFun, constPt]
  rcases FUOC_dichotomy_at_zero (semialgebraic_sect_FUOC hApos) with ⟨t, ht, hsub⟩ | ⟨t, ht, hdisj⟩
  · exact Or.inl ⟨t, ht, fun s hs hst => ((hmemPos s).mp (hsub ⟨hs, hst⟩)).2⟩
  · rcases FUOC_dichotomy_at_zero (semialgebraic_sect_FUOC hAneg) with
      ⟨t2, ht2, hsub2⟩ | ⟨t2, ht2, hdisj2⟩
    · refine Or.inr (Or.inr ⟨t2, ht2, fun s hs hst => ?_⟩)
      have := ((hmemNeg s).mp (hsub2 ⟨hs, hst⟩)).2
      simp only [SemialgGermRep.neg_toFun, Pi.neg_apply]; linarith
    · refine Or.inr (Or.inl ⟨min (min t t2) f.bound,
        lt_min (lt_min ht ht2) f.bound_pos, fun s hs hst => ?_⟩)
      simp only [SemialgGermRep.zero_toFun, Pi.zero_apply]
      have hsb : s < f.bound := lt_of_lt_of_le hst (min_le_right _ _)
      have hst1 : s < t := lt_of_lt_of_le hst (le_trans (min_le_left _ _) (min_le_left _ _))
      have hst2 : s < t2 := lt_of_lt_of_le hst (le_trans (min_le_left _ _) (min_le_right _ _))
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [Set.eq_empty_iff_forall_notMem] at hdisj2
        exact hdisj2 s ⟨⟨hs, hst2⟩, (hmemNeg s).mpr ⟨⟨hs, hsb⟩, hlt⟩⟩
      · rw [Set.eq_empty_iff_forall_notMem] at hdisj
        exact hdisj s ⟨⟨hs, hst1⟩, (hmemPos s).mpr ⟨⟨hs, hsb⟩, hgt⟩⟩

/-! ### Positivity of a germ -/

/-- A germ is **positive** if (any) representative is eventually positive. -/
def IsPosGerm : SemialgGerm R → Prop :=
  Quotient.lift SemialgGermRep.IsPos fun _ _ h => propext (SemialgGermRep.IsPos.welldef h)

theorem isPosGerm_mk (f : SemialgGermRep R) :
    IsPosGerm (Quotient.mk _ f : SemialgGerm R) = f.IsPos := rfl

theorem not_isPosGerm_zero : ¬ IsPosGerm (0 : SemialgGerm R) :=
  SemialgGermRep.not_isPos_zero

theorem isPosGerm_add {a b : SemialgGerm R} (ha : IsPosGerm a) (hb : IsPosGerm b) :
    IsPosGerm (a + b) := by
  induction a using Quotient.inductionOn with
  | _ f => induction b using Quotient.inductionOn with
    | _ g => rw [germ_mk_add]; exact SemialgGermRep.IsPos.add ha hb

theorem isPosGerm_mul {a b : SemialgGerm R} (ha : IsPosGerm a) (hb : IsPosGerm b) :
    IsPosGerm (a * b) := by
  induction a using Quotient.inductionOn with
  | _ f => induction b using Quotient.inductionOn with
    | _ g => rw [germ_mk_mul]; exact SemialgGermRep.IsPos.mul ha hb

theorem isPosGerm_not_neg {a : SemialgGerm R} (ha : IsPosGerm a) : ¬ IsPosGerm (-a) := by
  induction a using Quotient.inductionOn with
  | _ f => rw [germ_mk_neg]; exact SemialgGermRep.IsPos.not_neg ha

theorem isPosGerm_trichotomy (a : SemialgGerm R) :
    IsPosGerm a ∨ a = 0 ∨ IsPosGerm (-a) := by
  induction a using Quotient.inductionOn with
  | _ f =>
    rcases f.trichotomy with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Quotient.sound h))
    · exact Or.inr (Or.inr (by rw [germ_mk_neg]; exact h))

/-! ### The order -/

noncomputable instance : LinearOrder (SemialgGerm R) where
  le a b := IsPosGerm (b - a) ∨ a = b
  lt a b := IsPosGerm (b - a)
  le_refl a := Or.inr rfl
  le_trans a b c hab hbc := by
    rcases hab with hab | rfl
    · rcases hbc with hbc | rfl
      · refine Or.inl ?_
        have := isPosGerm_add hbc hab
        rwa [show (c - b) + (b - a) = c - a by ring] at this
      · exact Or.inl hab
    · exact hbc
  lt_iff_le_not_ge a b := by
    constructor
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (h2 | rfl)
      · exact isPosGerm_not_neg h (by rwa [← neg_sub] at h2)
      · exact not_isPosGerm_zero (by rwa [sub_self] at h)
    · rintro ⟨h1 | rfl, h2⟩
      · exact h1
      · exact absurd (Or.inr rfl) h2
  le_antisymm a b hab hba := by
    rcases hab with hab | rfl
    · rcases hba with hba | h
      · exact absurd (show IsPosGerm (-(b - a)) by rw [neg_sub]; exact hba) (isPosGerm_not_neg hab)
      · exact h.symm
    · rfl
  le_total a b := by
    rcases isPosGerm_trichotomy (b - a) with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (by rw [sub_eq_zero] at h; exact h.symm))
    · exact Or.inr (Or.inl (by rwa [neg_sub] at h))
  toDecidableLE := Classical.decRel _

theorem SemialgGerm.lt_zero_iff {a : SemialgGerm R} : 0 < a ↔ IsPosGerm a := by
  show IsPosGerm (a - 0) ↔ IsPosGerm a; rw [sub_zero]

theorem isPosGerm_one : IsPosGerm (1 : SemialgGerm R) := by
  show (SemialgGermRep.one : SemialgGermRep R).IsPos
  exact ⟨1, one_pos, fun s _ _ => by simp only [SemialgGermRep.one_toFun, Pi.one_apply]; exact one_pos⟩

instance : ZeroLEOneClass (SemialgGerm R) :=
  ⟨Or.inl (by rw [sub_zero]; exact isPosGerm_one)⟩

instance : IsOrderedAddMonoid (SemialgGerm R) where
  add_le_add_left a b hab c := by
    rcases hab with hab | rfl
    · refine Or.inl ?_
      rwa [show b + c - (a + c) = b - a by ring]
    · exact Or.inr rfl

noncomputable instance : IsStrictOrderedRing (SemialgGerm R) :=
  IsStrictOrderedRing.of_mul_pos fun _ _ ha hb =>
    SemialgGerm.lt_zero_iff.mpr
      (isPosGerm_mul (SemialgGerm.lt_zero_iff.mp ha) (SemialgGerm.lt_zero_iff.mp hb))

end Azurite.BPR
