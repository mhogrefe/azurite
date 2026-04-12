import Azurite.AzPolynomial.Tru
import Azurite.AzPolynomial.Equiv.Truncate
import Azurite.AzMvPolynomial.Equiv.Algebra

/-!
# Equivalence: `AzPolynomial.tru` ↔ BPR's `Tru`

Shows that Azurite's computable `tru` on
`AzPolynomial (AzMvPolynomial k D ord)` agrees with BPR's
noncomputable `Tru` on `Polynomial (MvPolynomial (Fin k) D)`
under the combined `liftPoly` bridge.
-/

namespace Azurite

open AzMvPolynomial Polynomial

variable {k : ℕ} {D : Type _} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}

/-! ### isConstant equivalence -/

omit [IsDomain D] in
private theorem ofMvPoly_C (d : D) :
    (AzMvPolynomial.ofMvPoly (MvPolynomial.C d) : AzMvPolynomial k D ord) =
      AzMvPolynomial.C d :=
  toMvPoly_injective (by rw [toMvPoly_ofMvPoly, toMvPoly_C])

omit [IsDomain D] in
/-- `isConstant p = true` iff `toMvPoly p` lies in the image of
`MvPolynomial.C`, i.e. `p` is a constant polynomial. -/
theorem AzMvPolynomial.isConstant_iff
    (p : AzMvPolynomial k D ord) :
    p.isConstant = true ↔ ∃ d : D, p.toMvPoly = MvPolynomial.C d := by
  constructor
  · intro h
    unfold AzMvPolynomial.isConstant at h
    match ht : p.terms.toList with
    | [] =>
      refine ⟨0, ?_⟩
      have hp0 : p.terms = #[] := by rwa [← Array.toList_eq_nil_iff]
      have : p = 0 := by
        show p = AzMvPolynomial.zero
        cases p with | mk ts hs =>
        unfold AzMvPolynomial.zero; congr 1
      rw [this]; simp
    | [m] =>
      rw [ht] at h; simp only [beq_iff_eq] at h
      have hp : p = AzMvPolynomial.ofMonomial m := by
        cases p with | mk ts hs =>
        show _ = AzMvPolynomial.ofMonomial m
        unfold AzMvPolynomial.ofMonomial
        congr 1
        exact Array.ext' ht
      rw [hp]
      have hC : AzMvPolynomial.ofMonomial m =
          (AzMvPolynomial.C m.coeff.val : AzMvPolynomial k D ord) := by
        unfold AzMvPolynomial.C
        rw [dif_neg m.coeff.property]
        unfold AzMvPolynomial.ofMonomial; congr 1
        cases m with | mk c mc =>
        simp only at h; subst h; rfl
      exact ⟨m.coeff.val, by rw [hC, toMvPoly_C]⟩
    | _ :: _ :: _ =>
      rw [ht] at h; simp at h
  · rintro ⟨d, hd⟩
    have hp : p = AzMvPolynomial.ofMvPoly (MvPolynomial.C d) := by
      rw [← ofMvPoly_toMvPoly p, hd]
    rw [hp, ofMvPoly_C]
    unfold AzMvPolynomial.isConstant AzMvPolynomial.C
    by_cases hd0 : d = 0
    · simp [hd0]
    · simp [hd0, AzMvPolynomial.ofMonomial, MonicMonomial.one]

/-! ### The combined bridge -/

/-- Combined bridge from `AzPolynomial (AzMvPolynomial k D ord)` to
`Polynomial (MvPolynomial (Fin k) D)`: first lift to `Polynomial`
via `toPoly`, then map coefficients via `toMvPolyHom`. -/
noncomputable def liftPoly (p : AzPolynomial (AzMvPolynomial k D ord)) :
    Polynomial (MvPolynomial (Fin k) D) :=
  Polynomial.map (AzMvPolynomial.toMvPolyHom) (AzPolynomial.toPoly p)

/-! ### Bridge lemmas for `liftPoly` -/

private theorem toMvPolyHom_injective :
    Function.Injective (AzMvPolynomial.toMvPolyHom (R := D) (n := k) (ord := ord)) :=
  fun _ _ h => toMvPoly_injective h

theorem liftPoly_injective :
    Function.Injective (liftPoly (k := k) (D := D) (ord := ord)) := by
  intro p q h
  unfold liftPoly at h
  exact (_root_.toPoly_inj (R := AzMvPolynomial k D ord)).mp
    (Polynomial.map_injective _ toMvPolyHom_injective h)

@[simp] theorem liftPoly_zero :
    liftPoly (0 : AzPolynomial (AzMvPolynomial k D ord)) = 0 := by
  unfold liftPoly
  rw [_root_.toPoly_zero, Polynomial.map_zero]

theorem liftPoly_eq_zero_iff (p : AzPolynomial (AzMvPolynomial k D ord)) :
    liftPoly p = 0 ↔ p = 0 := by
  constructor
  · intro h; exact liftPoly_injective (by rwa [liftPoly_zero])
  · rintro rfl; exact liftPoly_zero

@[simp] theorem liftPoly_natDegree (p : AzPolynomial (AzMvPolynomial k D ord)) :
    (liftPoly p).natDegree = p.natDegree := by
  unfold liftPoly
  rw [Polynomial.natDegree_map_eq_of_injective toMvPolyHom_injective,
      AzPolynomial.natDegree_toPoly]

@[simp] theorem liftPoly_leadingCoeff (p : AzPolynomial (AzMvPolynomial k D ord)) :
    (liftPoly p).leadingCoeff = p.leadingCoeff.toMvPoly := by
  unfold liftPoly
  conv_lhs => rw [Polynomial.leadingCoeff, Polynomial.natDegree_map_eq_of_injective
    toMvPolyHom_injective, Polynomial.coeff_map]
  show toMvPolyHom ((AzPolynomial.toPoly p).coeff (AzPolynomial.toPoly p).natDegree) =
    p.leadingCoeff.toMvPoly
  simp [AzMvPolynomial.toMvPolyHom, Azurite.AzPolynomial.leadingCoeff]

@[simp] theorem liftPoly_truncate (i : ℕ)
    (p : AzPolynomial (AzMvPolynomial k D ord)) :
    liftPoly (AzPolynomial.truncate i p) =
      BPR.truncate i (liftPoly p) := by
  unfold liftPoly
  rw [AzPolynomial.toPoly_truncate]
  ext j
  simp only [BPR.coeff_truncate, Polynomial.coeff_map]
  split <;> simp [map_zero]

/-! ### Main equivalence -/

/-- The computable `tru` agrees with BPR's `Tru` under the `liftPoly`
bridge: an element belongs to `tru p` iff its image under `liftPoly`
belongs to `Tru (liftPoly p)`. -/
private theorem isConstant_leadingCoeff_iff
    (p : AzPolynomial (AzMvPolynomial k D ord)) :
    p.leadingCoeff.isConstant = true ↔
      ∃ d : D, (liftPoly p).leadingCoeff = MvPolynomial.C d := by
  rw [liftPoly_leadingCoeff, AzMvPolynomial.isConstant_iff]

theorem mem_tru_iff_mem_Tru (p q : AzPolynomial (AzMvPolynomial k D ord)) :
    q ∈ AzPolynomial.tru p ↔ liftPoly q ∈ BPR.Tru (liftPoly p) := by
  suffices ∀ n, ∀ p : AzPolynomial (AzMvPolynomial k D ord),
      p.natDegree ≤ n →
      (q ∈ AzPolynomial.tru p ↔ liftPoly q ∈ BPR.Tru (liftPoly p)) from
    this p.natDegree p le_rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro p hpn
  conv_lhs => rw [AzPolynomial.tru]
  conv_rhs => rw [BPR.Tru]
  -- Match the zero case
  by_cases h0 : p = 0
  · subst h0; simp
  -- Match the base case
  · have hlift_ne : liftPoly p ≠ 0 := (liftPoly_eq_zero_iff p).not.mpr h0
    simp only [beq_iff_eq, h0, hlift_ne, ↓reduceIte, Bool.or_eq_true]
    by_cases hbase : p.leadingCoeff.isConstant = true ∨ p.natDegree = 0
    · have hbase' : (∃ d : D, (liftPoly p).leadingCoeff = MvPolynomial.C d) ∨
          (liftPoly p).natDegree = 0 := by
        rcases hbase with hc | hd
        · exact Or.inl (isConstant_leadingCoeff_iff p |>.mp hc)
        · exact Or.inr (by rw [liftPoly_natDegree]; exact hd)
      rw [if_pos hbase, if_pos hbase']
      simp only [List.mem_singleton, Set.mem_singleton_iff]
      exact ⟨fun h => congrArg liftPoly h, fun h => liftPoly_injective h⟩
    -- Recursive case
    · push Not at hbase
      have hbase' : ¬((∃ d : D, (liftPoly p).leadingCoeff = MvPolynomial.C d) ∨
          (liftPoly p).natDegree = 0) := by
        rintro (⟨d, hd⟩ | hd)
        · exact hbase.1 ((isConstant_leadingCoeff_iff p).mpr ⟨d, hd⟩)
        · rw [liftPoly_natDegree] at hd; exact hbase.2 hd
      rw [if_neg (not_or.mpr hbase), if_neg hbase']
      rw [List.mem_cons, Set.mem_union, Set.mem_singleton_iff]
      rw [liftPoly_natDegree]
      have hlt : (AzPolynomial.truncate (p.natDegree - 1) p).natDegree < p.natDegree := by
        have := AzPolynomial.natDegree_truncate_le (p.natDegree - 1) p
        have : 0 < p.natDegree := Nat.pos_of_ne_zero hbase.2
        omega
      set t := AzPolynomial.truncate (p.natDegree - 1) p
      constructor
      · rintro (rfl | hmem)
        · left; rfl
        · right; rw [← liftPoly_truncate]; exact (ih t.natDegree (by omega) t le_rfl).mp hmem
      · rintro (heq | hmem)
        · left; exact liftPoly_injective heq
        · right; rw [← liftPoly_truncate] at hmem; exact (ih t.natDegree (by omega) t le_rfl).mpr hmem

end Azurite
