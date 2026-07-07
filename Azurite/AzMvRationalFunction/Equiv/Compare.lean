import Azurite.AzMvRationalFunction.Compare
import Azurite.AzMvRationalFunction.Equiv.Parse
import Azurite.AzMvPolynomial.Equiv.Compare

/-!
# The `LinearOrder` on `AzMvRationalFunction`

Lawfulness of the display-fraction comparison of
`Azurite.AzMvRationalFunction.Compare`: the `LinearOrder AzMvRationalFunction`
instance in the house style (`compare := compare` with
`compare_eq_compareOfLessAndEq`), built on the lawful `AzMvPolynomial` order
lexicographically (denominator first) — the display pair determines the value
(`ofNumDen_displayNum_displayDen`), so comparison-equality is equality.

Plus the order-embedding theorems: a polynomial displays as `(p, 1)`
(`displayNum_ofMvPolynomial` / `displayDen_ofMvPolynomial`), so the canonical
map `ofMvPolynomial` is strictly order-preserving (`ofMvPolynomial_lt_iff`,
`ofMvPolynomial_strictMono`).
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-! ### Component shims: the raw `AzMvPolynomial.compare` vs the lawful order -/

private theorem pcmp_lt {p q : AzMvPolynomial n AzInt ord} :
    AzMvPolynomial.compare p q = .lt ↔ p < q := by
  show Ord.compare p q = .lt ↔ p < q
  exact compare_lt_iff_lt

private theorem pcmp_eq {p q : AzMvPolynomial n AzInt ord} :
    AzMvPolynomial.compare p q = .eq ↔ p = q := by
  show Ord.compare p q = .eq ↔ p = q
  exact compare_eq_iff_eq

private theorem pcmp_gt {p q : AzMvPolynomial n AzInt ord} :
    AzMvPolynomial.compare p q = .gt ↔ q < p := by
  show Ord.compare p q = .gt ↔ q < p
  exact compare_gt_iff_gt

/-! ### Laws of the display-lexicographic comparison -/

/-- Equal displays mean equal values: the display pair re-normalizes to the
original. -/
private theorem eq_of_display_eq {r s : AzMvRationalFunction n ord}
    (hn : displayNum r = displayNum s) (hd : displayDen r = displayDen s) : r = s := by
  rw [← ofNumDen_displayNum_displayDen r, ← ofNumDen_displayNum_displayDen s, hn, hd]

private theorem compare_self' (r : AzMvRationalFunction n ord) : compare r r = .eq := by
  rw [compare, pcmp_eq.mpr rfl]
  show AzMvPolynomial.compare (displayNum r) (displayNum r) = .eq
  exact pcmp_eq.mpr rfl

private theorem compare_swap' (r s : AzMvRationalFunction n ord) :
    compare s r = (compare r s).swap := by
  rw [compare, compare]
  rcases lt_trichotomy (displayDen r) (displayDen s) with h | h | h
  · rw [pcmp_lt.mpr h, pcmp_gt.mpr h]
    rfl
  · rw [pcmp_eq.mpr h, pcmp_eq.mpr h.symm]
    show AzMvPolynomial.compare (displayNum s) (displayNum r)
      = (AzMvPolynomial.compare (displayNum r) (displayNum s)).swap
    rcases lt_trichotomy (displayNum r) (displayNum s) with h2 | h2 | h2
    · rw [pcmp_lt.mpr h2, pcmp_gt.mpr h2]
      rfl
    · rw [pcmp_eq.mpr h2, pcmp_eq.mpr h2.symm]
      rfl
    · rw [pcmp_gt.mpr h2, pcmp_lt.mpr h2]
      rfl
  · rw [pcmp_gt.mpr h, pcmp_lt.mpr h]
    rfl

private theorem eq_of_compare_eq' {r s : AzMvRationalFunction n ord}
    (h : compare r s = .eq) : r = s := by
  rw [compare] at h
  rcases hdd : AzMvPolynomial.compare (displayDen r) (displayDen s) with _ | _ | _ <;>
    rw [hdd] at h
  · simp at h
  · have h2 : AzMvPolynomial.compare (displayNum r) (displayNum s) = .eq := h
    exact eq_of_display_eq (pcmp_eq.mp h2) (pcmp_eq.mp hdd)
  · simp at h

private theorem compare_trans' {r s t : AzMvRationalFunction n ord}
    (h1 : compare r s ≠ .gt) (h2 : compare s t ≠ .gt) : compare r t ≠ .gt := by
  rw [compare] at h1 h2 ⊢
  rcases lt_trichotomy (displayDen r) (displayDen s) with hab | hab | hab <;>
    rcases lt_trichotomy (displayDen s) (displayDen t) with hbc | hbc | hbc
  · rw [pcmp_lt.mpr (hab.trans hbc)]
    simp
  · rw [pcmp_lt.mpr (hbc ▸ hab)]
    simp
  · rw [pcmp_gt.mpr hbc] at h2
    exact absurd rfl h2
  · rw [pcmp_lt.mpr (by rw [hab]; exact hbc)]
    simp
  · -- equal display denominators throughout: numerators compose
    rw [pcmp_eq.mpr (hab.trans hbc)]
    rw [pcmp_eq.mpr hab] at h1
    rw [pcmp_eq.mpr hbc] at h2
    have h1' : AzMvPolynomial.compare (displayNum r) (displayNum s) ≠ .gt := h1
    have h2' : AzMvPolynomial.compare (displayNum s) (displayNum t) ≠ .gt := h2
    show AzMvPolynomial.compare (displayNum r) (displayNum t) ≠ .gt
    rw [Ne, pcmp_gt] at h1' h2' ⊢
    exact fun hlt => absurd hlt (not_lt.mpr ((not_lt.mp h1').trans (not_lt.mp h2')))
  · rw [pcmp_gt.mpr hbc] at h2
    exact absurd rfl h2
  · rw [pcmp_gt.mpr hab] at h1
    exact absurd rfl h1
  · rw [pcmp_gt.mpr hab] at h1
    exact absurd rfl h1
  · rw [pcmp_gt.mpr hab] at h1
    exact absurd rfl h1

/-! ### The `LinearOrder` instance -/

instance : LinearOrder (AzMvRationalFunction n ord) where
  le_refl r := by
    show compare r r ≠ .gt
    rw [compare_self']
    simp
  le_trans _ _ _ := compare_trans'
  le_antisymm r s h1 h2 := by
    have h2' : (compare r s).swap ≠ .gt := by
      rw [← compare_swap']
      exact h2
    apply eq_of_compare_eq'
    rcases h : compare r s with _ | _ | _
    · rw [h] at h2'
      exact absurd rfl h2'
    · rfl
    · exact absurd h h1
  le_total r s := by
    show compare r s ≠ .gt ∨ compare s r ≠ .gt
    rw [compare_swap' r s]
    rcases compare r s with _ | _ | _ <;> simp
  lt_iff_le_not_ge r s := by
    show compare r s = .lt ↔ compare r s ≠ .gt ∧ ¬ compare s r ≠ .gt
    rw [compare_swap' r s]
    rcases compare r s with _ | _ | _ <;> simp
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  min_def := fun _ _ => rfl
  max_def := fun _ _ => rfl
  compare := compare
  compare_eq_compareOfLessAndEq r s := by
    rw [compareOfLessAndEq]
    rcases h : compare r s with _ | _ | _
    · rw [if_pos (show r < s from h)]
    · rw [if_neg (show ¬ r < s from fun h2 => by
            rw [show compare r s = .lt from h2] at h
            exact absurd h (by simp)),
        if_pos (eq_of_compare_eq' h)]
    · rw [if_neg (show ¬ r < s from fun h2 => by
            rw [show compare r s = .lt from h2] at h
            exact absurd h (by simp)),
        if_neg (fun h2 => by
          subst h2
          rw [compare_self'] at h
          exact absurd h (by simp))]

/-! ### Helper facts about the constant `1` and the `ofNumDen` cofactor -/

private theorem sic_one : signedIntContent (1 : AzMvPolynomial n AzInt ord) = 1 := by
  rw [signedIntContent,
    if_pos (by rw [show leadingCoeff (1 : AzMvPolynomial n AzInt ord) = 1 from rfl]; decide)]
  rfl

private theorem signNorm_one : signNorm (1 : AzMvPolynomial n AzInt ord) = 1 := by
  rw [signNorm,
    if_pos (by rw [show leadingCoeff (1 : AzMvPolynomial n AzInt ord) = 1 from rfl]; decide)]

private theorem exactDiv_one (X : AzMvPolynomial n AzInt ord) :
    Azurite.ExactDiv.exactDiv X 1 = X := by
  have h := Azurite.ExactDiv.exactDiv_mul_self X 1 (one_dvd X) one_ne_zero
  rwa [mul_one] at h

private theorem C_one : (AzMvPolynomial.C (1 : AzInt) : AzMvPolynomial n AzInt ord) = 1 := by
  apply toMvPoly_injective
  rw [toMvPoly_C, show toMvPoly (1 : AzMvPolynomial n AzInt ord) = 1 from map_one toMvPolyHom,
    map_one]

private theorem primPos_one : primPos (1 : AzMvPolynomial n AzInt ord) = 1 := by
  rw [primPos, sic_one, C_one, exactDiv_one]

private theorem gcd_one_right' (Q : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial.gcd Q 1 = 1 := by
  apply toNested_injective (n := n)
  apply (towerBridge n).injective
  rw [towerBridge_toNested_gcd, toNested_one, map_one, gcd_one_right]

/-- The sign-normalized gcd cofactor of `ofNumDen p 1` is trivial. -/
private theorem gCofactor_p_one (p : AzMvPolynomial n AzInt ord) :
    signNorm (AzMvPolynomial.gcd (primPos p) (primPos 1)) = 1 := by
  rw [primPos_one, gcd_one_right', signNorm_one]

/-- The signed integer `AzInt` reconstructed from the factor of `ofAzInts a 1`
recovers `a` (nonzero case). -/
private theorem ofAzInts_one_eq_toAzRat {a : AzInt} (ha : a ≠ 0) :
    AzRat.ofAzInts a 1 = a.toAzRat := by
  have habs : a.abs ≠ 0 := by
    intro h; apply ha
    have hs := a.zero_sign h
    obtain ⟨s, ab, zs⟩ := a
    simp only at h hs; subst h; subst hs; rfl
  rw [AzRat.ofAzInts]
  show AzRat.ofSignAzNats (a.sign == (1 : AzInt).sign) a.abs (1 : AzInt).abs = a.toAzRat
  rw [AzRat.ofSignAzNats, dif_neg (show (1 : AzInt).abs ≠ 0 by decide), dif_neg habs]
  apply AzRat.ext
  · show (a.sign == true) = a.sign
    cases a.sign <;> rfl
  · show a.abs / AzNat.gcd a.abs (1 : AzInt).abs = a.abs
    apply Azurite.AzNat.toNat_injective
    rw [Azurite.AzNat.toNat_div, Azurite.AzNat.toNat_gcd]
    show a.abs.toNat / Nat.gcd a.abs.toNat (1 : AzNat).toNat = a.abs.toNat
    rw [Azurite.AzNat.toNat_one, Nat.gcd_one_right, Nat.div_one]
  · show (1 : AzNat) / AzNat.gcd a.abs (1 : AzInt).abs = 1
    apply Azurite.AzNat.toNat_injective
    rw [Azurite.AzNat.toNat_div, Azurite.AzNat.toNat_gcd]
    show (1 : AzNat).toNat / Nat.gcd a.abs.toNat (1 : AzNat).toNat = (1 : AzNat).toNat
    rw [Azurite.AzNat.toNat_one, Nat.gcd_one_right, Nat.div_one]

/-! ### The display of `ofMvPolynomial` -/

private theorem display_ofMvPolynomial (p : AzMvPolynomial n AzInt ord) :
    displayNum (ofMvPolynomial p) = p ∧ displayDen (ofMvPolynomial p) = 1 := by
  by_cases hp : p = 0
  · -- zero: `ofMvPolynomial 0 = 0`, which displays as `(0, 1)`
    subst hp
    have h0 : ofMvPolynomial (0 : AzMvPolynomial n AzInt ord) = 0 := by
      show ofNumDen 0 1 = 0
      rw [ofNumDen, if_pos (Or.inl rfl)]
    rw [h0]
    refine ⟨?_, ?_⟩
    · show (⟨(0 : AzRat).sign, (0 : AzRat).num, (0 : AzRat).zero_sign⟩ : AzInt)
          • (1 : AzMvPolynomial n AzInt ord) = 0
      rw [show (⟨(0 : AzRat).sign, (0 : AzRat).num, (0 : AzRat).zero_sign⟩ : AzInt) = 0 from rfl,
        zero_smul]
    · show (⟨true, (0 : AzRat).den, fun _ => rfl⟩ : AzInt)
          • (1 : AzMvPolynomial n AzInt ord) = 1
      rw [show (⟨true, (0 : AzRat).den, fun _ => rfl⟩ : AzInt) = 1 from rfl, one_smul]
  · have hp1 : (1 : AzMvPolynomial n AzInt ord) ≠ 0 := one_ne_zero
    set r := ofMvPolynomial p with hr
    have hrnum : r.num = primPos p := by
      rw [hr, ofMvPolynomial, ofNumDen_num hp hp1]
      show Azurite.ExactDiv.exactDiv (primPos p)
        (signNorm (AzMvPolynomial.gcd (primPos p) (primPos 1))) = primPos p
      rw [gCofactor_p_one, exactDiv_one]
    have hrden : r.den = 1 := by
      rw [hr, ofMvPolynomial, ofNumDen_den hp hp1]
      show Azurite.ExactDiv.exactDiv (primPos 1)
        (signNorm (AzMvPolynomial.gcd (primPos p) (primPos 1))) = 1
      rw [gCofactor_p_one, exactDiv_one, primPos_one]
    have hfactor : r.factor = (signedIntContent p).toAzRat := by
      rw [hr, ofMvPolynomial, ofNumDen_factor hp hp1, sic_one]
      exact ofAzInts_one_eq_toAzRat (signedIntContent_ne_zero hp)
    refine ⟨?_, ?_⟩
    · show (⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt) • r.num = p
      rw [hrnum]
      have haint : (⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt)
          = signedIntContent p := by rw [hfactor]; rfl
      rw [haint, ← C_mul_eq_smul]
      exact primPos_factorization p
    · show (⟨true, r.factor.den, fun _ => rfl⟩ : AzInt) • r.den = 1
      rw [hrden]
      have hden1 : (⟨true, r.factor.den, fun _ => rfl⟩ : AzInt) = 1 := by rw [hfactor]; rfl
      rw [hden1, one_smul]

/-- A polynomial displays with itself as the numerator. -/
theorem displayNum_ofMvPolynomial (p : AzMvPolynomial n AzInt ord) :
    displayNum (ofMvPolynomial p) = p :=
  (display_ofMvPolynomial p).1

/-- A polynomial displays with denominator `1`. -/
theorem displayDen_ofMvPolynomial (p : AzMvPolynomial n AzInt ord) :
    displayDen (ofMvPolynomial p) = 1 :=
  (display_ofMvPolynomial p).2

/-! ### The canonical map preserves order -/

/-- `ofMvPolynomial` reflects and preserves the strict order. -/
theorem ofMvPolynomial_lt_iff {p q : AzMvPolynomial n AzInt ord} :
    ofMvPolynomial p < ofMvPolynomial q ↔ p < q := by
  show compare (ofMvPolynomial p) (ofMvPolynomial q) = .lt ↔ p < q
  rw [compare, displayDen_ofMvPolynomial, displayDen_ofMvPolynomial, pcmp_eq.mpr rfl]
  show AzMvPolynomial.compare (displayNum (ofMvPolynomial p))
    (displayNum (ofMvPolynomial q)) = .lt ↔ p < q
  rw [displayNum_ofMvPolynomial, displayNum_ofMvPolynomial]
  exact pcmp_lt

/-- **The canonical map preserves order.** -/
theorem ofMvPolynomial_strictMono :
    StrictMono (ofMvPolynomial (n := n) (ord := ord)) :=
  fun _ _ h => ofMvPolynomial_lt_iff.mpr h

end Azurite.AzMvRationalFunction
