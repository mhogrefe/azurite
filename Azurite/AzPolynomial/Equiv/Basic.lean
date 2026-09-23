import Azurite.AzPolynomial.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Lemmas

open Polynomial

variable {R : Type _} [Semiring R]

/-- Evaluates a list of coefficients into a mathlib `Polynomial R` -/
noncomputable def List.toPoly : List R → Polynomial R
| [] => 0
| a :: as => C a + X * as.toPoly

/-- Converts a `AzPolynomial` into a mathlib `Polynomial R` -/
noncomputable def AzPolynomial.toPoly (p : Azurite.AzPolynomial R) : Polynomial R :=
  p.coeffs.toList.toPoly

/-- Converts a mathlib `Polynomial R` into a list of coefficients from 0 to natDegree -/
noncomputable def Polynomial.toDenseList [DecidableEq R] (p : Polynomial R) : List R :=
  if p = 0 then [] else (List.range (p.natDegree + 1)).map p.coeff

lemma length_toDenseList [DecidableEq R] (p : Polynomial R) (hp : p ≠ 0) :
  p.toDenseList.length = p.natDegree + 1 := by
  dsimp [Polynomial.toDenseList]
  split
  · contradiction
  · simp

-- We need a proof that `Polynomial.toDenseList` does not end in zero when `p ≠ 0`.
@[simp] lemma last_toDenseList_ne_zero [DecidableEq R] (p : Polynomial R) (hp : p ≠ 0) :
    (p.toDenseList.getLast (by
      intro h
      have h1 : p.toDenseList.length = 0 := List.length_eq_zero_iff.mpr h
      have h2 : p.toDenseList.length = p.natDegree + 1 := length_toDenseList p hp
      omega
    )) = p.leadingCoeff := by
  dsimp [Polynomial.toDenseList]
  split
  · contradiction
  · -- we are in the `else` branch where we map `List.range (p.natDegree + 1)`
    -- length is `natDegree + 1`, so the last element is `natDegree`
    rw [List.getLast_map]
    have : (List.range (p.natDegree + 1)).getLast (by simp) = p.natDegree := by
      rw [List.getLast_range]
      omega
    rw [this]
    rfl

/-- Converts a mathlib `Polynomial R` to `AzPolynomial R` -/
noncomputable def AzPolynomial.ofPoly [DecidableEq R] (p : Polynomial R) : Azurite.AzPolynomial R :=
  if hp : p = 0 then 0 else
  ⟨p.toDenseList.toArray, by
    intro h
    have h_last := last_toDenseList_ne_zero p hp
    have h_coeff := Polynomial.leadingCoeff_ne_zero.mpr hp
    have h_opt : p.toDenseList.toArray.back? = some (p.toDenseList.getLast (by
      intro len_zero
      have h1 : p.toDenseList.length = 0 := List.length_eq_zero_iff.mpr len_zero
      have h2 : p.toDenseList.length = p.natDegree + 1 := length_toDenseList p hp
      omega
    )) := by
      have hw1 : p.toDenseList.toArray.back? = p.toDenseList.toArray.toList.getLast? := by simp
      have hw2 : p.toDenseList.toArray.toList.getLast? = p.toDenseList.getLast? := by simp
      rw [hw1, hw2]
      exact List.getLast?_eq_some_getLast _
    rw [h_last] at h_opt
    rw [h] at h_opt
    injection h_opt with h_eq
    exact h_coeff h_eq.symm
  ⟩

lemma toPoly_dropTrailingZeros [DecidableEq R] (l : List R) :
  (Azurite.AzPolynomial.dropTrailingZeros l).toPoly = l.toPoly := by
  have hw := Azurite.AzPolynomial.eq_dropTrailingZeros_append_takeWhile l
  have h_toPoly (a b : List R) : (a ++ b).toPoly = a.toPoly + X ^ a.length * b.toPoly := by
    induction a with
    | nil => simp [List.toPoly]
    | cons x xs ih =>
      dsimp [List.toPoly]
      rw [ih, mul_add, ← mul_assoc, ← pow_succ']
      have h_assoc : C x + (X * xs.toPoly + X ^ (xs.length + 1) * b.toPoly) = C x + X * xs.toPoly + X ^ (xs.length + 1) * b.toPoly := by exact (add_assoc _ _ _).symm
      rw [h_assoc]
  have h1 : (Azurite.AzPolynomial.dropTrailingZeros l ++ (l.reverse.takeWhile (· = 0)).reverse).toPoly = l.toPoly := by rw [hw]
  rw [h_toPoly] at h1
  -- Now we need to show that ((l.reverse.takeWhile (· = 0)).reverse).toPoly = 0
  have h_zeros_toPoly (z : List R) (hz : ∀ x ∈ z, x = 0) : z.toPoly = 0 := by
    induction z with
    | nil => simp [List.toPoly]
    | cons a as ih =>
      have ha : a = 0 := hz a (by simp)
      have has : as.toPoly = 0 := ih (fun x hx => hz x (by simp [hx]))
      simp [List.toPoly, ha, has]
  have h_takeWhile_zeros_gen (L : List R) : ∀ x ∈ L.takeWhile (· = 0), x = 0 := by
    intro x hx
    induction L with
    | nil => cases hx
    | cons a as ih =>
      simp only [List.takeWhile] at hx
      split at hx
      · next h_eq =>
        cases hx with
        | head => exact beq_iff_eq.mp h_eq
        | tail _ h_in => exact ih h_in
      · next =>
        cases hx
  have h_takeWhile_zeros : ∀ x ∈ (l.reverse.takeWhile (· = 0)).reverse, x = 0 := by
    intro x hx
    rw [List.mem_reverse] at hx
    exact h_takeWhile_zeros_gen (l.reverse) x hx
  have h2 : ((l.reverse.takeWhile (· = 0)).reverse).toPoly = 0 := h_zeros_toPoly _ h_takeWhile_zeros
  rw [h2] at h1
  simp at h1
  exact h1

lemma toPoly_normalize [DecidableEq R] (a : Array R) :
  AzPolynomial.toPoly (Azurite.AzPolynomial.normalize a) = a.toList.toPoly := by
  have h1 : (a.popWhile (· == 0)).toList = Azurite.AzPolynomial.dropTrailingZeros a.toList := Azurite.AzPolynomial.toList_popWhile_eq_dropTrailingZeros a
  -- We establish `(normalize a).toPoly` converts to `(a.popWhile ...).toList.toPoly`
  have h2 : AzPolynomial.toPoly (Azurite.AzPolynomial.normalize a) = (a.popWhile (· == 0)).toList.toPoly := rfl
  rw [h2, h1]
  exact toPoly_dropTrailingZeros a.toList


lemma coeff_toPoly (l : List R) (i : ℕ) :
  (List.toPoly l).coeff i = l.getCoeff i := by
  induction l generalizing i with
  | nil => simp [List.toPoly, List.getCoeff]
  | cons a as ih =>
    cases i
    · simp [List.toPoly, List.getCoeff]
    · simp [List.toPoly, ih, List.getCoeff]

@[simp] lemma coeff_toPoly_eq (p : Azurite.AzPolynomial R) (i : ℕ) :
  (AzPolynomial.toPoly p).coeff i = p.coeff i := by
  dsimp [AzPolynomial.toPoly, Azurite.AzPolynomial.coeff]
  rw [coeff_toPoly]
  dsimp [List.getCoeff]
  have ht : p.coeffs.toList[i]? = p.coeffs[i]? := by simp
  rw [ht]

lemma getCoeff_map_range_coeff [DecidableEq R] (p : Polynomial R) (i : ℕ) :
  ((List.range (p.natDegree + 1)).map p.coeff).getCoeff i = if i ≤ p.natDegree then p.coeff i else 0 := by
  dsimp [List.getCoeff]
  rw [List.getElem?_map]
  by_cases h : i < p.natDegree + 1
  · have h1 : (List.range (p.natDegree + 1))[i]? = some i := List.getElem?_range h
    rw [h1]
    simp
    have h2 : i ≤ p.natDegree := by omega
    simp [h2]
  · have hlen : (List.range (p.natDegree + 1)).length ≤ i := by simp; omega
    have h2 : (List.range (p.natDegree + 1))[i]? = none := List.getElem?_eq_none hlen
    rw [h2]
    simp
    have h3 : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h3]
    have h4 : ¬(i ≤ p.natDegree) := by omega
    simp [h4]

lemma toPoly_ofPoly [DecidableEq R] (p : Polynomial R) : AzPolynomial.toPoly (AzPolynomial.ofPoly p) = p := by
  dsimp [AzPolynomial.ofPoly]
  split
  · next hp => simp [hp, AzPolynomial.toPoly, List.toPoly]
  · next hp =>
      dsimp [Polynomial.toDenseList, AzPolynomial.toPoly]
      ext i
      simp [hp]
      rw [coeff_toPoly, getCoeff_map_range_coeff]
      split
      · rfl
      · apply Eq.symm
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega

lemma natDegree_toPoly (l : List R) (h_nonempty : l ≠ []) (h_last : l.getLast? ≠ some 0) :
  (List.toPoly l).natDegree = l.length - 1 := by
  have h_len_pos : 0 < l.length := List.length_pos_iff_ne_nil.mpr h_nonempty
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    have hm2 : l.length ≤ m := by omega
    have h1 : (List.toPoly l).coeff m = l.getCoeff m := coeff_toPoly l m
    rw [h1]
    dsimp [List.getCoeff]
    have h2 : l[m]? = none := List.getElem?_eq_none hm2
    rw [h2]
    rfl
  · apply le_natDegree_of_ne_zero
    have h1 : (List.toPoly l).coeff (l.length - 1) = l.getCoeff (l.length - 1) := coeff_toPoly l (l.length - 1)
    rw [h1]
    have h2 : l[l.length - 1]? = l.getLast? := by
      apply Eq.symm
      apply List.getLast?_eq_getElem?
    dsimp [List.getCoeff]
    rw [h2]
    have h3 : l.getLast?.isSome := List.getLast?_isSome.mpr h_nonempty
    have h4 : ∃ c, l.getLast? = some c := Option.isSome_iff_exists.mp h3
    rcases h4 with ⟨c, hc_some⟩
    rw [hc_some]
    simp
    intro hc
    rw [hc] at hc_some
    rw [hc_some] at h_last
    exact h_last rfl

lemma map_getCoeff_range (l : List R) :
  (List.range l.length).map l.getCoeff = l := by
  apply List.ext_get
  · simp
  · intro i h1 h2
    simp
    dsimp [List.getCoeff]
    have h3 : l[i]? = some l[i] := List.getElem?_eq_getElem h2
    rw [h3]
    rfl

lemma array_eq_of_toList_eq {R : Type _} {a b : Array R} (h : a.toList = b.toList) : a = b := by
  cases a
  cases b
  simp at h
  congr

lemma eq_empty_of_toList_empty {R : Type _} [Semiring R] (a : Array R) (h : a.toList = []) : a = #[] := by
  apply array_eq_of_toList_eq
  exact h

lemma toList_empty_of_eq_empty {R : Type _} [Semiring R] (a : Array R) (h : a = #[]) : a.toList = [] := by
  rw [h]

lemma isEmpty_iff_toList_empty {R : Type _} [Semiring R] (a : Array R) : a.isEmpty ↔ a.toList = [] := by
  cases a
  simp

lemma ofPoly_toPoly [DecidableEq R] (p : Azurite.AzPolynomial R) : AzPolynomial.ofPoly (AzPolynomial.toPoly p) = p := by
  apply Azurite.AzPolynomial.ext
  dsimp [AzPolynomial.ofPoly, AzPolynomial.toPoly]
  by_cases h : p.coeffs.toList = []
  · have h_p_zero : p = 0 := by
      apply Azurite.AzPolynomial.ext
      exact eq_empty_of_toList_empty p.coeffs h
    rw [h_p_zero]
    rfl
  · have h_poly_ne_zero : List.toPoly p.coeffs.toList ≠ 0 := by
      intro hc
      have h4 : (List.toPoly p.coeffs.toList).coeff (p.coeffs.size - 1) = 0 := by rw [hc]; simp
      rw [coeff_toPoly] at h4
      have h1 : p.coeffs.toList[p.coeffs.size - 1]? = p.coeffs.toList.getLast? := by
        apply Eq.symm
        apply List.getLast?_eq_getElem?
      dsimp [List.getCoeff] at h4
      rw [h1] at h4
      -- Map back?
      have hw2 : p.coeffs.toList.getLast? = p.coeffs.back? := by simp
      rw [hw2] at h4
      have h2 : p.coeffs.back?.isSome := by
        have ht : p.coeffs.back? = p.coeffs.toList.getLast? := by simp
        rw [ht]
        exact List.getLast?_isSome.mpr h
      have h3 : ∃ c, p.coeffs.back? = some c := Option.isSome_iff_exists.mp h2
      rcases h3 with ⟨c, hc_some⟩
      rw [hc_some] at h4
      simp at h4
      have hlast : p.coeffs.back? ≠ some 0 := p.last_ne_zero
      rw [hc_some] at hlast
      rw [h4] at hlast
      exact hlast rfl
    simp [h_poly_ne_zero, Polynomial.toDenseList]
    have h1 : (List.toPoly p.coeffs.toList).natDegree = p.coeffs.size - 1 := by
      have hw : p.coeffs.size = p.coeffs.toList.length := (by simp)
      rw [hw]
      apply natDegree_toPoly
      · intro hc; exact h hc
      · have hh : p.coeffs.toList.getLast? = p.coeffs.back? := by simp
        rw [hh]
        exact p.last_ne_zero
    rw [h1]
    have h2 : p.coeffs.size - 1 + 1 = p.coeffs.size := by
      have hlen : p.coeffs.toList.length > 0 := List.length_pos_iff_ne_nil.mpr h
      have hw : p.coeffs.size = p.coeffs.toList.length := by simp
      omega
    rw [h2]
    have h3 : Polynomial.coeff (List.toPoly p.coeffs.toList) = p.coeffs.toList.getCoeff := by
      funext i
      exact coeff_toPoly p.coeffs.toList i
    rw [h3]
    have hw3 : (List.range p.coeffs.size).map p.coeffs.toList.getCoeff = p.coeffs.toList := by
      have hw : p.coeffs.size = p.coeffs.toList.length := (by simp)
      rw [hw]
      exact map_getCoeff_range p.coeffs.toList
    apply array_eq_of_toList_eq
    have ht : ((List.range p.coeffs.size).map p.coeffs.toList.getCoeff).toArray.toList = (List.range p.coeffs.size).map p.coeffs.toList.getCoeff := by simp
    rw [ht, hw3]

/-- The equivalence between `AzPolynomial R` and `Polynomial R`. -/
noncomputable def equivPolynomial [DecidableEq R] : Azurite.AzPolynomial R ≃ Polynomial R where
  toFun := AzPolynomial.toPoly
  invFun := AzPolynomial.ofPoly
  left_inv := ofPoly_toPoly
  right_inv := toPoly_ofPoly

@[simp] lemma toPoly_inj [DecidableEq R] {p q : Azurite.AzPolynomial R} : AzPolynomial.toPoly p = AzPolynomial.toPoly q ↔ p = q := by
  constructor
  · intro h
    have h2 : AzPolynomial.ofPoly (AzPolynomial.toPoly p) = AzPolynomial.ofPoly (AzPolynomial.toPoly q) := by rw [h]
    rw [ofPoly_toPoly p, ofPoly_toPoly q] at h2
    exact h2
  · intro h
    rw [h]

@[simp] lemma ofPoly_inj [DecidableEq R] {p q : Polynomial R} : AzPolynomial.ofPoly p = AzPolynomial.ofPoly q ↔ p = q := by
  constructor
  · intro h
    have h2 : AzPolynomial.toPoly (AzPolynomial.ofPoly p) = AzPolynomial.toPoly (AzPolynomial.ofPoly q) := by rw [h]
    rw [toPoly_ofPoly p, toPoly_ofPoly q] at h2
    exact h2
  · intro h
    rw [h]

@[simp] lemma AzPolynomial.natDegree_toPoly (p : Azurite.AzPolynomial R) : (toPoly p).natDegree = p.natDegree := by
  change (List.toPoly p.coeffs.toList).natDegree = p.coeffs.size - 1
  if h : p.coeffs.toList = [] then
    have hz : p.coeffs.size = 0 := by
      have hw : p.coeffs.size = p.coeffs.toList.length := by simp
      have hl : p.coeffs.toList.length = 0 := by rw [h]; rfl
      rw [hw, hl]
    rw [h, hz]
    rfl
  else
    have hw : p.coeffs.size = p.coeffs.toList.length := (by simp)
    rw [hw]
    have ht2 : p.coeffs.toList.getLast? ≠ some 0 := by
      have hh : p.coeffs.toList.getLast? = p.coeffs.back? := by simp
      rw [hh]
      exact p.last_ne_zero
    exact _root_.natDegree_toPoly p.coeffs.toList h ht2

@[simp] lemma AzPolynomial.degree_toPoly (p : Azurite.AzPolynomial R) : (toPoly p).degree = p.degree := by
  change (toPoly p).degree = if p.coeffs = #[] then ⊥ else ↑p.natDegree
  if h : p.coeffs.toList = [] then
    have h_toPoly_zero : toPoly p = 0 := by
      dsimp [toPoly]
      rw [h]
      rfl
    have he : p.coeffs = #[] := eq_empty_of_toList_empty p.coeffs h
    have h_empty : p.coeffs.isEmpty = true := by
      rw [he]
      rfl
    rw [h_toPoly_zero, Polynomial.degree_zero]
    rw [ite_eq_left he]
  else
    have he : ¬(p.coeffs = #[]) := by
      intro hc; have hz : p.coeffs.toList = [] := toList_empty_of_eq_empty p.coeffs hc
      exact h hz
    rw [ite_eq_right he]
    have hp_nat := AzPolynomial.natDegree_toPoly p
    have ht : toPoly p ≠ 0 := by
      intro hc
      have hc_deg : (toPoly p).natDegree = 0 := by rw [hc, Polynomial.natDegree_zero]
      rw [hp_nat] at hc_deg
      have h_nat : p.natDegree = p.coeffs.size - 1 := rfl
      have h_calc : p.coeffs.size - 1 = 0 := by rw [← h_nat, hc_deg]
      have h_list : ∃ a, p.coeffs.toList = [a] := by
        have hw : p.coeffs.toList.length = p.coeffs.size := by simp
        have hl : p.coeffs.toList.length - 1 = 0 := by rw [hw, h_calc]
        have h_len_pos : p.coeffs.toList.length > 0 := List.length_pos_iff_ne_nil.mpr h
        have hp : p.coeffs.toList.length = 1 := by omega
        exact List.length_eq_one_iff.mp hp
      rcases h_list with ⟨a, ha⟩
      have hc_zero : (toPoly p).coeff 0 = 0 := by rw [hc]; rfl
      have hc_eq : (toPoly p).coeff 0 = p.coeffs.toList.getCoeff 0 := coeff_toPoly p.coeffs.toList 0
      rw [hc_zero, ha] at hc_eq
      have ha_zero : a = 0 := hc_eq.symm
      have hlast : p.coeffs.back? = some 0 := by
        have hw : p.coeffs.back? = p.coeffs.toList.getLast? := by simp
        rw [hw]
        calc
          p.coeffs.toList.getLast? = [a].getLast? := by rw [ha]
          _ = [0].getLast? := by rw [ha_zero]
          _ = some 0 := rfl
      exact p.last_ne_zero hlast
    rw [Polynomial.degree_eq_natDegree ht]
    rw [hp_nat]

@[simp] lemma AzPolynomial.natDegree_ofPoly [DecidableEq R] (p : Polynomial R) : (ofPoly p).natDegree = p.natDegree := by
  have h := AzPolynomial.natDegree_toPoly (ofPoly p)
  rw [toPoly_ofPoly p] at h
  exact h.symm

@[simp] lemma AzPolynomial.degree_ofPoly [DecidableEq R] (p : Polynomial R) : (ofPoly p).degree = p.degree := by
  have h := AzPolynomial.degree_toPoly (ofPoly p)
  rw [toPoly_ofPoly p] at h
  exact h.symm

@[simp] lemma toPoly_zero [DecidableEq R] : AzPolynomial.toPoly (0 : Azurite.AzPolynomial R) = 0 := by
  have h := ofPoly_toPoly (0 : Azurite.AzPolynomial R)
  have hz : AzPolynomial.toPoly (0 : Azurite.AzPolynomial R) = 0 := rfl
  exact hz

@[simp] lemma ofPoly_zero [DecidableEq R] : AzPolynomial.ofPoly (0 : Polynomial R) = 0 := by
  dsimp [AzPolynomial.ofPoly]

@[simp] lemma ofPoly_one [DecidableEq R] : AzPolynomial.ofPoly (1 : Polynomial R) = 1 := by
  have h := toPoly_ofPoly (1 : Polynomial R)
  -- The simple proof handles the 1=1 native evaluation
  change AzPolynomial.ofPoly (1 : Polynomial R) = Azurite.AzPolynomial.one
  dsimp [AzPolynomial.ofPoly]
  split
  · next h =>
    -- 1 = 0 in Polynomial R -> 1 = 0 in R
    have h1 : (1 : R) = 0 := by
      have hc : (1 : Polynomial R).coeff 0 = (C (1 : R)).coeff 0 := by rw [Polynomial.C_1.symm]
      rw [h] at hc
      simp at hc
      exact hc.symm
    dsimp [Azurite.AzPolynomial.one]
    rw [dite_eq_left h1]
    rfl
  · next h =>
    -- 1 ≠ 0 in Polynomial R -> 1 ≠ 0 in R
    have h1 : (1 : R) ≠ 0 := by
      intro hc
      have hc2 : (1 : Polynomial R) = C (1 : R) := Polynomial.C_1.symm
      rw [hc] at hc2
      rw [Polynomial.C_0] at hc2
      exact h hc2
    dsimp [Azurite.AzPolynomial.one]
    rw [dite_eq_right h1]
    apply Azurite.AzPolynomial.ext
    dsimp [Polynomial.toDenseList]
    split
    · next h_poly => contradiction
    · next h_poly =>
      have h_deg : (1 : Polynomial R).natDegree = 0 := Polynomial.natDegree_one
      rw [h_deg]
      have h_list : (List.range (0 + 1)).map (1 : Polynomial R).coeff = [(1 : R)] := by simp
      rw [h_list]

@[simp] lemma toPoly_one [DecidableEq R] : AzPolynomial.toPoly (1 : Azurite.AzPolynomial R) = 1 := by
  have h := ofPoly_toPoly (1 : Azurite.AzPolynomial R)
  have h2 : AzPolynomial.toPoly (AzPolynomial.ofPoly (1 : Polynomial R)) = 1 := toPoly_ofPoly 1
  rw [ofPoly_one] at h2
  exact h2

@[ext] lemma ext [DecidableEq R] {p q : Azurite.AzPolynomial R} (h : ∀ i, p.coeff i = q.coeff i) : p = q := by
  have hp : AzPolynomial.toPoly p = AzPolynomial.toPoly q := by
    ext i
    rw [coeff_toPoly_eq, coeff_toPoly_eq, h i]
  have ht : AzPolynomial.ofPoly (AzPolynomial.toPoly p) = AzPolynomial.ofPoly (AzPolynomial.toPoly q) := by rw [hp]
  rw [ofPoly_toPoly, ofPoly_toPoly] at ht
  exact ht

@[simp] lemma leadingCoeff_toPoly (p : Azurite.AzPolynomial R) : (AzPolynomial.toPoly p).leadingCoeff = p.leadingCoeff := by
  change (AzPolynomial.toPoly p).coeff (AzPolynomial.toPoly p).natDegree = p.coeff p.natDegree
  rw [AzPolynomial.natDegree_toPoly, coeff_toPoly_eq]

@[simp] lemma leadingCoeff_ofPoly [DecidableEq R] (p : Polynomial R) : (AzPolynomial.ofPoly p).leadingCoeff = p.leadingCoeff := by
  have h := leadingCoeff_toPoly (AzPolynomial.ofPoly p)
  rw [toPoly_ofPoly] at h
  exact h.symm

@[simp] lemma nextCoeff_toPoly (p : Azurite.AzPolynomial R) : (AzPolynomial.toPoly p).nextCoeff = p.nextCoeff := by
  dsimp [Azurite.AzPolynomial.nextCoeff, Polynomial.nextCoeff]
  rw [AzPolynomial.natDegree_toPoly]
  split_ifs with h
  · rfl
  · rw [coeff_toPoly_eq]

@[simp] lemma nextCoeff_ofPoly [DecidableEq R] (p : Polynomial R) : (AzPolynomial.ofPoly p).nextCoeff = p.nextCoeff := by
  have h := nextCoeff_toPoly (AzPolynomial.ofPoly p)
  rw [toPoly_ofPoly] at h
  exact h.symm

@[simp] lemma Monic_toPoly (p : Azurite.AzPolynomial R) : (AzPolynomial.toPoly p).Monic ↔ p.Monic := by
  dsimp [Polynomial.Monic, Azurite.AzPolynomial.Monic]
  rw [leadingCoeff_toPoly]

@[simp] lemma Monic_ofPoly [DecidableEq R] (p : Polynomial R) : (AzPolynomial.ofPoly p).Monic ↔ p.Monic := by
  have h := Monic_toPoly (AzPolynomial.ofPoly p)
  rw [toPoly_ofPoly] at h
  exact h.symm
