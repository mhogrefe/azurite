import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Defs
import Azurite.DensePolyQ.Basic
import Azurite.DensePoly.Basic
import Azurite.DensePoly.Equiv.Basic

/-!
# DensePolyQ ↔ DensePoly ℚ Conversions

This module defines the conversions between `DensePolyQ` (integer numerators with
a shared positive denominator, in canonical form) and `DensePoly ℚ` (array of rationals).

## Main definitions

- `DensePolyQ.toIntPoly` — the underlying `DensePoly ℤ` of numerators
- `DensePolyQ.toDensePoly` — forward conversion: `n_i ↦ n_i / denom`
- `DensePolyQ.ofDensePoly` — inverse: scale coefficients by LCM of denominators, then normalize

## Main results

- `coeff_toDensePoly` — `toDensePoly p` has the same rational coefficients as `p`
- `toDensePoly_zero` — `toDensePoly 0 = 0`
- `coeff_ofDensePoly` — `ofDensePoly p` has the same rational coefficients as `p`
- `toDensePoly_ofDensePoly` — roundtrip `DensePoly ℚ → DensePolyQ → DensePoly ℚ = id`
-/

namespace Azurite

open DensePoly

/-! ## LCM helpers -/

/-- LCM of a list of naturals, using `foldr` with identity element 1. -/
private def listLcm' (l : List ℕ) : ℕ := l.foldr Nat.lcm 1

/-- Every element of `l` divides `listLcm' l`. -/
private lemma listLcm'_dvd_mem : ∀ (l : List ℕ) (n : ℕ), n ∈ l → n ∣ listLcm' l
  | [], n, h => (List.mem_nil_iff n |>.mp h).elim
  | a :: as, n, h => by
    simp only [listLcm', List.foldr_cons, List.mem_cons] at *
    cases h with
    | inl h => subst h; exact Nat.dvd_lcm_left n _
    | inr h => exact dvd_trans (listLcm'_dvd_mem as n h) (Nat.dvd_lcm_right a _)

/-- LCM of the denominators of a list of rationals is positive. -/
private lemma listLcm'_denList_pos : ∀ l : List ℚ, 0 < listLcm' (l.map (·.den))
  | [] => by simp [listLcm']
  | a :: as => by
    simp only [listLcm', List.map_cons, List.foldr_cons]
    apply Nat.pos_of_ne_zero
    intro h
    rw [Nat.lcm_eq_zero_iff] at h
    exact h.elim (fun h => a.pos.ne' h) (fun h => (listLcm'_denList_pos as).ne' h)

/-! ## scaleRat helper -/

/-- Scale a rational `q` by `d` to obtain an integer `q.num * (d / q.den)`. -/
private def scaleRat (q : ℚ) (d : ℕ) : ℤ := q.num * (d / q.den : ℕ)

/-- `scaleRat q d / d = q` when `q.den ∣ d` and `d > 0`. -/
private lemma scaleRat_div (q : ℚ) (d : ℕ) (hd : q.den ∣ d) (hd_pos : 0 < d) :
    (scaleRat q d : ℚ) / d = q := by
  simp only [scaleRat]
  have hqd_ne : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.pos.ne'
  obtain ⟨k, hk⟩ := hd; subst hk
  rw [Nat.mul_div_cancel_left _ q.pos]; push_cast
  have hk_ne : (k : ℚ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hkp
    · simp at hd_pos
    · exact_mod_cast hkp.ne'
  rw [mul_div_mul_right _ _ hk_ne, div_eq_iff hqd_ne]
  exact (div_eq_iff hqd_ne).mp q.num_div_den

/-! ## popWhile helper -/

/-- If the last element of `l` is nonzero, then dropping trailing zeros is a no-op. -/
private lemma list_dropWhile_reverse_of_getLast_ne (l : List ℤ) (h : l.getLast? ≠ some 0) :
    (l.reverse.dropWhile (fun x => decide (x = 0))).reverse = l := by
  rcases hl : l.getLast? with _ | v
  · simp [List.getLast?_eq_none_iff.mp hl]
  · rw [hl] at h
    have hv : (v : ℤ) ≠ 0 := fun hv => h (hv ▸ rfl)
    obtain ⟨tl, htl⟩ := List.head?_eq_some_iff.mp (show l.reverse.head? = some v by
      rw [List.head?_reverse]; exact hl)
    rw [htl]
    simp [show decide (v = 0) = false from by simp [hv]]
    have := congrArg List.reverse htl
    simp [List.reverse_cons] at this
    exact this.symm

/-! ## toDensePoly -/

/-- The `DensePoly ℤ` of numerators underlying a `DensePolyQ`. -/
def DensePolyQ.toIntPoly (p : DensePolyQ) : DensePoly ℤ :=
  ⟨p.numerators, p.last_ne_zero⟩

/-- Convert a `DensePolyQ` to a `DensePoly ℚ`: map each numerator `n_i ↦ n_i / denom`.
    Uses `mapZeroInjective` so the result is automatically normalized. -/
def DensePolyQ.toDensePoly (p : DensePolyQ) : DensePoly ℚ :=
  mapZeroInjective
    (fun n : ℤ => (n : ℚ) / p.denom)
    (fun n => ⟨fun h => by
        have hdne : (p.denom : ℚ) ≠ 0 := by exact_mod_cast p.denom_pos.ne'
        simpa [hdne, div_eq_zero_iff] using h,
      fun h => by simp [h]⟩)
    p.toIntPoly

@[simp]
lemma DensePolyQ.coeff_toDensePoly (p : DensePolyQ) (i : ℕ) :
    p.toDensePoly.coeff i = p.coeff i := by
  simp only [toDensePoly, toIntPoly, mapZeroInjective, DensePoly.coeff, coeff, Array.getElem?_map]
  cases p.numerators[i]? with
  | none => simp
  | some n => simp

@[simp]
lemma DensePolyQ.toDensePoly_zero : (0 : DensePolyQ).toDensePoly = 0 := by
  show mapZeroInjective (fun n : ℤ => (n : ℚ) / (1 : ℕ)) _
    (⟨#[], by simp⟩ : DensePoly ℤ) = (⟨#[], by simp⟩ : DensePoly ℚ)
  simp [mapZeroInjective]

/-! ## ofDensePoly -/

/-- Convert a `DensePoly ℚ` to a canonical `DensePolyQ`:
    1. Let `d = lcm` of all coefficient denominators
    2. Scale each `q_i` to the integer `scaleRat q_i d = q_i.num * (d / q_i.den)`
    3. Call `normalize` to drop trailing zeros and reduce by GCD -/
def DensePolyQ.ofDensePoly (p : DensePoly ℚ) : DensePolyQ :=
  let l := p.coeffs.toList
  let d := listLcm' (l.map (·.den))
  DensePolyQ.normalize (l.map (fun q => scaleRat q d)).toArray d (listLcm'_denList_pos l)

/-! ## Roundtrip: toDensePoly ∘ ofDensePoly = id -/

/-- The rational coefficients of `ofDensePoly p` agree with those of `p`. -/
@[simp]
lemma DensePolyQ.coeff_ofDensePoly (p : DensePoly ℚ) (i : ℕ) :
    (ofDensePoly p).coeff i = p.coeff i := by
  simp only [ofDensePoly]
  rw [DensePolyQ.normalize_coeff]
  set l := p.coeffs.toList
  set d := listLcm' (l.map (·.den))
  set scaleNums := (l.map (fun q => scaleRat q d)).toArray
  -- Step 1: popWhile (· = 0) is a no-op on scaleNums
  -- because p's last_ne_zero invariant propagates through scaleRat
  have hpw : scaleNums.popWhile (fun x => decide (x = 0)) = scaleNums := by
    conv_rhs => rw [show scaleNums = scaleNums.toList.toArray by simp]
    rw [List.popWhile_toArray]; congr 1
    apply list_dropWhile_reverse_of_getLast_ne
    simp only [List.getLast?_map]
    rcases hl : l.getLast? with _ | q
    · simp
    · simp only [Option.map_some]
      intro h; simp only [Option.some.injEq] at h
      have hq_ne : q ≠ 0 := fun hq => p.last_ne_zero
        (show p.coeffs.back? = some 0 by
          rw [← Array.getLast?_toList]; exact hl ▸ hq ▸ rfl)
      have hqden : q.den ∣ d :=
        listLcm'_dvd_mem _ _ (List.mem_map.mpr ⟨q, List.mem_of_getLast? hl, rfl⟩)
      have hdiv := scaleRat_div q d hqden (listLcm'_denList_pos l)
      rw [h] at hdiv; simp at hdiv
      exact hq_ne hdiv.symm
  rw [hpw]
  -- Step 2: for each index i, the scaled coefficient divided by d recovers p.coeff i
  simp only [scaleNums, DensePoly.coeff, ← Array.getElem?_toList, List.getElem?_map]
  rw [show l[i]? = p.coeffs[i]? from by simp [l, Array.getElem?_toList]]
  rcases hi : p.coeffs[i]? with _ | q
  · simp
  · simp only [Option.map_some, Option.getD_some]
    have hqden : q.den ∣ d :=
      listLcm'_dvd_mem _ _ (List.mem_map.mpr ⟨q, Array.mem_toList_iff.mpr
        (Array.mem_of_getElem? hi), rfl⟩)
    exact scaleRat_div q d hqden (listLcm'_denList_pos l)

/-- The roundtrip `DensePoly ℚ → DensePolyQ → DensePoly ℚ` is the identity. -/
lemma DensePolyQ.toDensePoly_ofDensePoly (p : DensePoly ℚ) :
    (ofDensePoly p).toDensePoly = p := by
  apply_fun DensePoly.toPoly using fun p q h => toPoly_inj.mp h
  ext i
  simp [coeff_toPoly_eq, coeff_toDensePoly, coeff_ofDensePoly]

/-! ## Coefficient extensionality -/

private lemma array_getElem?_of_lt {α} (a : Array α) (i : ℕ) (h : i < a.size) :
    a[i]? = some a[i] := by
  simp [h]

private lemma array_getElem?_of_ge {α} (a : Array α) (i : ℕ) (h : ¬(i < a.size)) :
    a[i]? = none := by
  simp [h]

private lemma array_mem_toList_index {α} {a : Array α} {n : α} (hn : n ∈ a.toList) :
    ∃ i, ∃ (hi : i < a.size), a[i] = n := by
  have := List.getElem_of_mem hn
  obtain ⟨i, hi, heq⟩ := this
  exact ⟨i, by rwa [← Array.length_toList], by rw [← Array.getElem_toList]; exact heq⟩

/-- If `B` divides every element's `natAbs` in a list, it divides the `listIntGcd`. -/
private lemma dvd_listIntGcd_of_dvd_all (l : List ℤ) (B : ℕ)
    (hall : ∀ n ∈ l, B ∣ n.natAbs) :
    B ∣ listIntGcd l := by
  suffices h : ∀ acc, B ∣ acc → B ∣ l.foldl (fun acc n => Nat.gcd acc n.natAbs) acc from
    h 0 (Nat.dvd_zero B)
  intro acc hacc
  induction l generalizing acc with
  | nil => exact hacc
  | cons a as ih =>
    simp only [List.foldl_cons]
    apply ih (fun n hn => hall n (List.Mem.tail a hn))
    exact Nat.dvd_gcd hacc (hall a (List.Mem.head as))

/-- `q.denom ∣ p.denom` when both have equal-sized numerator arrays and the
    cross-multiplication `p.nums[i] * q.denom = q.nums[i] * p.denom` holds at every index. -/
private lemma denom_dvd_of_cross (p q : DensePolyQ)
    (hsize : p.numerators.size = q.numerators.size)
    (cross : ∀ (i : ℕ), (p.numerators[i]?.getD 0 : ℤ) * q.denom =
        (q.numerators[i]?.getD 0 : ℤ) * p.denom) :
    q.denom ∣ p.denom := by
  set g := Nat.gcd q.denom p.denom
  set B := q.denom / g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ q.denom_pos
  have hg_dvd_q : g ∣ q.denom := Nat.gcd_dvd_left _ _
  have hg_dvd_p : g ∣ p.denom := Nat.gcd_dvd_right _ _
  have hcop_B : Nat.Coprime B (p.denom / g) := Nat.coprime_div_gcd_div_gcd hg_pos
  have hB_dvd : ∀ i (hi : i < q.numerators.size), B ∣ (q.numerators[i]'hi).natAbs := by
    intro i hi
    have hcr := cross i
    have hpi : i < p.numerators.size := hsize ▸ hi
    simp only [array_getElem?_of_lt q.numerators i hi,
               array_getElem?_of_lt p.numerators i hpi,
               Option.getD_some] at hcr
    have hqd : q.denom ∣ (q.numerators[i]'hi).natAbs * p.denom := by
      have hdvd : (q.denom : ℤ) ∣ (q.numerators[i]'hi) * p.denom :=
        ⟨p.numerators[i]'hpi, by linarith⟩
      have := Int.natAbs_dvd_natAbs.mpr hdvd
      rwa [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_natCast] at this
    rw [show q.denom = B * g from (Nat.div_mul_cancel hg_dvd_q).symm,
        show p.denom = (p.denom / g) * g from (Nat.div_mul_cancel hg_dvd_p).symm] at hqd
    rw [mul_comm (p.denom / g) g, ← mul_assoc, mul_comm B g, mul_comm ((q.numerators[i]'hi).natAbs) g, mul_assoc] at hqd
    exact hcop_B.dvd_of_dvd_mul_right (Nat.dvd_of_mul_dvd_mul_left hg_pos hqd)
  have hB_dvd_G : B ∣ listIntGcd q.numerators.toList := by
    apply dvd_listIntGcd_of_dvd_all
    intro n hn
    have ⟨i, hi, heq⟩ := array_mem_toList_index hn
    exact heq ▸ hB_dvd i hi
  have : B ∣ 1 := q.coprime ▸ Nat.dvd_gcd hB_dvd_G (Nat.div_dvd_of_dvd hg_dvd_q)
  rw [show q.denom = B * g from (Nat.div_mul_cancel hg_dvd_q).symm,
      Nat.eq_one_of_dvd_one this, one_mul]
  exact hg_dvd_p

/-- Two canonical `DensePolyQ` with the same rational coefficient at every position are equal.
    Uniqueness of reduced-fraction representation with a shared denominator. -/
lemma DensePolyQ.coeff_ext (p q : DensePolyQ)
    (h : ∀ i, p.coeff i = q.coeff i) : p = q := by
  have cross : ∀ (i : ℕ), (p.numerators[i]?.getD 0 : ℤ) * q.denom =
      (q.numerators[i]?.getD 0 : ℤ) * p.denom := by
    intro i; have hi := h i; simp only [DensePolyQ.coeff] at hi
    have hpd : (p.denom : ℚ) ≠ 0 := by exact_mod_cast p.denom_pos.ne'
    have hqd : (q.denom : ℚ) ≠ 0 := by exact_mod_cast q.denom_pos.ne'
    exact_mod_cast (div_eq_div_iff hpd hqd).mp hi
  have hsize : p.numerators.size = q.numerators.size := by
    by_contra hne
    wlog hgt : p.numerators.size < q.numerators.size with H
    · push_neg at hgt
      exact H q p (fun i => (h i).symm) (fun i => (cross i).symm) (Ne.symm hne) (by omega)
    set j := q.numerators.size - 1
    have hj_lt : j < q.numerators.size := by omega
    have hj_ge : ¬(j < p.numerators.size) := by omega
    have := cross j
    have hq_some : q.numerators[j]? = some q.numerators[j] := array_getElem?_of_lt _ _ hj_lt
    have hp_none : p.numerators[j]? = none := by
      exact array_getElem?_of_ge _ _ hj_ge
    simp only [hq_some, hp_none, Option.getD_some, Option.getD_none] at this
    have hpd_ne : (p.denom : ℤ) ≠ 0 := by exact_mod_cast p.denom_pos.ne'
    have hqn_zero : q.numerators[j] = (0 : ℤ) := by
      rcases mul_eq_zero.mp (by linarith : q.numerators[j] * (p.denom : ℤ) = 0) with h | h
      · exact h
      · exact absurd h hpd_ne
    exact q.last_ne_zero (by rw [Array.back?, array_getElem?_of_lt _ _ hj_lt, hqn_zero])
  have hdenom : p.denom = q.denom :=
    Nat.dvd_antisymm (denom_dvd_of_cross q p hsize.symm (fun i => (cross i).symm))
                      (denom_dvd_of_cross p q hsize cross)
  have hnums : p.numerators = q.numerators := by
    apply Array.ext
    · exact hsize
    · intro i hi1 hi2
      have := cross i
      simp only [array_getElem?_of_lt p.numerators i hi1,
                  array_getElem?_of_lt q.numerators i hi2,
                  Option.getD_some] at this
      rw [hdenom] at this
      exact mul_right_cancel₀ (by exact_mod_cast q.denom_pos.ne' : (q.denom : ℤ) ≠ 0) this
  exact DensePolyQ.ext hnums hdenom

/-- The roundtrip `DensePolyQ → DensePoly ℚ → DensePolyQ` is the identity. -/
lemma DensePolyQ.ofDensePoly_toDensePoly (p : DensePolyQ) :
    ofDensePoly p.toDensePoly = p := by
  apply DensePolyQ.coeff_ext
  intro i
  rw [coeff_ofDensePoly, coeff_toDensePoly]

/-! ## DensePolyQ ↔ Polynomial ℚ equivalences -/

/-- Convert a `DensePolyQ` to a `Polynomial ℚ` by composing through `DensePoly ℚ`. -/
noncomputable def DensePolyQ.toPoly (p : DensePolyQ) : Polynomial ℚ :=
  DensePoly.toPoly p.toDensePoly

@[simp] lemma DensePolyQ.coeff_toPoly_eq (p : DensePolyQ) (i : ℕ) :
    p.toPoly.coeff i = p.coeff i := by
  simp only [DensePolyQ.toPoly, _root_.coeff_toPoly_eq, coeff_toDensePoly]

@[simp] lemma DensePolyQ.natDegree_toPoly (p : DensePolyQ) :
    p.toPoly.natDegree = p.natDegree := by
  simp [toPoly, DensePoly.natDegree_toPoly, toDensePoly, toIntPoly,
    mapZeroInjective, DensePolyQ.natDegree, DensePoly.natDegree]

@[simp] lemma DensePolyQ.degree_toPoly (p : DensePolyQ) :
    p.toPoly.degree = p.degree := by
  simp only [DensePolyQ.degree]
  split
  · case isTrue h =>
    have : p.toPoly = 0 := by
      ext i; simp [coeff_toPoly_eq, DensePolyQ.coeff, h]
    simp [this]
  · case isFalse h =>
    have hne : p.toPoly ≠ 0 := by
      intro h0
      apply h
      by_contra hne
      have hsz : 0 < p.numerators.size :=
        Nat.pos_of_ne_zero (fun he => hne (Array.eq_empty_of_size_eq_zero he))
      have := congr_arg (·.coeff (p.numerators.size - 1)) h0
      simp [coeff_toPoly_eq, DensePolyQ.coeff,
        show p.numerators.size - 1 < p.numerators.size from by omega] at this
      rcases this with h1 | h1
      · exact p.last_ne_zero (by
          simp [Array.back?, show p.numerators.size - 1 < p.numerators.size from by omega, h1])
      · exact absurd (show (p.denom : ℤ) = 0 from by exact_mod_cast h1) (by exact_mod_cast p.denom_pos.ne')
    rw [Polynomial.degree_eq_natDegree hne, natDegree_toPoly]

@[simp] lemma DensePolyQ.leadingCoeff_toPoly (p : DensePolyQ) :
    p.toPoly.leadingCoeff = p.leadingCoeff := by
  simp [Polynomial.leadingCoeff, DensePolyQ.leadingCoeff,
    coeff_toPoly_eq, natDegree_toPoly]

@[simp] lemma DensePolyQ.nextCoeff_toPoly (p : DensePolyQ) :
    p.toPoly.nextCoeff = p.nextCoeff := by
  simp only [Polynomial.nextCoeff, DensePolyQ.nextCoeff, natDegree_toPoly]
  split
  · rfl
  · exact coeff_toPoly_eq p _

@[simp] lemma DensePolyQ.Monic_toPoly (p : DensePolyQ) :
    p.toPoly.Monic ↔ p.Monic := by
  simp [Polynomial.Monic, DensePolyQ.Monic, leadingCoeff_toPoly]

@[simp] lemma DensePolyQ.toPoly_zero :
    (0 : DensePolyQ).toPoly = 0 := by
  ext i; simp [coeff_toPoly_eq, DensePolyQ.coeff]

@[simp] lemma DensePolyQ.toPoly_one :
    (1 : DensePolyQ).toPoly = 1 := by
  ext i; simp [coeff_toPoly_eq, DensePolyQ.coeff]
  cases i with
  | zero => simp
  | succ n => simp [Polynomial.coeff_one]

end Azurite
