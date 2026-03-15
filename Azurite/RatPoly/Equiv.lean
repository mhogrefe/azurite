import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Defs
import Azurite.RatPoly.Basic
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

end Azurite
