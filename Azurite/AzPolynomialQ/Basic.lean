import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Defs
import Azurite.AzPolynomial.Basic

/-!
# AzPolynomialQ: Rational Polynomials with Shared Denominator

This module defines `AzPolynomialQ`, a canonical dense representation of univariate
polynomials over `ℚ`. A `AzPolynomialQ` stores:
- `numerators : Array ℤ` — integer numerators of each coefficient
- `denom : ℕ` — a shared positive denominator

The polynomial `p(x) = ∑ (numerators[i] / denom) * xⁱ`.

**Invariants** (ensuring canonical form):
1. `denom > 0`
2. The last numerator is nonzero (unless the zero polynomial, which has empty numerators)
3. `Nat.gcd (gcd of all |numerators[i]|) denom = 1` — fully reduced

The canonical form makes equality decidable by direct structural comparison.
-/

namespace Azurite

/-! ## Helper functions and lemmas on integer GCD via foldl -/

section IntGCDHelpers

/-- Compute the GCD of all absolute values in a list of integers, as a natural number.
    Returns 0 for the empty list (consistent with `Nat.gcd 0 n = n`). -/
abbrev listIntGcd (l : List ℤ) : ℕ :=
  l.foldl (fun acc n => Nat.gcd acc n.natAbs) 0

/-- The foldl gcd only weakens: its result divides the accumulator. -/
private lemma foldl_gcd_dvd_acc (l : List ℤ) (acc : ℕ) :
    l.foldl (fun acc m => Nat.gcd acc m.natAbs) acc ∣ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons]
    exact dvd_trans (ih _) (Nat.gcd_dvd_left acc a.natAbs)

/-- Helper: the foldl-gcd result with any accumulator divides any element in the list. -/
private lemma foldl_gcd_dvd_mem (l : List ℤ) (n : ℤ) (hn : n ∈ l) :
    ∀ acc : ℕ, l.foldl (fun acc m => Nat.gcd acc m.natAbs) acc ∣ n.natAbs := by
  induction l generalizing n with
  | nil => simp_all
  | cons a as ih =>
    intro acc
    simp only [List.foldl_cons, List.mem_cons] at *
    cases hn with
    | inl h => subst h; exact dvd_trans (foldl_gcd_dvd_acc as _) (Nat.gcd_dvd_right acc n.natAbs)
    | inr h => exact ih n h (Nat.gcd acc a.natAbs)

/-- The listIntGcd divides the absolute value of every element in the list. -/
lemma listIntGcd_dvd_of_mem (l : List ℤ) (n : ℤ) (hn : n ∈ l) :
    listIntGcd l ∣ n.natAbs := foldl_gcd_dvd_mem l n hn 0

/-- Dividing every element by `g` divides the listIntGcd by `g`,
    provided `g` divides every element. -/
private lemma listIntGcd_map_ediv (l : List ℤ) (g : ℕ) (hg : 0 < g)
    (hdvd : ∀ n ∈ l, (g : ℤ) ∣ n) :
    listIntGcd (l.map (· / (g : ℤ))) = listIntGcd l / g := by
  simp only [listIntGcd]
  suffices h : ∀ acc : ℕ, g ∣ acc →
      (l.map (· / (g : ℤ))).foldl (fun acc n => Nat.gcd acc n.natAbs) (acc / g) =
      l.foldl (fun acc n => Nat.gcd acc n.natAbs) acc / g by
    simpa using h 0 (Nat.dvd_zero g)
  intro acc hacc
  induction l generalizing acc with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.foldl_cons]
    have ha : (g : ℤ) ∣ a := hdvd a (List.mem_cons.mpr (Or.inl rfl))
    have has : ∀ n ∈ as, (g : ℤ) ∣ n :=
      fun n hn => hdvd n (List.mem_cons.mpr (Or.inr hn))
    have hgne : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
    obtain ⟨k, hk⟩ := ha
    rw [show a / (g : ℤ) = k from by rw [hk]; exact Int.mul_ediv_cancel_left k hgne]
    have hna : a.natAbs = g * k.natAbs := by rw [hk, Int.natAbs_mul]; simp
    have hna_dvd : g ∣ a.natAbs := hna ▸ dvd_mul_right g k.natAbs
    rw [show k.natAbs = a.natAbs / g from by rw [hna, Nat.mul_div_cancel_left _ hg]]
    conv_lhs => rw [Nat.gcd_div hacc hna_dvd]
    exact ih has _ (Nat.dvd_gcd hacc hna_dvd)

end IntGCDHelpers

/-! ## AzPolynomialQ structure -/

/-- A canonical dense representation of a univariate polynomial over `ℚ`.
    Stores integer `numerators` with a shared positive `denom`. The representation
    is canonical: the GCD of all numerators and the denominator is 1. -/
structure AzPolynomialQ where
  numerators   : Array ℤ
  denom        : ℕ
  denom_pos    : 0 < denom
  last_ne_zero : numerators.back? ≠ some 0
  coprime      : Nat.gcd (listIntGcd numerators.toList) denom = 1
  deriving Repr

namespace AzPolynomialQ

/-! ## Basic instances and zero -/

/-- Extensionality: two `AzPolynomialQ` are equal iff their numerators and
    denominator are equal. -/
@[ext]
lemma ext {p q : AzPolynomialQ}
    (hnum : p.numerators = q.numerators) (hdenom : p.denom = q.denom) : p = q := by
  cases p; cases q
  simp only at hnum hdenom
  subst hnum hdenom
  congr

/-- Decidable equality — justified by the canonical GCD invariant. -/
instance : DecidableEq AzPolynomialQ := fun p q =>
  if h1 : p.numerators = q.numerators then
    if h2 : p.denom = q.denom then
      isTrue (AzPolynomialQ.ext h1 h2)
    else
      isFalse (fun h => h2 (congrArg AzPolynomialQ.denom h))
  else
    isFalse (fun h => h1 (congrArg AzPolynomialQ.numerators h))

/-- The zero polynomial: empty numerators, denominator 1. -/
def zero : AzPolynomialQ :=
  ⟨#[], 1, by omega, by simp, by simp [listIntGcd]⟩

instance : Zero AzPolynomialQ := ⟨zero⟩
instance : Inhabited AzPolynomialQ := ⟨zero⟩

/-- The constant polynomial 1: numerator `#[1]`, denominator 1. -/
def one : AzPolynomialQ :=
  ⟨#[1], 1, by omega, by simp, by simp [listIntGcd]⟩

instance : One AzPolynomialQ := ⟨one⟩

@[simp] lemma zero_numerators : (0 : AzPolynomialQ).numerators = #[] := rfl
@[simp] lemma zero_denom : (0 : AzPolynomialQ).denom = 1 := rfl

/-! ## Accessors -/

/-- The `i`-th coefficient as a rational number. -/
def coeff (p : AzPolynomialQ) (i : ℕ) : ℚ :=
  (p.numerators[i]?.getD 0 : ℤ) / (p.denom : ℚ)

/-- The natural degree: size - 1, with 0 for the zero polynomial. -/
def natDegree (p : AzPolynomialQ) : ℕ :=
  p.numerators.size - 1

/-- The degree, returning `⊥` for the zero polynomial. -/
def degree (p : AzPolynomialQ) : WithBot ℕ :=
  if p.numerators = #[] then ⊥ else ↑p.natDegree

/-- The leading coefficient. -/
def leadingCoeff (p : AzPolynomialQ) : ℚ :=
  p.coeff p.natDegree

/-- The second-highest coefficient, or 0 for constants. -/
def nextCoeff (p : AzPolynomialQ) : ℚ :=
  if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)

/-- A polynomial is `Monic` if its leading coefficient is 1. -/
def Monic (p : AzPolynomialQ) : Prop :=
  p.leadingCoeff = 1

instance {p : AzPolynomialQ} : Decidable p.Monic := by
  unfold Monic leadingCoeff coeff
  infer_instance

@[simp]
theorem Monic.leadingCoeff_eq_one {p : AzPolynomialQ} (hp : p.Monic) : p.leadingCoeff = 1 :=
  hp

theorem Monic.coeff_natDegree {p : AzPolynomialQ} (hp : p.Monic) : p.coeff p.natDegree = 1 :=
  hp

@[simp] lemma coeff_zero (i : ℕ) : (0 : AzPolynomialQ).coeff i = 0 := by
  simp [coeff]

@[simp] lemma one_numerators : (1 : AzPolynomialQ).numerators = #[1] := rfl
@[simp] lemma one_denom : (1 : AzPolynomialQ).denom = 1 := rfl

/-! ## Normalization -/

/-- Normalize an integer array and a positive natural number denominator into
    a canonical `AzPolynomialQ` by:
    1. Dropping trailing zeros from `nums`
    2. Computing `g = gcd(all |nums[i]|, d)`
    3. Dividing numerators and denominator by `g` -/
def normalize (nums : Array ℤ) (d : ℕ) (hd : 0 < d) : AzPolynomialQ :=
  let nums' := nums.popWhile (· = 0)
  let G := listIntGcd nums'.toList
  let g := Nat.gcd G d
  let hg_pos : 0 < g := Nat.gcd_pos_of_pos_right G hd
  let hg_dvd_d : g ∣ d := Nat.gcd_dvd_right G d
  let hg_dvd_G : g ∣ G := Nat.gcd_dvd_left G d
  let newNums := nums'.map (· / (g : ℤ))
  let newDenom := d / g
  ⟨newNums, newDenom,
    -- denom_pos
    Nat.div_pos (Nat.le_of_dvd hd hg_dvd_d) hg_pos,
    -- last_ne_zero
    by
      -- nums' = nums.popWhile (· = 0) has last_ne_zero by construction
      have h_nums'_last : nums'.back? ≠ some 0 := by
        intro hbp
        rw [← Array.getLast?_toList] at hbp
        have hpw := List.popWhile_toArray (p := (· = 0)) nums.toList
        have hkey : nums'.toList =
            (nums.toList.reverse.dropWhile (· = 0)).reverse := by
          exact congrArg Array.toList ((by simp : nums.toList.toArray = nums) ▸ hpw)
        rw [hkey, List.getLast?_reverse] at hbp
        generalize hd' : nums.toList.reverse.dropWhile (· = 0) = dl at hbp
        rcases dl with _ | ⟨x, xs⟩
        · simp at hbp
        · simp only [List.head?_cons, Option.some.injEq] at hbp
          have hne : (x :: xs) ≠ [] := List.cons_ne_nil x xs
          have hhead := @List.head_dropWhile_not ℤ (· = 0) nums.toList.reverse
            (hd' ▸ hne)
          simp only [hd', List.head_cons] at hhead
          simp [hbp] at hhead
      -- newNums.back? = nums'.back?.map (· / g)
      intro h
      simp only [newNums, Array.back?_map] at h
      rcases hp : nums'.back? with _ | c
      · simp [hp] at h
      · simp [hp] at h
        -- h : c / g = 0, but c ≠ 0 and g ∣ c (since g ∣ G ∣ c.natAbs)
        apply h_nums'_last
        rw [hp]
        congr 1
        by_contra hc
        have hcG : G ∣ c.natAbs := by
          apply listIntGcd_dvd_of_mem
          simp [Array.mem_of_getElem? hp]
        have hgc : (g : ℤ) ∣ c := by
          rw [← Int.natAbs_dvd_natAbs]
          simpa using dvd_trans hg_dvd_G hcG
        obtain ⟨k, hk⟩ := hgc
        have hkne : k ≠ 0 := by
          intro hk0; rw [hk0, mul_zero] at hk; exact hc hk
        have hgne : (g : ℤ) ≠ 0 := by exact_mod_cast hg_pos.ne'
        rw [hk, Int.mul_ediv_cancel_left _ hgne] at h
        exact hkne h,
    -- coprime : Nat.gcd (listIntGcd newNums.toList) newDenom = 1
    by
      simp only [newNums, newDenom, Array.toList_map]
      have hdvd : ∀ n ∈ nums'.toList, (g : ℤ) ∣ n := by
        intro n hn
        have hGn : G ∣ n.natAbs := listIntGcd_dvd_of_mem _ n hn
        rw [← Int.natAbs_dvd_natAbs]
        simpa using dvd_trans hg_dvd_G hGn
      rw [listIntGcd_map_ediv _ g hg_pos hdvd]
      exact Nat.coprime_div_gcd_div_gcd hg_pos
  ⟩


/-! ## normalize_coeff -/

/-- The rational coefficient of `normalize nums d hd` at position `i` equals
    `(nums.popWhile (\u00b7 = 0))[i]?.getD 0 / d`.
    That is: normalization preserves rational values (GCD division cancels out). -/
lemma normalize_coeff (nums : Array ℤ) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    (normalize nums d hd).coeff i =
    ((nums.popWhile (fun x => decide (x = 0)))[i]?.getD 0 : ℤ) / d := by
  simp only [AzPolynomialQ.normalize, AzPolynomialQ.coeff, Array.getElem?_map]
  set nums' := nums.popWhile (fun x => decide (x = 0))
  set G := listIntGcd nums'.toList
  set g := Nat.gcd G d
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right G hd
  have hg_dvd_d : g ∣ d := Nat.gcd_dvd_right G d
  have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast hg_pos.ne'
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg_pos.ne'
  rcases h : nums'[i]? with _ | c
  · simp
  · -- simplify (Option.map f (some c)).getD 0 = f c
    simp only [Option.map_some, Option.getD_some]
    -- Need: (c / g : ℤ) / (d / g : ℕ) = (c : ℚ) / d
    have hg_c : (g : ℤ) ∣ c := by
      rw [← Int.natAbs_dvd_natAbs]
      simpa using dvd_trans (Nat.gcd_dvd_left G d)
        (listIntGcd_dvd_of_mem _ c (by rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? h))
    obtain ⟨k, hk⟩ := hg_c
    obtain ⟨m, hm⟩ := hg_dvd_d
    rw [hk, hm, Int.mul_ediv_cancel_left _ hgZ, Nat.mul_div_cancel_left _ hg_pos]
    push_cast
    rw [mul_div_mul_left _ _ hgQ]

end AzPolynomialQ
end Azurite
