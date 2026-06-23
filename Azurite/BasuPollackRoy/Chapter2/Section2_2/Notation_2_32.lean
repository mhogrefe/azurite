import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Sign.Basic

/-! # BPR Section 2.2 — Notation 2.32: Sign variations

> The number of sign variations `Var(a)` in a sequence `a = a₀, …, aₚ` of
> elements of `R ∖ {0}` is defined by induction on `p`:
>
> * `Var(a₀) = 0`,
> * `Var(a₀, …, aₚ) = Var(a₁, …, aₚ) + 1` if `a₀ · a₁ < 0`,
> * `Var(a₀, …, aₚ) = Var(a₁, …, aₚ)`     if `a₀ · a₁ > 0`.
>
> This definition extends to any finite sequence `a` of elements of `R` by
> considering the finite sequence `b` obtained by dropping the zeros from `a`
> and setting `Var(a) := Var(b)`, with `Var(∅) = 0`.

We formalise `a` as a `List R`. The helper `varNonzero` implements the
pairwise recursion over a list whose zeros have already been dropped, and
`Var` is the extension to arbitrary lists, obtained by filtering out zeros.

The file additionally records:

* basic simp lemmas (`varNonzero_nil`, `varNonzero_singleton`,
  `varNonzero_cons_cons`, `Var_nil`, `Var_eq_varNonzero_filter`,
  `Var_of_forall_ne_zero`);
* monotonicity-of-sign lemmas (`varNonzero_eq_zero_of_forall_nonneg/nonpos`,
  `Var_eq_zero_of_forall_nonneg/nonpos`, `Var_zero_cons`);
* sign-pattern invariance (`varNonzero_congr_sign`, `Var_congr_sign`);
* the BPR worked example
  `Var(1, −1, 2, 0, 0, 3, 4, −5, −2, 0, 3) = 4` (BPR p.43).
-/

namespace Azurite.BPR

variable {R : Type*}

/-- Count of sign variations in a list, realised by iterating over adjacent
    pairs. Intended to be applied to a list whose zeros have been removed;
    `Var` handles zero-dropping and calls this. -/
def varNonzero [Mul R] [Zero R] [LT R] [DecidableLT R] : List R → ℕ
  | []            => 0
  | [_]           => 0
  | a :: b :: rest =>
      (if a * b < 0 then 1 else 0) + varNonzero (b :: rest)

/-- **BPR Notation 2.32.** The number of sign variations `Var(a)` in a
    finite sequence `a` of elements of an ordered ring `R`. Zeros are
    dropped from `a` before counting adjacent pairs of opposite signs. -/
def Var [Mul R] [Zero R] [DecidableEq R] [LT R] [DecidableLT R]
    (a : List R) : ℕ :=
  varNonzero (a.filter (· ≠ 0))

section

variable [Mul R] [Zero R] [LT R] [DecidableLT R]

@[simp] lemma varNonzero_nil : varNonzero ([] : List R) = 0 := rfl

@[simp] lemma varNonzero_singleton (a : R) : varNonzero [a] = 0 := rfl

lemma varNonzero_cons_cons (a b : R) (rest : List R) :
    varNonzero (a :: b :: rest) =
      (if a * b < 0 then 1 else 0) + varNonzero (b :: rest) := rfl

/-- Appending one element to a list adds the single sign variation between the
    previous last element and the new one (none if the list was empty). -/
private lemma varNonzero_append_singleton (l : List R) (x : R) :
    varNonzero (l ++ [x]) =
      varNonzero l + (match l.getLast? with
        | none => 0
        | some y => if y * x < 0 then 1 else 0) := by
  induction l with
  | nil => simp [varNonzero]
  | cons a t ih =>
    cases t with
    | nil => simp [varNonzero]
    | cons b s =>
      rw [show (a :: b :: s) ++ [x] = a :: b :: (s ++ [x]) from rfl,
        varNonzero_cons_cons, ← List.cons_append, ih, varNonzero_cons_cons,
        List.getLast?_cons_cons, ← Nat.add_assoc]

end

section

variable [CommMagma R] [Zero R] [LT R] [DecidableLT R]

/-- `varNonzero` is invariant under reversal: the number of adjacent sign
    variations does not depend on the orientation of the list. Needs
    commutativity of multiplication, since the adjacent-pair test `a * b < 0`
    must be symmetric. -/
lemma varNonzero_reverse (l : List R) : varNonzero l.reverse = varNonzero l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.reverse_cons, varNonzero_append_singleton, List.getLast?_reverse, ih]
    cases t with
    | nil => rfl
    | cons b s =>
      rw [varNonzero_cons_cons, List.head?_cons]
      dsimp only
      rw [mul_comm b a, Nat.add_comm]

end

section

variable [Mul R] [Zero R] [DecidableEq R] [LT R] [DecidableLT R]

@[simp] lemma Var_nil : Var ([] : List R) = 0 := rfl

lemma Var_eq_varNonzero_filter (a : List R) :
    Var a = varNonzero (a.filter (· ≠ 0)) := rfl

/-- If every element of `a` is nonzero, then filtering zeros is a no-op and
    `Var a` agrees with the pairwise count `varNonzero a`. -/
lemma Var_of_forall_ne_zero {a : List R} (h : ∀ x ∈ a, x ≠ 0) :
    Var a = varNonzero a := by
  unfold Var
  congr 1
  exact List.filter_eq_self.mpr (fun x hx => by simpa using h x hx)

end

section

variable [CommMagma R] [Zero R] [DecidableEq R] [LT R] [DecidableLT R]

/-- **`Var` is invariant under reversal.** A coefficient sequence and its
    reverse have the same number of sign variations, so `Var(a₀, …, aₙ)` (the
    ascending form used by `varPoly`) equals `Var(aₙ, …, a₀)` (BPR's descending
    display). -/
lemma Var_reverse (a : List R) : Var a.reverse = Var a := by
  rw [Var, Var, List.filter_reverse, varNonzero_reverse]

end

section

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `varNonzero` vanishes on a list whose entries are all nonneg: every
    adjacent product is nonneg, so no sign variation ever triggers. -/
lemma varNonzero_eq_zero_of_forall_nonneg :
    ∀ {l : List R}, (∀ x ∈ l, 0 ≤ x) → varNonzero l = 0
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
      rw [varNonzero_cons_cons]
      have ha := h a (List.mem_cons_self)
      have hb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
      have hab : ¬ a * b < 0 := not_lt.mpr (mul_nonneg ha hb)
      rw [if_neg hab, zero_add]
      exact varNonzero_eq_zero_of_forall_nonneg
        (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- `varNonzero` vanishes on a list whose entries are all nonpos. -/
lemma varNonzero_eq_zero_of_forall_nonpos :
    ∀ {l : List R}, (∀ x ∈ l, x ≤ 0) → varNonzero l = 0
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
      rw [varNonzero_cons_cons]
      have ha := h a (List.mem_cons_self)
      have hb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
      have hab : ¬ a * b < 0 := not_lt.mpr (mul_nonneg_of_nonpos_of_nonpos ha hb)
      rw [if_neg hab, zero_add]
      exact varNonzero_eq_zero_of_forall_nonpos
        (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- `Var` vanishes on a list whose entries are all nonneg. -/
lemma Var_eq_zero_of_forall_nonneg {l : List R} (h : ∀ x ∈ l, 0 ≤ x) :
    Var l = 0 := by
  unfold Var
  exact varNonzero_eq_zero_of_forall_nonneg
    (fun x hx => h x (List.mem_of_mem_filter hx))

/-- `Var` vanishes on a list whose entries are all nonpos. -/
lemma Var_eq_zero_of_forall_nonpos {l : List R} (h : ∀ x ∈ l, x ≤ 0) :
    Var l = 0 := by
  unfold Var
  exact varNonzero_eq_zero_of_forall_nonpos
    (fun x hx => h x (List.mem_of_mem_filter hx))

omit [IsStrictOrderedRing R] in
/-- Prepending a zero to a list does not change its variation count. -/
@[simp] lemma Var_zero_cons (l : List R) : Var ((0 : R) :: l) = Var l := by
  unfold Var
  rw [List.filter_cons]
  simp

end

section

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- If two lists of nonzero elements have pointwise matching signs, their
    `varNonzero` counts agree. The `a * b < 0` comparison depends only on
    `sign a * sign b` (via `sign_mul`), so sign-map equality is enough. -/
lemma varNonzero_congr_sign : ∀ {l₁ l₂ : List R},
    l₁.map SignType.sign = l₂.map SignType.sign →
    varNonzero l₁ = varNonzero l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons => simp at h
  | cons a rest₁ ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp at h
    | cons a' rest₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨ha, hrest⟩ := h
      cases rest₁ with
      | nil =>
        cases rest₂ with
        | nil => rfl
        | cons => simp at hrest
      | cons b rest₁' =>
        cases rest₂ with
        | nil => simp at hrest
        | cons b' rest₂' =>
          simp only [List.map_cons, List.cons.injEq] at hrest
          obtain ⟨hb, hrest'⟩ := hrest
          rw [varNonzero_cons_cons, varNonzero_cons_cons]
          have h_iff : (a * b < 0) ↔ (a' * b' < 0) := by
            have hs : SignType.sign (a * b) = SignType.sign (a' * b') := by
              rw [sign_mul, sign_mul, ha, hb]
            refine ⟨fun hab => ?_, fun hab => ?_⟩
            · rw [sign_eq_neg_one_iff.mpr hab] at hs
              exact sign_eq_neg_one_iff.mp hs.symm
            · rw [sign_eq_neg_one_iff.mpr hab] at hs
              exact sign_eq_neg_one_iff.mp hs
          have hif_eq : (if a * b < 0 then (1 : ℕ) else 0) =
              (if a' * b' < 0 then 1 else 0) := by
            by_cases hab : a * b < 0
            · rw [if_pos hab, if_pos (h_iff.mp hab)]
            · rw [if_neg hab, if_neg (fun hc => hab (h_iff.mpr hc))]
          rw [hif_eq]
          congr 1
          apply ih
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨hb, hrest'⟩

/-- `Var` is invariant under operations that preserve the sign pattern of
    the list. -/
lemma Var_congr_sign {l₁ l₂ : List R}
    (h : l₁.map SignType.sign = l₂.map SignType.sign) :
    Var l₁ = Var l₂ := by
  unfold Var
  apply varNonzero_congr_sign
  -- Goal: (l₁.filter (· ≠ 0)).map sign = (l₂.filter (· ≠ 0)).map sign
  -- Strategy: show this equals (l_i.map sign).filter (· ≠ 0), then use h.
  have key : ∀ (l : List R),
      (l.filter (· ≠ 0)).map SignType.sign =
      (l.map SignType.sign).filter (· ≠ 0) := by
    intro l
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro x _
    simp only [Function.comp_apply, decide_not, sign_eq_zero_iff]
  rw [key, key, h]

end

/-! ### Worked example (BPR p. 43)

`Var(1, −1, 2, 0, 0, 3, 4, −5, −2, 0, 3) = 4`: after dropping zeros the
subsequence is `1, −1, 2, 3, 4, −5, −2, 3`, whose sign-change pairs are
`(1, −1)`, `(−1, 2)`, `(4, −5)`, `(−2, 3)`. -/

example : Var ([1, -1, 2, 0, 0, 3, 4, -5, -2, 0, 3] : List Int) = 4 := by decide

end Azurite.BPR
