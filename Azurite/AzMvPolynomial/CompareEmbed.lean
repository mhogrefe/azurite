/-
  Embedding and translation-invariance lemmas for `lexCompareAux`,
  `revlexCompareAux`, and `totalDeg`, plus `MonicMonomial`-specific
  strict-monotonicity and multiplication-preservation corollaries.

  The vector-level content here is variable-type independent and is the
  canonical home for these lemmas; the legacy `Azurite.AzMvPolynomial.CompareEmbed`
  now re-imports this file.
-/
import Azurite.AzMvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace Azurite
open MonomialOrder

variable {n₁ n₂ : ℕ}

/-- Embed an exponent vector from `n₁` variables into `n₂` variables via `g`.
    Position `j` in the result is `∑ i, if g(i) = j then v[i] else 0`. -/
noncomputable def embedVec (g : Fin n₁ → Fin n₂) (v : Vector ℕ n₁) : Vector ℕ n₂ :=
  Vector.ofFn (fun j => Finset.univ.sum (fun i : Fin n₁ =>
    if g i = j then v[i] else 0))

private theorem lex_skip {n : ℕ} (a b : Vector ℕ n) (start stop : ℕ)
    (_ : start ≤ stop) (_ : stop ≤ n)
    (heq : ∀ j : ℕ, start ≤ j → j < stop → (hj : j < n) → a[j] = b[j]) :
    lexCompareAux a b start = lexCompareAux a b stop := by
  by_cases h : start = stop; · rw [h]
  · rw [lexCompareAux, dif_pos (show start < n by omega)]
    rw [show compare (a[start]'(by omega)) (b[start]'(by omega)) = .eq from
      Nat.compare_eq_eq.mpr (heq start (le_refl _) (by omega) (by omega))]
    exact lex_skip a b (start + 1) stop (by omega) (by omega)
      (fun j hj1 hj2 hj3 => heq j (by omega) hj2 hj3)
  termination_by stop - start

private theorem revlex_skip {n : ℕ} (a b : Vector ℕ n) (start stop : ℕ)
    (_ : start ≤ stop) (_ : stop ≤ n)
    (heq : ∀ j : ℕ, start ≤ j → j < stop → (hj : j < n) →
      a[n - 1 - j]'(by omega) = b[n - 1 - j]'(by omega)) :
    revlexCompareAux a b start = revlexCompareAux a b stop := by
  by_cases h : start = stop; · rw [h]
  · rw [revlexCompareAux, dif_pos (show start < n by omega)]; dsimp only
    rw [show compare (a[n - 1 - start]'(by omega)) (b[n - 1 - start]'(by omega)) = .eq from
      Nat.compare_eq_eq.mpr (heq start (le_refl _) (by omega) (by omega))]
    exact revlex_skip a b (start + 1) stop (by omega) (by omega)
      (fun j hj1 hj2 hj3 => heq j (by omega) hj2 hj3)
  termination_by stop - start

private theorem embedVec_at (g : Fin n₁ → Fin n₂) (hg : Function.Injective g)
    (v : Vector ℕ n₁) (k : ℕ) (hk : k < n₁) :
    (embedVec g v)[(g ⟨k, hk⟩).val] = v[k] := by
  simp only [embedVec, Vector.getElem_ofFn, Fin.getElem_fin]
  rw [Finset.sum_eq_single_of_mem ⟨k, hk⟩ (Finset.mem_univ _)]
  · simp
  · intro j _ hji
    split; exact absurd (hg (Fin.ext (Fin.val_eq_of_eq ‹_›))) hji; rfl

theorem lex_embed (g : Fin n₁ → Fin n₂) (hg : StrictMono g) (a b : Vector ℕ n₁)
    (k : ℕ) (_ : k ≤ n₁) :
    lexCompareAux (embedVec g a) (embedVec g b)
      (if h : k < n₁ then (g ⟨k, h⟩).val else n₂) =
    lexCompareAux a b k := by
  by_cases hkn : k < n₁
  · rw [dif_pos hkn, lexCompareAux, dif_pos (g ⟨k, hkn⟩).isLt,
        embedVec_at g hg.injective a k hkn, embedVec_at g hg.injective b k hkn]
    conv_rhs => rw [lexCompareAux, dif_pos hkn]
    rcases compare (a[k]'hkn) (b[k]'hkn) with _ | _ | _
    · rfl
    · set next := if h : k + 1 < n₁ then (g ⟨k + 1, h⟩).val else n₂ with hnext
      rw [lex_skip (embedVec g a) (embedVec g b) ((g ⟨k, hkn⟩).val + 1) next
        (by simp only [next]; split
            · exact Nat.succ_le_of_lt (hg (Fin.mk_lt_mk.mpr (by omega)))
            · exact Nat.succ_le_of_lt (g ⟨k, hkn⟩).isLt)
        (by simp only [next]; split <;> [exact (g ⟨_, _⟩).isLt.le; exact le_refl _])
        (fun j hjge hjlt hjn₂ => by
            simp only [embedVec, Vector.getElem_ofFn, Fin.getElem_fin]
            congr 1; ext i
            have : (g i).val ≠ j := by
              by_cases hik : i.val ≤ k
              · have := Fin.val_le_of_le (hg.monotone (show i ≤ ⟨k, hkn⟩ from hik)); omega
              · simp only [next] at hjlt; split at hjlt
                · have hle : (⟨k+1, ‹_›⟩ : Fin n₁) ≤ i := Fin.mk_le_mk.mpr (by omega)
                  have := Fin.val_le_of_le (hg.monotone hle); omega
                · omega
            split; exact absurd (Fin.val_eq_of_eq ‹_›) this; rfl)]
      exact lex_embed g hg a b (k + 1) (by omega)
    · rfl
  · rw [dif_neg hkn, lexCompareAux, dif_neg (show ¬(n₂ < n₂) by omega),
        lexCompareAux, dif_neg hkn]
termination_by n₁ - k

theorem revlex_embed (g : Fin n₁ → Fin n₂) (hg : StrictMono g) (a b : Vector ℕ n₁)
    (k : ℕ) (_ : k ≤ n₁) :
    revlexCompareAux (embedVec g a) (embedVec g b)
      (if h : k < n₁ then n₂ - 1 - (g ⟨n₁ - 1 - k, by omega⟩).val else n₂) =
    revlexCompareAux a b k := by
  by_cases hkn : k < n₁
  · rw [dif_pos hkn]
    set rk := n₂ - 1 - (g ⟨n₁ - 1 - k, by omega⟩).val
    rw [revlexCompareAux, dif_pos (show rk < n₂ by simp [rk]; omega)]; dsimp only
    have hsimp : n₂ - 1 - rk = (g ⟨n₁ - 1 - k, by omega⟩).val := by simp [rk]; omega
    conv_lhs =>
      rw [show (embedVec g a)[n₂ - 1 - rk] = a[n₁ - 1 - k] from by
        simp_rw [hsimp]; exact embedVec_at g hg.injective a _ (by omega)]
      rw [show (embedVec g b)[n₂ - 1 - rk] = b[n₁ - 1 - k] from by
        simp_rw [hsimp]; exact embedVec_at g hg.injective b _ (by omega)]
    conv_rhs => rw [revlexCompareAux, dif_pos hkn]; dsimp only
    rcases compare (a[n₁ - 1 - k]'(by omega)) (b[n₁ - 1 - k]'(by omega)) with _ | _ | _
    · rfl
    · show revlexCompareAux (embedVec g a) (embedVec g b) (rk + 1) = revlexCompareAux a b (k + 1)
      set next := if h : k + 1 < n₁ then n₂ - 1 - (g ⟨n₁ - 1 - (k + 1), by omega⟩).val else n₂
      rw [revlex_skip (embedVec g a) (embedVec g b) (rk + 1) next
        (by simp only [rk, next]; split
            · rename_i hk1
              have h1 : (g ⟨n₁-1-(k+1), by omega⟩).val < (g ⟨n₁-1-k, by omega⟩).val :=
                hg (show n₁ - 1 - (k+1) < n₁ - 1 - k from by omega)
              omega
            · omega)
        (by simp only [next]; split <;> omega)
        (fun j hjge hjlt hjn₂ => by
            simp only [embedVec, Vector.getElem_ofFn, Fin.getElem_fin]
            congr 1; ext i
            have hni : (g i).val ≠ n₂ - 1 - j := by
              by_cases hle : n₁ - 1 - k ≤ i.val
              · have hgi := Fin.val_le_of_le (hg.monotone (show ⟨n₁-1-k, by omega⟩ ≤ i from hle))
                simp only [rk] at hjge; intro heq; omega
              · simp only [next] at hjlt; split at hjlt
                · have hgi := Fin.val_le_of_le (hg.monotone
                    (show i ≤ ⟨n₁-1-(k+1), by omega⟩ from Fin.mk_le_mk.mpr (by omega)))
                  intro heq; omega
                · omega
            split; exact absurd (Fin.val_eq_of_eq ‹_›) hni; rfl)]
      exact revlex_embed g hg a b (k + 1) (by omega)
    · rfl
  · rw [dif_neg hkn, revlexCompareAux, dif_neg (show ¬(n₂ < n₂) by omega),
        revlexCompareAux, dif_neg hkn]
termination_by n₁ - k

theorem totalDeg_eq_finsum {n : ℕ} (v : Vector ℕ n) :
    totalDeg v = Finset.univ.sum (fun i : Fin n => v[i]) := by
  simp only [totalDeg, ← Array.foldl_toList, ← List.sum_eq_foldl]
  rw [show v.toArray.toList = v.toList from rfl,
      show v.toList = List.ofFn (fun i : Fin n => v[i]) from by
        apply List.ext_getElem
        · simp [Vector.length_toList]
        · intro i hi1 hi2; simp [List.getElem_ofFn, Vector.getElem_toList]]
  exact List.sum_ofFn

theorem totalDeg_embedVec (g : Fin n₁ → Fin n₂) (_ : Function.Injective g)
    (v : Vector ℕ n₁) :
    totalDeg (embedVec g v) = totalDeg v := by
  rw [totalDeg_eq_finsum, totalDeg_eq_finsum]
  simp only [embedVec, Vector.getElem_ofFn, Fin.getElem_fin]
  rw [Finset.sum_comm]
  congr 1; ext i
  rw [Finset.sum_eq_single_of_mem (g i) (Finset.mem_univ _)]
  · simp
  · intro j _ hji; simp [Ne.symm (Fin.ne_of_val_ne (fun h => hji (Fin.ext h)))]

/-- `lexCompare` is preserved by strictly monotone embedding. -/
theorem lexCompare_embedVec (g : Fin n₁ → Fin n₂) (hg : StrictMono g)
    (a b : Vector ℕ n₁) :
    lexCompare (embedVec g a) (embedVec g b) = lexCompare a b := by
  unfold lexCompare
  have h0 := lex_embed g hg a b 0 (Nat.zero_le _)
  by_cases hn : 0 < n₁
  · simp only [hn, dite_true] at h0
    rw [lex_skip (embedVec g a) (embedVec g b) 0 (g ⟨0, hn⟩).val
      (Nat.zero_le _) (g ⟨0, hn⟩).isLt.le
      (fun j _ hjlt hjn₂ => by
        simp only [embedVec, Vector.getElem_ofFn, Fin.getElem_fin]
        congr 1; ext i
        have : (g i).val ≠ j := by
          have := Fin.val_le_of_le (hg.monotone
            (show (⟨0, hn⟩ : Fin n₁) ≤ i from Fin.mk_le_mk.mpr (Nat.zero_le _)))
          omega
        split; exact absurd (Fin.val_eq_of_eq ‹_›) this; rfl)]
    exact h0
  · simp only [show ¬(0 < n₁) from hn, dite_false] at h0
    -- n₁ = 0: both sides are .eq since all positions have embedVec = 0
    rw [lex_skip (embedVec g a) (embedVec g b) 0 n₂
      (Nat.zero_le _) (le_refl _)
      (fun j _ _ hjn₂ => by
        simp only [embedVec, Vector.getElem_ofFn, Fin.getElem_fin]
        congr 1; ext i; exact absurd i.isLt (by omega))]
    rw [lexCompareAux, dif_neg (by omega), lexCompareAux, dif_neg (by omega)]

/-- `revlexCompare` is preserved by strictly monotone embedding. -/
theorem revlexCompare_embedVec (g : Fin n₁ → Fin n₂) (hg : StrictMono g)
    (a b : Vector ℕ n₁) :
    revlexCompare (embedVec g a) (embedVec g b) = revlexCompare a b := by
  unfold revlexCompare
  have h0 := revlex_embed g hg a b 0 (Nat.zero_le _)
  by_cases hn : 0 < n₁
  · simp only [hn, dite_true] at h0
    rw [revlex_skip (embedVec g a) (embedVec g b) 0
      (n₂ - 1 - (g ⟨n₁ - 1, by omega⟩).val) (Nat.zero_le _) (by omega)
      (fun j _ hjlt hjn₂ => by
        simp only [embedVec, Vector.getElem_ofFn, Fin.getElem_fin]
        congr 1; ext i
        have : (g i).val ≠ n₂ - 1 - j := by
          have hgi := Fin.val_le_of_le (hg.monotone
            (show (⟨0, hn⟩ : Fin n₁) ≤ i from Fin.mk_le_mk.mpr (Nat.zero_le _)))
          -- g(i) ≤ g(n₁-1) and n₂-1-j > g(n₁-1) (from j < n₂-1-g(n₁-1))
          have hgn1 := Fin.val_le_of_le (hg.monotone
            (show i ≤ ⟨n₁-1, by omega⟩ from Fin.mk_le_mk.mpr (by omega)))
          intro heq; omega
        split; exact absurd (Fin.val_eq_of_eq ‹_›) this; rfl)]
    exact h0
  · simp only [show ¬(0 < n₁) from hn, dite_false] at h0
    rw [revlex_skip (embedVec g a) (embedVec g b) 0 n₂
      (Nat.zero_le _) (le_refl _)
      (fun j _ _ hjn₂ => by
        simp only [embedVec, Vector.getElem_ofFn, Fin.getElem_fin]
        congr 1; ext i; exact absurd i.isLt (by omega))]
    rw [revlexCompareAux, dif_neg (by omega), revlexCompareAux, dif_neg (by omega)]

/-- `compareExponents` is preserved by strictly monotone embedding. -/
theorem compareExponents_embedVec (g : Fin n₁ → Fin n₂) (hg : StrictMono g)
    (ord : MonomialOrder) (a b : Vector ℕ n₁) :
    ord.compareExponents (embedVec g a) (embedVec g b) = ord.compareExponents a b := by
  cases ord with
  | Lex => exact lexCompare_embedVec g hg a b
  | Deglex =>
    simp only [compareExponents, totalDeg_embedVec g hg.injective]
    rcases compare (totalDeg a) (totalDeg b) with _ | _ | _
    · rfl
    · exact lexCompare_embedVec g hg a b
    · rfl
  | Degrevlex =>
    simp only [compareExponents, totalDeg_embedVec g hg.injective]
    rcases compare (totalDeg a) (totalDeg b) with _ | _ | _
    · rfl
    · exact revlexCompare_embedVec g hg a b
    · rfl

/-! ### Monomial ordering is compatible with multiplication

All three orderings (lex, deglex, degrevlex) are translation-invariant:
adding a fixed exponent vector to both arguments does not change the
comparison result.  This implies that left-multiplication by a fixed
monic monomial preserves strict ordering. -/

section TranslationInvariance

variable {n : ℕ}

private theorem Nat.compare_add_left (c a b : ℕ) :
    compare (c + a) (c + b) = compare a b := by
  cases hab : compare a b
  · rw [compare_lt_iff_lt] at hab ⊢; omega
  · rw [compare_eq_iff_eq] at hab ⊢; omega
  · rw [compare_gt_iff_gt] at hab ⊢; omega

private theorem lexCompareAux_add_left (c a b : Vector ℕ n) (i : ℕ) :
    lexCompareAux (Vector.ofFn (fun j => c[j] + a[j]))
                  (Vector.ofFn (fun j => c[j] + b[j])) i
    = lexCompareAux a b i := by
  unfold lexCompareAux; split
  · next h =>
    simp only [Vector.getElem_ofFn, Nat.compare_add_left]
    match compare (a[i]'h) (b[i]'h) with
    | .lt => rfl
    | .eq => exact lexCompareAux_add_left c a b (i + 1)
    | .gt => rfl
  · rfl
termination_by n - i

private theorem revlexCompareAux_add_left (c a b : Vector ℕ n) (i : ℕ) :
    revlexCompareAux (Vector.ofFn (fun j => c[j] + a[j]))
                     (Vector.ofFn (fun j => c[j] + b[j])) i
    = revlexCompareAux a b i := by
  unfold revlexCompareAux; split
  · next h =>
    simp only [Vector.getElem_ofFn, Nat.compare_add_left]
    match compare (a[n - 1 - i]'(by omega)) (b[n - 1 - i]'(by omega)) with
    | .lt => rfl
    | .eq => exact revlexCompareAux_add_left c a b (i + 1)
    | .gt => rfl
  · rfl
termination_by n - i

private theorem totalDeg_add (a b : Vector ℕ n) :
    totalDeg (Vector.ofFn (fun j => a[j] + b[j])) = totalDeg a + totalDeg b := by
  simp only [totalDeg_eq_finsum, Vector.getElem_ofFn, Fin.getElem_fin]
  rw [← Finset.sum_add_distrib]

/-- `compareExponents` is invariant under pointwise addition of a fixed vector.
    This is the fundamental property that makes monomial orderings
    compatible with multiplication. -/
theorem MonomialOrder.compareExponents_add_left (ord : MonomialOrder) (c a b : Vector ℕ n) :
    compareExponents ord (Vector.ofFn (fun j => c[j] + a[j]))
                         (Vector.ofFn (fun j => c[j] + b[j]))
    = compareExponents ord a b := by
  unfold compareExponents; cases ord
  · exact lexCompareAux_add_left c a b 0
  · rw [totalDeg_add, totalDeg_add]; simp only [Nat.compare_add_left]
    cases compare (totalDeg a) (totalDeg b) <;> simp
    exact lexCompareAux_add_left c a b 0
  · rw [totalDeg_add, totalDeg_add]; simp only [Nat.compare_add_left]
    cases compare (totalDeg a) (totalDeg b) <;> simp
    exact revlexCompareAux_add_left c a b 0

end TranslationInvariance

/-! ### `MonicMonomial` strict-monotonicity and multiplication lemmas -/

variable {ord : MonomialOrder}

/-- The exponents of a renamed `MonicMonomial` match `embedVec g`. -/
theorem MonicMonomial.rename_exponents_eq
    (m : MonicMonomial n₁ ord) (f : Fin n₁ → Fin n₂) (ord₂ : MonomialOrder) :
    (m.rename f ord₂).exponents = embedVec f m.exponents := rfl

/-- If `f : Fin n₁ → Fin n₂` is strictly monotone, renaming preserves the
    monomial comparison. -/
theorem MonicMonomial.rename_compare
    (m₁ m₂ : MonicMonomial n₁ ord) (f : Fin n₁ → Fin n₂)
    (hg : StrictMono f) :
    compare (m₁.rename f ord) (m₂.rename f ord) = compare m₁ m₂ := by
  show ord.compareExponents (m₁.rename f ord).exponents (m₂.rename f ord).exponents =
    ord.compareExponents m₁.exponents m₂.exponents
  simp only [rename_exponents_eq]
  exact compareExponents_embedVec _ hg ord _ _

/-- `MonicMonomial.rename f` is strictly monotone if `f` is. -/
theorem MonicMonomial.rename_strictMono (f : Fin n₁ → Fin n₂) (hg : StrictMono f) :
    StrictMono (fun m : MonicMonomial n₁ ord => m.rename f ord) := by
  intro m₁ m₂ hlt
  show compare (m₁.rename f ord) (m₂.rename f ord) = .lt
  rw [rename_compare m₁ m₂ f hg]
  exact hlt

variable {n : ℕ}

/-- Left multiplication by a fixed monic monomial preserves strict ordering. -/
theorem MonicMonomial.mul_lt_mul_left (c a b : MonicMonomial n ord)
    (h : a < b) : c * a < c * b := by
  show compareExponents ord (c * a).exponents (c * b).exponents = .lt
  simp only [MonicMonomial.mul_exponents]
  rw [show (Vector.ofFn fun i => c.exponents[i] + a.exponents[i])
      = (Vector.ofFn fun i => c.exponents[↑i] + a.exponents[↑i]) from rfl,
      show (Vector.ofFn fun i => c.exponents[i] + b.exponents[i])
      = (Vector.ofFn fun i => c.exponents[↑i] + b.exponents[↑i]) from rfl]
  rw [MonomialOrder.compareExponents_add_left]; exact h

/-- Left multiplication by a fixed monic monomial preserves strict ordering (gt). -/
theorem MonicMonomial.mul_gt_mul_left (c a b : MonicMonomial n ord)
    (h : a > b) : c * a > c * b :=
  mul_lt_mul_left c b a h

end Azurite
