import Azurite.BasuPollackRoy.Chapter8.Section8_1.Definition_8_4

/-!
# BPR §8.1: Bitsize of sums and products of integers

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

Two unnumbered BPR facts about how `Int.size` propagates through
arithmetic:

* **Sum:** the bitsize of a sum of `n` integers each of bitsize `≤ τ`
  is at most `τ + bit(n)`.
* **Product:** the bitsize of a product of `n ≥ 1` integers each of
  bitsize `≤ τ` is at most `n · τ`.
-/

namespace Azurite.BPR

/-!
### Bitsize of a sum of integers

Each `|aᵢ| < 2^τ`, so the triangle inequality gives
`|∑ aᵢ| ≤ ∑ |aᵢ| ≤ n · 2^τ < 2^{bit(n)} · 2^τ = 2^{τ + bit(n)}`,
whence `bitsize(∑ aᵢ) ≤ τ + bit(n)`.
-/

/-- Triangle inequality for integer list sums: `|∑ aᵢ| ≤ ∑ |aᵢ|`. -/
theorem Int.natAbs_list_sum_le (l : List ℤ) :
    l.sum.natAbs ≤ (l.map Int.natAbs).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact le_trans (Int.natAbs_add_le a as.sum) (Nat.add_le_add_left ih _)

/-- If every element of a list is `≤ b`, then the sum is `≤ length · b`. -/
theorem List.sum_le_length_mul {l : List ℕ} {b : ℕ}
    (h : ∀ x ∈ l, x ≤ b) : l.sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.sum_cons, List.length_cons, Nat.add_comm as.length 1, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-- Adding `n` integers each of bitsize `≤ τ` yields an integer of bitsize
    `≤ τ + bit(n)`. BPR §8.1. -/
theorem Int.size_list_sum_le (l : List ℤ) (τ : ℕ)
    (hτ : ∀ x ∈ l, Int.size x ≤ τ) :
    Int.size l.sum ≤ τ + Nat.size l.length := by
  show l.sum.natAbs.size ≤ τ + l.length.size
  rw [Nat.size_le]
  have h_bound : ∀ x ∈ l.map Int.natAbs, x ≤ 2 ^ τ := by
    simp only [List.mem_map]; rintro _ ⟨a, ha, rfl⟩
    exact Nat.le_of_lt (Nat.size_le.mp (hτ a ha))
  have h1 : l.sum.natAbs ≤ (l.map Int.natAbs).sum := natAbs_list_sum_le l
  have h2 : (l.map Int.natAbs).sum ≤ l.length * 2 ^ τ := by
    have := List.sum_le_length_mul h_bound; simp at this; exact this
  have h3 : l.length * 2 ^ τ < 2 ^ l.length.size * 2 ^ τ :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self l.length) (Nat.two_pow_pos τ)
  have h4 : 2 ^ l.length.size * 2 ^ τ = 2 ^ (τ + l.length.size) := by
    rw [← pow_add]; congr 1; omega
  omega

/-!
### Bitsize of a product of integers

`|∏ aᵢ| = ∏ |aᵢ|` (multiplicativity of absolute value). Each
`|aᵢ| < 2^τ`, so `∏ |aᵢ| < (2^τ)^n = 2^{n·τ}`, whence
`bitsize(∏ aᵢ) ≤ n · τ`.

Note: this requires `n ≥ 1`, since for `n = 0` the empty product is
`1` and `bitsize(1) = 1 > 0 = 0 · τ`.
-/

/-- `|∏ aᵢ| = ∏ |aᵢ|` for integer lists. -/
theorem Int.natAbs_list_prod (l : List ℤ) :
    l.prod.natAbs = (l.map Int.natAbs).prod := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    show (a * as.prod).natAbs = a.natAbs * (as.map Int.natAbs).prod
    rw [Int.natAbs_mul, ih]

private theorem list_prod_le_pow {l : List ℕ} {b : ℕ}
    (h : ∀ x ∈ l, x ≤ b) : l.prod ≤ b ^ l.length := by
  induction l with
  | nil => exact le_refl 1
  | cons a as ih =>
    show a * as.prod ≤ b ^ (as.length + 1)
    rw [pow_succ']
    exact Nat.mul_le_mul (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

private theorem list_prod_lt_pow {l : List ℕ} {b : ℕ}
    (hl : l ≠ []) (hb : 0 < b) (h : ∀ x ∈ l, x < b) :
    l.prod < b ^ l.length := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a as ih =>
    have ha : a < b := h a (by simp)
    show a * as.prod < b ^ (as.length + 1)
    rw [pow_succ']
    have hle : as.prod ≤ b ^ as.length :=
      list_prod_le_pow (fun x hx => Nat.le_of_lt (h x (by simp [hx])))
    calc a * as.prod
        ≤ a * b ^ as.length := Nat.mul_le_mul_left a hle
      _ < b * b ^ as.length := Nat.mul_lt_mul_of_pos_right ha (Nat.pow_pos hb)

/-- Multiplying `n ≥ 1` integers each of bitsize `≤ τ` yields an integer of
    bitsize `≤ n · τ`. BPR §8.1. -/
theorem Int.size_list_prod_le (l : List ℤ) (τ : ℕ)
    (hl : l ≠ [])
    (hτ : ∀ x ∈ l, Int.size x ≤ τ) :
    Int.size l.prod ≤ l.length * τ := by
  show l.prod.natAbs.size ≤ l.length * τ
  rw [Nat.size_le, natAbs_list_prod]
  have h_map : ∀ x ∈ l.map Int.natAbs, x < 2 ^ τ := by
    simp only [List.mem_map]; rintro _ ⟨a, ha, rfl⟩
    exact Nat.size_le.mp (hτ a ha)
  have hne : l.map Int.natAbs ≠ [] := by simp [hl]
  calc (l.map Int.natAbs).prod
      < (2 ^ τ) ^ (l.map Int.natAbs).length :=
        list_prod_lt_pow hne (Nat.two_pow_pos τ) h_map
    _ = 2 ^ (l.length * τ) := by
        simp only [List.length_map]; rw [← pow_mul, Nat.mul_comm]

end Azurite.BPR
