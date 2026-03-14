import Mathlib.Data.Nat.Bits
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.Compare
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat

namespace Azurite.Nat

/-- `normalizedCompare x y` compares `x` and `y` as if their bit encodings were shifted to have the same length.
If `x > 0` and `y > 0`, the comparison is equivalent to a comparison between $f(x)$ and $f(y)$, where
$$
f(n) = n / 2^{\text{size } n}
$$
-/
def normalizedCompare (x y : ℕ) : Ordering :=
  if x = 0 then
    if y = 0 then Ordering.eq else Ordering.lt
  else if y = 0 then
    Ordering.gt
  else
    let sx := Nat.size x
    let sy := Nat.size y
    if sx ≤ sy then
      compare (x <<< (sy - sx)) y
    else
      compare x (y <<< (sx - sy))

#guard normalizedCompare 0 0 == Ordering.eq
#guard normalizedCompare 0 1 == Ordering.lt
#guard normalizedCompare 1 0 == Ordering.gt
#guard normalizedCompare 1 1 == Ordering.eq
#guard normalizedCompare 2 3 == Ordering.lt
#guard normalizedCompare 3 2 == Ordering.gt
#guard normalizedCompare 2 4 == Ordering.eq
#guard normalizedCompare 5 10 == Ordering.eq
#guard normalizedCompare 5 11 == Ordering.lt
#guard normalizedCompare 5 9 == Ordering.gt

lemma compare_div_eq_compare_mul {a b c d : ℚ} (hb : b > 0) (hd : d > 0) :
    compare (a / b) (c / d) = compare (a * d) (c * b) := by
  have hl : a / b < c / d ↔ a * d < c * b := div_lt_div_iff₀ hb hd
  have hg : c / d < a / b ↔ c * b < a * d := div_lt_div_iff₀ hd hb
  have he : a / b = c / d ↔ a * d = c * b := by
    constructor
    · intro h
      rcases lt_trichotomy (a * d) (c * b) with t1 | t2 | t3
      · exact False.elim (lt_irrefl (a / b) (h ▸ hl.mpr t1))
      · exact t2
      · exact False.elim (lt_irrefl (c / d) (h.symm ▸ hg.mpr t3))
    · intro h
      rcases lt_trichotomy (a / b) (c / d) with t1 | t2 | t3
      · exact False.elim (lt_irrefl (a * d) (h ▸ hl.mp t1))
      · exact t2
      · exact False.elim (lt_irrefl (c * b) (h.symm ▸ hg.mp t3))
  
  -- Use trichotomy to evaluate compare using standard macros
  rcases lt_trichotomy (a / b) (c / d) with h1 | h2 | h3
  · have h1' : a * d < c * b := hl.mp h1
    have c1 : compare (a / b) (c / d) = Ordering.lt := (compare_lt_iff_lt (a := a / b) (b := c / d)).mpr h1
    have c2 : compare (a * d) (c * b) = Ordering.lt := (compare_lt_iff_lt (a := a * d) (b := c * b)).mpr h1'
    rw [c1, c2]
  · have h2' : a * d = c * b := he.mp h2
    have c1 : compare (a / b) (c / d) = Ordering.eq := (compare_eq_iff_eq (a := a / b) (b := c / d)).mpr h2
    have c2 : compare (a * d) (c * b) = Ordering.eq := (compare_eq_iff_eq (a := a * d) (b := c * b)).mpr h2'
    rw [c1, c2]
  · have h3' : c * b < a * d := hg.mp h3
    have c1 : compare (a / b) (c / d) = Ordering.gt := (compare_gt_iff_gt (a := a / b) (b := c / d)).mpr h3
    have c2 : compare (a * d) (c * b) = Ordering.gt := (compare_gt_iff_gt (a := a * d) (b := c * b)).mpr h3'
    rw [c1, c2]

lemma compare_nat_cast (x y : ℕ) : compare (x : ℚ) (y : ℚ) = compare x y := by
  have hl : (x : ℚ) < (y : ℚ) ↔ x < y := Nat.cast_lt
  have hg : (y : ℚ) < (x : ℚ) ↔ y < x := Nat.cast_lt
  have he : (x : ℚ) = (y : ℚ) ↔ x = y := Nat.cast_inj
  
  rcases lt_trichotomy (x : ℚ) (y : ℚ) with h1 | h2 | h3
  · have h1' : x < y := hl.mp h1
    have c1 : compare (x : ℚ) (y : ℚ) = Ordering.lt := (compare_lt_iff_lt (a := (x : ℚ)) (b := (y : ℚ))).mpr h1
    have c2 : compare x y = Ordering.lt := (compare_lt_iff_lt (a := x) (b := y)).mpr h1'
    rw [c1, c2]
  · have h2' : x = y := he.mp h2
    have c1 : compare (x : ℚ) (y : ℚ) = Ordering.eq := (compare_eq_iff_eq (a := (x : ℚ)) (b := (y : ℚ))).mpr h2
    have c2 : compare x y = Ordering.eq := (compare_eq_iff_eq (a := x) (b := y)).mpr h2'
    rw [c1, c2]
  · have h3' : y < x := hg.mp h3
    have c1 : compare (x : ℚ) (y : ℚ) = Ordering.gt := (compare_gt_iff_gt (a := (x : ℚ)) (b := (y : ℚ))).mpr h3
    have c2 : compare x y = Ordering.gt := (compare_gt_iff_gt (a := x) (b := y)).mpr h3'
    rw [c1, c2]

lemma compare_mul_pos_right (a b c : ℕ) (hc : c > 0) : compare a b = compare (a * c) (b * c) := by
  have hl : a < b ↔ a * c < b * c := (Nat.mul_lt_mul_right hc).symm
  have hg : b < a ↔ b * c < a * c := (Nat.mul_lt_mul_right hc).symm
  have he : a = b ↔ a * c = b * c := by
    constructor
    · rintro rfl; rfl
    · intro h; exact Nat.eq_of_mul_eq_mul_right hc h
  
  rcases lt_trichotomy a b with h1 | h2 | h3
  · have h1' : a * c < b * c := hl.mp h1
    have c1 : compare a b = Ordering.lt := (compare_lt_iff_lt (a := a) (b := b)).mpr h1
    have c2 : compare (a * c) (b * c) = Ordering.lt := (compare_lt_iff_lt (a := a * c) (b := b * c)).mpr h1'
    rw [c1, c2]
  · have h2' : a * c = b * c := he.mp h2
    have c1 : compare a b = Ordering.eq := (compare_eq_iff_eq (a := a) (b := b)).mpr h2
    have c2 : compare (a * c) (b * c) = Ordering.eq := (compare_eq_iff_eq (a := a * c) (b := b * c)).mpr h2'
    rw [c1, c2]
  · have h3' : b * c < a * c := hg.mp h3
    have c1 : compare a b = Ordering.gt := (compare_gt_iff_gt (a := a) (b := b)).mpr h3
    have c2 : compare (a * c) (b * c) = Ordering.gt := (compare_gt_iff_gt (a := a * c) (b := b * c)).mpr h3'
    rw [c1, c2]

lemma normalizedCompare_eq_rat (x y : ℕ) (hx : x > 0) (hy : y > 0) :
  normalizedCompare x y = compare ((x : ℚ) / (2 ^ Nat.size x : ℚ)) ((y : ℚ) / (2 ^ Nat.size y : ℚ)) := by
  have sx_pos : 2 ^ Nat.size x > 0 := Nat.pow_pos (by decide)
  have sy_pos : 2 ^ Nat.size y > 0 := Nat.pow_pos (by decide)
  have qx_pos : (0 : ℚ) < (2 ^ Nat.size x : ℚ) := by exact_mod_cast sx_pos
  have qy_pos : (0 : ℚ) < (2 ^ Nat.size y : ℚ) := by exact_mod_cast sy_pos
  
  -- The core logic will rely on the ordering equivalence of cross multiplication
  have hm : compare ((x : ℚ) / (2 ^ Nat.size x : ℚ)) ((y : ℚ) / (2 ^ Nat.size y : ℚ)) = compare ((x : ℚ) * (2 ^ Nat.size y : ℚ)) ((y : ℚ) * (2 ^ Nat.size x : ℚ)) :=
    compare_div_eq_compare_mul qx_pos qy_pos
  rw [hm]
  
  -- Now we just pull the casts out
  have h_pull_x : (x : ℚ) * (2 ^ Nat.size y : ℚ) = ((x * 2 ^ Nat.size y : ℕ) : ℚ) := by simp
  have h_pull_y : (y : ℚ) * (2 ^ Nat.size x : ℚ) = ((y * 2 ^ Nat.size x : ℕ) : ℚ) := by simp
  rw [h_pull_x, h_pull_y]
  
  -- And use compare_nat_cast
  rw [compare_nat_cast]
  
  have hx_ne : x ≠ 0 := Nat.pos_iff_ne_zero.mp hx
  have hy_ne : y ≠ 0 := Nat.pos_iff_ne_zero.mp hy
  
  -- Relate shiftLeft directly to multiplied powers
  unfold normalizedCompare
  rw [if_neg hx_ne, if_neg hy_ne]
  
  dsimp only
  split_ifs with h_le
  · -- x.size <= y.size
    rw [Nat.shiftLeft_eq]
    have hm1 : compare (x * 2 ^ (y.size - x.size)) y = compare (x * 2 ^ (y.size - x.size) * 2 ^ x.size) (y * 2 ^ x.size) :=
      compare_mul_pos_right (x * 2 ^ (y.size - x.size)) y (2 ^ x.size) sx_pos
    rw [hm1]
    have h_add : y.size - x.size + x.size = y.size := Nat.sub_add_cancel h_le
    have h_mul : x * 2 ^ (y.size - x.size) * 2 ^ x.size = x * 2 ^ y.size := by
      rw [Nat.mul_assoc, ← Nat.pow_add, h_add]
    rw [h_mul]
  · -- y.size < x.size (since ¬ x.size <= y.size)
    have h_lt : y.size < x.size := Nat.lt_of_not_le h_le
    have h_le_rev : y.size ≤ x.size := Nat.le_of_lt h_lt
    rw [Nat.shiftLeft_eq]
    have hm1 : compare x (y * 2 ^ (x.size - y.size)) = compare (x * 2 ^ y.size) (y * 2 ^ (x.size - y.size) * 2 ^ y.size) :=
      compare_mul_pos_right x (y * 2 ^ (x.size - y.size)) (2 ^ y.size) sy_pos
    rw [hm1]
    have h_add : x.size - y.size + y.size = x.size := Nat.sub_add_cancel h_le_rev
    have h_mul : y * 2 ^ (x.size - y.size) * 2 ^ y.size = y * 2 ^ x.size := by
      rw [Nat.mul_assoc, ← Nat.pow_add, h_add]
    rw [h_mul]

end Azurite.Nat
