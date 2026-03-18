import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.Compare
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat

namespace Azurite.Nat

/-- For positive `n`, `Nat.size n = Nat.log2 n + 1`. -/
lemma size_eq_log2_succ (n : ℕ) (hn : n > 0) : Nat.size n = Nat.log2 n + 1 := by
  have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  apply Nat.le_antisymm
  · rw [Nat.size_le]
    exact (Nat.log2_lt hn').mp (Nat.lt_succ_of_le (Nat.le_refl _))
  · rw [Nat.add_one_le_iff, Nat.lt_size]
    exact Nat.log2_self_le hn'

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
    let lx := Nat.log2 x
    let ly := Nat.log2 y
    if lx ≤ ly then
      let shift := ly - lx
      match compare x (y >>> shift) with
      | .lt => .lt
      | .gt => .gt
      | .eq => if y &&& ((1 <<< shift) - 1) = 0 then .eq else .lt
    else
      let shift := lx - ly
      match compare (x >>> shift) y with
      | .lt => .lt
      | .gt => .gt
      | .eq => if x &&& ((1 <<< shift) - 1) = 0 then .eq else .gt

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

/-- Bridge lemma: comparing x with y>>>shift is equivalent to comparing x<<<shift with y. -/
private lemma compare_shiftr_eq_compare_shiftl (x y shift : Nat) :
    (match compare x (y >>> shift) with
     | .lt => Ordering.lt
     | .gt => Ordering.gt
     | .eq => if y &&& ((1 <<< shift) - 1) = 0 then Ordering.eq else Ordering.lt) =
    compare (x <<< shift) y := by
  simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow,
             Nat.and_two_pow_sub_one_eq_mod]
  have h_pos : (0 : Nat) < 2 ^ shift := Nat.pow_pos (by omega)
  have h_dam := Nat.div_add_mod y (2 ^ shift)
  have h_comm : 2 ^ shift * (y / 2 ^ shift) = y / 2 ^ shift * 2 ^ shift := Nat.mul_comm _ _
  rcases lt_trichotomy x (y / 2 ^ shift) with h_lt | h_eq | h_gt
  · have : x * 2 ^ shift < y :=
      lt_of_lt_of_le ((Nat.mul_lt_mul_right h_pos).mpr h_lt) (Nat.div_mul_le_self y _)
    simp [compare_lt_iff_lt.mpr h_lt, compare_lt_iff_lt.mpr this]
  · simp only [h_eq, compare_eq_iff_eq.mpr rfl]
    split
    · rename_i h
      exact (compare_eq_iff_eq.mpr (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h))).symm
    · rename_i h
      have : y / 2 ^ shift * 2 ^ shift < y := by omega
      exact (compare_lt_iff_lt.mpr this).symm
  · have : y < x * 2 ^ shift := Nat.lt_mul_of_div_lt h_gt h_pos
    simp [compare_gt_iff_gt.mpr h_gt, compare_gt_iff_gt.mpr this]

/-- Symmetric bridge lemma: comparing x>>>shift with y is equivalent to comparing x with y<<<shift. -/
private lemma compare_shiftr_eq_compare_shiftl' (x y shift : Nat) :
    (match compare (x >>> shift) y with
     | .lt => Ordering.lt
     | .gt => Ordering.gt
     | .eq => if x &&& ((1 <<< shift) - 1) = 0 then Ordering.eq else Ordering.gt) =
    compare x (y <<< shift) := by
  simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow,
             Nat.and_two_pow_sub_one_eq_mod]
  have h_pos : (0 : Nat) < 2 ^ shift := Nat.pow_pos (by omega)
  have h_dam := Nat.div_add_mod x (2 ^ shift)
  have h_comm : 2 ^ shift * (x / 2 ^ shift) = x / 2 ^ shift * 2 ^ shift := Nat.mul_comm _ _
  rcases lt_trichotomy (x / 2 ^ shift) y with h_lt | h_eq | h_gt
  · have : x < y * 2 ^ shift := Nat.lt_mul_of_div_lt h_lt h_pos
    simp [compare_lt_iff_lt.mpr h_lt, compare_lt_iff_lt.mpr this]
  · simp only [h_eq, compare_eq_iff_eq.mpr rfl]
    split
    · rename_i h
      have : x = x / 2 ^ shift * 2 ^ shift := by omega
      exact (compare_eq_iff_eq.mpr (by rw [this, h_eq])).symm
    · rename_i h
      have : x / 2 ^ shift * 2 ^ shift < x := by omega
      rw [h_eq] at this
      exact (compare_gt_iff_gt.mpr this).symm
  · have : y * 2 ^ shift < x :=
      lt_of_lt_of_le ((Nat.mul_lt_mul_right h_pos).mpr h_gt) (Nat.div_mul_le_self x _)
    simp [compare_gt_iff_gt.mpr h_gt, compare_gt_iff_gt.mpr this]

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
  -- Relate log2 to size for the proof
  have h_sx : Nat.log2 x + 1 = Nat.size x := (size_eq_log2_succ x hx).symm
  have h_sy : Nat.log2 y + 1 = Nat.size y := (size_eq_log2_succ y hy).symm
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
  
  -- Unfold and use bridge lemmas to convert shift-right back to shift-left form
  unfold normalizedCompare
  simp only [hx_ne, hy_ne, ↓reduceIte]
  
  have h_le_iff : Nat.log2 x ≤ Nat.log2 y ↔ Nat.size x ≤ Nat.size y := by omega
  have h_diff_eq : Nat.log2 y - Nat.log2 x = Nat.size y - Nat.size x := by omega
  have h_diff_eq' : Nat.log2 x - Nat.log2 y = Nat.size x - Nat.size y := by omega
  
  split
  · -- log2 x ≤ log2 y: use bridge lemma to convert shift-right to shift-left
    rename_i h_le
    rw [compare_shiftr_eq_compare_shiftl, h_diff_eq, Nat.shiftLeft_eq]
    have h_le' : Nat.size x ≤ Nat.size y := h_le_iff.mp h_le
    have hm1 : compare (x * 2 ^ (y.size - x.size)) y = compare (x * 2 ^ (y.size - x.size) * 2 ^ x.size) (y * 2 ^ x.size) :=
      compare_mul_pos_right (x * 2 ^ (y.size - x.size)) y (2 ^ x.size) sx_pos
    rw [hm1]
    have h_add : y.size - x.size + x.size = y.size := Nat.sub_add_cancel h_le'
    have h_mul : x * 2 ^ (y.size - x.size) * 2 ^ x.size = x * 2 ^ y.size := by
      rw [Nat.mul_assoc, ← Nat.pow_add, h_add]
    rw [h_mul]
  · -- log2 x > log2 y: use symmetric bridge lemma
    rename_i h_not_le
    rw [compare_shiftr_eq_compare_shiftl', h_diff_eq']
    have h_lt : y.size < x.size := by omega
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
