/-
  `BitInterleave` — m-way bit interleaving over an abstract slot assignment
  (`BitAssignment`), underlying Malachite's `BitDistributor`.

  A single counter `k : ℕ` is deinterleaved into `m` component numbers by
  distributing its bits among `m` slots. Which slot owns which counter-bit
  position is abstracted into a `BitAssignment m`: a three-map structure
  (`slotOf`/`rank`/`pos`) whose laws say exactly that the counter positions are
  partitioned among the slots, each slot owning an infinite strictly-ascending
  sequence of positions. `deinterleave`/`interleave` and the headline bijection
  `ℕ ≃ (Fin m → ℕ)` (`BitAssignment.deinterleaveTuple_bijective`) are defined
  and proved ONCE against the abstract laws, as bounded `Finset.range` bit sums
  — no recursion.

  The first instance is `roundRobin m`: the all-normal weight-1 assignment,
  counter-bit position `i` belongs to slot `m - 1 - (i % m)` (Malachite assigns
  the LAST output the least-significant bit), so bit `r` of slot `j`'s output
  is bit `r * m + (m - 1 - j)` of `k`.

  Architecture: further assignments — weighted round-robin (a slot owning `w`
  of every `∑ weights` consecutive positions) and tiny/ruler assignments (a
  slot owning logarithmically-sparse positions) — arrive later as new
  `BitAssignment` instances, and the bijection is free: only the four little
  laws need proving. CAPPED slots (finite components, where a slot owns only
  finitely many positions) do NOT fit this structure; they are the sibling
  `CappedBitAssignment` in `BitInterleaveCapped`.

  Everything is a self-contained pure-ℕ theory over `Nat.testBit`; no
  generator machinery is imported.
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace Azurite

/-! ### `Nat.testBit` toolbox

Two reusable `testBit` facts about `ℕ` arithmetic that the interleave proofs
rest on. Neither mentions the interleaving; they are generic bit lemmas. -/

/-- **Adding a fresh power of two sets exactly one bit.** If bit `p` of `rest`
is clear, then `rest + 2 ^ p` agrees with `rest` on every bit except `p`, which
becomes set. (No carry can reach or pass bit `p` because it was `0`.) This is
the carry-free addition fact underlying `testBit_sum_pow`. -/
theorem testBit_add_two_pow_of_testBit_false (rest p : ℕ) (h : rest.testBit p = false)
    (q : ℕ) : (rest + 2 ^ p).testBit q = (if q = p then true else rest.testBit q) := by
  have hpow : (0 : ℕ) < 2 ^ p := by positivity
  have heven : rest / 2 ^ p % 2 = 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at h
    simp only [decide_eq_false_iff_not] at h; omega
  have hlo : rest % 2 ^ p < 2 ^ p := Nat.mod_lt _ hpow
  have hsplit : rest = 2 ^ p * (rest / 2 ^ p) + rest % 2 ^ p := by
    conv_lhs => rw [← Nat.div_add_mod rest (2 ^ p)]
  have hsum : rest + 2 ^ p = 2 ^ p * (rest / 2 ^ p + 1) + rest % 2 ^ p := by
    conv_lhs => rw [hsplit]
    ring
  rw [hsum]; conv_rhs => rw [hsplit]
  rw [Nat.testBit_two_pow_mul_add _ hlo, Nat.testBit_two_pow_mul_add _ hlo]
  by_cases hqp : q < p
  · simp only [ite_eq_left hqp, ite_eq_right (show q ≠ p by omega)]
  · simp only [ite_eq_right hqp]
    by_cases hq0 : q = p
    · subst hq0; rw [Nat.sub_self, ite_eq_left rfl, Nat.testBit_zero]
      simp only [decide_eq_true_eq]; omega
    · rw [ite_eq_right hq0]
      obtain ⟨d, hd⟩ : ∃ d, q - p = d + 1 := ⟨q - p - 1, by omega⟩
      rw [hd, Nat.testBit_add_one, Nat.testBit_add_one]; congr 1; omega

/-- **`testBit` of a sum of distinct powers of two.** For a `Finset` sum of
terms each of the form `if b a then 2 ^ (e a) else 0`, where `e` is injective on
`s` (so the summands occupy pairwise-distinct bit positions and there are no
carries), the bit at `i` is set exactly when some `a ∈ s` has `e a = i` and its
flag `b a` is on. This is the bit-vector reading of any interleaving sum. -/
theorem testBit_sum_pow {α : Type*} [DecidableEq α] (s : Finset α) (e : α → ℕ)
    (b : α → Bool) (hinj : Set.InjOn e s) (i : ℕ) :
    (∑ a ∈ s, (if b a then 2 ^ (e a) else 0)).testBit i
      = decide (∃ a ∈ s, e a = i ∧ b a = true) := by
  induction s using Finset.induction generalizing i with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hinj' : Set.InjOn e s := hinj.mono (Finset.subset_insert _ _)
    by_cases hba : b a = true
    · -- The `a`-term is `2 ^ (e a)`, and the rest has bit `e a` clear (injectivity).
      simp only [hba, ite_true]
      have hrest_ea :
          (∑ a' ∈ s, (if b a' then 2 ^ (e a') else 0)).testBit (e a) = false := by
        rw [ih hinj']
        simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro a' ha' hea' _
        exact ha (by rw [← hinj (by simp [ha']) (by simp) hea']; exact ha')
      rw [Nat.add_comm, testBit_add_two_pow_of_testBit_false _ _ hrest_ea, ih hinj']
      by_cases hi : i = e a
      · subst hi
        rw [ite_eq_left rfl]
        symm; simp only [decide_eq_true_eq]
        exact ⟨a, Finset.mem_insert_self _ _, rfl, hba⟩
      · rw [ite_eq_right (by omega)]
        congr 1
        simp only [eq_iff_iff]
        constructor
        · rintro ⟨a', ha', hea', hba'⟩; exact ⟨a', Finset.mem_insert_of_mem ha', hea', hba'⟩
        · rintro ⟨a', ha', hea', hba'⟩
          rcases Finset.mem_insert.mp ha' with h1 | h1
          · exact absurd (h1 ▸ hea').symm hi
          · exact ⟨a', h1, hea', hba'⟩
    · -- The `a`-term is `0`; the sum is just the rest.
      simp only [Bool.not_eq_true] at hba
      simp only [hba, Bool.false_eq_true, ite_false, Nat.zero_add, ih hinj']
      congr 1
      simp only [eq_iff_iff]
      constructor
      · rintro ⟨a', ha', hea', hba'⟩; exact ⟨a', Finset.mem_insert_of_mem ha', hea', hba'⟩
      · rintro ⟨a', ha', hea', hba'⟩
        rcases Finset.mem_insert.mp ha' with h1 | h1
        · exact absurd hba' (by rw [h1, hba]; simp)
        · exact ⟨a', h1, hea', hba'⟩

/-! ### The abstract slot assignment -/

/-- A **bit assignment**: a partition of the counter-bit positions `ℕ` among
`m` slots, each slot owning an infinite strictly-ascending sequence of
positions. `slotOf i` is the slot owning counter position `i`; `rank i` is
`i`'s index within its slot's ascending positions; `pos j r` is the `r`-th
position owned by slot `j`. The four laws say `(slotOf, rank)` and
`Sigma.uncurry pos` are mutually inverse bijections `ℕ ≃ (j : Fin m) × ℕ` and
that each slot's positions come in ascending order.

The interleave/deinterleave maps and their bijection are proved once against
these laws; each concrete assignment (weight-1 round-robin below; weighted and
tiny/ruler assignments later) only has to establish the four laws. -/
structure BitAssignment (m : ℕ) where
  /-- The slot owning counter-bit position `i`. -/
  slotOf : ℕ → Fin m
  /-- The index of position `i` within its slot's ascending list of positions. -/
  rank : ℕ → ℕ
  /-- The `r`-th (0-based, ascending) counter position owned by slot `j`. -/
  pos : Fin m → ℕ → ℕ
  /-- Slot `j` owns all the positions `pos j r`. -/
  pos_slotOf : ∀ j r, slotOf (pos j r) = j
  /-- `pos j r` is the `r`-th position of its slot. -/
  rank_pos : ∀ j r, rank (pos j r) = r
  /-- Every position is reached: `pos` inverts `(slotOf, rank)`. -/
  pos_rank : ∀ i, pos (slotOf i) (rank i) = i
  /-- Each slot's positions are strictly ascending in the rank. -/
  pos_strictMono : ∀ j, StrictMono (pos j)

namespace BitAssignment

variable {m : ℕ} (A : BitAssignment m)

/-- The `r`-th position of a slot is at least `r` (strict monotonicity from
`0`). This is what bounds `deinterleave` by `k.size` bits. -/
theorem le_pos (j : Fin m) (r : ℕ) : r ≤ A.pos j r :=
  (A.pos_strictMono j).le_apply

/-- `(j, r) ↦ pos j r` is injective: `slotOf` recovers `j` and `rank` recovers
`r`. -/
theorem pos_inj {j j' : Fin m} {r r' : ℕ} (h : A.pos j r = A.pos j' r') :
    j = j' ∧ r = r' := by
  have hj : j = j' := by rw [← A.pos_slotOf j r, h, A.pos_slotOf]
  refine ⟨hj, ?_⟩
  rw [← A.rank_pos j r, h, ← hj, A.rank_pos]

/-! ### Deinterleave and interleave

Both maps are bounded bit sums over `Finset.range` — no recursion. The bound
`k.size` (resp. `(f j).size`) is exact: all higher bits vanish, because
`pos j r ≥ r` and `k < 2 ^ k.size`. -/

/-- `A.deinterleave j k` extracts slot `j`'s component of the counter `k`: the
number whose bit `r` is bit `A.pos j r` of `k`. Only ranks `r < k.size` can
contribute (`le_pos`), so the sum is finite and computable. -/
def deinterleave (j : Fin m) (k : ℕ) : ℕ :=
  ∑ r ∈ Finset.range k.size, if k.testBit (A.pos j r) then 2 ^ r else 0

/-- `A.interleave f` assembles a counter from the components: bit `r` of `f j`
lands at counter position `A.pos j r`. The double sum ranges over pairwise
distinct positions (`pos_inj`), so there are no carries. -/
def interleave (f : Fin m → ℕ) : ℕ :=
  ∑ j, ∑ r ∈ Finset.range (f j).size, if (f j).testBit r then 2 ^ (A.pos j r) else 0

/-- The full deinterleave map `ℕ → (Fin m → ℕ)`: distribute the bits of `k`
into `m` component numbers according to the assignment. This is the function
whose bijectivity powers the fair `m`-way product enumerations. -/
def deinterleaveTuple (k : ℕ) : Fin m → ℕ := fun j => A.deinterleave j k

/-- **The defining `testBit` characterization of `deinterleave`.** Bit `r` of
`A.deinterleave j k` is bit `A.pos j r` of `k` — with no bound on `r`: above
`k.size` both sides are false, since `pos j r ≥ r ≥ k.size` and
`k < 2 ^ k.size`. -/
theorem testBit_deinterleave (j : Fin m) (k r : ℕ) :
    (A.deinterleave j k).testBit r = k.testBit (A.pos j r) := by
  unfold deinterleave
  rw [testBit_sum_pow (Finset.range k.size) (fun x => x)
    (fun x => k.testBit (A.pos j x)) (Set.injOn_id _) r]
  by_cases hr : r < k.size
  · -- In range: the unique possible witness is `a = r`.
    by_cases hb : k.testBit (A.pos j r) = true
    · rw [hb]
      simp only [decide_eq_true_eq]
      exact ⟨r, Finset.mem_range.mpr hr, rfl, hb⟩
    · simp only [Bool.not_eq_true] at hb
      rw [hb]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      rintro a _ rfl
      simp [hb]
  · -- Above the bound: both sides are false.
    have hbig : k.testBit (A.pos j r) = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (Nat.lt_size_self k)
        (Nat.pow_le_pow_right (by norm_num) ((by omega : k.size ≤ r).trans (A.le_pos j r))))
    rw [hbig]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    rintro a ha rfl
    exact absurd (Finset.mem_range.mp ha) hr

/-- **The defining `testBit` characterization of `interleave`.** Bit `i` of
`A.interleave f` is bit `A.rank i` of the component owning position `i`,
namely `f (A.slotOf i)`. Position `i` appears in the double sum only as
`pos (slotOf i) (rank i)` (`pos_inj` + `pos_rank`); when `rank i` is at or
above `(f (slotOf i)).size` both sides are false. -/
theorem testBit_interleave (f : Fin m → ℕ) (i : ℕ) :
    (A.interleave f).testBit i = (f (A.slotOf i)).testBit (A.rank i) := by
  unfold interleave
  rw [Finset.sum_sigma' Finset.univ (fun j => Finset.range (f j).size)
    (fun j r => if (f j).testBit r then 2 ^ (A.pos j r) else 0)]
  rw [testBit_sum_pow (Finset.univ.sigma fun j => Finset.range (f j).size)
    (fun p => A.pos p.1 p.2) (fun p => (f p.1).testBit p.2) ?_ i]
  · by_cases hb : (f (A.slotOf i)).testBit (A.rank i) = true
    · rw [hb]
      simp only [decide_eq_true_eq]
      -- The bit is set, so the rank is below the size.
      have hrank : A.rank i < (f (A.slotOf i)).size := by
        by_contra hge
        rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (Nat.lt_size_self _)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hb
        exact Bool.false_ne_true hb
      exact ⟨⟨A.slotOf i, A.rank i⟩, Finset.mem_sigma.mpr
        ⟨Finset.mem_univ _, Finset.mem_range.mpr hrank⟩, A.pos_rank i, hb⟩
    · simp only [Bool.not_eq_true] at hb
      rw [hb]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      rintro ⟨pj, pr⟩ _ hpos
      have hj : A.slotOf i = pj := by rw [← hpos, A.pos_slotOf]
      have hr : A.rank i = pr := by rw [← hpos, A.rank_pos]
      rw [← hj, ← hr, hb]
      simp
  · -- The positions of the double sum are pairwise distinct.
    rintro ⟨pj, pr⟩ - ⟨qj, qr⟩ - hpq
    obtain ⟨h1, h2⟩ := A.pos_inj hpq
    subst h1; subst h2; rfl

/-! ### Round-trips and the bijection -/

/-- **Left inverse.** Deinterleaving the interleaving of `f` recovers `f`. By
`testBit` extensionality plus the two characterizations; the index bijection is
exactly the `pos_slotOf`/`rank_pos` laws. -/
theorem deinterleave_interleave (f : Fin m → ℕ) (j : Fin m) :
    A.deinterleave j (A.interleave f) = f j := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [A.testBit_deinterleave, A.testBit_interleave, A.pos_slotOf, A.rank_pos]

/-- **Right inverse.** Interleaving the deinterleaved components of `k`
recovers `k`. Dual to `deinterleave_interleave`, via the `pos_rank` law. -/
theorem interleave_deinterleave (k : ℕ) :
    A.interleave (A.deinterleaveTuple k) = k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [A.testBit_interleave, deinterleaveTuple, A.testBit_deinterleave, A.pos_rank]

/-- **The headline bijection.** `A.deinterleaveTuple : ℕ → (Fin m → ℕ)` is a
bijection for ANY bit assignment: injective because `A.interleave` is a common
left inverse (`interleave_deinterleave`), surjective with witness
`A.interleave f` (`deinterleave_interleave`). Every concrete assignment
(round-robin below; weighted/tiny later) inherits this for free. -/
theorem deinterleaveTuple_bijective : Function.Bijective A.deinterleaveTuple := by
  constructor
  · -- Injective: `A.interleave` retracts `A.deinterleaveTuple`.
    intro a b hab
    have ha := A.interleave_deinterleave a
    have hb := A.interleave_deinterleave b
    rw [← ha, ← hb, hab]
  · -- Surjective: `A.interleave f` maps to `f`.
    intro f
    refine ⟨A.interleave f, ?_⟩
    funext j
    exact A.deinterleave_interleave f j

end BitAssignment

/-! ### The weight-1 round-robin instance (Malachite's all-normal case) -/

/-- Malachite's all-normal weight-1 round-robin assignment: counter position
`i` belongs to slot `m - 1 - (i % m)` (the LAST slot owns the least-significant
bit), and slot `j`'s `r`-th position is `r * m + (m - 1 - j)`. The four laws
are elementary `%`/`/` arithmetic. -/
def roundRobin (m : ℕ) (hm : 0 < m) : BitAssignment m where
  slotOf i := ⟨m - 1 - i % m, by have := Nat.mod_lt i hm; omega⟩
  rank i := i / m
  pos j r := r * m + (m - 1 - j.val)
  pos_slotOf j r := by
    have hj := j.isLt
    apply Fin.ext
    show m - 1 - (r * m + (m - 1 - j.val)) % m = j.val
    rw [Nat.mul_add_mod', Nat.mod_eq_of_lt (by omega)]
    omega
  rank_pos j r := by
    have hj := j.isLt
    show (r * m + (m - 1 - j.val)) / m = r
    rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  pos_rank i := by
    have hlt := Nat.mod_lt i hm
    show i / m * m + (m - 1 - (m - 1 - i % m)) = i
    rw [show m - 1 - (m - 1 - i % m) = i % m by omega]
    conv_rhs => rw [← Nat.div_add_mod i m]
    ring
  pos_strictMono j a b h :=
    Nat.add_lt_add_right (Nat.mul_lt_mul_of_lt_of_le h (Nat.le_refl m) hm) _

/-- For `m = 1` there is a single slot owning every position, so `deinterleave`
is the identity. -/
theorem roundRobin_deinterleave_one (j : Fin 1) (k : ℕ) :
    (roundRobin 1 Nat.one_pos).deinterleave j k = k := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [(roundRobin 1 Nat.one_pos).testBit_deinterleave]
  show k.testBit (r * 1 + (1 - 1 - j.val)) = k.testBit r
  congr 1
  have : j.val = 0 := by omega
  omega

/-! ### Guards (pin Malachite's `Z`-order) -/

-- The exact `BitDistributor` pairs doctest (`[normal(1); 2]`): slot 0 = x owns
-- offset 1, slot 1 = y owns offset 0.
#guard (let A := roundRobin 2 (by norm_num);
  (List.range 10).map (fun k => (A.deinterleave 0 k, A.deinterleave 1 k)))
  == [(0,0),(0,1),(1,0),(1,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1)]

-- `m = 3` spot checks. Offsets: slot 0 = 2, slot 1 = 1, slot 2 = 0.
-- k = 0b111 = 7: bit0→slot2, bit1→slot1, bit2→slot0, so (1,1,1).
#guard (let A := roundRobin 3 (by norm_num);
  (A.deinterleave 0 7, A.deinterleave 1 7, A.deinterleave 2 7)) == (1, 1, 1)
-- k = 0b111000 = 56: bits 3,4,5 → r=1 of slots 2,1,0, so (2,2,2).
#guard (let A := roundRobin 3 (by norm_num);
  (A.deinterleave 0 56, A.deinterleave 1 56, A.deinterleave 2 56)) == (2, 2, 2)

-- `m = 1` deinterleave is the identity.
#guard (let A := roundRobin 1 Nat.one_pos;
  (List.range 6).map (A.deinterleave 0)) == [0, 1, 2, 3, 4, 5]

-- Round-trips both ways.
#guard (let A := roundRobin 2 (by norm_num);
  let k := A.interleave ![5, 3]; (A.deinterleave 0 k, A.deinterleave 1 k)) == (5, 3)
#guard (let A := roundRobin 2 (by norm_num);
  (List.range 12).all (fun k => A.interleave ![A.deinterleave 0 k, A.deinterleave 1 k] == k))
#guard (let A := roundRobin 3 (by norm_num);
  (List.range 20).all (fun k =>
    A.interleave ![A.deinterleave 0 k, A.deinterleave 1 k, A.deinterleave 2 k] == k))
#guard (let A := roundRobin 3 (by norm_num); A.interleave ![2, 2, 2]) == 56

end Azurite
