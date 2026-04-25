import Azurite.BasuPollackRoy.Chapter2.Proposition_2_27
import Mathlib.Data.List.Sort

/-!
# BPR Definition 2.45: Virtual Roots

**Definition 2.45 (BPR).** The *virtual roots* of a polynomial `P ∈ R[X]` of
degree `p` are defined inductively on `p`:

- If `p = 0`, `P` has no virtual roots.
- Otherwise, let `y_1 ≤ … ≤ y_{p−1}` be the virtual roots of `P'`. Partition
  the real line into `I_1 = (−∞, y_1]`, `I_i = [y_{i−1}, y_i]` for
  `2 ≤ i ≤ p − 1`, and `I_p = [y_{p−1}, +∞)`. The virtual root `x_i ∈ I_i`
  is the unique point where `|P|` attains its minimum on `I_i`.

Simultaneously, one proves three properties:
- (a) The number of virtual roots equals `p = deg P`.
- (b) On every open interval between consecutive virtual roots (or outside
  the extremes), the sign of `P` is constant.
- (c) The virtual roots of `P` and `P'` interlace:
  `x_1 ≤ y_1 ≤ x_2 ≤ y_2 ≤ ⋯ ≤ y_{p−1} ≤ x_p`.

This file lays the foundation: predicates capturing (a)–(c) and the base
case `p = 0`. The inductive step is developed in subsequent sections.
-/

namespace Azurite.BPR.VirtualRoots.Internal

open Polynomial Azurite.BPR Azurite.BPR.Proposition2_21 Azurite.BPR.Proposition2_27

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Core predicates -/

/-- Two lists `xs` and `ys` are **interlaced** when they have the shape
    `xs = [x₀, x₁, …, x_{p-1}, x_p]` and `ys = [y₀, …, y_{p-1}]` with
    `x₀ ≤ y₀ ≤ x₁ ≤ y₁ ≤ ⋯ ≤ y_{p-1} ≤ x_p`. Captured structurally by
    recursion on `ys`. Corresponds to BPR property (c). -/
def Interlaced : List R → List R → Prop
  | [_], [] => True
  | x :: x' :: xs, y :: ys => x ≤ y ∧ y ≤ x' ∧ Interlaced (x' :: xs) ys
  | _, _ => False

/-- The sign of `P` is constant on each open interval determined by consecutive
    entries of `roots`, and on the two unbounded tails. Concretely: whenever
    `x ≤ y` and no entry of `roots` lies in the closed interval `[x, y]`, the
    values `P.eval x` and `P.eval y` share the same nonzero sign. This is BPR
    property (b). -/
def SignConstantOnGaps (P : R[X]) (roots : List R) : Prop :=
  ∀ x y : R, x ≤ y → (∀ r ∈ roots, r < x ∨ y < r) →
    P.eval x ≠ 0 ∧ SignType.sign (P.eval x) = SignType.sign (P.eval y)

/-- `x ∈ S` is a non-strict minimizer of `|P.eval|` on `S`: `|P.eval x| ≤ |P.eval z|`
    for every `z ∈ S`. -/
def IsArgminAbsOn (P : R[X]) (S : Set R) (x : R) : Prop :=
  x ∈ S ∧ ∀ z ∈ S, |P.eval x| ≤ |P.eval z|

/-- Partition argmin witness for the middle/right intervals. Given an anchor
    `a` (the previous virtual root of `P'`), a non-empty tail `x :: rest` of
    virtual roots of `P`, and the corresponding tail of virtual roots of `P'`,
    say each `xᵢ` minimises `|P|` on `[yᵢ₋₁, yᵢ]` (or on `[y_{p−1}, ∞)` for
    the last). -/
def ArgminPartitionFrom (P : R[X]) (a : R) : List R → List R → Prop
  | [x], [] => IsArgminAbsOn P (Set.Ici a) x
  | x :: x' :: xs, y :: ys =>
      IsArgminAbsOn P (Set.Icc a y) x ∧ ArgminPartitionFrom P y (x' :: xs) ys
  | _, _ => False

/-- Partition argmin witness for the whole line. The first entry `x` minimises
    `|P|` on `(−∞, y₀]`, and subsequent entries follow via
    `ArgminPartitionFrom`. -/
def ArgminPartition (P : R[X]) : List R → List R → Prop
  | [x], [] => IsArgminAbsOn P Set.univ x
  | x :: x' :: xs, y :: ys =>
      IsArgminAbsOn P (Set.Iic y) x ∧ ArgminPartitionFrom P y (x' :: xs) ys
  | _, _ => False

/-- Depth-`n` virtual-roots-list predicate, parameterised by a `ℕ` that the
    recursion structurally decreases on. In practice, `n = P.natDegree`. The
    `n + 1` case requires a nested virtual-roots list `ys` of `derivative P`
    at depth `n`, which matches `(derivative P).natDegree = n`. -/
def IsVirtualRootsListAux : ℕ → R[X] → List R → Prop
  | 0, P, xs =>
      xs.length = P.natDegree ∧
      xs.Pairwise (· ≤ ·) ∧
      SignConstantOnGaps P xs
  | n + 1, P, xs =>
      xs.length = P.natDegree ∧
      xs.Pairwise (· ≤ ·) ∧
      SignConstantOnGaps P xs ∧
      (xs = [] ∨
        ∃ ys : List R,
          IsVirtualRootsListAux n (derivative P) ys ∧
          Interlaced xs ys ∧
          ArgminPartition P xs ys)

/-- `IsVirtualRootsList P xs` captures BPR Definition 2.45: `xs` is a sorted
    list whose length matches `natDegree P`, `P` has constant sign on each gap,
    and (when `xs ≠ []`) there is a virtual roots list `ys` of `P'` interlaced
    with `xs` such that each entry of `xs` is an argmin of `|P|` on the
    corresponding interval `Iᵢ` determined by `ys`.

    Implemented via `IsVirtualRootsListAux` with depth `P.natDegree`. -/
def IsVirtualRootsList (P : R[X]) (xs : List R) : Prop :=
  IsVirtualRootsListAux P.natDegree P xs

omit [IsStrictOrderedRing R] in
/-- `IsVirtualRootsListAux` always implies `xs.length = P.natDegree`. -/
lemma IsVirtualRootsListAux.length_eq : ∀ {n : ℕ} {P : R[X]} {xs : List R},
    IsVirtualRootsListAux n P xs → xs.length = P.natDegree
  | 0, _, _, h => h.1
  | _ + 1, _, _, h => h.1

omit [IsStrictOrderedRing R] in
/-- `IsVirtualRootsListAux` always implies `xs` is sorted. -/
lemma IsVirtualRootsListAux.sorted : ∀ {n : ℕ} {P : R[X]} {xs : List R},
    IsVirtualRootsListAux n P xs → xs.Pairwise (· ≤ ·)
  | 0, _, _, h => h.2.1
  | _ + 1, _, _, h => h.2.1

omit [IsStrictOrderedRing R] in
/-- `IsVirtualRootsListAux` always implies `P` has constant sign on gaps. -/
lemma IsVirtualRootsListAux.sign_const : ∀ {n : ℕ} {P : R[X]} {xs : List R},
    IsVirtualRootsListAux n P xs → SignConstantOnGaps P xs
  | 0, _, _, h => h.2.2
  | _ + 1, _, _, h => h.2.2.1

omit [IsStrictOrderedRing R] in
/-- Length of a virtual roots list equals `natDegree P`. -/
lemma IsVirtualRootsList.length_eq {P : R[X]} {xs : List R}
    (h : IsVirtualRootsList P xs) : xs.length = P.natDegree :=
  IsVirtualRootsListAux.length_eq h

omit [IsStrictOrderedRing R] in
/-- A virtual roots list is sorted. -/
lemma IsVirtualRootsList.sorted {P : R[X]} {xs : List R}
    (h : IsVirtualRootsList P xs) : xs.Pairwise (· ≤ ·) :=
  IsVirtualRootsListAux.sorted h

omit [IsStrictOrderedRing R] in
/-- `P` has constant sign on each gap between consecutive virtual roots. -/
lemma IsVirtualRootsList.sign_const {P : R[X]} {xs : List R}
    (h : IsVirtualRootsList P xs) : SignConstantOnGaps P xs :=
  IsVirtualRootsListAux.sign_const h

omit [IsStrictOrderedRing R] in
/-- Argmin witness clause extracted from `IsVirtualRootsListAux (n + 1)`. -/
lemma IsVirtualRootsListAux.argmin_wit_succ {n : ℕ} {P : R[X]} {xs : List R}
    (h : IsVirtualRootsListAux (n + 1) P xs) :
    xs = [] ∨
      ∃ ys : List R,
        IsVirtualRootsListAux n (derivative P) ys ∧
        Interlaced xs ys ∧
        ArgminPartition P xs ys :=
  h.2.2.2

/-! ### Elementary properties of `Interlaced` -/

omit [Field R] [IsStrictOrderedRing R] in
lemma Interlaced.length_succ : ∀ {xs ys : List R}, Interlaced xs ys →
    xs.length = ys.length + 1
  | [_], [], _ => rfl
  | x :: x' :: xs, y :: ys, h => by
    obtain ⟨_, _, hrec⟩ := h
    have := Interlaced.length_succ hrec
    simp [this]
  | [], _, h => absurd h (by cases ‹List R› <;> simp [Interlaced])
  | [_], _ :: _, h => absurd h (by simp [Interlaced])
  | _ :: _ :: _, [], h => absurd h (by simp [Interlaced])

omit [Field R] [IsStrictOrderedRing R] in
/-- If `xs` and `ys` are interlaced and `ys` is nondecreasing, then `xs` is
    nondecreasing. The interleaving inequalities `x_i ≤ y_i ≤ x_{i+1}` chain. -/
lemma Interlaced.pairwise_of_ys :
    ∀ {xs ys : List R}, Interlaced xs ys → ys.Pairwise (· ≤ ·) →
      xs.Pairwise (· ≤ ·)
  | [_], [], _, _ => by simp
  | x :: x' :: xs, [], h, _ => absurd h (by simp [Interlaced])
  | [x], _ :: _, h, _ => absurd h (by simp [Interlaced])
  | [], _, h, _ => absurd h (by cases ‹List R› <;> simp [Interlaced])
  | x :: x' :: xs, y :: ys, h, hys => by
    obtain ⟨hxy, hyx', hrec⟩ := h
    have hys_tail : ys.Pairwise (· ≤ ·) := hys.tail
    have hrec' := Interlaced.pairwise_of_ys hrec hys_tail
    -- xs' starts with x', and x ≤ y ≤ x', so x ≤ head. By pairwise_cons, done.
    rw [List.pairwise_cons]
    refine ⟨?_, hrec'⟩
    intro z hz
    have hxx' : x ≤ x' := le_trans hxy hyx'
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact hxx'
    · -- z ∈ xs. Since x' :: xs is pairwise, x' ≤ z.
      have : x' ≤ z := by
        have := (List.pairwise_cons.mp hrec').1 z hz'
        exact this
      exact le_trans hxx' this

/-! ### Base case: `natDegree P = 0` -/

omit [IsStrictOrderedRing R] in
/-- For a nonzero constant polynomial (`natDegree = 0`), the empty list is a
    valid virtual roots list: there are no roots, so the only "gap" is the full
    line, and a nonzero constant has constant sign everywhere. -/
lemma isVirtualRootsList_nil_of_natDegree_zero {P : R[X]} (hP : P.natDegree = 0)
    (hP0 : P ≠ 0) : IsVirtualRootsList P [] := by
  unfold IsVirtualRootsList
  rw [hP]
  refine ⟨?_, List.Pairwise.nil, ?_⟩
  · simp [hP]
  · intro x y _ _
    have hPC : P = C (P.coeff 0) := by
      have := eq_C_of_natDegree_le_zero (le_of_eq hP)
      simpa using this
    have hc0 : P.coeff 0 ≠ 0 := by
      intro h
      apply hP0
      rw [hPC, h, C_0]
    refine ⟨?_, ?_⟩
    · rw [hPC]; simpa using hc0
    · rw [hPC]; simp

omit [IsStrictOrderedRing R] in
lemma exists_virtualRootsList_of_natDegree_zero {P : R[X]} (hP : P.natDegree = 0)
    (hP0 : P ≠ 0) : ∃ roots : List R, IsVirtualRootsList P roots :=
  ⟨[], isVirtualRootsList_nil_of_natDegree_zero hP hP0⟩

/-! ### Monotonicity on half-infinite intervals

BPR Corollary 2.24 gives strict monotonicity on `Icc a b` from `P' > 0` on
`Ioo a b`. For the inductive construction of virtual roots we also need
the analogues on `Iic b` and `Ici a`, since `I_1` and `I_p` are half-infinite.
-/

/-- If `P' > 0` on `(-∞, b)`, then `P` is strictly increasing on `(-∞, b]`. -/
lemma strictMonoOn_of_deriv_pos_Iic (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {b : R} (hP' : ∀ x ∈ Set.Iio b, 0 < (derivative P).eval x) :
    StrictMonoOn (fun x => P.eval x) (Set.Iic b) := by
  intro x hx y hy hxy
  have hyb : y ≤ b := hy
  have hx1y : x - 1 < y := by
    have : x < y := hxy
    linarith
  have hder : ∀ z ∈ Set.Ioo (x - 1) y, 0 < (derivative P).eval z := by
    intro z ⟨_, hzy⟩
    exact hP' z (lt_of_lt_of_le hzy hyb)
  have hmono := corollary_2_24_increasing hIVP P hx1y hder
  exact hmono ⟨by linarith, hxy.le⟩ ⟨hx1y.le, le_refl y⟩ hxy

/-- If `P' < 0` on `(-∞, b)`, then `P` is strictly decreasing on `(-∞, b]`. -/
lemma strictAntiOn_of_deriv_neg_Iic (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {b : R} (hP' : ∀ x ∈ Set.Iio b, (derivative P).eval x < 0) :
    StrictAntiOn (fun x => P.eval x) (Set.Iic b) := by
  intro x hx y hy hxy
  have hyb : y ≤ b := hy
  have hx1y : x - 1 < y := by
    have : x < y := hxy
    linarith
  have hder : ∀ z ∈ Set.Ioo (x - 1) y, (derivative P).eval z < 0 := by
    intro z ⟨_, hzy⟩
    exact hP' z (lt_of_lt_of_le hzy hyb)
  have hanti := corollary_2_24_decreasing hIVP P hx1y hder
  exact hanti ⟨by linarith, hxy.le⟩ ⟨hx1y.le, le_refl y⟩ hxy

/-- If `P' > 0` on `(a, +∞)`, then `P` is strictly increasing on `[a, +∞)`. -/
lemma strictMonoOn_of_deriv_pos_Ici (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a : R} (hP' : ∀ x ∈ Set.Ioi a, 0 < (derivative P).eval x) :
    StrictMonoOn (fun x => P.eval x) (Set.Ici a) := by
  intro x hx y hy hxy
  have hax : a ≤ x := hx
  have hxy1 : x < y + 1 := by
    have : x < y := hxy
    linarith
  have hder : ∀ z ∈ Set.Ioo x (y + 1), 0 < (derivative P).eval z := by
    intro z ⟨hxz, _⟩
    exact hP' z (lt_of_le_of_lt hax hxz)
  have hmono := corollary_2_24_increasing hIVP P hxy1 hder
  exact hmono ⟨le_refl x, by linarith⟩ ⟨hxy.le, by linarith⟩ hxy

/-- If `P' < 0` on `(a, +∞)`, then `P` is strictly decreasing on `[a, +∞)`. -/
lemma strictAntiOn_of_deriv_neg_Ici (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a : R} (hP' : ∀ x ∈ Set.Ioi a, (derivative P).eval x < 0) :
    StrictAntiOn (fun x => P.eval x) (Set.Ici a) := by
  intro x hx y hy hxy
  have hax : a ≤ x := hx
  have hxy1 : x < y + 1 := by
    have : x < y := hxy
    linarith
  have hder : ∀ z ∈ Set.Ioo x (y + 1), (derivative P).eval z < 0 := by
    intro z ⟨hxz, _⟩
    exact hP' z (lt_of_le_of_lt hax hxz)
  have hanti := corollary_2_24_decreasing hIVP P hxy1 hder
  exact hanti ⟨le_refl x, by linarith⟩ ⟨hxy.le, by linarith⟩ hxy

/-- If `P' > 0` everywhere, then `P` is strictly increasing. -/
lemma strictMono_of_deriv_pos (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP' : ∀ x : R, 0 < (derivative P).eval x) :
    StrictMono (fun x => P.eval x) := by
  intro x y hxy
  have hmono : StrictMonoOn (fun x => P.eval x) (Set.Ici (x - 1)) :=
    strictMonoOn_of_deriv_pos_Ici hIVP (fun z _ => hP' z)
  exact hmono (show x - 1 ≤ x by linarith) (show x - 1 ≤ y by linarith) hxy

/-- If `P' < 0` everywhere, then `P` is strictly decreasing. -/
lemma strictAnti_of_deriv_neg (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP' : ∀ x : R, (derivative P).eval x < 0) :
    StrictAnti (fun x => P.eval x) := by
  intro x y hxy
  have hanti : StrictAntiOn (fun x => P.eval x) (Set.Ici (x - 1)) :=
    strictAntiOn_of_deriv_neg_Ici hIVP (fun z _ => hP' z)
  exact hanti (show x - 1 ≤ x by linarith) (show x - 1 ≤ y by linarith) hxy

/-! ### Root existence and uniqueness on a strictly monotonic interval

If `P` is strictly monotonic on an interval `S`, it has at most one root in `S`.
Combined with IVP, on a closed interval where `P` changes sign, there is exactly
one root. This is the key tool for locating `x_i` as a root in `I_i`.
-/

omit [IsStrictOrderedRing R] in
/-- A strictly monotonic function has at most one root: any two points where
    `P.eval` vanishes must be equal. -/
lemma uniqueRoot_of_strictMonoOn {P : R[X]} {S : Set R}
    (hmono : StrictMonoOn (fun x => P.eval x) S)
    {x y : R} (hxS : x ∈ S) (hyS : y ∈ S)
    (hx : P.eval x = 0) (hy : P.eval y = 0) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have := hmono hxS hyS h; simp [hx, hy] at this
  · exact h
  · have := hmono hyS hxS h; simp [hx, hy] at this

omit [IsStrictOrderedRing R] in
/-- Strictly antitonic version of `uniqueRoot_of_strictMonoOn`. -/
lemma uniqueRoot_of_strictAntiOn {P : R[X]} {S : Set R}
    (hanti : StrictAntiOn (fun x => P.eval x) S)
    {x y : R} (hxS : x ∈ S) (hyS : y ∈ S)
    (hx : P.eval x = 0) (hy : P.eval y = 0) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have := hanti hxS hyS h; simp [hx, hy] at this
  · exact h
  · have := hanti hyS hxS h; simp [hx, hy] at this

/-- If `P` is strictly monotonic on `[a, b]` and `P.eval a * P.eval b < 0`,
    then there is a unique `c ∈ (a, b)` with `P.eval c = 0`. -/
lemma exists_unique_root_of_strictMonoOn_Icc (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a < b)
    (hmono : StrictMonoOn (fun x => P.eval x) (Set.Icc a b))
    (hsign : P.eval a * P.eval b < 0) :
    ∃! c : R, c ∈ Set.Ioo a b ∧ P.eval c = 0 := by
  obtain ⟨c, hac, hcb, hPc⟩ := hIVP P a b hab hsign
  refine ⟨c, ⟨⟨hac, hcb⟩, hPc⟩, ?_⟩
  rintro c' ⟨⟨hac', hc'b⟩, hPc'⟩
  have hcS : c ∈ Set.Icc a b := ⟨hac.le, hcb.le⟩
  have hc'S : c' ∈ Set.Icc a b := ⟨hac'.le, hc'b.le⟩
  exact uniqueRoot_of_strictMonoOn hmono hc'S hcS hPc' hPc

/-- Strictly antitonic version: on `[a, b]` with `P(a) * P(b) < 0` there is a
    unique root in `(a, b)`. -/
lemma exists_unique_root_of_strictAntiOn_Icc (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a < b)
    (hanti : StrictAntiOn (fun x => P.eval x) (Set.Icc a b))
    (hsign : P.eval a * P.eval b < 0) :
    ∃! c : R, c ∈ Set.Ioo a b ∧ P.eval c = 0 := by
  obtain ⟨c, hac, hcb, hPc⟩ := hIVP P a b hab hsign
  refine ⟨c, ⟨⟨hac, hcb⟩, hPc⟩, ?_⟩
  rintro c' ⟨⟨hac', hc'b⟩, hPc'⟩
  have hcS : c ∈ Set.Icc a b := ⟨hac.le, hcb.le⟩
  have hc'S : c' ∈ Set.Icc a b := ⟨hac'.le, hc'b.le⟩
  exact uniqueRoot_of_strictAntiOn hanti hc'S hcS hPc' hPc

/-! ### Sign behaviour between consecutive roots under monotonicity

If `P` is strict-mono on an interval and no root lies in a subinterval, then
`P` has constant nonzero sign there. This will be used to characterise the
sign of `P` on the open intervals between consecutive virtual roots.
-/

omit [IsStrictOrderedRing R] in
/-- If `P` is strictly increasing on `S` and `P(x) > 0` at some `x ∈ S`, then
    `P > 0` on every `z ∈ S` with `x ≤ z`. -/
lemma pos_of_strictMonoOn_of_pos_left {P : R[X]} {S : Set R}
    (hmono : StrictMonoOn (fun x => P.eval x) S) {x : R}
    (hxS : x ∈ S) (hx : 0 < P.eval x) :
    ∀ z ∈ S, x ≤ z → 0 < P.eval z := by
  intro z hzS hxz
  rcases eq_or_lt_of_le hxz with rfl | hxz'
  · exact hx
  · exact lt_trans hx (hmono hxS hzS hxz')

omit [IsStrictOrderedRing R] in
/-- Dual: if `P` strict-mono on `S` and `P(x) < 0` at `x ∈ S`, then `P < 0` on
    all `z ∈ S` with `z ≤ x`. -/
lemma neg_of_strictMonoOn_of_neg_right {P : R[X]} {S : Set R}
    (hmono : StrictMonoOn (fun x => P.eval x) S) {x : R}
    (hxS : x ∈ S) (hx : P.eval x < 0) :
    ∀ z ∈ S, z ≤ x → P.eval z < 0 := by
  intro z hzS hzx
  rcases eq_or_lt_of_le hzx with rfl | hzx'
  · exact hx
  · exact lt_trans (hmono hzS hxS hzx') hx

omit [IsStrictOrderedRing R] in
/-- Strict-anti version: if `P` strict-anti on `S` and `P(x) > 0`, then `P > 0`
    on `z ∈ S` with `z ≤ x`. -/
lemma pos_of_strictAntiOn_of_pos_right {P : R[X]} {S : Set R}
    (hanti : StrictAntiOn (fun x => P.eval x) S) {x : R}
    (hxS : x ∈ S) (hx : 0 < P.eval x) :
    ∀ z ∈ S, z ≤ x → 0 < P.eval z := by
  intro z hzS hzx
  rcases eq_or_lt_of_le hzx with rfl | hzx'
  · exact hx
  · exact lt_trans hx (hanti hzS hxS hzx')

omit [IsStrictOrderedRing R] in
/-- Strict-anti version: if `P` strict-anti on `S` and `P(x) < 0`, then `P < 0`
    on `z ∈ S` with `x ≤ z`. -/
lemma neg_of_strictAntiOn_of_neg_left {P : R[X]} {S : Set R}
    (hanti : StrictAntiOn (fun x => P.eval x) S) {x : R}
    (hxS : x ∈ S) (hx : P.eval x < 0) :
    ∀ z ∈ S, x ≤ z → P.eval z < 0 := by
  intro z hzS hxz
  rcases eq_or_lt_of_le hxz with rfl | hxz'
  · exact hx
  · exact lt_trans (hanti hxS hzS hxz') hx

/-! ### Sign trichotomy on a strict-monotonic closed interval

On `[a, b]` with `P` strict-mono, either `P(a) ≤ 0 ≤ P(b)` (or the dual for
strict-anti) — in which case there is a unique root — or `P` has constant
strict sign on the interval. -/

/-- Strict-monotonic trichotomy: on `[a, b]` (`a ≤ b`) either `P` has a root or
    a fixed strict sign on the interval. -/
lemma strictMonoOn_Icc_sign_trichotomy (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a ≤ b)
    (hmono : StrictMonoOn (fun x => P.eval x) (Set.Icc a b)) :
    (∃ c ∈ Set.Icc a b, P.eval c = 0) ∨
    (∀ x ∈ Set.Icc a b, 0 < P.eval x) ∨
    (∀ x ∈ Set.Icc a b, P.eval x < 0) := by
  rcases lt_trichotomy (P.eval a) 0 with hPa | hPa | hPa
  · -- P(a) < 0
    rcases lt_trichotomy (P.eval b) 0 with hPb | hPb | hPb
    · -- P(b) < 0: P < 0 on [a, b] by neg_of_strictMonoOn_of_neg_right at b
      right; right
      intro x hx
      exact neg_of_strictMonoOn_of_neg_right hmono (Set.right_mem_Icc.mpr hab) hPb x hx hx.2
    · -- P(b) = 0: b is the root
      left; exact ⟨b, Set.right_mem_Icc.mpr hab, hPb⟩
    · -- P(a) < 0 < P(b): IVP gives a root
      left
      rcases eq_or_lt_of_le hab with rfl | hab'
      · -- a = b: can't have both P(a) < 0 and P(b) > 0
        exact absurd (hPa.trans hPb) (lt_irrefl _)
      · obtain ⟨c, hac, hcb, hPc⟩ := hIVP P a b hab' (mul_neg_of_neg_of_pos hPa hPb)
        exact ⟨c, ⟨hac.le, hcb.le⟩, hPc⟩
  · -- P(a) = 0: a is the root
    left; exact ⟨a, Set.left_mem_Icc.mpr hab, hPa⟩
  · -- P(a) > 0
    rcases lt_trichotomy (P.eval b) 0 with hPb | hPb | hPb
    · -- P(a) > 0 > P(b): IVP gives a root
      left
      rcases eq_or_lt_of_le hab with rfl | hab'
      · exact absurd (hPb.trans hPa) (lt_irrefl _)
      · obtain ⟨c, hac, hcb, hPc⟩ := hIVP P a b hab' (mul_neg_of_pos_of_neg hPa hPb)
        exact ⟨c, ⟨hac.le, hcb.le⟩, hPc⟩
    · left; exact ⟨b, Set.right_mem_Icc.mpr hab, hPb⟩
    · -- P(a) > 0, P(b) > 0: P > 0 on [a, b] by pos_of_strictMonoOn_of_pos_left at a
      right; left
      intro x hx
      exact pos_of_strictMonoOn_of_pos_left hmono (Set.left_mem_Icc.mpr hab) hPa x hx hx.1

/-- Strict-antitonic trichotomy: on `[a, b]` either `P` has a root or a fixed
    strict sign on the interval. -/
lemma strictAntiOn_Icc_sign_trichotomy (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a ≤ b)
    (hanti : StrictAntiOn (fun x => P.eval x) (Set.Icc a b)) :
    (∃ c ∈ Set.Icc a b, P.eval c = 0) ∨
    (∀ x ∈ Set.Icc a b, 0 < P.eval x) ∨
    (∀ x ∈ Set.Icc a b, P.eval x < 0) := by
  rcases lt_trichotomy (P.eval a) 0 with hPa | hPa | hPa
  · rcases lt_trichotomy (P.eval b) 0 with hPb | hPb | hPb
    · -- P(a) < 0, P(b) < 0: by neg_of_strictAntiOn_of_neg_left at a
      right; right
      intro x hx
      exact neg_of_strictAntiOn_of_neg_left hanti (Set.left_mem_Icc.mpr hab) hPa x hx hx.1
    · left; exact ⟨b, Set.right_mem_Icc.mpr hab, hPb⟩
    · -- P(a) < 0 < P(b) but anti: P is decreasing so this shouldn't occur if a < b
      rcases eq_or_lt_of_le hab with rfl | hab'
      · exact absurd (hPa.trans hPb) (lt_irrefl _)
      · -- P(a) < P(b) but hanti says P(b) < P(a) — contradiction
        have := hanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab'
        exact absurd this (by linarith)
  · left; exact ⟨a, Set.left_mem_Icc.mpr hab, hPa⟩
  · rcases lt_trichotomy (P.eval b) 0 with hPb | hPb | hPb
    · -- P(a) > 0 > P(b) and anti: OK, P decreasing. IVP gives root.
      left
      rcases eq_or_lt_of_le hab with rfl | hab'
      · exact absurd (hPb.trans hPa) (lt_irrefl _)
      · obtain ⟨c, hac, hcb, hPc⟩ := hIVP P a b hab' (mul_neg_of_pos_of_neg hPa hPb)
        exact ⟨c, ⟨hac.le, hcb.le⟩, hPc⟩
    · left; exact ⟨b, Set.right_mem_Icc.mpr hab, hPb⟩
    · -- P(a) > 0, P(b) > 0: by pos_of_strictAntiOn_of_pos_right at b
      right; left
      intro x hx
      exact pos_of_strictAntiOn_of_pos_right hanti (Set.right_mem_Icc.mpr hab) hPb x hx hx.2

/-! ### Argmin of `|P|` on a closed interval -/

/-- If `P` is strictly monotonic on `[a, b]`, then `|P|` attains a minimum on
    `[a, b]`. The witness is either a root of `P` (from IVP), the left
    endpoint (if `P > 0` throughout), or the right endpoint (if `P < 0`). -/
lemma exists_argmin_abs_strictMonoOn_Icc (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a ≤ b)
    (hmono : StrictMonoOn (fun x => P.eval x) (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b,
      (∀ y ∈ Set.Icc a b, |P.eval x| ≤ |P.eval y|) ∧
      (P.eval x = 0 ∨ x = a ∨ x = b) := by
  rcases strictMonoOn_Icc_sign_trichotomy hIVP hab hmono with
    ⟨c, hc, hPc⟩ | hpos | hneg
  · refine ⟨c, hc, ?_, Or.inl hPc⟩
    intro y _
    rw [hPc, abs_zero]
    exact abs_nonneg _
  · -- P > 0 on [a,b] and strict-mono: min |P| = min P = at a
    refine ⟨a, Set.left_mem_Icc.mpr hab, ?_, Or.inr (Or.inl rfl)⟩
    intro y hy
    have hPa : 0 < P.eval a := hpos a (Set.left_mem_Icc.mpr hab)
    have hPy : 0 < P.eval y := hpos y hy
    rw [abs_of_pos hPa, abs_of_pos hPy]
    exact hmono.monotoneOn (Set.left_mem_Icc.mpr hab) hy hy.1
  · -- P < 0 on [a,b] and strict-mono: min |P| = max P = at b
    refine ⟨b, Set.right_mem_Icc.mpr hab, ?_, Or.inr (Or.inr rfl)⟩
    intro y hy
    have hPb : P.eval b < 0 := hneg b (Set.right_mem_Icc.mpr hab)
    have hPy : P.eval y < 0 := hneg y hy
    rw [abs_of_neg hPb, abs_of_neg hPy, neg_le_neg_iff]
    exact hmono.monotoneOn hy (Set.right_mem_Icc.mpr hab) hy.2

/-- If `P` is strictly antitonic on `[a, b]`, then `|P|` attains a minimum on
    `[a, b]`. -/
lemma exists_argmin_abs_strictAntiOn_Icc (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a ≤ b)
    (hanti : StrictAntiOn (fun x => P.eval x) (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b,
      (∀ y ∈ Set.Icc a b, |P.eval x| ≤ |P.eval y|) ∧
      (P.eval x = 0 ∨ x = a ∨ x = b) := by
  rcases strictAntiOn_Icc_sign_trichotomy hIVP hab hanti with
    ⟨c, hc, hPc⟩ | hpos | hneg
  · refine ⟨c, hc, ?_, Or.inl hPc⟩
    intro y _
    rw [hPc, abs_zero]
    exact abs_nonneg _
  · -- P > 0 on [a,b] and strict-anti: min |P| = min P = at b
    refine ⟨b, Set.right_mem_Icc.mpr hab, ?_, Or.inr (Or.inr rfl)⟩
    intro y hy
    have hPb : 0 < P.eval b := hpos b (Set.right_mem_Icc.mpr hab)
    have hPy : 0 < P.eval y := hpos y hy
    rw [abs_of_pos hPb, abs_of_pos hPy]
    exact hanti.antitoneOn hy (Set.right_mem_Icc.mpr hab) hy.2
  · -- P < 0 on [a,b] and strict-anti: min |P| = max P = at a
    refine ⟨a, Set.left_mem_Icc.mpr hab, ?_, Or.inr (Or.inl rfl)⟩
    intro y hy
    have hPa : P.eval a < 0 := hneg a (Set.left_mem_Icc.mpr hab)
    have hPy : P.eval y < 0 := hneg y hy
    rw [abs_of_neg hPa, abs_of_neg hPy, neg_le_neg_iff]
    exact hanti.antitoneOn (Set.left_mem_Icc.mpr hab) hy hy.1

/-! ### Argmin of `|P|` on half-infinite intervals

These reductions take a far-endpoint bound as an *explicit hypothesis*
(`|P.eval c| ≤ |P.eval y|` for `y` beyond some threshold). That hypothesis is
furnished, in applications, by the polynomial asymptotic growth bound — built
separately. Decoupling it keeps the argmin search combinatorial. -/

/-- If `P` is strictly monotonic on `(−∞, c]` and eventually dominates
    `|P.eval c|` on the far left, then `|P|` attains a minimum on `Iic c`.
    The witness comes from the Icc argmin applied to `[N, c]` where `N` is
    the far-left threshold. -/
lemma exists_argmin_abs_strictMonoOn_Iic_of_bound
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {c : R}
    (hmono : StrictMonoOn (fun x => P.eval x) (Set.Iic c))
    (hbound : ∃ N ≤ c, ∀ y < N, |P.eval c| ≤ |P.eval y|) :
    ∃ x ∈ Set.Iic c, ∀ y ∈ Set.Iic c, |P.eval x| ≤ |P.eval y| := by
  obtain ⟨N, hNc, hN⟩ := hbound
  have hmono' : StrictMonoOn (fun x => P.eval x) (Set.Icc N c) :=
    hmono.mono (fun _ h => h.2)
  obtain ⟨x, hx_mem, hx_min, _⟩ := exists_argmin_abs_strictMonoOn_Icc hIVP hNc hmono'
  refine ⟨x, hx_mem.2, ?_⟩
  intro y hy
  by_cases hyN : N ≤ y
  · exact hx_min y ⟨hyN, hy⟩
  · have hyN' : y < N := lt_of_not_ge hyN
    calc |P.eval x|
        ≤ |P.eval c| := hx_min c (Set.right_mem_Icc.mpr hNc)
      _ ≤ |P.eval y| := hN y hyN'

/-- Strict-antitonic dual of `exists_argmin_abs_strictMonoOn_Iic_of_bound`. -/
lemma exists_argmin_abs_strictAntiOn_Iic_of_bound
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {c : R}
    (hanti : StrictAntiOn (fun x => P.eval x) (Set.Iic c))
    (hbound : ∃ N ≤ c, ∀ y < N, |P.eval c| ≤ |P.eval y|) :
    ∃ x ∈ Set.Iic c, ∀ y ∈ Set.Iic c, |P.eval x| ≤ |P.eval y| := by
  obtain ⟨N, hNc, hN⟩ := hbound
  have hanti' : StrictAntiOn (fun x => P.eval x) (Set.Icc N c) :=
    hanti.mono (fun _ h => h.2)
  obtain ⟨x, hx_mem, hx_min, _⟩ := exists_argmin_abs_strictAntiOn_Icc hIVP hNc hanti'
  refine ⟨x, hx_mem.2, ?_⟩
  intro y hy
  by_cases hyN : N ≤ y
  · exact hx_min y ⟨hyN, hy⟩
  · have hyN' : y < N := lt_of_not_ge hyN
    calc |P.eval x|
        ≤ |P.eval c| := hx_min c (Set.right_mem_Icc.mpr hNc)
      _ ≤ |P.eval y| := hN y hyN'

/-- If `P` is strictly monotonic on `[c, +∞)` and eventually dominates
    `|P.eval c|` on the far right, then `|P|` attains a minimum on `Ici c`. -/
lemma exists_argmin_abs_strictMonoOn_Ici_of_bound
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {c : R}
    (hmono : StrictMonoOn (fun x => P.eval x) (Set.Ici c))
    (hbound : ∃ N ≥ c, ∀ y > N, |P.eval c| ≤ |P.eval y|) :
    ∃ x ∈ Set.Ici c, ∀ y ∈ Set.Ici c, |P.eval x| ≤ |P.eval y| := by
  obtain ⟨N, hcN, hN⟩ := hbound
  have hmono' : StrictMonoOn (fun x => P.eval x) (Set.Icc c N) :=
    hmono.mono (fun _ h => h.1)
  obtain ⟨x, hx_mem, hx_min, _⟩ := exists_argmin_abs_strictMonoOn_Icc hIVP hcN hmono'
  refine ⟨x, hx_mem.1, ?_⟩
  intro y hy
  by_cases hyN : y ≤ N
  · exact hx_min y ⟨hy, hyN⟩
  · have hyN' : N < y := lt_of_not_ge hyN
    calc |P.eval x|
        ≤ |P.eval c| := hx_min c (Set.left_mem_Icc.mpr hcN)
      _ ≤ |P.eval y| := hN y hyN'

/-- Strict-antitonic dual of `exists_argmin_abs_strictMonoOn_Ici_of_bound`. -/
lemma exists_argmin_abs_strictAntiOn_Ici_of_bound
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {c : R}
    (hanti : StrictAntiOn (fun x => P.eval x) (Set.Ici c))
    (hbound : ∃ N ≥ c, ∀ y > N, |P.eval c| ≤ |P.eval y|) :
    ∃ x ∈ Set.Ici c, ∀ y ∈ Set.Ici c, |P.eval x| ≤ |P.eval y| := by
  obtain ⟨N, hcN, hN⟩ := hbound
  have hanti' : StrictAntiOn (fun x => P.eval x) (Set.Icc c N) :=
    hanti.mono (fun _ h => h.1)
  obtain ⟨x, hx_mem, hx_min, _⟩ := exists_argmin_abs_strictAntiOn_Icc hIVP hcN hanti'
  refine ⟨x, hx_mem.1, ?_⟩
  intro y hy
  by_cases hyN : y ≤ N
  · exact hx_min y ⟨hy, hyN⟩
  · have hyN' : N < y := lt_of_not_ge hyN
    calc |P.eval x|
        ≤ |P.eval c| := hx_min c (Set.left_mem_Icc.mpr hcN)
      _ ≤ |P.eval y| := hN y hyN'

/-! ### Polynomial magnitude growth at infinity

For a polynomial of positive degree, `|P(y)|` exceeds any fixed bound once
`|y|` is large enough. Concretely, for any target `B`, `|P(y)| ≥ B` for all
`y` outside some bounded window. This is the quantitative counterpart of
`HasSignAtNegInfty` / `HasSignAtPosInfty` and furnishes the asymptotic input
for the half-infinite argmin lemmas. -/

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Decompose `P(y)` into its leading term and tail. -/
private lemma eval_eq_lead_add_tail (P : R[X]) (y : R) :
    P.eval y = P.leadingCoeff * y ^ P.natDegree +
      ∑ i ∈ Finset.range P.natDegree, P.coeff i * y ^ i := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, add_comm]
  rfl

/-- The tail sum is bounded by `S · |y|^{n-1}` when `|y| ≥ 1`. -/
private lemma abs_tail_le_of_abs_ge_one (P : R[X])
    {y : R} (hy : 1 ≤ |y|) :
    |∑ i ∈ Finset.range P.natDegree, P.coeff i * y ^ i| ≤
      (∑ i ∈ Finset.range P.natDegree, |P.coeff i|) * |y| ^ (P.natDegree - 1) := by
  calc |∑ i ∈ Finset.range P.natDegree, P.coeff i * y ^ i|
      ≤ ∑ i ∈ Finset.range P.natDegree, |P.coeff i * y ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range P.natDegree, |P.coeff i| * |y| ^ i := by
        congr 1; ext i; rw [abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range P.natDegree, |P.coeff i| * |y| ^ (P.natDegree - 1) := by
        apply Finset.sum_le_sum; intro i hi
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hy (Nat.le_pred_of_lt (Finset.mem_range.mp hi)))
          (abs_nonneg _)
    _ = (∑ i ∈ Finset.range P.natDegree, |P.coeff i|) * |y| ^ (P.natDegree - 1) :=
        (Finset.sum_mul ..).symm

/-- For polynomials of positive degree, `|P(y)|` grows without bound as `|y|`
    does. Quantitatively, given any target `B`, we produce a threshold `K > 0`
    such that `|y| > K` implies `|P(y)| ≥ B`. -/
lemma exists_abs_eval_ge_of_natDegree_pos (P : R[X]) (hdeg : 0 < P.natDegree)
    (B : R) : ∃ K : R, 0 < K ∧ ∀ y : R, K < |y| → B ≤ |P.eval y| := by
  have hP : P ≠ 0 := fun h => by simp [h] at hdeg
  have ha_ne : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have ha_abs_pos : 0 < |P.leadingCoeff| := abs_pos.mpr ha_ne
  set S := ∑ i ∈ Finset.range P.natDegree, |P.coeff i| with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set K := max 1 (max (2 * S / |P.leadingCoeff|) (2 * (|B| + 1) / |P.leadingCoeff|))
    with hK_def
  have hK_ge_1 : (1 : R) ≤ K := le_max_left _ _
  have hK_ge_2S : 2 * S / |P.leadingCoeff| ≤ K :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hK_ge_2B : 2 * (|B| + 1) / |P.leadingCoeff| ≤ K :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK_ge_1
  refine ⟨K, hK_pos, ?_⟩
  intro y hy
  have hy_abs_ge_1 : 1 ≤ |y| := le_of_lt (lt_of_le_of_lt hK_ge_1 hy)
  have hy_abs_pos : 0 < |y| := lt_of_lt_of_le zero_lt_one hy_abs_ge_1
  -- |a| * |y| ≥ 2 * S
  have hay_ge_2S : 2 * S ≤ |P.leadingCoeff| * |y| := by
    have h1 : 2 * S / |P.leadingCoeff| < |y| := lt_of_le_of_lt hK_ge_2S hy
    rw [div_lt_iff₀ ha_abs_pos] at h1
    linarith
  -- |a| * |y| ≥ 2 * (|B| + 1)
  have hay_ge_2B : 2 * (|B| + 1) ≤ |P.leadingCoeff| * |y| := by
    have h1 : 2 * (|B| + 1) / |P.leadingCoeff| < |y| := lt_of_le_of_lt hK_ge_2B hy
    rw [div_lt_iff₀ ha_abs_pos] at h1
    linarith
  -- Decomposition and triangle inequality
  have hdecomp := eval_eq_lead_add_tail P y
  set tail := ∑ i ∈ Finset.range P.natDegree, P.coeff i * y ^ i with htail_def
  have hdecomp' : P.eval y = P.leadingCoeff * y ^ P.natDegree + tail := hdecomp
  have htriangle : |P.leadingCoeff * y ^ P.natDegree| ≤ |P.eval y| + |tail| := by
    have : P.leadingCoeff * y ^ P.natDegree = P.eval y - tail := by linarith
    rw [this]
    exact abs_sub _ _
  have habs_lead : |P.leadingCoeff * y ^ P.natDegree|
      = |P.leadingCoeff| * |y| ^ P.natDegree := by rw [abs_mul, abs_pow]
  -- Tail bound: |tail| ≤ S * |y|^{n-1}
  have htail_bound : |tail| ≤ S * |y| ^ (P.natDegree - 1) :=
    abs_tail_le_of_abs_ge_one P hy_abs_ge_1
  -- |y|^n = |y|^{n-1} * |y|
  have hn_eq : P.natDegree = (P.natDegree - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos hdeg).symm
  have hpow_split : |y| ^ P.natDegree = |y| ^ (P.natDegree - 1) * |y| := by
    conv_lhs => rw [hn_eq, pow_succ]
  have hpow_pos : 0 < |y| ^ (P.natDegree - 1) := pow_pos hy_abs_pos _
  have hpow_nm1_ge_1 : 1 ≤ |y| ^ (P.natDegree - 1) := one_le_pow₀ hy_abs_ge_1
  -- S * |y|^{n-1} ≤ |a| * |y|^n / 2
  have htail_small : S * |y| ^ (P.natDegree - 1)
      ≤ |P.leadingCoeff| * |y| ^ P.natDegree / 2 := by
    rw [hpow_split]
    have : 2 * (S * |y| ^ (P.natDegree - 1))
        ≤ |P.leadingCoeff| * |y| * |y| ^ (P.natDegree - 1) := by
      have : (2 * S) * |y| ^ (P.natDegree - 1)
          ≤ (|P.leadingCoeff| * |y|) * |y| ^ (P.natDegree - 1) :=
        mul_le_mul_of_nonneg_right hay_ge_2S (le_of_lt hpow_pos)
      linarith
    have hrearrange :
        |P.leadingCoeff| * (|y| ^ (P.natDegree - 1) * |y|)
        = |P.leadingCoeff| * |y| * |y| ^ (P.natDegree - 1) := by ring
    linarith [hrearrange]
  -- |P(y)| ≥ |a| * |y|^n / 2
  have hP_ge_half : |P.leadingCoeff| * |y| ^ P.natDegree / 2 ≤ |P.eval y| := by
    have h1 : |P.leadingCoeff| * |y| ^ P.natDegree ≤ |P.eval y| + |tail| := by
      rw [← habs_lead]; exact htriangle
    have h2 : |tail| ≤ |P.leadingCoeff| * |y| ^ P.natDegree / 2 :=
      le_trans htail_bound htail_small
    linarith
  -- |a| * |y|^n / 2 ≥ B
  have hhalf_ge_B : B ≤ |P.leadingCoeff| * |y| ^ P.natDegree / 2 := by
    -- |y|^n ≥ |y| (since |y| ≥ 1 and n ≥ 1)
    have hy_le_pow : |y| ≤ |y| ^ P.natDegree := by
      calc |y| = |y| * 1 := (mul_one _).symm
        _ ≤ |y| * |y| ^ (P.natDegree - 1) :=
            mul_le_mul_of_nonneg_left hpow_nm1_ge_1 (le_of_lt hy_abs_pos)
        _ = |y| ^ (P.natDegree - 1) * |y| := by ring
        _ = |y| ^ P.natDegree := by rw [← hpow_split]
    have h1 : |P.leadingCoeff| * |y| ≤ |P.leadingCoeff| * |y| ^ P.natDegree :=
      mul_le_mul_of_nonneg_left hy_le_pow (le_of_lt ha_abs_pos)
    have h2 : 2 * (|B| + 1) ≤ |P.leadingCoeff| * |y| ^ P.natDegree :=
      le_trans hay_ge_2B h1
    have h3 : B ≤ |B| := le_abs_self B
    linarith
  linarith

/-- For polynomials of positive degree, given any `c`, there is a threshold
    `N ≤ c` such that `|P(c)| ≤ |P(y)|` for every `y < N`. This is the
    asymptotic hypothesis consumed by the Iic argmin lemma. -/
lemma exists_bound_far_left (P : R[X]) (hdeg : 0 < P.natDegree) (c : R) :
    ∃ N ≤ c, ∀ y < N, |P.eval c| ≤ |P.eval y| := by
  obtain ⟨K, hK_pos, hK⟩ := exists_abs_eval_ge_of_natDegree_pos P hdeg |P.eval c|
  refine ⟨min (-K - 1) c, min_le_right _ _, ?_⟩
  intro y hy
  have hy_lt_negK : y < -K := lt_of_lt_of_le hy (le_trans (min_le_left _ _) (by linarith))
  have hy_neg : y < 0 := lt_of_lt_of_le hy_lt_negK (by linarith)
  have hy_abs : K < |y| := by rw [abs_of_neg hy_neg]; linarith
  exact hK y hy_abs

/-- Dual of `exists_bound_far_left`: `|P(c)| ≤ |P(y)|` for `y` far to the right. -/
lemma exists_bound_far_right (P : R[X]) (hdeg : 0 < P.natDegree) (c : R) :
    ∃ N ≥ c, ∀ y > N, |P.eval c| ≤ |P.eval y| := by
  obtain ⟨K, hK_pos, hK⟩ := exists_abs_eval_ge_of_natDegree_pos P hdeg |P.eval c|
  refine ⟨max (K + 1) c, le_max_right _ _, ?_⟩
  intro y hy
  have hy_gt_K : K < y := lt_of_le_of_lt (le_trans (by linarith) (le_max_left _ _)) hy
  have hy_pos : 0 < y := lt_of_le_of_lt (le_of_lt hK_pos) hy_gt_K
  have hy_abs : K < |y| := by rw [abs_of_pos hy_pos]; exact hy_gt_K
  exact hK y hy_abs

/-! ### Hypothesis-free argmin on half-infinite intervals

Combine the argmin reductions with the polynomial asymptotic bound to get
argmin existence on `Iic c` and `Ici c` without a manually supplied far-endpoint
witness. Available for polynomials of positive degree (needed for growth). -/

/-- Argmin of `|P|` exists on `Iic c` for `P` strict-mono there (positive degree).
    The witness is either a root of `P` (from a far-left sign change detected via
    pos-degree asymptotics) or the right endpoint `c` (when `P(c) ≤ 0`). -/
lemma exists_argmin_abs_strictMonoOn_Iic
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdeg : 0 < P.natDegree) {c : R}
    (hmono : StrictMonoOn (fun x => P.eval x) (Set.Iic c)) :
    ∃ x ∈ Set.Iic c, (∀ y ∈ Set.Iic c, |P.eval x| ≤ |P.eval y|) ∧
      (P.eval x = 0 ∨ x = c) := by
  rcases le_or_gt (P.eval c) 0 with hPc | hPc
  · -- P(c) ≤ 0: x = c is argmin (strict mono gives P(y) ≤ P(c) ≤ 0 on Iic c)
    refine ⟨c, le_refl c, ?_, ?_⟩
    · intro y hy
      have hPy_le : P.eval y ≤ P.eval c := hmono.monotoneOn hy (le_refl c) hy
      have hPy_nonpos : P.eval y ≤ 0 := le_trans hPy_le hPc
      rw [abs_of_nonpos hPy_nonpos, abs_of_nonpos hPc, neg_le_neg_iff]
      exact hPy_le
    · rcases eq_or_lt_of_le hPc with hPc0 | _
      · exact Or.inl hPc0
      · exact Or.inr rfl
  · -- P(c) > 0: asymptotic forces P(y₀) < 0 far left, IVT yields a root
    obtain ⟨K, hK_pos, hK⟩ :=
      exists_abs_eval_ge_of_natDegree_pos P hdeg (|P.eval c| + 1)
    set y₀ := min (c - 1) (-K - 1)
    have hy₀_lt_c : y₀ < c := by
      have : y₀ ≤ c - 1 := min_le_left _ _
      linarith
    have hy₀_le : y₀ ≤ -K - 1 := min_le_right _ _
    have hy₀_neg : y₀ < 0 := by linarith [hK_pos]
    have hy₀_abs : K < |y₀| := by rw [abs_of_neg hy₀_neg]; linarith
    have hPy₀_abs : |P.eval c| + 1 ≤ |P.eval y₀| := hK y₀ hy₀_abs
    have hPc_abs : |P.eval c| = P.eval c := abs_of_pos hPc
    have hPy₀_lt_Pc : P.eval y₀ < P.eval c := hmono hy₀_lt_c.le (le_refl c) hy₀_lt_c
    have hPy₀_neg : P.eval y₀ < 0 := by
      rcases le_or_gt (P.eval y₀) 0 with hle | hgt
      · rcases eq_or_lt_of_le hle with heq | hlt
        · exfalso; rw [heq, abs_zero, hPc_abs] at hPy₀_abs; linarith
        · exact hlt
      · exfalso; rw [abs_of_pos hgt, hPc_abs] at hPy₀_abs; linarith
    have hprod : P.eval y₀ * P.eval c < 0 := mul_neg_of_neg_of_pos hPy₀_neg hPc
    obtain ⟨r, _, hrc, hPr⟩ := hIVP P y₀ c hy₀_lt_c hprod
    refine ⟨r, hrc.le, ?_, Or.inl hPr⟩
    intro y _; rw [hPr, abs_zero]; exact abs_nonneg _

/-- Argmin of `|P|` exists on `Iic c` for `P` strict-anti there (positive degree). -/
lemma exists_argmin_abs_strictAntiOn_Iic
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdeg : 0 < P.natDegree) {c : R}
    (hanti : StrictAntiOn (fun x => P.eval x) (Set.Iic c)) :
    ∃ x ∈ Set.Iic c, (∀ y ∈ Set.Iic c, |P.eval x| ≤ |P.eval y|) ∧
      (P.eval x = 0 ∨ x = c) := by
  rcases le_or_gt 0 (P.eval c) with hPc | hPc
  · refine ⟨c, le_refl c, ?_, ?_⟩
    · intro y hy
      have hPy_ge : P.eval c ≤ P.eval y := hanti.antitoneOn hy (le_refl c) hy
      have hPy_nonneg : 0 ≤ P.eval y := le_trans hPc hPy_ge
      rw [abs_of_nonneg hPy_nonneg, abs_of_nonneg hPc]
      exact hPy_ge
    · rcases eq_or_lt_of_le hPc with hPc0 | _
      · exact Or.inl hPc0.symm
      · exact Or.inr rfl
  · obtain ⟨K, hK_pos, hK⟩ :=
      exists_abs_eval_ge_of_natDegree_pos P hdeg (|P.eval c| + 1)
    set y₀ := min (c - 1) (-K - 1)
    have hy₀_lt_c : y₀ < c := by
      have : y₀ ≤ c - 1 := min_le_left _ _
      linarith
    have hy₀_le : y₀ ≤ -K - 1 := min_le_right _ _
    have hy₀_neg : y₀ < 0 := by linarith [hK_pos]
    have hy₀_abs : K < |y₀| := by rw [abs_of_neg hy₀_neg]; linarith
    have hPy₀_abs : |P.eval c| + 1 ≤ |P.eval y₀| := hK y₀ hy₀_abs
    have hPc_abs : |P.eval c| = -P.eval c := abs_of_neg hPc
    have hPy₀_gt_Pc : P.eval c < P.eval y₀ := hanti hy₀_lt_c.le (le_refl c) hy₀_lt_c
    have hPy₀_pos : 0 < P.eval y₀ := by
      rcases le_or_gt (P.eval y₀) 0 with hle | hgt
      · exfalso; rw [abs_of_nonpos hle, hPc_abs] at hPy₀_abs; linarith
      · exact hgt
    have hprod : P.eval y₀ * P.eval c < 0 := mul_neg_of_pos_of_neg hPy₀_pos hPc
    obtain ⟨r, _, hrc, hPr⟩ := hIVP P y₀ c hy₀_lt_c hprod
    refine ⟨r, hrc.le, ?_, Or.inl hPr⟩
    intro y _; rw [hPr, abs_zero]; exact abs_nonneg _

/-- Argmin of `|P|` exists on `Ici c` for `P` strict-mono there (positive degree). -/
lemma exists_argmin_abs_strictMonoOn_Ici
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdeg : 0 < P.natDegree) {c : R}
    (hmono : StrictMonoOn (fun x => P.eval x) (Set.Ici c)) :
    ∃ x ∈ Set.Ici c, (∀ y ∈ Set.Ici c, |P.eval x| ≤ |P.eval y|) ∧
      (P.eval x = 0 ∨ x = c) := by
  rcases le_or_gt 0 (P.eval c) with hPc | hPc
  · refine ⟨c, le_refl c, ?_, ?_⟩
    · intro y hy
      have hPy_ge : P.eval c ≤ P.eval y := hmono.monotoneOn (le_refl c) hy hy
      have hPy_nonneg : 0 ≤ P.eval y := le_trans hPc hPy_ge
      rw [abs_of_nonneg hPy_nonneg, abs_of_nonneg hPc]
      exact hPy_ge
    · rcases eq_or_lt_of_le hPc with hPc0 | _
      · exact Or.inl hPc0.symm
      · exact Or.inr rfl
  · obtain ⟨K, hK_pos, hK⟩ :=
      exists_abs_eval_ge_of_natDegree_pos P hdeg (|P.eval c| + 1)
    set y₀ := max (c + 1) (K + 1)
    have hc_lt_y₀ : c < y₀ := by
      have : c + 1 ≤ y₀ := le_max_left _ _
      linarith
    have hK_lt_y₀ : K + 1 ≤ y₀ := le_max_right _ _
    have hy₀_pos : 0 < y₀ := by linarith [hK_pos]
    have hy₀_abs : K < |y₀| := by rw [abs_of_pos hy₀_pos]; linarith
    have hPy₀_abs : |P.eval c| + 1 ≤ |P.eval y₀| := hK y₀ hy₀_abs
    have hPc_abs : |P.eval c| = -P.eval c := abs_of_neg hPc
    have hPy₀_gt_Pc : P.eval c < P.eval y₀ := hmono (le_refl c) hc_lt_y₀.le hc_lt_y₀
    have hPy₀_pos : 0 < P.eval y₀ := by
      rcases le_or_gt (P.eval y₀) 0 with hle | hgt
      · exfalso; rw [abs_of_nonpos hle, hPc_abs] at hPy₀_abs; linarith
      · exact hgt
    have hprod : P.eval c * P.eval y₀ < 0 := mul_neg_of_neg_of_pos hPc hPy₀_pos
    obtain ⟨r, hcr, _, hPr⟩ := hIVP P c y₀ hc_lt_y₀ hprod
    refine ⟨r, hcr.le, ?_, Or.inl hPr⟩
    intro y _; rw [hPr, abs_zero]; exact abs_nonneg _

/-- Argmin of `|P|` exists on `Ici c` for `P` strict-anti there (positive degree). -/
lemma exists_argmin_abs_strictAntiOn_Ici
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdeg : 0 < P.natDegree) {c : R}
    (hanti : StrictAntiOn (fun x => P.eval x) (Set.Ici c)) :
    ∃ x ∈ Set.Ici c, (∀ y ∈ Set.Ici c, |P.eval x| ≤ |P.eval y|) ∧
      (P.eval x = 0 ∨ x = c) := by
  rcases le_or_gt (P.eval c) 0 with hPc | hPc
  · refine ⟨c, le_refl c, ?_, ?_⟩
    · intro y hy
      have hPy_le : P.eval y ≤ P.eval c := hanti.antitoneOn (le_refl c) hy hy
      have hPy_nonpos : P.eval y ≤ 0 := le_trans hPy_le hPc
      rw [abs_of_nonpos hPy_nonpos, abs_of_nonpos hPc, neg_le_neg_iff]
      exact hPy_le
    · rcases eq_or_lt_of_le hPc with hPc0 | _
      · exact Or.inl hPc0
      · exact Or.inr rfl
  · obtain ⟨K, hK_pos, hK⟩ :=
      exists_abs_eval_ge_of_natDegree_pos P hdeg (|P.eval c| + 1)
    set y₀ := max (c + 1) (K + 1)
    have hc_lt_y₀ : c < y₀ := by
      have : c + 1 ≤ y₀ := le_max_left _ _
      linarith
    have hK_lt_y₀ : K + 1 ≤ y₀ := le_max_right _ _
    have hy₀_pos : 0 < y₀ := by linarith [hK_pos]
    have hy₀_abs : K < |y₀| := by rw [abs_of_pos hy₀_pos]; linarith
    have hPy₀_abs : |P.eval c| + 1 ≤ |P.eval y₀| := hK y₀ hy₀_abs
    have hPc_abs : |P.eval c| = P.eval c := abs_of_pos hPc
    have hPy₀_lt_Pc : P.eval y₀ < P.eval c := hanti (le_refl c) hc_lt_y₀.le hc_lt_y₀
    have hPy₀_neg : P.eval y₀ < 0 := by
      rcases le_or_gt 0 (P.eval y₀) with hge | hlt
      · exfalso; rw [abs_of_nonneg hge, hPc_abs] at hPy₀_abs; linarith
      · exact hlt
    have hprod : P.eval c * P.eval y₀ < 0 := mul_neg_of_pos_of_neg hPc hPy₀_neg
    obtain ⟨r, hcr, _, hPr⟩ := hIVP P c y₀ hc_lt_y₀ hprod
    refine ⟨r, hcr.le, ?_, Or.inl hPr⟩
    intro y _; rw [hPr, abs_zero]; exact abs_nonneg _

/-! ### Root existence from sign change at `±∞`

If `P` has opposite nonzero signs at `−∞` and `+∞`, IVP produces a root. This
packages the sign-at-infty predicates together with IVP into a reusable lemma;
the linear case below invokes it via the leading-coefficient identities. -/

/-- If `P` is eventually negative at `−∞` and eventually positive at `+∞`, then
    `P` has a root. -/
lemma exists_root_of_sign_neg_pos_at_infty (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) (hneg : HasSignAtNegInfty P SignType.neg)
    (hpos : HasSignAtPosInfty P SignType.pos) :
    ∃ r, P.eval r = 0 := by
  obtain ⟨Mn, hMn⟩ := hneg
  obtain ⟨Mp, hMp⟩ := hpos
  set a := min Mn Mp - 1
  set b := max Mn Mp + 1
  have haMn : a < Mn := by
    have : min Mn Mp ≤ Mn := min_le_left _ _
    simp [a]; linarith
  have hMpb : Mp < b := by
    have : Mp ≤ max Mn Mp := le_max_right _ _
    simp [b]; linarith
  have hab : a < b := by
    have h1 : min Mn Mp ≤ max Mn Mp := min_le_max
    simp [a, b]; linarith
  have hPa_sign : SignType.sign (P.eval a) = SignType.neg := hMn a haMn
  have hPb_sign : SignType.sign (P.eval b) = SignType.pos := hMp b hMpb
  have hPa_neg : P.eval a < 0 := sign_eq_neg_one_iff.mp hPa_sign
  have hPb_pos : 0 < P.eval b := sign_eq_one_iff.mp hPb_sign
  have hprod : P.eval a * P.eval b < 0 := mul_neg_of_neg_of_pos hPa_neg hPb_pos
  obtain ⟨r, _, _, hPr⟩ := hIVP P a b hab hprod
  exact ⟨r, hPr⟩

/-- If `P` is eventually positive at `−∞` and eventually negative at `+∞`, then
    `P` has a root. -/
lemma exists_root_of_sign_pos_neg_at_infty (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) (hneg : HasSignAtNegInfty P SignType.pos)
    (hpos : HasSignAtPosInfty P SignType.neg) :
    ∃ r, P.eval r = 0 := by
  obtain ⟨Mn, hMn⟩ := hneg
  obtain ⟨Mp, hMp⟩ := hpos
  set a := min Mn Mp - 1
  set b := max Mn Mp + 1
  have haMn : a < Mn := by
    have : min Mn Mp ≤ Mn := min_le_left _ _
    simp [a]; linarith
  have hMpb : Mp < b := by
    have : Mp ≤ max Mn Mp := le_max_right _ _
    simp [b]; linarith
  have hab : a < b := by
    have h1 : min Mn Mp ≤ max Mn Mp := min_le_max
    simp [a, b]; linarith
  have hPa_sign : SignType.sign (P.eval a) = SignType.pos := hMn a haMn
  have hPb_sign : SignType.sign (P.eval b) = SignType.neg := hMp b hMpb
  have hPa_pos : 0 < P.eval a := sign_eq_one_iff.mp hPa_sign
  have hPb_neg : P.eval b < 0 := sign_eq_neg_one_iff.mp hPb_sign
  have hprod : P.eval a * P.eval b < 0 := mul_neg_of_pos_of_neg hPa_pos hPb_neg
  obtain ⟨r, _, _, hPr⟩ := hIVP P a b hab hprod
  exact ⟨r, hPr⟩

/-! ### Evaluation of the derivative of a linear polynomial

For `natDegree P = 1`, the derivative is the constant polynomial `C P.leadingCoeff`. -/

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- If `natDegree P = 1`, then `P.derivative` evaluates to `P.leadingCoeff`
    at every point. -/
lemma eval_derivative_of_natDegree_one {P : R[X]} (hdeg : P.natDegree = 1) (x : R) :
    (derivative P).eval x = P.leadingCoeff := by
  have hlt : (derivative P).natDegree < P.natDegree :=
    Polynomial.natDegree_derivative_lt (by rw [hdeg]; exact one_ne_zero)
  have hdle : (derivative P).natDegree = 0 := by
    rw [hdeg] at hlt; omega
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdle
  have hc0 : c = P.leadingCoeff := by
    have h1 := Polynomial.coeff_derivative P 0
    rw [← hc] at h1
    simp at h1
    rw [h1, ← hdeg, Polynomial.leadingCoeff]
  rw [← hc, Polynomial.eval_C, hc0]

/-! ### Root existence for linear polynomials

When `natDegree P = 1`, the derivative is a nonzero constant, so `P` is strictly
monotonic on all of `ℝ`. Its sign at `±∞` changes (odd degree), giving a root. -/

/-- A polynomial of degree 1 has a root. -/
lemma exists_root_of_natDegree_one (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdeg : P.natDegree = 1) : ∃ r, P.eval r = 0 := by
  have hP : P ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hdeg; exact absurd hdeg one_ne_zero.symm
  have hlc_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hpos := hasSignAtPosInfty_leadingCoeff P
  have hneg := hasSignAtNegInfty_leadingCoeff P
  rw [hdeg, pow_one] at hneg
  rcases lt_or_gt_of_ne hlc_ne with hlc_neg | hlc_pos
  · -- leadingCoeff < 0: sign at +∞ = neg, sign at −∞ = -neg = pos
    have hs : SignType.sign P.leadingCoeff = SignType.neg := sign_eq_neg_one_iff.mpr hlc_neg
    rw [hs] at hpos hneg
    simp at hneg
    exact exists_root_of_sign_pos_neg_at_infty hIVP P hneg hpos
  · -- leadingCoeff > 0: sign at +∞ = pos, sign at −∞ = -pos = neg
    have hs : SignType.sign P.leadingCoeff = SignType.pos := sign_eq_one_iff.mpr hlc_pos
    rw [hs] at hpos hneg
    simp at hneg
    exact exists_root_of_sign_neg_pos_at_infty hIVP P hneg hpos

/-! ### Sign dichotomy on gap intervals from `SignConstantOnGaps`

`SignConstantOnGaps Q ys` gives `Q` constant nonzero sign on any `x ≤ y` that
avoids `ys`. We repackage this as a strict-positivity-or-negativity dichotomy
on the three gap shapes: left tail `Iio c`, interior `Ioo a b`, and right tail
`Ioi c`. Each consumer will pick one branch and feed it to
`strictMonoOn_of_deriv_pos_*` / `strictAntiOn_of_deriv_neg_*`. -/

/-- Sign dichotomy on a left-tail gap: if every entry of `ys` is `≥ c`, then
    `Q` has a single strict sign throughout `Iio c`. -/
lemma sign_dichotomy_Iio {Q : R[X]} {ys : List R}
    (h : SignConstantOnGaps Q ys) {c : R} (hle : ∀ r ∈ ys, c ≤ r) :
    (∀ x ∈ Set.Iio c, 0 < Q.eval x) ∨ (∀ x ∈ Set.Iio c, Q.eval x < 0) := by
  set x₀ := c - 1
  have hx₀_lt : x₀ < c := sub_one_lt c
  have hx₀_mem : x₀ ∈ Set.Iio c := hx₀_lt
  have hsign_eq : ∀ x ∈ Set.Iio c, Q.eval x ≠ 0 ∧
      SignType.sign (Q.eval x) = SignType.sign (Q.eval x₀) := by
    intro x hx
    have hxc : x < c := hx
    rcases le_or_gt x x₀ with hxle | hlt
    · have hgap : ∀ r ∈ ys, r < x ∨ x₀ < r := by
        intro r hr; right; have := hle r hr; linarith
      exact h x x₀ hxle hgap
    · have hxle : x₀ ≤ x := le_of_lt hlt
      have hgap : ∀ r ∈ ys, r < x₀ ∨ x < r := by
        intro r hr; right; have := hle r hr; linarith
      obtain ⟨hne0, hs⟩ := h x₀ x hxle hgap
      refine ⟨?_, hs.symm⟩
      intro hzero; rw [hzero] at hs; simp at hs
      exact hne0 hs
  have hne_x₀ := (hsign_eq x₀ hx₀_mem).1
  rcases lt_or_gt_of_ne hne_x₀ with hx₀_neg | hx₀_pos
  · right; intro x hx
    obtain ⟨_, hs⟩ := hsign_eq x hx
    exact sign_eq_neg_one_iff.mp (hs.trans (sign_eq_neg_one_iff.mpr hx₀_neg))
  · left; intro x hx
    obtain ⟨_, hs⟩ := hsign_eq x hx
    exact sign_eq_one_iff.mp (hs.trans (sign_eq_one_iff.mpr hx₀_pos))

/-- Sign dichotomy on a right-tail gap: if every entry of `ys` is `≤ c`, then
    `Q` has a single strict sign throughout `Ioi c`. -/
lemma sign_dichotomy_Ioi {Q : R[X]} {ys : List R}
    (h : SignConstantOnGaps Q ys) {c : R} (hle : ∀ r ∈ ys, r ≤ c) :
    (∀ x ∈ Set.Ioi c, 0 < Q.eval x) ∨ (∀ x ∈ Set.Ioi c, Q.eval x < 0) := by
  set x₀ := c + 1
  have hcx₀ : c < x₀ := lt_add_one c
  have hx₀_mem : x₀ ∈ Set.Ioi c := hcx₀
  have hsign_eq : ∀ x ∈ Set.Ioi c, Q.eval x ≠ 0 ∧
      SignType.sign (Q.eval x) = SignType.sign (Q.eval x₀) := by
    intro x hx
    have hcx : c < x := hx
    rcases le_or_gt x x₀ with hxle | hlt
    · have hgap : ∀ r ∈ ys, r < x ∨ x₀ < r := by
        intro r hr; left; have := hle r hr; linarith
      obtain ⟨hne, hs⟩ := h x x₀ hxle hgap
      exact ⟨hne, hs⟩
    · have hxle : x₀ ≤ x := le_of_lt hlt
      have hgap : ∀ r ∈ ys, r < x₀ ∨ x < r := by
        intro r hr; left; have := hle r hr; linarith
      obtain ⟨hne0, hs⟩ := h x₀ x hxle hgap
      refine ⟨?_, hs.symm⟩
      intro hzero; rw [hzero] at hs; simp at hs
      exact hne0 hs
  have hne_x₀ := (hsign_eq x₀ hx₀_mem).1
  rcases lt_or_gt_of_ne hne_x₀ with hx₀_neg | hx₀_pos
  · right; intro x hx
    obtain ⟨_, hs⟩ := hsign_eq x hx
    exact sign_eq_neg_one_iff.mp (hs.trans (sign_eq_neg_one_iff.mpr hx₀_neg))
  · left; intro x hx
    obtain ⟨_, hs⟩ := hsign_eq x hx
    exact sign_eq_one_iff.mp (hs.trans (sign_eq_one_iff.mpr hx₀_pos))

/-- Sign dichotomy on an interior gap: if every entry of `ys` is outside
    `(a, b)`, then `Q` has a single strict sign throughout `Ioo a b`. -/
lemma sign_dichotomy_Ioo {Q : R[X]} {ys : List R}
    (h : SignConstantOnGaps Q ys) {a b : R} (hab : a < b)
    (hgap_out : ∀ r ∈ ys, r ≤ a ∨ b ≤ r) :
    (∀ x ∈ Set.Ioo a b, 0 < Q.eval x) ∨ (∀ x ∈ Set.Ioo a b, Q.eval x < 0) := by
  obtain ⟨x₀, ha0, h0b⟩ := exists_between hab
  have hx₀_mem : x₀ ∈ Set.Ioo a b := ⟨ha0, h0b⟩
  have hsign_eq : ∀ x ∈ Set.Ioo a b, Q.eval x ≠ 0 ∧
      SignType.sign (Q.eval x) = SignType.sign (Q.eval x₀) := by
    intro x hx
    have hax : a < x := hx.1
    have hxb : x < b := hx.2
    rcases le_or_gt x x₀ with hxle | hlt
    · have hgap : ∀ r ∈ ys, r < x ∨ x₀ < r := by
        intro r hr
        rcases hgap_out r hr with hra | hrb
        · left; linarith
        · right; linarith
      exact h x x₀ hxle hgap
    · have hxle : x₀ ≤ x := le_of_lt hlt
      have hgap : ∀ r ∈ ys, r < x₀ ∨ x < r := by
        intro r hr
        rcases hgap_out r hr with hra | hrb
        · left; linarith
        · right; linarith
      obtain ⟨hne0, hs⟩ := h x₀ x hxle hgap
      refine ⟨?_, hs.symm⟩
      intro hzero; rw [hzero] at hs; simp at hs
      exact hne0 hs
  have hne_x₀ := (hsign_eq x₀ hx₀_mem).1
  rcases lt_or_gt_of_ne hne_x₀ with hx₀_neg | hx₀_pos
  · right; intro x hx
    obtain ⟨_, hs⟩ := hsign_eq x hx
    exact sign_eq_neg_one_iff.mp (hs.trans (sign_eq_neg_one_iff.mpr hx₀_neg))
  · left; intro x hx
    obtain ⟨_, hs⟩ := hsign_eq x hx
    exact sign_eq_one_iff.mp (hs.trans (sign_eq_one_iff.mpr hx₀_pos))

/-! ### Singleton virtual roots list for a linear polynomial

For `natDegree P = 1`, `P` is strictly monotonic globally (derivative is a
nonzero constant). Its unique root `r` forms a singleton virtual roots list. -/

omit [IsStrictOrderedRing R] in
/-- If `P` is strictly monotonic with root `r`, the singleton `[r]` satisfies
    `SignConstantOnGaps P [r]`: outside `{r}`, `P` has constant nonzero sign
    (negative below `r`, positive above). -/
lemma signConstantOnGaps_singleton_of_strictMono {P : R[X]} {r : R}
    (hr : P.eval r = 0) (hmono : StrictMono (fun x => P.eval x)) :
    SignConstantOnGaps P [r] := by
  intro x y hxy hgap
  have hr_case : r < x ∨ y < r := by
    have := hgap r (List.mem_singleton.mpr rfl); exact this
  rcases hr_case with hrx | hyr
  · -- r < x ≤ y: both P(x), P(y) positive
    have hPx_pos : 0 < P.eval x := by
      have h := hmono hrx; simp only at h; rw [hr] at h; exact h
    have hPy_pos : 0 < P.eval y := by
      have hry : r < y := lt_of_lt_of_le hrx hxy
      have h := hmono hry; simp only at h; rw [hr] at h; exact h
    refine ⟨ne_of_gt hPx_pos, ?_⟩
    rw [sign_eq_one_iff.mpr hPx_pos, sign_eq_one_iff.mpr hPy_pos]
  · -- x ≤ y < r: both P(x), P(y) negative
    have hPy_neg : P.eval y < 0 := by
      have h := hmono hyr; simp only at h; rw [hr] at h; exact h
    have hPx_neg : P.eval x < 0 := by
      have hxr : x < r := lt_of_le_of_lt hxy hyr
      have h := hmono hxr; simp only at h; rw [hr] at h; exact h
    refine ⟨ne_of_lt hPx_neg, ?_⟩
    rw [sign_eq_neg_one_iff.mpr hPx_neg, sign_eq_neg_one_iff.mpr hPy_neg]

omit [IsStrictOrderedRing R] in
/-- Strictly antitonic version of `signConstantOnGaps_singleton_of_strictMono`. -/
lemma signConstantOnGaps_singleton_of_strictAnti {P : R[X]} {r : R}
    (hr : P.eval r = 0) (hanti : StrictAnti (fun x => P.eval x)) :
    SignConstantOnGaps P [r] := by
  intro x y hxy hgap
  have hr_case : r < x ∨ y < r := by
    have := hgap r (List.mem_singleton.mpr rfl); exact this
  rcases hr_case with hrx | hyr
  · -- r < x ≤ y: both P(x), P(y) negative
    have hPx_neg : P.eval x < 0 := by
      have h := hanti hrx; simp only at h; rw [hr] at h; exact h
    have hPy_neg : P.eval y < 0 := by
      have hry : r < y := lt_of_lt_of_le hrx hxy
      have h := hanti hry; simp only at h; rw [hr] at h; exact h
    refine ⟨ne_of_lt hPx_neg, ?_⟩
    rw [sign_eq_neg_one_iff.mpr hPx_neg, sign_eq_neg_one_iff.mpr hPy_neg]
  · -- x ≤ y < r: both P(x), P(y) positive
    have hPy_pos : 0 < P.eval y := by
      have h := hanti hyr; simp only at h; rw [hr] at h; exact h
    have hPx_pos : 0 < P.eval x := by
      have hxr : x < r := lt_of_le_of_lt hxy hyr
      have h := hanti hxr; simp only at h; rw [hr] at h; exact h
    refine ⟨ne_of_gt hPx_pos, ?_⟩
    rw [sign_eq_one_iff.mpr hPx_pos, sign_eq_one_iff.mpr hPy_pos]

/-- A linear polynomial has a virtual roots list consisting of its unique root.
    The argmin witness uses `ys = []` and `IsArgminAbsOn P Set.univ r` (since
    `P.eval r = 0`). -/
lemma exists_virtualRootsList_of_natDegree_one (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdeg : P.natDegree = 1) :
    ∃ roots : List R, IsVirtualRootsList P roots := by
  obtain ⟨r, hr⟩ := exists_root_of_natDegree_one hIVP hdeg
  have hP : P ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hdeg; exact absurd hdeg one_ne_zero.symm
  have hlc_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hderiv : ∀ x : R, (derivative P).eval x = P.leadingCoeff :=
    fun x => eval_derivative_of_natDegree_one hdeg x
  have hdP_ne : derivative P ≠ 0 := by
    intro h; have := hderiv 0; rw [h, Polynomial.eval_zero] at this; exact hlc_ne this.symm
  have hdP_deg : (derivative P).natDegree = 0 := by
    have h : (derivative P).degree = (P.natDegree - 1 : ℕ) :=
      Polynomial.degree_derivative_eq P (by rw [hdeg]; norm_num)
    have h' : (derivative P).natDegree = P.natDegree - 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some h
    rw [h', hdeg]
  have hsc : SignConstantOnGaps P [r] := by
    rcases lt_or_gt_of_ne hlc_ne with hlc_neg | hlc_pos
    · have hder_neg : ∀ x : R, (derivative P).eval x < 0 := by
        intro x; rw [hderiv]; exact hlc_neg
      exact signConstantOnGaps_singleton_of_strictAnti hr
        (strictAnti_of_deriv_neg hIVP hder_neg)
    · have hder_pos : ∀ x : R, 0 < (derivative P).eval x := by
        intro x; rw [hderiv]; exact hlc_pos
      exact signConstantOnGaps_singleton_of_strictMono hr
        (strictMono_of_deriv_pos hIVP hder_pos)
  refine ⟨[r], ?_⟩
  unfold IsVirtualRootsList
  rw [hdeg]
  refine ⟨by simp [hdeg], List.pairwise_singleton _ _, hsc, Or.inr ⟨[], ?_, trivial, ?_⟩⟩
  · -- IsVirtualRootsListAux 0 (derivative P) []
    refine ⟨?_, List.Pairwise.nil, ?_⟩
    · simp [hdP_deg]
    · -- SignConstantOnGaps (derivative P) []: derivative P is a nonzero constant
      intro x y _ _
      refine ⟨?_, ?_⟩
      · rw [hderiv]; exact hlc_ne
      · rw [hderiv, hderiv]
  · -- ArgminPartition P [r] [] = IsArgminAbsOn P Set.univ r
    show IsArgminAbsOn P Set.univ r
    refine ⟨Set.mem_univ _, ?_⟩
    intro z _
    rw [hr, abs_zero]
    exact abs_nonneg _

/-! ### Argmin existence chained off a derivative sign dichotomy

Given a strict-positive-or-negative dichotomy for `P'` on the open interior of
`Iic c`, `Icc a b`, or `Ici c`, we get an argmin of `|P|` on the corresponding
closed interval. These are the exact hypotheses produced by the
`sign_dichotomy_*` family — ready for direct composition. -/

/-- If `P'` has a dichotomous strict sign on `Iio c`, then `|P|` attains a
    minimum on `Iic c`. Requires `0 < natDegree P` for the asymptotic bound.
    The witness is either a root of `P` or `x = c`. -/
lemma exists_argmin_abs_on_Iic_of_deriv_dichotomy
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdeg : 0 < P.natDegree) {c : R}
    (hdich : (∀ x ∈ Set.Iio c, 0 < (derivative P).eval x) ∨
             (∀ x ∈ Set.Iio c, (derivative P).eval x < 0)) :
    ∃ x ∈ Set.Iic c, (∀ y ∈ Set.Iic c, |P.eval x| ≤ |P.eval y|) ∧
      (P.eval x = 0 ∨ x = c) := by
  rcases hdich with hpos | hneg
  · exact exists_argmin_abs_strictMonoOn_Iic hIVP hdeg
      (strictMonoOn_of_deriv_pos_Iic hIVP hpos)
  · exact exists_argmin_abs_strictAntiOn_Iic hIVP hdeg
      (strictAntiOn_of_deriv_neg_Iic hIVP hneg)

/-- If `P'` has a dichotomous strict sign on `Ioi c`, then `|P|` attains a
    minimum on `Ici c`. The witness is either a root of `P` or `x = c`. -/
lemma exists_argmin_abs_on_Ici_of_deriv_dichotomy
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdeg : 0 < P.natDegree) {c : R}
    (hdich : (∀ x ∈ Set.Ioi c, 0 < (derivative P).eval x) ∨
             (∀ x ∈ Set.Ioi c, (derivative P).eval x < 0)) :
    ∃ x ∈ Set.Ici c, (∀ y ∈ Set.Ici c, |P.eval x| ≤ |P.eval y|) ∧
      (P.eval x = 0 ∨ x = c) := by
  rcases hdich with hpos | hneg
  · exact exists_argmin_abs_strictMonoOn_Ici hIVP hdeg
      (strictMonoOn_of_deriv_pos_Ici hIVP hpos)
  · exact exists_argmin_abs_strictAntiOn_Ici hIVP hdeg
      (strictAntiOn_of_deriv_neg_Ici hIVP hneg)

/-- If `P'` has a dichotomous strict sign on `Ioo a b` (with `a < b`), then
    `|P|` attains a minimum on `Icc a b`. The witness is a root of `P` or an
    endpoint. -/
lemma exists_argmin_abs_on_Icc_of_deriv_dichotomy
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a < b)
    (hdich : (∀ x ∈ Set.Ioo a b, 0 < (derivative P).eval x) ∨
             (∀ x ∈ Set.Ioo a b, (derivative P).eval x < 0)) :
    ∃ x ∈ Set.Icc a b, (∀ y ∈ Set.Icc a b, |P.eval x| ≤ |P.eval y|) ∧
      (P.eval x = 0 ∨ x = a ∨ x = b) := by
  rcases hdich with hpos | hneg
  · exact exists_argmin_abs_strictMonoOn_Icc hIVP hab.le
      (corollary_2_24_increasing hIVP P hab hpos)
  · exact exists_argmin_abs_strictAntiOn_Icc hIVP hab.le
      (corollary_2_24_decreasing hIVP P hab hneg)

/-! ### Sign constancy from argmin of `|P|`

If `x₀` is the argmin of `|P|` on a closed interval on which `P` is strictly
monotonic, then on any gap `[x, y]` not containing `x₀`, `P` has constant
nonzero sign. Two sources: either `P(x₀) = 0` (so `x₀` is the unique root and
`P` has strict sign on each side by strict monotonicity), or `P(x₀) ≠ 0` (so
`P` has no root on the interval and the strict-mono trichotomy gives a
fixed strict sign). -/

/-- On `Icc a b`, argmin of `|P|` at `x₀` + strict-mono implies constant nonzero
    sign on any `x ≤ y` in `Icc a b` avoiding `x₀`. -/
lemma sign_const_of_argmin_strictMonoOn_Icc (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a ≤ b)
    (hmono : StrictMonoOn (fun x => P.eval x) (Set.Icc a b))
    {x₀ : R} (hx₀_mem : x₀ ∈ Set.Icc a b)
    (hx₀_min : ∀ y ∈ Set.Icc a b, |P.eval x₀| ≤ |P.eval y|)
    {x y : R} (hxy : x ≤ y) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hgap : x₀ < x ∨ y < x₀) :
    P.eval x ≠ 0 ∧ SignType.sign (P.eval x) = SignType.sign (P.eval y) := by
  by_cases hP0 : P.eval x₀ = 0
  · rcases hgap with hx₀x | hyx₀
    · have h1 : P.eval x₀ < P.eval x := hmono hx₀_mem hx hx₀x
      rw [hP0] at h1
      have h2 : P.eval x ≤ P.eval y := hmono.monotoneOn hx hy hxy
      have hPx_pos : 0 < P.eval x := h1
      have hPy_pos : 0 < P.eval y := lt_of_lt_of_le h1 h2
      exact ⟨ne_of_gt hPx_pos,
        by rw [sign_eq_one_iff.mpr hPx_pos, sign_eq_one_iff.mpr hPy_pos]⟩
    · have h2 : P.eval y < P.eval x₀ := hmono hy hx₀_mem hyx₀
      rw [hP0] at h2
      have h1 : P.eval x ≤ P.eval y := hmono.monotoneOn hx hy hxy
      have hPy_neg : P.eval y < 0 := h2
      have hPx_neg : P.eval x < 0 := lt_of_le_of_lt h1 h2
      exact ⟨ne_of_lt hPx_neg,
        by rw [sign_eq_neg_one_iff.mpr hPx_neg, sign_eq_neg_one_iff.mpr hPy_neg]⟩
  · rcases strictMonoOn_Icc_sign_trichotomy hIVP hab hmono with
      ⟨z, hz, hPz⟩ | hpos | hneg
    · exfalso; apply hP0
      have hle := hx₀_min z hz
      rw [hPz, abs_zero] at hle
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    · have hPx := hpos x hx
      have hPy := hpos y hy
      exact ⟨ne_of_gt hPx,
        by rw [sign_eq_one_iff.mpr hPx, sign_eq_one_iff.mpr hPy]⟩
    · have hPx := hneg x hx
      have hPy := hneg y hy
      exact ⟨ne_of_lt hPx,
        by rw [sign_eq_neg_one_iff.mpr hPx, sign_eq_neg_one_iff.mpr hPy]⟩

/-- Strict-antitonic version of `sign_const_of_argmin_strictMonoOn_Icc`. -/
lemma sign_const_of_argmin_strictAntiOn_Icc (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a ≤ b)
    (hanti : StrictAntiOn (fun x => P.eval x) (Set.Icc a b))
    {x₀ : R} (hx₀_mem : x₀ ∈ Set.Icc a b)
    (hx₀_min : ∀ y ∈ Set.Icc a b, |P.eval x₀| ≤ |P.eval y|)
    {x y : R} (hxy : x ≤ y) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hgap : x₀ < x ∨ y < x₀) :
    P.eval x ≠ 0 ∧ SignType.sign (P.eval x) = SignType.sign (P.eval y) := by
  by_cases hP0 : P.eval x₀ = 0
  · rcases hgap with hx₀x | hyx₀
    · have h1 : P.eval x < P.eval x₀ := hanti hx₀_mem hx hx₀x
      rw [hP0] at h1
      have h2 : P.eval y ≤ P.eval x := hanti.antitoneOn hx hy hxy
      have hPx_neg : P.eval x < 0 := h1
      have hPy_neg : P.eval y < 0 := lt_of_le_of_lt h2 h1
      exact ⟨ne_of_lt hPx_neg,
        by rw [sign_eq_neg_one_iff.mpr hPx_neg, sign_eq_neg_one_iff.mpr hPy_neg]⟩
    · have h2 : P.eval x₀ < P.eval y := hanti hy hx₀_mem hyx₀
      rw [hP0] at h2
      have h1 : P.eval y ≤ P.eval x := hanti.antitoneOn hx hy hxy
      have hPy_pos : 0 < P.eval y := h2
      have hPx_pos : 0 < P.eval x := lt_of_lt_of_le h2 h1
      exact ⟨ne_of_gt hPx_pos,
        by rw [sign_eq_one_iff.mpr hPx_pos, sign_eq_one_iff.mpr hPy_pos]⟩
  · rcases strictAntiOn_Icc_sign_trichotomy hIVP hab hanti with
      ⟨z, hz, hPz⟩ | hpos | hneg
    · exfalso; apply hP0
      have hle := hx₀_min z hz
      rw [hPz, abs_zero] at hle
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    · have hPx := hpos x hx
      have hPy := hpos y hy
      exact ⟨ne_of_gt hPx,
        by rw [sign_eq_one_iff.mpr hPx, sign_eq_one_iff.mpr hPy]⟩
    · have hPx := hneg x hx
      have hPy := hneg y hy
      exact ⟨ne_of_lt hPx,
        by rw [sign_eq_neg_one_iff.mpr hPx, sign_eq_neg_one_iff.mpr hPy]⟩

/-- Iic reduction of `sign_const_of_argmin_strictMonoOn_Icc`: restrict to
    `[min x x₀, c]`, an Icc subinterval of `Iic c` containing both `x`, `y`,
    and `x₀`. -/
lemma sign_const_of_argmin_strictMonoOn_Iic (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {c : R}
    (hmono : StrictMonoOn (fun x => P.eval x) (Set.Iic c))
    {x₀ : R} (hx₀_mem : x₀ ∈ Set.Iic c)
    (hx₀_min : ∀ y ∈ Set.Iic c, |P.eval x₀| ≤ |P.eval y|)
    {x y : R} (hxy : x ≤ y) (hx : x ∈ Set.Iic c) (hy : y ∈ Set.Iic c)
    (hgap : x₀ < x ∨ y < x₀) :
    P.eval x ≠ 0 ∧ SignType.sign (P.eval x) = SignType.sign (P.eval y) := by
  set N := min x x₀
  have hNx : N ≤ x := min_le_left _ _
  have hNx₀ : N ≤ x₀ := min_le_right _ _
  have hxc : x ≤ c := hx
  have hyc : y ≤ c := hy
  have hx₀c : x₀ ≤ c := hx₀_mem
  have hNc : N ≤ c := le_trans hNx hxc
  have hx_Icc : x ∈ Set.Icc N c := ⟨hNx, hxc⟩
  have hy_Icc : y ∈ Set.Icc N c := ⟨le_trans hNx hxy, hyc⟩
  have hx₀_Icc : x₀ ∈ Set.Icc N c := ⟨hNx₀, hx₀c⟩
  have hmono' : StrictMonoOn (fun x => P.eval x) (Set.Icc N c) :=
    hmono.mono (fun _ hz => hz.2)
  have hx₀_min' : ∀ y ∈ Set.Icc N c, |P.eval x₀| ≤ |P.eval y| :=
    fun y hy => hx₀_min y hy.2
  exact sign_const_of_argmin_strictMonoOn_Icc hIVP hNc hmono'
    hx₀_Icc hx₀_min' hxy hx_Icc hy_Icc hgap

/-- Strict-anti Iic version of `sign_const_of_argmin_strictMonoOn_Iic`. -/
lemma sign_const_of_argmin_strictAntiOn_Iic (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {c : R}
    (hanti : StrictAntiOn (fun x => P.eval x) (Set.Iic c))
    {x₀ : R} (hx₀_mem : x₀ ∈ Set.Iic c)
    (hx₀_min : ∀ y ∈ Set.Iic c, |P.eval x₀| ≤ |P.eval y|)
    {x y : R} (hxy : x ≤ y) (hx : x ∈ Set.Iic c) (hy : y ∈ Set.Iic c)
    (hgap : x₀ < x ∨ y < x₀) :
    P.eval x ≠ 0 ∧ SignType.sign (P.eval x) = SignType.sign (P.eval y) := by
  set N := min x x₀
  have hNx : N ≤ x := min_le_left _ _
  have hNx₀ : N ≤ x₀ := min_le_right _ _
  have hxc : x ≤ c := hx
  have hyc : y ≤ c := hy
  have hx₀c : x₀ ≤ c := hx₀_mem
  have hNc : N ≤ c := le_trans hNx hxc
  have hx_Icc : x ∈ Set.Icc N c := ⟨hNx, hxc⟩
  have hy_Icc : y ∈ Set.Icc N c := ⟨le_trans hNx hxy, hyc⟩
  have hx₀_Icc : x₀ ∈ Set.Icc N c := ⟨hNx₀, hx₀c⟩
  have hanti' : StrictAntiOn (fun x => P.eval x) (Set.Icc N c) :=
    hanti.mono (fun _ hz => hz.2)
  have hx₀_min' : ∀ y ∈ Set.Icc N c, |P.eval x₀| ≤ |P.eval y| :=
    fun y hy => hx₀_min y hy.2
  exact sign_const_of_argmin_strictAntiOn_Icc hIVP hNc hanti'
    hx₀_Icc hx₀_min' hxy hx_Icc hy_Icc hgap

/-- Ici reduction of `sign_const_of_argmin_strictMonoOn_Icc`. -/
lemma sign_const_of_argmin_strictMonoOn_Ici (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {c : R}
    (hmono : StrictMonoOn (fun x => P.eval x) (Set.Ici c))
    {x₀ : R} (hx₀_mem : x₀ ∈ Set.Ici c)
    (hx₀_min : ∀ y ∈ Set.Ici c, |P.eval x₀| ≤ |P.eval y|)
    {x y : R} (hxy : x ≤ y) (hx : x ∈ Set.Ici c) (hy : y ∈ Set.Ici c)
    (hgap : x₀ < x ∨ y < x₀) :
    P.eval x ≠ 0 ∧ SignType.sign (P.eval x) = SignType.sign (P.eval y) := by
  set M := max y x₀
  have hyM : y ≤ M := le_max_left _ _
  have hx₀M : x₀ ≤ M := le_max_right _ _
  have hcx : c ≤ x := hx
  have hcy : c ≤ y := hy
  have hcx₀ : c ≤ x₀ := hx₀_mem
  have hcM : c ≤ M := le_trans hcy hyM
  have hx_Icc : x ∈ Set.Icc c M := ⟨hcx, le_trans hxy hyM⟩
  have hy_Icc : y ∈ Set.Icc c M := ⟨hcy, hyM⟩
  have hx₀_Icc : x₀ ∈ Set.Icc c M := ⟨hcx₀, hx₀M⟩
  have hmono' : StrictMonoOn (fun x => P.eval x) (Set.Icc c M) :=
    hmono.mono (fun _ hz => hz.1)
  have hx₀_min' : ∀ y ∈ Set.Icc c M, |P.eval x₀| ≤ |P.eval y| :=
    fun y hy => hx₀_min y hy.1
  exact sign_const_of_argmin_strictMonoOn_Icc hIVP hcM hmono'
    hx₀_Icc hx₀_min' hxy hx_Icc hy_Icc hgap

/-- Strict-anti Ici version of `sign_const_of_argmin_strictMonoOn_Ici`. -/
lemma sign_const_of_argmin_strictAntiOn_Ici (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {c : R}
    (hanti : StrictAntiOn (fun x => P.eval x) (Set.Ici c))
    {x₀ : R} (hx₀_mem : x₀ ∈ Set.Ici c)
    (hx₀_min : ∀ y ∈ Set.Ici c, |P.eval x₀| ≤ |P.eval y|)
    {x y : R} (hxy : x ≤ y) (hx : x ∈ Set.Ici c) (hy : y ∈ Set.Ici c)
    (hgap : x₀ < x ∨ y < x₀) :
    P.eval x ≠ 0 ∧ SignType.sign (P.eval x) = SignType.sign (P.eval y) := by
  set M := max y x₀
  have hyM : y ≤ M := le_max_left _ _
  have hx₀M : x₀ ≤ M := le_max_right _ _
  have hcx : c ≤ x := hx
  have hcy : c ≤ y := hy
  have hcx₀ : c ≤ x₀ := hx₀_mem
  have hcM : c ≤ M := le_trans hcy hyM
  have hx_Icc : x ∈ Set.Icc c M := ⟨hcx, le_trans hxy hyM⟩
  have hy_Icc : y ∈ Set.Icc c M := ⟨hcy, hyM⟩
  have hx₀_Icc : x₀ ∈ Set.Icc c M := ⟨hcx₀, hx₀M⟩
  have hanti' : StrictAntiOn (fun x => P.eval x) (Set.Icc c M) :=
    hanti.mono (fun _ hz => hz.1)
  have hx₀_min' : ∀ y ∈ Set.Icc c M, |P.eval x₀| ≤ |P.eval y| :=
    fun y hy => hx₀_min y hy.1
  exact sign_const_of_argmin_strictAntiOn_Icc hIVP hcM hanti'
    hx₀_Icc hx₀_min' hxy hx_Icc hy_Icc hgap

/-! ### Interior argmin ⇒ critical point

Helper (1) for the non-root case of Lemma 2.48: if `c` is in the open interior
of `[v, y]`, is an argmin of `|P|` on `[v, y]`, and `P(c) ≠ 0`, then `P'(c) = 0`.

**Proof idea.** If `P'(c) ≠ 0`, Proposition 2.21 pins the sign of `P` and `P'`
on both sides of `c`, and the MVT (Corollary 2.23) forces `P` to be strictly
monotonic on a one-sided neighborhood of `c`. Combined with `P(c) ≠ 0`, this
produces a nearby point `x ∈ [v, y]` with `|P(x)| < |P(c)|`, contradicting the
argmin property. -/

/-- **Interior argmin ⇒ critical point of `P`.** If `v < c < y`, `c` is an
    argmin of `|P|` on `[v, y]`, and `P.eval c ≠ 0`, then `(derivative P).eval c = 0`. -/
lemma deriv_eq_zero_of_isArgminAbsOn_interior
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {v y c : R}
    (hvc : v < c) (hcy : c < y)
    (hc_argmin : IsArgminAbsOn P (Set.Icc v y) c)
    (hPc : P.eval c ≠ 0) :
    (derivative P).eval c = 0 := by
  by_contra hP'c
  obtain ⟨_, hmin⟩ := hc_argmin
  have hP : P ≠ 0 := fun h => hPc (by simp [h])
  have hdP : derivative P ≠ 0 := fun h => hP'c (by simp [h])
  have hmult_P : P.rootMultiplicity c = 0 := Polynomial.rootMultiplicity_eq_zero hPc
  have hmult_P' : (derivative P).rootMultiplicity c = 0 :=
    Polynomial.rootMultiplicity_eq_zero hP'c
  -- Prop 2.21 sign witnesses for P and P' on both sides of c.
  have hP_sr : HasSignRight P c (SignType.sign (P.eval c)) := by
    have h := proposition_2_21_right hIVP hP c
    rw [hmult_P] at h
    simpa using h
  have hP_sl : HasSignLeft P c (SignType.sign (P.eval c)) := by
    have h := proposition_2_21_left hIVP hP c
    rw [hmult_P] at h
    simpa using h
  have hP'_sr : HasSignRight (derivative P) c
      (SignType.sign ((derivative P).eval c)) := by
    have h := proposition_2_21_right hIVP hdP c
    rw [hmult_P'] at h
    simpa using h
  have hP'_sl : HasSignLeft (derivative P) c
      (SignType.sign ((derivative P).eval c)) := by
    have h := proposition_2_21_left hIVP hdP c
    rw [hmult_P'] at h
    simpa using h
  obtain ⟨bR, hbR, hsR⟩ := hP_sr
  obtain ⟨bL, hbL, hsL⟩ := hP_sl
  obtain ⟨b'R, hb'R, hs'R⟩ := hP'_sr
  obtain ⟨b'L, hb'L, hs'L⟩ := hP'_sl
  -- Pick common witness points on each side of c.
  have hc_lt : c < min bR (min b'R y) := lt_min hbR (lt_min hb'R hcy)
  have hlt_c : max bL (max b'L v) < c := max_lt hbL (max_lt hb'L hvc)
  obtain ⟨xR, hcxR, hxRlt⟩ := exists_between hc_lt
  obtain ⟨xL, hxLgt, hxLc⟩ := exists_between hlt_c
  have hxR_lt_bR : xR < bR := lt_of_lt_of_le hxRlt (min_le_left _ _)
  have hxR_lt_b'R : xR < b'R := lt_of_lt_of_le hxRlt
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hxR_lt_y : xR < y := lt_of_lt_of_le hxRlt
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hbL_lt_xL : bL < xL := lt_of_le_of_lt (le_max_left _ _) hxLgt
  have hb'L_lt_xL : b'L < xL := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hxLgt
  have hv_lt_xL : v < xL := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hxLgt
  have hs_PxR : SignType.sign (P.eval xR) = SignType.sign (P.eval c) :=
    hsR xR ⟨hcxR, hxR_lt_bR⟩
  have hs_PxL : SignType.sign (P.eval xL) = SignType.sign (P.eval c) :=
    hsL xL ⟨hbL_lt_xL, hxLc⟩
  -- MVT on [xL, c] and [c, xR].
  obtain ⟨ξL, ⟨hξLxL, hξLc⟩, hmvt_L⟩ := corollary_2_23 hIVP P hxLc
  obtain ⟨ξR, ⟨hcξR, hξRxR⟩, hmvt_R⟩ := corollary_2_23 hIVP P hcxR
  have hs_P'ξL : SignType.sign ((derivative P).eval ξL)
      = SignType.sign ((derivative P).eval c) :=
    hs'L ξL ⟨hb'L_lt_xL.trans hξLxL, hξLc⟩
  have hs_P'ξR : SignType.sign ((derivative P).eval ξR)
      = SignType.sign ((derivative P).eval c) :=
    hs'R ξR ⟨hcξR, hξRxR.trans hxR_lt_b'R⟩
  have hxR_mem : xR ∈ Set.Icc v y := ⟨hvc.le.trans hcxR.le, hxR_lt_y.le⟩
  have hxL_mem : xL ∈ Set.Icc v y := ⟨hv_lt_xL.le, hxLc.le.trans hcy.le⟩
  have hmin_xR := hmin xR hxR_mem
  have hmin_xL := hmin xL hxL_mem
  have hcxL_pos : 0 < c - xL := sub_pos.mpr hxLc
  have hxRc_pos : 0 < xR - c := sub_pos.mpr hcxR
  -- Sign of P(c) - P(xL) via MVT.
  have hsign_diff_L : SignType.sign (P.eval c - P.eval xL)
      = SignType.sign ((derivative P).eval c) := by
    rw [hmvt_L, sign_mul, sign_pos hcxL_pos, one_mul]; exact hs_P'ξL
  have hsign_diff_R : SignType.sign (P.eval xR - P.eval c)
      = SignType.sign ((derivative P).eval c) := by
    rw [hmvt_R, sign_mul, sign_pos hxRc_pos, one_mul]; exact hs_P'ξR
  -- Case-split on signs of P(c) and P'(c).
  rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
  · rcases lt_or_gt_of_ne hP'c with hP'c_neg | hP'c_pos
    · -- P(c) < 0, P'(c) < 0. Use xL: P(c) < P(xL), both negative ⇒ |P(c)| > |P(xL)|.
      have hdiff_neg : P.eval c - P.eval xL < 0 := by
        have h := hsign_diff_L
        rw [sign_neg hP'c_neg] at h
        exact sign_eq_neg_one_iff.mp h
      have hPxL_neg : P.eval xL < 0 := by
        have h := hs_PxL
        rw [sign_neg hPc_neg] at h
        exact sign_eq_neg_one_iff.mp h
      rw [abs_of_neg hPc_neg, abs_of_neg hPxL_neg] at hmin_xL
      linarith
    · -- P(c) < 0, P'(c) > 0. Use xR: P(c) < P(xR), both negative ⇒ |P(c)| > |P(xR)|.
      have hdiff_pos : 0 < P.eval xR - P.eval c := by
        have h := hsign_diff_R
        rw [sign_pos hP'c_pos] at h
        exact sign_eq_one_iff.mp h
      have hPxR_neg : P.eval xR < 0 := by
        have h := hs_PxR
        rw [sign_neg hPc_neg] at h
        exact sign_eq_neg_one_iff.mp h
      rw [abs_of_neg hPc_neg, abs_of_neg hPxR_neg] at hmin_xR
      linarith
  · rcases lt_or_gt_of_ne hP'c with hP'c_neg | hP'c_pos
    · -- P(c) > 0, P'(c) < 0. Use xR: P(xR) < P(c), both positive ⇒ |P(xR)| < |P(c)|.
      have hdiff_neg : P.eval xR - P.eval c < 0 := by
        have h := hsign_diff_R
        rw [sign_neg hP'c_neg] at h
        exact sign_eq_neg_one_iff.mp h
      have hPxR_pos : 0 < P.eval xR := by
        have h := hs_PxR
        rw [sign_pos hPc_pos] at h
        exact sign_eq_one_iff.mp h
      rw [abs_of_pos hPc_pos, abs_of_pos hPxR_pos] at hmin_xR
      linarith
    · -- P(c) > 0, P'(c) > 0. Use xL: P(xL) < P(c), both positive ⇒ |P(xL)| < |P(c)|.
      have hdiff_pos : 0 < P.eval c - P.eval xL := by
        have h := hsign_diff_L
        rw [sign_pos hP'c_pos] at h
        exact sign_eq_one_iff.mp h
      have hPxL_pos : 0 < P.eval xL := by
        have h := hs_PxL
        rw [sign_pos hPc_pos] at h
        exact sign_eq_one_iff.mp h
      rw [abs_of_pos hPc_pos, abs_of_pos hPxL_pos] at hmin_xL
      linarith

/-! ### Argmin direction from sign of `P(c) · P^(ν+1)(c)`

Helper (2) for the non-root case of Lemma 2.48. Given that `c` is an interior
argmin of `|P|` on `[v, y]` with `P(c) ≠ 0`, the parity of
`ν := (derivative P).rootMultiplicity c` and the sign of
`P(c) · P^(ν+1)(c)` are forced: `ν` must be **odd**, and the product must be
**positive**.

**Proof idea.** Let `σ = sign P(c)` and `τ = sign P^(ν+1)(c)`. Proposition 2.21
gives `sign P = σ` on both sides of `c`, `sign P' = τ` to the right, and
`sign P' = (-1)^ν · τ` to the left. Applying the MVT on `[xL, c]` and
`[c, xR]` and comparing with `|P(c)| ≤ |P(xL)|`, `|P(c)| ≤ |P(xR)|` pins
`τ = σ` and `(-1)^ν · τ = -σ`. Hence `(-1)^ν = -1` (so `ν` is odd) and
`σ · τ = σ² = 1 > 0`. -/

/-- **Argmin direction.** If `c` is an interior argmin of `|P|` on `[v, y]`
    with `P(c) ≠ 0` and `P' ≠ 0`, then `(derivative P).rootMultiplicity c` is
    **odd** and `0 < P(c) · P^(ν+1)(c)`. -/
lemma rootMult_odd_and_sign_pos_of_isArgminAbsOn_interior
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdP : derivative P ≠ 0) {v y c : R}
    (hvc : v < c) (hcy : c < y)
    (hc_argmin : IsArgminAbsOn P (Set.Icc v y) c)
    (hPc : P.eval c ≠ 0) :
    Odd ((derivative P).rootMultiplicity c) ∧
      0 < P.eval c *
        ((⇑derivative)^[(derivative P).rootMultiplicity c + 1] P).eval c := by
  set ν := (derivative P).rootMultiplicity c with hν_def
  obtain ⟨_, hmin⟩ := hc_argmin
  have hP : P ≠ 0 := fun h => hPc (by simp [h])
  have hmult_P : P.rootMultiplicity c = 0 :=
    Polynomial.rootMultiplicity_eq_zero hPc
  -- Identify `(derivative)^[ν + 1] P` with `(derivative)^[ν] (derivative P)`.
  have hshift : (⇑derivative)^[ν + 1] P = (⇑derivative)^[ν] (derivative P) := by
    rw [Function.iterate_succ, Function.comp_apply]
  -- `P^(ν+1)(c) ≠ 0` via Taylor expansion of `derivative P` at `c`.
  have hP_ν_plus_one_ne : ((⇑derivative)^[ν + 1] P).eval c ≠ 0 := by
    rw [hshift]
    have h := Polynomial.eval_iterate_derivative_rootMultiplicity
      (p := derivative P) (t := c)
    rw [← hν_def] at h
    rw [h, nsmul_eq_mul]
    refine mul_ne_zero ?_
      (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hdP)
    exact_mod_cast Nat.factorial_ne_zero _
  -- Prop 2.21 for `P` (rootMultiplicity 0).
  have hP_sr : HasSignRight P c (SignType.sign (P.eval c)) := by
    have h := proposition_2_21_right hIVP hP c
    rw [hmult_P] at h; simpa using h
  have hP_sl : HasSignLeft P c (SignType.sign (P.eval c)) := by
    have h := proposition_2_21_left hIVP hP c
    rw [hmult_P] at h; simpa using h
  -- Prop 2.21 for `derivative P` (rootMultiplicity ν).
  have hP'_sr : HasSignRight (derivative P) c
      (SignType.sign (((⇑derivative)^[ν + 1] P).eval c)) := by
    have h := proposition_2_21_right hIVP hdP c
    rw [← hν_def, ← hshift] at h; exact h
  have hP'_sl : HasSignLeft (derivative P) c
      ((-1) ^ ν * SignType.sign (((⇑derivative)^[ν + 1] P).eval c)) := by
    have h := proposition_2_21_left hIVP hdP c
    rw [← hν_def, ← hshift] at h; exact h
  obtain ⟨bR, hbR, hsR⟩ := hP_sr
  obtain ⟨bL, hbL, hsL⟩ := hP_sl
  obtain ⟨b'R, hb'R, hs'R⟩ := hP'_sr
  obtain ⟨b'L, hb'L, hs'L⟩ := hP'_sl
  -- Pick common witness points on each side of `c`.
  have hc_lt : c < min bR (min b'R y) := lt_min hbR (lt_min hb'R hcy)
  have hlt_c : max bL (max b'L v) < c := max_lt hbL (max_lt hb'L hvc)
  obtain ⟨xR, hcxR, hxRlt⟩ := exists_between hc_lt
  obtain ⟨xL, hxLgt, hxLc⟩ := exists_between hlt_c
  have hxR_lt_bR : xR < bR := lt_of_lt_of_le hxRlt (min_le_left _ _)
  have hxR_lt_b'R : xR < b'R := lt_of_lt_of_le hxRlt
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hxR_lt_y : xR < y := lt_of_lt_of_le hxRlt
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hbL_lt_xL : bL < xL := lt_of_le_of_lt (le_max_left _ _) hxLgt
  have hb'L_lt_xL : b'L < xL := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hxLgt
  have hv_lt_xL : v < xL := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hxLgt
  have hs_PxR : SignType.sign (P.eval xR) = SignType.sign (P.eval c) :=
    hsR xR ⟨hcxR, hxR_lt_bR⟩
  have hs_PxL : SignType.sign (P.eval xL) = SignType.sign (P.eval c) :=
    hsL xL ⟨hbL_lt_xL, hxLc⟩
  -- MVT on `[xL, c]` and `[c, xR]`.
  obtain ⟨ξL, ⟨hξLxL, hξLc⟩, hmvt_L⟩ := corollary_2_23 hIVP P hxLc
  obtain ⟨ξR, ⟨hcξR, hξRxR⟩, hmvt_R⟩ := corollary_2_23 hIVP P hcxR
  have hs_P'ξR : SignType.sign ((derivative P).eval ξR)
      = SignType.sign (((⇑derivative)^[ν + 1] P).eval c) :=
    hs'R ξR ⟨hcξR, hξRxR.trans hxR_lt_b'R⟩
  have hs_P'ξL : SignType.sign ((derivative P).eval ξL)
      = (-1) ^ ν * SignType.sign (((⇑derivative)^[ν + 1] P).eval c) :=
    hs'L ξL ⟨hb'L_lt_xL.trans hξLxL, hξLc⟩
  have hcxL_pos : 0 < c - xL := sub_pos.mpr hxLc
  have hxRc_pos : 0 < xR - c := sub_pos.mpr hcxR
  have hsign_diff_R : SignType.sign (P.eval xR - P.eval c)
      = SignType.sign (((⇑derivative)^[ν + 1] P).eval c) := by
    rw [hmvt_R, sign_mul, sign_pos hxRc_pos, one_mul]; exact hs_P'ξR
  have hsign_diff_L : SignType.sign (P.eval c - P.eval xL)
      = (-1) ^ ν * SignType.sign (((⇑derivative)^[ν + 1] P).eval c) := by
    rw [hmvt_L, sign_mul, sign_pos hcxL_pos, one_mul]; exact hs_P'ξL
  have hxR_mem : xR ∈ Set.Icc v y := ⟨hvc.le.trans hcxR.le, hxR_lt_y.le⟩
  have hxL_mem : xL ∈ Set.Icc v y := ⟨hv_lt_xL.le, hxLc.le.trans hcy.le⟩
  have hmin_xR := hmin xR hxR_mem
  have hmin_xL := hmin xL hxL_mem
  have hτ_ne : SignType.sign (((⇑derivative)^[ν + 1] P).eval c) ≠ 0 :=
    sign_ne_zero.mpr hP_ν_plus_one_ne
  have hpow_ne : (-1 : SignType) ^ ν ≠ 0 := by
    rcases Nat.even_or_odd ν with he | ho
    · rw [Even.neg_one_pow he]; decide
    · rw [Odd.neg_one_pow ho]; decide
  have hneg_τ_ne : (-1 : SignType) ^ ν *
      SignType.sign (((⇑derivative)^[ν + 1] P).eval c) ≠ 0 :=
    mul_ne_zero hpow_ne hτ_ne
  -- Split on sign of `P(c)`.
  rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
  · -- Case σ = -1.
    have hPxR_neg : P.eval xR < 0 := by
      have h := hs_PxR; rw [sign_neg hPc_neg] at h
      exact sign_eq_neg_one_iff.mp h
    have hPxL_neg : P.eval xL < 0 := by
      have h := hs_PxL; rw [sign_neg hPc_neg] at h
      exact sign_eq_neg_one_iff.mp h
    rw [abs_of_neg hPc_neg, abs_of_neg hPxR_neg] at hmin_xR
    rw [abs_of_neg hPc_neg, abs_of_neg hPxL_neg] at hmin_xL
    have hdiff_R_lt : P.eval xR - P.eval c < 0 := by
      rcases eq_or_lt_of_le (show P.eval xR - P.eval c ≤ 0 by linarith) with h | h
      · exfalso; apply hτ_ne; rw [← hsign_diff_R, h, sign_zero]
      · exact h
    have hτ_eq : SignType.sign (((⇑derivative)^[ν + 1] P).eval c) = -1 := by
      rw [← hsign_diff_R]; exact sign_neg hdiff_R_lt
    have hdiff_L_lt : 0 < P.eval c - P.eval xL := by
      rcases eq_or_lt_of_le (show (0 : R) ≤ P.eval c - P.eval xL by linarith)
        with h | h
      · exfalso; apply hneg_τ_ne; rw [← hsign_diff_L, ← h, sign_zero]
      · exact h
    have hL_one : SignType.sign (P.eval c - P.eval xL) = 1 := sign_pos hdiff_L_lt
    rw [hsign_diff_L, hτ_eq] at hL_one
    -- hL_one : (-1)^ν * (-1) = 1. With ν even, (-1)^ν = 1, so 1 * (-1) = -1 ≠ 1.
    have hν_odd : Odd ν := by
      rcases Nat.even_or_odd ν with he | ho
      · exfalso
        rw [Even.neg_one_pow he, one_mul] at hL_one
        exact absurd hL_one (by decide)
      · exact ho
    refine ⟨hν_odd, ?_⟩
    have hP_ν_plus_one_neg : ((⇑derivative)^[ν + 1] P).eval c < 0 :=
      sign_eq_neg_one_iff.mp hτ_eq
    exact mul_pos_of_neg_of_neg hPc_neg hP_ν_plus_one_neg
  · -- Case σ = +1.
    have hPxR_pos : 0 < P.eval xR := by
      have h := hs_PxR; rw [sign_pos hPc_pos] at h
      exact sign_eq_one_iff.mp h
    have hPxL_pos : 0 < P.eval xL := by
      have h := hs_PxL; rw [sign_pos hPc_pos] at h
      exact sign_eq_one_iff.mp h
    rw [abs_of_pos hPc_pos, abs_of_pos hPxR_pos] at hmin_xR
    rw [abs_of_pos hPc_pos, abs_of_pos hPxL_pos] at hmin_xL
    have hdiff_R_lt : 0 < P.eval xR - P.eval c := by
      rcases eq_or_lt_of_le (show (0 : R) ≤ P.eval xR - P.eval c by linarith)
        with h | h
      · exfalso; apply hτ_ne; rw [← hsign_diff_R, ← h, sign_zero]
      · exact h
    have hτ_eq : SignType.sign (((⇑derivative)^[ν + 1] P).eval c) = 1 := by
      rw [← hsign_diff_R]; exact sign_pos hdiff_R_lt
    have hdiff_L_lt : P.eval c - P.eval xL < 0 := by
      rcases eq_or_lt_of_le (show P.eval c - P.eval xL ≤ 0 by linarith) with h | h
      · exfalso; apply hneg_τ_ne; rw [← hsign_diff_L, h, sign_zero]
      · exact h
    have hL_neg_one : SignType.sign (P.eval c - P.eval xL) = -1 :=
      sign_neg hdiff_L_lt
    rw [hsign_diff_L, hτ_eq, mul_one] at hL_neg_one
    -- hL_neg_one : (-1)^ν = -1. With ν even, (-1)^ν = 1 ≠ -1.
    have hν_odd : Odd ν := by
      rcases Nat.even_or_odd ν with he | ho
      · exfalso
        rw [Even.neg_one_pow he] at hL_neg_one
        exact absurd hL_neg_one (by decide)
      · exact ho
    refine ⟨hν_odd, ?_⟩
    have hP_ν_plus_one_pos : 0 < ((⇑derivative)^[ν + 1] P).eval c :=
      sign_eq_one_iff.mp hτ_eq
    exact mul_pos hPc_pos hP_ν_plus_one_pos

/-! ### Boundary variants of Helper (2)

When `c` is the **right endpoint** of the argmin interval `[v, c]` (so no
strict interior argument is available on the right), the analysis is still
possible using only the **left** MVT. The conclusion is weaker: instead of
forcing `ν` to be odd, it pins the sign of `(-1)^ν · P(c) · P^(ν+1)(c)` to be
negative. This is what drives the `x₀ = c` classification inside the c-block.

Symmetrically for the **left endpoint** of `[c, y]`: the right MVT gives the
sign of `P(c) · P^(ν+1)(c)` to be negative. -/

/-- **Right-boundary argmin.** If `c` is argmin of `|P|` on `[v, c]` with
    `v < c` and `P(c) ≠ 0`, then `0 < (-1)^(ν+1) · P(c) · P^(ν+1)(c)` where
    `ν := (derivative P).rootMultiplicity c`. (Here `(-1 : R)^k` is the power
    in the coefficient ring.) -/
lemma sign_of_isArgminAbsOn_right_boundary
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdP : derivative P ≠ 0) {v c : R}
    (hvc : v < c)
    (hc_argmin : IsArgminAbsOn P (Set.Icc v c) c)
    (hPc : P.eval c ≠ 0) :
    0 < (-1 : R) ^ ((derivative P).rootMultiplicity c + 1) * P.eval c *
      ((⇑derivative)^[(derivative P).rootMultiplicity c + 1] P).eval c := by
  set ν := (derivative P).rootMultiplicity c with hν_def
  obtain ⟨_, hmin⟩ := hc_argmin
  have hP : P ≠ 0 := fun h => hPc (by simp [h])
  have hmult_P : P.rootMultiplicity c = 0 :=
    Polynomial.rootMultiplicity_eq_zero hPc
  have hshift : (⇑derivative)^[ν + 1] P = (⇑derivative)^[ν] (derivative P) := by
    rw [Function.iterate_succ, Function.comp_apply]
  have hP_ν_plus_one_ne : ((⇑derivative)^[ν + 1] P).eval c ≠ 0 := by
    rw [hshift]
    have h := Polynomial.eval_iterate_derivative_rootMultiplicity
      (p := derivative P) (t := c)
    rw [← hν_def] at h
    rw [h, nsmul_eq_mul]
    refine mul_ne_zero ?_
      (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hdP)
    exact_mod_cast Nat.factorial_ne_zero _
  have hP_sl : HasSignLeft P c (SignType.sign (P.eval c)) := by
    have h := proposition_2_21_left hIVP hP c
    rw [hmult_P] at h; simpa using h
  have hP'_sl : HasSignLeft (derivative P) c
      ((-1) ^ ν * SignType.sign (((⇑derivative)^[ν + 1] P).eval c)) := by
    have h := proposition_2_21_left hIVP hdP c
    rw [← hν_def, ← hshift] at h; exact h
  obtain ⟨bL, hbL, hsL⟩ := hP_sl
  obtain ⟨b'L, hb'L, hs'L⟩ := hP'_sl
  have hlt_c : max bL (max b'L v) < c := max_lt hbL (max_lt hb'L hvc)
  obtain ⟨xL, hxLgt, hxLc⟩ := exists_between hlt_c
  have hbL_lt_xL : bL < xL := lt_of_le_of_lt (le_max_left _ _) hxLgt
  have hb'L_lt_xL : b'L < xL := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hxLgt
  have hv_lt_xL : v < xL := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hxLgt
  have hs_PxL : SignType.sign (P.eval xL) = SignType.sign (P.eval c) :=
    hsL xL ⟨hbL_lt_xL, hxLc⟩
  obtain ⟨ξL, ⟨hξLxL, hξLc⟩, hmvt_L⟩ := corollary_2_23 hIVP P hxLc
  have hs_P'ξL : SignType.sign ((derivative P).eval ξL)
      = (-1) ^ ν * SignType.sign (((⇑derivative)^[ν + 1] P).eval c) :=
    hs'L ξL ⟨hb'L_lt_xL.trans hξLxL, hξLc⟩
  have hcxL_pos : 0 < c - xL := sub_pos.mpr hxLc
  have hsign_diff_L : SignType.sign (P.eval c - P.eval xL)
      = (-1) ^ ν * SignType.sign (((⇑derivative)^[ν + 1] P).eval c) := by
    rw [hmvt_L, sign_mul, sign_pos hcxL_pos, one_mul]; exact hs_P'ξL
  have hxL_mem : xL ∈ Set.Icc v c := ⟨hv_lt_xL.le, hxLc.le⟩
  have hmin_xL := hmin xL hxL_mem
  have hτ_ne : SignType.sign (((⇑derivative)^[ν + 1] P).eval c) ≠ 0 :=
    sign_ne_zero.mpr hP_ν_plus_one_ne
  have hpow_ne : (-1 : SignType) ^ ν ≠ 0 := by
    rcases Nat.even_or_odd ν with he | ho
    · rw [Even.neg_one_pow he]; decide
    · rw [Odd.neg_one_pow ho]; decide
  have hneg_τ_ne : (-1 : SignType) ^ ν *
      SignType.sign (((⇑derivative)^[ν + 1] P).eval c) ≠ 0 :=
    mul_ne_zero hpow_ne hτ_ne
  -- Case split on sign of P(c).
  rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
  · have hPxL_neg : P.eval xL < 0 := by
      have h := hs_PxL; rw [sign_neg hPc_neg] at h
      exact sign_eq_neg_one_iff.mp h
    rw [abs_of_neg hPc_neg, abs_of_neg hPxL_neg] at hmin_xL
    -- |P(c)| ≤ |P(xL)| with both negative: -P(c) ≤ -P(xL), i.e. P(xL) ≤ P(c).
    have hdiff_L_nonneg : 0 ≤ P.eval c - P.eval xL := by linarith
    have hdiff_L_pos : 0 < P.eval c - P.eval xL := by
      rcases eq_or_lt_of_le hdiff_L_nonneg with h | h
      · exfalso; apply hneg_τ_ne; rw [← hsign_diff_L, ← h, sign_zero]
      · exact h
    have hL_one : SignType.sign (P.eval c - P.eval xL) = 1 := sign_pos hdiff_L_pos
    rw [hsign_diff_L] at hL_one
    -- (-1)^ν · τ = 1. So τ = (-1)^ν. Hence P^(ν+1)(c) and (-1)^ν · 1 have same sign.
    -- We need: (-1)^(ν+1) · P(c) · P^(ν+1)(c) > 0.
    -- Since P(c) < 0: (-1)^(ν+1) · P(c) · P^(ν+1)(c) > 0 ⟺
    --   (-1)^(ν+1) · P^(ν+1)(c) < 0 ⟺ (-1)^ν · P^(ν+1)(c) > 0.
    -- From (-1)^ν · τ = 1: τ = (-1)^ν, so sign(P^(ν+1)(c)) = (-1)^ν, so
    --   (-1)^ν · P^(ν+1)(c) has sign (-1)^(2ν) = 1 > 0. ✓
    have hτ_eq_pow : SignType.sign (((⇑derivative)^[ν + 1] P).eval c) =
        (-1 : SignType) ^ ν := by
      have hp2 : ((-1 : SignType) ^ ν) * ((-1 : SignType) ^ ν) = 1 := by
        rcases Nat.even_or_odd ν with he | ho
        · rw [Even.neg_one_pow he]; decide
        · rw [Odd.neg_one_pow ho]; decide
      have htmp : ((-1 : SignType) ^ ν) *
          ((-1 : SignType) ^ ν *
            SignType.sign (((⇑derivative)^[ν + 1] P).eval c)) =
          ((-1 : SignType) ^ ν) * 1 := by rw [hL_one]
      rw [← mul_assoc, hp2, one_mul, mul_one] at htmp
      exact htmp
    -- Derive the R-level sign.
    have hpow_sign_R :
        SignType.sign ((-1 : R) ^ ν * ((⇑derivative)^[ν + 1] P).eval c)
          = 1 := by
      rw [sign_mul]
      -- sign((-1 : R)^ν) equals (-1 : SignType)^ν
      have hsignR : SignType.sign ((-1 : R) ^ ν) = (-1 : SignType) ^ ν := by
        rcases Nat.even_or_odd ν with he | ho
        · rw [Even.neg_one_pow he, Even.neg_one_pow he]; exact sign_one
        · rw [Odd.neg_one_pow ho, Odd.neg_one_pow ho]
          exact sign_neg (by norm_num : (-1 : R) < 0)
      rw [hsignR, hτ_eq_pow]
      rcases Nat.even_or_odd ν with he | ho
      · rw [Even.neg_one_pow he]; decide
      · rw [Odd.neg_one_pow ho]; decide
    have hpow_mul_pos : 0 < (-1 : R) ^ ν * ((⇑derivative)^[ν + 1] P).eval c :=
      sign_eq_one_iff.mp hpow_sign_R
    -- Goal: 0 < (-1)^(ν+1) · P(c) · P^(ν+1)(c).
    -- = -((-1)^ν · P(c) · P^(ν+1)(c)) = -P(c) · ((-1)^ν · P^(ν+1)(c))
    have : (-1 : R) ^ (ν + 1) * P.eval c * ((⇑derivative)^[ν + 1] P).eval c
        = (-P.eval c) * ((-1 : R) ^ ν * ((⇑derivative)^[ν + 1] P).eval c) := by
      ring
    rw [this]
    exact mul_pos (neg_pos.mpr hPc_neg) hpow_mul_pos
  · have hPxL_pos : 0 < P.eval xL := by
      have h := hs_PxL; rw [sign_pos hPc_pos] at h
      exact sign_eq_one_iff.mp h
    rw [abs_of_pos hPc_pos, abs_of_pos hPxL_pos] at hmin_xL
    -- |P(c)| ≤ |P(xL)| with both positive: P(c) ≤ P(xL), so P(c) - P(xL) ≤ 0.
    have hdiff_L_nonpos : P.eval c - P.eval xL ≤ 0 := by linarith
    have hdiff_L_neg : P.eval c - P.eval xL < 0 := by
      rcases eq_or_lt_of_le hdiff_L_nonpos with h | h
      · exfalso; apply hneg_τ_ne; rw [← hsign_diff_L, h, sign_zero]
      · exact h
    have hL_neg_one : SignType.sign (P.eval c - P.eval xL) = -1 :=
      sign_neg hdiff_L_neg
    rw [hsign_diff_L] at hL_neg_one
    -- (-1)^ν · τ = -1. So τ = -(-1)^ν = (-1)^(ν+1).
    have hτ_eq_pow : SignType.sign (((⇑derivative)^[ν + 1] P).eval c) =
        (-1 : SignType) ^ (ν + 1) := by
      have hp2 : ((-1 : SignType) ^ ν) * ((-1 : SignType) ^ ν) = 1 := by
        rcases Nat.even_or_odd ν with he | ho
        · rw [Even.neg_one_pow he]; decide
        · rw [Odd.neg_one_pow ho]; decide
      have hlhs : ((-1 : SignType) ^ ν) *
          ((-1 : SignType) ^ ν *
            SignType.sign (((⇑derivative)^[ν + 1] P).eval c)) =
          ((-1 : SignType) ^ ν) * (-1) := by rw [hL_neg_one]
      rw [← mul_assoc, hp2, one_mul] at hlhs
      rw [hlhs]; rw [pow_succ]
    have hpow_sign_R :
        SignType.sign ((-1 : R) ^ (ν + 1) * ((⇑derivative)^[ν + 1] P).eval c)
          = 1 := by
      rw [sign_mul]
      have hsignR : SignType.sign ((-1 : R) ^ (ν + 1))
          = (-1 : SignType) ^ (ν + 1) := by
        rcases Nat.even_or_odd (ν + 1) with he | ho
        · rw [Even.neg_one_pow he, Even.neg_one_pow he]; exact sign_one
        · rw [Odd.neg_one_pow ho, Odd.neg_one_pow ho]
          exact sign_neg (by norm_num : (-1 : R) < 0)
      rw [hsignR, hτ_eq_pow]
      rcases Nat.even_or_odd (ν + 1) with he | ho
      · rw [Even.neg_one_pow he]; decide
      · rw [Odd.neg_one_pow ho]; decide
    have hpow_mul_pos :
        0 < (-1 : R) ^ (ν + 1) * ((⇑derivative)^[ν + 1] P).eval c :=
      sign_eq_one_iff.mp hpow_sign_R
    have : (-1 : R) ^ (ν + 1) * P.eval c * ((⇑derivative)^[ν + 1] P).eval c
        = P.eval c * ((-1 : R) ^ (ν + 1) * ((⇑derivative)^[ν + 1] P).eval c) := by
      ring
    rw [this]
    exact mul_pos hPc_pos hpow_mul_pos

/-- **Left-boundary argmin.** If `c` is argmin of `|P|` on `[c, y]` with
    `c < y` and `P(c) ≠ 0`, then `0 < P(c) · P^(ν+1)(c)` where
    `ν := (derivative P).rootMultiplicity c`. (Note: no parity constraint on
    `ν`, unlike the interior case.) -/
lemma sign_of_isArgminAbsOn_left_boundary
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdP : derivative P ≠ 0) {c y : R}
    (hcy : c < y)
    (hc_argmin : IsArgminAbsOn P (Set.Icc c y) c)
    (hPc : P.eval c ≠ 0) :
    0 < P.eval c *
      ((⇑derivative)^[(derivative P).rootMultiplicity c + 1] P).eval c := by
  set ν := (derivative P).rootMultiplicity c with hν_def
  obtain ⟨_, hmin⟩ := hc_argmin
  have hP : P ≠ 0 := fun h => hPc (by simp [h])
  have hmult_P : P.rootMultiplicity c = 0 :=
    Polynomial.rootMultiplicity_eq_zero hPc
  have hshift : (⇑derivative)^[ν + 1] P = (⇑derivative)^[ν] (derivative P) := by
    rw [Function.iterate_succ, Function.comp_apply]
  have hP_ν_plus_one_ne : ((⇑derivative)^[ν + 1] P).eval c ≠ 0 := by
    rw [hshift]
    have h := Polynomial.eval_iterate_derivative_rootMultiplicity
      (p := derivative P) (t := c)
    rw [← hν_def] at h
    rw [h, nsmul_eq_mul]
    refine mul_ne_zero ?_
      (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hdP)
    exact_mod_cast Nat.factorial_ne_zero _
  have hP_sr : HasSignRight P c (SignType.sign (P.eval c)) := by
    have h := proposition_2_21_right hIVP hP c
    rw [hmult_P] at h; simpa using h
  have hP'_sr : HasSignRight (derivative P) c
      (SignType.sign (((⇑derivative)^[ν + 1] P).eval c)) := by
    have h := proposition_2_21_right hIVP hdP c
    rw [← hν_def, ← hshift] at h; exact h
  obtain ⟨bR, hbR, hsR⟩ := hP_sr
  obtain ⟨b'R, hb'R, hs'R⟩ := hP'_sr
  have hc_lt : c < min bR (min b'R y) := lt_min hbR (lt_min hb'R hcy)
  obtain ⟨xR, hcxR, hxRlt⟩ := exists_between hc_lt
  have hxR_lt_bR : xR < bR := lt_of_lt_of_le hxRlt (min_le_left _ _)
  have hxR_lt_b'R : xR < b'R := lt_of_lt_of_le hxRlt
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hxR_lt_y : xR < y := lt_of_lt_of_le hxRlt
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hs_PxR : SignType.sign (P.eval xR) = SignType.sign (P.eval c) :=
    hsR xR ⟨hcxR, hxR_lt_bR⟩
  obtain ⟨ξR, ⟨hcξR, hξRxR⟩, hmvt_R⟩ := corollary_2_23 hIVP P hcxR
  have hs_P'ξR : SignType.sign ((derivative P).eval ξR)
      = SignType.sign (((⇑derivative)^[ν + 1] P).eval c) :=
    hs'R ξR ⟨hcξR, hξRxR.trans hxR_lt_b'R⟩
  have hxRc_pos : 0 < xR - c := sub_pos.mpr hcxR
  have hsign_diff_R : SignType.sign (P.eval xR - P.eval c)
      = SignType.sign (((⇑derivative)^[ν + 1] P).eval c) := by
    rw [hmvt_R, sign_mul, sign_pos hxRc_pos, one_mul]; exact hs_P'ξR
  have hxR_mem : xR ∈ Set.Icc c y := ⟨hcxR.le, hxR_lt_y.le⟩
  have hmin_xR := hmin xR hxR_mem
  have hτ_ne : SignType.sign (((⇑derivative)^[ν + 1] P).eval c) ≠ 0 :=
    sign_ne_zero.mpr hP_ν_plus_one_ne
  rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
  · have hPxR_neg : P.eval xR < 0 := by
      have h := hs_PxR; rw [sign_neg hPc_neg] at h
      exact sign_eq_neg_one_iff.mp h
    rw [abs_of_neg hPc_neg, abs_of_neg hPxR_neg] at hmin_xR
    -- |P(c)| ≤ |P(xR)|, both negative: -P(c) ≤ -P(xR), so P(xR) ≤ P(c),
    -- hence P(xR) - P(c) ≤ 0 ⟹ τ ≤ 0 ⟹ τ = -1 ⟹ P^(ν+1)(c) < 0.
    have hdiff_R_nonpos : P.eval xR - P.eval c ≤ 0 := by linarith
    have hdiff_R_neg : P.eval xR - P.eval c < 0 := by
      rcases eq_or_lt_of_le hdiff_R_nonpos with h | h
      · exfalso; apply hτ_ne; rw [← hsign_diff_R, h, sign_zero]
      · exact h
    have hτ_eq : SignType.sign (((⇑derivative)^[ν + 1] P).eval c) = -1 := by
      rw [← hsign_diff_R]; exact sign_neg hdiff_R_neg
    have hP_ν_plus_one_neg : ((⇑derivative)^[ν + 1] P).eval c < 0 :=
      sign_eq_neg_one_iff.mp hτ_eq
    exact mul_pos_of_neg_of_neg hPc_neg hP_ν_plus_one_neg
  · have hPxR_pos : 0 < P.eval xR := by
      have h := hs_PxR; rw [sign_pos hPc_pos] at h
      exact sign_eq_one_iff.mp h
    rw [abs_of_pos hPc_pos, abs_of_pos hPxR_pos] at hmin_xR
    -- |P(c)| ≤ |P(xR)|, both positive: P(c) ≤ P(xR), so P(xR) - P(c) ≥ 0.
    have hdiff_R_nonneg : 0 ≤ P.eval xR - P.eval c := by linarith
    have hdiff_R_pos : 0 < P.eval xR - P.eval c := by
      rcases eq_or_lt_of_le hdiff_R_nonneg with h | h
      · exfalso; apply hτ_ne; rw [← hsign_diff_R, ← h, sign_zero]
      · exact h
    have hτ_eq : SignType.sign (((⇑derivative)^[ν + 1] P).eval c) = 1 := by
      rw [← hsign_diff_R]; exact sign_pos hdiff_R_pos
    have hP_ν_plus_one_pos : 0 < ((⇑derivative)^[ν + 1] P).eval c :=
      sign_eq_one_iff.mp hτ_eq
    exact mul_pos hPc_pos hP_ν_plus_one_pos

/-! ### Argmin located at an endpoint via monotonicity + sign at endpoint

When `P` is strictly monotonic on `[a, b]` and both `P(a)` and `P(b)` have
the same nonzero sign (so `P` has no root in the interval), `|P|` is strictly
monotonic in the matching direction, hence the argmin sits at a specific
endpoint. These are the converse-direction variants of the boundary Helper 2
lemmas and feed the c-block analysis. -/

/-- Strict-mono + `P(a) > 0` ⟹ argmin of `|P|` on `[a, b]` is `a`. -/
lemma argmin_eq_left_of_strictMono_pos
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a < b)
    (hdP_pos : ∀ x ∈ Set.Ioo a b, 0 < (derivative P).eval x)
    (hPa_pos : 0 < P.eval a)
    {z : R} (hz : IsArgminAbsOn P (Set.Icc a b) z) :
    z = a := by
  have hmono : StrictMonoOn (fun x => P.eval x) (Set.Icc a b) :=
    corollary_2_24_increasing hIVP P hab hdP_pos
  have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  have hPx_pos : ∀ x ∈ Set.Icc a b, 0 < P.eval x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hPa_pos
    · exact lt_of_lt_of_le hPa_pos (hmono.monotoneOn ha_mem hx h.le)
  have hPz_pos : 0 < P.eval z := hPx_pos z hz.1
  have habs : |P.eval a| ≤ |P.eval z| := by
    rw [abs_of_pos hPa_pos, abs_of_pos hPz_pos]
    exact hmono.monotoneOn ha_mem hz.1 hz.1.1
  have hz_min_a : |P.eval z| ≤ |P.eval a| := hz.2 a ha_mem
  have hPeq : P.eval a = P.eval z := by
    rw [abs_of_pos hPa_pos, abs_of_pos hPz_pos] at habs hz_min_a
    linarith
  exact (hmono.injOn ha_mem hz.1 hPeq).symm

/-- Strict-anti + `P(a) < 0` ⟹ argmin of `|P|` on `[a, b]` is `a`. -/
lemma argmin_eq_left_of_strictAnti_neg
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a < b)
    (hdP_neg : ∀ x ∈ Set.Ioo a b, (derivative P).eval x < 0)
    (hPa_neg : P.eval a < 0)
    {z : R} (hz : IsArgminAbsOn P (Set.Icc a b) z) :
    z = a := by
  have hanti : StrictAntiOn (fun x => P.eval x) (Set.Icc a b) :=
    corollary_2_24_decreasing hIVP P hab hdP_neg
  have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  have hPx_neg : ∀ x ∈ Set.Icc a b, P.eval x < 0 := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hPa_neg
    · exact lt_of_le_of_lt (hanti.antitoneOn ha_mem hx h.le) hPa_neg
  have hPz_neg : P.eval z < 0 := hPx_neg z hz.1
  have habs : |P.eval a| ≤ |P.eval z| := by
    rw [abs_of_neg hPa_neg, abs_of_neg hPz_neg, neg_le_neg_iff]
    exact hanti.antitoneOn ha_mem hz.1 hz.1.1
  have hz_min_a : |P.eval z| ≤ |P.eval a| := hz.2 a ha_mem
  have hPeq : P.eval a = P.eval z := by
    rw [abs_of_neg hPa_neg, abs_of_neg hPz_neg] at habs hz_min_a
    linarith
  exact (hanti.injOn ha_mem hz.1 hPeq).symm

/-- Strict-mono + `P(b) < 0` ⟹ argmin of `|P|` on `[a, b]` is `b`. -/
lemma argmin_eq_right_of_strictMono_neg
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a < b)
    (hdP_pos : ∀ x ∈ Set.Ioo a b, 0 < (derivative P).eval x)
    (hPb_neg : P.eval b < 0)
    {z : R} (hz : IsArgminAbsOn P (Set.Icc a b) z) :
    z = b := by
  have hmono : StrictMonoOn (fun x => P.eval x) (Set.Icc a b) :=
    corollary_2_24_increasing hIVP P hab hdP_pos
  have hb_mem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab.le
  have hPx_neg : ∀ x ∈ Set.Icc a b, P.eval x < 0 := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · rw [h]; exact hPb_neg
    · exact lt_of_lt_of_le (hmono hx hb_mem h) hPb_neg.le
  have hPz_neg : P.eval z < 0 := hPx_neg z hz.1
  have habs : |P.eval b| ≤ |P.eval z| := by
    rw [abs_of_neg hPb_neg, abs_of_neg hPz_neg, neg_le_neg_iff]
    exact hmono.monotoneOn hz.1 hb_mem hz.1.2
  have hz_min_b : |P.eval z| ≤ |P.eval b| := hz.2 b hb_mem
  have hPeq : P.eval b = P.eval z := by
    rw [abs_of_neg hPb_neg, abs_of_neg hPz_neg] at habs hz_min_b
    linarith
  exact (hmono.injOn hb_mem hz.1 hPeq).symm

/-- Strict-anti + `P(b) > 0` ⟹ argmin of `|P|` on `[a, b]` is `b`. -/
lemma argmin_eq_right_of_strictAnti_pos
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {a b : R} (hab : a < b)
    (hdP_neg : ∀ x ∈ Set.Ioo a b, (derivative P).eval x < 0)
    (hPb_pos : 0 < P.eval b)
    {z : R} (hz : IsArgminAbsOn P (Set.Icc a b) z) :
    z = b := by
  have hanti : StrictAntiOn (fun x => P.eval x) (Set.Icc a b) :=
    corollary_2_24_decreasing hIVP P hab hdP_neg
  have hb_mem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab.le
  have hPx_pos : ∀ x ∈ Set.Icc a b, 0 < P.eval x := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · rw [h]; exact hPb_pos
    · exact lt_of_lt_of_le hPb_pos (hanti.antitoneOn hx hb_mem h.le)
  have hPz_pos : 0 < P.eval z := hPx_pos z hz.1
  have habs : |P.eval b| ≤ |P.eval z| := by
    rw [abs_of_pos hPb_pos, abs_of_pos hPz_pos]
    exact hanti.antitoneOn hz.1 hb_mem hz.1.2
  have hz_min_b : |P.eval z| ≤ |P.eval b| := hz.2 b hb_mem
  have hPeq : P.eval b = P.eval z := by
    rw [abs_of_pos hPb_pos, abs_of_pos hPz_pos] at habs hz_min_b
    linarith
  exact (hanti.injOn hb_mem hz.1 hPeq).symm

/-- If `P'` has sign opposite to `P(c)` throughout `(v, c)`, then any argmin of
    `|P|` on `[v, c]` equals `c`. Combines strict monotonicity from the sign of
    `P'` with the appropriate converse argmin helper. -/
private lemma argmin_right_of_derivSign_opp
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {v c : R} (hvc : v < c)
    (hPc : P.eval c ≠ 0)
    (hsign_opp : ∀ x ∈ Set.Ioo v c,
      SignType.sign ((derivative P).eval x) = -SignType.sign (P.eval c))
    {z : R} (harg : IsArgminAbsOn P (Set.Icc v c) z) :
    z = c := by
  rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
  · have hder_pos : ∀ x ∈ Set.Ioo v c, 0 < (derivative P).eval x := by
      intro x hx
      have h := hsign_opp x hx
      rw [sign_neg hPc_neg, neg_neg] at h
      exact sign_eq_one_iff.mp h
    exact argmin_eq_right_of_strictMono_neg hIVP hvc hder_pos hPc_neg harg
  · have hder_neg : ∀ x ∈ Set.Ioo v c, (derivative P).eval x < 0 := by
      intro x hx
      have h := hsign_opp x hx
      rw [sign_pos hPc_pos] at h
      exact sign_eq_neg_one_iff.mp h
    exact argmin_eq_right_of_strictAnti_pos hIVP hvc hder_neg hPc_pos harg

/-- If `P'` has sign equal to `P(c)` throughout `(c, y)`, then any argmin of
    `|P|` on `[c, y]` equals `c`. -/
private lemma argmin_left_of_derivSign_same
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {c y : R} (hcy : c < y)
    (hPc : P.eval c ≠ 0)
    (hsign_same : ∀ x ∈ Set.Ioo c y,
      SignType.sign ((derivative P).eval x) = SignType.sign (P.eval c))
    {z : R} (harg : IsArgminAbsOn P (Set.Icc c y) z) :
    z = c := by
  rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
  · have hder_neg : ∀ x ∈ Set.Ioo c y, (derivative P).eval x < 0 := by
      intro x hx
      have h := hsign_same x hx
      rw [sign_neg hPc_neg] at h
      exact sign_eq_neg_one_iff.mp h
    exact argmin_eq_left_of_strictAnti_neg hIVP hcy hder_neg hPc_neg harg
  · have hder_pos : ∀ x ∈ Set.Ioo c y, 0 < (derivative P).eval x := by
      intro x hx
      have h := hsign_same x hx
      rw [sign_pos hPc_pos] at h
      exact sign_eq_one_iff.mp h
    exact argmin_eq_left_of_strictMono_pos hIVP hcy hder_pos hPc_pos harg

/-- `Ici c` version: if `P'` has sign equal to `P(c)` throughout `(c, +∞)`, then
    any argmin of `|P|` on `Ici c` equals `c`. -/
private lemma argmin_left_of_derivSign_same_Ici
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {c : R}
    (hPc : P.eval c ≠ 0)
    (hsign_same : ∀ x ∈ Set.Ioi c,
      SignType.sign ((derivative P).eval x) = SignType.sign (P.eval c))
    {z : R} (harg : IsArgminAbsOn P (Set.Ici c) z) :
    z = c := by
  obtain ⟨hc_le_z, hmin⟩ := harg
  rcases eq_or_lt_of_le hc_le_z with h_eq | h_lt
  · exact h_eq.symm
  exfalso
  have hc_mem : c ∈ Set.Ici c := Set.self_mem_Ici
  have hmin_c := hmin c hc_mem
  rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
  · have hder_neg : ∀ x ∈ Set.Ioo c z, (derivative P).eval x < 0 := by
      intro x hx
      have h := hsign_same x hx.1
      rw [sign_neg hPc_neg] at h
      exact sign_eq_neg_one_iff.mp h
    have hanti : StrictAntiOn (fun x => P.eval x) (Set.Icc c z) :=
      corollary_2_24_decreasing hIVP P h_lt hder_neg
    have hPz_lt : P.eval z < P.eval c :=
      hanti (Set.left_mem_Icc.mpr h_lt.le) (Set.right_mem_Icc.mpr h_lt.le) h_lt
    have hPz_neg : P.eval z < 0 := hPz_lt.trans hPc_neg
    rw [abs_of_neg hPc_neg, abs_of_neg hPz_neg] at hmin_c
    linarith
  · have hder_pos : ∀ x ∈ Set.Ioo c z, 0 < (derivative P).eval x := by
      intro x hx
      have h := hsign_same x hx.1
      rw [sign_pos hPc_pos] at h
      exact sign_eq_one_iff.mp h
    have hmono : StrictMonoOn (fun x => P.eval x) (Set.Icc c z) :=
      corollary_2_24_increasing hIVP P h_lt hder_pos
    have hPc_lt : P.eval c < P.eval z :=
      hmono (Set.left_mem_Icc.mpr h_lt.le) (Set.right_mem_Icc.mpr h_lt.le) h_lt
    have hPz_pos : 0 < P.eval z := hPc_pos.trans hPc_lt
    rw [abs_of_pos hPc_pos, abs_of_pos hPz_pos] at hmin_c
    linarith

/-- `Iic c` version: if `P'` has sign opposite to `P(c)` throughout `(−∞, c)`,
    then any argmin of `|P|` on `Iic c` equals `c`. -/
private lemma argmin_right_of_derivSign_opp_Iic
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {c : R}
    (hPc : P.eval c ≠ 0)
    (hsign_opp : ∀ x ∈ Set.Iio c,
      SignType.sign ((derivative P).eval x) = -SignType.sign (P.eval c))
    {z : R} (harg : IsArgminAbsOn P (Set.Iic c) z) :
    z = c := by
  obtain ⟨hz_le_c, hmin⟩ := harg
  rcases eq_or_lt_of_le hz_le_c with h_eq | h_lt
  · exact h_eq
  exfalso
  have hc_mem : c ∈ Set.Iic c := Set.self_mem_Iic
  have hmin_c := hmin c hc_mem
  rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
  · have hder_pos : ∀ x ∈ Set.Ioo z c, 0 < (derivative P).eval x := by
      intro x hx
      have h := hsign_opp x hx.2
      rw [sign_neg hPc_neg, neg_neg] at h
      exact sign_eq_one_iff.mp h
    have hmono : StrictMonoOn (fun x => P.eval x) (Set.Icc z c) :=
      corollary_2_24_increasing hIVP P h_lt hder_pos
    have hPz_lt : P.eval z < P.eval c :=
      hmono (Set.left_mem_Icc.mpr h_lt.le) (Set.right_mem_Icc.mpr h_lt.le) h_lt
    have hPz_neg : P.eval z < 0 := hPz_lt.trans hPc_neg
    rw [abs_of_neg hPc_neg, abs_of_neg hPz_neg] at hmin_c
    linarith
  · have hder_neg : ∀ x ∈ Set.Ioo z c, (derivative P).eval x < 0 := by
      intro x hx
      have h := hsign_opp x hx.2
      rw [sign_pos hPc_pos] at h
      exact sign_eq_neg_one_iff.mp h
    have hanti : StrictAntiOn (fun x => P.eval x) (Set.Icc z c) :=
      corollary_2_24_decreasing hIVP P h_lt hder_neg
    have hPc_lt : P.eval c < P.eval z :=
      hanti (Set.left_mem_Icc.mpr h_lt.le) (Set.right_mem_Icc.mpr h_lt.le) h_lt
    have hPz_pos : 0 < P.eval z := hPc_pos.trans hPc_lt
    rw [abs_of_pos hPc_pos, abs_of_pos hPz_pos] at hmin_c
    linarith

omit [IsStrictOrderedRing R] in
/-- **c-block walker.** If `ArgminPartitionFrom P c xs ys` with `ys` starting
    with `m` copies of `c`, then `xs` starts with `m` copies of `c` and the
    residual structure is `ArgminPartitionFrom P c xs_rest ys_rest`. -/
private lemma argminPartitionFrom_c_prefix
    {P : R[X]} {c : R} (m : ℕ) : ∀ {xs ys : List R},
    ArgminPartitionFrom P c xs (List.replicate m c ++ ys) →
    ∃ xs_rest : List R,
      xs = List.replicate m c ++ xs_rest ∧
      ArgminPartitionFrom P c xs_rest ys := by
  induction m with
  | zero => intro xs ys h; exact ⟨xs, by simp, by simpa using h⟩
  | succ m ih =>
    intro xs ys h
    have hrepl_eq : List.replicate (m + 1) c ++ ys =
        c :: (List.replicate m c ++ ys) := by
      simp [List.replicate, List.cons_append]
    rw [hrepl_eq] at h
    match xs, h with
    | [], h => exact absurd h (by simp [ArgminPartitionFrom])
    | [_], h => exact absurd h (by simp [ArgminPartitionFrom])
    | x :: x' :: xs'', h =>
      change IsArgminAbsOn P (Set.Icc c c) x ∧
        ArgminPartitionFrom P c (x' :: xs'') (List.replicate m c ++ ys) at h
      obtain ⟨hx_argmin, hrest⟩ := h
      have hx_eq : x = c := le_antisymm hx_argmin.1.2 hx_argmin.1.1
      subst hx_eq
      obtain ⟨xs_rest, hxs_eq, hrest'⟩ := ih hrest
      refine ⟨xs_rest, ?_, hrest'⟩
      rw [List.replicate, List.cons_append, hxs_eq]

omit [IsStrictOrderedRing R] in
/-- In an `ArgminPartitionFrom P a xs ys`, every entry of `xs` lies in the union
    of the closed intervals in the partition. In particular, each entry is at
    least `a`. -/
private lemma argminPartitionFrom_mem_ge
    {P : R[X]} {a : R} : ∀ {xs ys : List R},
    ArgminPartitionFrom P a xs ys →
    ∀ z ∈ xs, a ≤ z := by
  intro xs ys harg z hz
  induction ys generalizing xs a with
  | nil =>
    match xs, harg with
    | [w], harg =>
      change IsArgminAbsOn P (Set.Ici a) w at harg
      rcases List.mem_cons.mp hz with rfl | h
      · exact harg.1
      · exact absurd h List.not_mem_nil
    | [], harg => exact absurd harg (by simp [ArgminPartitionFrom])
    | _ :: _ :: _, harg => exact absurd harg (by simp [ArgminPartitionFrom])
  | cons y ys' ih =>
    match xs, harg with
    | [], harg => exact absurd harg (by simp [ArgminPartitionFrom])
    | [_], harg => exact absurd harg (by simp [ArgminPartitionFrom])
    | x :: x' :: xs'', harg =>
      change IsArgminAbsOn P (Set.Icc a y) x ∧
        ArgminPartitionFrom P y (x' :: xs'') ys' at harg
      obtain ⟨hx_arg, harg_rest⟩ := harg
      rcases List.mem_cons.mp hz with rfl | h
      · exact hx_arg.1.1
      · have hay : a ≤ y := hx_arg.1.1.trans hx_arg.1.2
        exact hay.trans (ih harg_rest h)

omit [IsStrictOrderedRing R] in
/-- In an `ArgminPartitionFrom P a xs ys`, the tail of `xs` (past the first
    entry) lies in `Ici (first entry of ys)` (or trivially empty). -/
private lemma argminPartitionFrom_tail_ge_head
    {P : R[X]} {a y : R} {ys' : List R} : ∀ {xs : List R},
    ArgminPartitionFrom P a xs (y :: ys') →
    ∀ z ∈ xs.tail, y ≤ z := by
  intro xs harg z hz
  match xs, harg with
  | [], harg => exact absurd harg (by simp [ArgminPartitionFrom])
  | [_], harg => exact absurd harg (by simp [ArgminPartitionFrom])
  | x :: x' :: xs'', harg =>
    change IsArgminAbsOn P (Set.Icc a y) x ∧
      ArgminPartitionFrom P y (x' :: xs'') ys' at harg
    obtain ⟨_, harg_rest⟩ := harg
    exact argminPartitionFrom_mem_ge harg_rest z hz

omit [IsStrictOrderedRing R] in
/-- **Full c-block decomposition.** Given `ArgminPartitionFrom P c xs ys`
    with every `z ∈ ys` satisfying `c ≤ z`, peel off the maximal c-prefix of
    `ys` (of length `m`) and the matching c-prefix of `xs`. The residual
    `ys_rest` is either empty or begins with an element strictly greater than
    `c`. -/
private lemma argminPartitionFrom_c_split
    (P : R[X]) (c : R) : ∀ (ys : List R) (xs : List R),
    (∀ z ∈ ys, c ≤ z) →
    ArgminPartitionFrom P c xs ys →
    ∃ (m : ℕ) (xs_rest ys_rest : List R),
      ys = List.replicate m c ++ ys_rest ∧
      xs = List.replicate m c ++ xs_rest ∧
      ArgminPartitionFrom P c xs_rest ys_rest ∧
      (ys_rest = [] ∨ ∃ z ys_r, ys_rest = z :: ys_r ∧ c < z) := by
  intro ys
  induction ys with
  | nil =>
    intro xs _ harg
    exact ⟨0, xs, [], rfl, by simp, by simpa using harg, Or.inl rfl⟩
  | cons z ys' ih =>
    intro xs hge harg
    rcases eq_or_lt_of_le (hge z List.mem_cons_self) with hcz | hcz
    · -- hcz : c = z
      rw [← hcz] at harg
      -- harg : ArgminPartitionFrom P c xs (c :: ys')
      match xs, harg with
      | [], harg => exact absurd harg (by simp [ArgminPartitionFrom])
      | [_], harg => exact absurd harg (by simp [ArgminPartitionFrom])
      | x :: x' :: xs'', harg =>
        change IsArgminAbsOn P (Set.Icc c c) x ∧
          ArgminPartitionFrom P c (x' :: xs'') ys' at harg
        obtain ⟨hx_arg, hrest⟩ := harg
        have hx_eq : x = c := le_antisymm hx_arg.1.2 hx_arg.1.1
        have hge' : ∀ z' ∈ ys', c ≤ z' := fun z' hz' =>
          hge z' (List.mem_cons_of_mem _ hz')
        obtain ⟨m, xs_rest, ys_rest, hys_eq, hxs_eq, harg_rest, hend⟩ :=
          ih (x' :: xs'') hge' hrest
        refine ⟨m + 1, xs_rest, ys_rest, ?_, ?_, harg_rest, hend⟩
        · rw [← hcz, List.replicate_succ, List.cons_append]; exact congrArg _ hys_eq
        · rw [hx_eq, List.replicate_succ, List.cons_append]; exact congrArg _ hxs_eq
    · exact ⟨0, xs, z :: ys', rfl, by simp, by simpa using harg,
             Or.inr ⟨z, ys', rfl, hcz⟩⟩

omit [IsStrictOrderedRing R] in
/-- **Boundary count in the c-block tail.** If `ArgminPartitionFrom P c xs ys`
    where `ys` is sorted and either empty or begins with some `z > c`, then
    `xs = w :: xs_tail` with `xs.count c = 𝟙(w = c)` and `ys.count c = 0`.
    When `ys = []`, `w` is the argmin of `|P|` on `Ici c`; when
    `ys = z :: ys_r`, `w` is the argmin on `[c, z]`. -/
private lemma argminPartitionFrom_c_tail_count
    {P : R[X]} {c : R} {xs ys : List R}
    (harg : ArgminPartitionFrom P c xs ys)
    (hys_sort : ys.Pairwise (· ≤ ·))
    (hend : ys = [] ∨ ∃ z ys_r, ys = z :: ys_r ∧ c < z) :
    ∃ w : R, ∃ xs_tail : List R,
      xs = w :: xs_tail ∧
      xs.count c = (if w = c then 1 else 0) ∧
      ys.count c = 0 ∧
      ((ys = [] ∧ IsArgminAbsOn P (Set.Ici c) w) ∨
       (∃ z ys_r, ys = z :: ys_r ∧ c < z ∧ IsArgminAbsOn P (Set.Icc c z) w)) := by
  rcases hend with hys | ⟨z, ys_r, hys, hcz⟩
  · -- ys = []
    subst hys
    match xs, harg with
    | [], h => exact absurd h (by simp [ArgminPartitionFrom])
    | _ :: _ :: _, h => exact absurd h (by simp [ArgminPartitionFrom])
    | [w], h =>
      change IsArgminAbsOn P (Set.Ici c) w at h
      refine ⟨w, [], rfl, ?_, rfl, Or.inl ⟨rfl, h⟩⟩
      by_cases hw : w = c
      · simp [hw]
      · rw [List.count_cons_of_ne hw, List.count_nil]; simp [hw]
  · -- ys = z :: ys_r, c < z
    subst hys
    have hys_r_ge : ∀ a ∈ ys_r, z ≤ a :=
      (List.pairwise_cons.mp hys_sort).1
    match xs, harg with
    | [], h => exact absurd h (by simp [ArgminPartitionFrom])
    | [_], h => exact absurd h (by simp [ArgminPartitionFrom])
    | w :: w' :: ws, h =>
      change IsArgminAbsOn P (Set.Icc c z) w ∧
        ArgminPartitionFrom P z (w' :: ws) ys_r at h
      obtain ⟨hw_arg, h_rest⟩ := h
      have hws_ge : ∀ a ∈ w' :: ws, z ≤ a :=
        argminPartitionFrom_mem_ge h_rest
      have hys_count : (z :: ys_r).count c = 0 := by
        refine List.count_eq_zero.mpr (fun hm => ?_)
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hcz.ne' rfl
        · exact ((hcz.trans_le (hys_r_ge _ hm)).ne' rfl)
      have hws_count : (w' :: ws).count c = 0 :=
        List.count_eq_zero.mpr
          (fun hm => ((hcz.trans_le (hws_ge _ hm)).ne' rfl))
      refine ⟨w, w' :: ws, rfl, ?_, hys_count,
        Or.inr ⟨z, ys_r, rfl, hcz, hw_arg⟩⟩
      by_cases hw : w = c
      · rw [hw, List.count_cons_self, hws_count]; simp
      · rw [List.count_cons_of_ne hw, hws_count]; simp [hw]

/-! ### The natDegree = 2 case

When `P.natDegree = 2`, `P.derivative` has `natDegree = 1`, so its virtual
roots list has the form `[v]` where `v` is the unique root of `P'`. The `P'`
sign dichotomy on `Iio v` and `Ioi v` gives `P` strictly monotonic on each of
`Iic v` and `Ici v`. Picking the argmin of `|P|` on each of those half-infinite
intervals yields a length-2 virtual roots list `[x₁, x₂]` for `P`. -/

/-- When `natDegree P = 2` and `[v]` is a virtual roots list of `P'`, the pair
    `[x₁, x₂]` with `x₁ = argmin_{Iic v} |P|` and `x₂ = argmin_{Ici v} |P|`
    is a virtual roots list of `P`, interlaced with `[v]`. -/
theorem exists_virtualRootsList_of_natDegree_two
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdeg : P.natDegree = 2) {v : R}
    (hys : IsVirtualRootsList P.derivative [v]) :
    ∃ xs : List R, IsVirtualRootsList P xs ∧ Interlaced xs [v] := by
  have hdeg_pos : 0 < P.natDegree := by rw [hdeg]; norm_num
  have hdP_deg : (derivative P).natDegree = 1 := by
    have h : (derivative P).degree = (P.natDegree - 1 : ℕ) :=
      Polynomial.degree_derivative_eq P hdeg_pos
    have h' : (derivative P).natDegree = P.natDegree - 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some h
    rw [h', hdeg]
  have hle_Iio : ∀ r ∈ ([v] : List R), v ≤ r := by
    intro r hr; rw [List.mem_singleton] at hr; rw [hr]
  have hle_Ioi : ∀ r ∈ ([v] : List R), r ≤ v := by
    intro r hr; rw [List.mem_singleton] at hr; rw [hr]
  have hdich_Iio := sign_dichotomy_Iio hys.sign_const hle_Iio
  have hdich_Ioi := sign_dichotomy_Ioi hys.sign_const hle_Ioi
  obtain ⟨x₁, hx₁_mem, hx₁_min, _hx₁_wit⟩ :=
    exists_argmin_abs_on_Iic_of_deriv_dichotomy hIVP hdeg_pos hdich_Iio
  obtain ⟨x₂, hx₂_mem, hx₂_min, _hx₂_wit⟩ :=
    exists_argmin_abs_on_Ici_of_deriv_dichotomy hIVP hdeg_pos hdich_Ioi
  have hx₁v : x₁ ≤ v := hx₁_mem
  have hvx₂ : v ≤ x₂ := hx₂_mem
  have hx₁x₂ : x₁ ≤ x₂ := le_trans hx₁v hvx₂
  have hys_aux : IsVirtualRootsListAux 1 (derivative P) [v] := by
    have h := hys
    unfold IsVirtualRootsList at h
    rw [hdP_deg] at h
    exact h
  refine ⟨[x₁, x₂], ?_, ?_⟩
  · unfold IsVirtualRootsList
    rw [hdeg]
    refine ⟨?_, ?_, ?_, Or.inr ⟨[v], hys_aux, ?_, ?_, ?_⟩⟩
    · simp [hdeg]
    · refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
      intro b hb; rw [List.mem_singleton] at hb; rw [hb]; exact hx₁x₂
    · -- SignConstantOnGaps P [x₁, x₂]
      intro x y hxy hgap
      have hgap1 : x₁ < x ∨ y < x₁ := hgap x₁ (by simp)
      have hgap2 : x₂ < x ∨ y < x₂ := hgap x₂ (by simp)
      -- Helper: invoke the Iic argmin sign-const in either mono or anti branch
      have iic_case : ∀ {x' y' : R}, x' ≤ y' → x' ≤ v → y' ≤ v →
          (x₁ < x' ∨ y' < x₁) →
          P.eval x' ≠ 0 ∧ SignType.sign (P.eval x') = SignType.sign (P.eval y') := by
        intro x' y' hxy' hxv hyv hgap'
        rcases hdich_Iio with hpos | hneg
        · exact sign_const_of_argmin_strictMonoOn_Iic hIVP
            (strictMonoOn_of_deriv_pos_Iic hIVP hpos)
            hx₁_mem hx₁_min hxy' hxv hyv hgap'
        · exact sign_const_of_argmin_strictAntiOn_Iic hIVP
            (strictAntiOn_of_deriv_neg_Iic hIVP hneg)
            hx₁_mem hx₁_min hxy' hxv hyv hgap'
      have ici_case : ∀ {x' y' : R}, x' ≤ y' → v ≤ x' → v ≤ y' →
          (x₂ < x' ∨ y' < x₂) →
          P.eval x' ≠ 0 ∧ SignType.sign (P.eval x') = SignType.sign (P.eval y') := by
        intro x' y' hxy' hvx hvy hgap'
        rcases hdich_Ioi with hpos | hneg
        · exact sign_const_of_argmin_strictMonoOn_Ici hIVP
            (strictMonoOn_of_deriv_pos_Ici hIVP hpos)
            hx₂_mem hx₂_min hxy' hvx hvy hgap'
        · exact sign_const_of_argmin_strictAntiOn_Ici hIVP
            (strictAntiOn_of_deriv_neg_Ici hIVP hneg)
            hx₂_mem hx₂_min hxy' hvx hvy hgap'
      -- Case split on position of [x, y] relative to x₁, x₂, v
      rcases lt_or_ge y x₁ with hy_x₁ | hy_ge
      · -- y < x₁: entirely below x₁, so [x,y] ⊆ Iic v
        have hxv : x ≤ v := le_trans hxy (le_trans (le_of_lt hy_x₁) hx₁v)
        have hyv : y ≤ v := le_trans (le_of_lt hy_x₁) hx₁v
        exact iic_case hxy hxv hyv (Or.inr hy_x₁)
      · -- x₁ ≤ y
        have hx₁x : x₁ < x := hgap1.resolve_right (not_lt.mpr hy_ge)
        rcases le_or_gt x x₂ with hxx₂ | hx₂x
        · -- x ≤ x₂
          have hyx₂ : y < x₂ := hgap2.resolve_left (not_lt.mpr hxx₂)
          rcases le_or_gt y v with hyv | hvy
          · -- y ≤ v: Iic case
            have hxv : x ≤ v := le_trans hxy hyv
            exact iic_case hxy hxv hyv (Or.inl hx₁x)
          · rcases le_or_gt v x with hvx | hxv
            · -- v ≤ x: Ici case
              exact ici_case hxy hvx (le_trans hvx hxy) (Or.inr hyx₂)
            · -- x < v < y: straddle — glue via sign at v
              have hxv' : x ≤ v := le_of_lt hxv
              have hvy' : v ≤ y := le_of_lt hvy
              obtain ⟨hPx_ne, hsign_xv⟩ :=
                iic_case hxv' hxv' (le_refl v) (Or.inl hx₁x)
              obtain ⟨_, hsign_vy⟩ :=
                ici_case hvy' (le_refl v) hvy' (Or.inr hyx₂)
              exact ⟨hPx_ne, hsign_xv.trans hsign_vy⟩
        · -- x₂ < x: Ici case
          have hvx : v ≤ x := le_trans hvx₂ (le_of_lt hx₂x)
          exact ici_case hxy hvx (le_trans hvx hxy) (Or.inl hx₂x)
    · -- Interlaced [x₁, x₂] [v]
      exact ⟨hx₁v, hvx₂, trivial⟩
    · -- IsArgminAbsOn P (Set.Iic v) x₁
      exact ⟨hx₁_mem, hx₁_min⟩
    · -- ArgminPartitionFrom P v [x₂] [] = IsArgminAbsOn P (Set.Ici v) x₂
      exact ⟨hx₂_mem, hx₂_min⟩
  · -- Interlaced [x₁, x₂] [v]
    exact ⟨hx₁v, hvx₂, trivial⟩

/-! ### General inductive step: arbitrary length `ys`

For a polynomial `P` of any degree `≥ 1`, given a virtual roots list `ys` of
`P'`, we build a virtual roots list `xs` of `P`. The construction recurses on
`ys`: given a "prev" anchor `v_prev` (the virtual root we just passed) and a
"remaining" sub-list `ys_rest`, we produce the remaining argmins.

At each step we need the sign-constancy hypothesis on the full list; we thread
the split `ys_full = past ++ v_prev :: ys_rest` so the IH can advance with
`past' = past ++ [v_prev]`, `v_prev' = head of ys_rest`. -/

omit [Field R] [IsStrictOrderedRing R] in
/-- Consequences of a sorted split: all past elements are `≤ v_prev`, `v_prev`
    is `≤` all rest elements, and the rest is itself sorted. -/
lemma sorted_split_le
    {past : List R} {v_prev : R} {rest : List R}
    (h : (past ++ v_prev :: rest).Pairwise (· ≤ ·)) :
    (∀ a ∈ past, a ≤ v_prev) ∧ (∀ b ∈ rest, v_prev ≤ b) ∧ rest.Pairwise (· ≤ ·) := by
  rw [List.pairwise_append] at h
  obtain ⟨_, h_tail, h_cross⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro a ha; exact h_cross a ha v_prev List.mem_cons_self
  · intro b hb; exact (List.pairwise_cons.mp h_tail).1 b hb
  · exact (List.pairwise_cons.mp h_tail).2

omit [Field R] [IsStrictOrderedRing R] in
/-- Gap closure across a `v_prev :: v' :: _` split: every element of `ys_full`
    is either `≤ v_prev` or `≥ v'`. -/
lemma gap_closure_adjacent
    {past : List R} {v_prev v' : R} {ys_rest : List R} {ys_full : List R}
    (hsplit : ys_full = past ++ v_prev :: v' :: ys_rest)
    (hsorted : ys_full.Pairwise (· ≤ ·)) :
    ∀ r ∈ ys_full, r ≤ v_prev ∨ v' ≤ r := by
  intro r hr
  rw [hsplit] at hr
  rcases List.mem_append.mp hr with hr_past | hr_cons
  · left
    rw [hsplit] at hsorted
    exact (sorted_split_le hsorted).1 r hr_past
  · rcases List.mem_cons.mp hr_cons with rfl | hr_tail
    · left; exact le_refl _
    · right
      rw [hsplit] at hsorted
      have ⟨_, hv_prev_le_rest, hrest_sorted⟩ := sorted_split_le hsorted
      -- hr_tail : r ∈ v' :: ys_rest
      rcases List.mem_cons.mp hr_tail with rfl | hr_ys_rest
      · exact le_refl _
      · exact (List.pairwise_cons.mp hrest_sorted).1 r hr_ys_rest

omit [Field R] [IsStrictOrderedRing R] in
/-- Right-tail gap closure: when `v_prev` is the *last* element of `ys_full`
    (i.e., `ys_rest = []`), every element of `ys_full` is `≤ v_prev`. -/
lemma gap_closure_last
    {past : List R} {v_prev : R} {ys_full : List R}
    (hsplit : ys_full = past ++ v_prev :: [])
    (hsorted : ys_full.Pairwise (· ≤ ·)) :
    ∀ r ∈ ys_full, r ≤ v_prev := by
  intro r hr
  rw [hsplit] at hr hsorted
  rcases List.mem_append.mp hr with hr_past | hr_cons
  · exact (sorted_split_le hsorted).1 r hr_past
  · rw [List.mem_singleton] at hr_cons; exact hr_cons.le

/-- The core induction: given `ys_full` a sorted list with sign-constancy on
    gaps for `P'`, and a split `ys_full = past ++ v_prev :: ys_rest`, build an
    xs_tail of length `ys_rest.length + 1` that captures the argmins on the
    closed intervals starting at `v_prev`, packaged as an `ArgminPartitionFrom`
    witness. -/
lemma exists_buildTail (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdeg_pos : 0 < P.natDegree)
    (ys_full : List R)
    (hsorted_full : ys_full.Pairwise (· ≤ ·))
    (hsc_full : SignConstantOnGaps (derivative P) ys_full) :
    ∀ (ys_rest : List R) (past : List R) (v_prev : R),
      ys_full = past ++ v_prev :: ys_rest →
    ∃ (x_head : R) (xs_rest : List R),
      (x_head :: xs_rest).length = ys_rest.length + 1 ∧
      (x_head :: xs_rest).Pairwise (· ≤ ·) ∧
      v_prev ≤ x_head ∧
      Interlaced (x_head :: xs_rest) ys_rest ∧
      (∀ x y : R, v_prev ≤ x → x ≤ y →
        (∀ r ∈ x_head :: xs_rest, r < x ∨ y < r) →
        P.eval x ≠ 0 ∧ SignType.sign (P.eval x) = SignType.sign (P.eval y)) ∧
      ArgminPartitionFrom P v_prev (x_head :: xs_rest) ys_rest := by
  intro ys_rest
  induction ys_rest with
  | nil =>
    intro past v_prev hsplit
    -- x_head = argmin on Ici v_prev
    have hle_Ioi : ∀ r ∈ ys_full, r ≤ v_prev := gap_closure_last hsplit hsorted_full
    have hdich : (∀ x ∈ Set.Ioi v_prev, 0 < (derivative P).eval x) ∨
                 (∀ x ∈ Set.Ioi v_prev, (derivative P).eval x < 0) :=
      sign_dichotomy_Ioi hsc_full hle_Ioi
    obtain ⟨x_p, hx_p_mem, hx_p_min, _hx_p_wit⟩ :=
      exists_argmin_abs_on_Ici_of_deriv_dichotomy hIVP hdeg_pos hdich
    refine ⟨x_p, [], rfl, List.pairwise_singleton _ _, hx_p_mem, trivial, ?_, ?_⟩
    · -- sign-const
      intro x y hv_prev_x hxy hgap
      have hgap_x_p := hgap x_p List.mem_cons_self
      have hx_mem : x ∈ Set.Ici v_prev := hv_prev_x
      have hy_mem : y ∈ Set.Ici v_prev := le_trans hv_prev_x hxy
      rcases hdich with hpos | hneg
      · exact sign_const_of_argmin_strictMonoOn_Ici hIVP
          (strictMonoOn_of_deriv_pos_Ici hIVP hpos)
          hx_p_mem hx_p_min hxy hx_mem hy_mem hgap_x_p
      · exact sign_const_of_argmin_strictAntiOn_Ici hIVP
          (strictAntiOn_of_deriv_neg_Ici hIVP hneg)
          hx_p_mem hx_p_min hxy hx_mem hy_mem hgap_x_p
    · -- ArgminPartitionFrom P v_prev [x_p] [] = IsArgminAbsOn P (Set.Ici v_prev) x_p
      exact ⟨hx_p_mem, hx_p_min⟩
  | cons v' ys'' ih =>
    intro past v_prev hsplit
    -- Derive sortedness on (v_prev :: v' :: ys'') by reading off sorted_full.
    have hsorted_tail : (v_prev :: v' :: ys'').Pairwise (· ≤ ·) := by
      rw [hsplit] at hsorted_full
      exact ((List.pairwise_append.mp hsorted_full).2.1)
    have hv_prev_le_v' : v_prev ≤ v' :=
      (List.pairwise_cons.mp hsorted_tail).1 v' List.mem_cons_self
    -- Need v_prev < v' for interior dichotomy. Handle v_prev = v' separately.
    rcases eq_or_lt_of_le hv_prev_le_v' with hveq | hvlt
    · -- v_prev = v'. Use x_head := v_prev, recurse for the rest.
      obtain ⟨x_next, xs_more, hlen_ih, hpw_ih, hv'_le_next, hinter_ih, hsc_ih, hamp_ih⟩ :=
        ih (past ++ [v_prev]) v' (by rw [hsplit]; simp)
      refine ⟨v_prev, x_next :: xs_more, ?_, ?_, le_refl _, ?_, ?_, ?_, ?_⟩
      · -- length
        simp [hlen_ih]
      · -- sorted
        refine List.Pairwise.cons ?_ hpw_ih
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · rw [hveq]; exact hv'_le_next
        · exact le_trans (le_trans (le_refl v_prev) (by rw [hveq]; exact hv'_le_next))
            ((List.pairwise_cons.mp hpw_ih).1 b hb')
      · -- Interlaced
        exact ⟨hv_prev_le_v', hv'_le_next, hinter_ih⟩
      · -- sign-const
        intro x y hv_prev_x hxy hgap
        have hgap_vprev : v_prev < x ∨ y < v_prev := hgap v_prev List.mem_cons_self
        have _hv_prev_lt_x : v_prev < x :=
          hgap_vprev.resolve_right (fun hyv => not_lt.mpr (le_trans hv_prev_x hxy) hyv)
        have hv'_le_x : v' ≤ x := by rw [← hveq]; exact hv_prev_x
        have hgap' : ∀ r ∈ x_next :: xs_more, r < x ∨ y < r := by
          intro r hr; exact hgap r (List.mem_cons_of_mem _ hr)
        exact hsc_ih x y hv'_le_x hxy hgap'
      · -- IsArgminAbsOn P (Set.Icc v_prev v') v_prev
        -- Since v_prev = v', the interval is a singleton {v_prev}.
        refine ⟨⟨le_refl _, hv_prev_le_v'⟩, ?_⟩
        intro z hz
        have hzv : z = v_prev := le_antisymm (hveq ▸ hz.2) hz.1
        rw [hzv]
      · -- ArgminPartitionFrom P v' (x_next :: xs_more) ys''
        exact hamp_ih
    · -- v_prev < v'. Proceed with argmin on Icc v_prev v'.
      have hgap_out : ∀ r ∈ ys_full, r ≤ v_prev ∨ v' ≤ r :=
        gap_closure_adjacent hsplit hsorted_full
      have hdich : (∀ x ∈ Set.Ioo v_prev v', 0 < (derivative P).eval x) ∨
                   (∀ x ∈ Set.Ioo v_prev v', (derivative P).eval x < 0) :=
        sign_dichotomy_Ioo hsc_full hvlt hgap_out
      obtain ⟨x_head, hx_head_mem, hx_head_min, _hx_head_wit⟩ :=
        exists_argmin_abs_on_Icc_of_deriv_dichotomy hIVP hvlt hdich
      -- Recurse
      obtain ⟨x_next, xs_more, hlen_ih, hpw_ih, hv'_le_next, hinter_ih, hsc_ih, hamp_ih⟩ :=
        ih (past ++ [v_prev]) v' (by rw [hsplit]; simp)
      refine ⟨x_head, x_next :: xs_more, ?_, ?_, hx_head_mem.1, ?_, ?_, ?_, ?_⟩
      · -- length
        simp [hlen_ih]
      · -- sorted
        refine List.Pairwise.cons ?_ hpw_ih
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact le_trans hx_head_mem.2 hv'_le_next
        · exact le_trans (le_trans hx_head_mem.2 hv'_le_next)
            ((List.pairwise_cons.mp hpw_ih).1 b hb')
      · -- Interlaced
        exact ⟨hx_head_mem.2, hv'_le_next, hinter_ih⟩
      · -- sign-const for xs_tail = x_head :: x_next :: xs_more
        intro x y hv_prev_x hxy hgap
        have hgap_head : x_head < x ∨ y < x_head := hgap x_head List.mem_cons_self
        have hgap_rest : ∀ r ∈ x_next :: xs_more, r < x ∨ y < r :=
          fun r hr => hgap r (List.mem_cons_of_mem _ hr)
        -- Dichotomy on mono/anti of P on Icc v_prev v'
        -- Helper closures:
        have icc_case : ∀ {x' y' : R}, x' ≤ y' → v_prev ≤ x' → y' ≤ v' →
            (x_head < x' ∨ y' < x_head) →
            P.eval x' ≠ 0 ∧ SignType.sign (P.eval x') = SignType.sign (P.eval y') := by
          intro x' y' hxy' hxv hyv hgap'
          rcases hdich with hp | hn
          · have hmono := corollary_2_24_increasing hIVP P hvlt hp
            exact sign_const_of_argmin_strictMonoOn_Icc hIVP hvlt.le hmono
              hx_head_mem hx_head_min hxy' ⟨hxv, le_trans hxy' hyv⟩ ⟨le_trans hxv hxy', hyv⟩ hgap'
          · have hanti := corollary_2_24_decreasing hIVP P hvlt hn
            exact sign_const_of_argmin_strictAntiOn_Icc hIVP hvlt.le hanti
              hx_head_mem hx_head_min hxy' ⟨hxv, le_trans hxy' hyv⟩ ⟨le_trans hxv hxy', hyv⟩ hgap'
        -- Case split on position of [x, y]
        rcases le_or_gt y v' with hyv' | hv'y
        · -- y ≤ v': [x,y] ⊆ Icc v_prev v'
          exact icc_case hxy hv_prev_x hyv' hgap_head
        · -- v' < y. Then either x ≥ v' (IH territory) or x < v' (straddle).
          rcases le_or_gt v' x with hv'x | hxv'
          · -- v' ≤ x: entirely in IH territory.
            exact hsc_ih x y hv'x hxy hgap_rest
          · -- x < v' < y: straddle.
            have hxv'_le : x ≤ v' := hxv'.le
            have hv'y_le : v' ≤ y := hv'y.le
            have hgap_head' : x_head < x := by
              rcases hgap_head with h | h
              · exact h
              · exact absurd (lt_of_lt_of_le h hx_head_mem.2) (not_lt.mpr hv'y.le)
            obtain ⟨hPx_ne, hsign_xv'⟩ :=
              icc_case hxv'_le hv_prev_x (le_refl v') (Or.inl hgap_head')
            have hgap_rest_v' : ∀ r ∈ x_next :: xs_more, r < v' ∨ y < r := fun r hr =>
              (hgap_rest r hr).imp_left (fun h => lt_trans h hxv')
            obtain ⟨_, hsign_v'y⟩ :=
              hsc_ih v' y (le_refl v') hv'y_le hgap_rest_v'
            exact ⟨hPx_ne, hsign_xv'.trans hsign_v'y⟩
      · -- IsArgminAbsOn P (Set.Icc v_prev v') x_head
        exact ⟨hx_head_mem, hx_head_min⟩
      · -- ArgminPartitionFrom P v' (x_next :: xs_more) ys''
        exact hamp_ih

/-- General existence of a virtual roots list for `P`, given one for `P'`.
    Uses `exists_buildTail` to construct the tail after the first argmin on
    `Iic (head ys)`. -/
theorem exists_virtualRootsList_of_ys_general
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hdeg_pos : 0 < P.natDegree)
    {ys : List R} (hys : IsVirtualRootsList P.derivative ys)
    (hlen : ys.length + 1 = P.natDegree) :
    ∃ xs : List R, IsVirtualRootsList P xs ∧ Interlaced xs ys := by
  match ys, hys, hlen with
  | [], hys, hlen =>
    -- P.natDegree = 1
    have hdeg : P.natDegree = 1 := by simp at hlen; omega
    obtain ⟨xs, hxs⟩ := exists_virtualRootsList_of_natDegree_one hIVP hdeg
    have hlen_xs : xs.length = 1 := by rw [hxs.length_eq]; exact hdeg
    match xs, hlen_xs, hxs with
    | [r], _, hxs => exact ⟨[r], hxs, trivial⟩
  | v :: ys', hys, hlen =>
    -- Head argmin on Iic v.
    have hle_Iio : ∀ r ∈ v :: ys', v ≤ r := by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact le_refl _
      · exact (List.pairwise_cons.mp hys.sorted).1 r hr'
    have hdich_Iio : (∀ x ∈ Set.Iio v, 0 < (derivative P).eval x) ∨
                     (∀ x ∈ Set.Iio v, (derivative P).eval x < 0) :=
      sign_dichotomy_Iio hys.sign_const hle_Iio
    obtain ⟨x₁, hx₁_mem, hx₁_min, _hx₁_wit⟩ :=
      exists_argmin_abs_on_Iic_of_deriv_dichotomy hIVP hdeg_pos hdich_Iio
    -- Tail via buildTail with past=[], v_prev=v, ys_rest=ys'.
    obtain ⟨x_head, xs_rest, hlen_tail, hpw_tail, hv_le_head, hinter_tail, hsc_tail,
        hamp_tail⟩ :=
      exists_buildTail hIVP hdeg_pos (v :: ys') hys.sorted hys.sign_const
        ys' [] v (by simp)
    -- hys at the (v :: ys').length depth for the argmin_wit clause
    have hys_aux : IsVirtualRootsListAux (v :: ys').length (derivative P) (v :: ys') := by
      have h : IsVirtualRootsListAux (derivative P).natDegree (derivative P) (v :: ys') := hys
      rw [hys.length_eq.symm] at h
      exact h
    refine ⟨x₁ :: x_head :: xs_rest, ?_, ?_⟩
    · unfold IsVirtualRootsList
      rw [← hlen]
      refine ⟨?_, ?_, ?_, Or.inr ⟨v :: ys', hys_aux, ?_, ?_, ?_⟩⟩
      · -- length
        simp only [List.length_cons, hlen_tail]
        omega
      · -- sorted: x₁ ≤ x_head (since x₁ ≤ v ≤ x_head)
        refine List.Pairwise.cons ?_ hpw_tail
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact le_trans hx₁_mem hv_le_head
        · exact le_trans (le_trans hx₁_mem hv_le_head)
            ((List.pairwise_cons.mp hpw_tail).1 b hb')
      · -- sign-const on gaps of xs = x₁ :: x_head :: xs_rest
        intro x y hxy hgap
        have hgap_1 : x₁ < x ∨ y < x₁ := hgap x₁ List.mem_cons_self
        have hgap_rest : ∀ r ∈ x_head :: xs_rest, r < x ∨ y < r :=
          fun r hr => hgap r (List.mem_cons_of_mem _ hr)
        -- Iic helper: sign-const on (x, y) ⊆ Iic v with gap x₁.
        have iic_case : ∀ {x' y' : R}, x' ≤ y' → x' ≤ v → y' ≤ v →
            (x₁ < x' ∨ y' < x₁) →
            P.eval x' ≠ 0 ∧ SignType.sign (P.eval x') = SignType.sign (P.eval y') := by
          intro x' y' hxy' hxv hyv hgap'
          rcases hdich_Iio with hp | hn
          · exact sign_const_of_argmin_strictMonoOn_Iic hIVP
              (strictMonoOn_of_deriv_pos_Iic hIVP hp)
              hx₁_mem hx₁_min hxy' hxv hyv hgap'
          · exact sign_const_of_argmin_strictAntiOn_Iic hIVP
              (strictAntiOn_of_deriv_neg_Iic hIVP hn)
              hx₁_mem hx₁_min hxy' hxv hyv hgap'
        -- Case split on y relative to v (the first virtual root of P')
        rcases le_or_gt y v with hyv | hvy
        · -- y ≤ v: [x, y] ⊆ Iic v; use iic_case with gap hgap_1.
          exact iic_case hxy (le_trans hxy hyv) hyv hgap_1
        · rcases le_or_gt v x with hvx | hxv
          · -- v ≤ x: [x, y] ⊆ [v, ∞); use hsc_tail with gap hgap_rest.
            exact hsc_tail x y hvx hxy hgap_rest
          · -- x < v < y: straddle; glue at v.
            have hxv' : x ≤ v := hxv.le
            have hvy' : v ≤ y := hvy.le
            -- Sign x to v via iic_case. Need gap at x₁ to apply.
            have hgap_1' : x₁ < x := by
              rcases hgap_1 with h | h
              · exact h
              · exact absurd (lt_of_lt_of_le h hx₁_mem) (not_lt.mpr hvy.le)
            obtain ⟨hPx_ne, hsign_xv⟩ :=
              iic_case hxv' hxv' (le_refl v) (Or.inl hgap_1')
            have hgap_rest_v : ∀ r ∈ x_head :: xs_rest, r < v ∨ y < r := fun r hr =>
              (hgap_rest r hr).imp_left (fun h => lt_trans h hxv)
            obtain ⟨_, hsign_vy⟩ :=
              hsc_tail v y (le_refl v) hvy' hgap_rest_v
            exact ⟨hPx_ne, hsign_xv.trans hsign_vy⟩
      · -- Interlaced (x₁ :: x_head :: xs_rest) (v :: ys')
        -- = x₁ ≤ v ∧ v ≤ x_head ∧ Interlaced (x_head :: xs_rest) ys'
        exact ⟨hx₁_mem, hv_le_head, hinter_tail⟩
      · -- IsArgminAbsOn P (Set.Iic v) x₁
        exact ⟨hx₁_mem, hx₁_min⟩
      · -- ArgminPartitionFrom P v (x_head :: xs_rest) ys'
        exact hamp_tail
    · -- Interlaced (x₁ :: x_head :: xs_rest) (v :: ys')
      exact ⟨hx₁_mem, hv_le_head, hinter_tail⟩

/-! ## Top-level existence and `virtualRoots` definition -/

/-- Existence of a virtual roots list for any nonzero polynomial, bundled
    with an interlaced virtual roots list for the derivative when nonzero.
    Proved by induction on `natDegree`. -/
theorem exists_virtualRootsList_aux (hIVP : HasIntermediateValueProperty R) :
    ∀ (n : ℕ) (P : R[X]), P.natDegree = n → P ≠ 0 →
    ∃ xs, IsVirtualRootsList P xs ∧
      (derivative P = 0 ∨
        ∃ ys, IsVirtualRootsList (derivative P) ys ∧ Interlaced xs ys) := by
  intro n
  induction n with
  | zero =>
    intro P hn hP
    refine ⟨[], isVirtualRootsList_nil_of_natDegree_zero hn hP, ?_⟩
    exact Or.inl (Polynomial.derivative_of_natDegree_zero hn)
  | succ m IH =>
    intro P hn hP
    have hdeg_pos : 0 < P.natDegree := by rw [hn]; omega
    have hdP_deg : (derivative P).natDegree = m := by
      have h : (derivative P).degree = (P.natDegree - 1 : ℕ) :=
        Polynomial.degree_derivative_eq P hdeg_pos
      have h' : (derivative P).natDegree = P.natDegree - 1 :=
        Polynomial.natDegree_eq_of_degree_eq_some h
      rw [h', hn]; omega
    have hdP_ne : derivative P ≠ 0 := by
      intro heq
      have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero heq
      omega
    obtain ⟨ys, hys, _⟩ := IH (derivative P) hdP_deg hdP_ne
    have hlen : ys.length + 1 = P.natDegree := by rw [hys.length_eq, hdP_deg, hn]
    obtain ⟨xs, hxs, hinter⟩ :=
      exists_virtualRootsList_of_ys_general hIVP hdeg_pos hys hlen
    exact ⟨xs, hxs, Or.inr ⟨ys, hys, hinter⟩⟩

/-- Existence of a virtual roots list for any nonzero polynomial. -/
theorem exists_virtualRootsList (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) : ∃ xs, IsVirtualRootsList P xs :=
  let ⟨xs, hxs, _⟩ := exists_virtualRootsList_aux hIVP P.natDegree P rfl hP
  ⟨xs, hxs⟩

/-! ### Count bounds for interlaced sorted lists

For the BPR theorem on virtual multiplicities: if `xs` and `ys` are interlaced
with `ys` sorted, then for any `t : R`, the counts of `t` in `xs` and `ys`
differ by at most `1`. -/

omit [Field R] [IsStrictOrderedRing R] in
/-- **Sub-lemma for count bounds.** In an interlaced pair `(x :: rest, ys)` with
    `ys` sorted, the count of `x` in `ys` is at most the count in `x :: rest`. -/
private lemma Interlaced.count_head_le {x : R} :
    ∀ {rest ys : List R}, Interlaced (x :: rest) ys →
      ys.Pairwise (· ≤ ·) → ys.count x ≤ (x :: rest).count x
  | [], [], _, _ => by simp
  | [], _ :: _, h, _ => absurd h (by simp [Interlaced])
  | _ :: _, [], _, _ => by simp
  | x' :: rest, y :: ys', h, hsort => by
    obtain ⟨hxy, hyx', hrec⟩ := h
    have hsort_tail : ys'.Pairwise (· ≤ ·) := hsort.tail
    rcases lt_or_eq_of_le hxy with hy_gt | hy_eq
    · have hall : ∀ a ∈ y :: ys', x < a := by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact hy_gt
        · exact hy_gt.trans_le ((List.pairwise_cons.mp hsort).1 a ha')
      have hcount : (y :: ys').count x = 0 :=
        List.count_eq_zero.mpr (fun hm => (hall x hm).ne rfl)
      rw [hcount]; exact Nat.zero_le _
    · subst hy_eq
      rcases lt_or_eq_of_le hyx' with hx'_gt | hx'_eq
      · have hxs_sort : (x' :: rest).Pairwise (· ≤ ·) :=
          Interlaced.pairwise_of_ys hrec hsort_tail
        have hxs_gt : ∀ a ∈ x' :: rest, x < a := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha'
          · exact hx'_gt
          · exact hx'_gt.trans_le ((List.pairwise_cons.mp hxs_sort).1 a ha')
        have hys'_gt : ∀ a ∈ ys', x < a := by
          intro a ha
          match ys', rest, hrec, ha with
          | [], _, _, ha => exact absurd ha List.not_mem_nil
          | y' :: ys'', [], hrec, _ => exact absurd hrec (by simp [Interlaced])
          | y' :: ys'', x'' :: rest', hrec, ha =>
            obtain ⟨hx'y', _, _⟩ := hrec
            have hy'_gt : x < y' := hx'_gt.trans_le hx'y'
            rcases List.mem_cons.mp ha with rfl | ha''
            · exact hy'_gt
            · exact hy'_gt.trans_le ((List.pairwise_cons.mp hsort_tail).1 a ha'')
        have hcount_xs : (x' :: rest).count x = 0 :=
          List.count_eq_zero.mpr (fun hm => (hxs_gt x hm).ne rfl)
        have hcount_ys' : ys'.count x = 0 :=
          List.count_eq_zero.mpr (fun hm => (hys'_gt x hm).ne rfl)
        rw [List.count_cons_self, List.count_cons_self, hcount_ys', hcount_xs]
      · subst hx'_eq
        have ih : ys'.count x ≤ (x :: rest).count x :=
          Interlaced.count_head_le hrec hsort_tail
        rw [List.count_cons_self, List.count_cons_self, List.count_cons_self] at *
        omega

omit [Field R] [IsStrictOrderedRing R] in
/-- **Count bound for interlaced sorted lists.** If `xs` and `ys` are interlaced
    with `ys` sorted, then for any `t : R`, the counts of `t` in `xs` and `ys`
    differ by at most `1`. -/
lemma Interlaced.count_diff_le_one :
    ∀ {xs ys : List R}, Interlaced xs ys →
      ys.Pairwise (· ≤ ·) → ∀ (t : R),
        ys.count t ≤ xs.count t + 1 ∧ xs.count t ≤ ys.count t + 1
  | [_], [], _, _, _ => by
    refine ⟨by simp, ?_⟩
    rw [List.count_cons]; split_ifs <;> simp
  | [], ys, h, _, _ => absurd h (by cases ys <;> simp [Interlaced])
  | [_], _ :: _, h, _, _ => absurd h (by simp [Interlaced])
  | _ :: _ :: _, [], h, _, _ => absurd h (by simp [Interlaced])
  | x :: x' :: xs, y :: ys, h, hsort, t => by
    obtain ⟨hxy, hyx', hrec⟩ := h
    have hsort_tail : ys.Pairwise (· ≤ ·) := hsort.tail
    obtain ⟨ih_yx, ih_xy⟩ := Interlaced.count_diff_le_one hrec hsort_tail t
    by_cases hx : x = t
    · subst hx
      by_cases hy : y = x
      · subst hy
        simp only [List.count_cons_self] at ih_yx ih_xy ⊢
        omega
      · have hy_gt : x < y := lt_of_le_of_ne hxy (Ne.symm hy)
        have hx'_gt : x < x' := hy_gt.trans_le hyx'
        have hxs_sort := Interlaced.pairwise_of_ys hrec hsort_tail
        have hxs_gt : ∀ a ∈ x' :: xs, x < a := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha'
          · exact hx'_gt
          · exact hx'_gt.trans_le ((List.pairwise_cons.mp hxs_sort).1 a ha')
        have hys_gt : ∀ a ∈ ys, x < a := fun a ha =>
          hy_gt.trans_le ((List.pairwise_cons.mp hsort).1 a ha)
        have hcx' : (x' :: xs).count x = 0 :=
          List.count_eq_zero.mpr (fun hm => (hxs_gt x hm).ne rfl)
        have hcy : ys.count x = 0 :=
          List.count_eq_zero.mpr (fun hm => (hys_gt x hm).ne rfl)
        rw [List.count_cons_self, List.count_cons_of_ne hy, hcx', hcy]
        simp
    · by_cases hy : y = t
      · subst hy
        have hx_lt : x < y := lt_of_le_of_ne hxy hx
        rcases lt_or_eq_of_le hyx' with hx'_gt | hx'_eq
        · have hxs_sort := Interlaced.pairwise_of_ys hrec hsort_tail
          have hxs_gt : ∀ a ∈ x' :: xs, y < a := by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha'
            · exact hx'_gt
            · exact hx'_gt.trans_le ((List.pairwise_cons.mp hxs_sort).1 a ha')
          have hys_gt : ∀ a ∈ ys, y < a := by
            intro a ha
            match xs, ys, hrec, ha with
            | _, [], _, ha => exact absurd ha List.not_mem_nil
            | [], y' :: ys', hrec, _ => exact absurd hrec (by simp [Interlaced])
            | x'' :: xs', y' :: ys', hrec, ha =>
              obtain ⟨hx'y', _, _⟩ := hrec
              have hy'_gt : y < y' := hx'_gt.trans_le hx'y'
              rcases List.mem_cons.mp ha with rfl | ha''
              · exact hy'_gt
              · exact hy'_gt.trans_le ((List.pairwise_cons.mp hsort_tail).1 a ha'')
          have hcx' : (x' :: xs).count y = 0 :=
            List.count_eq_zero.mpr (fun hm => (hxs_gt y hm).ne rfl)
          have hcy : ys.count y = 0 :=
            List.count_eq_zero.mpr (fun hm => (hys_gt y hm).ne rfl)
          rw [List.count_cons_of_ne hx, List.count_cons_self, hcx', hcy]
          simp
        · subst hx'_eq
          have sub := Interlaced.count_head_le hrec hsort_tail
          simp only [List.count_cons_self, List.count_cons_of_ne hx] at sub ih_yx ih_xy ⊢
          omega
      · rw [List.count_cons_of_ne hx, List.count_cons_of_ne hy]
        exact ⟨ih_yx, ih_xy⟩

/-! ### BPR Proposition 2.46 interpretation (1): `P(x) = 0 ⇒ ν(P, x) = ν(P', x) + 1` -/

omit [IsStrictOrderedRing R] in
/-- If `P` has constant sign on each gap determined by `xs` and `P.eval x = 0`,
    then `x ∈ xs`: roots of `P` must be accounted for in the virtual roots. -/
lemma mem_of_eval_eq_zero_of_signConstantOnGaps {P : R[X]} {xs : List R}
    (h : SignConstantOnGaps P xs) {x : R} (hx : P.eval x = 0) : x ∈ xs := by
  by_contra hne
  have hgap : ∀ r ∈ xs, r < x ∨ x < r := by
    intro r hr
    rcases lt_trichotomy r x with h1 | rfl | h1
    · exact Or.inl h1
    · exact absurd hr hne
    · exact Or.inr h1
  exact (h x x (le_refl x) hgap).1 hx

omit [IsStrictOrderedRing R] in
/-- `P.eval x = 0` forces `x` to appear in any virtual roots list of `P`. -/
lemma count_pos_of_eval_eq_zero {P : R[X]} {xs : List R}
    (hxs : IsVirtualRootsList P xs) {x : R} (hx : P.eval x = 0) :
    0 < xs.count x :=
  List.count_pos_iff.mpr
    (mem_of_eval_eq_zero_of_signConstantOnGaps hxs.sign_const hx)

omit [IsStrictOrderedRing R] in
/-- If `z ∉ ys` and `SignConstantOnGaps Q ys`, then `Q.eval z ≠ 0`. -/
lemma eval_ne_zero_of_not_mem_of_signConstantOnGaps {Q : R[X]} {ys : List R}
    (hys : SignConstantOnGaps Q ys) {z : R} (hz : z ∉ ys) : Q.eval z ≠ 0 := by
  refine (hys z z (le_refl z) ?_).1
  intro r hr
  rcases lt_trichotomy r z with h1 | rfl | h1
  · exact Or.inl h1
  · exact absurd hr hz
  · exact Or.inr h1

/-- **Rolle + SignConstantOnGaps contradiction helper.** If `a < b` are both
    actual roots of `P`, `ys` is sorted with `SignConstantOnGaps P' ys`, and
    no entry of `ys` lies in the closed interval `[a, b]`, then a contradiction
    ensues (via Rolle's theorem giving a root of `P'` in `(a, b)` that is
    missed by `ys`'s sign-constant cover). -/
lemma false_of_rolle_gap
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {ys : List R}
    (hys : SignConstantOnGaps (derivative P) ys)
    {a b : R} (hab : a < b) (hPa : P.eval a = 0) (hPb : P.eval b = 0)
    (hno : ∀ y ∈ ys, y < a ∨ b < y) : False := by
  obtain ⟨c, hc, hPc⟩ := proposition_2_22 hIVP P hab hPa hPb
  have hc_not_in : c ∉ ys := fun hcy => by
    rcases hno c hcy with hlt | hlt
    · exact absurd hlt (not_lt.mpr hc.1.le)
    · exact absurd hlt (not_lt.mpr hc.2.le)
  exact eval_ne_zero_of_not_mem_of_signConstantOnGaps hys hc_not_in hPc

/-- Non-strict variant of `false_of_rolle_gap`: if each `y ∈ ys` satisfies
    `y ≤ a` or `b ≤ y`, the Rolle witness in the open interval `(a, b)`
    strictly avoids all of `ys`, giving the same contradiction. -/
lemma false_of_rolle_gap_closed
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {ys : List R}
    (hys : SignConstantOnGaps (derivative P) ys)
    {a b : R} (hab : a < b) (hPa : P.eval a = 0) (hPb : P.eval b = 0)
    (hno : ∀ y ∈ ys, y ≤ a ∨ b ≤ y) : False := by
  obtain ⟨c, hc, hPc⟩ := proposition_2_22 hIVP P hab hPa hPb
  have hc_not_in : c ∉ ys := fun hcy => by
    rcases hno c hcy with hle | hle
    · exact absurd hc.1 (not_lt.mpr hle)
    · exact absurd hc.2 (not_lt.mpr hle)
  exact eval_ne_zero_of_not_mem_of_signConstantOnGaps hys hc_not_in hPc

/-- **Argmin-chain uniqueness of a root.** In the `ArgminPartitionFrom`
    structure, if `x₀ ∈ [v, y]` minimises `|P|` on `[v, y]`, `x ∈ [v, y]` with
    `P(x) = 0`, and every `y' ∈ ys_full` satisfies `y' ≤ v` or `y ≤ y'`, then
    `x₀ = x`. The two non-equal cases are ruled out by Rolle's theorem: any
    witness `c` strictly between `x₀` and `x` lies in `(v, y)`, hence is
    disjoint from `ys_full`, but `P'(c) ≠ 0` by sign-constancy. -/
private lemma argmin_eq_root_of_Icc
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {ys_full : List R}
    (hsg : SignConstantOnGaps (derivative P) ys_full)
    {v y x₀ x : R}
    (hx₀ : IsArgminAbsOn P (Set.Icc v y) x₀)
    (hx : P.eval x = 0) (hvx : v ≤ x) (hxy : x ≤ y)
    (hno : ∀ y' ∈ ys_full, y' ≤ v ∨ y ≤ y') :
    x₀ = x := by
  obtain ⟨⟨hvx₀, hx₀y⟩, hmin⟩ := hx₀
  have hPx₀ : P.eval x₀ = 0 := by
    have := hmin x ⟨hvx, hxy⟩
    rw [hx, abs_zero] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  rcases lt_trichotomy x₀ x with hlt | heq | hgt
  · exfalso
    refine false_of_rolle_gap_closed hIVP hsg hlt hPx₀ hx ?_
    intro y' hy'
    rcases hno y' hy' with h | h
    · exact Or.inl (h.trans hvx₀)
    · exact Or.inr (hxy.trans h)
  · exact heq
  · exfalso
    refine false_of_rolle_gap_closed hIVP hsg hgt hx hPx₀ ?_
    intro y' hy'
    rcases hno y' hy' with h | h
    · exact Or.inl (h.trans hvx)
    · exact Or.inr (hx₀y.trans h)

/-- Variant of `argmin_eq_root_of_Icc` for the leftmost interval `Iic y`. -/
private lemma argmin_eq_root_of_Iic
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {ys_full : List R}
    (hsg : SignConstantOnGaps (derivative P) ys_full)
    {y x₀ x : R}
    (hx₀ : IsArgminAbsOn P (Set.Iic y) x₀)
    (hx : P.eval x = 0) (hxy : x ≤ y)
    (hno : ∀ y' ∈ ys_full, y ≤ y') :
    x₀ = x := by
  obtain ⟨hx₀y, hmin⟩ := hx₀
  have hPx₀ : P.eval x₀ = 0 := by
    have := hmin x hxy
    rw [hx, abs_zero] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  rcases lt_trichotomy x₀ x with hlt | heq | hgt
  · exfalso
    refine false_of_rolle_gap_closed hIVP hsg hlt hPx₀ hx ?_
    intro y' hy'; exact Or.inr (hxy.trans (hno y' hy'))
  · exact heq
  · exfalso
    refine false_of_rolle_gap_closed hIVP hsg hgt hx hPx₀ ?_
    intro y' hy'; exact Or.inr (hx₀y.trans (hno y' hy'))

/-- Variant of `argmin_eq_root_of_Icc` for the rightmost interval `Ici v`. -/
private lemma argmin_eq_root_of_Ici
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {ys_full : List R}
    (hsg : SignConstantOnGaps (derivative P) ys_full)
    {v x₀ x : R}
    (hx₀ : IsArgminAbsOn P (Set.Ici v) x₀)
    (hx : P.eval x = 0) (hvx : v ≤ x)
    (hno : ∀ y' ∈ ys_full, y' ≤ v) :
    x₀ = x := by
  obtain ⟨hvx₀, hmin⟩ := hx₀
  have hPx₀ : P.eval x₀ = 0 := by
    have := hmin x hvx
    rw [hx, abs_zero] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  rcases lt_trichotomy x₀ x with hlt | heq | hgt
  · exfalso
    refine false_of_rolle_gap_closed hIVP hsg hlt hPx₀ hx ?_
    intro y' hy'; exact Or.inl ((hno y' hy').trans hvx₀)
  · exact heq
  · exfalso
    refine false_of_rolle_gap_closed hIVP hsg hgt hx hPx₀ ?_
    intro y' hy'; exact Or.inl ((hno y' hy').trans hvx)

/-- Recursive count identity along an `ArgminPartitionFrom` chain, carrying a
    full ambient list `ys_full` whose `SignConstantOnGaps (derivative P)`
    witness survives the recursion. The invariants `past ++ ys = ys_full` and
    `∀ p ∈ past, p ≤ v` let the recursion move one step of `ys` into `past`
    while updating the anchor `v`. -/
private lemma count_eq_of_root_from_aux
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {ys_full : List R}
    (hys_full_sort : ys_full.Pairwise (· ≤ ·))
    (hsg : SignConstantOnGaps (derivative P) ys_full)
    {x : R} (hx : P.eval x = 0) :
    ∀ {xs ys : List R} {v : R} {past : List R},
      ys_full = past ++ ys →
      Interlaced xs ys →
      ArgminPartitionFrom P v xs ys →
      v ≤ x →
      (∀ p ∈ past, p ≤ v) →
      ys.count x + 1 = xs.count x := by
  intro xs ys
  induction ys generalizing xs with
  | nil =>
    intro v past hsplit hi harg hvx hpast
    -- ys = []; Interlaced xs [] forces xs = [z].
    match xs, hi with
    | [z], _ =>
      change IsArgminAbsOn P (Set.Ici v) z at harg
      -- ys_full = past ++ [] = past, so ys_full = past. All of ys_full ≤ v.
      have hno : ∀ y' ∈ ys_full, y' ≤ v := by
        rw [hsplit, List.append_nil]; exact hpast
      have hz : z = x := argmin_eq_root_of_Ici hIVP hsg harg hx hvx hno
      subst hz; simp
    | x₀ :: _ :: _, hi => exact absurd hi (by simp [Interlaced])
    | [], hi => exact absurd hi (by simp [Interlaced])
  | cons y ys' ih =>
    intro v past hsplit hi harg hvx hpast
    -- ys = y :: ys', xs must be x₀ :: x₁ :: xs''.
    match xs, hi, harg with
    | [], hi, _ => exact absurd hi (by simp [Interlaced])
    | [_], hi, _ => exact absurd hi (by simp [Interlaced])
    | x₀ :: x₁ :: xs'', hi, harg =>
      obtain ⟨h_x0_le_y, h_y_le_x1, hi_rest⟩ := hi
      change IsArgminAbsOn P (Set.Icc v y) x₀ ∧
        ArgminPartitionFrom P y (x₁ :: xs'') ys' at harg
      obtain ⟨harg_x0, harg_rest⟩ := harg
      -- Extract: the suffix `y :: ys'` of `ys_full` is still pairwise-sorted.
      have hpw_suff : (y :: ys').Pairwise (· ≤ ·) := by
        have h := hys_full_sort
        rw [hsplit, List.pairwise_append] at h
        exact h.2.1
      have hy_le_ys' : ∀ y' ∈ ys', y ≤ y' := (List.pairwise_cons.mp hpw_suff).1
      have hys'_sort : ys'.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hpw_suff).2
      -- `v ≤ x₀ ≤ y`, so `v ≤ y`; combined with `hpast`, all `past ++ [y]` are `≤ y`.
      have hv_le_y : v ≤ y := harg_x0.1.1.trans harg_x0.1.2
      have hpast' : ∀ p ∈ past ++ [y], p ≤ y := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact (hpast p hp).trans hv_le_y
        · rcases List.mem_cons.mp hp with rfl | h
          · exact le_refl _
          · exact absurd h List.not_mem_nil
      have hsplit' : ys_full = (past ++ [y]) ++ ys' := by
        rw [List.append_assoc, List.singleton_append]; exact hsplit
      rcases le_or_gt x y with hxy | hyx
      · -- Case x ≤ y: argmin on `Icc v y` forces `x₀ = x`.
        have hno : ∀ y' ∈ ys_full, y' ≤ v ∨ y ≤ y' := by
          intro y' hy'
          rw [hsplit] at hy'
          rcases List.mem_append.mp hy' with hp | hyrest
          · exact Or.inl (hpast y' hp)
          · rcases List.mem_cons.mp hyrest with rfl | hy'_in_ys'
            · exact Or.inr (le_refl _)
            · exact Or.inr (hy_le_ys' y' hy'_in_ys')
        have hx0_eq : x₀ = x :=
          argmin_eq_root_of_Icc hIVP hsg harg_x0 hx hvx hxy hno
        rw [hx0_eq]
        rcases lt_or_eq_of_le hxy with hxy_lt | hxy_eq
        · -- x < y: all remaining entries are ≥ y > x, so counts past x are zero.
          have hx_lt_x1 : x < x₁ := lt_of_lt_of_le hxy_lt h_y_le_x1
          have hxs_sort := Interlaced.pairwise_of_ys hi_rest hys'_sort
          have hxs_gt : ∀ a ∈ x₁ :: xs'', x < a := by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | h
            · exact hx_lt_x1
            · exact hx_lt_x1.trans_le ((List.pairwise_cons.mp hxs_sort).1 a h)
          have hys_gt : ∀ a ∈ y :: ys', x < a := by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | h
            · exact hxy_lt
            · exact hxy_lt.trans_le (hy_le_ys' a h)
          have hcy : (y :: ys').count x = 0 :=
            List.count_eq_zero.mpr (fun hm => (hys_gt x hm).ne rfl)
          have hcx1 : (x₁ :: xs'').count x = 0 :=
            List.count_eq_zero.mpr (fun hm => (hxs_gt x hm).ne rfl)
          rw [hcy, List.count_cons_self, hcx1]
        · -- x = y: recurse with `v := x`, `past := past ++ [x]`.
          subst hxy_eq
          have hrec := ih (v := x) (past := past ++ [x]) hsplit' hi_rest harg_rest
            (le_refl x) hpast'
          rw [List.count_cons_self, List.count_cons_self]
          omega
      · -- Case y < x: `x₀ ≤ y < x`, so `x₀ ≠ x` and `y ≠ x`. Recurse.
        have hx0_ne : x₀ ≠ x := ne_of_lt (lt_of_le_of_lt harg_x0.1.2 hyx)
        have hy_ne : y ≠ x := ne_of_lt hyx
        have hrec := ih (v := y) (past := past ++ [y]) hsplit' hi_rest harg_rest
          hyx.le hpast'
        rw [List.count_cons_of_ne hy_ne, List.count_cons_of_ne hx0_ne]
        exact hrec

/-- Core count identity. If `xs`, `ys` satisfy the virtual-roots structure
    (interlaced, sorted, with argmin partition of `|P|`, `P` sign-constant on
    xs-gaps, `P'` sign-constant on ys-gaps) and `P.eval x = 0`, then
    `ys.count x + 1 = xs.count x`.

    **Proof outline.** Each entry of `xs` is the argmin of `|P|` on an
    interval. When the interval's endpoints are ≤ `x` or ≥ `x`, the argmin is
    forced to equal `x` (by a Rolle contradiction on the polynomial roots
    `x₀ ≠ x` case): any witness `c` strictly between lies in a region disjoint
    from `ys`, so `P'(c) ≠ 0` contradicts the Rolle-produced root.
    `count_eq_of_root_from_aux` packages this as a recursion along the
    argmin chain. -/
lemma count_eq_of_root
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {xs ys : List R}
    (hi : Interlaced xs ys)
    (hys_sort : ys.Pairwise (· ≤ ·))
    (harg : ArgminPartition P xs ys)
    (hsg_xs : SignConstantOnGaps P xs)
    (hsg_ys : SignConstantOnGaps (derivative P) ys)
    {x : R} (hx : P.eval x = 0) :
    ys.count x + 1 = xs.count x := by
  match xs, ys, hi, harg with
  | [], ys, hi, _ => exact absurd hi (by cases ys <;> simp [Interlaced])
  | [_], _ :: _, hi, _ => exact absurd hi (by simp [Interlaced])
  | _ :: _ :: _, [], hi, _ => exact absurd hi (by simp [Interlaced])
  | [z], [], _, harg =>
    change IsArgminAbsOn P Set.univ z at harg
    have hz_mem_xs : x ∈ ([z] : List R) :=
      mem_of_eval_eq_zero_of_signConstantOnGaps hsg_xs hx
    have : z = x := by
      rcases List.mem_cons.mp hz_mem_xs with h | h
      · exact h.symm
      · exact absurd h List.not_mem_nil
    subst this; simp
  | x₀ :: x₁ :: xs'', y :: ys', hi, harg =>
    obtain ⟨h_x0_le_y, h_y_le_x1, hi_rest⟩ := hi
    change IsArgminAbsOn P (Set.Iic y) x₀ ∧
      ArgminPartitionFrom P y (x₁ :: xs'') ys' at harg
    obtain ⟨harg_x0, harg_rest⟩ := harg
    have hy_le_ys : ∀ y' ∈ y :: ys', y ≤ y' := by
      intro y' hy'
      rcases List.mem_cons.mp hy' with rfl | h
      · exact le_refl _
      · exact (List.pairwise_cons.mp hys_sort).1 y' h
    rcases le_or_gt x y with hxy | hyx
    · -- Case x ≤ y: argmin x₀ on Iic y forces x₀ = x.
      have hx0_eq : x₀ = x :=
        argmin_eq_root_of_Iic hIVP hsg_ys harg_x0 hx hxy hy_le_ys
      rw [hx0_eq]
      -- Further split on x vs y.
      rcases lt_or_eq_of_le hxy with hxy_lt | hxy_eq
      · -- x < y: y, x₁, and all later ≥ y > x, so counts of x all-zero past x.
        have hx_lt_x1 : x < x₁ := lt_of_lt_of_le hxy_lt h_y_le_x1
        have hxs_gt : ∀ a ∈ x₁ :: xs'', x < a := by
          intro a ha
          have hxs_sort := Interlaced.pairwise_of_ys hi_rest hys_sort.tail
          rcases List.mem_cons.mp ha with rfl | h
          · exact hx_lt_x1
          · exact hx_lt_x1.trans_le ((List.pairwise_cons.mp hxs_sort).1 a h)
        have hys_gt : ∀ a ∈ y :: ys', x < a := fun a ha =>
          lt_of_lt_of_le hxy_lt (hy_le_ys a ha)
        have hcy : (y :: ys').count x = 0 :=
          List.count_eq_zero.mpr (fun hm => (hys_gt x hm).ne rfl)
        have hcx1 : (x₁ :: xs'').count x = 0 :=
          List.count_eq_zero.mpr (fun hm => (hxs_gt x hm).ne rfl)
        rw [hcy, List.count_cons_self, hcx1]
      · -- x = y: recurse via count_eq_of_root_from_aux with past = [x], v = x.
        subst hxy_eq
        have hsplit : (x :: ys') = [x] ++ ys' := rfl
        have hpast : ∀ p ∈ ([x] : List R), p ≤ x := by
          intro p hp; rcases List.mem_cons.mp hp with rfl | h
          · exact le_refl _
          · exact absurd h List.not_mem_nil
        have := count_eq_of_root_from_aux hIVP hys_sort hsg_ys hx
          hsplit hi_rest harg_rest (le_refl x) hpast
        rw [List.count_cons_self, List.count_cons_self]
        omega
    · -- Case y < x: x₀ ≤ y < x, so x₀ ≠ x. Recurse.
      have hx0_ne : x₀ ≠ x := by
        have : x₀ ≤ y := harg_x0.1
        exact ne_of_lt (lt_of_le_of_lt this hyx)
      have hy_ne : y ≠ x := ne_of_lt hyx
      have hsplit : (y :: ys') = [y] ++ ys' := rfl
      have hpast : ∀ p ∈ ([y] : List R), p ≤ y := by
        intro p hp; rcases List.mem_cons.mp hp with rfl | h
        · exact le_refl _
        · exact absurd h List.not_mem_nil
      have := count_eq_of_root_from_aux hIVP hys_sort hsg_ys hx
        hsplit hi_rest harg_rest hyx.le hpast
      rw [List.count_cons_of_ne hy_ne, List.count_cons_of_ne hx0_ne]
      exact this

/-! ### Count identity, non-root case

Target: when `P.eval c ≠ 0`, the difference of counts `xs.count c - ys.count c`
along the argmin chain equals the sign-dependent constant

```
if Even ν then 0 else if 0 < P(c) · P^(ν+1)(c) then 1 else -1
```

where `ν = (derivative P).rootMultiplicity c`. Structure parallels
`count_eq_of_root_from_aux`, but the "contributions from the current step"
are determined by sign analysis (Helpers 1 + 2) rather than by forcing
`x₀ = c`. -/

/-- The non-root diff formula packaged as an `ℤ`-valued expression. -/
noncomputable def nonRootDiffFormula (P : R[X]) (c : R) : ℤ :=
  if Even ((derivative P).rootMultiplicity c) then 0
  else if 0 < P.eval c *
        ((⇑derivative)^[(derivative P).rootMultiplicity c + 1] P).eval c
    then 1 else -1

/-- **Non-root `c = y` case, right-boundary `Ici c` variant.** In the aux
    `c = y` branch when `ys_rest = []`, the right-side argmin is on `Ici c`.
    Given the left/right sign information for `P'` around `c`, we match the
    count contribution `[x₀=c] + [w=c] - 1` to `nonRootDiffFormula P c` via a
    4-way case analysis on (parity of `ν`) × (sign of `P(c) · P^(ν+1)(c)`). -/
private lemma nonRoot_case_cy_close_aux_A
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hdP : derivative P ≠ 0)
    {c : R} (hPc : P.eval c ≠ 0) {v : R} (hvc : v < c)
    {x₀ : R} (harg_x0 : IsArgminAbsOn P (Set.Icc v c) x₀)
    {w : R} (hw_arg : IsArgminAbsOn P (Set.Ici c) w)
    (hL_const_sign : ∀ x ∈ Set.Ioo v c,
      SignType.sign ((derivative P).eval x) =
        (-1 : SignType) ^ (derivative P).rootMultiplicity c *
          SignType.sign
            (((⇑derivative)^[(derivative P).rootMultiplicity c + 1] P).eval c))
    (hR_const_sign : ∀ x ∈ Set.Ioi c,
      SignType.sign ((derivative P).eval x) =
        SignType.sign
          (((⇑derivative)^[(derivative P).rootMultiplicity c + 1] P).eval c)) :
    (if x₀ = c then (1 : ℤ) else 0) + (if w = c then (1 : ℤ) else 0) - 1 =
      nonRootDiffFormula P c := by
  set ν := (derivative P).rootMultiplicity c with hν_def
  have hshift : (⇑derivative)^[ν + 1] P = (⇑derivative)^[ν] (derivative P) := by
    rw [Function.iterate_succ, Function.comp_apply]
  have hτR_ne : ((⇑derivative)^[ν + 1] P).eval c ≠ 0 := by
    rw [hshift]
    have h := Polynomial.eval_iterate_derivative_rootMultiplicity
      (p := derivative P) (t := c)
    rw [← hν_def] at h
    rw [h, nsmul_eq_mul]
    refine mul_ne_zero ?_
      (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hdP)
    exact_mod_cast Nat.factorial_ne_zero _
  have hστ_ne : P.eval c * ((⇑derivative)^[ν + 1] P).eval c ≠ 0 :=
    mul_ne_zero hPc hτR_ne
  have forward_x0 : x₀ = c → 0 < (-1 : R) ^ (ν + 1) * P.eval c *
      ((⇑derivative)^[ν + 1] P).eval c := fun hx0_eq => by
    subst hx0_eq
    have h := sign_of_isArgminAbsOn_right_boundary hIVP hdP hvc harg_x0 hPc
    rw [← hν_def] at h
    exact h
  have forward_w : w = c → 0 < P.eval c *
      ((⇑derivative)^[ν + 1] P).eval c := fun hw_eq => by
    have hw_arg_c : IsArgminAbsOn P (Set.Ici c) c := hw_eq ▸ hw_arg
    have hc_lt : c < c + 1 := lt_add_one c
    have hsub : Set.Icc c (c + 1) ⊆ Set.Ici c := fun _ hx => hx.1
    have hc_argmin_Icc : IsArgminAbsOn P (Set.Icc c (c + 1)) c := by
      refine ⟨⟨le_rfl, hc_lt.le⟩, ?_⟩
      intro x hx; exact hw_arg_c.2 x (hsub hx)
    have h := sign_of_isArgminAbsOn_left_boundary hIVP hdP hc_lt hc_argmin_Icc hPc
    rw [← hν_def] at h
    exact h
  have hsign_rel_pos : 0 < P.eval c * ((⇑derivative)^[ν + 1] P).eval c →
      SignType.sign (((⇑derivative)^[ν + 1] P).eval c) =
        SignType.sign (P.eval c) := by
    intro h
    rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
    · have hτR_neg : ((⇑derivative)^[ν + 1] P).eval c < 0 := by
        rcases lt_or_gt_of_ne hτR_ne with ht | ht
        · exact ht
        · exact absurd h (not_lt.mpr (mul_neg_of_neg_of_pos hPc_neg ht).le)
      rw [sign_neg hPc_neg, sign_neg hτR_neg]
    · have hτR_pos : 0 < ((⇑derivative)^[ν + 1] P).eval c := by
        rcases lt_or_gt_of_ne hτR_ne with ht | ht
        · exact absurd h (not_lt.mpr (mul_neg_of_pos_of_neg hPc_pos ht).le)
        · exact ht
      rw [sign_pos hPc_pos, sign_pos hτR_pos]
  have hsign_rel_neg : P.eval c * ((⇑derivative)^[ν + 1] P).eval c < 0 →
      SignType.sign (((⇑derivative)^[ν + 1] P).eval c) =
        -SignType.sign (P.eval c) := by
    intro h
    rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
    · have hτR_pos : 0 < ((⇑derivative)^[ν + 1] P).eval c := by
        rcases lt_or_gt_of_ne hτR_ne with ht | ht
        · exact absurd h (not_lt.mpr (mul_pos_of_neg_of_neg hPc_neg ht).le)
        · exact ht
      rw [sign_neg hPc_neg, sign_pos hτR_pos]; rfl
    · have hτR_neg : ((⇑derivative)^[ν + 1] P).eval c < 0 := by
        rcases lt_or_gt_of_ne hτR_ne with ht | ht
        · exact ht
        · exact absurd h (not_lt.mpr (mul_pos hPc_pos ht).le)
      rw [sign_pos hPc_pos, sign_neg hτR_neg]
  by_cases hν_even : Even ν
  · have hformula : nonRootDiffFormula P c = 0 := by
      unfold nonRootDiffFormula
      rw [hν_def] at hν_even
      rw [if_pos hν_even]
    rw [hformula]
    rcases lt_or_gt_of_ne hστ_ne with hστ_neg | hστ_pos
    · have hτ_eq := hsign_rel_neg hστ_neg
      have hhL : ∀ x ∈ Set.Ioo v c,
          SignType.sign ((derivative P).eval x) = -SignType.sign (P.eval c) := by
        intro x hx
        rw [hL_const_sign x hx, Even.neg_one_pow hν_even, one_mul, hτ_eq]
      have hx0_eq : x₀ = c :=
        argmin_right_of_derivSign_opp hIVP hvc hPc hhL harg_x0
      have hw_ne : w ≠ c := fun hw_eq => by linarith [forward_w hw_eq]
      rw [if_pos hx0_eq, if_neg hw_ne]; norm_num
    · have hτ_eq := hsign_rel_pos hστ_pos
      have hhR : ∀ x ∈ Set.Ioi c,
          SignType.sign ((derivative P).eval x) = SignType.sign (P.eval c) := by
        intro x hx
        rw [hR_const_sign x hx, hτ_eq]
      have hw_eq : w = c :=
        argmin_left_of_derivSign_same_Ici hIVP hPc hhR hw_arg
      have hx0_ne : x₀ ≠ c := fun hx0_eq => by
        have h := forward_x0 hx0_eq
        have hh : (-1 : R) ^ (ν + 1) * P.eval c * ((⇑derivative)^[ν + 1] P).eval c
                  = -(P.eval c * ((⇑derivative)^[ν + 1] P).eval c) := by
          rw [pow_succ, Even.neg_one_pow hν_even]; ring
        rw [hh] at h
        linarith
      rw [if_neg hx0_ne, if_pos hw_eq]; norm_num
  · have hν_odd : Odd ν := Nat.not_even_iff_odd.mp hν_even
    rcases lt_or_gt_of_ne hστ_ne with hστ_neg | hστ_pos
    · have hformula : nonRootDiffFormula P c = -1 := by
        unfold nonRootDiffFormula
        rw [hν_def] at hν_even
        rw [if_neg hν_even, if_neg (not_lt.mpr hστ_neg.le)]
      rw [hformula]
      have hw_ne : w ≠ c := fun hw_eq => by linarith [forward_w hw_eq]
      have hx0_ne : x₀ ≠ c := fun hx0_eq => by
        have h := forward_x0 hx0_eq
        have hpow : (-1 : R) ^ (ν + 1) = 1 := by
          rw [pow_succ, Odd.neg_one_pow hν_odd]; ring
        rw [hpow] at h
        linarith
      rw [if_neg hx0_ne, if_neg hw_ne]; norm_num
    · have hformula : nonRootDiffFormula P c = 1 := by
        unfold nonRootDiffFormula
        rw [hν_def] at hν_even
        rw [if_neg hν_even, if_pos hστ_pos]
      rw [hformula]
      have hτ_eq := hsign_rel_pos hστ_pos
      have hhL : ∀ x ∈ Set.Ioo v c,
          SignType.sign ((derivative P).eval x) = -SignType.sign (P.eval c) := by
        intro x hx
        rw [hL_const_sign x hx, Odd.neg_one_pow hν_odd, hτ_eq, neg_one_mul]
      have hx0_eq : x₀ = c :=
        argmin_right_of_derivSign_opp hIVP hvc hPc hhL harg_x0
      have hhR : ∀ x ∈ Set.Ioi c,
          SignType.sign ((derivative P).eval x) = SignType.sign (P.eval c) := by
        intro x hx
        rw [hR_const_sign x hx, hτ_eq]
      have hw_eq : w = c :=
        argmin_left_of_derivSign_same_Ici hIVP hPc hhR hw_arg
      rw [if_pos hx0_eq, if_pos hw_eq]; norm_num

/-- **Non-root `c = y` case, right-boundary `Icc c z` variant.** Same as
    `nonRoot_case_cy_close_aux_A` but the right-side argmin is on a bounded
    interval `Icc c z` (used when `ys_rest` starts with some `z > c`). -/
private lemma nonRoot_case_cy_close_aux_B
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hdP : derivative P ≠ 0)
    {c : R} (hPc : P.eval c ≠ 0) {v : R} (hvc : v < c)
    {z : R} (hcz : c < z)
    {x₀ : R} (harg_x0 : IsArgminAbsOn P (Set.Icc v c) x₀)
    {w : R} (hw_arg : IsArgminAbsOn P (Set.Icc c z) w)
    (hL_const_sign : ∀ x ∈ Set.Ioo v c,
      SignType.sign ((derivative P).eval x) =
        (-1 : SignType) ^ (derivative P).rootMultiplicity c *
          SignType.sign
            (((⇑derivative)^[(derivative P).rootMultiplicity c + 1] P).eval c))
    (hR_const_sign : ∀ x ∈ Set.Ioo c z,
      SignType.sign ((derivative P).eval x) =
        SignType.sign
          (((⇑derivative)^[(derivative P).rootMultiplicity c + 1] P).eval c)) :
    (if x₀ = c then (1 : ℤ) else 0) + (if w = c then (1 : ℤ) else 0) - 1 =
      nonRootDiffFormula P c := by
  set ν := (derivative P).rootMultiplicity c with hν_def
  have hshift : (⇑derivative)^[ν + 1] P = (⇑derivative)^[ν] (derivative P) := by
    rw [Function.iterate_succ, Function.comp_apply]
  have hτR_ne : ((⇑derivative)^[ν + 1] P).eval c ≠ 0 := by
    rw [hshift]
    have h := Polynomial.eval_iterate_derivative_rootMultiplicity
      (p := derivative P) (t := c)
    rw [← hν_def] at h
    rw [h, nsmul_eq_mul]
    refine mul_ne_zero ?_
      (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hdP)
    exact_mod_cast Nat.factorial_ne_zero _
  have hστ_ne : P.eval c * ((⇑derivative)^[ν + 1] P).eval c ≠ 0 :=
    mul_ne_zero hPc hτR_ne
  have forward_x0 : x₀ = c → 0 < (-1 : R) ^ (ν + 1) * P.eval c *
      ((⇑derivative)^[ν + 1] P).eval c := fun hx0_eq => by
    subst hx0_eq
    have h := sign_of_isArgminAbsOn_right_boundary hIVP hdP hvc harg_x0 hPc
    rw [← hν_def] at h
    exact h
  have forward_w : w = c → 0 < P.eval c *
      ((⇑derivative)^[ν + 1] P).eval c := fun hw_eq => by
    subst hw_eq
    have h := sign_of_isArgminAbsOn_left_boundary hIVP hdP hcz hw_arg hPc
    rw [← hν_def] at h
    exact h
  have hsign_rel_pos : 0 < P.eval c * ((⇑derivative)^[ν + 1] P).eval c →
      SignType.sign (((⇑derivative)^[ν + 1] P).eval c) =
        SignType.sign (P.eval c) := by
    intro h
    rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
    · have hτR_neg : ((⇑derivative)^[ν + 1] P).eval c < 0 := by
        rcases lt_or_gt_of_ne hτR_ne with ht | ht
        · exact ht
        · exact absurd h (not_lt.mpr (mul_neg_of_neg_of_pos hPc_neg ht).le)
      rw [sign_neg hPc_neg, sign_neg hτR_neg]
    · have hτR_pos : 0 < ((⇑derivative)^[ν + 1] P).eval c := by
        rcases lt_or_gt_of_ne hτR_ne with ht | ht
        · exact absurd h (not_lt.mpr (mul_neg_of_pos_of_neg hPc_pos ht).le)
        · exact ht
      rw [sign_pos hPc_pos, sign_pos hτR_pos]
  have hsign_rel_neg : P.eval c * ((⇑derivative)^[ν + 1] P).eval c < 0 →
      SignType.sign (((⇑derivative)^[ν + 1] P).eval c) =
        -SignType.sign (P.eval c) := by
    intro h
    rcases lt_or_gt_of_ne hPc with hPc_neg | hPc_pos
    · have hτR_pos : 0 < ((⇑derivative)^[ν + 1] P).eval c := by
        rcases lt_or_gt_of_ne hτR_ne with ht | ht
        · exact absurd h (not_lt.mpr (mul_pos_of_neg_of_neg hPc_neg ht).le)
        · exact ht
      rw [sign_neg hPc_neg, sign_pos hτR_pos]; rfl
    · have hτR_neg : ((⇑derivative)^[ν + 1] P).eval c < 0 := by
        rcases lt_or_gt_of_ne hτR_ne with ht | ht
        · exact ht
        · exact absurd h (not_lt.mpr (mul_pos hPc_pos ht).le)
      rw [sign_pos hPc_pos, sign_neg hτR_neg]
  by_cases hν_even : Even ν
  · have hformula : nonRootDiffFormula P c = 0 := by
      unfold nonRootDiffFormula
      rw [hν_def] at hν_even
      rw [if_pos hν_even]
    rw [hformula]
    rcases lt_or_gt_of_ne hστ_ne with hστ_neg | hστ_pos
    · have hτ_eq := hsign_rel_neg hστ_neg
      have hhL : ∀ x ∈ Set.Ioo v c,
          SignType.sign ((derivative P).eval x) = -SignType.sign (P.eval c) := by
        intro x hx
        rw [hL_const_sign x hx, Even.neg_one_pow hν_even, one_mul, hτ_eq]
      have hx0_eq : x₀ = c :=
        argmin_right_of_derivSign_opp hIVP hvc hPc hhL harg_x0
      have hw_ne : w ≠ c := fun hw_eq => by linarith [forward_w hw_eq]
      rw [if_pos hx0_eq, if_neg hw_ne]; norm_num
    · have hτ_eq := hsign_rel_pos hστ_pos
      have hhR : ∀ x ∈ Set.Ioo c z,
          SignType.sign ((derivative P).eval x) = SignType.sign (P.eval c) := by
        intro x hx
        rw [hR_const_sign x hx, hτ_eq]
      have hw_eq : w = c :=
        argmin_left_of_derivSign_same hIVP hcz hPc hhR hw_arg
      have hx0_ne : x₀ ≠ c := fun hx0_eq => by
        have h := forward_x0 hx0_eq
        have hh : (-1 : R) ^ (ν + 1) * P.eval c * ((⇑derivative)^[ν + 1] P).eval c
                  = -(P.eval c * ((⇑derivative)^[ν + 1] P).eval c) := by
          rw [pow_succ, Even.neg_one_pow hν_even]; ring
        rw [hh] at h
        linarith
      rw [if_neg hx0_ne, if_pos hw_eq]; norm_num
  · have hν_odd : Odd ν := Nat.not_even_iff_odd.mp hν_even
    rcases lt_or_gt_of_ne hστ_ne with hστ_neg | hστ_pos
    · have hformula : nonRootDiffFormula P c = -1 := by
        unfold nonRootDiffFormula
        rw [hν_def] at hν_even
        rw [if_neg hν_even, if_neg (not_lt.mpr hστ_neg.le)]
      rw [hformula]
      have hw_ne : w ≠ c := fun hw_eq => by linarith [forward_w hw_eq]
      have hx0_ne : x₀ ≠ c := fun hx0_eq => by
        have h := forward_x0 hx0_eq
        have hpow : (-1 : R) ^ (ν + 1) = 1 := by
          rw [pow_succ, Odd.neg_one_pow hν_odd]; ring
        rw [hpow] at h
        linarith
      rw [if_neg hx0_ne, if_neg hw_ne]; norm_num
    · have hformula : nonRootDiffFormula P c = 1 := by
        unfold nonRootDiffFormula
        rw [hν_def] at hν_even
        rw [if_neg hν_even, if_pos hστ_pos]
      rw [hformula]
      have hτ_eq := hsign_rel_pos hστ_pos
      have hhL : ∀ x ∈ Set.Ioo v c,
          SignType.sign ((derivative P).eval x) = -SignType.sign (P.eval c) := by
        intro x hx
        rw [hL_const_sign x hx, Odd.neg_one_pow hν_odd, hτ_eq, neg_one_mul]
      have hx0_eq : x₀ = c :=
        argmin_right_of_derivSign_opp hIVP hvc hPc hhL harg_x0
      have hhR : ∀ x ∈ Set.Ioo c z,
          SignType.sign ((derivative P).eval x) = SignType.sign (P.eval c) := by
        intro x hx
        rw [hR_const_sign x hx, hτ_eq]
      have hw_eq : w = c :=
        argmin_left_of_derivSign_same hIVP hcz hPc hhR hw_arg
      rw [if_pos hx0_eq, if_pos hw_eq]; norm_num

/-- Non-root version of `count_eq_of_root_from_aux`: along the argmin chain,
    the difference of counts of `c` in `xs` vs. `ys` equals the sign-dependent
    formula `nonRootDiffFormula P c`. -/
private lemma count_diff_of_not_root_from_aux
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hdP : derivative P ≠ 0) {ys_full : List R}
    (hys_full_sort : ys_full.Pairwise (· ≤ ·))
    (hsg_ys : SignConstantOnGaps (derivative P) ys_full)
    {c : R} (hPc : P.eval c ≠ 0) :
    ∀ {xs ys : List R} {v : R} {past : List R},
      ys_full = past ++ ys →
      Interlaced xs ys →
      ArgminPartitionFrom P v xs ys →
      v < c →
      (∀ p ∈ past, p ≤ v) →
      (xs.count c : ℤ) - (ys.count c : ℤ) = nonRootDiffFormula P c := by
  intro xs ys
  induction ys generalizing xs with
  | nil =>
    intro v past hsplit hi harg hvc hpast
    match xs, hi with
    | [z], _ =>
      change IsArgminAbsOn P (Set.Ici v) z at harg
      -- `ys_full = past`, all ≤ v < c. So c ∉ ys_full, hence ν = 0 and
      -- formula = 0. We need z ≠ c; this follows from Helper 1 applied
      -- via an Icc subinterval containing c strictly.
      have hc_notin_full : c ∉ ys_full := by
        intro hc_mem
        have : c ≤ v := by
          rw [hsplit, List.append_nil] at hc_mem
          exact hpast c hc_mem
        exact absurd this (not_le.mpr hvc)
      have hP'c : (derivative P).eval c ≠ 0 :=
        eval_ne_zero_of_not_mem_of_signConstantOnGaps hsg_ys hc_notin_full
      have hnu_zero : (derivative P).rootMultiplicity c = 0 :=
        Polynomial.rootMultiplicity_eq_zero hP'c
      have hformula_zero : nonRootDiffFormula P c = 0 := by
        unfold nonRootDiffFormula
        rw [hnu_zero]
        simp
      -- Show z ≠ c by restricting the argmin to Icc v (c + 1).
      have hc_lt_cp1 : c < c + 1 := lt_add_one c
      have hz_ne : z ≠ c := by
        intro hz_eq
        rw [hz_eq] at harg
        -- Now harg : IsArgminAbsOn P (Set.Ici v) c. Restrict to Icc v (c+1).
        have hsub : Set.Icc v (c + 1) ⊆ Set.Ici v := fun _ hx => hx.1
        have hc_mem : c ∈ Set.Icc v (c + 1) := ⟨hvc.le, hc_lt_cp1.le⟩
        have hc_argmin_Icc : IsArgminAbsOn P (Set.Icc v (c + 1)) c := by
          refine ⟨hc_mem, ?_⟩
          intro x hx
          exact harg.2 x (hsub hx)
        exact hP'c (deriv_eq_zero_of_isArgminAbsOn_interior hIVP hvc
          hc_lt_cp1 hc_argmin_Icc hPc)
      rw [List.count_cons_of_ne hz_ne, List.count_nil, hformula_zero]
      simp
    | x₀ :: _ :: _, hi => exact absurd hi (by simp [Interlaced])
    | [], hi => exact absurd hi (by simp [Interlaced])
  | cons y ys' ih =>
    intro v past hsplit hi harg hvc hpast
    match xs, hi, harg with
    | [], hi, _ => exact absurd hi (by simp [Interlaced])
    | [_], hi, _ => exact absurd hi (by simp [Interlaced])
    | x₀ :: x₁ :: xs'', hi, harg =>
      obtain ⟨h_x0_le_y, h_y_le_x1, hi_rest⟩ := hi
      change IsArgminAbsOn P (Set.Icc v y) x₀ ∧
        ArgminPartitionFrom P y (x₁ :: xs'') ys' at harg
      obtain ⟨harg_x0, harg_rest⟩ := harg
      have hpw_suff : (y :: ys').Pairwise (· ≤ ·) := by
        have h := hys_full_sort
        rw [hsplit, List.pairwise_append] at h
        exact h.2.1
      have hy_le_ys' : ∀ y' ∈ ys', y ≤ y' := (List.pairwise_cons.mp hpw_suff).1
      have _hys'_sort : ys'.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hpw_suff).2
      have _hv_le_y : v ≤ y := harg_x0.1.1.trans harg_x0.1.2
      have hpast' : ∀ p ∈ past ++ [y], p ≤ y := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact (hpast p hp).trans _hv_le_y
        · rcases List.mem_cons.mp hp with rfl | h
          · exact le_refl _
          · exact absurd h List.not_mem_nil
      have hsplit' : ys_full = (past ++ [y]) ++ ys' := by
        rw [List.append_assoc, List.singleton_append]; exact hsplit
      rcases lt_trichotomy c y with hcy_lt | hcy_eq | hyc_lt
      · -- Case c < y: terminal. v < c < y, so c strictly interior of [v, y].
        -- All of `y :: ys'` and `x₁ :: xs''` are > c. Only `x₀` might equal c.
        -- c ∉ ys_full (strictly between gap), so ν = 0, formula = 0.
        -- Helper (1) gives x₀ ≠ c. LHS = 0 = formula.
        have hys_gt : ∀ a ∈ y :: ys', c < a := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | h
          · exact hcy_lt
          · exact hcy_lt.trans_le (hy_le_ys' a h)
        have hys_count : (y :: ys').count c = 0 :=
          List.count_eq_zero.mpr (fun hm => (hys_gt c hm).ne' rfl)
        have hxs_sort := Interlaced.pairwise_of_ys hi_rest _hys'_sort
        have hxs_gt : ∀ a ∈ x₁ :: xs'', c < a := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | h
          · exact hcy_lt.trans_le h_y_le_x1
          · exact (hcy_lt.trans_le h_y_le_x1).trans_le
              ((List.pairwise_cons.mp hxs_sort).1 a h)
        have hxs'_count : (x₁ :: xs'').count c = 0 :=
          List.count_eq_zero.mpr (fun hm => (hxs_gt c hm).ne' rfl)
        have hc_notin_past : c ∉ past := fun hp =>
          absurd (hpast c hp) (not_le.mpr hvc)
        have hc_notin_yys : c ∉ y :: ys' := fun hp =>
          absurd (hys_gt c hp) (lt_irrefl c)
        have hc_notin_full : c ∉ ys_full := by
          rw [hsplit]
          intro hm
          rcases List.mem_append.mp hm with h | h
          · exact hc_notin_past h
          · exact hc_notin_yys h
        have hP'c : (derivative P).eval c ≠ 0 :=
          eval_ne_zero_of_not_mem_of_signConstantOnGaps hsg_ys hc_notin_full
        have hnu_zero : (derivative P).rootMultiplicity c = 0 :=
          Polynomial.rootMultiplicity_eq_zero hP'c
        have hformula_zero : nonRootDiffFormula P c = 0 := by
          unfold nonRootDiffFormula
          rw [hnu_zero]
          simp
        have hx0_ne : x₀ ≠ c := by
          intro hx0_eq
          subst hx0_eq
          exact hP'c (deriv_eq_zero_of_isArgminAbsOn_interior hIVP hvc
            hcy_lt harg_x0 hPc)
        rw [List.count_cons_of_ne hx0_ne, hxs'_count, hys_count,
          hformula_zero]
        simp
      · -- Case c = y: c lies on the right endpoint [v, y] = [v, c].
        -- Right-boundary argmin at c for x₀, then continue past the c-block.
        subst hcy_eq
        set ν := (derivative P).rootMultiplicity c with hν_def
        have hshift : (⇑derivative)^[ν + 1] P = (⇑derivative)^[ν] (derivative P) := by
          rw [Function.iterate_succ, Function.comp_apply]
        have hτR_ne : ((⇑derivative)^[ν + 1] P).eval c ≠ 0 := by
          rw [hshift]
          have h := Polynomial.eval_iterate_derivative_rootMultiplicity
            (p := derivative P) (t := c)
          rw [← hν_def] at h
          rw [h, nsmul_eq_mul]
          refine mul_ne_zero ?_
            (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hdP)
          exact_mod_cast Nat.factorial_ne_zero _
        have hστR_ne : P.eval c * ((⇑derivative)^[ν + 1] P).eval c ≠ 0 :=
          mul_ne_zero hPc hτR_ne
        have hP'_sl : HasSignLeft (derivative P) c
            ((-1 : SignType) ^ ν *
              SignType.sign (((⇑derivative)^[ν + 1] P).eval c)) := by
          have h := proposition_2_21_left hIVP hdP c
          rw [← hν_def, ← hshift] at h; exact h
        have hP'_sr : HasSignRight (derivative P) c
            (SignType.sign (((⇑derivative)^[ν + 1] P).eval c)) := by
          have h := proposition_2_21_right hIVP hdP c
          rw [← hν_def, ← hshift] at h; exact h
        obtain ⟨m, xs_rest, ys_rest, hys'_eq, hxs1_eq, harg_split, hend⟩ :=
          argminPartitionFrom_c_split P c ys' (x₁ :: xs'') hy_le_ys' harg_rest
        have hys_rest_sort : ys_rest.Pairwise (· ≤ ·) := by
          have h := _hys'_sort
          rw [hys'_eq, List.pairwise_append] at h
          exact h.2.1
        obtain ⟨w, xs_tail, hxs_rest_eq, hxs_rest_count, hys_rest_count,
          hbdy_arg⟩ :=
          argminPartitionFrom_c_tail_count harg_split hys_rest_sort hend
        have hrepl_count : (List.replicate m c).count c = m := by
          rw [List.count_replicate]; simp
        have hys_count_eq : (c :: ys').count c = m + 1 := by
          rw [List.count_cons_self, hys'_eq, List.count_append, hrepl_count,
            hys_rest_count]
        have hxs1_count_eq :
            (x₁ :: xs'').count c = m + (if w = c then 1 else 0) := by
          rw [hxs1_eq, List.count_append, hrepl_count, hxs_rest_count]
        have hcount_diff :
            ((x₀ :: x₁ :: xs'').count c : ℤ) - ((c :: ys').count c : ℤ)
              = (if x₀ = c then 1 else 0) + (if w = c then 1 else 0) - 1 := by
          by_cases hx0 : x₀ = c
          · rw [if_pos hx0, hx0, List.count_cons_self, hxs1_count_eq,
              hys_count_eq]
            push_cast; split_ifs <;> ring
          · rw [if_neg hx0, List.count_cons_of_ne hx0, hxs1_count_eq,
              hys_count_eq]
            push_cast; split_ifs <;> ring
        rw [hcount_diff]
        have hgap_out_L : ∀ r ∈ ys_full, r ≤ v ∨ c ≤ r := by
          intro r hr
          rw [hsplit] at hr
          rcases List.mem_append.mp hr with hp | hs
          · exact Or.inl (hpast r hp)
          · rcases List.mem_cons.mp hs with rfl | hin
            · exact Or.inr le_rfl
            · exact Or.inr (hy_le_ys' r hin)
        have hL_dich := sign_dichotomy_Ioo hsg_ys hvc hgap_out_L
        have hL_const_sign : ∀ x ∈ Set.Ioo v c,
            SignType.sign ((derivative P).eval x) =
              (-1 : SignType) ^ ν *
                SignType.sign (((⇑derivative)^[ν + 1] P).eval c) := by
          obtain ⟨b'L, hb'L_lt_c, hb'L_sign⟩ := hP'_sl
          have hmax_lt : max v b'L < c := max_lt hvc hb'L_lt_c
          obtain ⟨xL, hxL_gt, hxL_lt⟩ := exists_between hmax_lt
          have hv_lt_xL : v < xL := lt_of_le_of_lt (le_max_left _ _) hxL_gt
          have hb'L_lt_xL : b'L < xL :=
            lt_of_le_of_lt (le_max_right _ _) hxL_gt
          have hxL_sign := hb'L_sign xL ⟨hb'L_lt_xL, hxL_lt⟩
          intro x hx
          rcases hL_dich with hL_pos | hL_neg
          · rw [sign_pos (hL_pos xL ⟨hv_lt_xL, hxL_lt⟩)] at hxL_sign
            rw [sign_pos (hL_pos x hx)]; exact hxL_sign
          · rw [sign_neg (hL_neg xL ⟨hv_lt_xL, hxL_lt⟩)] at hxL_sign
            rw [sign_neg (hL_neg x hx)]; exact hxL_sign
        -- Case split on hbdy_arg (Ici c vs Icc c z), then 4-way on parity × sign.
        rcases hbdy_arg with
          ⟨hys_rest_nil, hw_arg_Ici⟩ |
          ⟨z, ys_r, _hys_rest_eq_cons, hczR, hw_arg_Icc⟩
        · -- Case A: ys_rest = []. All of ys_full ≤ c.
          have hle_ys_full : ∀ r ∈ ys_full, r ≤ c := by
            intro r hr
            rw [hsplit] at hr
            rcases List.mem_append.mp hr with hp | hs
            · exact (hpast r hp).trans hvc.le
            · rcases List.mem_cons.mp hs with rfl | hin
              · exact le_rfl
              · rw [hys'_eq, hys_rest_nil, List.append_nil,
                  List.mem_replicate] at hin
                exact le_of_eq hin.2
          have hR_dich := sign_dichotomy_Ioi hsg_ys hle_ys_full
          have hR_const_sign : ∀ x ∈ Set.Ioi c,
              SignType.sign ((derivative P).eval x) =
                SignType.sign (((⇑derivative)^[ν + 1] P).eval c) := by
            obtain ⟨b'R, hc_lt_b'R, hb'R_sign⟩ := hP'_sr
            obtain ⟨xR, hcxR, hxR_lt⟩ := exists_between hc_lt_b'R
            have hxR_sign := hb'R_sign xR ⟨hcxR, hxR_lt⟩
            intro x hx
            rcases hR_dich with hR_pos | hR_neg
            · rw [sign_pos (hR_pos xR hcxR)] at hxR_sign
              rw [sign_pos (hR_pos x hx)]; exact hxR_sign
            · rw [sign_neg (hR_neg xR hcxR)] at hxR_sign
              rw [sign_neg (hR_neg x hx)]; exact hxR_sign
          exact nonRoot_case_cy_close_aux_A hIVP hdP hPc hvc harg_x0
            hw_arg_Ici hL_const_sign hR_const_sign
        · -- Case B: ys_rest = z :: ys_r, c < z.
          have hgap_out_R : ∀ r ∈ ys_full, r ≤ c ∨ z ≤ r := by
            intro r hr
            rw [hsplit] at hr
            rcases List.mem_append.mp hr with hp | hs
            · exact Or.inl ((hpast r hp).trans hvc.le)
            · rcases List.mem_cons.mp hs with rfl | hin
              · exact Or.inl le_rfl
              · rw [hys'_eq] at hin
                rcases List.mem_append.mp hin with hrepl | hrest
                · rw [List.mem_replicate] at hrepl
                  exact Or.inl (le_of_eq hrepl.2)
                · rw [_hys_rest_eq_cons] at hrest
                  rcases List.mem_cons.mp hrest with rfl | hrin
                  · exact Or.inr le_rfl
                  · have hys_rest_sort' := hys_rest_sort
                    rw [_hys_rest_eq_cons] at hys_rest_sort'
                    exact Or.inr
                      ((List.pairwise_cons.mp hys_rest_sort').1 r hrin)
          have hR_dich := sign_dichotomy_Ioo hsg_ys hczR hgap_out_R
          have hR_const_sign : ∀ x ∈ Set.Ioo c z,
              SignType.sign ((derivative P).eval x) =
                SignType.sign (((⇑derivative)^[ν + 1] P).eval c) := by
            obtain ⟨b'R, hc_lt_b'R, hb'R_sign⟩ := hP'_sr
            have hmin_gt : c < min b'R z := lt_min hc_lt_b'R hczR
            obtain ⟨xR, hcxR, hxR_lt⟩ := exists_between hmin_gt
            have hxR_lt_b'R : xR < b'R := lt_of_lt_of_le hxR_lt (min_le_left _ _)
            have hxR_lt_z : xR < z := lt_of_lt_of_le hxR_lt (min_le_right _ _)
            have hxR_sign := hb'R_sign xR ⟨hcxR, hxR_lt_b'R⟩
            intro x hx
            rcases hR_dich with hR_pos | hR_neg
            · rw [sign_pos (hR_pos xR ⟨hcxR, hxR_lt_z⟩)] at hxR_sign
              rw [sign_pos (hR_pos x hx)]; exact hxR_sign
            · rw [sign_neg (hR_neg xR ⟨hcxR, hxR_lt_z⟩)] at hxR_sign
              rw [sign_neg (hR_neg x hx)]; exact hxR_sign
          exact nonRoot_case_cy_close_aux_B hIVP hdP hPc hvc hczR harg_x0
            hw_arg_Icc hL_const_sign hR_const_sign
      · -- Case y < c: past the current interval; recurse with v ← y (< c strict).
        have hx0_ne : x₀ ≠ c := ne_of_lt (lt_of_le_of_lt harg_x0.1.2 hyc_lt)
        have hy_ne : y ≠ c := ne_of_lt hyc_lt
        have hrec := ih (v := y) (past := past ++ [y])
          hsplit' hi_rest harg_rest hyc_lt hpast'
        rw [List.count_cons_of_ne hx0_ne, List.count_cons_of_ne hy_ne]
        exact hrec

/-- **Non-root count identity.** If `xs`, `ys` satisfy the virtual-roots
    structure (interlaced, sorted, argmin-partitioning `|P|`, with `P'`
    sign-constant on `ys`-gaps) and `P.eval c ≠ 0`, then

    ```
    (xs.count c : ℤ) − (ys.count c : ℤ) = nonRootDiffFormula P c
    ```

    The proof dispatches on the shape of the chain and on the trichotomy of
    `c` vs. the first entry of `ys`, delegating the main induction to
    `count_diff_of_not_root_from_aux`. -/
lemma count_diff_of_not_root
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hdP : derivative P ≠ 0)
    {xs ys : List R}
    (hi : Interlaced xs ys)
    (hys_sort : ys.Pairwise (· ≤ ·))
    (harg : ArgminPartition P xs ys)
    (hsg_ys : SignConstantOnGaps (derivative P) ys)
    {c : R} (hPc : P.eval c ≠ 0) :
    (xs.count c : ℤ) - (ys.count c : ℤ) = nonRootDiffFormula P c := by
  match xs, ys, hi, harg with
  | [], ys, hi, _ => exact absurd hi (by cases ys <;> simp [Interlaced])
  | [_], _ :: _, hi, _ => exact absurd hi (by simp [Interlaced])
  | _ :: _ :: _, [], hi, _ => exact absurd hi (by simp [Interlaced])
  | [z], [], _, harg =>
    change IsArgminAbsOn P Set.univ z at harg
    -- ys = [], so c ∉ ys vacuously. Sign constancy on the full line gives
    -- P'(c) ≠ 0, hence ν = 0, formula = 0. Helper 1 on Icc (c-1) (c+1) rules
    -- out z = c.
    have hP'c : (derivative P).eval c ≠ 0 :=
      eval_ne_zero_of_not_mem_of_signConstantOnGaps hsg_ys List.not_mem_nil
    have hnu_zero : (derivative P).rootMultiplicity c = 0 :=
      Polynomial.rootMultiplicity_eq_zero hP'c
    have hformula_zero : nonRootDiffFormula P c = 0 := by
      unfold nonRootDiffFormula; rw [hnu_zero]; simp
    have hc_lt_cp1 : c < c + 1 := lt_add_one c
    have hcm1_lt : c - 1 < c := sub_one_lt c
    have hz_ne : z ≠ c := by
      intro hz_eq
      rw [hz_eq] at harg
      have hc_argmin_Icc : IsArgminAbsOn P (Set.Icc (c - 1) (c + 1)) c := by
        refine ⟨⟨hcm1_lt.le, hc_lt_cp1.le⟩, ?_⟩
        intro x _
        exact harg.2 x (Set.mem_univ x)
      exact hP'c (deriv_eq_zero_of_isArgminAbsOn_interior hIVP hcm1_lt
        hc_lt_cp1 hc_argmin_Icc hPc)
    rw [List.count_cons_of_ne hz_ne, List.count_nil, hformula_zero]
    simp
  | x₀ :: x₁ :: xs'', y :: ys', hi, harg =>
    obtain ⟨h_x0_le_y, h_y_le_x1, hi_rest⟩ := hi
    change IsArgminAbsOn P (Set.Iic y) x₀ ∧
      ArgminPartitionFrom P y (x₁ :: xs'') ys' at harg
    obtain ⟨harg_x0, harg_rest⟩ := harg
    have hy_le_ys : ∀ y' ∈ y :: ys', y ≤ y' := by
      intro y' hy'
      rcases List.mem_cons.mp hy' with rfl | h
      · exact le_refl _
      · exact (List.pairwise_cons.mp hys_sort).1 y' h
    rcases lt_trichotomy c y with hcy_lt | hcy_eq | hyc_lt
    · -- Case c < y: x₀ argmin on Iic y, c strictly interior (c < y).
      -- All of `y :: ys'` and `x₁ :: xs''` are > c, and c ∉ ys, so ν = 0,
      -- formula = 0. Helper 1 (via restriction to Icc (c-1) y) gives x₀ ≠ c.
      have hys_gt : ∀ a ∈ y :: ys', c < a := fun a ha =>
        lt_of_lt_of_le hcy_lt (hy_le_ys a ha)
      have hys_count : (y :: ys').count c = 0 :=
        List.count_eq_zero.mpr (fun hm => (hys_gt c hm).ne' rfl)
      have hys'_sort : ys'.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hys_sort).2
      have hxs_sort : (x₁ :: xs'').Pairwise (· ≤ ·) :=
        Interlaced.pairwise_of_ys hi_rest hys'_sort
      have hxs_gt : ∀ a ∈ x₁ :: xs'', c < a := by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | h
        · exact hcy_lt.trans_le h_y_le_x1
        · exact (hcy_lt.trans_le h_y_le_x1).trans_le
            ((List.pairwise_cons.mp hxs_sort).1 a h)
      have hxs'_count : (x₁ :: xs'').count c = 0 :=
        List.count_eq_zero.mpr (fun hm => (hxs_gt c hm).ne' rfl)
      have hc_notin : c ∉ y :: ys' := fun hm => (hys_gt c hm).ne' rfl
      have hP'c : (derivative P).eval c ≠ 0 :=
        eval_ne_zero_of_not_mem_of_signConstantOnGaps hsg_ys hc_notin
      have hnu_zero : (derivative P).rootMultiplicity c = 0 :=
        Polynomial.rootMultiplicity_eq_zero hP'c
      have hformula_zero : nonRootDiffFormula P c = 0 := by
        unfold nonRootDiffFormula; rw [hnu_zero]; simp
      have hcm1_lt : c - 1 < c := sub_one_lt c
      have hx0_ne : x₀ ≠ c := by
        intro hx0_eq
        rw [hx0_eq] at harg_x0
        have hc_argmin_Icc : IsArgminAbsOn P (Set.Icc (c - 1) y) c := by
          refine ⟨⟨hcm1_lt.le, hcy_lt.le⟩, ?_⟩
          intro x hx
          exact harg_x0.2 x hx.2
        exact hP'c (deriv_eq_zero_of_isArgminAbsOn_interior hIVP hcm1_lt
          hcy_lt hc_argmin_Icc hPc)
      rw [List.count_cons_of_ne hx0_ne, hxs'_count, hys_count, hformula_zero]
      simp
    · -- Case c = y: reduce the `Iic c` argmin on x₀ to an `Icc v c` argmin
      -- (with `v = x₀ - 1`), then dispatch to the `nonRoot_case_cy_close_aux`
      -- helpers after the c-block split.
      subst hcy_eq
      have hx0_le_c : x₀ ≤ c := harg_x0.1
      set v := x₀ - 1 with hv_def
      have hv_le_x0 : v ≤ x₀ := by rw [hv_def]; linarith
      have hvc : v < c := by rw [hv_def]; linarith
      have harg_x0_Icc : IsArgminAbsOn P (Set.Icc v c) x₀ :=
        ⟨⟨hv_le_x0, hx0_le_c⟩, fun x hx => harg_x0.2 x hx.2⟩
      set ν := (derivative P).rootMultiplicity c with hν_def
      have hshift : (⇑derivative)^[ν + 1] P = (⇑derivative)^[ν] (derivative P) := by
        rw [Function.iterate_succ, Function.comp_apply]
      have hτR_ne : ((⇑derivative)^[ν + 1] P).eval c ≠ 0 := by
        rw [hshift]
        have h := Polynomial.eval_iterate_derivative_rootMultiplicity
          (p := derivative P) (t := c)
        rw [← hν_def] at h
        rw [h, nsmul_eq_mul]
        refine mul_ne_zero ?_
          (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hdP)
        exact_mod_cast Nat.factorial_ne_zero _
      have hP'_sl : HasSignLeft (derivative P) c
          ((-1 : SignType) ^ ν *
            SignType.sign (((⇑derivative)^[ν + 1] P).eval c)) := by
        have h := proposition_2_21_left hIVP hdP c
        rw [← hν_def, ← hshift] at h; exact h
      have hP'_sr : HasSignRight (derivative P) c
          (SignType.sign (((⇑derivative)^[ν + 1] P).eval c)) := by
        have h := proposition_2_21_right hIVP hdP c
        rw [← hν_def, ← hshift] at h; exact h
      have hy_le_ys' : ∀ y' ∈ ys', c ≤ y' := (List.pairwise_cons.mp hys_sort).1
      obtain ⟨m, xs_rest, ys_rest, hys'_eq, hxs1_eq, harg_split, hend⟩ :=
        argminPartitionFrom_c_split P c ys' (x₁ :: xs'') hy_le_ys' harg_rest
      have hys_rest_sort : ys_rest.Pairwise (· ≤ ·) := by
        have h := (List.pairwise_cons.mp hys_sort).2
        rw [hys'_eq, List.pairwise_append] at h
        exact h.2.1
      obtain ⟨w, xs_tail, hxs_rest_eq, hxs_rest_count, hys_rest_count,
        hbdy_arg⟩ :=
        argminPartitionFrom_c_tail_count harg_split hys_rest_sort hend
      have hrepl_count : (List.replicate m c).count c = m := by
        rw [List.count_replicate]; simp
      have hys_count_eq : (c :: ys').count c = m + 1 := by
        rw [List.count_cons_self, hys'_eq, List.count_append, hrepl_count,
          hys_rest_count]
      have hxs1_count_eq :
          (x₁ :: xs'').count c = m + (if w = c then 1 else 0) := by
        rw [hxs1_eq, List.count_append, hrepl_count, hxs_rest_count]
      have hcount_diff :
          ((x₀ :: x₁ :: xs'').count c : ℤ) - ((c :: ys').count c : ℤ)
            = (if x₀ = c then 1 else 0) + (if w = c then 1 else 0) - 1 := by
        by_cases hx0 : x₀ = c
        · rw [if_pos hx0, hx0, List.count_cons_self, hxs1_count_eq,
            hys_count_eq]
          push_cast; split_ifs <;> ring
        · rw [if_neg hx0, List.count_cons_of_ne hx0, hxs1_count_eq,
            hys_count_eq]
          push_cast; split_ifs <;> ring
      rw [hcount_diff]
      have hle_ys : ∀ r ∈ c :: ys', c ≤ r := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hin
        · exact le_rfl
        · exact hy_le_ys' r hin
      have hL_dich := sign_dichotomy_Iio hsg_ys hle_ys
      have hL_const_sign : ∀ x ∈ Set.Ioo v c,
          SignType.sign ((derivative P).eval x) =
            (-1 : SignType) ^ ν *
              SignType.sign (((⇑derivative)^[ν + 1] P).eval c) := by
        obtain ⟨b'L, hb'L_lt_c, hb'L_sign⟩ := hP'_sl
        obtain ⟨xL, hxL_gt, hxL_lt⟩ := exists_between hb'L_lt_c
        have hxL_sign := hb'L_sign xL ⟨hxL_gt, hxL_lt⟩
        intro x hx
        rcases hL_dich with hL_pos | hL_neg
        · rw [sign_pos (hL_pos xL hxL_lt)] at hxL_sign
          rw [sign_pos (hL_pos x hx.2)]; exact hxL_sign
        · rw [sign_neg (hL_neg xL hxL_lt)] at hxL_sign
          rw [sign_neg (hL_neg x hx.2)]; exact hxL_sign
      rcases hbdy_arg with
        ⟨hys_rest_nil, hw_arg_Ici⟩ |
        ⟨z, ys_r, _hys_rest_eq_cons, hczR, hw_arg_Icc⟩
      · -- Case A: ys_rest = []. All of c :: ys' ≤ c.
        have hle_ys_full : ∀ r ∈ c :: ys', r ≤ c := by
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hin
          · exact le_rfl
          · rw [hys'_eq, hys_rest_nil, List.append_nil,
              List.mem_replicate] at hin
            exact le_of_eq hin.2
        have hR_dich := sign_dichotomy_Ioi hsg_ys hle_ys_full
        have hR_const_sign : ∀ x ∈ Set.Ioi c,
            SignType.sign ((derivative P).eval x) =
              SignType.sign (((⇑derivative)^[ν + 1] P).eval c) := by
          obtain ⟨b'R, hc_lt_b'R, hb'R_sign⟩ := hP'_sr
          obtain ⟨xR, hcxR, hxR_lt⟩ := exists_between hc_lt_b'R
          have hxR_sign := hb'R_sign xR ⟨hcxR, hxR_lt⟩
          intro x hx
          rcases hR_dich with hR_pos | hR_neg
          · rw [sign_pos (hR_pos xR hcxR)] at hxR_sign
            rw [sign_pos (hR_pos x hx)]; exact hxR_sign
          · rw [sign_neg (hR_neg xR hcxR)] at hxR_sign
            rw [sign_neg (hR_neg x hx)]; exact hxR_sign
        exact nonRoot_case_cy_close_aux_A hIVP hdP hPc hvc harg_x0_Icc
          hw_arg_Ici hL_const_sign hR_const_sign
      · -- Case B: ys_rest = z :: ys_r, c < z.
        have hgap_out_R : ∀ r ∈ c :: ys', r ≤ c ∨ z ≤ r := by
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hin
          · exact Or.inl le_rfl
          · rw [hys'_eq] at hin
            rcases List.mem_append.mp hin with hrepl | hrest
            · rw [List.mem_replicate] at hrepl
              exact Or.inl (le_of_eq hrepl.2)
            · rw [_hys_rest_eq_cons] at hrest
              rcases List.mem_cons.mp hrest with rfl | hrin
              · exact Or.inr le_rfl
              · have hys_rest_sort' := hys_rest_sort
                rw [_hys_rest_eq_cons] at hys_rest_sort'
                exact Or.inr
                  ((List.pairwise_cons.mp hys_rest_sort').1 r hrin)
        have hR_dich := sign_dichotomy_Ioo hsg_ys hczR hgap_out_R
        have hR_const_sign : ∀ x ∈ Set.Ioo c z,
            SignType.sign ((derivative P).eval x) =
              SignType.sign (((⇑derivative)^[ν + 1] P).eval c) := by
          obtain ⟨b'R, hc_lt_b'R, hb'R_sign⟩ := hP'_sr
          have hmin_gt : c < min b'R z := lt_min hc_lt_b'R hczR
          obtain ⟨xR, hcxR, hxR_lt⟩ := exists_between hmin_gt
          have hxR_lt_b'R : xR < b'R := lt_of_lt_of_le hxR_lt (min_le_left _ _)
          have hxR_lt_z : xR < z := lt_of_lt_of_le hxR_lt (min_le_right _ _)
          have hxR_sign := hb'R_sign xR ⟨hcxR, hxR_lt_b'R⟩
          intro x hx
          rcases hR_dich with hR_pos | hR_neg
          · rw [sign_pos (hR_pos xR ⟨hcxR, hxR_lt_z⟩)] at hxR_sign
            rw [sign_pos (hR_pos x hx)]; exact hxR_sign
          · rw [sign_neg (hR_neg xR ⟨hcxR, hxR_lt_z⟩)] at hxR_sign
            rw [sign_neg (hR_neg x hx)]; exact hxR_sign
        exact nonRoot_case_cy_close_aux_B hIVP hdP hPc hvc hczR harg_x0_Icc
          hw_arg_Icc hL_const_sign hR_const_sign
    · -- Case y < c: x₀ ≤ y < c, so x₀ ≠ c and y ≠ c. Recurse via the aux.
      have hx0_ne : x₀ ≠ c := ne_of_lt (lt_of_le_of_lt harg_x0.1 hyc_lt)
      have hy_ne : y ≠ c := ne_of_lt hyc_lt
      have hsplit : (y :: ys') = [y] ++ ys' := rfl
      have hpast : ∀ p ∈ ([y] : List R), p ≤ y := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | h
        · exact le_refl _
        · exact absurd h List.not_mem_nil
      have haux := count_diff_of_not_root_from_aux (ys_full := y :: ys')
        hIVP hdP hys_sort hsg_ys hPc hsplit hi_rest harg_rest hyc_lt hpast
      rw [List.count_cons_of_ne hx0_ne, List.count_cons_of_ne hy_ne]
      exact haux

/-! ### Uniqueness of virtual roots lists

Virtual roots lists are pinned down by the argmin partition: given the same
derivative witness `ys`, each entry of `xs` is the unique minimiser of `|P|`
on its interval because `P` is strictly monotonic there (from the sign
dichotomy for `P'` and `strictMonoOn_of_deriv_pos_*` / `strictAntiOn_of_deriv_neg_*`).
We first prove a general argmin uniqueness on any order-connected set where
`P` is injective, then specialize to each of the interval shapes that appear
in `ArgminPartition`, and finally induct on `P.natDegree`. -/

/-- **General argmin uniqueness.** On an order-connected set `S` on which `P`
    is injective, the argmin of `|P|` is unique. The only non-trivial case is
    `P z₁ = -P z₂` with both nonzero (opposite signs): `OrdConnected` gives
    `Icc z₁ z₂ ⊆ S` and IVP produces a root between them — a strictly smaller
    `|P|`, contradicting the argmin claim. -/
lemma IsArgminAbsOn.unique_of_injOn
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {S : Set R}
    (hord : S.OrdConnected)
    (hinj : S.InjOn (fun x => P.eval x))
    {z₁ z₂ : R}
    (h₁ : IsArgminAbsOn P S z₁) (h₂ : IsArgminAbsOn P S z₂) :
    z₁ = z₂ := by
  obtain ⟨hz₁, hmin₁⟩ := h₁
  obtain ⟨hz₂, hmin₂⟩ := h₂
  have habs : |P.eval z₁| = |P.eval z₂| :=
    le_antisymm (hmin₁ z₂ hz₂) (hmin₂ z₁ hz₁)
  rcases abs_eq_abs.mp habs with heq | hneg
  · exact hinj hz₁ hz₂ heq
  · by_cases hP₁ : P.eval z₁ = 0
    · have hP₂ : P.eval z₂ = 0 := by linarith
      exact hinj hz₁ hz₂ (hP₁.trans hP₂.symm)
    · have hP₂ : P.eval z₂ ≠ 0 := fun h => hP₁ (by rw [hneg, h, neg_zero])
      have hsq_pos : 0 < P.eval z₂ * P.eval z₂ := by
        rcases lt_or_gt_of_ne hP₂ with h | h
        · exact mul_pos_of_neg_of_neg h h
        · exact mul_pos h h
      have hprod_neg : P.eval z₁ * P.eval z₂ < 0 := by
        have : P.eval z₁ * P.eval z₂ = -(P.eval z₂ * P.eval z₂) := by
          rw [hneg]; ring
        linarith
      rcases lt_trichotomy z₁ z₂ with hlt | heq | hgt
      · have hsubset : Set.Icc z₁ z₂ ⊆ S := hord.out hz₁ hz₂
        obtain ⟨r, hz₁r, hrz₂, hPr⟩ := hIVP P z₁ z₂ hlt hprod_neg
        have hr_mem : r ∈ S := hsubset ⟨hz₁r.le, hrz₂.le⟩
        have hle : |P.eval z₁| ≤ |P.eval r| := hmin₁ r hr_mem
        rw [hPr, abs_zero] at hle
        exact absurd (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))) hP₁
      · exact heq
      · have hsubset : Set.Icc z₂ z₁ ⊆ S := hord.out hz₂ hz₁
        have hprod_neg' : P.eval z₂ * P.eval z₁ < 0 := by
          rw [mul_comm]; exact hprod_neg
        obtain ⟨r, hz₂r, hrz₁, hPr⟩ := hIVP P z₂ z₁ hgt hprod_neg'
        have hr_mem : r ∈ S := hsubset ⟨hz₂r.le, hrz₁.le⟩
        have hle : |P.eval z₁| ≤ |P.eval r| := hmin₁ r hr_mem
        rw [hPr, abs_zero] at hle
        exact absurd (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))) hP₁

/-- Argmin uniqueness from strict monotonicity: every strict-mono function is
    injective, so `unique_of_injOn` applies. -/
lemma IsArgminAbsOn.unique_of_strictMonoOn
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {S : Set R}
    (hord : S.OrdConnected)
    (hmono : StrictMonoOn (fun x => P.eval x) S)
    {z₁ z₂ : R}
    (h₁ : IsArgminAbsOn P S z₁) (h₂ : IsArgminAbsOn P S z₂) :
    z₁ = z₂ :=
  IsArgminAbsOn.unique_of_injOn hIVP hord hmono.injOn h₁ h₂

/-- Argmin uniqueness from strict antitonicity. -/
lemma IsArgminAbsOn.unique_of_strictAntiOn
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {S : Set R}
    (hord : S.OrdConnected)
    (hanti : StrictAntiOn (fun x => P.eval x) S)
    {z₁ z₂ : R}
    (h₁ : IsArgminAbsOn P S z₁) (h₂ : IsArgminAbsOn P S z₂) :
    z₁ = z₂ :=
  IsArgminAbsOn.unique_of_injOn hIVP hord hanti.injOn h₁ h₂

/-- Argmin uniqueness on `Iic c` from a derivative sign dichotomy on `Iio c`.
    The dichotomy produces strict mono (if `P' > 0` on `Iio c`) or strict anti
    (if `P' < 0` on `Iio c`) on `Iic c`. -/
lemma IsArgminAbsOn.unique_on_Iic_of_deriv_dichotomy
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {c : R}
    (hdich : (∀ x ∈ Set.Iio c, 0 < (derivative P).eval x) ∨
             (∀ x ∈ Set.Iio c, (derivative P).eval x < 0))
    {z₁ z₂ : R}
    (h₁ : IsArgminAbsOn P (Set.Iic c) z₁)
    (h₂ : IsArgminAbsOn P (Set.Iic c) z₂) :
    z₁ = z₂ := by
  rcases hdich with hpos | hneg
  · exact IsArgminAbsOn.unique_of_strictMonoOn hIVP Set.ordConnected_Iic
      (strictMonoOn_of_deriv_pos_Iic hIVP hpos) h₁ h₂
  · exact IsArgminAbsOn.unique_of_strictAntiOn hIVP Set.ordConnected_Iic
      (strictAntiOn_of_deriv_neg_Iic hIVP hneg) h₁ h₂

/-- Argmin uniqueness on `Ici c` from a derivative sign dichotomy on `Ioi c`. -/
lemma IsArgminAbsOn.unique_on_Ici_of_deriv_dichotomy
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {c : R}
    (hdich : (∀ x ∈ Set.Ioi c, 0 < (derivative P).eval x) ∨
             (∀ x ∈ Set.Ioi c, (derivative P).eval x < 0))
    {z₁ z₂ : R}
    (h₁ : IsArgminAbsOn P (Set.Ici c) z₁)
    (h₂ : IsArgminAbsOn P (Set.Ici c) z₂) :
    z₁ = z₂ := by
  rcases hdich with hpos | hneg
  · exact IsArgminAbsOn.unique_of_strictMonoOn hIVP Set.ordConnected_Ici
      (strictMonoOn_of_deriv_pos_Ici hIVP hpos) h₁ h₂
  · exact IsArgminAbsOn.unique_of_strictAntiOn hIVP Set.ordConnected_Ici
      (strictAntiOn_of_deriv_neg_Ici hIVP hneg) h₁ h₂

/-- Argmin uniqueness on `Icc a b` from a derivative sign dichotomy on `Ioo a b`. -/
lemma IsArgminAbsOn.unique_on_Icc_of_deriv_dichotomy
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} {a b : R} (hab : a < b)
    (hdich : (∀ x ∈ Set.Ioo a b, 0 < (derivative P).eval x) ∨
             (∀ x ∈ Set.Ioo a b, (derivative P).eval x < 0))
    {z₁ z₂ : R}
    (h₁ : IsArgminAbsOn P (Set.Icc a b) z₁)
    (h₂ : IsArgminAbsOn P (Set.Icc a b) z₂) :
    z₁ = z₂ := by
  rcases hdich with hpos | hneg
  · exact IsArgminAbsOn.unique_of_strictMonoOn hIVP Set.ordConnected_Icc
      (corollary_2_24_increasing hIVP P hab hpos) h₁ h₂
  · exact IsArgminAbsOn.unique_of_strictAntiOn hIVP Set.ordConnected_Icc
      (corollary_2_24_decreasing hIVP P hab hneg) h₁ h₂

omit [IsStrictOrderedRing R] in
/-- `SignConstantOnGaps Q []` means `Q` has a single strict sign everywhere. -/
lemma sign_dichotomy_univ_of_nil {Q : R[X]} (h : SignConstantOnGaps Q []) :
    (∀ x : R, 0 < Q.eval x) ∨ (∀ x : R, Q.eval x < 0) := by
  have h0 : Q.eval 0 ≠ 0 := (h 0 0 (le_refl 0) (fun r hr => absurd hr List.not_mem_nil)).1
  have hsign : ∀ x : R, SignType.sign (Q.eval x) = SignType.sign (Q.eval 0) := by
    intro x
    rcases le_or_gt x 0 with hx | hx
    · exact (h x 0 hx (fun r hr => absurd hr List.not_mem_nil)).2
    · exact ((h 0 x hx.le (fun r hr => absurd hr List.not_mem_nil)).2).symm
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · right; intro x
    have := hsign x
    rw [sign_eq_neg_one_iff.mpr hneg] at this
    exact sign_eq_neg_one_iff.mp this
  · left; intro x
    have := hsign x
    rw [sign_eq_one_iff.mpr hpos] at this
    exact sign_eq_one_iff.mp this

/-- Argmin uniqueness on `Set.univ` when `P'` has constant strict sign on all
    of `R` (captured by `SignConstantOnGaps (derivative P) []`). -/
lemma IsArgminAbsOn.unique_on_univ_of_signConstantOnGaps_nil
    (hIVP : HasIntermediateValueProperty R) {P : R[X]}
    (hsg : SignConstantOnGaps (derivative P) [])
    {z₁ z₂ : R}
    (h₁ : IsArgminAbsOn P Set.univ z₁) (h₂ : IsArgminAbsOn P Set.univ z₂) :
    z₁ = z₂ := by
  rcases sign_dichotomy_univ_of_nil hsg with hpos | hneg
  · exact IsArgminAbsOn.unique_of_strictMonoOn hIVP Set.ordConnected_univ
      ((strictMono_of_deriv_pos hIVP hpos).strictMonoOn Set.univ) h₁ h₂
  · exact IsArgminAbsOn.unique_of_strictAntiOn hIVP Set.ordConnected_univ
      ((strictAnti_of_deriv_neg hIVP hneg).strictAntiOn Set.univ) h₁ h₂

/-- **Uniqueness of the inner partition witness.** Given a sorted `ys_full`
    with `SignConstantOnGaps (derivative P) ys_full`, and a split
    `ys_full = past ++ a :: ys_rest`, any two `ArgminPartitionFrom P a _ ys_rest`
    witnesses agree. -/
private theorem ArgminPartitionFrom.unique_aux
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]}
    {ys_full : List R}
    (hys_full_sort : ys_full.Pairwise (· ≤ ·))
    (hsg : SignConstantOnGaps (derivative P) ys_full) :
    ∀ {past : List R} {a : R} {ys_rest : List R},
      ys_full = past ++ a :: ys_rest →
      ∀ {xs xs' : List R},
        ArgminPartitionFrom P a xs ys_rest →
        ArgminPartitionFrom P a xs' ys_rest →
        xs = xs' := by
  intro past a ys_rest hsplit
  induction ys_rest generalizing past a with
  | nil =>
    intro xs xs' harg harg'
    rcases xs with _ | ⟨x, xrest⟩
    · exact absurd harg (by simp [ArgminPartitionFrom])
    rcases xrest with _ | ⟨_, _⟩
    swap
    · exact absurd harg (by simp [ArgminPartitionFrom])
    rcases xs' with _ | ⟨x', xrest'⟩
    · exact absurd harg' (by simp [ArgminPartitionFrom])
    rcases xrest' with _ | ⟨_, _⟩
    swap
    · exact absurd harg' (by simp [ArgminPartitionFrom])
    change IsArgminAbsOn P (Set.Ici a) x at harg
    change IsArgminAbsOn P (Set.Ici a) x' at harg'
    have hr_le : ∀ r ∈ ys_full, r ≤ a := by
      intro r hr
      rw [hsplit] at hr
      rcases List.mem_append.mp hr with hpast | hcons
      · rw [hsplit] at hys_full_sort
        exact (sorted_split_le hys_full_sort).1 r hpast
      · rw [List.mem_cons] at hcons
        rcases hcons with rfl | h0
        · exact le_refl _
        · exact absurd h0 List.not_mem_nil
    have : x = x' := IsArgminAbsOn.unique_on_Ici_of_deriv_dichotomy hIVP
      (sign_dichotomy_Ioi hsg hr_le) harg harg'
    rw [this]
  | cons y ys_rest' ih =>
    intro xs xs' harg harg'
    rcases xs with _ | ⟨x, xrest⟩
    · exact absurd harg (by simp [ArgminPartitionFrom])
    rcases xrest with _ | ⟨x'', xs_rest⟩
    · exact absurd harg (by simp [ArgminPartitionFrom])
    rcases xs' with _ | ⟨x₀, xrest'⟩
    · exact absurd harg' (by simp [ArgminPartitionFrom])
    rcases xrest' with _ | ⟨x₀'', xs_rest'⟩
    · exact absurd harg' (by simp [ArgminPartitionFrom])
    change IsArgminAbsOn P (Set.Icc a y) x ∧
      ArgminPartitionFrom P y (x'' :: xs_rest) ys_rest' at harg
    change IsArgminAbsOn P (Set.Icc a y) x₀ ∧
      ArgminPartitionFrom P y (x₀'' :: xs_rest') ys_rest' at harg'
    obtain ⟨harg_head, harg_rest⟩ := harg
    obtain ⟨harg'_head, harg'_rest⟩ := harg'
    have hsplit_next : ys_full = (past ++ [a]) ++ y :: ys_rest' := by
      rw [hsplit, List.append_assoc]; rfl
    have hay : a ≤ y := by
      have hsorted' := hys_full_sort
      rw [hsplit] at hsorted'
      exact (sorted_split_le hsorted').2.1 y List.mem_cons_self
    have hx_eq : x = x₀ := by
      rcases eq_or_lt_of_le hay with heq | hlt
      · have hx : x = a := by
          have hm : x ∈ Set.Icc a y := harg_head.1
          rw [← heq, Set.Icc_self] at hm; exact hm
        have hx₀ : x₀ = a := by
          have hm : x₀ ∈ Set.Icc a y := harg'_head.1
          rw [← heq, Set.Icc_self] at hm; exact hm
        rw [hx, hx₀]
      · have hgap_out : ∀ r ∈ ys_full, r ≤ a ∨ y ≤ r :=
          gap_closure_adjacent hsplit hys_full_sort
        exact IsArgminAbsOn.unique_on_Icc_of_deriv_dichotomy hIVP hlt
          (sign_dichotomy_Ioo hsg hlt hgap_out) harg_head harg'_head
    subst hx_eq
    have := ih hsplit_next harg_rest harg'_rest
    rw [this]

/-- **Uniqueness of the outer partition witness.** Given a sorted `ys` with
    `SignConstantOnGaps (derivative P) ys`, any two `ArgminPartition P _ ys`
    witnesses agree. -/
theorem ArgminPartition.unique
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]}
    {ys : List R} (hys_sort : ys.Pairwise (· ≤ ·))
    (hsg : SignConstantOnGaps (derivative P) ys)
    {xs xs' : List R}
    (harg : ArgminPartition P xs ys) (harg' : ArgminPartition P xs' ys) :
    xs = xs' := by
  cases ys with
  | nil =>
    rcases xs with _ | ⟨x, xrest⟩
    · exact absurd harg (by simp [ArgminPartition])
    rcases xrest with _ | ⟨_, _⟩
    swap
    · exact absurd harg (by simp [ArgminPartition])
    rcases xs' with _ | ⟨x', xrest'⟩
    · exact absurd harg' (by simp [ArgminPartition])
    rcases xrest' with _ | ⟨_, _⟩
    swap
    · exact absurd harg' (by simp [ArgminPartition])
    change IsArgminAbsOn P Set.univ x at harg
    change IsArgminAbsOn P Set.univ x' at harg'
    have : x = x' :=
      IsArgminAbsOn.unique_on_univ_of_signConstantOnGaps_nil hIVP hsg harg harg'
    rw [this]
  | cons y ys_rest =>
    rcases xs with _ | ⟨x, xrest⟩
    · exact absurd harg (by simp [ArgminPartition])
    rcases xrest with _ | ⟨x'', xs_rest⟩
    · exact absurd harg (by simp [ArgminPartition])
    rcases xs' with _ | ⟨x₀, xrest'⟩
    · exact absurd harg' (by simp [ArgminPartition])
    rcases xrest' with _ | ⟨x₀'', xs_rest'⟩
    · exact absurd harg' (by simp [ArgminPartition])
    change IsArgminAbsOn P (Set.Iic y) x ∧
      ArgminPartitionFrom P y (x'' :: xs_rest) ys_rest at harg
    change IsArgminAbsOn P (Set.Iic y) x₀ ∧
      ArgminPartitionFrom P y (x₀'' :: xs_rest') ys_rest at harg'
    obtain ⟨harg_head, harg_rest⟩ := harg
    obtain ⟨harg'_head, harg'_rest⟩ := harg'
    have hy_le : ∀ r ∈ y :: ys_rest, y ≤ r := by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | h'
      · exact le_refl _
      · exact (List.pairwise_cons.mp hys_sort).1 r h'
    have hx_eq : x = x₀ :=
      IsArgminAbsOn.unique_on_Iic_of_deriv_dichotomy hIVP
        (sign_dichotomy_Iio hsg hy_le) harg_head harg'_head
    subst hx_eq
    have hsplit : (y :: ys_rest) = [] ++ y :: ys_rest := by rfl
    have := ArgminPartitionFrom.unique_aux hIVP hys_sort hsg hsplit
      harg_rest harg'_rest
    rw [this]

/-- **Uniqueness at a given depth.** If `P.natDegree = n`, then any two
    `IsVirtualRootsListAux n P _` witnesses agree. -/
private theorem IsVirtualRootsListAux.unique
    (hIVP : HasIntermediateValueProperty R) :
    ∀ (n : ℕ) {P : R[X]}, P.natDegree = n → ∀ {xs ys : List R},
      IsVirtualRootsListAux n P xs → IsVirtualRootsListAux n P ys → xs = ys := by
  intro n
  induction n with
  | zero =>
    intro P hdeg xs ys hxs hys
    have hxs_len := hxs.length_eq
    have hys_len := hys.length_eq
    rw [hdeg] at hxs_len hys_len
    rw [List.length_eq_zero_iff] at hxs_len hys_len
    rw [hxs_len, hys_len]
  | succ n ih =>
    intro P hdeg xs ys hxs hys
    rcases hxs.argmin_wit_succ with hxnil | ⟨ys_x, hys_x_aux, _, harg_x⟩
    · have hlen := hxs.length_eq
      rw [hxnil, hdeg] at hlen
      simp at hlen
    rcases hys.argmin_wit_succ with hynil | ⟨ys_y, hys_y_aux, _, harg_y⟩
    · have hlen := hys.length_eq
      rw [hynil, hdeg] at hlen
      simp at hlen
    have hdP_deg : (derivative P).natDegree = n := by
      have hdeg_pos : 0 < P.natDegree := by rw [hdeg]; omega
      have h1 : (derivative P).degree = (P.natDegree - 1 : ℕ) :=
        Polynomial.degree_derivative_eq P hdeg_pos
      have h2 : (derivative P).natDegree = P.natDegree - 1 :=
        Polynomial.natDegree_eq_of_degree_eq_some h1
      rw [h2, hdeg]; omega
    have hys_eq : ys_x = ys_y := ih hdP_deg hys_x_aux hys_y_aux
    subst hys_eq
    exact ArgminPartition.unique hIVP hys_x_aux.sorted hys_x_aux.sign_const
      harg_x harg_y

/-- **Uniqueness of virtual roots lists.** Any two virtual roots lists of `P`
    agree. The argmin entries are pinned down by the derivative witness (by
    induction on `natDegree`), and the derivative witness itself is unique by
    the inductive hypothesis. -/
theorem IsVirtualRootsList.unique
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} {xs ys : List R}
    (hxs : IsVirtualRootsList P xs) (hys : IsVirtualRootsList P ys) :
    xs = ys :=
  IsVirtualRootsListAux.unique hIVP P.natDegree rfl hxs hys

end Azurite.BPR.VirtualRoots.Internal
