import Azurite.BasuPollackRoy.Chapter3.Section3_1.EuclideanBall
import Mathlib.Topology.Basic

/-! # BPR §3.1 — the euclidean topology on `R^k`

A set `U ⊆ R^k` is **open** if it is a union of open balls, i.e. if every point of `U` is contained
in an open ball contained in `U`; a set `F ⊆ R^k` is **closed** if its complement is open.

We realize this as a genuine `TopologicalSpace (Fin k → R)` instance, taking the displayed predicate
as the family of open sets. The only non-trivial topology axiom is closure under binary intersection,
which uses the **triangle inequality** for the euclidean norm — itself a consequence of the
Cauchy–Schwarz inequality `(∑ aᵢbᵢ)² ≤ (∑ aᵢ²)(∑ bᵢ²)`, valid over any ordered field.

With this instance, Mathlib's `IsOpen`, `IsClosed`, `closure`, `interior`, `Continuous`, … are BPR's
notions (`isOpen_iff` records that `IsOpen` is exactly BPR's ball definition, by construction).
Consequently the arbitrary union of open sets is open (`isOpen_iUnion`/`isOpen_sUnion`) and the
arbitrary intersection of closed sets is closed (`isClosed_iInter`/`isClosed_sInter`) — for free.

(BPR's *higher* notions — semialgebraic connectedness in §3.2 and the closed-and-bounded sets of
§3.4 — are **not** Mathlib's `IsConnected`/`IsCompact`, since topological connectedness and the
Heine–Borel property fail over a non-Archimedean real closed field; those are defined separately.) -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Inner product and the triangle inequality -/

/-- The euclidean inner product `⟨a, b⟩ = ∑ᵢ aᵢ bᵢ`. -/
def euclideanInner (a b : Fin k → R) : R := ∑ i, a i * b i

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem euclideanNormSq_add (a b : Fin k → R) :
    euclideanNormSq (a + b) = euclideanNormSq a + 2 * euclideanInner a b + euclideanNormSq b := by
  simp only [euclideanNormSq, euclideanInner, Pi.add_apply, add_sq, Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; ring

omit [IsRealClosed R] in
/-- **Cauchy–Schwarz** `⟨a,b⟩² ≤ ‖a‖²‖b‖²`. -/
theorem euclideanInner_sq_le (a b : Fin k → R) :
    euclideanInner a b ^ 2 ≤ euclideanNormSq a * euclideanNormSq b :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b

theorem euclideanInner_le_norm_mul_norm (a b : Fin k → R) :
    euclideanInner a b ≤ euclideanNorm a * euclideanNorm b := by
  refine le_of_sq_le_sq ?_ (mul_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _))
  rw [mul_pow, euclideanNorm_sq, euclideanNorm_sq]; exact euclideanInner_sq_le a b

/-- **Triangle inequality** `‖a + b‖ ≤ ‖a‖ + ‖b‖`. -/
theorem euclideanNorm_add_le (a b : Fin k → R) :
    euclideanNorm (a + b) ≤ euclideanNorm a + euclideanNorm b := by
  refine le_of_sq_le_sq ?_ (add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _))
  rw [euclideanNorm_sq, euclideanNormSq_add, add_sq, euclideanNorm_sq, euclideanNorm_sq]
  nlinarith [euclideanInner_le_norm_mul_norm a b]

/-! ### Open balls via the norm; ball nesting -/

theorem mem_openBall_iff_norm {c : Fin k → R} {r : R} (hr : 0 < r) {y : Fin k → R} :
    y ∈ openBall c r ↔ euclideanNorm (y - c) < r := by
  rw [mem_openBall, ← euclideanNorm_sq]
  exact ⟨fun h => lt_of_pow_lt_pow_left₀ 2 hr.le h,
    fun h => by nlinarith [euclideanNorm_nonneg (y - c)]⟩

/-- If `‖x − c‖ + s ≤ r` then the ball `B(x,s)` is contained in `B(c,r)`. -/
theorem openBall_subset_openBall {c x : Fin k → R} {r s : R} (hr : 0 < r) (hs : 0 < s)
    (h : euclideanNorm (x - c) + s ≤ r) : openBall x s ⊆ openBall c r := by
  intro y hy
  rw [mem_openBall_iff_norm hs] at hy
  rw [mem_openBall_iff_norm hr]
  calc euclideanNorm (y - c) = euclideanNorm ((y - x) + (x - c)) := by ring_nf
    _ ≤ euclideanNorm (y - x) + euclideanNorm (x - c) := euclideanNorm_add_le _ _
    _ < s + euclideanNorm (x - c) := by linarith
    _ ≤ r := by linarith

theorem mem_openBall_self (c : Fin k → R) {r : R} (hr : 0 < r) : c ∈ openBall c r := by
  rw [mem_openBall, sub_self]
  have h0 : euclideanNormSq (0 : Fin k → R) = 0 := by simp [euclideanNormSq]
  rw [h0]; positivity

/-! ### The euclidean topology -/

/-- **The euclidean (ball) topology on `R^k`.** The open sets are exactly the unions of open balls
(BPR's definition of *open*); closure under binary intersection is the only non-trivial axiom and
uses the triangle inequality. -/
instance : TopologicalSpace (Fin k → R) where
  IsOpen U := ∀ x ∈ U, ∃ (c : Fin k → R) (r : R), 0 < r ∧ x ∈ openBall c r ∧ openBall c r ⊆ U
  isOpen_univ := fun x _ => ⟨x, 1, one_pos, mem_openBall_self x one_pos, Set.subset_univ _⟩
  isOpen_inter := by
    intro U V hU hV x hx
    obtain ⟨c1, r1, hr1, hxc1, hsub1⟩ := hU x hx.1
    obtain ⟨c2, r2, hr2, hxc2, hsub2⟩ := hV x hx.2
    rw [mem_openBall_iff_norm hr1] at hxc1
    rw [mem_openBall_iff_norm hr2] at hxc2
    set s := min (r1 - euclideanNorm (x - c1)) (r2 - euclideanNorm (x - c2)) with hs_def
    have hs : 0 < s := lt_min (by linarith) (by linarith)
    have h1 : euclideanNorm (x - c1) + s ≤ r1 := by
      have hm := min_le_left (r1 - euclideanNorm (x - c1)) (r2 - euclideanNorm (x - c2))
      rw [← hs_def] at hm; linarith
    have h2 : euclideanNorm (x - c2) + s ≤ r2 := by
      have hm := min_le_right (r1 - euclideanNorm (x - c1)) (r2 - euclideanNorm (x - c2))
      rw [← hs_def] at hm; linarith
    refine ⟨x, s, hs, mem_openBall_self x hs, Set.subset_inter_iff.mpr ⟨?_, ?_⟩⟩
    · exact (openBall_subset_openBall hr1 hs h1).trans hsub1
    · exact (openBall_subset_openBall hr2 hs h2).trans hsub2
  isOpen_sUnion := by
    intro S hS x hx
    obtain ⟨U, hUS, hxU⟩ := hx
    obtain ⟨c, r, hr, hxc, hsub⟩ := hS U hUS x hxU
    exact ⟨c, r, hr, hxc, hsub.trans (Set.subset_sUnion_of_mem hUS)⟩

/-- **Fidelity to BPR.** A set is open (Mathlib's `IsOpen`, for this topology) exactly when every
point is contained in an open ball contained in it — BPR's definition. Holds definitionally. -/
theorem isOpen_iff {U : Set (Fin k → R)} :
    IsOpen U ↔ ∀ x ∈ U, ∃ (c : Fin k → R) (r : R), 0 < r ∧ x ∈ openBall c r ∧ openBall c r ⊆ U :=
  Iff.rfl

/-- A set is closed exactly when its complement is open — BPR's definition matches Mathlib's
`IsClosed`. -/
theorem isClosed_iff {F : Set (Fin k → R)} : IsClosed F ↔ IsOpen Fᶜ := isOpen_compl_iff.symm

/-- Every open ball is open. -/
theorem isOpen_openBall (c : Fin k → R) {r : R} (hr : 0 < r) : IsOpen (openBall c r) :=
  fun _ hx => ⟨c, r, hr, hx, le_refl _⟩

/-- **The arbitrary union of open sets is open** (inherited from the topology). -/
theorem isOpen_iUnion_of {ι : Type*} {U : ι → Set (Fin k → R)} (h : ∀ i, IsOpen (U i)) :
    IsOpen (⋃ i, U i) := isOpen_iUnion h

/-- **The arbitrary intersection of closed sets is closed** (inherited from the topology). -/
theorem isClosed_iInter_of {ι : Type*} {F : ι → Set (Fin k → R)} (h : ∀ i, IsClosed (F i)) :
    IsClosed (⋂ i, F i) := isClosed_iInter h

end Azurite.BPR
