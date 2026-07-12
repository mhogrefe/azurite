/-
  `bit_distributor_sequence` — the sequence read off one slot of a two-slot
  BitDistributor (Malachite `bit_distributor_sequence`).

  Malachite builds `BitDistributor::new(&[y_output_type, x_output_type])` and
  streams `get_output(1)` (the `x` slot) while incrementing the counter — in
  the abstract-assignment language of `BitInterleave`, term `n` is
  `P.deinterleave 1 n` for the corresponding 2-slot `BitAssignment P`. The
  port is exactly that, generic over the assignment:
  `bitDistributorSequence P n = P.deinterleave 1 n`, with the weighted
  Malachite argument order recovered by
  `bitDistributorSequenceNormal p q = bitDistributorSequence
  (weightedRoundRobin ![q, p] …)` (x normal with weight `p`, y normal with
  weight `q` — the distributor array is `[y, x]`, so the weights vector is
  `![q, p]`) and the tiny configurations by the existing
  `fairPairAssignmentTinyFirst`/`TinySecond`. With both weights `1` the
  sequence is OEIS A059905 (the even-indexed bits of `n`). Malachite's
  "panics if both output types are tiny" is not a runtime possibility here:
  `tinyAssignment` REQUIRES a normal slot (`0 < normalCount`) as a
  hypothesis.

  The headline theorem (Malachite: "Every number occurs infinitely many
  times") is proved once at the `BitAssignment` level and holds for EVERY
  assignment and EVERY slot, provided some OTHER slot exists to absorb the
  variation: `interleave` with slot `j` pinned to `k` and slot `i ≠ j`
  sweeping `ℕ` lands injectively inside the fiber
  `{n | deinterleave j n = k}` (`BitAssignment.infinite_setOf_deinterleave_eq`
  — the same one-proof-serves-all pattern as `deinterleaveTuple_bijective`).
  The two-slot instances and an unbounded-occurrence form follow.

  The growth claims of the Malachite doc (`O(n)` / `O(log n)` /
  `O(n^{p/(p+q)})` by configuration) are the per-assignment component-growth
  facts of the fair-enumeration layer, not properties of this wrapper; the
  doctest guards pin the representative prefixes instead.
-/
import Azurite.ExhaustiveGenerator.BitInterleaveWeighted
import Azurite.ExhaustiveGenerator.BitInterleaveTiny
import Mathlib.Order.Interval.Finset.Basic

namespace Azurite

namespace BitAssignment

/-- **Every slot value recurs infinitely often** (for any assignment, any
slot, as long as another slot exists): the fiber
`{n | deinterleave j n = k}` is infinite, witnessed by `interleave` with slot
`j` pinned to `k` and slot `i` sweeping `ℕ` — injective because
`deinterleave i` recovers the swept value. -/
theorem infinite_setOf_deinterleave_eq {m : ℕ} (A : BitAssignment m) {i j : Fin m}
    (hij : i ≠ j) (k : ℕ) : {n | A.deinterleave j n = k}.Infinite :=
  Set.infinite_of_injective_forall_mem
    (f := fun a : ℕ => A.interleave fun l => if l = i then a else if l = j then k else 0)
    (fun a b hab => by
      have hab' : A.interleave (fun l => if l = i then a else if l = j then k else 0)
          = A.interleave (fun l => if l = i then b else if l = j then k else 0) := hab
      have ha := A.deinterleave_interleave
        (fun l => if l = i then a else if l = j then k else 0) i
      have hb := A.deinterleave_interleave
        (fun l => if l = i then b else if l = j then k else 0) i
      rw [show (if i = i then a else if i = j then k else 0) = a from if_pos rfl] at ha
      rw [show (if i = i then b else if i = j then k else 0) = b from if_pos rfl] at hb
      rw [← ha, ← hb, hab'])
    (fun a => by
      show A.deinterleave j (A.interleave _) = k
      rw [A.deinterleave_interleave]
      show (if j = i then a else if j = j then k else 0) = k
      rw [if_neg (Ne.symm hij), if_pos rfl])

end BitAssignment

namespace ExhaustiveGenerator

/-- **The bit-distributor sequence** (Malachite `bit_distributor_sequence`):
term `n` is slot `1`'s deinterleaved component of the counter `n` — Malachite
streams `get_output(1)` of a two-output distributor. Generic over the 2-slot
assignment; see `bitDistributorSequenceNormal` for Malachite's weighted
argument order and `fairPairAssignmentTinyFirst`/`TinySecond` for the tiny
configurations. -/
def bitDistributorSequence (P : BitAssignment 2) (n : ℕ) : ℕ :=
  P.deinterleave 1 n

/-- The weighted form in Malachite's argument order:
`bit_distributor_sequence(normal(p), normal(q))` — `x` (the streamed slot)
normal with weight `p`, `y` normal with weight `q`; the distributor array is
`[y, x]`, so the weights vector is `![q, p]`. Grows as `O(n^(p/(p+q)))`;
with `p = q = 1` this is OEIS A059905. -/
def bitDistributorSequenceNormal (p q : ℕ) (hp : 0 < p) (hq : 0 < q) : ℕ → ℕ :=
  bitDistributorSequence (weightedRoundRobin ![q, p] (by norm_num) (fun j =>
    match j with
    | 0 => by simpa using hq
    | 1 => by simpa using hp))

/-- **Every number occurs infinitely many times** (Malachite's headline
claim), for EVERY two-slot configuration — normal/normal of any weights,
either tiny arrangement. -/
theorem infinite_setOf_bitDistributorSequence_eq (P : BitAssignment 2) (k : ℕ) :
    {n | bitDistributorSequence P n = k}.Infinite :=
  P.infinite_setOf_deinterleave_eq (i := 0) (j := 1) (by decide) k

/-- Unbounded-occurrence form: past any point the sequence takes the value
`k` again. -/
theorem exists_le_and_bitDistributorSequence_eq (P : BitAssignment 2) (k N : ℕ) :
    ∃ n, N ≤ n ∧ bitDistributorSequence P n = k := by
  obtain ⟨n, hmem, hlt⟩ := (infinite_setOf_bitDistributorSequence_eq P k).exists_gt N
  exact ⟨n, le_of_lt hlt, hmem⟩

end ExhaustiveGenerator

/-! ### Guards

The two 50-value tables are Malachite's `bit_distributor_sequence` doctests
verbatim (`num/iterators/mod.rs`); the `1,1` prefix is OEIS A059905. The tiny
tables pin the two mixed configurations (`x` tiny: slow, `O(log n)`; `y`
tiny: fast, `O(n)`). -/

open ExhaustiveGenerator

-- Doctest 1, verbatim: `bit_distributor_sequence(normal(1), normal(2))`.
#guard (List.range 50).map (bitDistributorSequenceNormal 1 2 (by norm_num) (by norm_num))
  = [0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2,
     3, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 0, 1]

-- Doctest 2, verbatim: `bit_distributor_sequence(normal(2), normal(1))`.
#guard (List.range 50).map (bitDistributorSequenceNormal 2 1 (by norm_num) (by norm_num))
  = [0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 4, 5, 6, 7, 8, 9, 10, 11, 8, 9, 10, 11, 12, 13, 14,
     15, 12, 13, 14, 15, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 4, 5, 6, 7, 8, 9]

-- Weights `1, 1`: OEIS A059905 (the even-indexed bits of `n`).
#guard (List.range 16).map (bitDistributorSequenceNormal 1 1 (by norm_num) (by norm_num))
  = [0, 1, 0, 1, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3]

-- `x` tiny, `y` normal (`[normal(1), tiny()]` distributor): the streamed slot
-- reads the RULER positions `{0, 1, 3, 7, …}` — slow growth.
#guard (List.range 16).map (bitDistributorSequence fairPairAssignmentTinySecond)
  = [0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 4, 5, 6, 7]

-- `x` normal, `y` tiny (`[tiny(), normal(1)]` distributor): the streamed slot
-- reads everything EXCEPT the ruler positions — fast growth.
#guard (List.range 16).map (bitDistributorSequence fairPairAssignmentTinyFirst)
  = [0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1]

-- Recurrence at depth: value `5` recurs past `10^6` in the `2,1` doctest
-- configuration (the theorem made concrete: `deinterleave 0` of the witness
-- sweeps, `deinterleave 1` stays pinned).
#guard (let P := weightedRoundRobin ![1, 2] (by norm_num) (by decide);
  bitDistributorSequence P (P.interleave ![10 ^ 6, 5])) == 5

end Azurite
