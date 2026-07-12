/-
  Exhaustive generators for the modular-integer types: `AzZMod m` (general
  modulus) and `AzZModPow2 k` (power-of-two modulus), enumerated as the
  residues in increasing order `0, 1, …, card - 1`, then exhausted.

  Malachite has no modular-integer type in `malachite-base`, so there is no
  doctest to replay; these are the Azurite-native analogues of
  `exhaustive_unsigneds` for the computable coefficient rings — the missing
  ingredient for the chapter's motivating use: streams of polynomials over
  `ZMod p` (coefficient lists via `exhaustive_vecs`, exercised in the
  guards) feeding the factorization algorithms.

  Both types are structures `⟨val : AzNat, isLt : val.toNat < card⟩`, so the
  bounded builder `ofBoundedBijOn` constructs each residue DIRECTLY with its
  canonicity proof — no modular reduction and no reduction lemmas needed:
  injectivity and surjectivity are the `AzNat.toNat/ofNat` round-trips.
  `card` is `m.toNat` (computed from the modulus index) respectively `2 ^ k`,
  carried as `FiniteGenerator` data so the composites (capped fair products,
  fixed-length and all-length vecs) resolve through the finite rail.
-/
import Azurite.ExhaustiveGenerator.ExhaustiveVecs
import Azurite.AzZMod.Basic
import Azurite.AzZModPow2.Basic

namespace Azurite

/-! ### `AzZMod m` -/

/-- The exhaustive generator for `AzZMod m`: residues `0, 1, …, m - 1` in
increasing order, constructed directly with their canonicity proofs. -/
instance azZModGen (m : AzNat) [NeZero m.toNat] : ExhaustiveGenerator (AzZMod m) :=
  ExhaustiveGenerator.ofBoundedBijOn m.toNat
    (fun n h => ⟨AzNat.ofNat n, by rw [AzNat.toNat_ofNat]; exact h⟩)
    (fun i j _ _ hij => by
      have := congrArg (fun a : AzZMod m => a.val.toNat) hij
      simpa [AzNat.toNat_ofNat] using this)
    (fun a => ⟨a.val.toNat, a.isLt, by
      apply AzZMod.ext
      show AzNat.ofNat a.val.toNat = a.val
      exact AzNat.ofNat_toNat a.val⟩)

/-- `AzZMod m` is finite with `card = m.toNat`. -/
instance (m : AzNat) [NeZero m.toNat] : FiniteGenerator (AzZMod m) :=
  .ofBoundedBijOn (azZModGen m) m.toNat rfl

/-! ### `AzZModPow2 k` -/

/-- The exhaustive generator for `AzZModPow2 k`: residues `0, 1, …, 2^k - 1`
in increasing order, constructed directly with their canonicity proofs. -/
instance azZModPow2Gen (k : ℕ) : ExhaustiveGenerator (AzZModPow2 k) :=
  ExhaustiveGenerator.ofBoundedBijOn (2 ^ k)
    (fun n h => ⟨AzNat.ofNat n, by rw [AzNat.toNat_ofNat]; exact h⟩)
    (fun i j _ _ hij => by
      have := congrArg (fun a : AzZModPow2 k => a.val.toNat) hij
      simpa [AzNat.toNat_ofNat] using this)
    (fun a => ⟨a.val.toNat, a.isLt, by
      apply AzZModPow2.ext
      show AzNat.ofNat a.val.toNat = a.val
      exact AzNat.ofNat_toNat a.val⟩)

/-- `AzZModPow2 k` is finite with `card = 2 ^ k`. -/
instance (k : ℕ) : FiniteGenerator (AzZModPow2 k) :=
  .ofBoundedBijOn (azZModPow2Gen k) (2 ^ k) rfl

/-! ### Guards

The base enumerations, the finite caps, and — the point of the exercise —
the composites: a capped fair pair with an infinite partner, and the fair
all-length vec enumeration of `AzZMod (AzNat.ofNat 3)` coefficient lists (the polynomial
coefficient stream shape). `AzZMod (AzNat.ofNat 3)` has the same cardinality as
`Ordering`, so its all-length table is the `ExhaustiveVecs` guard's table
under `.lt ↦ 0, .eq ↦ 1, .gt ↦ 2` — pinning that the fair machinery depends
only on the cards. -/

open ExhaustiveGenerator

-- `AzZMod (AzNat.ofNat 7)`: the seven residues in order, then exhausted.
#guard (firstN (AzZMod (AzNat.ofNat 7)) 10).map (·.val.toNat) = [0, 1, 2, 3, 4, 5, 6]
#guard (firstN (AzZMod (AzNat.ofNat 7)) 10).length == 7
#guard FiniteGenerator.card (T := AzZMod (AzNat.ofNat 7)) == 7

-- `AzZModPow2 3`: the eight residues, then exhausted.
#guard (firstN (AzZModPow2 3) 12).map (·.val.toNat) = [0, 1, 2, 3, 4, 5, 6, 7]
#guard FiniteGenerator.card (T := AzZModPow2 3) == 8

-- Capped fair pair with an infinite partner (`AzZMod (AzNat.ofNat 3) × AzNat`): the
-- compressed fair enumeration, mirroring the `Ordering × AzNat` shape.
#guard (firstN (AzZMod (AzNat.ofNat 3) × AzNat) 12).map (fun p => (p.1.val.toNat, p.2.toNat))
  = [(0, 0), (0, 1), (1, 0), (1, 1), (0, 2), (0, 3), (1, 2), (1, 3),
     (2, 0), (2, 1), (2, 2), (2, 3)]

-- Finite × finite pair (`AzZMod (AzNat.ofNat 3) × AzZModPow2 1`): all six pairs, capped.
#guard (firstN (AzZMod (AzNat.ofNat 3) × AzZModPow2 1) 10).map
    (fun p => (p.1.val.toNat, p.2.val.toNat))
  = [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)]
#guard (firstN (AzZMod (AzNat.ofNat 3) × AzZModPow2 1) 10).length == 6

-- THE COEFFICIENT-STREAM SHAPE: all `AzZMod (AzNat.ofNat 3)` coefficient lists, fairly
-- (the `exhaustive_vecs` instance through the finite rail). Same table as
-- the `List Ordering` guard under the card-3 relabeling.
#guard ((List.range 48).filterMap (gen (T := List (AzZMod (AzNat.ofNat 3))))).map
    (fun l => l.map (·.val.toNat))
  = [[], [0], [0, 0], [1], [0, 0, 0], [2], [0, 1],
     [0, 0, 0, 0], [1, 0], [0, 0, 1], [1, 1],
     [0, 0, 0, 0, 0], [0, 2], [0, 1, 0], [1, 2],
     [0, 0, 0, 1]]

end Azurite
