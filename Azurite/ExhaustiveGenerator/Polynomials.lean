/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  The exhaustive polynomial generator: every `AzPolynomial R`, of every
  degree, exactly once. ORIGINAL work — Malachite has no polynomials — built
  from the ported combinators.

  `AzPolynomial R` is a coefficient array with the canonicity invariant
  `back? ≠ some 0` (no trailing zeros), so the enumeration must produce
  exactly the coefficient lists whose LAST entry is nonzero — plus the empty
  list (the zero polynomial). Filtering the full vec enumeration for that
  condition would discard a `1/card` fraction at every length (hopeless for
  large coefficient types, and unquantifiable for infinite ones); instead
  the constraint is built into the SHAPE: a length-`(n+1)` vec with nonzero
  last entry is exactly a pair of an arbitrary length-`n` prefix and a
  nonzero element,

    `List.Vector T n × {t : T // t ≠ 0}  ≃  {v : Vector T (n+1) // last ≠ 0}`,

  so the fair PAIR machinery enumerates the constrained fibers directly —
  `nonzeroLastVecGen`, the requested constrained analogue of
  `ExhaustiveGenerator (List.Vector T n)` — with only the last coordinate
  drawn from the nonzero-element generator. The polynomial generator is then
  the fair dependent pair of lengths and these fibers (length `0` being the
  zero polynomial's singleton), flattened onto the canonical-list subtype
  and transported across `List ↔ Array` onto `AzPolynomial R` itself.

  Nonzero-element generators are provided for the modular coefficient rings
  (`{a : AzZMod m // a ≠ 0}`, `{a : AzZModPow2 k // a ≠ 0}` — the residues
  `1, …, card - 1`); `AzInt` already has `nonzeroIntegersGen`. Any `R` with
  an `ExhaustiveGenerator {t : R // t ≠ 0}` (plus the usual finite/infinite
  data) gets `ExhaustiveGenerator (AzPolynomial R)` for free.

  Fibers with EMPTY nonzero part are legal: over the zero ring the only
  polynomial is `0`, and the dependent pair simply leaves holes at every
  positive length — the clean combinator needs no nonemptiness.
-/
import Azurite.ExhaustiveGenerator.ExhaustiveVecs
import Azurite.ExhaustiveGenerator.ZMods
import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.ToString
import Azurite.AzZMod.Instances
import Azurite.AzInt.Instances
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Azurite.AzMvPolynomial.ParsableCoeff.AzZMod
import Azurite.ExhaustiveGenerator.Integers
import Azurite.ExhaustiveGenerator.VecsLengthRange

namespace Azurite

/-! ### Nonzero-element generators for the modular rings -/

/-- The nonzero residues of `AzZMod m`: `1, 2, …, m - 1`. -/
instance nonzeroAzZModGen (m : AzNat) [NeZero m.toNat] :
    ExhaustiveGenerator {a : AzZMod m // a ≠ 0} :=
  ExhaustiveGenerator.ofBoundedBijOn (m.toNat - 1)
    (fun i h => ⟨⟨AzNat.ofNat (i + 1), by rw [AzNat.toNat_ofNat]; omega⟩, fun hz => by
      have hval : AzNat.ofNat (i + 1) = (0 : AzZMod m).val := congrArg AzZMod.val hz
      rw [AzZMod.val_zero] at hval
      have := congrArg AzNat.toNat hval
      rw [AzNat.toNat_ofNat, AzNat.toNat_zero] at this
      omega⟩)
    (fun i j _ _ hij => by
      have h2 : AzNat.ofNat (i + 1) = AzNat.ofNat (j + 1) :=
        congrArg (fun a : {a : AzZMod m // a ≠ 0} => a.val.val) hij
      have := congrArg AzNat.toNat h2
      rw [AzNat.toNat_ofNat, AzNat.toNat_ofNat] at this
      omega)
    (fun a => by
      have hne : a.val.val.toNat ≠ 0 := by
        intro h0
        refine a.property (AzZMod.ext ?_)
        rw [AzZMod.val_zero]
        rw [← AzNat.ofNat_toNat a.val.val, h0]
        exact AzNat.toNat_injective (by rw [AzNat.toNat_ofNat, AzNat.toNat_zero])
      refine ⟨a.val.val.toNat - 1, by have := a.val.isLt; omega, ?_⟩
      apply Subtype.ext
      apply AzZMod.ext
      show AzNat.ofNat (a.val.val.toNat - 1 + 1) = a.val.val
      rw [show a.val.val.toNat - 1 + 1 = a.val.val.toNat from by omega]
      exact AzNat.ofNat_toNat a.val.val)

/-- `{a : AzZMod m // a ≠ 0}` is finite with `card = m.toNat - 1`. -/
instance (m : AzNat) [NeZero m.toNat] : FiniteGenerator {a : AzZMod m // a ≠ 0} :=
  .ofBoundedBijOn (nonzeroAzZModGen m) (m.toNat - 1) rfl

/-- The nonzero residues of `AzZModPow2 k`: `1, 2, …, 2^k - 1`. -/
instance nonzeroAzZModPow2Gen (k : ℕ) :
    ExhaustiveGenerator {a : AzZModPow2 k // a ≠ 0} :=
  ExhaustiveGenerator.ofBoundedBijOn (2 ^ k - 1)
    (fun i h => ⟨⟨AzNat.ofNat (i + 1), by rw [AzNat.toNat_ofNat]; omega⟩, fun hz => by
      have hval : AzNat.ofNat (i + 1) = (0 : AzZModPow2 k).val := congrArg AzZModPow2.val hz
      rw [AzZModPow2.val_zero] at hval
      have := congrArg AzNat.toNat hval
      rw [AzNat.toNat_ofNat, AzNat.toNat_zero] at this
      omega⟩)
    (fun i j _ _ hij => by
      have h2 : AzNat.ofNat (i + 1) = AzNat.ofNat (j + 1) :=
        congrArg (fun a : {a : AzZModPow2 k // a ≠ 0} => a.val.val) hij
      have := congrArg AzNat.toNat h2
      rw [AzNat.toNat_ofNat, AzNat.toNat_ofNat] at this
      omega)
    (fun a => by
      have hne : a.val.val.toNat ≠ 0 := by
        intro h0
        refine a.property (AzZModPow2.ext ?_)
        rw [AzZModPow2.val_zero]
        rw [← AzNat.ofNat_toNat a.val.val, h0]
        exact AzNat.toNat_injective (by rw [AzNat.toNat_ofNat, AzNat.toNat_zero])
      refine ⟨a.val.val.toNat - 1, by have := a.val.isLt; omega, ?_⟩
      apply Subtype.ext
      apply AzZModPow2.ext
      show AzNat.ofNat (a.val.val.toNat - 1 + 1) = a.val.val
      rw [show a.val.val.toNat - 1 + 1 = a.val.val.toNat from by omega]
      exact AzNat.ofNat_toNat a.val.val)

/-- `{a : AzZModPow2 k // a ≠ 0}` is finite with `card = 2^k - 1`. -/
instance (k : ℕ) : FiniteGenerator {a : AzZModPow2 k // a ≠ 0} :=
  .ofBoundedBijOn (nonzeroAzZModPow2Gen k) (2 ^ k - 1) rfl

namespace ExhaustiveGenerator

/-! ### Vecs with nonzero last entry -/

/-- Append a nonzero last entry: the structural bijection behind the
constrained fibers. -/
@[reducible] def snocNZ {T : Type*} [Zero T] {n : ℕ} :
    List.Vector T n × {t : T // t ≠ 0}
      → {v : List.Vector T (n + 1) // v.toList.getLast? ≠ some 0} :=
  fun p => ⟨⟨p.1.toList ++ [p.2.val], by simp⟩, fun h => by
    have h' : (p.1.toList ++ [p.2.val]).getLast? = some 0 := h
    rw [List.getLast?_concat] at h'
    exact p.2.property (Option.some.inj h')⟩

theorem snocNZ_bijective {T : Type*} [Zero T] {n : ℕ} :
    Function.Bijective (snocNZ (T := T) (n := n)) := by
  constructor
  · rintro ⟨v, t, ht⟩ ⟨w, u, hu⟩ h
    have hl : v.toList ++ [t] = w.toList ++ [u] :=
      congrArg (fun x : {v : List.Vector T (n + 1) //
        v.toList.getLast? ≠ some 0} => x.val.toList) h
    obtain ⟨hvw, htu⟩ := List.append_inj hl
      (by rw [v.toList_length, w.toList_length])
    have h1 : v = w := List.Vector.eq v w hvw
    have h2 : t = u := by
      have := congrArg (fun l : List T => l.getLast?) htu
      simpa using this
    subst h1 h2
    rfl
  · rintro ⟨⟨l, hlen⟩, hlast⟩
    rcases List.eq_nil_or_concat l with rfl | ⟨l', x, rfl⟩
    · simp at hlen
    · have hlen' : l'.length = n := by
        have h2 : (l'.concat x).length = n + 1 := hlen
        rw [List.concat_eq_append, List.length_append] at h2
        simpa using h2
      have hlast' : (l'.concat x).getLast? ≠ some 0 := hlast
      rw [List.concat_eq_append, List.getLast?_concat] at hlast'
      have hx : x ≠ 0 := fun h0 => hlast' (by rw [h0])
      refine ⟨(⟨l', hlen'⟩, ⟨x, hx⟩), ?_⟩
      apply Subtype.ext
      apply List.Vector.eq
      show l' ++ [x] = List.Vector.toList ⟨l'.concat x, hlen⟩
      have hred : List.Vector.toList (⟨l'.concat x, hlen⟩ : List.Vector T (n + 1))
          = l'.concat x := rfl
      rw [hred, List.concat_eq_append]

/-- **Fixed-length vecs with nonzero last entry**: the constrained analogue
of `ExhaustiveGenerator (List.Vector T n)` — only the LAST coordinate is
drawn from the nonzero elements, everything else is the unconstrained fair
enumeration. No filtering: the pair structure IS the constraint. -/
instance nonzeroLastVecGen {T : Type*} [Zero T] {n : ℕ}
    [instP : ExhaustiveGenerator (List.Vector T n × {t : T // t ≠ 0})] :
    ExhaustiveGenerator {v : List.Vector T (n + 1) // v.toList.getLast? ≠ some 0} :=
  mapGen snocNZ snocNZ_bijective instP

/-! ### The polynomial generator -/

/-- The canonical coefficient fiber at each length: length `0` is the zero
polynomial's singleton, length `n + 1` the nonzero-last vecs. -/
def polyCoeffFiber (T : Type*) [Zero T] : ℕ → Type _
  | 0 => List.Vector T 0
  | n + 1 => {v : List.Vector T (n + 1) // v.toList.getLast? ≠ some 0}

/-- The degree-`0` fiber pair, directly from the nonzero elements (the
length-`0` vec component is a singleton). This is what lets the fiber
family resolve for an ABSTRACT length: instance search cannot case-split
`n`, so the `n = 0` pair — whose vec side is finite even over an infinite
`T` — is built by hand, and the `∀`-gate only quantifies over the uniform
`n + 1` shapes. -/
@[reducible] def pairZeroGen {T : Type*} [Zero T]
    [instNZ : ExhaustiveGenerator {t : T // t ≠ 0}] :
    ExhaustiveGenerator (List.Vector T 0 × {t : T // t ≠ 0}) :=
  mapGen (fun t => (List.Vector.nil, t))
    ⟨fun a b h => congrArg Prod.snd h,
     fun p => ⟨p.2, by
      have hnil : p.1 = List.Vector.nil := List.Vector.eq p.1 List.Vector.nil
        (by rw [List.eq_nil_of_length_eq_zero p.1.toList_length]; rfl)
      show (List.Vector.nil, p.2) = p
      rw [← hnil]⟩⟩
    instNZ

/-- The per-length canonical-fiber generators. -/
@[reducible] def polyCoeffFiberGen (T : Type*) [Zero T]
    [ExhaustiveGenerator {t : T // t ≠ 0}]
    [∀ n : ℕ, ExhaustiveGenerator (List.Vector T (n + 1) × {t : T // t ≠ 0})] :
    (n : ℕ) → ExhaustiveGenerator (polyCoeffFiber T n)
  | 0 => fairVecGenZero T
  | 1 => nonzeroLastVecGen (instP := pairZeroGen)
  | _ + 2 => nonzeroLastVecGen

/-- Flatten a length-tagged canonical fiber to the canonical-list subtype
(the empty list — the zero polynomial — satisfies the invariant trivially:
`getLast? [] = none`). -/
@[reducible] def flattenPoly {T : Type*} [Zero T] :
    ((n : ℕ) × polyCoeffFiber T n) → {l : List T // l.getLast? ≠ some 0}
  | ⟨0, v⟩ => ⟨v.toList, by
      rw [List.eq_nil_of_length_eq_zero v.toList_length]
      simp⟩
  | ⟨_ + 1, v⟩ => ⟨v.val.toList, v.property⟩

/-- The flattened list's length is the fiber index. -/
theorem flattenPoly_length {T : Type*} [Zero T] :
    ∀ p : (n : ℕ) × polyCoeffFiber T n, (flattenPoly p).val.length = p.1
  | ⟨0, v⟩ => v.toList_length
  | ⟨_ + 1, v⟩ => v.val.toList_length

theorem flattenPoly_bijective {T : Type*} [Zero T] :
    Function.Bijective (flattenPoly (T := T)) := by
  constructor
  · rintro ⟨n, v⟩ ⟨m, w⟩ h
    have hl : (flattenPoly ⟨n, v⟩).val = (flattenPoly ⟨m, w⟩).val := congrArg Subtype.val h
    -- lengths agree, so the indices agree
    have hnm : n = m := by
      have h1 : (flattenPoly ⟨n, v⟩).val.length = n := flattenPoly_length ⟨n, v⟩
      have h2 : (flattenPoly ⟨m, w⟩).val.length = m := flattenPoly_length ⟨m, w⟩
      rw [← h1, ← h2, hl]
    subst hnm
    cases n with
    | zero =>
      have hv : v = List.Vector.nil := List.Vector.eq v List.Vector.nil
        (by rw [List.eq_nil_of_length_eq_zero v.toList_length]; rfl)
      have hw : w = List.Vector.nil := List.Vector.eq w List.Vector.nil
        (by rw [List.eq_nil_of_length_eq_zero w.toList_length]; rfl)
      rw [hv, hw]
    | succ n =>
      have hl' : v.val.toList = w.val.toList := hl
      have hvw : v = w := Subtype.ext (List.Vector.eq v.val w.val hl')
      rw [hvw]
  · rintro ⟨l, hl⟩
    cases hlen : l.length with
    | zero =>
      refine ⟨⟨0, List.Vector.nil⟩, ?_⟩
      apply Subtype.ext
      show ([] : List T) = l
      exact (List.eq_nil_of_length_eq_zero hlen).symm
    | succ n =>
      exact ⟨⟨n + 1, ⟨⟨l, hlen⟩, hl⟩⟩, rfl⟩

/-- All canonical coefficient lists, fairly: the fair dependent pair of
lengths and the constrained fibers. -/
@[reducible] def canonicalCoeffListsGen (T : Type*) [Zero T]
    [ExhaustiveGenerator {t : T // t ≠ 0}]
    [∀ n : ℕ, ExhaustiveGenerator (List.Vector T (n + 1) × {t : T // t ≠ 0})] :
    ExhaustiveGenerator {l : List T // l.getLast? ≠ some 0} :=
  mapGen flattenPoly flattenPoly_bijective
    (exhaustiveDepPairGen rulerSequence exists_le_and_rulerSequence_eq
      lengthsGen (polyCoeffFiberGen T))

/-- Canonical coefficient lists ARE the polynomials (across
`List ↔ Array`). -/
@[reducible] def listToPoly {R : Type*} [Semiring R] :
    {l : List R // l.getLast? ≠ some 0} → AzPolynomial R :=
  fun l => ⟨l.val.toArray, fun h => l.property ((Array.getLast?_toList _).trans h)⟩

theorem listToPoly_bijective {R : Type*} [Semiring R] :
    Function.Bijective (listToPoly (R := R)) := by
  constructor
  · rintro ⟨l, hl⟩ ⟨l', hl'⟩ h
    have h2 : l.toArray.toList = l'.toArray.toList :=
      congrArg (fun p : AzPolynomial R => p.coeffs.toList) h
    exact Subtype.ext (show l = l' from h2)
  · intro p
    refine ⟨⟨p.coeffs.toList, by rw [Array.getLast?_toList]; exact p.last_ne_zero⟩, ?_⟩
    apply AzPolynomial.ext
    show p.coeffs.toList.toArray = p.coeffs
    exact Array.toArray_toList

end ExhaustiveGenerator

open ExhaustiveGenerator

/-- **The exhaustive polynomial generator**: every `AzPolynomial R` — every
degree, the zero polynomial included — exactly once, fairly. Available for
any coefficient ring with generators for its elements AND its nonzero
elements (finite or infinite rails alike). -/
instance azPolynomialGen {R : Type*} [Semiring R]
    [ExhaustiveGenerator {t : R // t ≠ 0}]
    [∀ n : ℕ, ExhaustiveGenerator (List.Vector R (n + 1) × {t : R // t ≠ 0})] :
    ExhaustiveGenerator (AzPolynomial R) :=
  mapGen listToPoly listToPoly_bijective (canonicalCoeffListsGen R)

/-! ### Bounded degree -/

/-- The degree bound in size form: `deg p < b` is exactly `size ≤ b` (the
zero polynomial has degree `⊥ < b`; a nonzero one has degree
`size - 1`). -/
theorem degree_lt_iff_size_le {R : Type*} [Semiring R] (p : AzPolynomial R) (b : ℕ) :
    p.degree < (b : WithBot ℕ) ↔ p.coeffs.size ≤ b := by
  unfold AzPolynomial.degree
  split_ifs with h
  · simp [h]
  · rw [show ((p.natDegree : ℕ) : WithBot ℕ) < (b : WithBot ℕ)
        ↔ p.natDegree < b from WithBot.coe_lt_coe]
    unfold AzPolynomial.natDegree
    have hpos : 0 < p.coeffs.size := by
      rcases Nat.eq_zero_or_pos p.coeffs.size with h0 | h0
      · exact absurd (Array.eq_empty_of_size_eq_zero h0) h
      · exact h0
    omega

namespace ExhaustiveGenerator

/-- Flatten a range-tagged canonical fiber directly onto the bounded-degree
polynomial subtype — the composite of `flattenPoly` and `listToPoly`,
re-packaged with the size bound. -/
@[reducible] def flattenPolyDegLt {R : Type*} [Semiring R] {b : ℕ} :
    ((n : {n : ℕ // 0 ≤ n ∧ n < b + 1}) × polyCoeffFiber R n.val)
      → {p : AzPolynomial R // p.degree < (b : WithBot ℕ)} :=
  fun q => ⟨listToPoly (flattenPoly ⟨q.1.val, q.2⟩), by
    rw [degree_lt_iff_size_le]
    show (flattenPoly ⟨q.1.val, q.2⟩).val.toArray.size ≤ b
    rw [List.size_toArray, flattenPoly_length]
    show q.1.val ≤ b
    have h := q.1.property
    omega⟩

theorem flattenPolyDegLt_bijective {R : Type*} [Semiring R] {b : ℕ} :
    Function.Bijective (flattenPolyDegLt (R := R) (b := b)) := by
  constructor
  · rintro ⟨⟨n, hn⟩, v⟩ ⟨⟨m, hm⟩, w⟩ h
    have h1 : listToPoly (flattenPoly ⟨n, v⟩) = listToPoly (flattenPoly ⟨m, w⟩) :=
      congrArg Subtype.val h
    have h2 : flattenPoly (T := R) ⟨n, v⟩ = flattenPoly ⟨m, w⟩ :=
      listToPoly_bijective.injective h1
    have h3 : (⟨n, v⟩ : (k : ℕ) × polyCoeffFiber R k) = ⟨m, w⟩ :=
      flattenPoly_bijective.injective h2
    obtain ⟨hnm, hvw⟩ := Sigma.mk.injEq .. ▸ h3
    subst hnm
    have hvw' : v = w := eq_of_heq hvw
    subst hvw'
    rfl
  · rintro ⟨p, hp⟩
    obtain ⟨⟨l, hl⟩, hlp⟩ := listToPoly_bijective.surjective p
    obtain ⟨⟨n, v⟩, hnv⟩ := flattenPoly_bijective.surjective ⟨l, hl⟩
    have hlen : n ≤ b := by
      have hsize : p.coeffs.size ≤ b := (degree_lt_iff_size_le p b).mp hp
      have h1 : (flattenPoly ⟨n, v⟩).val.length = n := flattenPoly_length ⟨n, v⟩
      rw [hnv] at h1
      have h2 : l.toArray.size = p.coeffs.size := by
        rw [show l.toArray = p.coeffs from congrArg AzPolynomial.coeffs hlp]
      rw [List.size_toArray] at h2
      have : l.length = n := h1
      omega
    refine ⟨⟨⟨n, Nat.zero_le n, by omega⟩, v⟩, ?_⟩
    apply Subtype.ext
    show listToPoly (flattenPoly ⟨n, v⟩) = p
    rw [hnv, hlp]

end ExhaustiveGenerator

open ExhaustiveGenerator in
/-- **Bounded-degree polynomials**: every `AzPolynomial R` with
`degree < b`, exactly once, fairly — the polynomial fiber family over the
length range `[0, b + 1)` (Malachite-style half-open convention: `deg ≤ d`
is `b := d + 1`). FINITE for finite coefficient rings (it exhausts), and
the shape the factorization steps draw their bounded-degree candidates
from. -/
@[reducible] def azPolynomialDegreeLtGen {R : Type*} [Semiring R] (b : ℕ)
    [ExhaustiveGenerator {t : R // t ≠ 0}]
    [∀ n : ℕ, ExhaustiveGenerator (List.Vector R (n + 1) × {t : R // t ≠ 0})] :
    ExhaustiveGenerator {p : AzPolynomial R // p.degree < (b : WithBot ℕ)} :=
  mapGen flattenPolyDegLt flattenPolyDegLt_bijective
    (exhaustiveDepPairGen rulerSequence exists_le_and_rulerSequence_eq
      (natRangeGen 0 (b + 1)) (fun n => polyCoeffFiberGen R n.val))

/-! ### Guards

Base nonzero enumerations, the constrained fibers, and the polynomial
streams themselves — over a finite field-like ring (`AzZMod 3`, the
factorization coefficient shape) and an infinite ring (`AzInt`), both
resolved purely by instance search. Displayed as coefficient lists
(constant first): `[] = 0`, `[0, 1] = x`, `[1, 2] = 2x + 1`, … -/

open ExhaustiveGenerator

-- The nonzero residues of `AzZMod 5`, then exhausted.
#guard (firstN {a : AzZMod (AzNat.ofNat 5) // a ≠ 0} 8).map (·.val.val.toNat)
  = [1, 2, 3, 4]

-- Nonzero-last vecs (`AzZMod 3`, length 2): 3·2 of the 9 raw vecs — built
-- structurally, not filtered.
#guard (firstN {v : List.Vector (AzZMod (AzNat.ofNat 3)) 2 //
      v.toList.getLast? ≠ some 0} 10).map (fun v => v.val.toList.map (·.val.toNat))
  = [[0, 1], [0, 2], [1, 1], [1, 2], [2, 1], [2, 2]]

-- THE POLYNOMIAL STREAM, `AzZMod 3` coefficients: `0, 1, x, 2, x², 2x, x³,
-- x+1, 2x², …` — every canonical coefficient list, fairly, exactly once.
#guard ((List.range 60).filterMap (gen (T := AzPolynomial (AzZMod (AzNat.ofNat 3))))).map
    (fun p => p.coeffs.toList.map (·.val.toNat))
  = [[], [1], [0, 1], [2], [0, 0, 1], [0, 2], [0, 0, 0, 1], [1, 1], [0, 0, 2], [1, 2],
     [0, 0, 0, 0, 1], [2, 1], [0, 1, 1], [2, 2], [0, 0, 0, 2], [0, 1, 2]]

-- Over the INFINITE ring `AzInt`: degrees and coefficients both grow
-- fairly (`0, 1, x, -1, x², 2, -x, -2, x³, 3, x+1, -3, …`).
#guard ((List.range 60).filterMap (gen (T := AzPolynomial AzInt))).map
    (fun p => p.coeffs.toList.map (·.toInt))
  = [[], [1], [0, 1], [-1], [0, 0, 1], [2], [0, -1], [-2], [0, 0, 0, 1], [3], [1, 1],
     [-3], [0, 0, -1], [4], [1, -1], [-4], [0, 0, 0, 0, 1], [5], [0, 2], [-5],
     [0, 1, 1], [6], [0, -2], [-6], [0, 0, 0, -1], [7], [1, 2], [-7], [0, 1, -1],
     [8], [1, -2]]

-- Occurs-exactly-once, concrete: long prefixes have no duplicates.
#guard ((List.range 200).filterMap
    (gen (T := AzPolynomial (AzZMod (AzNat.ofNat 3))))).Nodup
#guard ((List.range 200).filterMap (gen (T := AzPolynomial AzInt))).Nodup

/-! ### The streams, in print (guard-string style: `toString`-out is the spec)

The first 100 polynomials of each ring through the real `AzPolynomial`
printer. Degree grows logarithmically in the position (`x^9` first appears
at position 90 of the `AzZMod 3` stream), and over `AzInt` the constants,
coefficient sizes, and degrees all interleave fairly. -/

/-- `Fact`-transport onto `AzNat` literal moduli (companion of
`instNeZeroToNatOfNat`), so literal-modulus guards can use the
`ParsableCoeff`/`ToString` machinery. -/
instance instFactOneLtToNatOfNat (n : ℕ) [Fact (1 < n)] :
    Fact (1 < (AzNat.ofNat n).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; exact Fact.out⟩

#guard (((List.range 3000).filterMap
      (gen (T := AzPolynomial (AzZMod (AzNat.ofNat 3))))).take 100).map toString
  = ["0", "1", "x", "2", "x^2", "2*x", "x^3", "x+1", "2*x^2", "2*x+1",
     "x^4", "x+2", "x^2+x", "2*x+2", "2*x^3", "2*x^2+x", "x^5", "x^2+1", "x^3+x^2", "2*x^2+1",
     "2*x^4", "x^2+x+1", "2*x^3+x^2", "2*x^2+x+1", "x^6", "x^2+2*x", "x^3+x", "2*x^2+2*x",
     "x^4+x^3", "x^2+2*x+1",
     "2*x^3+x", "2*x^2+2*x+1", "2*x^5", "x^2+2", "x^3+x^2+x", "2*x^2+2", "2*x^4+x^3",
     "x^2+x+2", "2*x^3+x^2+x", "2*x^2+x+2",
     "x^7", "x^2+2*x+2", "x^3+1", "2*x^2+2*x+2", "x^4+x^2", "2*x^3+1", "x^5+x^4",
     "x^3+x^2+1", "2*x^4+x^2", "2*x^3+x^2+1",
     "2*x^6", "x^3+x+1", "x^4+x^3+x^2", "2*x^3+x+1", "2*x^5+x^4", "x^3+x^2+x+1",
     "2*x^4+x^3+x^2", "2*x^3+x^2+x+1", "x^8", "x^3+2*x^2",
     "x^4+x", "2*x^3+2*x^2", "x^5+x^3", "x^3+2*x^2+x", "2*x^4+x", "2*x^3+2*x^2+x",
     "x^6+x^5", "x^3+2*x^2+1", "x^4+x^3+x", "2*x^3+2*x^2+1",
     "2*x^5+x^3", "x^3+2*x^2+x+1", "2*x^4+x^3+x", "2*x^3+2*x^2+x+1", "2*x^7", "x^3+2*x",
     "x^4+x^2+x", "2*x^3+2*x", "x^5+x^4+x^3", "x^3+x^2+2*x",
     "2*x^4+x^2+x", "2*x^3+x^2+2*x", "2*x^6+x^5", "x^3+2*x+1", "x^4+x^3+x^2+x",
     "2*x^3+2*x+1", "2*x^5+x^4+x^3", "x^3+x^2+2*x+1", "2*x^4+x^3+x^2+x", "2*x^3+x^2+2*x+1",
     "x^9", "x^3+2*x^2+2*x", "x^4+1", "2*x^3+2*x^2+2*x", "x^5+x^2", "x^3+2*x^2+2*x+1",
     "2*x^4+1", "2*x^3+2*x^2+2*x+1", "x^6+x^4", "x^3+2"]

#guard (((List.range 1000).filterMap (gen (T := AzPolynomial AzInt))).take 100).map toString
  = ["0", "1", "x", "-1", "x^2", "2", "-x", "-2", "x^3", "3",
     "x+1", "-3", "-x^2", "4", "-x+1", "-4", "x^4", "5", "2*x", "-5",
     "x^2+x", "6", "-2*x", "-6", "-x^3", "7", "2*x+1", "-7", "-x^2+x", "8",
     "-2*x+1", "-8", "x^5", "9", "x-1", "-9", "2*x^2", "10", "-x-1", "-10",
     "x^3+x^2", "11", "x+2", "-11", "-2*x^2", "12", "-x+2", "-12", "-x^4", "13",
     "2*x-1", "-13", "2*x^2+x", "14", "-2*x-1", "-14", "-x^3+x^2", "15", "2*x+2", "-15",
     "-2*x^2+x", "16", "-2*x+2", "-16", "x^6", "17", "3*x", "-17", "x^2+1", "18",
     "-3*x", "-18", "2*x^3", "19", "3*x+1", "-19", "-x^2+1", "20", "-3*x+1", "-20",
     "x^4+x^3", "21", "4*x", "-21", "x^2+x+1", "22", "-4*x", "-22", "-2*x^3", "23",
     "4*x+1", "-23", "-x^2+x+1", "24", "-4*x+1", "-24", "-x^5", "25", "3*x-1", "-25"]

/-! ### Bounded-degree guards

`degree < 3` over `AzZMod 3` is the COMPLETE space of quadratics-and-below
— exactly `1 + 2 + 6 + 18 = 27` polynomials, then exhausted. Over `AzInt`
the bounded stream interleaves constants and linears forever. -/

#guard (((List.range 500).filterMap
      ((azPolynomialDegreeLtGen (R := AzZMod (AzNat.ofNat 3)) 3).gen)).map
      (fun p => toString p.val))
  = ["0", "1", "x", "2", "x^2", "2*x", "x+1", "2*x^2", "2*x+1", "x+2", "x^2+x",
     "2*x+2", "2*x^2+x", "x^2+1", "2*x^2+1", "x^2+x+1", "2*x^2+x+1", "x^2+2*x",
     "2*x^2+2*x", "x^2+2*x+1", "2*x^2+2*x+1", "x^2+2", "2*x^2+2", "x^2+x+2",
     "2*x^2+x+2", "x^2+2*x+2", "2*x^2+2*x+2"]
#guard ((List.range 500).filterMap
    ((azPolynomialDegreeLtGen (R := AzZMod (AzNat.ofNat 3)) 3).gen)).length == 27

#guard ((((List.range 200).filterMap
      ((azPolynomialDegreeLtGen (R := AzInt) 2).gen)).take 24).map
      (fun p => toString p.val))
  = ["0", "1", "x", "-1", "2", "-x", "-2", "3", "x+1", "-3", "4", "-x+1", "-4",
     "5", "2*x", "-5", "6", "-2*x", "-6", "7", "2*x+1", "-7", "8", "-2*x+1"]

end Azurite
