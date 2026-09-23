import Azurite.AzPolynomial.SRemS
import Azurite.AzPolynomial.Mul

/-!
# BPR Algorithm 8.20: Extended Signed Remainder Sequence

Alongside the signed remainder sequence `sRemS P Q` (Algorithm 8.19), the
*extended* signed remainder sequence tracks the Bézout cofactors `sRemU`, `sRemV`
with `sRemU_n · P + sRemV_n · Q = sRemS_n` (BPR Lemma 1.11). They mirror the
abstract `Azurite.BPR.SRemU` / `Azurite.BPR.SRemV` (BPR Definition 1.10) on
`Polynomial K`:

* `sRemU P Q 0 = 1`, `sRemU P Q 1 = 0`;
* `sRemV P Q 0 = 0`, `sRemV P Q 1 = 1`;
* `sRemU P Q (n+2) = −sRemU_n + A · sRemU_{n+1}` and likewise for `sRemV`, where
  `A = Quo(sRemS_n, sRemS_{n+1})` is the quotient of the division step producing
  `sRemS_{n+2}` (and `0` once `sRemS_{n+1} = 0`).

`extendedSRemS P Q n` packages the algorithm's output as the triple of the three
lists `(SRemS, SRemU, SRemV)` truncated to `n` terms; the sequences stabilize at
`0` once the remainders terminate, so any `n` past the termination index captures
the full extended sequence.
-/

namespace Azurite.AzPolynomial

variable {K : Type _} [Field K] [DecidableEq K]

/-- The `U`-cofactor of the extended signed remainder sequence (BPR Definition
    1.10), mirroring `Azurite.BPR.SRemU` after `toPoly`. -/
def sRemU (P Q : AzPolynomial K) : ℕ → AzPolynomial K
  | 0 => 1
  | 1 => 0
  | n + 2 =>
      if sRemS P Q (n + 1) = 0 then 0
      else -(sRemU P Q n) + quo (sRemS P Q n) (sRemS P Q (n + 1)) * sRemU P Q (n + 1)

/-- The `V`-cofactor of the extended signed remainder sequence (BPR Definition
    1.10), mirroring `Azurite.BPR.SRemV` after `toPoly`. -/
def sRemV (P Q : AzPolynomial K) : ℕ → AzPolynomial K
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      if sRemS P Q (n + 1) = 0 then 0
      else -(sRemV P Q n) + quo (sRemS P Q n) (sRemS P Q (n + 1)) * sRemV P Q (n + 1)

@[simp] theorem sRemU_zero (P Q : AzPolynomial K) : sRemU P Q 0 = 1 := rfl
@[simp] theorem sRemU_one (P Q : AzPolynomial K) : sRemU P Q 1 = 0 := rfl
@[simp] theorem sRemV_zero (P Q : AzPolynomial K) : sRemV P Q 0 = 0 := rfl
@[simp] theorem sRemV_one (P Q : AzPolynomial K) : sRemV P Q 1 = 1 := rfl

theorem sRemU_succ_succ (P Q : AzPolynomial K) (n : ℕ) :
    sRemU P Q (n + 2) =
      (if sRemS P Q (n + 1) = 0 then 0
       else -(sRemU P Q n) + quo (sRemS P Q n) (sRemS P Q (n + 1)) * sRemU P Q (n + 1)) :=
  rfl

theorem sRemV_succ_succ (P Q : AzPolynomial K) (n : ℕ) :
    sRemV P Q (n + 2) =
      (if sRemS P Q (n + 1) = 0 then 0
       else -(sRemV P Q n) + quo (sRemS P Q n) (sRemS P Q (n + 1)) * sRemV P Q (n + 1)) :=
  rfl

/-- The first `n` terms of `sRemU P Q` packaged as a list. -/
def sRemUList (P Q : AzPolynomial K) (n : ℕ) : List (AzPolynomial K) :=
  (List.range n).map (sRemU P Q)

/-- The first `n` terms of `sRemV P Q` packaged as a list. -/
def sRemVList (P Q : AzPolynomial K) (n : ℕ) : List (AzPolynomial K) :=
  (List.range n).map (sRemV P Q)

/-! ### Efficient single-pass implementation

The defining recursions `sRemS`/`sRemU`/`sRemV` mirror the abstract sequences for
*reasoning* (they recompute from scratch and are exponential — each `sRemS P Q
(n+2)` evaluates both `sRemS P Q n` and `sRemS P Q (n+1)`). For *computation* we
walk the sequence once, carrying the previous two entries and reusing a single
`quoRem` per step. `extendedSRemS_eq_spec` proves the fast version returns exactly
the spec lists. -/

/-- One step of the extended sequence: from the entries at indices `i-1` and `i`
    (each a triple `(S, U, V)`), produce the entry at index `i+1`, reusing a single
    `quoRem`. -/
def sRemStep (e₀ e₁ : AzPolynomial K × AzPolynomial K × AzPolynomial K) :
    AzPolynomial K × AzPolynomial K × AzPolynomial K :=
  if e₁.1 = 0 then (0, 0, 0)
  else
    (-(quoRem e₀.1 e₁.1).2,
      -e₀.2.1 + (quoRem e₀.1 e₁.1).1 * e₁.2.1,
      -e₀.2.2 + (quoRem e₀.1 e₁.1).1 * e₁.2.2)

/-- `sRemBuild n a b = [a, b, step a b, …]` of length `n`: the consecutive triples
    obtained by iterating `sRemStep`, each computed exactly once. -/
def sRemBuild : ℕ → (AzPolynomial K × AzPolynomial K × AzPolynomial K) →
    (AzPolynomial K × AzPolynomial K × AzPolynomial K) →
    List (AzPolynomial K × AzPolynomial K × AzPolynomial K)
  | 0, _, _ => []
  | m + 1, a, b => a :: sRemBuild m b (sRemStep a b)

/-- **BPR Algorithm 8.20 (Extended Signed Remainder Sequence).** The triple of
    lists `(SRemS, SRemU, SRemV)` of `P` and `Q`, each truncated to `n` terms.
    Computed by a single forward pass (`sRemBuild`): no recomputation. -/
def extendedSRemS (P Q : AzPolynomial K) (n : ℕ) :
    List (AzPolynomial K) × List (AzPolynomial K) × List (AzPolynomial K) :=
  let l := sRemBuild n (P, 1, 0) (Q, 0, 1)
  (l.map (·.1), l.map (·.2.1), l.map (·.2.2))

/-- The triple-valued spec entry at index `i`. -/
private def sRemTriple (P Q : AzPolynomial K) (i : ℕ) :
    AzPolynomial K × AzPolynomial K × AzPolynomial K :=
  (sRemS P Q i, sRemU P Q i, sRemV P Q i)

/-- The single step matches the defining recursions of `sRemS`/`sRemU`/`sRemV`. -/
private theorem sRemStep_triple (P Q : AzPolynomial K) (i : ℕ) :
    sRemStep (sRemTriple P Q i) (sRemTriple P Q (i + 1)) = sRemTriple P Q (i + 2) := by
  rw [sRemTriple, sRemTriple, sRemTriple, sRemS_succ_succ, sRemU_succ_succ, sRemV_succ_succ,
    sRemStep]
  by_cases h : sRemS P Q (i + 1) = 0
  · simp [h]
  · simp only [ite_eq_right h]
    rfl

/-- `sRemBuild` started at the entries of indices `i, i+1` reproduces the spec
    triples `[T i, T (i+1), …]`. -/
private theorem sRemBuild_eq (P Q : AzPolynomial K) (n : ℕ) : ∀ i,
    sRemBuild n (sRemTriple P Q i) (sRemTriple P Q (i + 1))
      = (List.range' i n).map (sRemTriple P Q) := by
  induction n with
  | zero => intro i; rfl
  | succ m ih =>
    intro i
    rw [sRemBuild, sRemStep_triple, show i + 2 = (i + 1) + 1 from rfl, ih (i + 1),
      List.range'_succ, List.map_cons]

/-- **The fast `extendedSRemS` returns exactly the spec lists** (`sRemSList`,
    `sRemUList`, `sRemVList`), so all spec-level facts (e.g. the Bézout identity)
    transfer to the efficient output. -/
theorem extendedSRemS_eq_spec (P Q : AzPolynomial K) (n : ℕ) :
    extendedSRemS P Q n = (sRemSList P Q n, sRemUList P Q n, sRemVList P Q n) := by
  have hb : sRemBuild n (P, 1, 0) (Q, 0, 1) = (List.range' 0 n).map (sRemTriple P Q) :=
    sRemBuild_eq P Q n 0
  simp only [extendedSRemS, hb, sRemSList_eq, sRemUList, sRemVList, List.map_map,
    List.range_eq_range']
  rfl

/-! ## Worked examples (over `AzRat`)

For `P = x² − 1`, `Q = x`: the signed remainder sequence is `x²−1, x, 1, 0`, with
cofactors `(U,V)` equal to `(1,0), (0,1), (−1, x), (−x, x²−1)`. -/

section Tests

private def exP : AzPolynomial AzRat := (parseAzPolynomial (R := AzRat) "x^2-1").get!
private def exQ : AzPolynomial AzRat := (parseAzPolynomial (R := AzRat) "x").get!

-- Cofactor values.
#guard toChars (sRemU exP exQ 2) == "-1"
#guard toChars (sRemV exP exQ 2) == "x"
#guard toChars (sRemU exP exQ 3) == "-x"
#guard toChars (sRemV exP exQ 3) == "x^2-1"

-- Bézout identity `sRemUᵢ · P + sRemVᵢ · Q = sRemSᵢ` (BPR Lemma 1.11).
#guard toChars (sRemU exP exQ 0 * exP + sRemV exP exQ 0 * exQ) == toChars (sRemS exP exQ 0)
#guard toChars (sRemU exP exQ 1 * exP + sRemV exP exQ 1 * exQ) == toChars (sRemS exP exQ 1)
#guard toChars (sRemU exP exQ 2 * exP + sRemV exP exQ 2 * exQ) == toChars (sRemS exP exQ 2)
#guard toChars (sRemU exP exQ 3 * exP + sRemV exP exQ 3 * exQ) == toChars (sRemS exP exQ 3)

-- The fast single-pass `extendedSRemS` agrees with the spec lists (cf.
-- `extendedSRemS_eq_spec`); here `SRemS = [x²−1, x, 1, 0]`, `SRemU = [1, 0, −1, −x]`,
-- `SRemV = [0, 1, x, x²−1]`.
#guard (sRemSList exP exQ 4).map toChars == ["x^2-1", "x", "1", "0"]
#guard extendedSRemS exP exQ 4
  == (sRemSList exP exQ 4, sRemUList exP exQ 4, sRemVList exP exQ 4)
#guard ((extendedSRemS exP exQ 4).2.1).map toChars == ["1", "0", "-1", "-x"]

end Tests

end Azurite.AzPolynomial
