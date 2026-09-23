# Karatsuba Correctness Proof — Planning Document

Goal: prove `karatsubaMulLimbs_toNat` in [`Azurite/AzNat/Equiv/Mul/Karatsuba.lean`](../Azurite/AzNat/Equiv/Mul/Karatsuba.lean), removing both `sorry`s.

The file already has:
- Correct theorem statements for `absSubLimbsKM_toNat`, `karatsubaMulLimbsRec_toNat`, `karatsubaMulLimbs_toNat`.
- Working helper lemmas: `toNat_slice_split`, `slice_lt_pow`, `toNat_full_eq_slice`, `toNat_replicate_zero`.
- Prose proof outline in the file docstring.

## Mathematical content (Theorem 1.2, MCA)

Let `β = 2^64`, `k = ⌈len/2⌉`, `m = len - k` (so `k+m = len`, `m ≤ k`).

Inputs split as `A = A₀ + A₁ β^k`, `B = B₀ + B₁ β^k`.

The algorithm computes:
- `C₀ = A₀ B₀` (size `2k`)
- `C₁ = A₁ B₁` (size `2m`)
- `C₂ = |A₀ − A₁| · |B₀ − B₁|` (size `2k`)
- `middle = C₀ + C₁ − s_A s_B C₂` (in a `2k+1` buffer)
  where `s_A s_B = +1` iff `signA = signB`.

Key algebra:
```
s_A · |A₀ − A₁| = A₀ − A₁                  (by definition of sign)
s_A s_B · C₂ = (A₀ − A₁)(B₀ − B₁)
            = A₀ B₀ − A₀ B₁ − A₁ B₀ + A₁ B₁
            = C₀ + C₁ − (A₀ B₁ + A₁ B₀)
⇒ middle = A₀ B₁ + A₁ B₀
⇒ result = C₀ + middle · β^k + C₁ · β^{2k}
        = (A₀ + A₁ β^k)(B₀ + B₁ β^k)
        = A · B
```

In ℕ (no signs):
- If `signA = signB` (cross-product positive): `middle = C₀ + C₁ − C₂`.
- If `signA ≠ signB` (cross-product negative): `middle = C₀ + C₁ + C₂`.

Both reduce to `A₀ B₁ + A₁ B₀`.

## Lean execution strategy

Split into stages, each as its own (`private`) lemma. Each stage:
- Takes the immediately preceding stage's output value/size.
- Returns a clean `toNat = …` characterization.

This avoids the `let`-folding problem (where `cpy.2` in a proof refers
to `(addSameLengthLimbs ...).2` but Lean doesn't unfold automatically).

### Stage lemmas for `absSubLimbsKM`

Pull each step out as a top-level definition with its own `_toNat` lemma:

```lean
private def absSubLimbsKM.copy (a : Array UInt64) (loA k : Nat)
    (hA : loA + k ≤ a.size) (h_kpos : 0 < k) : { c : Array UInt64 // c.size = k }

private def absSubLimbsKM.subPart (a : Array UInt64) (loA k m : Nat)
    (hA : loA + k + m ≤ a.size) (h_le : m ≤ k) (h_kpos : 0 < k) (h_mpos : 0 < m) :
    { d : Array UInt64 // d.size = k } × Bool
  -- = subGeqLimbs of (copy a loA k) by a[loA+k..]

private def absSubLimbsKM.negPart (d : Array UInt64) (h : d.size = k) :
    { n : Array UInt64 // n.size = k }
  -- = subSameLengthLimbs of zero buffer by d
```

Then `absSubLimbsKM` becomes a thin wrapper, and each stage gets a focused `_toNat` lemma:

| Lemma | Statement |
|---|---|
| `copy_toNat` | `toNat (copy a loA k).val = A₀` |
| `subPart_toNat` | `(subPart …).2 = true ↔ A₀ < A₁`; if `false`, `toNat .1 = A₀ - A₁`; if `true`, `toNat .1 = β^k + A₀ - A₁` |
| `negPart_toNat` | `toNat (negPart d) = β^k - toNat d` (provided `0 < toNat d`) |

Then `absSubLimbsKM_toNat` is a 10-line case split combining these.

**Alternative if we don't want to refactor the algorithm**: use an explicit term-level proof structured around `have` (no `let`). Reference everything via the full term and rely on `simp` / `change` for unfolding. Doable but messy; stage extraction is cleaner.

### Stage lemmas for `karatsubaMulLimbsRec`

Same approach — break the algorithm body into named stages:

```lean
private def karatsubaMulLimbsRec.middleBuf
    (k m : Nat) (C₀ C₁ C₂ : Array UInt64) (sameSign : Bool)
    (hC₀ : C₀.size = 2*k) (hC₁ : C₁.size = 2*m) (hC₂ : C₂.size = 2*k)
    (h_kpos : 0 < k) (h_mpos : 0 < m) (h_le : m ≤ k) :
    { mid : Array UInt64 // mid.size = 2*k + 1 }

private def karatsubaMulLimbsRec.assemble
    (k m len : Nat) (C₀ C₁ middle : Array UInt64)
    (hC₀ : C₀.size = 2*k) (hC₁ : C₁.size = 2*m) (hMid : middle.size = 2*k + 1)
    (hkm : k + m = len) (h_kpos : 0 < k) (h_mpos : 0 < m) :
    { c : Array UInt64 // c.size = 2*len }
```

Then for each, prove a focused `_toNat` lemma:

| Lemma | Statement |
|---|---|
| `middleBuf_toNat` | `toNat (middleBuf …) = if sameSign then toNat C₀ + toNat C₁ - toNat C₂ else toNat C₀ + toNat C₁ + toNat C₂`, plus a bound `< 2 β^(k+m)` for the final assembly step |
| `assemble_toNat` | `toNat (assemble …) = toNat C₀ + toNat middle · β^k + toNat C₁ · β^{2k}` (using `toNatLimbsList_append` for `C₀ ++ C₁` and `addGeqLimbs_toNat` for the middle add) |

The main theorem `karatsubaMulLimbsRec_toNat` then becomes a strong induction
that:
1. Splits `len < max 2 threshold` (base case) → `schoolbookMulLimbs_toNat`.
2. Otherwise:
   - Use IH on `k` and `m` to get `toNat C₀ = A₀ B₀`, `toNat C₁ = A₁ B₁`.
   - Use `absSubLimbsKM_toNat` to get `toNat absA = |A₀ − A₁|`, similarly `absB`.
   - Use IH on `k` again for `toNat C₂ = toNat absA · toNat absB = |A₀ − A₁| · |B₀ − B₁|`.
   - Use `middleBuf_toNat` + case split on `signA = signB` to get
     `toNat middle = A₀ B₁ + A₁ B₀`.
   - Use `assemble_toNat` to combine.
   - Use `toNat_slice_split` to relate `A`, `A₀`, `A₁`.

## Bound argument: `addLen` truncation

The implementation uses `addLen = min(2k+1, 2*len − k)`. When `len = 3`, `2k+1 = 5 > 4 = 2*len − k`, so the top limb of `middle` is truncated.

Mathematical fact: `middle = A₀ B₁ + A₁ B₀ < 2β^(k+m) ≤ β^(k+m+1) ≤ β^addLen`
(the last step requires `addLen ≥ k + m + 1`, which holds since
`k+m = len = (k+m)` and `addLen ≥ k+m+1` for all `len ≥ 2` we recurse on).

So the truncated portion is zero and `toNat slice (middle, 0, addLen) = toNat middle`.

This will need its own helper: **`toNat_slice_eq_full_of_lt_pow`** —
"if `toNat a < 2^(64*j)` and `j ≤ a.size`, then `toNat (a.take j) = toNat a`".

## Carry argument: final `addGeqLimbs` produces no carry

After all the math, we get
```
toNat acc.1 + acc.2.toNat · β^(2*len) = A · B
```
with `A · B < β^(2*len)` and `acc.1.size = 2*len` (so `toNat acc.1 < β^(2*len)`)
and `acc.2.toNat ∈ {0, 1}`. Conclude `acc.2 = false` and
`toNat acc.1 = A · B`.

## Termination

`karatsubaMulLimbsRec` uses `termination_by len` with `decreasing_by … omega`.
The induction proof should mirror this: strong induction `Nat.strong_induction_on`
on `len`. Inductive hypotheses on `k` (with `k < len`) and `m` (with `m < len`).

## Effort estimate

- Stage extraction (refactor `Karatsuba.lean`): ~30 lines.
- `absSubLimbsKM_toNat` (post-refactor): ~80 lines across 3 stage lemmas + main.
- `middleBuf_toNat`: ~60 lines, mostly Nat arithmetic and `addGeqLimbs_toNat` / `subGeqLimbs_toNat` chaining.
- `assemble_toNat`: ~80 lines (`toNatLimbsList_append` + `addGeqLimbs_toNat` + carry-out reasoning).
- `karatsubaMulLimbsRec_toNat`: ~120 lines (induction skeleton, base case, recursive case combining all the above).

Total: roughly 350–400 lines of new proof text. Tractable in 3–4 focused passes.

## Order of operations

1. **Refactor** `Karatsuba.lean`: extract `absSubLimbsKM.copy`, `.subPart`, `.negPart` and the karatsuba inner stages (`middleBuf`, `assemble`) as named definitions. Verify `karatsubaMulLimbs` still equals what it was via `rfl`-checks.
2. **Prove** `copy_toNat`, `subPart_toNat`, `negPart_toNat` → combine into `absSubLimbsKM_toNat`.
3. **Prove** `middleBuf_toNat` and the bound on `toNat middle`.
4. **Prove** `assemble_toNat` (handles the carry-out argument).
5. **Prove** `karatsubaMulLimbsRec_toNat` by strong induction.
6. Remove `sorry`s. Add a `#guard` example if desired.
