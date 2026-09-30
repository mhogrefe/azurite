# Schönhage–Strassen multiplication: plan and source ledger

The top of the multiplication ladder (`docs/toom_cook_plan.md`, milestone 7). The source is
Brent & Zimmermann, *Modern Computer Arithmetic* (MCA), §2.3, walked through fragment by
fragment; the user keeps the fragments in a separate document and this file records, for each
one, what it states, what was formalized and where, and what it defers to later fragments.

Standing rules are those of the rest of the library: Apache-2.0, so no GMP code; the
description in MCA (and any other published description the user supplies) is the only source.
Formal statements live under `Azurite/BrentZimmermann/Chapter2/`, namespace `Azurite.BZ`; the
eventual limb-level implementation goes under `Azurite/AzNat/Mul/` like the Toom variants, with
the `BZ` theory as its specification.

## Where the FFT stage plugs in

`MulThresholds` (in `Azurite/AzNat/Mul.lean`) ends at Toom-4 (from 512 limbs, measured in
milestone 5). Toom-4 wins over Toom-3 by only 3–6 % in our cost model, so the FFT stage will
take over directly from Toom-4 at a cutoff to be measured; Toom-6.5/8.5 are not planned unless
the FFT crossover turns out to be far above 4096 limbs.

## Fragment ledger

### Fragment 1 — MCA §2.3, §2.3.1 "Theoretical setting" (2026-09-27)

**States.** Over a ring `R`, `K ≥ 2`, and a *principal* `K`-th root of unity `ω` (`ω^K = 1` and
`∑_{j<K} ω^{ij} = 0` for `1 ≤ i < K`), the Fourier transform of `a = [a_0, …, a_{K−1}]` is
`â_i = ∑_j ω^{ij} a_j` (2.1). Transforming twice gives `K · [a_0, a_{K−1}, …, a_1]`; transforming
forward then *backward* (the same sum with `ω^{−1}`) gives `K · a`. The proofs reduce to the
geometric sums `∑_j τ^j` with `τ = ω^{i+ℓ}` resp. `ω^{ℓ−i}`, which vanish unless the exponent is
`0 mod K`. Forward references: the Convolution Theorem and computing convolutions with three
transforms (§2.9); the FFT itself and the `O(n log n log log n)` integer multiplication
(§2.3.2–2.3.3).

**Formalized** in `Azurite/BrentZimmermann/Chapter2/DFT.lean` (3-axiom):

| MCA | Lean |
|---|---|
| principal `K`-th root of unity | `IsPrincipalRoot ω K` (structure: `pow_eq_one`, `sum_pow_eq_zero`) |
| `∑_j τ^j` vanishes unless `τ = 1` | `IsPrincipalRoot.sum_pow_mul : ∑_{j<K} ω^{mj} = if m % K = 0 then K else 0` (via `pow_mod`) |
| `ω^{−1}` (used by the backward transform) | `IsPrincipalRoot.inv : IsPrincipalRoot (ω^(K−1)) K` |
| (2.1) | `dft ω a : Fin K → R` |
| backward transform | `dftInv ω a := dft (ω^(K−1)) a` |
| `â̂ = K · [a_0, a_{K−1}, …, a_1]` | `dft_dft`, `dft_dft_apply : dft ω (dft ω a) i = K * a (−i)` |
| `ã̂ = K · a` | `dftInv_dft`, `dftInv_dft_apply : dftInv ω (dft ω a) i = K * a i` |

Design notes. Vectors are `Fin K → R` with `[NeZero K]` where negation of indices is needed
(MCA's `K ≥ 2` is not needed for these statements). The inverse root is written `ω^(K−1)`
rather than `ω⁻¹` so that nothing requires a field or a `Units` coercion; in `ℤ/(2^N+1)` the
root `2` has inverse `2^(2N−1)`, i.e. `−2^(N−1)`, which is a cheap shift in the implementation.
Mathlib's `ZMod.dft` is `ℂ`-valued and not usable here. The principal (rather than primitive)
notion is what the Schönhage–Strassen ring needs: it has zero divisors, and the vanishing sums are
exactly the invertibility of the transform.

**Deferred.** Convolution Theorem (§2.9 or when the fragment arrives); the FFT recursion
(§2.3.2); the choice of ring and root for integer multiplication (§2.3.3).

### Fragment 2 — MCA §2.3.2 "The fast Fourier transform" (2026-09-27)

**States.** Naive evaluation of (2.1) is `Ω(K²)`; the FFT does it in `O(K log K)`. From here on
`K` is a power of two (§2.9 for the general case). The worked example `K = 8` shares partial sums:
first `a_{j,j+4} = a_j + a_{j+4}` and `a_{j+4,j} = a_j + ω^4 a_{j+4}` for `j < 4`; then `â_{even}`
are combinations of the `a_{j,j+4}` with powers of `ω²`, and `â_{odd}` combinations of
`ω^j a_{j+4,j}` with powers of `ω²`; the second stage repeats the split on each half (with
`ω^4 = (ω²)²` playing the role of `ω^4`), and the third stage finishes. (Two indices in the
final display are truncated in the source: `a_{3,7,1}` and `a_{1,5,3}` are `a_{3,7,1,5}` and
`a_{1,5,3,7}`.) The example does not yet mention that the in-place version delivers the outputs
in bit-reversed order; the recursion as written delivers them in natural order.

**Formalized** in `Azurite/BrentZimmermann/Chapter2/FFT.lean` (3-axiom), as the general recursion
the example instantiates:

| MCA | Lean |
|---|---|
| `a_{j,j+m} = a_j + a_{j+m}` | the `s` of `fftRec` |
| `ω^j a_{j+m,j} = ω^j (a_j + ω^m a_{j+m})` | the `d` of `fftRec` |
| `â_{2i}`, `â_{2i+1}` from half-size transforms at `ω²` | `fftRec ω (k+1) a r = if r even then fftRec (ω²) k s (r/2) else fftRec (ω²) k d (r/2)` |
| the FFT equals (2.1) | `fftRec_eq_dftNat` (`ω^(2^k) = 1`, `i < 2^k`); `fft k ω a = dft ω a` (`fft_eq_dft`) |

Design notes. The recursion is on `ℕ → R` with an explicit length (`dftNat ω K a i` is (2.1)
on such functions; `extendZero` and `dft_eq_dftNat` connect to `Fin K → R`). MCA's `ω^4 a_4` is
kept as `ω^m a_{j+m}` rather than `−a_{j+m}`: correctness then needs only `ω^K = 1`, whereas
`ω^{K/2} = −1` needs `K/2` to be a non-zero-divisor (true in `ℤ/(2^N+1)` but not in general).
The two half-step identities are `dftNat_two_mul` and `dftNat_two_mul_add_one`, each a
`Finset.sum_range_add` split plus exponent algebra. The implementation later will want the
in-place, bit-reversed form; that is a separate, index-only refinement of `fftRec`.

**Deferred.** General `K` (§2.9); the ring and root for integer multiplication and the
operation count `O(n log n log log n)` (§2.3.3); the Convolution Theorem (§2.9).

### Fragment 3 — MCA §2.3.2, operation count, butterflies, in-place (2026-09-27)

**States.** The `K = 8` example uses `8 + 8 + 8 = 24 = 8 lg 8` steps of the form `a ← b + ω^j c`.
Steps pair up as `(a, a') = (b + ω^j c, b + ω^{j+K/2} c) = (b + ω^j c, b − ω^j c)` "since
`ω^{K/2} = −1`", so `ω^j c` is computed once per pair: a *butterfly*. The transform can be done
*in place*, the butterfly on `(a_j, a_{j+K/2})` overwriting those two entries. Algorithm
ForwardFFT follows in the next fragment.

**Formalized** in `Azurite/BrentZimmermann/Chapter2/FFT.lean` (3-axiom):

| MCA | Lean |
|---|---|
| "since `ω^{K/2} = −1`" | `IsPrincipalRoot.natCast_mul_one_add_pow_half : (K/2 : R) · (1 + ω^{K/2}) = 0` for any principal `K`-th root; `IsPrincipalRoot.pow_half_eq_neg_one : ω^{K/2} = −1` when `K/2` is a unit of `R` |
| butterfly `(b + ω^j c, b − ω^j c)` | `fftRecSub` (the `d` of `fftRec` becomes `ω^j (a_j − a_{j+m})`) |
| it computes the same transform | `fftRecSub_eq_fftRec` (`ω^{K/2} = −1`), `fftRecSub_eq_dftNat`, `fftRecSub_eq_dftNat_of_principal` (principal root, `K/2` a unit) |

Design notes. In a ring with zero divisors a principal root need not satisfy `ω^{K/2} = −1`; the
general fact is `(K/2) · (1 + ω^{K/2}) = 0` (the `K/2`-th vanishing sum has terms alternating
`1, ω^{K/2}`). In `ℤ/(2^N + 1)` the relevant `K/2` is a power of two and the modulus is odd, so
the unit hypothesis holds and the butterfly form is exact. The count `K lg K` is visible in
`fftRecSub`: `K/2` butterflies (each one twiddle product, one addition, one subtraction) at each
of `lg K` levels; it is not stated as a theorem (that would need a cost-instrumented copy of the
recursion, which the implementation's own benchmarks will make moot). In-place evaluation is an
implementation matter for the algorithm fragment; `fftRecSub` is the functional form it must agree
with.

**Deferred.** Algorithm ForwardFFT (in place, output order); general `K` (§2.9); the ring and
root for integer multiplication (§2.3.3); the Convolution Theorem (§2.9).

### Fragment 4 — MCA Algorithm 2.2 ForwardFFT and Theorem 2.1 (2026-09-27)

**States.** `bitrev(j, K)` reverses the `lg K` bits of `j` (for `K = 8`: `0,4,2,6,1,5,3,7`).
Algorithm 2.2: for `K = 2` replace `[a_0, a_1]` by `[a_0 + a_1, a_0 − a_1]`; otherwise transform
the even-indexed entries and the odd-indexed entries in place (at `ω²`, size `K/2`), then for
`j < K/2` replace `(a_{2j}, a_{2j+1})` by `(a_{2j} + ω^{j'} a_{2j+1}, a_{2j} − ω^{j'} a_{2j+1})`
with `j' = bitrev(j, K/2)`. Theorem 2.1: the result is the transform in bit-reversed order, in
`O(K log K)` ring operations. Proof by induction: `b_j = ∑_ℓ ω^{2j'ℓ} a_{2ℓ}`,
`c_j = ∑_ℓ ω^{2j'ℓ} a_{2ℓ+1}` by induction (they sit at `a_{2j}`, `a_{2j+1}`), so the butterfly
gives `â_{j'}` and, using `−ω^{j'} = ω^{K/2 + j'}` and `ω^{2j'} = ω^{2(j' + K/2)}`,
`â_{K/2 + j'}`; and `bitrev(2j, K) = j'`, `bitrev(2j+1, K) = K/2 + j'`. Note that this is
*decimation in time* (split the inputs by parity, combine after recursing) whereas the `K = 8`
example of fragment 2 was decimation in frequency (split first, recurse on sums and
differences); both are `O(K log K)` and both are useful, since a DIF forward transform followed
by a DIT backward transform needs no bit reversal at all.

**Formalized** in `Azurite/BrentZimmermann/Chapter2/FFT.lean` (3-axiom):

| MCA | Lean |
|---|---|
| `bitrev(j, 2^k)` | `bitrev k j` (recursive on the bits); `bitrev_lt`, `bitrev_two_mul` (`bitrev(2j, K) = bitrev(j, K/2)`), `bitrev_two_mul_add_one` (`bitrev(2j+1, K) = K/2 + bitrev(j, K/2)`), `bitrev_succ_of_lt`, `bitrev_succ_pow_add`, `bitrev_bitrev` (an involution on `k`-bit numbers, needed later to undo the order) |
| Algorithm 2.2 | `forwardFFT ω k a r` (position `r` of the in-place result; one recursive clause, the `K = 2` case being the general step over the identity at `K = 1`) |
| Theorem 2.1 | `forwardFFT_eq_dftNat : ω^{K/2} = −1 → r < K → forwardFFT ω (k+1) a r = dftNat ω K a (bitrev (k+1) r)`; `forwardFFT_eq_dft` on `Fin K → R` |

Design notes. The hypothesis is `ω^{K/2} = −1` (which gives `ω^K = 1`); with a principal root
it follows from `IsPrincipalRoot.pow_half_eq_neg_one` when `K/2` is a unit. The induction is
MCA's: the two recursive transforms are the induction hypothesis at `ω²`, the even/odd split of
`∑_{ℓ<K}` is `sum_range_two_mul_split`, and the two exponent identities are handled by
rewriting `ω^{2K'ℓ}` to `1` and `ω^{K'}` to `−1` (with `K' = K/2` protected from the generic
`pow_add` rewrite, which otherwise splits `2^(k+1)`). The complexity bound is again not stated
formally. In-place storage is an implementation matter; `forwardFFT` fixes the values each
position must hold.

**Deferred.** General `K` (§2.9); the ring and root for integer multiplication and the
`O(n log n log log n)` count (§2.3.3); the Convolution Theorem (§2.9); the backward transform in
bit-reversed order (presumably next, or in §2.3.3).

### Fragment 5 — MCA Algorithm 2.3 BackwardFFT and Theorem 2.2 (2026-09-28)

**States.** Input in bit-reversed order, output in normal order. For `K = 2` the same butterfly
as forward (`ω = ω^{−1} = −1`); otherwise transform the first and second halves in place (at
`ω²`), then for `j < K/2` replace `(a_j, a_{K/2+j})` by `(a_j + ω^{−j} a_{K/2+j}, a_j − ω^{−j}
a_{K/2+j})` with `ω^{−j} = ω^{K−j}`. Theorem 2.2: the result is the backward transform in normal
order, `O(K log K)`. Proof: the first half of a bit-reversed vector is the bit-reversed vector of
the even-indexed entries (`bitrev(2j, K) = bitrev(j, K/2)`) and the second half that of the
odd-indexed ones (`bitrev(2j+1, K) = K/2 + bitrev(j, K/2)`), so induction gives
`b_j = ∑_ℓ ω^{−2jℓ} a_{2ℓ}`, `c_j = ∑_ℓ ω^{−2jℓ} a_{2ℓ+1}`, and the butterfly gives `ã_j` and,
via `−ω^{−j} = ω^{−K/2−j}` and `ω^{−2j} = ω^{−2(K/2+j)}`, `ã_{K/2+j}`.

**Formalized** in `Azurite/BrentZimmermann/Chapter2/FFT.lean` (3-axiom):

| MCA | Lean |
|---|---|
| Algorithm 2.3 | `backwardFFT ω k a r` (position `r`; recursive calls on `a` and `fun s => a (K/2 + s)`; twiddle `ω^(K − j)` as in MCA's remark) |
| Theorem 2.2 | `backwardFFT_eq_dftNat : ω^{K/2} = −1 → (∀ r < K, a r = x (bitrev r)) → j < K → backwardFFT ω (k+1) a j = dftNat (ω^(K−1)) K x j` |
| forward then backward | `backwardFFT_forwardFFT : IsPrincipalRoot ω K → IsUnit (K/2 : R) → backwardFFT ω (k+1) (forwardFFT ω (k+1) (extendZero x)) j = K · x j` (Theorems 2.1, 2.2 and `dftInv_dft`) |

Design notes. The input relation is stated pointwise for `r < K` (`a r = x (bitrev r)`) rather
than as a function equality, so the algorithm can be fed the raw output of `forwardFFT` (whose
values beyond `K` are unspecified). The proof introduces `ν = ω^{K−1}` and works with the facts
`ν ω = 1`, `ν^K = 1`, `ν^{K/2} = −1`, `ω^{K−j} = ν^j` (`j ≤ K`) and `(ω²)^{K/2−1} = ν²`
(uniqueness of inverses), after which the two exponent identities are the same as in Theorem
2.1 with `ν` in place of `ω`. The round trip `backwardFFT_forwardFFT` is the first end-to-end
statement of the arc: transform, do something pointwise, transform back, divide by `K` (the
division is the one place the ring has to cooperate; in `ℤ/(2^N+1)` it is a shift).

**Deferred.** General `K` (§2.9); the ring and root for integer multiplication and the
`O(n log n log log n)` count (§2.3.3); the Convolution Theorem (§2.9), which is what turns the
round trip into a multiplication.

### Fragment 6 — MCA §2.3.3 Algorithm 2.4 FFTMulMod, Theorem 2.3, example, remarks (2026-09-29)

**States.** Multiply `0 ≤ A, B < 2^n + 1` modulo `2^n + 1`, with `K = 2^k`, `n = MK`: cut `A`, `B`
into `K` digits of `M` bits (`a_{K−1} ≤ 2^M` allowed, since `A` may equal `2^n`); choose
`n' ≥ 2n/K + k` a multiple of `K`, `θ = 2^{n'/K}`, `ω = θ²`; weight `a_j ← θ^j a_j`,
`b_j ← θ^j b_j` mod `2^{n'}+1`; ForwardFFT both; multiply pointwise mod `2^{n'}+1` (recursively,
or by a simpler algorithm when `n'` is small); BackwardFFT; `c_j ← c_j /(K θ^j)`; if
`c_j ≥ (j+1) 2^{2M}` subtract `2^{n'}+1`; `C = ∑ c_j 2^{jM}` (mod `2^n+1`). Theorem 2.3 (proof):
`A·B ≡ ∑_j c_j 2^{jM}` with `c_j = ∑_{ℓ+m=j} a_ℓ b_m − ∑_{ℓ+m=K+j} a_ℓ b_m` (2.2);
`(j+1−K) 2^{2M} ≤ c_j < (j+1) 2^{2M}`; after the transforms and the pointwise products,
Theorems 2.1–2.2 give `c'_i = K ∑_{ℓ+m=i} a'_ℓ b'_m + K ∑_{ℓ+m=K+i} a'_ℓ b'_m` with
`a' = θ^ℓ a_ℓ`, i.e. `K θ^i (∑_{ℓ+m=i} − ∑_{ℓ+m=K+i})` since `θ^K = −1`; the division by `K θ^i`
and the correction recover `c_i`. Example: `n = 2^20`, `K = 1024`, `n' = 3072` (or `K = 512`,
`n' = 4608`). Remark 1: recursion depth 1–2 in practice; the `log log n` is a constant. Remark
2: with `θ = 1` (no weighting, divide by `K`, correction at `K 2^{2M}`) the same algorithm
computes `A·B mod (2^n − 1)` (McLaughlin, §2.4.3).

**Formalized** in `Azurite/BrentZimmermann/Chapter2/FFTMulMod.lean` (3-axiom), the mathematics of
the algorithm over a general commutative ring and over `ℤ`, ready for the implementation to
instantiate at `R = ℤ/(2^{n'}+1)`, `θ = 2^{n'/K}`:

| MCA | Lean |
|---|---|
| `ω = θ²` is a principal `K`-th root in `ℤ/(2^{n'}+1)` | `IsPrincipalRoot.of_pow_two_pow_eq_neg_one` (from `ω^{K/2} = θ^K = −1` alone, in any ring; via `geom_sum_two_pow : ∑_{j<2^k} τ^j = ∏_{t<k} (1 + τ^{2^t})`) and `two_pow_eq_neg_one_zmod` |
| Convolution Theorem (§2.9) | `cyclicConv`, `dft_cyclicConv : dft ω (cyclicConv a b) j = dft ω a j * dft ω b j` (`ω^K = 1`); `sum_cyclicConv` |
| the two sums of the proof, `θ^K = −1` | `weight`, `negacyclicConv` (2.2), `cyclicConv_weight : cyclicConv (weight θ a) (weight θ b) i = θ^i · negacyclicConv a b i` |
| steps 4–11 | `dftInv_dft_weight_mul : dftInv ω (dft ω a' * dft ω b') i = K · θ^i · c_i`; with Algorithms 2.2/2.3, `backwardFFT_forwardFFT_weight_mul` (hypothesis `θ^K = −1` only) |
| (2.2): `A·B ≡ ∑ c_j 2^{jM}` | `sum_weight_mul_sum_weight : (∑ θ^ℓ a_ℓ)(∑ θ^m b_m) = ∑ θ^j c_j` in any ring with `θ^K = −1`; at `θ = 2^M` in `ℤ/(2^{MK}+1)` this is (2.2) |
| `(j+1−K) 2^{2M} ≤ c_j < (j+1) 2^{2M}` | `negacyclicConv_bounds` (digits in `[0, B)`; `−(K−1−j) B² ≤ c_j < (j+1) B²`) |
| steps 12–13 | `int_recover_of_mem_window : U − N ≤ c < U → c = if U ≤ c % N then c % N − N else c % N` |

Design notes. The digit bound is strict (`a_j < 2^M`): the implementation will handle
`A = 2^n` or `B = 2^n` separately (the product is then `−B` resp. `−A` modulo `2^n+1`), which
removes MCA's `a_{K−1} ≤ 2^M` exception and its `K ≥ 2` subtlety. `negacyclicConv` is indexed by
`Fin K` with the sign decided by `ℓ ≤ i`, so the bound proof is a filter/card argument
(`Fin.card_Iic`). The root-of-unity facts need no unit hypothesis: `θ^K = −1` gives
`ω^{K/2} = −1`, which gives principal-ness; the only division in the algorithm is by `K θ^j`, a
power of two, which in `ℤ/(2^{n'}+1)` is a shift (`2^{−t} = −2^{n'−t}`).

**Everything in §2.3 is now formalized**; what remains is the implementation (below).

## Implementation plan (Schönhage–Strassen in `AzNat`)

Digits will be limb slices: choose `M` a multiple of 64, so `a_j = block a 0 len (M/64) j` from
`Mul/ToomEval.lean` and the decomposition `A = ∑ a_j 2^{jM}` is `sliceVal_eq_polyEval_blocks`.
All modular arithmetic is in `ℤ/(2^{n'}+1)` with `n'` a multiple of `64` as well.

1. **The Fermat ring `ℤ/(2^N + 1)` on limb arrays** (`Azurite/AzNat/Fermat.lean`, spec
   `Equiv/Fermat.lean`). Representatives `0 ≤ x ≤ 2^N` in `N/64 + 1` limbs (the top limb is `0`
   or `1`). Operations: `add`, `sub`, `neg`, `mulPow2 t` (`x · 2^t`: a shift whose overflow
   wraps with a sign, since `2^N ≡ −1`), `divPow2 t` (`x / 2^t = −x · 2^{N−t}`), `reduce` of a
   `2N`-bit product (`hi · 2^N + lo ≡ lo − hi`), `mul` = full product (the production `mul`,
   i.e. the Toom ladder, or recursively `fftMulMod`) followed by `reduce`. Each proven equal to
   the `ZMod (2^N + 1)` operation (pattern of `AzZModPow2`).
2. **In-place FFT over the Fermat ring** on an `Array` of representatives (one flat
   `Array UInt64` with a stride, or an `Array (Array UInt64)`): `forwardFFTLimbs`,
   `backwardFFTLimbs` with `ω = 2^{2n'/K}`, all twiddle multiplications being `mulPow2`. Proven
   equal, position by position, to `BZ.forwardFFT` / `BZ.backwardFFT` on the `ZMod` values.
3. **`fftMulMod`** (Algorithm 2.4) for `A, B < 2^n + 1` given `k` and `M` (`n = 2^k · M`):
   weighting, transforms, pointwise products (through step 1's `mul`), division by `K θ^j`,
   recovery of the signed `c_j` (`int_recover_of_mem_window`), assembly `∑ c_j 2^{jM}` modulo
   `2^n + 1` (signed coefficients: `AzInt` `assemble` from the Toom framework, then one modular
   reduction). Correctness: `toNat (fftMulMod A B) = (A · B) % (2^n + 1)`, from
   `sum_weight_mul_sum_weight` and `backwardFFT_forwardFFT_weight_mul` at
   `R = ZMod (2^{n'}+1)`, `θ = 2^{n'/K}`, plus `negacyclicConv_bounds` for the recovery.
   Parameter choice as in MCA: `k ≈ lg n / 2`, `n' ≥ 2M + k` rounded up to a multiple of
   `64 K`.
4. **Integer multiplication** `fftMul A B`: pick `n ≥ bits A + bits B` of the form `2^k · M`
   (then `A · B < 2^n + 1` and the residue is the product); add to `MulThresholds` above Toom-4
   with a cutoff to be measured (a `tune_aznat_fft` sweep like milestone 5's); squaring as the
   same algorithm with `a = b` (one forward transform saved).
5. **Optional later**: the recursive pointwise products (`fftMulMod` inside step 3 when `n'` is
   large; MCA's depth 1–2), and the `mod 2^n − 1` variant of Remark 2 if a use appears.

Items 1–3 need no benchmarking; item 4's cutoff does.

## Status log

* **2026-09-29 — Items 1–4 implemented and proven (3-axiom); item 4's cutoff not yet tuned.**
  * `Azurite/AzFermat/Basic.lean` + `Equiv/Basic.lean`: `AzFermat N` (canonical `AzNat` residue in
    `[0, 2^N]`), `add`/`sub`/`neg`, `reduceSplit` (`hi ≤ 2^N`), `reduceAny` (recursive on `hi`, no
    division anywhere), `mulWith mulFn` (the multiplier is a parameter, so the FFT can use the Toom
    ladder without an import cycle), `mulPow2`/`divPow2` (exponent reduced modulo `2N`, sign from
    `2^N ≡ −1`); every operation proven against `ZMod (2^N + 1)`.
  * `Azurite/AzFermat/FFT.lean` + `Equiv/FFT.lean`: Algorithms 2.2 and 2.3 on `{ b : Array _ //
    b.size = 2^k }` with root `2^e`, proven position by position equal to `BZ.forwardFFT` /
    `BZ.backwardFFT` (the recursion copies even/odd or lower/upper halves; not yet in place).
  * `Azurite/AzNat/Mul/SchonhageStrassen.lean` + `Equiv/Mul/SchonhageStrassen.lean`: Algorithm 2.4
    in stages (`ssWeighted`, `ssProducts`/`ssSquares`, `ssCoefficients`, `ssAssemble`, `ssFinish`),
    `fftMulModWith_toNat` (Theorem 2.3) via `ssFinish_toNat`, which is generic in the array of
    pointwise products so the squaring version is a one-line corollary; `fftMul`/`fftSquare` with
    `ssParams` (`k = ⌊lg L⌋/2`, `w = ⌈L/K⌉`) proven exact (`toNat_fftMul`, `toNat_fftSquare`);
    `fftMulLimbs`/`fftSquareLimbs` for the ladders.  Design changes from the plan: digits are
    reduced by `ofAzNat` (one comparison) instead of carrying a bound proof; the signed
    coefficients are produced directly as residues modulo `2^n + 1` and assembled by Horner's rule
    in `AzFermat n`, so no `AzInt` and no remainder operation is involved.  The exceptional case
    `A = 2^n` never arises for `fftMul` (`n` is chosen above the product's size).
  * Dispatchers: `MulThresholds.fft` and `squareDispatchFFTCutoff` put the FFT above Toom-4 in `balancedMulLimbs` (`toomLadderLimbs`/`toomLadderMul` below
    it) and `squareLimbsParam` (`toomSquareLadderLimbs`/`toomSquareLadder`); `toNat_mul` and
    `toNat_square` re-established.  `#guard`s in `Azurite/AzNat/Tests/SchonhageStrassen.lean`.
  * Gotcha: Mathlib's vector-literal notation `![…]` reaches the tuner through the new imports, so
    `xs[i]![j]!` must be written `(xs[i]!)[j]!`.
  * Next: item 4's cutoff (`tune_aznat_fft_crossover`, `tune_aznat_square_fft_crossover`,
    `tune_aznat_fft_dispatch` in `Tune.lean`) on a quiet machine; then, if the numbers ask for it,
    item 5 and the in-place transform.

* **2026-09-29 — Item 4 tuned: FFT cutoffs measured** (quiet machine; `tune_aznat_fft_crossover`,
  `tune_aznat_square_fft_crossover` on pairs of exactly `n` limbs, median of three, the Toom
  ladder with the milestone-5 thresholds against `fftMul`/`fftSquare` using that ladder for the
  pointwise products; `tune_aznat_fft_dispatch` over random pairs of mean 524288 bits).

  | limbs | mul: Toom µs | mul: FFT µs | FFT/Toom | sqr: Toom µs | sqr: FFT µs | FFT/Toom |
  |---|---|---|---|---|---|---|
  | 1024 | 2251 | 4615 | 205 % | 1532 | 3294 | 214 % |
  | 4096 | 17378 | 24560 | 141 % | 12364 | 17988 | 145 % |
  | 8192 | 48123 | 58000 | 120 % | 34702 | 43654 | 125 % |
  | 16384 | 131825 | 137708 | 104 % | 94935 | 102641 | 108 % |
  | 24576 | 233862 | 230765 | 98 % | 169401 | 172618 | 101 % |
  | 32768 | 359176 | 337090 | 93 % | 261031 | 257747 | 98 % |
  | 49152 | 639543 | 546706 | 85 % | 467190 | 422396 | 90 % |
  | 65536 | 967151 | 785906 | 81 % | 698723 | 604363 | 86 % |

  The dispatcher sweep at mean 524288 bits (about 8192 limbs) confirms that no cutoff at or
  below 16384 helps there. Constants set: `MulThresholds.fft = 24576`,
  `squareDispatchFFTCutoff = 32768` (1.5 and 2 million bits). The crossover is high because
  this first version allocates freely: every `AzFermat` operation builds a fresh `AzNat`, the
  transform copies its halves at each level, and the pointwise products pad to a common
  length. The asymptotics show through nonetheless (19 % at 65536 limbs and widening). The
  levers for lowering the crossover, in the order they should pay: an in-place transform on
  one flat limb buffer, shift-with-wraparound and add/sub written at limb level for the Fermat
  ring, and the recursive pointwise products of item 5. None of them changes a proof
  statement.
