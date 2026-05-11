# Plan for `offdiag_prod_eq_omega_sq`

## Goal

Prove the identity:
```
((s ×ˢ s - s.map diag).map sub).prod
  = algebraMap R (Ri R) ((-1)^{N_t} · ω²)
```
where `s = P.aroots (Ri R)`, `N_t = t(t-1)/2`, `t = linears.card`, and
`ω = vandermondeOmega linears quadratics`.

## Setup

By `aroots_decomposition`: `s = sl + sq` where:
- `sl := linears.map ι` (real roots, |sl| = t)
- `sq := quadratics.bind quadRoots` (complex root pairs, |sq| = 2s where s = |Q|)
- `ι := algebraMap R (Ri R)`

From `hnodup`: `sl + sq` is nodup. Hence:
- `sl.Nodup` (via `linears_nodup` + injectivity of `ι`)
- `sq.Nodup` (via `quadRoots_bind_nodup`)
- `Disjoint sl sq` (from `Multiset.nodup_add`)

## Strategy

### Step 1: Multiset partition

```
(sl + sq) ×ˢ (sl + sq) - (sl + sq).map diag
  = (sl ×ˢ sl - sl.map diag)  -- LL piece
    + (sl ×ˢ sq)                -- LQ piece
    + (sq ×ˢ sl)                -- QL piece
    + (sq ×ˢ sq - sq.map diag)  -- QQ piece
```

Components:
- `multiset_product_add_add` ✓ (already proven): `(sl + sq) ×ˢ (sl + sq) = sl ×ˢ sl + sl ×ˢ sq + sq ×ˢ sl + sq ×ˢ sq`
- `Multiset.map_add`: `(sl + sq).map diag = sl.map diag + sq.map diag`
- Need: `diag_le_product`: `s.map diag ≤ s ×ˢ s` (so subtraction lands properly)
- Use `tsub_add_eq_add_tsub` (or `Multiset.add_sub_assoc`) to redistribute.

Helper: `Multiset.le_iff_count` + `count_product_eq` + `count_diag_map` (from Proposition_4_3 — accessible via Remark_4_4 import).

### Step 2: Product factors

From `Multiset.prod_add` and `Multiset.map_add`:
```
((A + B + C + D).map sub).prod
  = (A.map sub).prod * (B.map sub).prod * (C.map sub).prod * (D.map sub).prod
```

### Step 3: Compute each piece

#### LL piece: `((sl ×ˢ sl - sl.map diag).map sub).prod = ι((-1)^{N_t} · ll²)`

where `ll = ∏_{a < b in linears.toList} (b - a)`.

- `sl = linears.map ι` is nodup (proven).
- `(sl ×ˢ sl - sl.map diag).map sub` is in image of `ι.map` via push-through.
- Need: `(linears.map ι ×ˢ linears.map ι - (linears.map ι).map diag).map sub = (linears ×ˢ linears - linears.map diag).map (ι ∘ sub).map sub` — combine `ι` with the off-diag of `linears` itself.

Hmm need to push ι through ×ˢ:
- `multiset_product_map`: `(s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g)` (exists in Remark_4_4)

So `linears.map ι ×ˢ linears.map ι = (linears ×ˢ linears).map (Prod.map ι ι)`.

And `(linears.map ι).map diag = linears.map (diag ∘ ι) = linears.map (fun a => (ι a, ι a)) = (linears.map (fun a => (a, a))).map (Prod.map ι ι)`.

Subtraction: `multiset_map_sub_of_injective` (exists in Remark_4_4): if `f` injective, `(m - n).map f = m.map f - n.map f`. With `f = Prod.map ι ι` (injective since `ι` is).

So `(linears.map ι ×ˢ linears.map ι - (linears.map ι).map diag)
  = (linears ×ˢ linears - linears.map diag).map (Prod.map ι ι)`.

Then `.map sub` composed with `Prod.map ι ι`: `sub ∘ (Prod.map ι ι) = ι ∘ sub` (since `ι` is a ring hom and preserves subtraction).

So `((sl ×ˢ sl - sl.map diag).map sub).prod
  = ι (((linears ×ˢ linears - linears.map diag).map sub).prod)`.

Now compute `((linears ×ˢ linears - linears.map diag).map sub).prod` over R.

This is `∏ over off-diag of linears of (a - b)` — the "off-diagonal product on R-roots".

Using a list ordering: `linears.toList = [l_1, ..., l_t]`. Then:
- off-diag multiset = `{(l_i, l_j) : i ≠ j}` (since linears nodup).
- Product = `∏_{i ≠ j} (l_i - l_j) = (-1)^{N_t} · (∏_{i < j} (l_j - l_i))² = (-1)^{N_t} · ll²`.

This requires:
- A general lemma: for nodup multiset `m` with `m.toList = [a_1, ..., a_n]`,
  `((m ×ˢ m - m.map diag).map sub).prod = (-1)^{n(n-1)/2} · (∏_{i<j}(a_j - a_i))²`.

Or directly: convert to list and compute.

#### LQ piece: `((sl ×ˢ sq).map sub).prod`

`sl ×ˢ sq = (linears.map ι) ×ˢ (quadratics.bind quadRoots)`
       = `linears.bind (fun y => (quadratics.bind quadRoots).map (Prod.mk (ι y)))`

For each `y ∈ linears`, the contribution is `∏ over cd ∈ quadratics, ∏ over z ∈ quadRoots cd of (ι y - z)`.

For each cd = (c, d), `∏ over z ∈ {ι c + ι d i, ι c - ι d i} of (ι y - z) =
  (ι y - ι c - ι d i) · (ι y - ι c + ι d i) = (ι y - ι c)² + (ι d)² = ι((y-c)² + d²)`.

So for each `(y, cd)`, contribution = `ι((y-c)² + d²)`.

Total LQ = `∏ over (y, cd) ∈ linears × quadratics of ι((y-c)² + d²)`
        = `ι(∏ over (y, cd) of ((y-c)² + d²))`
        = `ι(lq)`.

#### QL piece: `((sq ×ˢ sl).map sub).prod`

By swap symmetry: `sq ×ˢ sl = (sl ×ˢ sq).map Prod.swap`. So `sub ∘ Prod.swap` = `-sub` (since `Prod.swap (a, b) = (b, a)` and `sub (b, a) = b - a = -(a - b)`).

So `((sq ×ˢ sl).map sub).prod = (-1)^{|sq ×ˢ sl|} · ((sl ×ˢ sq).map sub).prod
  = (-1)^{|sl| · |sq|} · LQ
  = (-1)^{t · 2s} · LQ = LQ` (since `t · 2s` is even).

#### QQ_within: contribution from within-pair off-diagonal

For each cd ∈ quadratics, the off-diagonal of `quadRoots cd` has 2 elements `(z, z̄)` and `(z̄, z)`. Product of differences:
- `(z - z̄)(z̄ - z) = -(z - z̄)² = -(2 ι d i)² = -(4 (ι d)² · (-1)) = 4 (ι d)² = ι(4 d²)`.

Aggregated over all cd: `∏ over cd of ι(4 d²) = ι(∏ over cd of 4 d²) = ι(4^|Q| · ∏d²) = ι((2^|Q| · ∏d)²) = ι(qq_within²)`.

Note: `qq_within = 2^|Q| · ∏ d` in our definition.

#### QQ_across: between-pair contributions

For each pair of distinct (c_α, d_α), (c_β, d_β) at distinct positions in quadratics.toList: 8 ordered pairs from `quadRoots cd_α × quadRoots cd_β` and `quadRoots cd_β × quadRoots cd_α`.

Product = `((c_α-c_β)² + (d_α-d_β)²)² · ((c_α-c_β)² + (d_α+d_β)²)²` (computed via conjugate-norm).

Across all unordered pairs: `(qq_across)²` where `qq_across = ∏ over α < β of ((c_β-c_α)² + (d_β-d_α)²) · ((c_β-c_α)² + (d_β+d_α)²)`.

Combined with `ι`: `ι(qq_across²)`.

### Step 4: Combine

Off-diag prod = LL · LQ · QL · QQ_within · QQ_across_part
            = ι((-1)^{N_t} · ll²) · ι(lq) · ι(lq) · ι(qq_within²) · ι(qq_across²)
            = ι((-1)^{N_t} · ll² · lq² · qq_within² · qq_across²)
            = ι((-1)^{N_t} · ω²)

since `ω² = ll² · lq² · qq_within² · qq_across²`.

Wait, but QQ piece is `(QQ_within) · (QQ_across)`. Hmm let me check the actual decomposition.

The QQ piece in the multiset partition is `sq ×ˢ sq - sq.map diag`. This single multiset includes BOTH within-pair contributions and across-pair contributions. Let me recompute its product.

`sq ×ˢ sq - sq.map diag` for sq = ∑ cd ∈ Q quadRoots cd:

Each ordered pair (z, z') with z ≠ z' contributes (z - z'). Counts:
- For (z, z̄) with both in same quadRoots cd: counted once per (z ∈ quadRoots cd, z' ∈ quadRoots cd, z ≠ z'). 2 such pairs per cd.
- For (z, z') with z ∈ quadRoots cd_α, z' ∈ quadRoots cd_β, α ≠ β: 4 pairs per (α, β) ordered = 8 unordered pair contributions, but 4 per ordered.

So QQ piece's product is the product of within-cd off-diag products times across-(cd_α, cd_β) cross products.

OK so QQ = QQ_within · QQ_across_full = ι(qq_within²) · ι(qq_across²) = ι(qq_within² · qq_across²)

Total: LL · LQ · QL · QQ = ι((-1)^{N_t}) · ι(ll²) · ι(lq²) · ι(qq_within²) · ι(qq_across²)
                       = ι((-1)^{N_t} · (ll · lq · qq_within · qq_across)²)
                       = ι((-1)^{N_t} · ω²)

since ω = ll · lq · qq_within · qq_across.

## Order of attack

1. **Diag ≤ product** (helper).
2. **Partition lemma** (structural multiset identity).
3. **Product factoring** (from `Multiset.map_add`, `Multiset.prod_add`).
4. **LL piece**: relate to `R`-side off-diagonal product of `linears`, then express as `(-1)^{N_t} · ll²`.
5. **LQ + QL piece**: combine via the conjugate-pair norm trick.
6. **QQ piece** (within + across combined): partition `sq ×ˢ sq` again by cd-pair source, compute each.
7. **Combine** the four pieces into `ω²` with the `(-1)^{N_t}` sign.

Each step deserves a separate sub-lemma. The hardest is likely Step 4 (LL) due to ordering, and Step 6 (QQ).

Let me start with the simpler pieces and build up.
