import Azurite.BasuPollackRoy.Chapter2.Section2_1.Factorization
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Notation_2_18
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_a_b
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_b_c
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Notation_4_1
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Remark_4_4

/-!
# BPR Proposition 4.5: Sign of the discriminant

**Proposition 4.5 (BPR).** Let `P ∈ R[X]` be monic with `R` real closed, of
degree `p`, with `p` distinct roots in `C = R[i]`. Denote by `t` the number
of roots of `P` in `R`. Then

* `Disc(P) > 0 ↔ t ≡ p (mod 4)`,
* `Disc(P) < 0 ↔ t ≡ p − 2 (mod 4)`.

## Strategy

The BPR-faithful discriminant `disc P : Ri R` (`Section4_1/Notation_4_1`)
is defined as the product-over-roots in the algebraic closure `Ri R = R[i]`.
For `P : R[X]`, this product is conjugation-invariant: the canonical
conjugation `Ri.conj R` permutes the roots of `P` (Section 2.1's
`conj_isRoot_of_map`), and the product over an off-diagonal Cartesian
square is symmetric under any permutation acting by a ring automorphism.
Hence `disc P : Ri R` lies in the image of `algebraMap R (Ri R)`, and we
can extract an R-valued discriminant `discReal P : R`.

To determine the sign of `discReal P`, factor `P` over `R` via BPR
Proposition 2.19 (`Section2_1/Factorization.lean`) as
`P = ∏(X - y_i) · ∏((X - c_j)^2 + d_j^2)` with `t` linear factors (real
roots `y_i`) and `s` irreducible quadratic factors (complex conjugate
pairs `c_j ± i·d_j`). Then in `Ri R` the roots split into `t` reals
`ι(y_i)` and `s` conjugate pairs `ι(c_j) ± ι(d_j) i`. Expanding
`disc P` over this multiset, all factors are positive squares except for
the `s` "self-pairs" `(ι(c_j) + ι(d_j) i, ι(c_j) - ι(d_j) i)`, each
contributing `(2 i d_j)^2 = -4 d_j^2 < 0` (after extracting from the
ordered off-diagonal formula). The product of these `s` factors gives
sign `(-1)^s`, and then `p - t = 2s`, so `s ≡ 0 (mod 2)` ↔ `t ≡ p (mod 4)`.

This file is structured as:

1. `discReal` definition (Choose-based from `disc P : Ri R`).
2. Conjugation invariance of `disc P : Ri R` and the bridge
   `algebraMap R (Ri R) (discReal P) = disc P`.
3. Sign theorem via factorization.
4. BPR Proposition 4.5.
-/

namespace Azurite.BPR.Chapter4

open Polynomial Azurite.BPR Azurite.BPR.Theorem2_11

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

section DiscReal

/-! ## R-valued discriminant via the algebraic closure `Ri R` -/

/-- Real-valued discriminant of `P : R[X]`, extracted from
    `disc P : Ri R` when `disc P` is in the image of `algebraMap R (Ri R)`
    (which holds whenever `P : R[X]`; see `disc_mem_range_algebraMap` below).
    Returns `0` as a junk value when the preimage does not exist. -/
noncomputable def discReal (P : R[X]) : R := by
  classical
  exact if h : ∃ d : R, algebraMap R (Ri R) d = (disc P : Ri R) then
    h.choose else 0

/-- The root multiset of `P : R[X]` in `Ri R` is invariant under
    conjugation: `(P.aroots (Ri R)).map (Ri.conj R) = P.aroots (Ri R)`.

    Reason: conjugation is an `R`-algebra automorphism of `Ri R`, so it
    fixes the coefficients of `P.map (algebraMap R (Ri R))`; combined
    with `Splits.roots_map_of_injective` (`P` splits in `Ri R` since it
    is algebraically closed) the result follows. -/
lemma aroots_map_conj (P : R[X]) :
    (P.aroots (Ri R)).map (Ri.conj R) = P.aroots (Ri R) := by
  classical
  have : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  set ι : R →+* Ri R := algebraMap R (Ri R)
  set σ : Ri R →+* Ri R := (Ri.conj R).toRingHom with hσ_def
  have hinj : Function.Injective σ := Ri.conj_injective R
  have hsplits : (P.map ι).Splits := IsAlgClosed.splits _
  -- `σ` fixes the coefficients of `P.map ι`, since `σ ∘ ι = ι`.
  have hfix : (P.map ι).map σ = P.map ι := by
    rw [Polynomial.map_map]
    congr 1
    ext r
    show σ (ι r) = ι r
    exact (Ri.conj R).commutes r
  -- For a splitting polynomial `f`, `(f.map σ).roots = f.roots.map σ`.
  have hroot := hsplits.roots_map_of_injective hinj
  -- `aroots` unfolds to the roots of the mapped polynomial.
  show ((P.map ι).roots).map σ = (P.map ι).roots
  rw [← hroot, hfix]

omit [IsRealClosed R] in
/-- Pushing `Ri.conj R` through the off-diagonal "all-pairs" multiset:
    if `s : Multiset (Ri R)` is invariant under `Ri.conj`, then so is the
    multiset `(s ×ˢ s - s.map diag).map sub` used in the discriminant
    formula (here `diag a = (a, a)` and `sub (a, b) = a - b`). -/
private lemma offdiag_pairs_map_conj (s : Multiset (Ri R))
    (hs : s.map (Ri.conj R) = s) :
    ((s ×ˢ s - s.map (fun a => (a, a))).map
      (fun ab : Ri R × Ri R => ab.1 - ab.2)).map (Ri.conj R) =
    ((s ×ˢ s - s.map (fun a => (a, a))).map
      (fun ab : Ri R × Ri R => ab.1 - ab.2)) := by
  classical
  set σ : Ri R → Ri R := fun x => (Ri.conj R) x with hσ_def
  have hinj : Function.Injective σ := Ri.conj_injective R
  have hinjP : Function.Injective (Prod.map σ σ) := hinj.prodMap hinj
  -- Combine the two outer maps and re-factor `σ ∘ sub = sub ∘ Prod.map σ σ`.
  rw [Multiset.map_map]
  have hcomp : (σ ∘ fun ab : Ri R × Ri R => ab.1 - ab.2) =
      (fun ab : Ri R × Ri R => ab.1 - ab.2) ∘ Prod.map σ σ := by
    funext ab
    obtain ⟨a, b⟩ := ab
    show (Ri.conj R) (a - b) = (Ri.conj R) a - (Ri.conj R) b
    rw [map_sub]
  rw [hcomp, ← Multiset.map_map]
  -- Now goal: ((s ×ˢ s - s.map diag).map (Prod.map σ σ)).map sub = ((s ×ˢ s - s.map diag).map sub)
  congr 1
  -- Goal: (s ×ˢ s - s.map diag).map (Prod.map σ σ) = s ×ˢ s - s.map diag
  rw [multiset_map_sub_of_injective hinjP]
  congr 1
  · -- (s ×ˢ s).map (Prod.map σ σ) = s ×ˢ s
    rw [← multiset_product_map s s σ σ, hs]
  · -- (s.map diag).map (Prod.map σ σ) = s.map diag
    rw [Multiset.map_map]
    have heq : Prod.map σ σ ∘ (fun a : Ri R => (a, a)) =
        (fun a : Ri R => (a, a)) ∘ σ := by
      funext a; simp [Prod.map]
    rw [heq, ← Multiset.map_map, hs]

/-- **Conjugation invariance of `disc`.** For `P : R[X]` and `R` real
    closed, the C-side discriminant `disc P : Ri R` is fixed by
    conjugation. -/
theorem disc_conj_invariant (P : R[X]) :
    (Ri.conj R) (disc P : Ri R) = (disc P : Ri R) := by
  classical
  unfold disc
  show (Ri.conj R) ((-1 : Ri R) ^ _ *
    (((P.aroots (Ri R)) ×ˢ (P.aroots (Ri R)) -
      (P.aroots (Ri R)).map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod)
    = _
  rw [map_mul, map_pow]
  simp only [map_neg, map_one]
  rw [map_multiset_prod]
  congr 1
  exact congrArg Multiset.prod
    (offdiag_pairs_map_conj (P.aroots (Ri R)) (aroots_map_conj P))

/-- **`disc P : Ri R` is in the image of `algebraMap R (Ri R)`.** For
    `P : R[X]`, conjugation fixes `disc P`, hence by
    `Ri.conj_fixed_mem_range_ordered` the value is real. -/
theorem disc_mem_range_algebraMap (P : R[X]) :
    ∃ d : R, algebraMap R (Ri R) d = (disc P : Ri R) := by
  obtain ⟨d, hd⟩ := Ri.conj_fixed_mem_range_ordered (disc P : Ri R)
    (disc_conj_invariant P)
  exact ⟨d, hd⟩

/-- **Bridge.** `algebraMap R (Ri R) (discReal P) = disc P` for any
    `P : R[X]` over a real closed field `R`. -/
theorem algebraMap_discReal_eq_disc (P : R[X]) :
    algebraMap R (Ri R) (discReal P) = (disc P : Ri R) := by
  classical
  unfold discReal
  rw [dite_eq_left (disc_mem_range_algebraMap P)]
  exact (disc_mem_range_algebraMap P).choose_spec

end DiscReal

section SignTheorem

/-! ## Sign of `discReal` via a real square root of `(-1)^s · disc P`

The classical identity `disc(P) = V²` for a Vandermonde difference
`V = ∏_{i<j} (x_j - x_i)` can be split, using BPR's real-closed
factorisation `P = ∏(X-y) · ∏((X-c)² + d²)`, into four pieces:

* `LL`  -- real-real off-diagonal factors;
* `LQ`  -- real-quadratic cross factors (each contributing `((c-y)²+d²)²`);
* `QQ_within` -- per-pair factors `4 d²` (a square);
* `QQ_across` -- per-pair-pair factors, each a product of two real squares.

Collecting all factors and tracking signs gives the key identity

  `(-1) ^ quadratics.card · disc P = (algebraMap R (Ri R)) (ω ^ 2)`

for the explicit `ω : R` defined by the factorisation data. Setting
`V := (Ri.i R) ^ quadratics.card · algebraMap R (Ri R) ω` then gives a
witness with `V² = disc P`, `conj V = (-1)^s · V`, and `V ≠ 0`.

The case analysis on the parity of `s` (in `sign_discReal_of_factorization`
below) then determines the sign of `discReal P` from the parity of
`quadratics.card`. -/

/-- The factorisation-data "scaled Vandermonde" element `ω ∈ R`, whose
    square scales `disc P` by `(-1) ^ quadratics.card`. Concretely:

    `ω = (∏_{a < b ∈ linears.toList} (b - a))
         · (∏_{y ∈ linears, (c,d) ∈ quadratics} ((c-y)² + d²))
         · (2 ^ s · ∏_{(c,d) ∈ quadratics} d)
         · (∏_{α < β ∈ quadratics.toList} ((c_β-c_α)² + (d_β-d_α)²) ·
                                            ((c_β-c_α)² + (d_β+d_α)²))`.

    Each factor corresponds to one of `LL`, `LQ`, `QQ_within`, `QQ_across`
    in the off-diagonal product decomposition. -/
noncomputable def vandermondeOmega
    (linears : Multiset R) (quadratics : Multiset (R × R)) : R :=
  let ll : R :=
    (linears.toList.tails.flatMap (fun l =>
      match l with
      | [] => []
      | a :: rest => rest.map (fun b => b - a))).prod
  let lq : R :=
    (linears.toList.flatMap (fun y =>
      quadratics.toList.map (fun cd => (cd.1 - y) ^ 2 + cd.2 ^ 2))).prod
  let qq_within : R :=
    (2 : R) ^ quadratics.card * (quadratics.toList.map Prod.snd).prod
  let qq_across : R :=
    (quadratics.toList.tails.flatMap (fun l =>
      match l with
      | [] => []
      | cd_a :: rest => rest.flatMap (fun cd_b =>
          [(cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 - cd_a.2) ^ 2,
           (cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 + cd_a.2) ^ 2]))).prod
  ll * lq * qq_within * qq_across

/-! ### Aroots decomposition

For `P` factoring as `∏ linearFactor · ∏ quadraticFactor` over `R`, the
multiset of roots in `Ri R` decomposes as

  `P.aroots (Ri R) = linears.map ι + quadratics.bind quadRoots`

where `quadRoots (c, d) = {ι c + ι d · i, ι c - ι d · i}` for the
canonical `i ∈ Ri R`. -/

/-- The two roots in `Ri R` of an irreducible quadratic factor over `R`. -/
private noncomputable def quadRoots (cd : R × R) : Multiset (Ri R) :=
  {algebraMap R (Ri R) cd.1 + algebraMap R (Ri R) cd.2 * Ri.i R,
   algebraMap R (Ri R) cd.1 - algebraMap R (Ri R) cd.2 * Ri.i R}

omit [IsRealClosed R] in
/-- The mapped quadratic factor `((X - C c)² + C d²).map ι` factors as
    `(X - C α)(X - C β)` over `Ri R`, where `α = ι c + ι d · i` and
    `β = ι c - ι d · i`. -/
private lemma quadraticFactor_map_eq (cd : R × R) :
    (Factorization.quadraticFactor cd).map (algebraMap R (Ri R)) =
    (X - C (algebraMap R (Ri R) cd.1 +
            algebraMap R (Ri R) cd.2 * Ri.i R)) *
    (X - C (algebraMap R (Ri R) cd.1 -
            algebraMap R (Ri R) cd.2 * Ri.i R)) := by
  unfold Factorization.quadraticFactor
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sub,
             Polynomial.map_X, Polynomial.map_C, map_add, map_sub, map_mul,
             map_pow]
  have hC_i_sq : (C (Ri.i R) : (Ri R)[X])^2 = (-1 : (Ri R)[X]) := by
    rw [show ((C (Ri.i R)) : (Ri R)[X])^2 = C ((Ri.i R)^2) from by simp,
        Ri.i_sq, map_neg, map_one]
  linear_combination C (algebraMap R (Ri R) cd.2)^2 * hC_i_sq

omit [IsRealClosed R] in
/-- The aroots of a `linearFactor a` in `Ri R` is the singleton `{ι a}`. -/
private lemma aroots_linearFactor (a : R) :
    (Factorization.linearFactor a).aroots (Ri R) =
      {algebraMap R (Ri R) a} := by
  unfold Factorization.linearFactor
  exact Polynomial.aroots_X_sub_C a

omit [IsRealClosed R] in
/-- The aroots of a `quadraticFactor (c, d)` in `Ri R` form the doubleton
    `{ι c + ι d · i, ι c - ι d · i}`. -/
private lemma aroots_quadraticFactor (cd : R × R) :
    (Factorization.quadraticFactor cd).aroots (Ri R) = quadRoots cd := by
  classical
  unfold Polynomial.aroots quadRoots
  rw [quadraticFactor_map_eq cd]
  rw [Polynomial.roots_mul (mul_ne_zero
        (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _))]
  rw [Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- `linearFactor a = X - C a` is nonzero. -/
private lemma linearFactor_ne_zero (a : R) :
    Factorization.linearFactor a ≠ 0 := by
  unfold Factorization.linearFactor
  exact Polynomial.X_sub_C_ne_zero a

omit [IsRealClosed R] in
/-- `(linearFactor a).map ι = X - C (ι a)`. -/
private lemma linearFactor_map (a : R) :
    (Factorization.linearFactor a).map (algebraMap R (Ri R)) =
      X - C (algebraMap R (Ri R) a) := by
  unfold Factorization.linearFactor
  simp

omit [IsRealClosed R] in
/-- `quadraticFactor cd` is nonzero. -/
private lemma quadraticFactor_ne_zero (cd : R × R) :
    Factorization.quadraticFactor cd ≠ 0 := by
  intro h
  have hmap : (Factorization.quadraticFactor cd).map (algebraMap R (Ri R)) = 0 := by
    rw [h]; exact Polynomial.map_zero _
  rw [quadraticFactor_map_eq cd] at hmap
  exact mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
    (Polynomial.X_sub_C_ne_zero _) hmap

omit [IsRealClosed R] in
/-- The aroots decomposition for `P` over a real closed `R`. -/
private lemma aroots_decomposition (P : R[X])
    (linears : Multiset R) (quadratics : Multiset (R × R))
    (hfact : P = (linears.map (Factorization.linearFactor (R := R))).prod *
                  (quadratics.map (Factorization.quadraticFactor (R := R))).prod) :
    P.aroots (Ri R) =
      linears.map (algebraMap R (Ri R)) + quadratics.bind quadRoots := by
  classical
  -- Each factor product is nonzero (product of nonzero polynomials in a domain).
  have hlin_prod_ne : (linears.map Factorization.linearFactor).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro h
    rw [Multiset.mem_map] at h
    obtain ⟨a, _, ha⟩ := h
    exact linearFactor_ne_zero a ha
  have hquad_prod_ne : (quadratics.map Factorization.quadraticFactor).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro h
    rw [Multiset.mem_map] at h
    obtain ⟨cd, _, hcd⟩ := h
    exact quadraticFactor_ne_zero cd hcd
  -- Split P.aroots via the factorization.
  rw [hfact, Polynomial.aroots_mul (mul_ne_zero hlin_prod_ne hquad_prod_ne)]
  -- Linear product's aroots = linears.map ι.
  have hlin_aroots : (linears.map Factorization.linearFactor).prod.aroots
        (Ri R) = linears.map (algebraMap R (Ri R)) := by
    unfold Polynomial.aroots
    rw [Polynomial.map_multiset_prod, Polynomial.roots_multiset_prod _ ?_,
        Multiset.map_map, Multiset.bind_map]
    · -- Goal: linears.bind (((map ι) ∘ linearFactor) ·).roots = linears.map ι
      rw [Multiset.bind_congr (g := fun a => {algebraMap R (Ri R) a}) (fun a _ => by
            show (Polynomial.map (algebraMap R (Ri R))
                  (Factorization.linearFactor a)).roots = _
            rw [linearFactor_map a]
            exact Polynomial.roots_X_sub_C _)]
      exact Multiset.bind_singleton linears (algebraMap R (Ri R))
    · intro h
      rw [Multiset.mem_map] at h
      obtain ⟨q, hq, hq0⟩ := h
      rw [Multiset.mem_map] at hq
      obtain ⟨a, _, rfl⟩ := hq
      rw [linearFactor_map] at hq0
      exact Polynomial.X_sub_C_ne_zero _ hq0
  -- Quadratic product's aroots = quadratics.bind quadRoots.
  have hquad_aroots : (quadratics.map Factorization.quadraticFactor).prod.aroots
        (Ri R) = quadratics.bind quadRoots := by
    unfold Polynomial.aroots
    rw [Polynomial.map_multiset_prod, Polynomial.roots_multiset_prod _ ?_,
        Multiset.map_map, Multiset.bind_map]
    · exact Multiset.bind_congr (fun cd _ => aroots_quadraticFactor cd)
    · intro h
      rw [Multiset.mem_map] at h
      obtain ⟨q, hq, hq0⟩ := h
      rw [Multiset.mem_map] at hq
      obtain ⟨cd, _, rfl⟩ := hq
      rw [quadraticFactor_map_eq cd] at hq0
      exact mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
        (Polynomial.X_sub_C_ne_zero _) hq0
  rw [hlin_aroots, hquad_aroots]

omit [IsRealClosed R] in
/-- From the aroots decomposition + nodup, the real-root multiset `linears`
    is nodup. -/
private lemma linears_nodup (P : R[X])
    (linears : Multiset R) (quadratics : Multiset (R × R))
    (hfact : P = (linears.map (Factorization.linearFactor (R := R))).prod *
                  (quadratics.map (Factorization.quadraticFactor (R := R))).prod)
    (hnodup : (P.aroots (Ri R)).Nodup) :
    linears.Nodup := by
  rw [aroots_decomposition P linears quadratics hfact] at hnodup
  have h_map_nd : (linears.map (algebraMap R (Ri R))).Nodup :=
    (Multiset.nodup_add.mp hnodup).1
  exact (Multiset.nodup_map_iff_of_injective
    (RingHom.injective (algebraMap R (Ri R)))).mp h_map_nd

omit [IsRealClosed R] in
/-- From the aroots decomposition + nodup, the conjugate-pair root multiset
    `quadratics.bind quadRoots` is nodup. -/
private lemma quadRoots_bind_nodup (P : R[X])
    (linears : Multiset R) (quadratics : Multiset (R × R))
    (hfact : P = (linears.map (Factorization.linearFactor (R := R))).prod *
                  (quadratics.map (Factorization.quadraticFactor (R := R))).prod)
    (hnodup : (P.aroots (Ri R)).Nodup) :
    (quadratics.bind quadRoots).Nodup := by
  rw [aroots_decomposition P linears quadratics hfact] at hnodup
  exact (Multiset.nodup_add.mp hnodup).2.1

/-- Parity fact: `(t+2s)(t+2s-1)/2 + s + t(t-1)/2` is even. This is the
    arithmetic kernel of the sign computation in `vandermondeOmega_sq_eq`,
    expressing the invariance `C(t+2s, 2) + s ≡ C(t, 2) (mod 2)` for any
    `t, s : ℕ`. Proven by induction on `s`: the base case `s = 0` gives
    `2 · C(t, 2)`, manifestly even; the inductive step relies on
    `C(n+2, 2) = C(n, 2) + 2n + 1`, so each `s ⤳ s+1` step adds
    `2n + 1 + 1 = 2(n + 1)` to the sum, preserving evenness. -/
private lemma vandermondeOmega_parity_aux (t s : ℕ) :
    ((t + 2 * s) * (t + 2 * s - 1) / 2 + s + t * (t - 1) / 2) % 2 = 0 := by
  induction s with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    have hev : Even (t * (t - 1)) := Nat.even_mul_pred_self t
    obtain ⟨k, hk⟩ := hev
    rw [hk, show k + k = 2 * k from by ring]
    rw [Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]
    omega
  | succ s ih =>
    set n := t + 2 * s with hn_def
    have h_prod_succ : (t + 2 * (s + 1)) * (t + 2 * (s + 1) - 1) =
                n * (n - 1) + 2 * (2 * n + 1) := by
      have hLHS_a : t + 2 * (s + 1) = n + 2 := by omega
      rw [hLHS_a]
      rw [show n + 2 - 1 = n + 1 from by omega]
      cases n with
      | zero => simp
      | succ m =>
        rw [show m + 1 - 1 = m from by omega]
        ring
    have h2 : n * (n - 1) % 2 = 0 := by
      rcases Nat.even_mul_pred_self n with ⟨k, hk⟩
      omega
    have h3 : (t + 2 * (s + 1)) * (t + 2 * (s + 1) - 1) % 2 = 0 := by
      rcases Nat.even_mul_pred_self (t + 2 * (s + 1)) with ⟨k, hk⟩
      omega
    omega

/-- **Cartesian product distributes over multiset addition (on both sides).**
    Useful for the 4-way off-diagonal decomposition. -/
private lemma multiset_product_add_add {α : Type*} [DecidableEq α]
    (sl sq : Multiset α) :
    (sl + sq) ×ˢ (sl + sq) = sl ×ˢ sl + sl ×ˢ sq + sq ×ˢ sl + sq ×ˢ sq := by
  show (sl + sq).bind (fun a => (sl + sq).map (Prod.mk a)) = _
  rw [Multiset.add_bind]
  rw [show sl.bind (fun a => (sl + sq).map (Prod.mk a)) =
      sl.bind (fun a => sl.map (Prod.mk a)) +
      sl.bind (fun a => sq.map (Prod.mk a)) from by
    rw [← Multiset.bind_add]
    apply Multiset.bind_congr
    intro a _; rw [Multiset.map_add]]
  rw [show sq.bind (fun a => (sl + sq).map (Prod.mk a)) =
      sq.bind (fun a => sl.map (Prod.mk a)) +
      sq.bind (fun a => sq.map (Prod.mk a)) from by
    rw [← Multiset.bind_add]
    apply Multiset.bind_congr
    intro a _; rw [Multiset.map_add]]
  show sl.bind _ + sl.bind _ + (sq.bind _ + sq.bind _) = _
  abel

/-- **Count of `(a, b)` in `s.map diag`** is 0 when `a ≠ b`. -/
private lemma count_diag_map_off {α : Type*} [DecidableEq α]
    (s : Multiset α) (a b : α) (h : a ≠ b) :
    (s.map (fun y => ((y, y) : α × α))).count (a, b) = 0 := by
  rw [Multiset.count_map, Multiset.card_eq_zero]
  apply Multiset.filter_eq_nil.mpr
  intros x _ hx
  obtain ⟨hax, hbx⟩ := (Prod.mk.injEq a b x x).mp hx
  exact h (hax.trans hbx.symm)

/-- **Diagonal embedding is a sub-multiset of the Cartesian product.**
    `s.map (fun a => (a, a)) ≤ s ×ˢ s`. -/
private lemma diag_le_product {α : Type*} [DecidableEq α]
    (s : Multiset α) :
    s.map (fun a => (a, a)) ≤ s ×ˢ s := by
  rw [Multiset.le_iff_count]
  intro ⟨a, b⟩
  by_cases hab : a = b
  · subst hab
    rw [count_diag_map, count_product_eq]
    nlinarith [Nat.zero_le (s.count a)]
  · rw [count_diag_map_off s a b hab]
    exact Nat.zero_le _

/-- **Off-diagonal multiset partition.** For any two multisets `sl` and `sq`,
    the off-diagonal multiset of `sl + sq` partitions into four pieces:
    the `sl`-off-diagonal, the two cross products, and the `sq`-off-diagonal.
    This identity holds in `ℕ`-counts and follows by `Multiset.ext`. -/
private lemma offdiag_multiset_partition {α : Type*} [DecidableEq α]
    (sl sq : Multiset α) :
    (sl + sq) ×ˢ (sl + sq) - (sl + sq).map (fun a => (a, a)) =
    (sl ×ˢ sl - sl.map (fun a => (a, a))) +
    (sl ×ˢ sq) + (sq ×ˢ sl) +
    (sq ×ˢ sq - sq.map (fun a => (a, a))) := by
  apply Multiset.ext.mpr
  intro ⟨a, b⟩
  rw [Multiset.count_sub, Multiset.count_add, Multiset.count_add,
      Multiset.count_add, Multiset.count_sub, Multiset.count_sub,
      count_product_eq, count_product_eq, count_product_eq,
      count_product_eq, count_product_eq]
  by_cases hab : a = b
  · subst hab
    rw [count_diag_map, count_diag_map, count_diag_map]
    simp only [Multiset.count_add]
    have hc2 : sl.count a ≤ sl.count a * sl.count a := by
      rcases Nat.eq_zero_or_pos (sl.count a) with h | h
      · rw [h]
      · exact Nat.le_mul_of_pos_left _ h
    have hd2 : sq.count a ≤ sq.count a * sq.count a := by
      rcases Nat.eq_zero_or_pos (sq.count a) with h | h
      · rw [h]
      · exact Nat.le_mul_of_pos_left _ h
    have hexpand : (sl.count a + sq.count a) * (sl.count a + sq.count a) =
        sl.count a * sl.count a + sl.count a * sq.count a +
          sq.count a * sl.count a + sq.count a * sq.count a := by ring
    omega
  · rw [count_diag_map_off _ _ _ hab, count_diag_map_off _ _ _ hab,
        count_diag_map_off _ _ _ hab]
    simp only [Multiset.count_add, Nat.sub_zero]
    ring

/-- The `LL` piece of the off-diagonal product. -/
private noncomputable abbrev offdiag_LL (linears : Multiset R) : Ri R :=
  (((linears.map (algebraMap R (Ri R)) ×ˢ linears.map (algebraMap R (Ri R)) -
      (linears.map (algebraMap R (Ri R))).map (fun a => (a, a))).map
      (fun ab : Ri R × Ri R => ab.1 - ab.2)).prod)

/-- The `LQ` piece (real × complex) of the off-diagonal product. -/
private noncomputable abbrev offdiag_LQ
    (linears : Multiset R) (quadratics : Multiset (R × R)) : Ri R :=
  ((linears.map (algebraMap R (Ri R)) ×ˢ quadratics.bind quadRoots).map
      (fun ab : Ri R × Ri R => ab.1 - ab.2)).prod

/-- The `QL` piece (complex × real) of the off-diagonal product. -/
private noncomputable abbrev offdiag_QL
    (linears : Multiset R) (quadratics : Multiset (R × R)) : Ri R :=
  ((quadratics.bind quadRoots ×ˢ linears.map (algebraMap R (Ri R))).map
      (fun ab : Ri R × Ri R => ab.1 - ab.2)).prod

/-- The `QQ` piece (complex × complex off-diagonal) of the off-diagonal product. -/
private noncomputable abbrev offdiag_QQ (quadratics : Multiset (R × R)) : Ri R :=
  ((quadratics.bind quadRoots ×ˢ quadratics.bind quadRoots -
      (quadratics.bind quadRoots).map (fun a => (a, a))).map
      (fun ab : Ri R × Ri R => ab.1 - ab.2)).prod

/-- Arithmetic helper: `n + n(n-1)/2 = (n+1)n/2`. -/
private lemma offdiag_sign_exp_step (n : ℕ) :
    n + n * (n - 1) / 2 = (n + 1) * n / 2 := by
  have h1 : 2 * (n + n * (n - 1) / 2) = 2 * n + n * (n - 1) := by
    rw [Nat.mul_add]; congr 1
    exact Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one n)
  have h2 : 2 * ((n + 1) * n / 2) = (n + 1) * n := by
    have hdvd : 2 ∣ (n + 1) * n := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨(n + 1) * k, by rw [hk]; ring⟩
      · exact ⟨(k + 1) * n, by
          have hodd : n + 1 = 2 * (k + 1) := by omega
          rw [hodd]; ring⟩
    exact Nat.mul_div_cancel' hdvd
  have h3 : 2 * n + n * (n - 1) = (n + 1) * n := by
    cases n with
    | zero => simp
    | succ m =>
      rw [show m + 1 - 1 = m from by omega]
      ring
  omega

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **`R`-side off-diagonal product formula, list version.** Auxiliary
    induction on `l` for `offdiag_R_prod_formula`. -/
private lemma offdiag_R_prod_formula_aux (l : List R) (hl : l.Nodup) :
    (((↑l : Multiset R) ×ˢ (↑l : Multiset R) -
        (↑l : Multiset R).map (fun a => (a, a))).map
      (fun ab : R × R => ab.1 - ab.2)).prod =
    (-1) ^ (l.length * (l.length - 1) / 2) *
      ((l.tails.flatMap (fun m =>
        match m with
        | [] => []
        | a :: rest => rest.map (fun b => b - a))).prod) ^ 2 := by
  induction l with
  | nil =>
    show ((((0 : Multiset R) ×ˢ 0 -
          (0 : Multiset R).map (fun a => (a, a))).map _)).prod = _
    simp
  | cons a l' ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨ha_notin, hl'_nodup⟩ := hl
    have ih' := ih hl'_nodup
    -- Use offdiag_multiset_partition with sl = {a}, sq = ↑l'.
    have hcoe : (↑(a :: l') : Multiset R) = ({a} : Multiset R) + ↑l' := rfl
    rw [hcoe]
    rw [offdiag_multiset_partition ({a} : Multiset R) (↑l' : Multiset R)]
    -- Simplify the singleton ×ˢ {a} pieces.
    rw [show ({a} : Multiset R) ×ˢ ({a} : Multiset R) -
            ({a} : Multiset R).map (fun x => (x, x)) = 0 from by
      show ({(a, a)} : Multiset (R × R)) - ({(a, a)} : Multiset (R × R)) = 0
      exact tsub_self _]
    rw [show ({a} : Multiset R) ×ˢ (↑l' : Multiset R) =
            (↑l' : Multiset R).map (Prod.mk a) from by
      show ({a} : Multiset R).bind
          (fun x => (↑l' : Multiset R).map (Prod.mk x)) = _
      rw [Multiset.singleton_bind]]
    rw [show (↑l' : Multiset R) ×ˢ ({a} : Multiset R) =
            (↑l' : Multiset R).map (fun b => (b, a)) from by
      show (↑l' : Multiset R).bind
          (fun x => ({a} : Multiset R).map (Prod.mk x)) = _
      conv_lhs =>
        rw [show (fun x : R => Multiset.map (Prod.mk x) ({a} : Multiset R)) =
              fun x : R => ({(x, a)} : Multiset (R × R)) from by
            funext x; rfl]
      exact Multiset.bind_singleton _ _]
    rw [zero_add]
    -- Now: (((↑l'.map (Prod.mk a) + ↑l'.map (·, a) +
    --        (↑l' ×ˢ ↑l' - ↑l'.map diag)).map sub).prod = RHS
    rw [Multiset.map_add, Multiset.map_add, Multiset.prod_add, Multiset.prod_add]
    -- Simplify each .map sub piece.
    rw [show Multiset.map (fun ab : R × R => ab.1 - ab.2)
            ((↑l' : Multiset R).map (Prod.mk a)) =
          (↑l' : Multiset R).map (fun b => a - b) from by
      rw [Multiset.map_map]; rfl]
    rw [show Multiset.map (fun ab : R × R => ab.1 - ab.2)
            ((↑l' : Multiset R).map (fun b : R => (b, a))) =
          (↑l' : Multiset R).map (fun b => b - a) from by
      rw [Multiset.map_map]; rfl]
    rw [ih']
    -- Combine cross-pair prods: ∏(a-b)·∏(b-a) = (-1)^|l'|·(∏(b-a))²
    have hpair : (((↑l' : Multiset R)).map (fun b : R => a - b)).prod *
                 (((↑l' : Multiset R)).map (fun b : R => b - a)).prod =
                 (-1 : R) ^ l'.length *
                 ((((↑l' : Multiset R)).map (fun b : R => b - a)).prod) ^ 2 := by
      rw [Multiset.map_coe, Multiset.map_coe, Multiset.prod_coe, Multiset.prod_coe]
      rw [show l'.map (fun b : R => a - b) =
            l'.map (fun b : R => -(b - a)) from by
        apply List.map_congr_left; intro x _; ring]
      rw [show (fun b : R => -(b - a)) =
            Neg.neg ∘ (fun b : R => b - a) from rfl]
      rw [← List.map_map, List.prod_map_neg, List.length_map]
      ring
    -- Algebra: (LHS) = (-1)^|l'| · (l'.map (b-a)).prod² · (-1)^(...) · (...).prod²
    rw [show ((↑l' : Multiset R).map (fun b => a - b)).prod *
            ((↑l' : Multiset R).map (fun b => b - a)).prod *
            ((-1 : R) ^ (l'.length * (l'.length - 1) / 2) *
              ((l'.tails.flatMap (fun m => match m with
                | [] => []
                | a :: rest => rest.map (fun b => b - a))).prod) ^ 2) =
          ((↑l' : Multiset R).map (fun b => a - b)).prod *
            ((↑l' : Multiset R).map (fun b => b - a)).prod *
            (-1 : R) ^ (l'.length * (l'.length - 1) / 2) *
              ((l'.tails.flatMap (fun m => match m with
                | [] => []
                | a :: rest => rest.map (fun b => b - a))).prod) ^ 2 from by ring]
    rw [hpair]
    -- Expand (a :: l').tails.flatMap to factor out the new term.
    rw [show (a :: l').tails.flatMap (fun m : List R => match m with
              | [] => []
              | a :: rest => rest.map (fun b : R => b - a)) =
            l'.map (fun b => b - a) ++
            l'.tails.flatMap (fun m => match m with
              | [] => []
              | a :: rest => rest.map (fun b => b - a)) from by
      show ((a :: l') :: l'.tails).flatMap _ = _
      rw [List.flatMap_cons]]
    rw [List.prod_append]
    -- Connect list prod to multiset prod.
    rw [show (l'.map (fun b : R => b - a)).prod =
          ((↑l' : Multiset R).map (fun b : R => b - a)).prod from by
      rw [Multiset.map_coe, Multiset.prod_coe]]
    -- Sign arithmetic: l'.length + l'.length*(l'.length-1)/2 = (l'.length+1)*l'.length/2
    rw [show (a :: l').length * ((a :: l').length - 1) / 2 =
          l'.length + l'.length * (l'.length - 1) / 2 from by
      show (l'.length + 1) * (l'.length + 1 - 1) / 2 = _
      rw [show l'.length + 1 - 1 = l'.length from by omega]
      rw [show (l'.length + 1) * l'.length = (l'.length + 1) * l'.length from rfl]
      exact (offdiag_sign_exp_step l'.length).symm]
    rw [pow_add]
    ring

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **`R`-side off-diagonal product formula for nodup multisets.** For a
    nodup multiset `linears`, the off-diagonal product equals
    `(-1)^{n(n-1)/2} · ll²` where `n = linears.card` and `ll` is the
    upper-triangular Vandermonde difference of `linears.toList`. -/
private theorem offdiag_R_prod_formula (linears : Multiset R)
    (hnodup_lin : linears.Nodup) :
    ((linears ×ˢ linears - linears.map (fun a => (a, a))).map
      (fun ab : R × R => ab.1 - ab.2)).prod =
    (-1) ^ (linears.card * (linears.card - 1) / 2) *
      ((linears.toList.tails.flatMap (fun l =>
        match l with
        | [] => []
        | a :: rest => rest.map (fun b => b - a))).prod) ^ 2 := by
  have hl_nodup : linears.toList.Nodup := by
    rw [← Multiset.coe_nodup, Multiset.coe_toList]; exact hnodup_lin
  have key := offdiag_R_prod_formula_aux linears.toList hl_nodup
  rw [show (↑linears.toList : Multiset R) = linears from Multiset.coe_toList _,
      Multiset.length_toList] at key
  exact key

omit [IsRealClosed R] in
/-- **LL piece evaluation.** `offdiag_LL linears = ι((-1)^{t(t-1)/2} · ll²)`
    where `t = linears.card`, `ll` is the linears Vandermonde. -/
private theorem offdiag_LL_eq (linears : Multiset R) (_quadratics : Multiset (R × R))
    (hnodup_lin : linears.Nodup) :
    offdiag_LL linears =
      algebraMap R (Ri R) ((-1) ^ (linears.card * (linears.card - 1) / 2) *
        ((linears.toList.tails.flatMap (fun l =>
          match l with
          | [] => []
          | a :: rest => rest.map (fun b => b - a))).prod) ^ 2) := by
  classical
  unfold offdiag_LL
  -- Step 1: Push ι through ×ˢ, diag, sub.
  set ι : R →+* Ri R := algebraMap R (Ri R) with hι_def
  have hι_inj : Function.Injective ι := RingHom.injective ι
  have hprod_map_inj : Function.Injective (Prod.map ι ι) := hι_inj.prodMap hι_inj
  have hpush_prod : linears.map ι ×ˢ linears.map ι =
      (linears ×ˢ linears).map (Prod.map ι ι) :=
    multiset_product_map linears linears ι ι
  have hpush_diag :
      (linears.map ι).map (fun a : Ri R => (a, a)) =
        (linears.map (fun a : R => (a, a))).map (Prod.map ι ι) := by
    rw [Multiset.map_map, Multiset.map_map]
    rfl
  rw [hpush_prod, hpush_diag]
  rw [← multiset_map_sub_of_injective hprod_map_inj]
  rw [Multiset.map_map]
  -- Now: (((linears ×ˢ linears - linears.map diag).map
  --        ((fun ab => ab.1 - ab.2) ∘ Prod.map ι ι)).prod) = RHS
  -- Since (sub ∘ Prod.map ι ι)(a, b) = ι a - ι b = ι (a - b), this is ι ∘ sub.
  rw [show ((fun ab : Ri R × Ri R => ab.1 - ab.2) ∘ Prod.map ι ι) =
        ι ∘ (fun ab : R × R => ab.1 - ab.2) from by
      funext ⟨a, b⟩; show ι a - ι b = ι (a - b); rw [map_sub]]
  rw [← Multiset.map_map]
  -- Now: ((linears ×ˢ linears - linears.map diag).map sub).map ι .prod = RHS
  rw [← map_multiset_prod ι _]
  -- Now: ι (((linears ×ˢ linears - linears.map diag).map sub).prod) = RHS
  congr 1
  -- Use the R-side formula
  exact offdiag_R_prod_formula linears hnodup_lin

omit [IsRealClosed R] in
/-- **LQ piece evaluation.** `offdiag_LQ = ι(lq)` where `lq` is the LQ part
    of `ω`. Each cross-pair `(ι y, z), (ι y, z̄)` for `z = ι c + ι d · i`
    contributes `(ι y - z)(ι y - z̄) = ι((y - c)² + d²)`. -/
private theorem offdiag_LQ_eq (linears : Multiset R) (quadratics : Multiset (R × R)) :
    offdiag_LQ linears quadratics =
      algebraMap R (Ri R)
        ((linears.toList.flatMap (fun y =>
          quadratics.toList.map (fun cd => (cd.1 - y) ^ 2 + cd.2 ^ 2))).prod) := by
  classical
  unfold offdiag_LQ
  -- Step 1: unfold ×ˢ as bind, simplify with simp_only (which descends into
  -- lambda binders).
  show (Multiset.map (fun ab : Ri R × Ri R => ab.1 - ab.2)
        ((linears.map (algebraMap R (Ri R))).bind
          (fun a => (quadratics.bind quadRoots).map (Prod.mk a)))).prod = _
  simp only [Multiset.bind_map, Multiset.map_bind, Multiset.prod_bind,
             Multiset.map_map, Function.comp_def]
  -- Step 2: reduce each per-cd factor to ι((cd.1 - y)² + cd.2²).
  have hcd_reduce : ∀ y : R, ∀ cd : R × R,
      (Multiset.map (fun b => algebraMap R (Ri R) y - b) (quadRoots cd)).prod =
        algebraMap R (Ri R) ((cd.1 - y) ^ 2 + cd.2 ^ 2) := by
    intro y cd
    unfold quadRoots
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
               Multiset.prod_cons, Multiset.prod_singleton]
    have hi_sq : (Ri.i R) ^ 2 = -1 := Ri.i_sq R
    have hexpand : (algebraMap R (Ri R) y -
            (algebraMap R (Ri R) cd.1 + algebraMap R (Ri R) cd.2 * Ri.i R)) *
          (algebraMap R (Ri R) y -
            (algebraMap R (Ri R) cd.1 - algebraMap R (Ri R) cd.2 * Ri.i R)) =
          (algebraMap R (Ri R) y - algebraMap R (Ri R) cd.1) ^ 2 -
            (algebraMap R (Ri R) cd.2) ^ 2 * (Ri.i R) ^ 2 := by ring
    rw [hexpand, hi_sq]
    rw [show (algebraMap R (Ri R) y - algebraMap R (Ri R) cd.1) ^ 2 -
          algebraMap R (Ri R) cd.2 ^ 2 * (-1) =
        algebraMap R (Ri R) ((cd.1 - y) ^ 2 + cd.2 ^ 2) from by
      rw [map_add, map_pow, map_pow, map_sub]; ring]
  -- Step 3: replace each cd-factor in the goal via hcd_reduce.
  conv_lhs =>
    rw [show (fun x : R =>
        (Multiset.map (fun a : R × R =>
          (Multiset.map (fun b => algebraMap R (Ri R) x - b)
            (quadRoots a)).prod) quadratics).prod) =
        (fun y : R =>
        (Multiset.map (fun cd : R × R =>
          algebraMap R (Ri R) ((cd.1 - y) ^ 2 + cd.2 ^ 2)) quadratics).prod) from by
      funext y
      congr 1
      apply Multiset.map_congr rfl
      intro cd _
      exact hcd_reduce y cd]
  -- Step 4: push ι out of inner prod (per y).
  conv_lhs =>
    rw [show (fun y : R =>
        (Multiset.map (fun cd : R × R =>
          algebraMap R (Ri R) ((cd.1 - y) ^ 2 + cd.2 ^ 2)) quadratics).prod) =
        (fun y : R => algebraMap R (Ri R)
          ((Multiset.map (fun cd : R × R => (cd.1 - y) ^ 2 + cd.2 ^ 2)
            quadratics).prod)) from by
      funext y
      rw [show Multiset.map (fun cd : R × R =>
              algebraMap R (Ri R) ((cd.1 - y) ^ 2 + cd.2 ^ 2)) quadratics =
            (Multiset.map (fun cd : R × R => (cd.1 - y) ^ 2 + cd.2 ^ 2)
              quadratics).map (algebraMap R (Ri R)) from by
        rw [Multiset.map_map]; rfl]
      exact (map_multiset_prod (algebraMap R (Ri R)) _).symm]
  -- Step 5: push ι out of outer prod (over linears).
  rw [show (Multiset.map (fun y : R => algebraMap R (Ri R)
            ((Multiset.map (fun cd : R × R => (cd.1 - y) ^ 2 + cd.2 ^ 2)
              quadratics).prod)) linears) =
          (Multiset.map (fun y : R =>
            (Multiset.map (fun cd : R × R => (cd.1 - y) ^ 2 + cd.2 ^ 2)
              quadratics).prod) linears).map (algebraMap R (Ri R)) from by
    rw [Multiset.map_map]; rfl]
  rw [← map_multiset_prod (algebraMap R (Ri R))]
  congr 1
  -- Step 6: bridge multiset version to list version.
  rw [show (linears.toList.flatMap (fun y : R =>
        quadratics.toList.map (fun cd : R × R =>
          (cd.1 - y) ^ 2 + cd.2 ^ 2))).prod =
      (linears.toList.map (fun y : R =>
        (quadratics.toList.map (fun cd : R × R =>
          (cd.1 - y) ^ 2 + cd.2 ^ 2)).prod)).prod from by
    rw [List.flatMap_def, List.prod_flatten, List.map_map]
    rfl]
  conv_lhs =>
    rw [show linears = (↑linears.toList : Multiset R) from
          (Multiset.coe_toList _).symm,
        show quadratics = (↑quadratics.toList : Multiset (R × R)) from
          (Multiset.coe_toList _).symm]
    simp only [Multiset.map_coe, Multiset.prod_coe]

omit [IsRealClosed R] in
/-- **QL piece equals LQ piece.** Since QL is the swap of LQ, the
    sub-product picks up a sign of `(-1)^{t · 2s}` which is always `1`. -/
private theorem offdiag_QL_eq_LQ (linears : Multiset R) (quadratics : Multiset (R × R)) :
    offdiag_QL linears quadratics = offdiag_LQ linears quadratics := by
  classical
  unfold offdiag_QL offdiag_LQ
  -- (sq ×ˢ sl).map sub = (sl ×ˢ sq).map (sub ∘ Prod.swap) = (sl ×ˢ sq).map (-sub)
  rw [← Multiset.map_swap_product (linears.map (algebraMap R (Ri R)))
        (quadratics.bind quadRoots), Multiset.map_map]
  -- Now: ((sl ×ˢ sq).map ((fun ab => ab.1 - ab.2) ∘ Prod.swap)).prod = ...
  -- ((sub ∘ swap)(a, b)) = (b - a) = -(a - b) = -(sub (a, b))
  rw [show ((fun ab : Ri R × Ri R => ab.1 - ab.2) ∘ Prod.swap) =
        fun ab : Ri R × Ri R => -(ab.1 - ab.2) from by
      funext ⟨a, b⟩; simp [Prod.swap]]
  rw [show (fun ab : Ri R × Ri R => -(ab.1 - ab.2)) =
        (fun x => -x) ∘ (fun ab : Ri R × Ri R => ab.1 - ab.2) from rfl]
  rw [← Multiset.map_map, Multiset.prod_map_neg]
  -- Now: (-1)^(card) * ((sl ×ˢ sq).map sub).prod = ((sl ×ˢ sq).map sub).prod
  -- Need: (-1)^(card of (sl ×ˢ sq).map sub) = 1, i.e., its card is even.
  -- card = (linears.map ι).card * (quadratics.bind quadRoots).card = t * (2s) = 2ts. Even.
  rw [Multiset.card_map, Multiset.card_product, Multiset.card_map,
      Multiset.card_bind]
  rw [show ((Multiset.card ∘ quadRoots : R × R → ℕ)) = fun _ => 2 from rfl,
      Multiset.map_const', Multiset.sum_replicate, smul_eq_mul]
  rw [show linears.card * (quadratics.card * 2) =
      2 * (linears.card * quadratics.card) from by ring]
  rw [pow_mul, neg_one_sq, one_pow, one_mul]

omit [IsRealClosed R] in
/-- **Within-pair off-diagonal product.** For a single `cd = (c, d)`,
    the off-diagonal product over `quadRoots cd` equals `ι(4 d²)`. -/
private lemma offdiag_QQ_within_pair (cd : R × R) :
    (((quadRoots cd) ×ˢ (quadRoots cd) - (quadRoots cd).map (fun a => (a, a))).map
      (fun ab : Ri R × Ri R => ab.1 - ab.2)).prod =
    algebraMap R (Ri R) (4 * cd.2 ^ 2) := by
  classical
  unfold quadRoots
  -- quadRoots cd = {ι c + ι d i, ι c - ι d i}; off-diag is two pairs:
  -- (z, z̄) and (z̄, z); product is (z - z̄)(z̄ - z) = -(2 ι d i)² = 4 (ι d)² = ι(4 d²).
  set α : Ri R := algebraMap R (Ri R) cd.1 + algebraMap R (Ri R) cd.2 * Ri.i R
  set β : Ri R := algebraMap R (Ri R) cd.1 - algebraMap R (Ri R) cd.2 * Ri.i R
  show ((({α, β} : Multiset (Ri R)) ×ˢ ({α, β} : Multiset (Ri R)) -
        ({α, β} : Multiset (Ri R)).map (fun a => (a, a))).map
        (fun ab : Ri R × Ri R => ab.1 - ab.2)).prod = _
  -- Split as {α} + {β}.
  rw [show ({α, β} : Multiset (Ri R)) = ({α} : Multiset (Ri R)) + {β} from rfl]
  rw [offdiag_multiset_partition ({α} : Multiset (Ri R)) ({β} : Multiset (Ri R))]
  -- Three singleton diagonal pieces cancel; two cross pieces remain.
  rw [show ({α} : Multiset (Ri R)) ×ˢ ({α} : Multiset (Ri R)) -
        ({α} : Multiset (Ri R)).map (fun a => (a, a)) = 0 from tsub_self _,
      show ({β} : Multiset (Ri R)) ×ˢ ({β} : Multiset (Ri R)) -
        ({β} : Multiset (Ri R)).map (fun a => (a, a)) = 0 from tsub_self _,
      show ({α} : Multiset (Ri R)) ×ˢ ({β} : Multiset (Ri R)) =
        ({(α, β)} : Multiset (Ri R × Ri R)) from rfl,
      show ({β} : Multiset (Ri R)) ×ˢ ({α} : Multiset (Ri R)) =
        ({(β, α)} : Multiset (Ri R × Ri R)) from rfl,
      zero_add, add_zero]
  -- Now: ({(α, β)} + {(β, α)}.map sub).prod = (α - β)(β - α)
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_singleton,
      Multiset.map_singleton, Multiset.prod_singleton, Multiset.prod_singleton]
  -- (α - β)(β - α) = -(α - β)² = -(2 ι d i)² = -(4 (ι d)² · (-1)) = 4 (ι d)² = ι(4 d²)
  have hi_sq : (Ri.i R) ^ 2 = -1 := Ri.i_sq R
  show (α - β) * (β - α) = _
  have hαβ : α - β = 2 * algebraMap R (Ri R) cd.2 * Ri.i R := by
    show (algebraMap R (Ri R) cd.1 + algebraMap R (Ri R) cd.2 * Ri.i R) -
         (algebraMap R (Ri R) cd.1 - algebraMap R (Ri R) cd.2 * Ri.i R) = _
    ring
  rw [show (α - β) * (β - α) = -((α - β) ^ 2) from by ring, hαβ]
  rw [show -(2 * algebraMap R (Ri R) cd.2 * Ri.i R) ^ 2 =
      4 * (algebraMap R (Ri R) cd.2) ^ 2 * (-(Ri.i R) ^ 2) from by ring, hi_sq]
  rw [map_mul, map_pow]
  have h4 : (algebraMap R (Ri R)) 4 = (4 : Ri R) := by rfl
  rw [h4]
  ring

omit [IsRealClosed R] in
/-- **Across-pair off-diagonal product.** For two distinct `cd_a` and `cd_b`,
    the cross product `quadRoots cd_a ×ˢ quadRoots cd_b` has `.map sub.prod`
    equal to `ι(((c_a - c_b)² + (d_a - d_b)²) · ((c_a - c_b)² + (d_a + d_b)²))`. -/
private lemma offdiag_QQ_across_pair (cd_a cd_b : R × R) :
    ((quadRoots cd_a ×ˢ quadRoots cd_b).map (fun ab : Ri R × Ri R => ab.1 - ab.2)).prod =
    algebraMap R (Ri R)
      (((cd_a.1 - cd_b.1) ^ 2 + (cd_a.2 - cd_b.2) ^ 2) *
        ((cd_a.1 - cd_b.1) ^ 2 + (cd_a.2 + cd_b.2) ^ 2)) := by
  classical
  unfold quadRoots
  -- quadRoots cd_a × quadRoots cd_b = 4 ordered pairs. Map sub and product.
  set αa : Ri R := algebraMap R (Ri R) cd_a.1 + algebraMap R (Ri R) cd_a.2 * Ri.i R
  set βa : Ri R := algebraMap R (Ri R) cd_a.1 - algebraMap R (Ri R) cd_a.2 * Ri.i R
  set αb : Ri R := algebraMap R (Ri R) cd_b.1 + algebraMap R (Ri R) cd_b.2 * Ri.i R
  set βb : Ri R := algebraMap R (Ri R) cd_b.1 - algebraMap R (Ri R) cd_b.2 * Ri.i R
  show ((({αa, βa} : Multiset (Ri R)) ×ˢ ({αb, βb} : Multiset (Ri R))).map
        (fun ab : Ri R × Ri R => ab.1 - ab.2)).prod = _
  -- ×ˢ for {αa, βa} × {αb, βb} = αa-elements bound to {αb, βb}.
  rw [show ({αa, βa} : Multiset (Ri R)) ×ˢ ({αb, βb} : Multiset (Ri R)) =
        ({(αa, αb), (αa, βb), (βa, αb), (βa, βb)} : Multiset (Ri R × Ri R)) from by
      show ({αa, βa} : Multiset (Ri R)).bind
            (fun x => ({αb, βb} : Multiset (Ri R)).map (Prod.mk x)) = _
      rfl]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
             Multiset.prod_cons, Multiset.prod_singleton]
  -- Now: (αa - αb)(αa - βb)(βa - αb)(βa - βb) = (·)((·)((·)(·)))
  -- Group conjugate pairs: ((αa - αb)(βa - βb)) · ((αa - βb)(βa - αb))
  -- First = (ι(c_a - c_b))² + (ι(d_a - d_b))²·... = ι((c_a-c_b)² + (d_a-d_b)²)
  -- Second similarly = ι((c_a-c_b)² + (d_a+d_b)²)
  have hi_sq : (Ri.i R) ^ 2 = -1 := Ri.i_sq R
  have hprod1 : (αa - αb) * (βa - βb) =
      algebraMap R (Ri R) ((cd_a.1 - cd_b.1) ^ 2 + (cd_a.2 - cd_b.2) ^ 2) := by
    show ((algebraMap R (Ri R) cd_a.1 + algebraMap R (Ri R) cd_a.2 * Ri.i R) -
          (algebraMap R (Ri R) cd_b.1 + algebraMap R (Ri R) cd_b.2 * Ri.i R)) *
         ((algebraMap R (Ri R) cd_a.1 - algebraMap R (Ri R) cd_a.2 * Ri.i R) -
          (algebraMap R (Ri R) cd_b.1 - algebraMap R (Ri R) cd_b.2 * Ri.i R)) = _
    rw [show algebraMap R (Ri R)
          ((cd_a.1 - cd_b.1) ^ 2 + (cd_a.2 - cd_b.2) ^ 2) =
        (algebraMap R (Ri R) cd_a.1 - algebraMap R (Ri R) cd_b.1) ^ 2 +
        (algebraMap R (Ri R) cd_a.2 - algebraMap R (Ri R) cd_b.2) ^ 2 from by
      rw [map_add, map_pow, map_pow, map_sub, map_sub]]
    linear_combination
      -((algebraMap R (Ri R) cd_a.2 - algebraMap R (Ri R) cd_b.2) ^ 2) * hi_sq
  have hprod2 : (αa - βb) * (βa - αb) =
      algebraMap R (Ri R) ((cd_a.1 - cd_b.1) ^ 2 + (cd_a.2 + cd_b.2) ^ 2) := by
    show ((algebraMap R (Ri R) cd_a.1 + algebraMap R (Ri R) cd_a.2 * Ri.i R) -
          (algebraMap R (Ri R) cd_b.1 - algebraMap R (Ri R) cd_b.2 * Ri.i R)) *
         ((algebraMap R (Ri R) cd_a.1 - algebraMap R (Ri R) cd_a.2 * Ri.i R) -
          (algebraMap R (Ri R) cd_b.1 + algebraMap R (Ri R) cd_b.2 * Ri.i R)) = _
    rw [show algebraMap R (Ri R)
          ((cd_a.1 - cd_b.1) ^ 2 + (cd_a.2 + cd_b.2) ^ 2) =
        (algebraMap R (Ri R) cd_a.1 - algebraMap R (Ri R) cd_b.1) ^ 2 +
        (algebraMap R (Ri R) cd_a.2 + algebraMap R (Ri R) cd_b.2) ^ 2 from by
      rw [map_add, map_pow, map_pow, map_sub, map_add]]
    linear_combination
      -((algebraMap R (Ri R) cd_a.2 + algebraMap R (Ri R) cd_b.2) ^ 2) * hi_sq
  rw [show (αa - αb) * ((αa - βb) * ((βa - αb) * (βa - βb))) =
        ((αa - αb) * (βa - βb)) * ((αa - βb) * (βa - αb)) from by ring]
  rw [hprod1, hprod2, ← map_mul]

/-- Helper: `m ×ˢ (n.bind f) = n.bind (fun a => m ×ˢ f a)`. -/
private lemma multiset_product_bind {α β γ : Type*}
    (m : Multiset α) (n : Multiset γ) (f : γ → Multiset β) :
    m ×ˢ (n.bind f) = n.bind (fun a => m ×ˢ f a) := by
  induction n using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_bind, Multiset.product_add, ih, Multiset.cons_bind]

/-- Helper: `(n.bind f) ×ˢ m = n.bind (fun a => f a ×ˢ m)`. -/
private lemma multiset_bind_product {α β γ : Type*}
    (m : Multiset α) (n : Multiset γ) (f : γ → Multiset β) :
    (n.bind f) ×ˢ m = n.bind (fun a => f a ×ˢ m) := by
  induction n using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_bind, Multiset.add_product, ih, Multiset.cons_bind]

omit [IsRealClosed R] in
/-- Value of `(quadRoots cd ×ˢ X.bind quadRoots).map sub.prod` for any
    multiset `X` of quadratic-pair data, expressed as `ι` of the
    list-level cross-product. -/
private lemma offdiag_QQ_cross_left (cd : R × R) (rest : List (R × R)) :
    ((quadRoots cd ×ˢ (↑rest : Multiset (R × R)).bind quadRoots).map
      (fun ab : Ri R × Ri R => ab.1 - ab.2)).prod =
    algebraMap R (Ri R)
      ((rest.map (fun cd' : R × R =>
        ((cd.1 - cd'.1) ^ 2 + (cd.2 - cd'.2) ^ 2) *
        ((cd.1 - cd'.1) ^ 2 + (cd.2 + cd'.2) ^ 2))).prod) := by
  rw [multiset_product_bind, Multiset.map_bind, Multiset.prod_bind]
  rw [show (fun cd' : R × R =>
          (Multiset.map (fun ab : Ri R × Ri R => ab.1 - ab.2)
            (quadRoots cd ×ˢ quadRoots cd')).prod) =
        fun cd' : R × R =>
          algebraMap R (Ri R)
            (((cd.1 - cd'.1) ^ 2 + (cd.2 - cd'.2) ^ 2) *
              ((cd.1 - cd'.1) ^ 2 + (cd.2 + cd'.2) ^ 2)) from by
    funext cd'; exact offdiag_QQ_across_pair cd cd']
  rw [show (Multiset.map (fun cd' : R × R => algebraMap R (Ri R)
            (((cd.1 - cd'.1) ^ 2 + (cd.2 - cd'.2) ^ 2) *
              ((cd.1 - cd'.1) ^ 2 + (cd.2 + cd'.2) ^ 2))) (↑rest : Multiset _)) =
          (Multiset.map (fun cd' : R × R =>
            ((cd.1 - cd'.1) ^ 2 + (cd.2 - cd'.2) ^ 2) *
              ((cd.1 - cd'.1) ^ 2 + (cd.2 + cd'.2) ^ 2)) (↑rest : Multiset _)).map
            (algebraMap R (Ri R)) from by rw [Multiset.map_map]; rfl]
  rw [← map_multiset_prod]
  rw [Multiset.map_coe, Multiset.prod_coe]

omit [IsRealClosed R] in
/-- Value of `(X.bind quadRoots ×ˢ quadRoots cd).map sub.prod`. Equals
    the left version by the symmetry `(a-b)² = (b-a)²` and
    `(a+b)² = (b+a)²`. -/
private lemma offdiag_QQ_cross_right (cd : R × R) (rest : List (R × R)) :
    (((↑rest : Multiset (R × R)).bind quadRoots ×ˢ quadRoots cd).map
      (fun ab : Ri R × Ri R => ab.1 - ab.2)).prod =
    algebraMap R (Ri R)
      ((rest.map (fun cd' : R × R =>
        ((cd.1 - cd'.1) ^ 2 + (cd.2 - cd'.2) ^ 2) *
        ((cd.1 - cd'.1) ^ 2 + (cd.2 + cd'.2) ^ 2))).prod) := by
  rw [multiset_bind_product, Multiset.map_bind, Multiset.prod_bind]
  rw [show (fun cd' : R × R =>
          (Multiset.map (fun ab : Ri R × Ri R => ab.1 - ab.2)
            (quadRoots cd' ×ˢ quadRoots cd)).prod) =
        fun cd' : R × R =>
          algebraMap R (Ri R)
            (((cd.1 - cd'.1) ^ 2 + (cd.2 - cd'.2) ^ 2) *
              ((cd.1 - cd'.1) ^ 2 + (cd.2 + cd'.2) ^ 2)) from by
    funext cd'
    have h := offdiag_QQ_across_pair cd' cd
    rw [show (((cd'.1 - cd.1) ^ 2 + (cd'.2 - cd.2) ^ 2) *
              ((cd'.1 - cd.1) ^ 2 + (cd'.2 + cd.2) ^ 2)) =
            (((cd.1 - cd'.1) ^ 2 + (cd.2 - cd'.2) ^ 2) *
              ((cd.1 - cd'.1) ^ 2 + (cd.2 + cd'.2) ^ 2)) from by ring] at h
    exact h]
  rw [show (Multiset.map (fun cd' : R × R => algebraMap R (Ri R)
            (((cd.1 - cd'.1) ^ 2 + (cd.2 - cd'.2) ^ 2) *
              ((cd.1 - cd'.1) ^ 2 + (cd.2 + cd'.2) ^ 2))) (↑rest : Multiset _)) =
          (Multiset.map (fun cd' : R × R =>
            ((cd.1 - cd'.1) ^ 2 + (cd.2 - cd'.2) ^ 2) *
              ((cd.1 - cd'.1) ^ 2 + (cd.2 + cd'.2) ^ 2)) (↑rest : Multiset _)).map
            (algebraMap R (Ri R)) from by rw [Multiset.map_map]; rfl]
  rw [← map_multiset_prod]
  rw [Multiset.map_coe, Multiset.prod_coe]

omit [IsRealClosed R] in
/-- **QQ piece evaluation, list version (auxiliary).** List induction
    on `l`. Inductive step uses `offdiag_multiset_partition` with
    `sl = quadRoots cd` and `sq = ↑rest.bind quadRoots`, then
    `offdiag_QQ_within_pair` for the within-piece,
    `offdiag_QQ_cross_left`/`offdiag_QQ_cross_right` for the two cross
    pieces, and IH for the rest-within. -/
private lemma offdiag_QQ_eq_aux (l : List (R × R)) (hq_ne : ∀ pq ∈ l, pq.2 ≠ 0) :
    (((((↑l : Multiset (R × R)).bind quadRoots) ×ˢ
        ((↑l : Multiset (R × R)).bind quadRoots) -
       (((↑l : Multiset (R × R)).bind quadRoots)).map (fun a => (a, a))).map
      (fun ab : Ri R × Ri R => ab.1 - ab.2))).prod =
    algebraMap R (Ri R)
      (((2 : R) ^ l.length * (l.map Prod.snd).prod) ^ 2 *
       (l.tails.flatMap (fun m =>
          match m with
          | [] => []
          | cd_a :: rest => rest.flatMap (fun cd_b =>
              [(cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 - cd_a.2) ^ 2,
               (cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 + cd_a.2) ^ 2]))).prod ^ 2) := by
  classical
  induction l with
  | nil =>
    show (Multiset.map _ (((0 : Multiset (R × R)).bind quadRoots) ×ˢ _ - _)).prod = _
    simp
  | cons cd rest ih =>
    have hrest_ne : ∀ pq ∈ rest, pq.2 ≠ 0 :=
      fun pq hpq => hq_ne pq (List.mem_cons_of_mem _ hpq)
    have ih' := ih hrest_ne
    -- Step 1: decompose the bind.
    have hbind : ((↑(cd :: rest) : Multiset (R × R)).bind quadRoots) =
        quadRoots cd + ((↑rest : Multiset (R × R)).bind quadRoots) := by
      show ((cd ::ₘ ↑rest : Multiset (R × R)).bind quadRoots) = _
      rw [Multiset.cons_bind]
    rw [hbind]
    -- Step 2: apply offdiag_multiset_partition.
    rw [offdiag_multiset_partition (quadRoots cd)
          ((↑rest : Multiset (R × R)).bind quadRoots)]
    -- Step 3: distribute .map sub and .prod over the 4-piece sum.
    rw [Multiset.map_add, Multiset.map_add, Multiset.map_add,
        Multiset.prod_add, Multiset.prod_add, Multiset.prod_add]
    -- Step 4: substitute the four piece evaluations.
    rw [offdiag_QQ_within_pair cd,
        offdiag_QQ_cross_left cd rest,
        offdiag_QQ_cross_right cd rest,
        ih']
    -- Step 5: combine four ι(...) factors into one ι(...).
    rw [← map_mul, ← map_mul, ← map_mul]
    congr 1
    -- Step 6: expand the (cd :: rest).tails.flatMap on the RHS.
    rw [show ((cd :: rest).tails.flatMap (fun m : List (R × R) => match m with
              | [] => []
              | cd_a :: rest => rest.flatMap (fun cd_b =>
                  [(cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 - cd_a.2) ^ 2,
                   (cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 + cd_a.2) ^ 2]))) =
            (rest.flatMap (fun cd_b =>
              [(cd_b.1 - cd.1) ^ 2 + (cd_b.2 - cd.2) ^ 2,
               (cd_b.1 - cd.1) ^ 2 + (cd_b.2 + cd.2) ^ 2])) ++
            (rest.tails.flatMap (fun m => match m with
              | [] => []
              | cd_a :: rest => rest.flatMap (fun cd_b =>
                  [(cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 - cd_a.2) ^ 2,
                   (cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 + cd_a.2) ^ 2]))) from by
      show (((cd :: rest) :: rest.tails).flatMap _) = _
      rw [List.flatMap_cons]]
    rw [List.prod_append]
    -- Step 7: the new flatMap on rest equals the map-based product.
    have hflat_eq : (rest.flatMap (fun cd_b : R × R =>
              [(cd_b.1 - cd.1) ^ 2 + (cd_b.2 - cd.2) ^ 2,
               (cd_b.1 - cd.1) ^ 2 + (cd_b.2 + cd.2) ^ 2])).prod =
            (rest.map (fun cd' : R × R =>
              ((cd.1 - cd'.1) ^ 2 + (cd.2 - cd'.2) ^ 2) *
              ((cd.1 - cd'.1) ^ 2 + (cd.2 + cd'.2) ^ 2))).prod := by
      rw [List.flatMap_def, List.prod_flatten, List.map_map]
      congr 1
      apply List.map_congr_left
      intro x _
      show List.prod [_, _] = _
      rw [List.prod_cons, List.prod_singleton]
      ring
    rw [hflat_eq]
    -- Step 8: pure ring identity.
    rw [show (cd :: rest).length = rest.length + 1 from rfl]
    rw [show (cd :: rest).map Prod.snd = cd.2 :: rest.map Prod.snd from rfl]
    rw [List.prod_cons]
    ring

omit [IsRealClosed R] in
/-- **QQ piece evaluation.** `offdiag_QQ = ι(qq_within² · qq_across²)`,
    reducing to `offdiag_QQ_eq_aux` via the multiset/list bridge. -/
private theorem offdiag_QQ_eq (quadratics : Multiset (R × R))
    (hq_ne : ∀ pq ∈ quadratics, pq.2 ≠ 0)
    (_hnodup_qq : (quadratics.bind quadRoots).Nodup) :
    offdiag_QQ quadratics =
      algebraMap R (Ri R)
        (((2 : R) ^ quadratics.card * (quadratics.toList.map Prod.snd).prod) ^ 2 *
         (quadratics.toList.tails.flatMap (fun l =>
            match l with
            | [] => []
            | cd_a :: rest => rest.flatMap (fun cd_b =>
                [(cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 - cd_a.2) ^ 2,
                 (cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 + cd_a.2) ^ 2]))).prod ^ 2) := by
  have hl_ne : ∀ pq ∈ quadratics.toList, pq.2 ≠ 0 :=
    fun pq hpq => hq_ne pq (Multiset.mem_toList.mp hpq)
  have key := offdiag_QQ_eq_aux quadratics.toList hl_ne
  rw [show (↑quadratics.toList : Multiset (R × R)) = quadratics from
        Multiset.coe_toList _,
      Multiset.length_toList] at key
  exact key

omit [IsRealClosed R] in
/-- **Off-diagonal product expressed via the factorisation data.** Under
    Proposition 4.5's hypotheses, the off-diagonal product
    `((s ×ˢ s - s.map diag).map sub).prod` of `s = P.aroots (Ri R)`
    equals `(algebraMap R (Ri R)) ((-1)^{t(t-1)/2} · ω²)` where
    `t = linears.card`. The proof multiplies the four piece evaluations
    (`offdiag_LL_eq`, `offdiag_LQ_eq`, `offdiag_QL_eq_LQ`, `offdiag_QQ_eq`)
    after applying the multiset partition `offdiag_multiset_partition`. -/
theorem offdiag_prod_eq_omega_sq (P : R[X])
    (linears : Multiset R) (quadratics : Multiset (R × R))
    (hq_ne : ∀ pq ∈ quadratics, pq.2 ≠ 0)
    (hfact : P = (linears.map (Factorization.linearFactor (R := R))).prod *
                  (quadratics.map (Factorization.quadraticFactor (R := R))).prod)
    (hnodup : (P.aroots (Ri R)).Nodup) :
    ((((P.aroots (Ri R)) ×ˢ (P.aroots (Ri R)) -
        (P.aroots (Ri R)).map (fun a => (a, a))).map
        (fun ab : Ri R × Ri R => ab.1 - ab.2))).prod =
      algebraMap R (Ri R)
        ((-1) ^ (linears.card * (linears.card - 1) / 2) *
          (vandermondeOmega linears quadratics) ^ 2) := by
  classical
  -- Set up sl, sq from the aroots decomposition.
  have haroots := aroots_decomposition P linears quadratics hfact
  set sl := linears.map (algebraMap R (Ri R))
  set sq := quadratics.bind quadRoots
  have hnodup_lin : linears.Nodup :=
    linears_nodup P linears quadratics hfact hnodup
  have hnodup_qq : (quadratics.bind quadRoots).Nodup :=
    quadRoots_bind_nodup P linears quadratics hfact hnodup
  -- Rewrite P.aroots (Ri R) = sl + sq, apply the partition.
  rw [haroots, offdiag_multiset_partition sl sq]
  -- Distribute .map sub across the 4-piece sum, then .prod splits multiplicatively.
  rw [Multiset.map_add, Multiset.map_add, Multiset.map_add,
      Multiset.prod_add, Multiset.prod_add, Multiset.prod_add]
  -- Now identify each piece via the helpers.
  show offdiag_LL linears * offdiag_LQ linears quadratics *
       offdiag_QL linears quadratics * offdiag_QQ quadratics = _
  -- First convert QL into another LQ via swap symmetry; then unfold all.
  rw [offdiag_QL_eq_LQ linears quadratics,
      offdiag_LL_eq linears quadratics hnodup_lin,
      offdiag_LQ_eq linears quadratics,
      offdiag_QQ_eq quadratics hq_ne hnodup_qq]
  -- Combine the four ι-images into a single ι of the ω² product.
  rw [← map_mul, ← map_mul, ← map_mul]
  congr 1
  unfold vandermondeOmega
  ring

omit [IsRealClosed R] in
/-- **Key identity for the sign theorem.** For `P : R[X]` admitting the BPR
    real-closed factorisation and with distinct roots in `Ri R`,
    `(-1) ^ quadratics.card · disc P` is the image under `algebraMap R (Ri R)`
    of a square in `R`.

    Reduces to `offdiag_prod_eq_omega_sq` (the multiset partition of the
    off-diagonal product) plus the arithmetic identity `N + N_t + s` even,
    where `N = p(p-1)/2`, `N_t = t(t-1)/2`, and `p = t + 2s` (so
    `N - N_t = s(2t + 2s - 1)` and the odd factor `2t + 2s - 1` reduces
    parity to `s` modulo 2). -/
theorem vandermondeOmega_sq_eq (P : R[X]) (_hP : P.Monic)
    (linears : Multiset R) (quadratics : Multiset (R × R))
    (hq_ne : ∀ pq ∈ quadratics, pq.2 ≠ 0)
    (hfact : P = (linears.map (Factorization.linearFactor (R := R))).prod *
                  (quadratics.map (Factorization.quadraticFactor (R := R))).prod)
    (hnodup : (P.aroots (Ri R)).Nodup) :
    algebraMap R (Ri R) ((vandermondeOmega linears quadratics) ^ 2) =
      (-1) ^ quadratics.card * (disc P : Ri R) := by
  classical
  set t := linears.card with ht_def
  set s := quadratics.card with hs_def
  -- Off-diagonal product equals `ι((-1)^{N_t} · ω²)`.
  have hoff := offdiag_prod_eq_omega_sq P linears quadratics hq_ne hfact hnodup
  -- Number of roots in `Ri R` equals `t + 2s` via the aroots decomposition.
  have hcard : (P.aroots (Ri R)).card = t + 2 * s := by
    rw [aroots_decomposition P linears quadratics hfact, Multiset.card_add,
        Multiset.card_map, Multiset.card_bind]
    rw [show ((Multiset.card ∘ quadRoots : R × R → ℕ)) = fun _ => 2 from rfl,
        Multiset.map_const', Multiset.sum_replicate, smul_eq_mul]
    omega
  -- Unfold `disc` and apply the off-diagonal lemma.
  unfold disc
  show algebraMap R (Ri R) ((vandermondeOmega linears quadratics) ^ 2) =
    (-1) ^ s * ((-1 : Ri R) ^ ((P.aroots (Ri R)).card *
      ((P.aroots (Ri R)).card - 1) / 2) *
      (((P.aroots (Ri R) ×ˢ P.aroots (Ri R) -
        (P.aroots (Ri R)).map (fun a => (a, a))).map
        (fun ab => ab.1 - ab.2))).prod)
  rw [hcard, hoff]
  set N := (t + 2 * s) * (t + 2 * s - 1) / 2 with hN_def
  set N_t := t * (t - 1) / 2 with hNt_def
  -- Combine the sign factors: (-1)^s · (-1)^N · (-1)^{N_t} = 1.
  -- Parity: N - N_t = s(2t + 2s - 1), with (2t+2s-1) odd, so N ≡ N_t + s
  -- (mod 2). Hence N + N_t + s ≡ 2(N_t + s) ≡ 0 (mod 2).
  have hN_parity_even : (N + s + N_t) % 2 = 0 :=
    vandermondeOmega_parity_aux t s
  simp only [map_mul, map_pow, map_neg, map_one]
  rw [← mul_assoc, ← mul_assoc]
  rw [show ((-1 : Ri R) ^ s * (-1) ^ N * (-1) ^ N_t) = 1 from by
        rw [← pow_add, ← pow_add]
        rw [show s + N + N_t = N + s + N_t by ring]
        rcases Nat.even_or_odd (N + s + N_t) with hev | hodd
        · exact hev.neg_one_pow
        · exact absurd (Nat.odd_iff.mp hodd) (by omega)]
  rw [one_mul]

omit [IsRealClosed R] in
/-- **Non-degeneracy of `vandermondeOmega`.** Under the hypotheses of
    Proposition 4.5 (factorisation + nodup roots), the factorisation-data
    element `ω` is non-zero.

    Each factor of `ω` is non-zero because the roots in `Ri R` are
    distinct: this forces all `y_i` distinct, each `d_j ≠ 0` (already
    from `hq_ne`), and each cross-difference `(c_α - c_β)² + (d_α ± d_β)²`
    strictly positive in the real-closed `R`. -/
theorem vandermondeOmega_ne_zero (P : R[X]) (_hP : P.Monic)
    (linears : Multiset R) (quadratics : Multiset (R × R))
    (hq_ne : ∀ pq ∈ quadratics, pq.2 ≠ 0)
    (hfact : P = (linears.map (Factorization.linearFactor (R := R))).prod *
                  (quadratics.map (Factorization.quadraticFactor (R := R))).prod)
    (hnodup : (P.aroots (Ri R)).Nodup) :
    vandermondeOmega linears quadratics ≠ 0 := by
  classical
  unfold vandermondeOmega
  -- `ω = ll * lq * qq_within * qq_across`. Show each factor is nonzero.
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · -- ll ≠ 0: each `b - a` for distinct a, b ∈ linears.toList.
    -- linears.toList.Nodup follows from linears.Nodup via Multiset.Nodup.toList.
    have hlin_nd : linears.Nodup := linears_nodup P linears quadratics hfact hnodup
    have htoList_nd : linears.toList.Nodup := Multiset.coe_nodup.mp
      (by rw [Multiset.coe_toList]; exact hlin_nd)
    apply List.prod_ne_zero
    intro h0
    rw [List.mem_flatMap] at h0
    obtain ⟨t, ht_tails, h0⟩ := h0
    rw [List.mem_tails] at ht_tails
    have ht_nd : t.Nodup := ht_tails.sublist.nodup htoList_nd
    match t, h0 with
    | [], h0 => simp at h0
    | a :: rest, h0 =>
      rw [List.mem_map] at h0
      obtain ⟨b, hb_in, hb_eq⟩ := h0
      have hab : a ≠ b := (List.nodup_cons.mp ht_nd).1 |>.imp fun h => h ▸ hb_in
      exact (sub_ne_zero.mpr (Ne.symm hab)) hb_eq
  · -- lq ≠ 0: each `(c - y)^2 + d^2 > 0` since d ≠ 0.
    apply List.prod_ne_zero
    intro h0
    rw [List.mem_flatMap] at h0
    obtain ⟨y, _, h0⟩ := h0
    rw [List.mem_map] at h0
    obtain ⟨cd, hcd_in, hcd_eq⟩ := h0
    have h1 : 0 ≤ (cd.1 - y) ^ 2 := sq_nonneg _
    have h2 : 0 < cd.2 ^ 2 := sq_pos_of_ne_zero
      (hq_ne cd (Multiset.mem_toList.mp hcd_in))
    linarith [hcd_eq]
  · -- qq_within ≠ 0: 2 ≠ 0 and each d ≠ 0.
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · norm_num
    · apply List.prod_ne_zero
      intro h0
      rw [List.mem_map] at h0
      obtain ⟨cd, hcd_in, hcd_eq⟩ := h0
      exact hq_ne cd (Multiset.mem_toList.mp hcd_in) hcd_eq
  · -- qq_across ≠ 0: Suppose a factor `(c_β-c_α)² + (d_β±d_α)²` is zero.
    -- Then `cd_α` and `cd_β` share a root in `Ri R`, but the structural
    -- nodup of `quadratics.bind quadRoots` (Lemma `quadRoots_bind_nodup`)
    -- forbids this.
    have hbind_nd : (quadratics.bind quadRoots).Nodup :=
      quadRoots_bind_nodup P linears quadratics hfact hnodup
    apply List.prod_ne_zero
    intro h0
    rw [List.mem_flatMap] at h0
    obtain ⟨t, ht_tails, h0⟩ := h0
    rw [List.mem_tails] at ht_tails
    obtain ⟨pre, hpre⟩ := ht_tails  -- pre ++ t = quadratics.toList
    match t, h0, hpre with
    | [], h0, _ => simp at h0
    | cd_a :: rest, h0, hpre =>
      rw [List.mem_flatMap] at h0
      obtain ⟨cd_b, hcd_b_rest, hzero⟩ := h0
      have hzero_eq : 0 = (cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 - cd_a.2) ^ 2 ∨
                      0 = (cd_b.1 - cd_a.1) ^ 2 + (cd_b.2 + cd_a.2) ^ 2 := by
        rcases List.mem_cons.mp hzero with h | h
        · left; exact h
        · right; rwa [List.mem_singleton] at h
      set x : Ri R :=
        algebraMap R (Ri R) cd_a.1 + algebraMap R (Ri R) cd_a.2 * Ri.i R
      have hx_in_a : x ∈ quadRoots cd_a :=
        show x ∈ ({_, _} : Multiset (Ri R)) from Multiset.mem_cons_self _ _
      have hx_in_b : x ∈ quadRoots cd_b := by
        rcases hzero_eq with hzero | hzero
        · -- cd_b = cd_a
          have hp1 : (cd_b.1 - cd_a.1) ^ 2 = 0 := by
            nlinarith [sq_nonneg (cd_b.1 - cd_a.1),
                       sq_nonneg (cd_b.2 - cd_a.2)]
          have hp2 : (cd_b.2 - cd_a.2) ^ 2 = 0 := by
            nlinarith [sq_nonneg (cd_b.1 - cd_a.1),
                       sq_nonneg (cd_b.2 - cd_a.2)]
          have h1' : cd_b.1 = cd_a.1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hp1)
          have h2' : cd_b.2 = cd_a.2 := sub_eq_zero.mp (sq_eq_zero_iff.mp hp2)
          have : cd_b = cd_a := Prod.ext h1' h2'
          rw [this]; exact hx_in_a
        · -- cd_b = (cd_a.1, -cd_a.2)
          have hp1 : (cd_b.1 - cd_a.1) ^ 2 = 0 := by
            nlinarith [sq_nonneg (cd_b.1 - cd_a.1),
                       sq_nonneg (cd_b.2 + cd_a.2)]
          have hp2 : (cd_b.2 + cd_a.2) ^ 2 = 0 := by
            nlinarith [sq_nonneg (cd_b.1 - cd_a.1),
                       sq_nonneg (cd_b.2 + cd_a.2)]
          have h1' : cd_b.1 = cd_a.1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hp1)
          have h2' : cd_b.2 = -cd_a.2 := by
            have hs : cd_b.2 + cd_a.2 = 0 := sq_eq_zero_iff.mp hp2
            linarith
          show x ∈ ({_, _} : Multiset (Ri R))
          refine Multiset.mem_cons_of_mem (Multiset.mem_singleton.mpr ?_)
          rw [h1', h2', map_neg, neg_mul, sub_neg_eq_add]
      -- count x in `quadratics.bind quadRoots` ≥ 2 via cd_a, cd_b
      -- contributions; ≤ 1 from nodup; contradiction.
      have hquad_decomp : quadratics = ↑pre + (cd_a ::ₘ (↑rest : Multiset _)) := by
        rw [← Multiset.coe_toList quadratics, ← hpre]
        rfl
      have hbind_decomp : quadratics.bind quadRoots =
          (↑pre : Multiset _).bind quadRoots +
            (quadRoots cd_a + (↑rest : Multiset _).bind quadRoots) := by
        rw [hquad_decomp, Multiset.add_bind, Multiset.cons_bind]
      have hcd_b_rest_ms : ({cd_b} : Multiset (R × R)) ≤ (↑rest : Multiset _) :=
        Multiset.singleton_le.mpr hcd_b_rest
      have hbind_b_le : quadRoots cd_b ≤ (↑rest : Multiset _).bind quadRoots := by
        have : ({cd_b} : Multiset _).bind quadRoots ≤
            (↑rest : Multiset _).bind quadRoots := by
          obtain ⟨t', ht'⟩ := Multiset.le_iff_exists_add.mp hcd_b_rest_ms
          rw [ht', Multiset.add_bind]
          exact Multiset.le_add_right _ _
        simpa [Multiset.singleton_bind] using this
      have hcount_b : 1 ≤
          Multiset.count x ((↑rest : Multiset _).bind quadRoots) := by
        have := Multiset.count_le_of_le x hbind_b_le
        have hfb : 1 ≤ Multiset.count x (quadRoots cd_b) :=
          Multiset.count_pos.mpr hx_in_b
        omega
      have hcount_a : 1 ≤ Multiset.count x (quadRoots cd_a) :=
        Multiset.count_pos.mpr hx_in_a
      have hcount_ge : 2 ≤ Multiset.count x (quadratics.bind quadRoots) := by
        rw [hbind_decomp, Multiset.count_add, Multiset.count_add]
        omega
      have hcount_le : Multiset.count x (quadratics.bind quadRoots) ≤ 1 :=
        Multiset.nodup_iff_count_le_one.mp hbind_nd x
      omega

omit [IsRealClosed R] in
/-- The Vandermonde "difference" `V` with the conjugation behaviour
    needed for Proposition 4.5. Constructed as `V = i ^ s · ι(ω)`. -/
theorem exists_vandermonde_of_factorization (P : R[X]) (hP : P.Monic)
    (linears : Multiset R) (quadratics : Multiset (R × R))
    (hq_ne : ∀ pq ∈ quadratics, pq.2 ≠ 0)
    (hfact : P = (linears.map (Factorization.linearFactor (R := R))).prod *
                  (quadratics.map (Factorization.quadraticFactor (R := R))).prod)
    (hnodup : (P.aroots (Ri R)).Nodup) :
    ∃ V : Ri R,
      V ^ 2 = (disc P : Ri R) ∧
      (Ri.conj R) V = (-1) ^ quadratics.card * V ∧
      V ≠ 0 := by
  classical
  set ι : R →+* Ri R := algebraMap R (Ri R) with hι_def
  set ω : R := vandermondeOmega linears quadratics with hω_def
  set s : ℕ := quadratics.card with hs_def
  have hω_ne : ω ≠ 0 :=
    vandermondeOmega_ne_zero P hP linears quadratics hq_ne hfact hnodup
  have hkey : ι (ω ^ 2) = (-1) ^ s * (disc P : Ri R) :=
    vandermondeOmega_sq_eq P hP linears quadratics hq_ne hfact hnodup
  -- Define `V := i ^ s · ι ω`.
  refine ⟨(Ri.i R) ^ s * ι ω, ?_, ?_, ?_⟩
  · -- V² = (i^s)² · ι(ω²) = (-1)^s · ι(ω²) = (-1)^s · (-1)^s · disc P = disc P.
    have hi_sq : (Ri.i R) ^ (s * 2) = (-1 : Ri R) ^ s := by
      rw [mul_comm, pow_mul, Ri.i_sq]
    have hsq : ((Ri.i R) ^ s * ι ω) ^ 2 = (-1 : Ri R) ^ s * ι (ω ^ 2) := by
      rw [mul_pow, ← pow_mul, hi_sq, map_pow]
    rw [hsq, hkey]
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  · -- conj V = conj (i^s) · ι ω = (-i)^s · ι ω = (-1)^s · V.
    have hconj_i_pow : (Ri.conj R) ((Ri.i R) ^ s) = (-1) ^ s * (Ri.i R) ^ s := by
      rw [map_pow, Ri.conj_i]
      rw [neg_eq_neg_one_mul, mul_pow]
    rw [map_mul, hconj_i_pow]
    -- conj ι ω = ι ω (since ι ω is in image of ι).
    have hconj_iω : (Ri.conj R) (ι ω) = ι ω := (Ri.conj R).commutes ω
    rw [hconj_iω]
    ring
  · -- V ≠ 0: i^s ≠ 0 and ι ω ≠ 0.
    have hι_inj : Function.Injective ι := RingHom.injective _
    have hi_ne : Ri.i R ≠ 0 := Theorem2_11.Ri.i_ne_zero_ordered
    have hi_pow_ne : (Ri.i R) ^ s ≠ 0 := pow_ne_zero _ hi_ne
    have hιω_ne : ι ω ≠ 0 := by
      intro h
      exact hω_ne (hι_inj (by rw [h, map_zero]))
    exact mul_ne_zero hi_pow_ne hιω_ne

/-- **Sign theorem.** For `P : R[X]` monic over a real closed field `R`
    with `p = deg P` distinct roots in `Ri R`, the sign of `discReal P`
    matches the parity of the number of irreducible quadratic factors
    `s` in BPR's real-closed factorisation of `P`:
    `discReal P > 0 ↔ Even s` and `discReal P < 0 ↔ Odd s`. -/
theorem sign_discReal_of_factorization (P : R[X]) (hP : P.Monic)
    (linears : Multiset R) (quadratics : Multiset (R × R))
    (hq_ne : ∀ pq ∈ quadratics, pq.2 ≠ 0)
    (hfact : P = (linears.map (Factorization.linearFactor (R := R))).prod *
                  (quadratics.map (Factorization.quadraticFactor (R := R))).prod)
    (hnodup : (P.aroots (Ri R)).Nodup) :
    (0 < discReal P ↔ Even quadratics.card) ∧
    (discReal P < 0 ↔ Odd quadratics.card) := by
  classical
  obtain ⟨V, hV_sq, hV_conj, hV_ne⟩ :=
    exists_vandermonde_of_factorization P hP linears quadratics
      hq_ne hfact hnodup
  have hι_inj : Function.Injective (algebraMap R (Ri R)) :=
    RingHom.injective _
  -- Bridge: algebraMap (discReal P) = disc P = V²
  have hdiscReal : algebraMap R (Ri R) (discReal P) = V ^ 2 := by
    rw [hV_sq]; exact algebraMap_discReal_eq_disc P
  -- Case split on parity of quadratics.card.
  rcases Nat.even_or_odd quadratics.card with hs_even | hs_odd
  · -- Even case: conj(V) = V, so V is in image of ι.
    have hconj_V : (Ri.conj R) V = V := by
      rw [hV_conj]
      have hpow : ((-1 : Ri R) ^ (quadratics.card)) = 1 := hs_even.neg_one_pow
      rw [hpow, one_mul]
    obtain ⟨k, hk⟩ := hs_even
    obtain ⟨v, hv⟩ := Ri.conj_fixed_mem_range_ordered V hconj_V
    -- V = ι(v), so V² = ι(v²), hence discReal P = v².
    have hv_ne : v ≠ 0 := by
      intro h; apply hV_ne; rw [← hv, h, map_zero]
    have hdR : discReal P = v ^ 2 := by
      apply hι_inj
      rw [hdiscReal, map_pow, hv]
    refine ⟨?_, ?_⟩
    · refine ⟨fun _ => ⟨k, hk⟩, fun _ => ?_⟩
      rw [hdR]; exact sq_pos_of_ne_zero hv_ne
    · refine ⟨fun hneg => ?_, fun hodd => ?_⟩
      · exfalso
        rw [hdR] at hneg
        exact absurd hneg (not_lt.mpr (sq_nonneg v))
      · exfalso
        have := Nat.not_odd_iff_even.mpr ⟨k, hk⟩
        exact this hodd
  · -- Odd case: conj(V) = -V, so V is purely imaginary.
    have hconj_V : (Ri.conj R) V = -V := by
      rw [hV_conj]
      have hpow : ((-1 : Ri R) ^ (quadratics.card)) = -1 := hs_odd.neg_one_pow
      rw [hpow, neg_one_mul]
    obtain ⟨k, hk⟩ := hs_odd
    obtain ⟨a, b, hab⟩ := Ri.repr_exists V
    -- conj(V) = ι(a) − ι(b)·i; combined with conj(V) = −V we get a = 0.
    have ha_zero : a = 0 := by
      have hconj_eq : algebraMap R (Ri R) a - algebraMap R (Ri R) b * Ri.i R =
          -(algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R) := by
        have hlhs : (Ri.conj R) V =
            algebraMap R (Ri R) a - algebraMap R (Ri R) b * Ri.i R := by
          rw [hab]
          simp only [map_add, map_mul, Ri.conj_algebraMap_ordered, Ri.conj_i,
            mul_neg, sub_eq_add_neg]
        rw [← hlhs, hconj_V, hab]
      -- Simplify: 2·ι(a) = 0 ⇒ ι(a) = 0 ⇒ a = 0.
      have htwo_a_zero : (2 : Ri R) * algebraMap R (Ri R) a = 0 := by
        linear_combination hconj_eq
      have hι_a_zero : algebraMap R (Ri R) a = 0 := by
        have h2ne : (2 : Ri R) ≠ 0 := by
          intro h
          have h2R : algebraMap R (Ri R) (2 : R) = 0 := by
            rw [show algebraMap R (Ri R) (2 : R) = (2 : Ri R) from by rfl]
            exact h
          have : (2 : R) = 0 := hι_inj (by rw [h2R, map_zero])
          norm_num at this
        exact (mul_eq_zero.mp htwo_a_zero).resolve_left h2ne
      have : algebraMap R (Ri R) a = algebraMap R (Ri R) 0 := by
        rw [hι_a_zero, map_zero]
      exact hι_inj this
    -- So V = ι(b)·i; V² = -ι(b²); discReal P = -b².
    have hV_eq : V = algebraMap R (Ri R) b * Ri.i R := by
      rw [hab, ha_zero, map_zero, zero_add]
    have hV_sq' : V ^ 2 = -algebraMap R (Ri R) (b ^ 2) := by
      rw [hV_eq, mul_pow, ← map_pow, Ri.i_sq, mul_neg, mul_one]
    have hb_ne : b ≠ 0 := by
      intro h; apply hV_ne; rw [hV_eq, h, map_zero, zero_mul]
    have hdR : discReal P = -(b ^ 2) := by
      apply hι_inj
      rw [hdiscReal, hV_sq', map_neg]
    refine ⟨?_, ?_⟩
    · refine ⟨fun hpos => ?_, fun heven => ?_⟩
      · exfalso
        rw [hdR] at hpos
        have : -(b ^ 2) ≤ 0 := neg_nonpos_of_nonneg (sq_nonneg b)
        linarith
      · exfalso
        exact (Nat.not_even_iff_odd.mpr ⟨k, hk⟩) heven
    · refine ⟨fun _ => ⟨k, hk⟩, fun _ => ?_⟩
      rw [hdR]
      have hpos : 0 < b ^ 2 := sq_pos_of_ne_zero hb_ne
      linarith

end SignTheorem

section CountingLemmas

/-! ## Counting lemmas relating factorization data to root counts -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The natural degree of a `linearFactor` is `1`. -/
private lemma natDegree_linearFactor (a : R) :
    (Factorization.linearFactor a : R[X]).natDegree = 1 := by
  unfold Factorization.linearFactor
  exact Polynomial.natDegree_X_sub_C a

omit [IsRealClosed R] in
/-- The natural degree of a `quadraticFactor (c, d)` is `2`. -/
private lemma natDegree_quadraticFactor (cd : R × R) :
    (Factorization.quadraticFactor cd : R[X]).natDegree = 2 := by
  unfold Factorization.quadraticFactor
  obtain ⟨c, d⟩ := cd
  compute_degree!

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- `linearFactor a` is monic. -/
private lemma monic_linearFactor (a : R) :
    (Factorization.linearFactor a : R[X]).Monic :=
  Polynomial.monic_X_sub_C a

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- `quadraticFactor (c, d)` is monic. -/
private lemma monic_quadraticFactor (cd : R × R) :
    (Factorization.quadraticFactor cd : R[X]).Monic := by
  unfold Factorization.quadraticFactor
  obtain ⟨c, d⟩ := cd
  have hsq : ((X - C c : R[X]) ^ 2).Monic := (Polynomial.monic_X_sub_C c).pow 2
  have hCd_deg : (C (d ^ 2) : R[X]).degree < ((X - C c : R[X]) ^ 2).degree := by
    have h1 : ((X - C c : R[X]) ^ 2).degree = 2 := by
      rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]; rfl
    rw [h1]
    exact lt_of_le_of_lt (Polynomial.degree_C_le) (by decide)
  exact hsq.add_of_left hCd_deg

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- For a multiset of monic polynomials, the natDegree of the product is the
    sum of their natDegrees. -/
private lemma natDegree_multiset_prod_of_monic
    (m : Multiset R[X]) (hm : ∀ q ∈ m, q.Monic) :
    (m.prod).natDegree = (m.map Polynomial.natDegree).sum := by
  classical
  induction m using Multiset.induction with
  | empty => simp
  | cons p s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    have hp : p.Monic := hm p (Multiset.mem_cons_self _ _)
    have hs : ∀ q ∈ s, q.Monic := fun q hq => hm q (Multiset.mem_cons_of_mem hq)
    have hp_prod : (s.prod).Monic :=
      Multiset.prod_induction _ _ (fun a b ha hb => ha.mul hb) Polynomial.monic_one hs
    rw [Polynomial.Monic.natDegree_mul hp hp_prod, ih hs]

omit [IsRealClosed R] in
/-- Degree formula: for the BPR real-closed factorisation, `natDegree P
    equals `linears.card + 2 · quadratics.card`. -/
lemma natDegree_eq_of_factorization
    (linears : Multiset R) (quadratics : Multiset (R × R))
    (P : R[X])
    (hfact : P = (linears.map (Factorization.linearFactor (R := R))).prod *
                  (quadratics.map (Factorization.quadraticFactor (R := R))).prod) :
    P.natDegree = linears.card + 2 * quadratics.card := by
  classical
  have hlin_monic : ∀ q ∈ (linears.map Factorization.linearFactor), q.Monic := by
    intro q hq
    rw [Multiset.mem_map] at hq
    obtain ⟨a, _, rfl⟩ := hq
    exact monic_linearFactor a
  have hquad_monic : ∀ q ∈ (quadratics.map Factorization.quadraticFactor),
      q.Monic := by
    intro q hq
    rw [Multiset.mem_map] at hq
    obtain ⟨cd, _, rfl⟩ := hq
    exact monic_quadraticFactor cd
  have hlin_prod_monic :
      ((linears.map Factorization.linearFactor).prod : R[X]).Monic :=
    Multiset.prod_induction _ _ (fun a b ha hb => ha.mul hb)
      Polynomial.monic_one hlin_monic
  have hquad_prod_monic :
      ((quadratics.map Factorization.quadraticFactor).prod : R[X]).Monic :=
    Multiset.prod_induction _ _ (fun a b ha hb => ha.mul hb)
      Polynomial.monic_one hquad_monic
  rw [hfact, Polynomial.Monic.natDegree_mul hlin_prod_monic hquad_prod_monic,
      natDegree_multiset_prod_of_monic _ hlin_monic,
      natDegree_multiset_prod_of_monic _ hquad_monic,
      Multiset.map_map, Multiset.map_map]
  have h1 : (linears.map (Polynomial.natDegree ∘
        (Factorization.linearFactor (R := R)))).sum = linears.card := by
    have heq : (Polynomial.natDegree ∘ (Factorization.linearFactor (R := R))) =
        fun _ => 1 := by
      funext a; exact natDegree_linearFactor a
    rw [heq, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
  have h2 : (quadratics.map (Polynomial.natDegree ∘
        (Factorization.quadraticFactor (R := R)))).sum = 2 * quadratics.card := by
    have heq : (Polynomial.natDegree ∘ (Factorization.quadraticFactor (R := R))) =
        fun _ => 2 := by
      funext cd; exact natDegree_quadraticFactor cd
    rw [heq, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_comm]
  rw [h1, h2]

end CountingLemmas

section Proposition45

/-! ## BPR Proposition 4.5 -/

omit [IsRealClosed R] in
/-- The quadratic factor `(X - C c)² + C (d²)` has no roots in `R` when
    `d ≠ 0`: evaluating gives `(x - c)² + d² > 0` in the real closed `R`. -/
private lemma roots_quadraticFactor_eq_zero (cd : R × R) (hd : cd.2 ≠ 0) :
    (Factorization.quadraticFactor cd).roots = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro x hx
  have hnz : Factorization.quadraticFactor cd ≠ 0 :=
    (monic_quadraticFactor cd).ne_zero
  rw [Polynomial.mem_roots hnz] at hx
  unfold Polynomial.IsRoot Factorization.quadraticFactor at hx
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
             Polynomial.eval_X, Polynomial.eval_C] at hx
  have h1 : 0 ≤ (x - cd.1) ^ 2 := sq_nonneg _
  have h2 : 0 < cd.2 ^ 2 := sq_pos_of_ne_zero hd
  linarith

/-- Bind a function returning `0` on every element of a multiset gives `0`. -/
private lemma multiset_bind_eq_zero
    {α β : Type*} (m : Multiset α) (f : α → Multiset β)
    (h : ∀ a ∈ m, f a = 0) : m.bind f = 0 := by
  induction m using Multiset.induction with
  | empty => rfl
  | cons a s ih =>
    rw [Multiset.cons_bind, h a (Multiset.mem_cons_self _ _), zero_add]
    exact ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))

omit [IsRealClosed R] in
/-- For the BPR real-closed factorisation of a monic `P`, the `R`-side root
    multiset `P.roots` coincides with `linears`. -/
private lemma roots_eq_linears_of_factorization
    (P : R[X]) (linears : Multiset R) (quadratics : Multiset (R × R))
    (hq_ne : ∀ pq ∈ quadratics, pq.2 ≠ 0)
    (hfact : P = (linears.map (Factorization.linearFactor (R := R))).prod *
                  (quadratics.map (Factorization.quadraticFactor (R := R))).prod) :
    P.roots = linears := by
  classical
  have hlin_monic : ∀ q ∈ (linears.map Factorization.linearFactor), q.Monic := by
    intro q hq
    rw [Multiset.mem_map] at hq
    obtain ⟨a, _, rfl⟩ := hq
    exact monic_linearFactor a
  have hquad_monic : ∀ q ∈ (quadratics.map Factorization.quadraticFactor),
      q.Monic := by
    intro q hq
    rw [Multiset.mem_map] at hq
    obtain ⟨cd, _, rfl⟩ := hq
    exact monic_quadraticFactor cd
  have hlin_prod_monic : (linears.map Factorization.linearFactor).prod.Monic :=
    Multiset.prod_induction _ _ (fun _ _ => Polynomial.Monic.mul)
      Polynomial.monic_one hlin_monic
  have hquad_prod_monic :
      (quadratics.map Factorization.quadraticFactor).prod.Monic :=
    Multiset.prod_induction _ _ (fun _ _ => Polynomial.Monic.mul)
      Polynomial.monic_one hquad_monic
  rw [hfact, Polynomial.roots_mul
    (mul_ne_zero hlin_prod_monic.ne_zero hquad_prod_monic.ne_zero)]
  -- Linear product: roots = linears.
  have hlin_roots : (linears.map Factorization.linearFactor).prod.roots =
      linears := by
    rw [Polynomial.roots_multiset_prod _ ?_, Multiset.bind_map]
    · have hcomp : (fun a : R => (Factorization.linearFactor a).roots) =
          fun a => {a} := by
        funext a
        unfold Factorization.linearFactor
        exact Polynomial.roots_X_sub_C a
      rw [hcomp]
      have := Multiset.bind_singleton linears id
      simp at this
      exact this
    · intro h
      rw [Multiset.mem_map] at h
      obtain ⟨a, _, ha⟩ := h
      exact (monic_linearFactor a).ne_zero ha
  -- Quadratic product: roots = 0.
  have hquad_roots : (quadratics.map Factorization.quadraticFactor).prod.roots
      = 0 := by
    rw [Polynomial.roots_multiset_prod _ ?_, Multiset.bind_map]
    · exact multiset_bind_eq_zero _ _ (fun cd hcd =>
        roots_quadraticFactor_eq_zero cd (hq_ne cd hcd))
    · intro h
      rw [Multiset.mem_map] at h
      obtain ⟨cd, _, hcd⟩ := h
      exact (monic_quadraticFactor cd).ne_zero hcd
  rw [hlin_roots, hquad_roots, add_zero]

/-- **BPR Proposition 4.5 (factorisation form).** Let `R` be a real closed
    field and `P : R[X]` a monic polynomial of degree `p` with `p` distinct
    roots in `Ri R`. If `P` factors as
    `(linears.map linearFactor).prod * (quadratics.map quadraticFactor).prod`
    (BPR's real-closed factorisation; cf. `Section2_1.Factorization`), with
    `t = linears.card` and `s = quadratics.card`, then:

    * `0 < discReal P ↔ t ≡ p (mod 4)`,
    * `discReal P < 0 ↔ t + 2 ≡ p (mod 4)`.

    Reformulated: the sign of `discReal P` is `(-1)^s`, where `p - t = 2s`. -/
theorem proposition_4_5_of_factorization (P : R[X]) (hP : P.Monic)
    (linears : Multiset R) (quadratics : Multiset (R × R))
    (hq_ne : ∀ pq ∈ quadratics, pq.2 ≠ 0)
    (hfact : P = (linears.map (Factorization.linearFactor (R := R))).prod *
                  (quadratics.map (Factorization.quadraticFactor (R := R))).prod)
    (hnodup : (P.aroots (Ri R)).Nodup) :
    (0 < discReal P ↔ linears.card ≡ P.natDegree [MOD 4]) ∧
    (discReal P < 0 ↔ linears.card + 2 ≡ P.natDegree [MOD 4]) := by
  obtain ⟨hsign_pos, hsign_neg⟩ :=
    sign_discReal_of_factorization P hP linears quadratics hq_ne hfact hnodup
  have hdeg : P.natDegree = linears.card + 2 * quadratics.card :=
    natDegree_eq_of_factorization linears quadratics P hfact
  -- Even quadratics.card ↔ linears.card ≡ P.natDegree (mod 4)
  -- Odd quadratics.card ↔ linears.card + 2 ≡ P.natDegree (mod 4)
  have hmod_even_iff : Even quadratics.card ↔
      linears.card ≡ P.natDegree [MOD 4] := by
    rw [hdeg, Nat.ModEq]
    constructor
    · rintro ⟨k, hk⟩
      have : 2 * quadratics.card = 4 * k := by omega
      omega
    · intro hmod
      refine ⟨quadratics.card / 2, ?_⟩
      have : quadratics.card % 2 = 0 := by omega
      omega
  have hmod_odd_iff : Odd quadratics.card ↔
      linears.card + 2 ≡ P.natDegree [MOD 4] := by
    rw [hdeg, Nat.ModEq]
    constructor
    · rintro ⟨k, hk⟩
      omega
    · intro hmod
      refine ⟨quadratics.card / 2, ?_⟩
      have : quadratics.card % 2 = 1 := by omega
      omega
  exact ⟨hsign_pos.trans hmod_even_iff, hsign_neg.trans hmod_odd_iff⟩

/-- **BPR Proposition 4.5.** Let `R` be a real closed field and `P : R[X]`
    a monic polynomial of degree `p` with `p` distinct roots in `Ri R`.
    Writing `t = P.roots.card` for the number of roots of `P` in `R`:

    * `0 < discReal P ↔ t ≡ p (mod 4)`,
    * `discReal P < 0 ↔ t + 2 ≡ p (mod 4)`.

    This is the BPR-faithful form: only the monic + nodup-in-`Ri R`
    hypotheses are needed; the BPR real-closed factorisation is obtained
    internally via `Factorization.exists_factorization`, and the number
    of `R`-roots `t` matches the count of linear factors. -/
theorem proposition_4_5 (P : R[X]) (hP : P.Monic)
    (hnodup : (P.aroots (Ri R)).Nodup) :
    (0 < discReal P ↔ P.roots.card ≡ P.natDegree [MOD 4]) ∧
    (discReal P < 0 ↔ P.roots.card + 2 ≡ P.natDegree [MOD 4]) := by
  classical
  obtain ⟨linears, quadratics, hq_ne, hfact⟩ :=
    Factorization.exists_factorization P
  -- Use `hP : P.Monic` to remove the leading-coefficient factor.
  have hlc : Polynomial.C P.leadingCoeff = (1 : R[X]) := by rw [hP, map_one]
  rw [hlc, one_mul] at hfact
  -- Identify `P.roots` with `linears`.
  have hroots : P.roots = linears :=
    roots_eq_linears_of_factorization P linears quadratics hq_ne hfact
  rw [hroots]
  exact proposition_4_5_of_factorization P hP linears quadratics hq_ne hfact
    hnodup

end Proposition45

end Azurite.BPR.Chapter4
