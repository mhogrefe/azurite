/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_1.Notation_4_1

/-!
# BPR Subdiscriminant

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

For a (not necessarily monic) polynomial `P = a_p X^p + ⋯ + a_0 : K[X]`
with roots `x_1, …, x_p` in `C` (counted with multiplicity), BPR defines
the **`(p-k)`-subdiscriminant** for `1 ≤ k ≤ p` by

  `sDisc_{p-k}(P) = a_p^{2k-2} · sDisc_{p-k}(P / a_p)`
                 = `a_p^{2k-2} · ∑_{I ⊆ {1,…,p}, #I = k}
                                    ∏_{(j, ℓ) ∈ I, ℓ > j} (x_j − x_ℓ)^2`.

For `k = p` the unique subset `I = {1, …, p}` recovers `Disc(P)`; for `k = 1`
each singleton contributes the empty product `1`, so the formula gives
`sDisc_{p-1}(P) = p` (the leading factor `a_p^{0}` is `1` for any `P`).

The Lean definition is indexed by the BPR subscript `j` (so `sDisc P j`
corresponds to `sDisc_j(P)`) and uses the multiset-friendly symmetric form

  `a_p^{2k-2} · (-1)^{k(k-1)/2} ·
     ∑_{t ≤ s, t.card = k} ∏_{(a, b) ∈ (t ×ˢ t) \ Δ}(a − b)`,

where `s = P.aroots C` and `k = p − j`. As in `disc`, the off-diagonal
multiset product `∏_{i ≠ j}(x_i − x_j)` and `(-1)^{k(k-1)/2}` together
reproduce the squared product `∏_{i > j}(x_i − x_j)^2`, and the
sub-multiset sum reflects the BPR index sum. The leading coefficient
factor `a_p^{2k-2}` uses Nat subtraction (saturating at `0` when
`k = 0`); for the BPR range `1 ≤ k ≤ p` the exponent agrees with
`2k - 2`. Specialising at `j = 0` and `P` monic recovers `disc P`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {K : Type*} [Field K] {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

open Classical in
/-- **BPR Subdiscriminant** (unnumbered definition, §4.1). For
    `P = a_p X^p + ⋯ + a_0 : K[X]` (not necessarily monic) with roots
    `x_1, …, x_p` in `C` and `1 ≤ k ≤ p`, the `(p-k)`-subdiscriminant is
    `sDisc_{p-k}(P) = a_p^{2k-2} · ∑_{I ⊆ {1,…,p}, #I = k}
                                    ∏_{(j, ℓ) ∈ I, ℓ > j} (x_j − x_ℓ)^2`.

    Indexed here by the BPR subscript `j`, so `sDisc P j = sDisc_j(P)`. With
    `s := P.aroots C` and `k := s.card − j`, the symmetric reformulation
    `∏_{i > j}(x_i − x_j)^2 = (-1)^{k(k-1)/2} · ∏_{i ≠ j}(x_i − x_j)` gives
    `sDisc P j = (algebraMap K C P.leadingCoeff)^(2k - 2) ·
                  (-1)^{k(k-1)/2} ·
                  ∑_{t ≤ s, t.card = k}
                    ∏_{(a, b) ∈ (t ×ˢ t) \ Δ}(a − b)`. -/
noncomputable def sDisc (P : K[X]) (j : ℕ) : C :=
  algebraMap K C P.leadingCoeff ^ (2 * ((P.aroots C).card - j) - 2) *
    ((-1 : C) ^ (((P.aroots C).card - j) * ((P.aroots C).card - j - 1) / 2) *
      (((P.aroots C).powersetCard ((P.aroots C).card - j)).map (fun t =>
        ((t ×ˢ t - t.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod)).sum)

omit [IsAlgClosed C] in
/-- **BPR unnumbered corollary** (monic case): `sDisc_0(P) = Disc(P)` when
    `P` is monic. At `j = 0` the only sub-multiset of size `k = p` is `s`
    itself, so the sub-multiset sum collapses to the off-diagonal product
    defining `disc P`; the leading coefficient factor
    `a_p^{2p-2} = 1^{2p-2} = 1` for monic `P`. -/
lemma sDisc_zero_eq_disc (P : K[X]) (hMonic : P.Monic) :
    (sDisc P 0 : C) = disc P := by
  classical
  unfold sDisc disc
  simp [Multiset.powersetCard_self, hMonic.leadingCoeff]

omit [IsAlgClosed C] in
/-- **BPR unnumbered corollary**: `sDisc_{p-1}(P) = p` for a polynomial of
    degree `p ≥ 1`. The leading coefficient factor `a_p^{2·1-2} = a_p^0 = 1`,
    each `k = 1` sub-multiset contributes the empty off-diagonal product
    `1`, and there are `p` such sub-multisets. -/
lemma sDisc_card_pred_eq (P : K[X]) (h : 0 < (P.aroots C).card) :
    (sDisc P ((P.aroots C).card - 1) : C) = ((P.aroots C).card : C) := by
  classical
  set s := P.aroots C with hs_def
  have hk : s.card - (s.card - 1) = 1 := by omega
  unfold sDisc
  rw [← hs_def, hk]
  simp only [show 2 * 1 - 2 = 0 from rfl, pow_zero, one_mul,
             Nat.zero_div]
  -- Each 1-element sub-multiset has empty off-diagonal product = 1.
  have hmap :
      (s.powersetCard 1).map (fun t : Multiset C =>
        ((t ×ˢ t - t.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod) =
      Multiset.replicate (s.powersetCard 1).card (1 : C) := by
    rw [← Multiset.map_const]
    apply Multiset.map_congr rfl
    intro t ht
    rw [Multiset.mem_powersetCard] at ht
    obtain ⟨_, hcard⟩ := ht
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard
    subst ha
    simp [Multiset.product_singleton]
  rw [hmap, Multiset.sum_replicate, Multiset.card_powersetCard,
      Nat.choose_one_right, nsmul_eq_mul, mul_one]

end Azurite.BPR.Chapter4
