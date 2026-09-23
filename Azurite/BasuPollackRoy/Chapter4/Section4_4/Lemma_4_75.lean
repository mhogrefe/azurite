/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Field.Basic

/-!
# BPR Lemma 4.75

If a polynomial `B(Z₁, …, Z_k) ∈ K[Z₁, …, Z_k]` is not identically zero and has (total) degree
`d`, there are elements `(z₁, …, z_k) ∈ {0, …, d}^k` such that `B(z₁, …, z_k)` is a non-zero
element of `K`.

The proof requires the elements `0, …, d` to be distinct in `K` (otherwise a degree-`d`
polynomial could vanish on all of `{0, …, d}`, e.g. `X(X-1)` over `𝔽₂`), so we work over a
field of characteristic zero — the setting of real algebraic geometry. Rather than the
induction of BPR, we read it off Mathlib's Schwartz–Zippel bound
(`MvPolynomial.schwartz_zippel_totalDegree`): the proportion of zeros of a nonzero polynomial in
the box `{0, …, d}^k` is at most `d / (d + 1) < 1`, so some point of the box is a non-zero.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K] [CharZero K]

/-- **BPR Lemma 4.75.** A nonzero polynomial `B ∈ K[Z₁, …, Z_k]` of total degree `d` takes a
nonzero value at some point `(z₁, …, z_k) ∈ {0, …, d}^k` (with `K` of characteristic zero). -/
theorem lemma_4_75 (B : MvPolynomial (Fin k) K) (hB : B ≠ 0) :
    ∃ z : Fin k → K, (∀ i, ∃ m : ℕ, m ≤ B.totalDegree ∧ z i = (m : K)) ∧
      MvPolynomial.eval z B ≠ 0 := by
  classical
  set S : Finset K := (Finset.range (B.totalDegree + 1)).image (Nat.cast) with hS
  have hScard : S.card = B.totalDegree + 1 := by
    rw [hS, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  -- Schwartz–Zippel: the proportion of zeros in the box is at most `d / (d + 1) < 1`.
  have hSZ := schwartz_zippel_totalDegree hB S
  rw [hScard] at hSZ
  set box := Fintype.piFinset (fun _ : Fin k => S) with hbox
  have hboxcard : box.card = (B.totalDegree + 1) ^ k := by
    rw [hbox, Fintype.card_piFinset]
    simp [hScard]
  have hd1 : (B.totalDegree : ℚ≥0) / ((B.totalDegree + 1 : ℕ) : ℚ≥0) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast Nat.lt_succ_self B.totalDegree
  have hZlt1 := lt_of_le_of_lt hSZ hd1
  rw [div_lt_one (by positivity)] at hZlt1
  have hlt : (box.filter (fun f => MvPolynomial.eval f B = 0)).card < (B.totalDegree + 1) ^ k := by
    exact_mod_cast hZlt1
  -- Hence the box contains a point at which `B` does not vanish.
  have hne : (box.filter (fun f => ¬ MvPolynomial.eval f B = 0)).Nonempty := by
    rw [← Finset.card_pos]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := box) (p := fun f => MvPolynomial.eval f B = 0)
    omega
  obtain ⟨f, hf⟩ := hne
  rw [Finset.mem_filter] at hf
  refine ⟨f, fun i => ?_, hf.2⟩
  have hfi : f i ∈ S := Fintype.mem_piFinset.mp hf.1 i
  rw [hS, Finset.mem_image] at hfi
  obtain ⟨m, hm, hmf⟩ := hfi
  rw [Finset.mem_range] at hm
  exact ⟨m, by omega, hmf.symm⟩

end Azurite.BPR.Chapter4
