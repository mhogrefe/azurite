/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.ThomEncodingTransfer

/-! # Root correspondence between two real closures (analytic heart)

For an ordered field `F` with two order-preserving embeddings `ι : F → R`,
`τ : F → R'` into real closed (here: IVP) fields, and `p ∈ F[X]` with a root
`α ∈ R`:

* `exists_unique_thom_root` — there is a **unique** `β ∈ R'` carrying `α`'s exact
  Thom encoding (existence by `derReali_nonempty_transfer`, uniqueness by
  `proposition_2_28_part1`);
* `sign_preserved` — for **every** `q ∈ F[X]`, `sign(q(α)) = sign(ψq(β))`.

The second statement says the assignment `α ↦ β` preserves all sign data, hence
the field embedding `F(α) → R'`, `α ↦ β` is order-preserving. This is the
analytic core of the Artin–Schreier embedding extension; the remaining work is
the algebraic construction of the embedding and the Zorn extension.
-/

open scoped Polynomial

namespace Azurite.BPR

open _root_.Polynomial Azurite.BPR.Proposition2_27 Azurite.BPR.Proposition2_28

/-- The Thom encoding of `α` with respect to `P`: the sign of each iterated
derivative of `P` at `α`. -/
noncomputable def thomEnc {R : Type*} [Field R] [LinearOrder R] (P : R[X]) (α : R) :
    ℕ → SignType :=
  fun i => SignType.sign (((⇑derivative)^[i] P).eval α)

variable {E R R' : Type*} [Field E] [Field R] [Field R']

/-- `map φ` commutes with appending one polynomial (`Fin.snoc`) to a family. -/
lemma map_comp_snoc {n : ℕ} (φ : E →+* R) (L : Fin n → E[X]) (q : E[X]) :
    (fun i => Polynomial.map φ ((Fin.snoc L q : Fin (n+1) → E[X]) i))
      = Fin.snoc (fun i => (L i).map φ) (q.map φ) := by
  funext i; refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j; simp

variable [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
/-- Membership in the realization of a sign condition with one polynomial `q`
appended to the family splits into the original condition and the sign of `q`. -/
lemma mem_realizationOver_snoc {n : ℕ}
    (σ : SignCondition (Fin n)) (sq : SignType) (P : R[X]) (Q : Fin n → R[X]) (q : R[X]) (x : R) :
    x ∈ SignCondition.realizationOver (Fin.snoc σ sq) P (Fin.snoc Q q) ↔
    (P.IsRoot x ∧ ∀ i : Fin n, SignType.sign ((Q i).eval x) = σ i)
      ∧ SignType.sign (q.eval x) = sq := by
  rw [SignCondition.mem_realizationOver]
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨⟨hr, fun i => ?_⟩, ?_⟩
    · have := h i.castSucc; rwa [Fin.snoc_castSucc, Fin.snoc_castSucc] at this
    · have := h (Fin.last n); rwa [Fin.snoc_last, Fin.snoc_last] at this
  · rintro ⟨⟨hr, h⟩, hq⟩
    refine ⟨hr, fun i => ?_⟩
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last, Fin.snoc_last]; exact hq
    · intro j; rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact h j

variable [LinearOrder E] [IsStrictOrderedRing E] [LinearOrder R'] [IsStrictOrderedRing R']

/-- **Existence and uniqueness of the matching root.** For `p ∈ F[X]` with a root
`α ∈ R`, there is a unique `β ∈ R'` realizing `α`'s Thom encoding for `p.map τ`. -/
theorem exists_unique_thom_root (hR : HasIntermediateValueProperty R)
    (hR' : HasIntermediateValueProperty R')
    (ι : E →+* R) (hι : StrictMono ι) (τ : E →+* R') (hτ : StrictMono τ)
    (p : E[X]) (hp : p ≠ 0) (α : R) (hα : (p.map ι).IsRoot α) :
    ∃ β : R', derReali (p.map τ) (p.map ι).natDegree (thomEnc (p.map ι) α) = {β} := by
  set σ := thomEnc (p.map ι) α with hσ
  have hσ0 : σ 0 = 0 := by simp [hσ, thomEnc, hα.eq_zero]
  have hαmem : α ∈ derReali (p.map ι) (p.map ι).natDegree σ := fun i _ => rfl
  have hne : (derReali (p.map τ) (p.map ι).natDegree σ).Nonempty := by
    rw [← derReali_nonempty_transfer hR hR' ι hι τ hτ (p.map ι).natDegree p hp σ hσ0]
    exact ⟨α, hαmem⟩
  obtain ⟨β, hβ⟩ := hne
  have hpτ : p.map τ ≠ 0 := by simpa [Polynomial.map_eq_zero_iff τ.injective] using hp
  have hdeg : (p.map τ).natDegree ≤ (p.map ι).natDegree := by
    rw [natDegree_map_eq_of_injective τ.injective, natDegree_map_eq_of_injective ι.injective]
  refine ⟨β, Set.eq_singleton_iff_unique_mem.mpr ⟨hβ, fun y hy => ?_⟩⟩
  exact proposition_2_28_part1 hR' (p.map τ) hpτ (p.map ι).natDegree σ hdeg hσ0 y β hy hβ

/-- **Sign preservation.** If `β` realizes `α`'s Thom encoding for `p.map τ`,
then for every `q ∈ F[X]` the signs match: `sign(q(α)) = sign(ψq(β))`. Hence the
field embedding `α ↦ β` is order-preserving.

Proof: append `q` to the Thom derivative family; `α` realizes the extended sign
condition `(Thom encoding of α, sign(q(α)))`, which therefore is realized in `R'`
by some `γ`; `γ` carries `α`'s Thom encoding so `γ = β` by uniqueness, and its
`q`-component gives `sign(ψq(β)) = sign(q(α))`. -/
theorem sign_preserved (hR : HasIntermediateValueProperty R)
    (hR' : HasIntermediateValueProperty R')
    (ι : E →+* R) (hι : StrictMono ι) (τ : E →+* R') (hτ : StrictMono τ)
    (p : E[X]) (hp : p ≠ 0) (α : R) (hα : (p.map ι).IsRoot α)
    (β : R') (hβ : derReali (p.map τ) (p.map ι).natDegree (thomEnc (p.map ι) α) = {β})
    (q : E[X]) :
    SignType.sign ((q.map ι).eval α) = SignType.sign ((q.map τ).eval β) := by
  set N := (p.map ι).natDegree with hN
  set σ := thomEnc (p.map ι) α with hσ
  have hσ0 : σ 0 = 0 := by simp [hσ, thomEnc, hα.eq_zero]
  set sq := SignType.sign ((q.map ι).eval α) with hsq
  set Qext : Fin (N+1) → E[X] := Fin.snoc (thomFamily p N) q with hQext
  set σext : SignCondition (Fin (N+1)) := Fin.snoc (thomSC N σ) sq with hσext
  have hαreal :
      (SignCondition.realizationOver σext (p.map ι) (fun i => (Qext i).map ι)).Nonempty := by
    refine ⟨α, ?_⟩
    rw [hQext, hσext, map_comp_snoc, thomFamily_map, mem_realizationOver_snoc]
    exact ⟨⟨hα, fun i => by simp only [thomFamily, thomSC, hσ, thomEnc]⟩, rfl⟩
  obtain ⟨γ, hγ⟩ :=
    (realizationOver_nonempty_transfer hR hR' ι hι τ hτ (N+1) p hp Qext σext).mp hαreal
  rw [hQext, hσext, map_comp_snoc, thomFamily_map, mem_realizationOver_snoc] at hγ
  obtain ⟨⟨hγroot, hγthom⟩, hγq⟩ := hγ
  have hγderReali : γ ∈ derReali (p.map τ) N σ := by
    rw [derReali_eq_realizationOver _ N σ hσ0, SignCondition.mem_realizationOver]
    exact ⟨hγroot, hγthom⟩
  rw [hβ, Set.mem_singleton_iff] at hγderReali
  subst hγderReali
  rw [← hγq]

end Azurite.BPR
