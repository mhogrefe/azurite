/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_88
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83

/-! # BPR Proposition 2.89: extension of the graph of a semialgebraic function

If `f : S → T` is a semialgebraic function with graph `G ⊆ R^{k+ℓ}`, and `R'` is a real
closed extension of `R`, then `Ext(G, R')` is the graph of a semialgebraic function
`Ext(f, R') : Ext(S, R') → Ext(T, R')`.

Following BPR, the fact that `G` is the graph of a function `S → T` is a first-order
property (domain, single-valuedness, codomain containment); it is true in `R`, so by the
Tarski–Seidenberg transfer principle it is true in `R'`. We carry this out at the set level,
using that the extension commutes with the boolean operations (Proposition 2.87), with the
projection (Proposition 2.88), with coordinate reindexing (`ext_comap` below), and preserves
inclusions (`ext_mono`).
-/

open MvPolynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
variable [Algebra R R']

/-- **The extension of the empty set is empty.** -/
theorem ext_empty {k : ℕ} (h : IsSemialgebraicSet (∅ : Set (Fin k → R))) :
    extension (R' := R') (∅ : Set (Fin k → R)) h = ∅ := by
  have hfalse : (∅ : Set (Fin k → R))
      = (Formula.atom (⟨1, OrderRel.eq⟩ : OrderedFieldAtom (Fin k) R)).realization (C := R) := by
    ext y
    simp only [Formula.realization, AtomRealization.interpret, Set.mem_ofPred_eq, map_one,
      Set.mem_empty_iff_false, false_iff]
    exact one_ne_zero
  rw [ext_eq h hfalse]
  ext y'
  simp only [Formula.realization, AtomRealization.interpret, Set.mem_ofPred_eq, map_one,
    Set.mem_empty_iff_false, iff_false]
  exact one_ne_zero

/-- **The extension commutes with coordinate reindexing.** For semialgebraic `W ⊆ R^a` and an
injective `g : Fin a → Fin b`, the extension of the pullback `{y | y ∘ g ∈ W}` is the pullback
of the extension. (The formula-level `comap` is `Formula.rename`.) -/
theorem ext_comap {a b : ℕ} (g : Fin a → Fin b) (hg : Function.Injective g)
    {W : Set (Fin a → R)} (hW : IsSemialgebraicSet W) :
    extension (R' := R') {y : Fin b → R | y ∘ g ∈ W} (IsSemialgebraicSet.comap g hW)
      = {y' : Fin b → R' | y' ∘ g ∈ extension (R' := R') W hW} := by
  obtain ⟨Θ, hqf, hWeq⟩ := semialgebraic_isQFRealizable W hW
  have h1 : {y : Fin b → R | y ∘ g ∈ W}
      = (Θ.rename g (OrderedFieldAtom.renameVars g)).realization (C := R) := by
    rw [Formula.rename_realization_ordered g hg]
    ext y; simp only [Set.mem_ofPred_eq, Set.mem_preimage, hWeq]
  rw [ext_eq (IsSemialgebraicSet.comap g hW) h1, Formula.rename_realization_ordered g hg]
  ext y'
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [ext_eq hW hWeq]

/-- Peeling one coordinate off the block projection: forgetting the last `ℓ+1` coordinates is
forgetting the last one (`Fin.init`) and then the last `ℓ`. -/
private theorem castAdd_succ_image {k ℓ : ℕ} {α : Type*} (W : Set (Fin (k + (ℓ + 1)) → α)) :
    (· ∘ Fin.castAdd (ℓ + 1)) '' W = (· ∘ Fin.castAdd ℓ) '' (Fin.init '' W) := by
  rw [Set.image_image]
  exact Set.image_congr' fun z => rfl

/-- The block projection `· ∘ Fin.castAdd ℓ` (forget the last `ℓ` coordinates) of a
semialgebraic set is semialgebraic (iterate Proposition 2.88). -/
theorem projBlock_isSemialgebraic {k : ℕ} : ∀ {ℓ : ℕ} {W : Set (Fin (k + ℓ) → R)},
    IsSemialgebraicSet W → IsSemialgebraicSet ((· ∘ Fin.castAdd ℓ) '' W) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro W hW
    have hf : (fun z : Fin (k + 0) → R => z ∘ Fin.castAdd 0) = id := by
      funext z i; exact congrArg z (Fin.ext rfl)
    rw [hf, Set.image_id]; exact hW
  | succ ℓ ih =>
    intro W hW
    rw [castAdd_succ_image]
    exact ih (proj_isSemialgebraic hW)

/-- **The extension commutes with the block projection** `π_X = · ∘ Fin.castAdd ℓ` (forget the
last `ℓ` coordinates): `Ext(π_X W) = π_X(Ext W)`. Iterate Proposition 2.88. -/
theorem ext_proj {k : ℕ} : ∀ {ℓ : ℕ} {W : Set (Fin (k + ℓ) → R)} (hW : IsSemialgebraicSet W),
    extension (R' := R') ((· ∘ Fin.castAdd ℓ) '' W) (projBlock_isSemialgebraic hW)
      = (· ∘ Fin.castAdd ℓ) '' (extension (R' := R') W hW) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro W hW
    have heR : (· ∘ Fin.castAdd 0) '' W = W := by
      have hf : (fun z : Fin (k + 0) → R => z ∘ Fin.castAdd 0) = id := by
        funext z i; exact congrArg z (Fin.ext rfl)
      rw [hf, Set.image_id]
    have heR' : (· ∘ Fin.castAdd 0) '' (extension (R' := R') W hW) = extension (R' := R') W hW := by
      have hf : (fun z : Fin (k + 0) → R' => z ∘ Fin.castAdd 0) = id := by
        funext z i; exact congrArg z (Fin.ext rfl)
      rw [hf, Set.image_id]
    rw [ext_congr (projBlock_isSemialgebraic hW) hW heR, heR']
  | succ ℓ ih =>
    intro W hW
    rw [ext_congr (projBlock_isSemialgebraic hW)
        (projBlock_isSemialgebraic (proj_isSemialgebraic hW)) (castAdd_succ_image W),
      ih (proj_isSemialgebraic hW), ← proposition_2_88 hW, castAdd_succ_image (extension (R' := R') W hW)]

/-- Reconstruction: a point equals the `Fin.append` of its two coordinate blocks. -/
private theorem append_castAdd_natAdd {k ℓ : ℕ} {α : Type*} (z : Fin (k + ℓ) → α) :
    Fin.append (z ∘ Fin.castAdd ℓ) (z ∘ Fin.natAdd k) = z := by
  funext i
  induction i using Fin.addCases with
  | left a => simp [Fin.append_left]
  | right j => simp [Fin.append_right]

/-- The block projection in `∃ Fin.append` form. -/
private theorem projImage_eq_exists {k ℓ : ℕ} {α : Type*} (W : Set (Fin (k + ℓ) → α)) :
    (· ∘ Fin.castAdd ℓ) '' W = {x : Fin k → α | ∃ y : Fin ℓ → α, Fin.append x y ∈ W} := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hzW, rfl⟩
    exact ⟨z ∘ Fin.natAdd k, by rw [append_castAdd_natAdd]; exact hzW⟩
  · rintro ⟨y, hy⟩
    exact ⟨Fin.append x y, hy, append_comp_castAdd x y⟩

/-- **The extension commutes with the `∃ Fin.append` projection** (the existential projection
forgetting the last `ℓ` coordinates): `Ext {x | ∃ y, (x,y) ∈ W} = {x' | ∃ y', (x',y') ∈ Ext W}`. -/
theorem ext_exists_append {k ℓ : ℕ} {W : Set (Fin (k + ℓ) → R)} (hW : IsSemialgebraicSet W)
    (hπ : IsSemialgebraicSet {x : Fin k → R | ∃ y : Fin ℓ → R, Fin.append x y ∈ W}) :
    extension (R' := R') {x : Fin k → R | ∃ y : Fin ℓ → R, Fin.append x y ∈ W} hπ
      = {x' : Fin k → R' | ∃ y' : Fin ℓ → R', Fin.append x' y' ∈ extension (R' := R') W hW} := by
  rw [ext_congr hπ (projBlock_isSemialgebraic hW) (projImage_eq_exists W).symm, ext_proj hW,
    projImage_eq_exists]

/-! ### Equality-block sets (diagonals) and their extension -/

/-- `⋀_{j ∈ M} (X (p j) = X (q j))` — conjunction of coordinate-equalities. -/
noncomputable def eqBlockFormOn {N m : ℕ} (M : List (Fin m)) (p q : Fin m → Fin N) :
    Formula (Fin N) (OrderedFieldAtom (Fin N) R) :=
  M.foldr (fun j φ =>
      (Formula.atom (⟨X (p j) - X (q j), OrderRel.eq⟩ : OrderedFieldAtom (Fin N) R)).and φ)
    (Formula.atom (⟨0, OrderRel.eq⟩ : OrderedFieldAtom (Fin N) R))

omit [IsRealClosed R] [Algebra R R'] [LinearOrder R] [IsStrictOrderedRing R] in
theorem mem_eqBlockFormOn {N m : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Algebra R K] (M : List (Fin m)) (p q : Fin m → Fin N) (w : Fin N → K) :
    w ∈ (eqBlockFormOn (R := R) M p q).realization (C := K) ↔ ∀ j ∈ M, w (p j) = w (q j) := by
  induction M with
  | nil =>
    have hunfold : eqBlockFormOn (R := R) ([] : List (Fin m)) p q
        = Formula.atom (⟨0, OrderRel.eq⟩ : OrderedFieldAtom (Fin N) R) := rfl
    rw [hunfold]
    simp only [Formula.realization, AtomRealization.interpret, Set.mem_ofPred_eq, map_zero,
      List.not_mem_nil, false_implies, implies_true]
  | cons j M' ih =>
    have hunfold : eqBlockFormOn (R := R) (j :: M') p q
        = (Formula.atom (⟨X (p j) - X (q j), OrderRel.eq⟩ : OrderedFieldAtom (Fin N) R)).and
            (eqBlockFormOn (R := R) M' p q) := rfl
    rw [hunfold]
    simp only [Formula.realization, Set.mem_inter_iff, AtomRealization.interpret,
      Set.mem_ofPred_eq, map_sub, aeval_X, sub_eq_zero, ih, List.forall_mem_cons]

omit [IsRealClosed R] in
/-- The equality-block set `{w | ∀ j, w (p j) = w (q j)}` is semialgebraic. -/
theorem eqBlock_isSemialgebraic {N m : ℕ} (p q : Fin m → Fin N) :
    IsSemialgebraicSet {w : Fin N → R | ∀ j, w (p j) = w (q j)} := by
  have heq : {w : Fin N → R | ∀ j, w (p j) = w (q j)}
      = (eqBlockFormOn (R := R) (List.finRange m) p q).realization (C := R) := by
    ext w; rw [mem_eqBlockFormOn]; simp [List.mem_finRange]
  rw [heq]; exact qfRealizable_isSemialgebraic (by
    show (eqBlockFormOn (R := R) (List.finRange m) p q).IsQuantifierFree
    clear heq
    induction (List.finRange m) with
    | nil => exact trivial
    | cons j M' ih => exact ⟨trivial, ih⟩)

/-- **The extension commutes with an equality-block (diagonal) set.** -/
theorem ext_eqBlock {N m : ℕ} (p q : Fin m → Fin N) :
    extension (R' := R') {w : Fin N → R | ∀ j, w (p j) = w (q j)} (eqBlock_isSemialgebraic p q)
      = {w' : Fin N → R' | ∀ j, w' (p j) = w' (q j)} := by
  have hR : {w : Fin N → R | ∀ j, w (p j) = w (q j)}
      = (eqBlockFormOn (R := R) (List.finRange m) p q).realization (C := R) := by
    ext w; rw [mem_eqBlockFormOn]; simp [List.mem_finRange]
  rw [ext_eq (eqBlock_isSemialgebraic p q) hR]
  ext w'; rw [mem_eqBlockFormOn]; simp [List.mem_finRange]

/-! ### Proposition 2.89 -/

/-- **BPR Proposition 2.89.** If `f : S → T` is a semialgebraic function with graph `G`, and
`R'` is a real closed extension of `R`, then `Ext(G, R')` is the graph of a semialgebraic
function `Ext(S, R') → Ext(T, R')`. We produce the function `f'` and show its graph (over
`Ext(S, R')`) is `Ext(G, R')`, and that it maps `Ext(S, R')` into `Ext(T, R')`. -/
theorem proposition_2_89 {k ℓ : ℕ} {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T)
    (hf : IsSemialgebraicFunction S f) (hmaps : Set.MapsTo f S T) :
    ∃ f' : (Fin k → R') → (Fin ℓ → R'),
      extension (R' := R') (funGraph S f) hf = funGraph (extension (R' := R') S hS) f' ∧
      Set.MapsTo f' (extension (R' := R') S hS) (extension (R' := R') T hT) := by
  classical
  -- **Domain.** `S = π_X(G)`, and the extension commutes with this projection.
  have hSeq : S = {x : Fin k → R | ∃ y : Fin ℓ → R, Fin.append x y ∈ funGraph S f} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hx; exact ⟨f x, (append_mem_funGraph S f x (f x)).mpr ⟨hx, rfl⟩⟩
    · rintro ⟨y, hy⟩; exact ((append_mem_funGraph S f x y).mp hy).1
  have hdom : extension (R' := R') S hS
      = {x' : Fin k → R' | ∃ y' : Fin ℓ → R', Fin.append x' y' ∈ extension (R' := R') (funGraph S f) hf} := by
    rw [ext_congr hS (IsSemialgebraicSet.exists_append_right hf) hSeq]
    exact ext_exists_append hf (IsSemialgebraicSet.exists_append_right hf)
  -- **Codomain.** `G ⊆ {p | p∘natAdd ∈ T}`, and the extension commutes with that pullback.
  have hcod : ∀ p' ∈ extension (R' := R') (funGraph S f) hf,
      p' ∘ Fin.natAdd k ∈ extension (R' := R') T hT := by
    have hsub : funGraph S f ⊆ {p : Fin (k + ℓ) → R | p ∘ Fin.natAdd k ∈ T} := by
      intro p hp
      rw [mem_funGraph] at hp
      simp only [Set.mem_ofPred_eq, hp.2]; exact hmaps hp.1
    have hmono := ext_mono (R' := R') hf (IsSemialgebraicSet.comap (Fin.natAdd k) hT) hsub
    rw [ext_comap (Fin.natAdd k) (Fin.natAdd_injective ℓ k) hT] at hmono
    exact fun p' hp' => hmono hp'
  -- **Single-valuedness.** Work in `Fin (N) = Fin ((k+ℓ)+(k+ℓ))` (two copies `z, z'`).
  have hsv : ∀ z ∈ extension (R' := R') (funGraph S f) hf,
      ∀ z' ∈ extension (R' := R') (funGraph S f) hf,
      z ∘ Fin.castAdd ℓ = z' ∘ Fin.castAdd ℓ → z ∘ Fin.natAdd k = z' ∘ Fin.natAdd k := by
    set gz : Fin (k + ℓ) → Fin ((k + ℓ) + (k + ℓ)) := Fin.castAdd (k + ℓ) with hgz
    set gz' : Fin (k + ℓ) → Fin ((k + ℓ) + (k + ℓ)) := Fin.natAdd (k + ℓ) with hgz'
    set px : Fin k → Fin ((k + ℓ) + (k + ℓ)) := fun a => gz (Fin.castAdd ℓ a) with hpx
    set qx : Fin k → Fin ((k + ℓ) + (k + ℓ)) := fun a => gz' (Fin.castAdd ℓ a) with hqx
    set py : Fin ℓ → Fin ((k + ℓ) + (k + ℓ)) := fun j => gz (Fin.natAdd k j) with hpy
    set qy : Fin ℓ → Fin ((k + ℓ) + (k + ℓ)) := fun j => gz' (Fin.natAdd k j) with hqy
    -- `P ⊆ Diag` over `R` is single-valuedness of `G`.
    have hPD : (({w | w ∘ gz ∈ funGraph S f} ∩ {w | w ∘ gz' ∈ funGraph S f})
        ∩ {w : Fin ((k+ℓ)+(k+ℓ)) → R | ∀ a, w (px a) = w (qx a)})
        ⊆ {w : Fin ((k+ℓ)+(k+ℓ)) → R | ∀ j, w (py j) = w (qy j)} := by
      rintro w ⟨⟨hwz, hwz'⟩, hwx⟩ j
      simp only [Set.mem_ofPred_eq] at hwz hwz'
      rw [mem_funGraph] at hwz hwz'
      have hxeq : (w ∘ gz) ∘ Fin.castAdd ℓ = (w ∘ gz') ∘ Fin.castAdd ℓ := by
        funext a; exact hwx a
      have hyeq : (w ∘ gz) ∘ Fin.natAdd k = (w ∘ gz') ∘ Fin.natAdd k := by
        rw [hwz.2, hwz'.2, hxeq]
      exact congrFun hyeq j
    have hPsa : IsSemialgebraicSet (({w | w ∘ gz ∈ funGraph S f} ∩ {w | w ∘ gz' ∈ funGraph S f})
        ∩ {w : Fin ((k+ℓ)+(k+ℓ)) → R | ∀ a, w (px a) = w (qx a)}) :=
      ((IsSemialgebraicSet.comap gz hf).inter (IsSemialgebraicSet.comap gz' hf)).inter
        (eqBlock_isSemialgebraic px qx)
    have hmono := ext_mono (R' := R') hPsa (eqBlock_isSemialgebraic py qy) hPD
    -- decode the two extensions
    rw [ext_eqBlock py qy] at hmono
    have hPext : extension (R' := R') _ hPsa
        = (({w' | w' ∘ gz ∈ extension (R' := R') (funGraph S f) hf}
            ∩ {w' | w' ∘ gz' ∈ extension (R' := R') (funGraph S f) hf})
          ∩ {w' : Fin ((k+ℓ)+(k+ℓ)) → R' | ∀ a, w' (px a) = w' (qx a)}) := by
      rw [ext_inter ((IsSemialgebraicSet.comap gz hf).inter (IsSemialgebraicSet.comap gz' hf))
            (eqBlock_isSemialgebraic px qx),
          ext_inter (IsSemialgebraicSet.comap gz hf) (IsSemialgebraicSet.comap gz' hf),
          ext_comap gz (Fin.castAdd_injective _ _) hf,
          ext_comap gz' (Fin.natAdd_injective _ _) hf, ext_eqBlock px qx]
    rw [hPext] at hmono
    -- apply to `w' = append z z'`
    intro z hz z' hz' hzz
    have hgzval : Fin.append z z' ∘ gz = z := by rw [hgz]; exact append_comp_castAdd z z'
    have hgz'val : Fin.append z z' ∘ gz' = z' := by rw [hgz']; exact append_comp_natAdd z z'
    have hw' : Fin.append z z' ∈ (({w' | w' ∘ gz ∈ extension (R' := R') (funGraph S f) hf}
        ∩ {w' | w' ∘ gz' ∈ extension (R' := R') (funGraph S f) hf})
      ∩ {w' : Fin ((k+ℓ)+(k+ℓ)) → R' | ∀ a, w' (px a) = w' (qx a)}) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Set.mem_ofPred_eq, hgzval]; exact hz
      · rw [Set.mem_ofPred_eq, hgz'val]; exact hz'
      · intro a
        show Fin.append z z' (px a) = Fin.append z z' (qx a)
        rw [hpx, hqx]
        show Fin.append z z' (gz (Fin.castAdd ℓ a)) = Fin.append z z' (gz' (Fin.castAdd ℓ a))
        have e1 : Fin.append z z' (gz (Fin.castAdd ℓ a)) = z (Fin.castAdd ℓ a) :=
          congrFun hgzval (Fin.castAdd ℓ a)
        have e2 : Fin.append z z' (gz' (Fin.castAdd ℓ a)) = z' (Fin.castAdd ℓ a) :=
          congrFun hgz'val (Fin.castAdd ℓ a)
        rw [e1, e2]; exact congrFun hzz a
    have := hmono hw'
    funext j
    have hj := this j
    show z (Fin.natAdd k j) = z' (Fin.natAdd k j)
    rw [hpy, hqy] at hj
    rw [← congrFun hgzval (Fin.natAdd k j), ← congrFun hgz'val (Fin.natAdd k j)]
    exact hj
  -- **Construct `f'`** and verify the graph equality and the codomain.
  set ExtG := extension (R' := R') (funGraph S f) hf with hExtG
  refine ⟨fun x' => if h : ∃ y' : Fin ℓ → R', Fin.append x' y' ∈ ExtG then h.choose else 0, ?_, ?_⟩
  · ext z
    rw [mem_funGraph]
    constructor
    · intro hz
      have hx : z ∘ Fin.castAdd ℓ ∈ extension (R' := R') S hS := by
        rw [hdom]; exact ⟨z ∘ Fin.natAdd k, by rw [append_castAdd_natAdd]; exact hz⟩
      refine ⟨hx, ?_⟩
      have hex : ∃ y' : Fin ℓ → R', Fin.append (z ∘ Fin.castAdd ℓ) y' ∈ ExtG :=
        ⟨z ∘ Fin.natAdd k, by rw [append_castAdd_natAdd]; exact hz⟩
      simp only [dite_eq_left hex]
      have hmem : Fin.append (z ∘ Fin.castAdd ℓ) hex.choose ∈ ExtG := hex.choose_spec
      have h1 := hsv z hz (Fin.append (z ∘ Fin.castAdd ℓ) hex.choose) hmem (by
        rw [append_comp_castAdd])
      rw [append_comp_natAdd] at h1; exact h1
    · rintro ⟨hx, hval⟩
      have hex : ∃ y' : Fin ℓ → R', Fin.append (z ∘ Fin.castAdd ℓ) y' ∈ ExtG := by
        rw [hdom] at hx; exact hx
      rw [dite_eq_left hex] at hval
      have : z = Fin.append (z ∘ Fin.castAdd ℓ) hex.choose := by
        rw [← hval, append_castAdd_natAdd]
      rw [this]; exact hex.choose_spec
  · intro x' hx'
    have hex : ∃ y' : Fin ℓ → R', Fin.append x' y' ∈ ExtG := by rw [hdom] at hx'; exact hx'
    simp only [dite_eq_left hex]
    have hmem : Fin.append x' hex.choose ∈ ExtG := hex.choose_spec
    have := hcod (Fin.append x' hex.choose) hmem
    rwa [append_comp_natAdd] at this

end Azurite.BPR
