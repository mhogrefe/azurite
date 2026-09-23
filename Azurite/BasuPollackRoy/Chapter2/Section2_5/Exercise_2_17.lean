import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_89

/-! # BPR Exercise 2.17: extension of a semialgebraic function preserves injectivity,
surjectivity, bijectivity, and commutes with taking preimages

Throughout, `f : S → T` is a semialgebraic function (graph `G = funGraph S f`) and `f'` is an
extension of `f` to `R'` in the sense of Proposition 2.89: `Ext(G) = funGraph(Ext S) f'`.

- (a) `f` is injective / surjective / bijective iff `Ext(f)` is.
- (b) `Ext(f⁻¹(T'), R') = Ext(f, R')⁻¹(Ext(T', R'))`.

Both rest on the extension's commutation properties (Proposition 2.87 boolean/monotone,
Proposition 2.88/`ext_exists_append` projection, `ext_comap` reindexing) and on point-transfer
`mem_ext_algebraMap`. The key new reusable fact is `ext_subset_iff`: `A ⊆ B` over `R` iff
`Ext A ⊆ Ext B` over `R'`.
-/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
variable [Algebra R R']

/-- **Inclusions transfer both ways.** `A ⊆ B` iff `Ext A ⊆ Ext B`: forward is monotonicity
(Proposition 2.87); backward embeds `R`-points via `mem_ext_algebraMap`. -/
theorem ext_subset_iff {k : ℕ} {A B : Set (Fin k → R)} (hA : IsSemialgebraicSet A)
    (hB : IsSemialgebraicSet B) :
    A ⊆ B ↔ extension (R' := R') A hA ⊆ extension (R' := R') B hB := by
  constructor
  · exact fun h => ext_mono hA hB h
  · intro h x hx
    have : (algebraMap R R' ∘ x) ∈ extension (R' := R') A hA :=
      (mem_ext_algebraMap hA x).mpr hx
    exact (mem_ext_algebraMap hB x).mp (h this)

/-- **BPR Exercise 2.17(b).** The extension commutes with taking preimages:
`Ext(f⁻¹(T'), R') = Ext(f, R')⁻¹(Ext(T', R'))`. Here `f⁻¹(T') = {x ∈ S | f x ∈ T'}`. -/
theorem exercise_2_17b {k ℓ : ℕ} {S : Set (Fin k → R)} {T' : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {f' : (Fin k → R') → (Fin ℓ → R')}
    (hS : IsSemialgebraicSet S) (hT' : IsSemialgebraicSet T')
    (hf : IsSemialgebraicFunction S f)
    (hgraph : extension (R' := R') (funGraph S f) hf
      = funGraph (extension (R' := R') S hS) f')
    (hpre : IsSemialgebraicSet {x : Fin k → R | x ∈ S ∧ f x ∈ T'}) :
    extension (R' := R') {x : Fin k → R | x ∈ S ∧ f x ∈ T'} hpre
      = {x' : Fin k → R' | x' ∈ extension (R' := R') S hS
          ∧ f' x' ∈ extension (R' := R') T' hT'} := by
  -- `f⁻¹(T') = π_X(G ∩ {p | p∘natAdd ∈ T'})`.
  have hWsa : IsSemialgebraicSet (funGraph S f ∩ {p : Fin (k + ℓ) → R | p ∘ Fin.natAdd k ∈ T'}) :=
    hf.inter (IsSemialgebraicSet.comap (Fin.natAdd k) hT')
  have hpre_eq : {x : Fin k → R | x ∈ S ∧ f x ∈ T'}
      = {x : Fin k → R | ∃ y : Fin ℓ → R,
          Fin.append x y ∈ funGraph S f ∩ {p : Fin (k + ℓ) → R | p ∘ Fin.natAdd k ∈ T'}} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hxS, hfx⟩
      exact ⟨f x, (append_mem_funGraph S f x (f x)).mpr ⟨hxS, rfl⟩, by
        rw [append_comp_natAdd]; exact hfx⟩
    · rintro ⟨y, hg, hy⟩
      rw [append_comp_natAdd] at hy
      obtain ⟨hxS, hyf⟩ := (append_mem_funGraph S f x y).mp hg
      exact ⟨hxS, hyf ▸ hy⟩
  rw [ext_congr hpre (IsSemialgebraicSet.exists_append_right hWsa) hpre_eq,
    ext_exists_append hWsa,
    ext_inter hf (IsSemialgebraicSet.comap (Fin.natAdd k) hT'),
    ext_comap (Fin.natAdd k) (Fin.natAdd_injective ℓ k) hT', hgraph]
  ext x'
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨y', hg, hy'⟩
    rw [append_comp_natAdd] at hy'
    obtain ⟨hxS, hyf⟩ := (append_mem_funGraph (extension (R' := R') S hS) f' x' y').mp hg
    exact ⟨hxS, hyf ▸ hy'⟩
  · rintro ⟨hxS, hfx⟩
    refine ⟨f' x', (append_mem_funGraph (extension (R' := R') S hS) f' x' (f' x')).mpr ⟨hxS, rfl⟩, ?_⟩
    rw [append_comp_natAdd]; exact hfx

/-! ### Part (a): injectivity, surjectivity, bijectivity -/

/-- A function is injective on its domain iff its graph is left-unique (same output coordinate
implies same input coordinate). -/
theorem funGraph_injOn_iff {k ℓ : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (A : Set (Fin k → K)) (g : (Fin k → K) → (Fin ℓ → K)) :
    Set.InjOn g A ↔ ∀ z ∈ funGraph A g, ∀ z' ∈ funGraph A g,
      z ∘ Fin.natAdd k = z' ∘ Fin.natAdd k → z ∘ Fin.castAdd ℓ = z' ∘ Fin.castAdd ℓ := by
  constructor
  · intro hinj z hz z' hz' hy
    rw [mem_funGraph] at hz hz'
    have hg : g (z ∘ Fin.castAdd ℓ) = g (z' ∘ Fin.castAdd ℓ) := by rw [← hz.2, ← hz'.2]; exact hy
    exact hinj hz.1 hz'.1 hg
  · intro hlu x₁ hx₁ x₂ hx₂ hgx
    have hz₁ : Fin.append x₁ (g x₁) ∈ funGraph A g :=
      (append_mem_funGraph A g x₁ (g x₁)).mpr ⟨hx₁, rfl⟩
    have hz₂ : Fin.append x₂ (g x₂) ∈ funGraph A g :=
      (append_mem_funGraph A g x₂ (g x₂)).mpr ⟨hx₂, rfl⟩
    have hyeq : Fin.append x₁ (g x₁) ∘ Fin.natAdd k = Fin.append x₂ (g x₂) ∘ Fin.natAdd k := by
      rw [append_comp_natAdd, append_comp_natAdd, hgx]
    have hcast := hlu _ hz₁ _ hz₂ hyeq
    rw [append_comp_castAdd, append_comp_castAdd] at hcast
    exact hcast

/-- The doubled-space "collision" set: two copies of `W` with equal *output* (last `ℓ`)
coordinates. -/
def blockP {k ℓ : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (W : Set (Fin (k + ℓ) → K)) : Set (Fin ((k + ℓ) + (k + ℓ)) → K) :=
  ({w | w ∘ Fin.castAdd (k + ℓ) ∈ W} ∩ {w | w ∘ Fin.natAdd (k + ℓ) ∈ W})
    ∩ {w | ∀ j : Fin ℓ, w (Fin.castAdd (k + ℓ) (Fin.natAdd k j))
        = w (Fin.natAdd (k + ℓ) (Fin.natAdd k j))}

/-- The diagonal on the *input* (first `k`) coordinates of the doubled space. -/
def blockD {k ℓ : ℕ} (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Set (Fin ((k + ℓ) + (k + ℓ)) → K) :=
  {w | ∀ a : Fin k, w (Fin.castAdd (k + ℓ) (Fin.castAdd ℓ a))
      = w (Fin.natAdd (k + ℓ) (Fin.castAdd ℓ a))}

/-- `blockP W ⊆ blockD` iff `W` is left-unique. (The bijection `w ↔ (w∘castAdd, w∘natAdd)`.) -/
theorem blockSubset_iff_leftUnique {k ℓ : ℕ} {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (W : Set (Fin (k + ℓ) → K)) :
    blockP W ⊆ blockD (k := k) (ℓ := ℓ) K ↔
      ∀ z ∈ W, ∀ z' ∈ W, z ∘ Fin.natAdd k = z' ∘ Fin.natAdd k → z ∘ Fin.castAdd ℓ = z' ∘ Fin.castAdd ℓ := by
  constructor
  · intro hPD z hz z' hz' hy
    have hw : Fin.append z z' ∈ blockP W := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show Fin.append z z' ∘ Fin.castAdd (k + ℓ) ∈ W; rw [append_comp_castAdd]; exact hz
      · show Fin.append z z' ∘ Fin.natAdd (k + ℓ) ∈ W; rw [append_comp_natAdd]; exact hz'
      · intro j
        show Fin.append z z' (Fin.castAdd (k + ℓ) (Fin.natAdd k j))
          = Fin.append z z' (Fin.natAdd (k + ℓ) (Fin.natAdd k j))
        rw [show Fin.append z z' (Fin.castAdd (k + ℓ) (Fin.natAdd k j))
              = z (Fin.natAdd k j) from congrFun (append_comp_castAdd z z') (Fin.natAdd k j),
          show Fin.append z z' (Fin.natAdd (k + ℓ) (Fin.natAdd k j))
              = z' (Fin.natAdd k j) from congrFun (append_comp_natAdd z z') (Fin.natAdd k j)]
        exact congrFun hy j
    funext a
    have := hPD hw a
    rw [show Fin.append z z' (Fin.castAdd (k + ℓ) (Fin.castAdd ℓ a))
          = z (Fin.castAdd ℓ a) from congrFun (append_comp_castAdd z z') (Fin.castAdd ℓ a),
      show Fin.append z z' (Fin.natAdd (k + ℓ) (Fin.castAdd ℓ a))
          = z' (Fin.castAdd ℓ a) from congrFun (append_comp_natAdd z z') (Fin.castAdd ℓ a)] at this
    exact this
  · intro hlu w hw a
    obtain ⟨⟨hwz, hwz'⟩, hwy⟩ := hw
    have hzW : w ∘ Fin.castAdd (k + ℓ) ∈ W := hwz
    have hz'W : w ∘ Fin.natAdd (k + ℓ) ∈ W := hwz'
    have hyeq : (w ∘ Fin.castAdd (k + ℓ)) ∘ Fin.natAdd k
        = (w ∘ Fin.natAdd (k + ℓ)) ∘ Fin.natAdd k := by funext j; exact hwy j
    have hxeq := hlu _ hzW _ hz'W hyeq
    exact congrFun hxeq a

/-- **Left-uniqueness transfers** from `W` to `Ext W` (both directions), via `ext_subset_iff`
applied to `blockP W ⊆ blockD`. -/
theorem ext_leftUnique_iff {k ℓ : ℕ} {W : Set (Fin (k + ℓ) → R)} (hW : IsSemialgebraicSet W) :
    (∀ z ∈ W, ∀ z' ∈ W,
        z ∘ Fin.natAdd k = z' ∘ Fin.natAdd k → z ∘ Fin.castAdd ℓ = z' ∘ Fin.castAdd ℓ)
    ↔ (∀ z ∈ extension (R' := R') W hW, ∀ z' ∈ extension (R' := R') W hW,
        z ∘ Fin.natAdd k = z' ∘ Fin.natAdd k → z ∘ Fin.castAdd ℓ = z' ∘ Fin.castAdd ℓ) := by
  rw [← blockSubset_iff_leftUnique W, ← blockSubset_iff_leftUnique (extension (R' := R') W hW)]
  set py : Fin ℓ → Fin ((k + ℓ) + (k + ℓ)) := fun j => Fin.castAdd (k + ℓ) (Fin.natAdd k j) with hpy
  set qy : Fin ℓ → Fin ((k + ℓ) + (k + ℓ)) := fun j => Fin.natAdd (k + ℓ) (Fin.natAdd k j) with hqy
  set px : Fin k → Fin ((k + ℓ) + (k + ℓ)) := fun a => Fin.castAdd (k + ℓ) (Fin.castAdd ℓ a) with hpx
  set qx : Fin k → Fin ((k + ℓ) + (k + ℓ)) := fun a => Fin.natAdd (k + ℓ) (Fin.castAdd ℓ a) with hqx
  have hPsa : IsSemialgebraicSet (blockP W) :=
    ((IsSemialgebraicSet.comap (Fin.castAdd (k + ℓ)) hW).inter
      (IsSemialgebraicSet.comap (Fin.natAdd (k + ℓ)) hW)).inter (eqBlock_isSemialgebraic py qy)
  have hDsa : IsSemialgebraicSet (blockD (k := k) (ℓ := ℓ) R) := eqBlock_isSemialgebraic px qx
  rw [ext_subset_iff (R' := R') hPsa hDsa]
  have hextP : extension (R' := R') (blockP W) hPsa = blockP (extension (R' := R') W hW) := by
    show extension (R' := R')
        (({w | w ∘ Fin.castAdd (k + ℓ) ∈ W} ∩ {w | w ∘ Fin.natAdd (k + ℓ) ∈ W})
          ∩ {w | ∀ j, w (py j) = w (qy j)}) hPsa = _
    rw [ext_inter ((IsSemialgebraicSet.comap (Fin.castAdd (k + ℓ)) hW).inter
          (IsSemialgebraicSet.comap (Fin.natAdd (k + ℓ)) hW)) (eqBlock_isSemialgebraic py qy),
        ext_inter (IsSemialgebraicSet.comap (Fin.castAdd (k + ℓ)) hW)
          (IsSemialgebraicSet.comap (Fin.natAdd (k + ℓ)) hW),
        ext_comap (Fin.castAdd (k + ℓ)) (Fin.castAdd_injective _ _) hW,
        ext_comap (Fin.natAdd (k + ℓ)) (Fin.natAdd_injective _ _) hW, ext_eqBlock py qy]
    rfl
  have hextD : extension (R' := R') (blockD (k := k) (ℓ := ℓ) R) hDsa
      = blockD (k := k) (ℓ := ℓ) R' := by
    show extension (R' := R') {w | ∀ a, w (px a) = w (qx a)} hDsa = _
    rw [ext_eqBlock px qx]
    rfl
  rw [hextP, hextD]

/-- **BPR Exercise 2.17(a), injectivity.** `f` is injective on `S` iff `Ext(f)` is injective
on `Ext(S)`. -/
theorem exercise_2_17a_injOn {k ℓ : ℕ} {S : Set (Fin k → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {f' : (Fin k → R') → (Fin ℓ → R')}
    (hS : IsSemialgebraicSet S) (hf : IsSemialgebraicFunction S f)
    (hgraph : extension (R' := R') (funGraph S f) hf
      = funGraph (extension (R' := R') S hS) f') :
    Set.InjOn f S ↔ Set.InjOn f' (extension (R' := R') S hS) := by
  rw [funGraph_injOn_iff S f, funGraph_injOn_iff (extension (R' := R') S hS) f', ← hgraph]
  exact ext_leftUnique_iff hf

/-- Block-swap reindexing `Fin (k+ℓ) → Fin (ℓ+k)` (`k`-block to the back, `ℓ`-block to the
front). -/
def blockSwap (k ℓ : ℕ) : Fin (k + ℓ) → Fin (ℓ + k) :=
  Fin.addCases (fun a : Fin k => Fin.natAdd ℓ a) (fun j : Fin ℓ => Fin.castAdd k j)

theorem blockSwap_injective (k ℓ : ℕ) : Function.Injective (blockSwap k ℓ) := by
  intro i i' h
  induction i using Fin.addCases with
  | left a =>
    induction i' using Fin.addCases with
    | left a' =>
      simp only [blockSwap, Fin.addCases_left] at h
      exact congrArg _ (Fin.natAdd_injective k ℓ h)
    | right j' =>
      exfalso; simp only [blockSwap, Fin.addCases_left, Fin.addCases_right] at h
      have := congrArg Fin.val h; simp only [Fin.val_natAdd, Fin.val_castAdd] at this; omega
  | right j =>
    induction i' using Fin.addCases with
    | left a' =>
      exfalso; simp only [blockSwap, Fin.addCases_left, Fin.addCases_right] at h
      have := congrArg Fin.val h; simp only [Fin.val_natAdd, Fin.val_castAdd] at this; omega
    | right j' =>
      simp only [blockSwap, Fin.addCases_right] at h
      exact congrArg _ (Fin.castAdd_injective ℓ k h)

omit [IsRealClosed R] [IsRealClosed R'] [Algebra R R'] in
/-- `(Fin.append y x) ∘ blockSwap = Fin.append x y`. -/
theorem blockSwap_append {k ℓ : ℕ} {K : Type*} (x : Fin k → K) (y : Fin ℓ → K) :
    Fin.append y x ∘ blockSwap k ℓ = Fin.append x y := by
  funext i
  induction i using Fin.addCases with
  | left a => simp only [Function.comp_apply, blockSwap, Fin.addCases_left, Fin.append_left,
      Fin.append_right]
  | right j => simp only [Function.comp_apply, blockSwap, Fin.addCases_right, Fin.append_left,
      Fin.append_right]

/-- **The extension commutes with the left `∃ Fin.append` projection** (forget the first `k`
coordinates). -/
theorem ext_exists_append_left {k ℓ : ℕ} {W : Set (Fin (k + ℓ) → R)} (hW : IsSemialgebraicSet W)
    (hπ : IsSemialgebraicSet {y : Fin ℓ → R | ∃ x : Fin k → R, Fin.append x y ∈ W}) :
    extension (R' := R') {y : Fin ℓ → R | ∃ x : Fin k → R, Fin.append x y ∈ W} hπ
      = {y' : Fin ℓ → R' | ∃ x' : Fin k → R', Fin.append x' y' ∈ extension (R' := R') W hW} := by
  have hset : {y : Fin ℓ → R | ∃ x : Fin k → R, Fin.append x y ∈ W}
      = {y : Fin ℓ → R | ∃ x : Fin k → R,
          Fin.append y x ∈ {v : Fin (ℓ + k) → R | v ∘ blockSwap k ℓ ∈ W}} := by
    ext y; simp only [Set.mem_ofPred_eq, blockSwap_append]
  rw [ext_congr hπ (IsSemialgebraicSet.exists_append_right
        (IsSemialgebraicSet.comap (blockSwap k ℓ) hW)) hset,
      ext_exists_append (IsSemialgebraicSet.comap (blockSwap k ℓ) hW),
      ext_comap (blockSwap k ℓ) (blockSwap_injective k ℓ) hW]
  ext y'; simp only [Set.mem_ofPred_eq, blockSwap_append]

omit [IsRealClosed R] [IsRealClosed R'] [Algebra R R'] in
/-- The image of a function is the left projection of its graph. -/
theorem image_eq_proj_left {k ℓ : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (A : Set (Fin k → K)) (g : (Fin k → K) → (Fin ℓ → K)) :
    g '' A = {y : Fin ℓ → K | ∃ x : Fin k → K, Fin.append x y ∈ funGraph A g} := by
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, (append_mem_funGraph A g x (g x)).mpr ⟨hx, rfl⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨hxA, hgx⟩ := (append_mem_funGraph A g x y).mp hx
    exact ⟨x, hxA, hgx.symm⟩

/-- **BPR Exercise 2.17(a), surjectivity.** `f` is surjective onto `T` iff `Ext(f)` is
surjective onto `Ext(T)`. -/
theorem exercise_2_17a_surjOn {k ℓ : ℕ} {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {f' : (Fin k → R') → (Fin ℓ → R')}
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) (hf : IsSemialgebraicFunction S f)
    (hgraph : extension (R' := R') (funGraph S f) hf
      = funGraph (extension (R' := R') S hS) f') :
    Set.SurjOn f S T ↔ Set.SurjOn f' (extension (R' := R') S hS) (extension (R' := R') T hT) := by
  have hπsa : IsSemialgebraicSet {y : Fin ℓ → R | ∃ x : Fin k → R, Fin.append x y ∈ funGraph S f} :=
    IsSemialgebraicSet.exists_append_left hf
  rw [Set.SurjOn, Set.SurjOn, image_eq_proj_left S f, image_eq_proj_left,
    ext_subset_iff (R' := R') hT hπsa, ext_exists_append_left hf, ← hgraph]

/-- **`MapsTo` transfers.** -/
theorem ext_mapsTo_iff {k ℓ : ℕ} {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {f' : (Fin k → R') → (Fin ℓ → R')}
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) (hf : IsSemialgebraicFunction S f)
    (hgraph : extension (R' := R') (funGraph S f) hf
      = funGraph (extension (R' := R') S hS) f') :
    Set.MapsTo f S T ↔ Set.MapsTo f' (extension (R' := R') S hS) (extension (R' := R') T hT) := by
  have hπsa : IsSemialgebraicSet {y : Fin ℓ → R | ∃ x : Fin k → R, Fin.append x y ∈ funGraph S f} :=
    IsSemialgebraicSet.exists_append_left hf
  rw [Set.mapsTo_iff_image_subset, Set.mapsTo_iff_image_subset,
    image_eq_proj_left S f, image_eq_proj_left,
    ext_subset_iff (R' := R') hπsa hT, ext_exists_append_left hf, ← hgraph]

/-- **BPR Exercise 2.17(a), bijectivity.** `f` is bijective `S → T` iff `Ext(f)` is bijective
`Ext(S) → Ext(T)`. -/
theorem exercise_2_17a_bijOn {k ℓ : ℕ} {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {f' : (Fin k → R') → (Fin ℓ → R')}
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) (hf : IsSemialgebraicFunction S f)
    (hgraph : extension (R' := R') (funGraph S f) hf
      = funGraph (extension (R' := R') S hS) f') :
    Set.BijOn f S T ↔ Set.BijOn f' (extension (R' := R') S hS) (extension (R' := R') T hT) := by
  rw [Set.BijOn, Set.BijOn, ext_mapsTo_iff hS hT hf hgraph,
    exercise_2_17a_injOn hS hf hgraph, exercise_2_17a_surjOn hS hT hf hgraph]

end Azurite.BPR
