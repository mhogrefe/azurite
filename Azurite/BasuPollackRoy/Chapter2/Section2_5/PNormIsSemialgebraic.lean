import Azurite.BasuPollackRoy.Chapter2.Section2_5.EvenRootIsSemialgebraic
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83

/-! # The `p`-norm is a semialgebraic function

(Not in BPR.) For a rational `p ≥ 1`, the `p`-norm `x ↦ (∑ᵢ |xᵢ|^p)^{1/p}` is a semialgebraic
function `Rᵏ → R`. Each `|xᵢ|^p` is the nonnegative `2·q.den`-th root of `xᵢ^{2·q.num}`, and
the norm itself is a nonnegative `q.num`-th root, so the graph is the projection (dropping the
`k` auxiliary "component power" variables `uᵢ`) of the semialgebraic set
`{(x, y, u) | (∀ i, 0 ≤ uᵢ ∧ uᵢ^{2b} = xᵢ^{2a}) ∧ 0 ≤ y ∧ y^a = (∑ uᵢ)^b}`.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The nonnegative `m`-th root of `t` (`0` if `m = 0`). -/
noncomputable def nnroot (m : ℕ) (t : R) : R :=
  if hm : m = 0 then 0 else (exists_root_total hm t).choose

theorem nnroot_spec {m : ℕ} (hm : m ≠ 0) (t : R) (ht : 0 ≤ t) :
    0 ≤ nnroot m t ∧ (nnroot m t) ^ m = t := by
  rw [nnroot, dif_neg hm]; exact (exists_root_total hm t).choose_spec ht

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Finite intersections of semialgebraic sets are semialgebraic. -/
theorem IsSemialgebraicSet.iInter_finset {k : ℕ} {ι : Type*} (s : Finset ι)
    {S : ι → Set (Fin k → R)} (h : ∀ i ∈ s, IsSemialgebraicSet (S i)) :
    IsSemialgebraicSet (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ]
    exact .algebraic ⟨∅, by ext z; simp [Zer]⟩
  | @insert a s _ ih =>
    rw [Finset.set_biInter_insert]
    exact (h a (Finset.mem_insert_self a s)).inter
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The `p`-norm `(∑ᵢ |xᵢ|^p)^{1/p}`, built from nonnegative roots. -/
noncomputable def pNorm {k : ℕ} (p : ℚ) (x : Fin k → R) : R :=
  nnroot p.num.toNat ((∑ i, nnroot (2 * p.den) (x i ^ (2 * p.num.toNat))) ^ p.den)

/-- The `p`-norm as a function `Rᵏ → R`, valued in `Fin 1 → R`. -/
noncomputable def pNormFun {k : ℕ} (p : ℚ) : (Fin k → R) → (Fin 1 → R) :=
  fun x _ => pNorm p x

/-- **The `p`-norm `x ↦ (∑ᵢ |xᵢ|^p)^{1/p}` (`p ≥ 1` rational) is semialgebraic.** Its graph is
the projection (dropping the auxiliary component-power variables) of a semialgebraic set. -/
theorem pNormFun_isSemialgebraicFunction {k : ℕ} (p : ℚ) (hp : 1 ≤ p) :
    IsSemialgebraicFunction (Set.univ : Set (Fin k → R)) (pNormFun (R := R) p) := by
  have hp0 : (0 : ℚ) < p := lt_of_lt_of_le one_pos hp
  have ha : p.num.toNat ≠ 0 := by have : 0 < p.num := Rat.num_pos.mpr hp0; omega
  have hb2 : 2 * p.den ≠ 0 := by have := p.den_pos; omega
  -- abbreviations for the three coordinate blocks of `Fin ((k+1)+k)`: x (first k), y, u.
  set xc : Fin k → Fin ((k + 1) + k) := fun i => Fin.castAdd k (Fin.castAdd 1 i) with hxc
  set yc : Fin ((k + 1) + k) := Fin.castAdd k (Fin.natAdd k 0) with hyc
  set uc : Fin k → Fin ((k + 1) + k) := fun i => Fin.natAdd (k + 1) i with huc
  -- nonnegativity of `t ^ (2 a)`.
  have hpow2a : ∀ t : R, 0 ≤ t ^ (2 * p.num.toNat) := fun t => by
    rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  -- the auxiliary semialgebraic set `W`.
  set W : Set (Fin ((k + 1) + k) → R) :=
    {w | (∀ i, 0 ≤ w (uc i) ∧ (w (uc i)) ^ (2 * p.den) = (w (xc i)) ^ (2 * p.num.toNat)) ∧
      0 ≤ w yc ∧ (w yc) ^ p.num.toNat = (∑ i, w (uc i)) ^ p.den} with hW
  -- `append`-evaluation facts.
  have happ_uc : ∀ (q : Fin (k + 1) → R) (u : Fin k → R) (i : Fin k),
      Fin.append q u (uc i) = u i := fun q u i => by rw [huc, Fin.append_right]
  have happ_xc : ∀ (q : Fin (k + 1) → R) (u : Fin k → R) (i : Fin k),
      Fin.append q u (xc i) = q (Fin.castAdd 1 i) := fun q u i => by rw [hxc, Fin.append_left]
  have happ_yc : ∀ (q : Fin (k + 1) → R) (u : Fin k → R),
      Fin.append q u yc = q (Fin.natAdd k 0) := fun q u => by rw [hyc, Fin.append_left]
  -- `W` is semialgebraic.
  have hWsemialg : IsSemialgebraicSet W := by
    have h1 : IsSemialgebraicSet {w : Fin ((k + 1) + k) → R | ∀ i, 0 ≤ w (uc i)} := by
      have := IsSemialgebraicSet.iInter_finset (R := R) (Finset.univ : Finset (Fin k))
        (S := fun i => {w : Fin ((k + 1) + k) → R | MvPolynomial.eval w (X (uc i)) ≥ 0})
        (fun i _ => IsSemialgebraicSet.geZero _)
      convert this using 1
      ext w; simp [MvPolynomial.eval_X]
    have h2 : IsSemialgebraicSet
        {w : Fin ((k + 1) + k) → R | ∀ i, (w (uc i)) ^ (2 * p.den) = (w (xc i)) ^ (2 * p.num.toNat)} := by
      refine IsSemialgebraicSet.algebraic
        ⟨Finset.univ.image (fun i => X (uc i) ^ (2 * p.den) - X (xc i) ^ (2 * p.num.toNat)), ?_⟩
      ext w
      simp only [Zer, Set.mem_setOf_eq, Finset.mem_image, Finset.mem_univ, true_and,
        forall_exists_index, forall_apply_eq_imp_iff, map_sub, map_pow, MvPolynomial.eval_X,
        sub_eq_zero]
    have h3 : IsSemialgebraicSet {w : Fin ((k + 1) + k) → R | 0 ≤ w yc} := by
      have := IsSemialgebraicSet.geZero (R := R) (X yc)
      convert this using 1; ext w; simp [MvPolynomial.eval_X]
    have h4 : IsSemialgebraicSet
        {w : Fin ((k + 1) + k) → R | (w yc) ^ p.num.toNat = (∑ i, w (uc i)) ^ p.den} := by
      have := IsSemialgebraicSet.eqZero (R := R)
        (X yc ^ p.num.toNat - (∑ i, X (uc i)) ^ p.den)
      convert this using 1
      ext w
      simp only [Set.mem_setOf_eq, map_sub, map_pow, map_sum, MvPolynomial.eval_X, sub_eq_zero]
    have : W = ({w | ∀ i, 0 ≤ w (uc i)} ∩
        {w | ∀ i, (w (uc i)) ^ (2 * p.den) = (w (xc i)) ^ (2 * p.num.toNat)}) ∩
        ({w | 0 ≤ w yc} ∩ {w | (w yc) ^ p.num.toNat = (∑ i, w (uc i)) ^ p.den}) := by
      rw [hW]; ext w; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, forall_and]
    rw [this]
    exact (h1.inter h2).inter (h3.inter h4)
  -- the graph of the `p`-norm is the projection of `W`.
  have hgraph : funGraph (Set.univ : Set (Fin k → R)) (pNormFun p)
      = {q : Fin (k + 1) → R | ∃ u : Fin k → R, Fin.append q u ∈ W} := by
    ext q
    rw [mem_funGraph]
    simp only [Set.mem_univ, true_and, Set.mem_setOf_eq, hW, happ_uc, happ_xc, happ_yc]
    constructor
    · intro hq
      have hQ : q (Fin.natAdd k 0) = pNorm p (q ∘ Fin.castAdd 1) := by
        have := congrFun hq 0; simpa [pNormFun] using this
      refine ⟨fun i => nnroot (2 * p.den) ((q ∘ Fin.castAdd 1) i ^ (2 * p.num.toNat)), ?_, ?_, ?_⟩
      · intro i
        exact ⟨(nnroot_spec hb2 _ (hpow2a _)).1, (nnroot_spec hb2 _ (hpow2a _)).2⟩
      · rw [hQ, pNorm]
        exact (nnroot_spec ha _ (pow_nonneg
          (Finset.sum_nonneg fun i _ => (nnroot_spec hb2 _ (hpow2a _)).1) _)).1
      · rw [hQ, pNorm]
        exact (nnroot_spec ha _ (pow_nonneg
          (Finset.sum_nonneg fun i _ => (nnroot_spec hb2 _ (hpow2a _)).1) _)).2
    · rintro ⟨u, hu, hY0, hYpow⟩
      have huu : ∀ i, u i = nnroot (2 * p.den) ((q ∘ Fin.castAdd 1) i ^ (2 * p.num.toNat)) := by
        intro i
        refine (pow_left_inj₀ (hu i).1 (nnroot_spec hb2 _ (hpow2a _)).1 hb2).mp ?_
        rw [(hu i).2, (nnroot_spec hb2 _ (hpow2a _)).2]; rfl
      have hsum : (∑ i, u i)
          = ∑ i, nnroot (2 * p.den) ((q ∘ Fin.castAdd 1) i ^ (2 * p.num.toNat)) :=
        Finset.sum_congr rfl fun i _ => huu i
      have hpre : q (Fin.natAdd k 0) = pNorm p (q ∘ Fin.castAdd 1) := by
        rw [pNorm]
        refine (pow_left_inj₀ hY0 (nnroot_spec ha _ (pow_nonneg
          (Finset.sum_nonneg fun i _ => (nnroot_spec hb2 _ (hpow2a _)).1) _)).1 ha).mp ?_
        rw [hYpow, hsum, (nnroot_spec ha _ (pow_nonneg
          (Finset.sum_nonneg fun i _ => (nnroot_spec hb2 _ (hpow2a _)).1) _)).2]
      funext i; rw [Subsingleton.elim i 0]
      simpa [pNormFun] using hpre
  show IsSemialgebraicSet (funGraph (Set.univ : Set (Fin k → R)) (pNormFun p))
  rw [hgraph]
  exact hWsemialg.exists_append_right

end Azurite.BPR
