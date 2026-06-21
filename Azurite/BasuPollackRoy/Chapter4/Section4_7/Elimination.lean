import Azurite.BasuPollackRoy.Chapter4.Section4_4.Corollary_4_84
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.StdBasis

/-!
# BPR §4.7: the projective elimination theorem (affine-cone core)

This file proves the algebraic heart of BPR Theorem 4.103 ("the projection of an algebraic subset
of `ℙ_{k₁}(C) × ℙ_{k₂}(C)` is algebraic"): the *affine-cone elimination theorem*.

Let `C` be an algebraically closed field of characteristic zero. Write `D = C[Y_0, …, Y_{k₂}]` for
the polynomials in the second block of variables, and view a polynomial that is homogeneous in the
first block `X = (X_0, …, X_{k₁})` as an element `p i : D[X_0, …, X_{k₁}]` — an `X`-polynomial whose
coefficients are `Y`-polynomials. The hypotheses are exactly multihomogeneity:

* `hd i` : `p i` is homogeneous of degree `d i` in `X` (over `D`);
* `he i γ` : every `X`-coefficient of `p i` is homogeneous of degree `e i` in `Y`.

For `y : C^{k₂+1}`, write `P_i(X, y) = (map (eval y)) (p i) : C[X]`. The theorem produces a finite set
`Qs` of `Y`-homogeneous polynomials with
`{ y | ∀ Q ∈ Qs, Q(y) = 0 } = { y | ∃ x ≠ 0, ∀ i, P_i(x, y) = 0 }`,
i.e. the `Y`-locus where the `P_i(·, y)` have a common nonzero zero is cut out by the `Qs`.

The `Qs` are the maximal minors of the *Macaulay/elimination matrix* `𝓜` of the multiplication map
`(H_i) ↦ ∑ H_i P_i` on a single large degree `N`, with `N` chosen uniformly via the quantitative
Nullstellensatz (Corollary 4.84). This is BPR's `M_N(𝒫)` and its maximal minors `M_i(Y)`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

namespace Elimination

variable {C : Type*} [Field C]

/-- The (finite) index set of monomials of total degree `N` in `K + 1` variables: exponent vectors
`d : Fin (K+1) →₀ ℕ` with `d.degree = N`. This indexes a basis of the homogeneous component of
degree `N`. -/
def Mon (K N : ℕ) : Type := { d : Fin (K + 1) →₀ ℕ // d.degree = N }

namespace Mon

instance (K N : ℕ) : DecidableEq (Mon K N) := Subtype.instDecidableEq

/-- Every exponent in a degree-`N` monomial is at most `N`, so the index set embeds into
`Fin (K+1) → Fin (N+1)` and is finite. -/
instance (K N : ℕ) : Finite (Mon K N) := by
  apply Finite.of_injective
    (f := fun d : Mon K N => (fun i => (⟨min (d.1 i) N, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ :
      Fin (N + 1))))
  rintro ⟨d, hd⟩ ⟨d', hd'⟩ h
  apply Subtype.ext
  ext i
  have hi : d i ≤ N := hd ▸ Finsupp.le_degree i d
  have hi' : d' i ≤ N := hd' ▸ Finsupp.le_degree i d'
  have := congrFun h i
  simp only [Fin.mk.injEq] at this
  rw [Nat.min_eq_left hi, Nat.min_eq_left hi'] at this
  exact this

noncomputable instance (K N : ℕ) : Fintype (Mon K N) := Fintype.ofFinite _

/-- The underlying exponent vector of a monomial index. -/
abbrev exp {K N : ℕ} (m : Mon K N) : Fin (K + 1) →₀ ℕ := m.val

end Mon

/-- The uniform exponent bound from Corollary 4.84: applying the quantitative Nullstellensatz to a
coordinate `X_{i'}` (degree `1`) against a homogeneous system of `X`-degrees `≤ sup d` in `k₁ + 1`
variables, every `X_{i'}^{n} ` lies in the ideal for some `n` bounded by this. It is independent of
`y` and of the coordinate `i'`. -/
def bound (k₁ : ℕ) {s : ℕ} (d : Fin s → ℕ) : ℕ :=
  (2 * (max (Finset.univ.sup d) 1 + 1)) ^ (2 ^ (k₁ + 2))

/-- The single large degree `N` at which the elimination (Macaulay) matrix is formed: chosen so that
every monomial of degree `N` in `k₁ + 1` variables has some coordinate of exponent `≥ bound`,
hence is a multiple of some `X_{i'}^{n_{i'}}` with `n_{i'} ≤ bound`. -/
def bigDeg (k₁ : ℕ) {s : ℕ} (d : Fin s → ℕ) : ℕ := (k₁ + 1) * bound k₁ d

variable {k₁ k₂ s : ℕ} (d : Fin s → ℕ)
  (p : Fin s → MvPolynomial (Fin (k₁ + 1)) (MvPolynomial (Fin (k₂ + 1)) C))

/-- **The elimination matrix `𝓜`** (BPR's `M_N(𝒫)`), over `D = C[Y]`. Rows are indexed by the
degree-`N` monomials in `X`; columns by pairs `(i, β)` with `β` a degree-`(N - d i)` monomial in `X`.
The `(α, (i, β))` entry is the `X^α`-coefficient of `X^β · p i`, an element of `D` (a polynomial in
`Y`). The map `(H_i) ↦ ∑_i H_i · p_i` on degree-`N` homogeneous parts has this matrix in the
monomial bases. -/
noncomputable def elimMatrix :
    Matrix (Mon k₁ (bigDeg k₁ d)) (Σ i : Fin s, Mon k₁ (bigDeg k₁ d - d i))
      (MvPolynomial (Fin (k₂ + 1)) C) :=
  fun α c => (monomial c.2.val (1 : MvPolynomial (Fin (k₂ + 1)) C) * p c.1).coeff α.val

/-- The elimination matrix specialized at a point `y ∈ C^{k₂+1}`, over `C`: `M_N(y)`. -/
noncomputable def elimMatrixAt (y : Fin (k₂ + 1) → C) :
    Matrix (Mon k₁ (bigDeg k₁ d)) (Σ i : Fin s, Mon k₁ (bigDeg k₁ d - d i)) C :=
  (elimMatrix d p).map (eval y)

/-- `M_N(y)` is surjective. By the elimination argument this fails exactly when the `P_i(·, y)`
have a common nonzero zero in `C^{k₁+1}`. -/
def SurjAt (y : Fin (k₂ + 1) → C) : Prop :=
  Function.Surjective (elimMatrixAt d p y).mulVecLin

/-- A maximal minor of the elimination matrix, indexed by an embedding `f` of the (degree-`N`) rows
into the columns. An element of `D = C[Y]`; these are BPR's `M_i(Y)`. -/
noncomputable def Minor
    (f : Mon k₁ (bigDeg k₁ d) ↪ (Σ i : Fin s, Mon k₁ (bigDeg k₁ d - d i))) :
    MvPolynomial (Fin (k₂ + 1)) C :=
  ((elimMatrix d p).submatrix id f).det

/-- The finite set of maximal minors of the elimination matrix. -/
noncomputable def minors : Finset (MvPolynomial (Fin (k₂ + 1)) C) := by
  classical exact Finset.image (Minor d p) Finset.univ

/-- Specializing a minor at `y` is the determinant of the specialized submatrix. -/
theorem eval_minor (y : Fin (k₂ + 1) → C)
    (f : Mon k₁ (bigDeg k₁ d) ↪ (Σ i : Fin s, Mon k₁ (bigDeg k₁ d - d i))) :
    eval y (Minor d p f) = ((elimMatrixAt d p y).submatrix id f).det := by
  rw [Minor, elimMatrixAt, Matrix.submatrix_map]
  exact RingHom.map_det (eval y) _

/-- A linear map `A.mulVecLin` on `R → F` matrices is surjective iff some square submatrix obtained
by selecting `Fintype.card R` columns is invertible (its determinant is a unit). -/
private theorem surjective_mulVecLin_iff_exists_isUnit
    {R K : Type*} [Fintype R] [Fintype K] [DecidableEq R] [DecidableEq K]
    {F : Type*} [Field F] (A : Matrix R K F) :
    Function.Surjective A.mulVecLin ↔ ∃ f : R ↪ K, IsUnit (A.submatrix id ⇑f).det := by
  constructor
  · -- (⟹)
    intro hsurj
    have htop : Submodule.span F (Set.range A.col) = ⊤ := by
      rw [← Matrix.range_mulVecLin]
      exact LinearMap.range_eq_top.2 hsurj
    obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' F A.col
    have hsp' : ⊤ ≤ Submodule.span F (Set.range (A.col ∘ a)) := by
      rw [hsp, htop]
    -- `A.col ∘ a` is a basis of `R → F`, indexed by `κ`.
    let b : Module.Basis κ F (R → F) := Module.Basis.mk hli hsp'
    -- transport along the standard basis indexed by `R`
    let e : R ≃ κ := Module.Basis.indexEquiv (Pi.basisFun F R) b
    refine ⟨⟨a ∘ e, ha.comp e.injective⟩, ?_⟩
    set S : Matrix R R F := A.submatrix id (a ∘ e) with hS
    have hcol : S.col = (A.col ∘ a) ∘ e := by
      funext r i
      simp [hS, Matrix.col_apply, Matrix.submatrix_apply, Function.comp]
    have hliS : LinearIndependent F S.col := by
      rw [hcol]
      exact hli.comp e e.injective
    have hinj : Function.Injective S.mulVec := Matrix.mulVec_injective_iff.2 hliS
    have hSunit : IsUnit S := Matrix.mulVec_injective_iff_isUnit.1 hinj
    exact (Matrix.isUnit_iff_isUnit_det S).1 hSunit
  · -- (⟸)
    rintro ⟨f, hf⟩
    set S : Matrix R R F := A.submatrix id ⇑f with hS
    have hSunit : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).2 hf
    have hSsurj : Function.Surjective S.mulVec := Matrix.mulVec_surjective_iff_isUnit.2 hSunit
    have hStop : Submodule.span F (Set.range S.col) = ⊤ := by
      rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
      intro w; obtain ⟨v, hv⟩ := hSsurj w; exact ⟨v, hv⟩
    have hsub : Set.range S.col ⊆ Set.range A.col := by
      rintro v ⟨r, rfl⟩
      exact ⟨f r, by funext i; simp [hS, Matrix.col_apply, Matrix.submatrix_apply]⟩
    have hle : (⊤ : Submodule F (R → F)) ≤ Submodule.span F (Set.range A.col) := by
      rw [← hStop]; exact Submodule.span_mono hsub
    rw [← LinearMap.range_eq_top, Matrix.range_mulVecLin]
    exact top_le_iff.1 hle

/-- **Bridge C** (determinantal-rank characterization). `M_N(y)` is *not* surjective exactly when
every maximal minor vanishes at `y`. -/
theorem not_surjAt_iff_forall_minor (y : Fin (k₂ + 1) → C) :
    ¬ SurjAt d p y ↔ ∀ f, eval y (Minor d p f) = 0 := by
  rw [SurjAt, surjective_mulVecLin_iff_exists_isUnit, not_exists]
  refine forall_congr' fun f => ?_
  rw [eval_minor, isUnit_iff_ne_zero, not_not]

/-- Each `X`-degree `d i` is at most the uniform exponent bound. -/
theorem d_le_bound (i : Fin s) : d i ≤ bound k₁ d := by
  have h1 : d i ≤ Finset.univ.sup d := Finset.le_sup (Finset.mem_univ i)
  have h2 : Finset.univ.sup d ≤ max (Finset.univ.sup d) 1 := le_max_left _ _
  have h4 : 2 * (max (Finset.univ.sup d) 1 + 1) ≤ bound k₁ d := by
    rw [bound]; exact Nat.le_self_pow (by positivity) _
  omega

/-- The bound is at most the big degree `N = (k₁+1)·bound`. -/
theorem bound_le_bigDeg : bound k₁ d ≤ bigDeg k₁ d := by
  rw [bigDeg]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos k₁)

/-- Each `X`-degree `d i` is at most the big degree `N`. -/
theorem d_le_bigDeg (i : Fin s) : d i ≤ bigDeg k₁ d := (d_le_bound d i).trans (bound_le_bigDeg d)

/-- Specializing `p i` at `y` preserves homogeneity in `X`: `P_i(·, y) = map (eval y) (p i)` is
homogeneous of degree `d i`. -/
theorem map_eval_isHomogeneous (hd : ∀ i, (p i).IsHomogeneous (d i)) (y : Fin (k₂ + 1) → C)
    (i : Fin s) : (map (eval y) (p i)).IsHomogeneous (d i) := by
  intro c hc
  rw [coeff_map] at hc
  exact hd i fun h => hc (by rw [h, map_zero])

/-- The generator family for the degree-`N` image of the multiplication map: `gen (i, β) = X^β ·
P_i(·, y)`, a homogeneous polynomial of degree `N` in `X`. -/
noncomputable def gen (y : Fin (k₂ + 1) → C) :
    (Σ i : Fin s, Mon k₁ (bigDeg k₁ d - d i)) → MvPolynomial (Fin (k₁ + 1)) C :=
  fun cc => monomial cc.2.val 1 * map (eval y) (p cc.1)

/-- The specialized matrix entry is the `X^α`-coefficient of the generator `gen (i, β)`. -/
theorem elimMatrixAt_apply (y : Fin (k₂ + 1) → C) (α : Mon k₁ (bigDeg k₁ d))
    (cc : Σ i : Fin s, Mon k₁ (bigDeg k₁ d - d i)) :
    elimMatrixAt d p y α cc = (gen d p y cc).coeff α.val := by
  rw [elimMatrixAt, Matrix.map_apply, elimMatrix, gen, ← coeff_map, map_mul, map_monomial, map_one]

/-- **The coefficient dictionary.** Applying the specialized matrix `M_N(y)` to a coordinate vector
`c` computes the `X^α`-coefficient of the corresponding combination `∑ c_{i,β} · X^β · P_i(·, y)`. -/
theorem mulVecLin_eq (y : Fin (k₂ + 1) → C)
    (c : (Σ i : Fin s, Mon k₁ (bigDeg k₁ d - d i)) → C) (α : Mon k₁ (bigDeg k₁ d)) :
    (elimMatrixAt d p y).mulVecLin c α = (∑ cc, c cc • gen d p y cc).coeff α.val := by
  rw [Matrix.mulVecLin_apply, MvPolynomial.coeff_sum]
  have hL : (elimMatrixAt d p y).mulVec c α = ∑ cc, elimMatrixAt d p y α cc * c cc := rfl
  rw [hL]
  refine Finset.sum_congr rfl fun cc _ => ?_
  rw [elimMatrixAt_apply, coeff_smul, smul_eq_mul, mul_comm]

/-- Each generator `gen (i, β) = X^β · P_i(·, y)` is homogeneous of degree `N` in `X`. -/
theorem gen_isHomogeneous (hd : ∀ i, (p i).IsHomogeneous (d i)) (y : Fin (k₂ + 1) → C)
    (cc : Σ i : Fin s, Mon k₁ (bigDeg k₁ d - d i)) :
    (gen d p y cc).IsHomogeneous (bigDeg k₁ d) := by
  rw [gen]
  have h1 : (monomial cc.2.val (1 : C)).IsHomogeneous (bigDeg k₁ d - d cc.1) :=
    isHomogeneous_monomial _ cc.2.property
  have h2 := h1.mul (map_eval_isHomogeneous d p hd y cc.1)
  rwa [Nat.sub_add_cancel (d_le_bigDeg d cc.1)] at h2

/-- Any combination `∑ c_{i,β} · gen (i, β)` is homogeneous of degree `N`. -/
theorem sum_gen_isHomogeneous (hd : ∀ i, (p i).IsHomogeneous (d i)) (y : Fin (k₂ + 1) → C)
    (c : (Σ i : Fin s, Mon k₁ (bigDeg k₁ d - d i)) → C) :
    (∑ cc, c cc • gen d p y cc).IsHomogeneous (bigDeg k₁ d) := by
  rw [← mem_homogeneousSubmodule]
  apply Submodule.sum_mem
  intro cc _
  apply Submodule.smul_mem
  rw [mem_homogeneousSubmodule]
  exact gen_isHomogeneous d p hd y cc

/-- Two homogeneous polynomials of degree `N` that agree on every degree-`N` monomial are equal. -/
theorem homog_coeff_ext {N : ℕ} {H₁ H₂ : MvPolynomial (Fin (k₁ + 1)) C}
    (h₁ : H₁.IsHomogeneous N) (h₂ : H₂.IsHomogeneous N)
    (h : ∀ α : Mon k₁ N, H₁.coeff α.val = H₂.coeff α.val) : H₁ = H₂ := by
  ext m
  by_cases hm : m.degree = N
  · exact h ⟨m, hm⟩
  · rw [h₁.coeff_eq_zero hm, h₂.coeff_eq_zero hm]

/-- The homogeneous polynomial of degree `N` with prescribed coefficients `t` on the degree-`N`
monomials. -/
noncomputable def polyOfVec {N : ℕ} (t : Mon k₁ N → C) : MvPolynomial (Fin (k₁ + 1)) C :=
  ∑ α : Mon k₁ N, t α • monomial α.val 1

theorem coeff_polyOfVec {N : ℕ} (t : Mon k₁ N → C) (β : Mon k₁ N) :
    (polyOfVec t).coeff β.val = t β := by
  rw [polyOfVec, MvPolynomial.coeff_sum,
    Finset.sum_eq_single β
      (fun α _ hαβ => by
        rw [coeff_smul, coeff_monomial, if_neg (fun h => hαβ (Subtype.ext h)), smul_zero])
      (fun h => absurd (Finset.mem_univ β) h)]
  rw [coeff_smul, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]

theorem polyOfVec_isHomogeneous {N : ℕ} (t : Mon k₁ N → C) :
    (polyOfVec t).IsHomogeneous N := by
  rw [← mem_homogeneousSubmodule]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.smul_mem
  rw [mem_homogeneousSubmodule]
  exact isHomogeneous_monomial _ α.property

/-- **Bridge A** (coefficient↔polynomial dictionary). `M_N(y)` is surjective exactly when every
degree-`N` homogeneous polynomial in `X` lies in the `C`-span of the generators
`{X^β · P_i(·, y)}` — equivalently, in the degree-`N` part of the ideal generated by the
`P_i(·, y)`. -/
theorem surjAt_iff_homog_le (hd : ∀ i, (p i).IsHomogeneous (d i)) (y : Fin (k₂ + 1) → C) :
    SurjAt d p y ↔
      homogeneousSubmodule (Fin (k₁ + 1)) C (bigDeg k₁ d) ≤
        Submodule.span C (Set.range (gen d p y)) := by
  constructor
  · intro hsurj H hH
    rw [mem_homogeneousSubmodule] at hH
    obtain ⟨c, hc⟩ := hsurj (fun α => H.coeff α.val)
    have hGH : (∑ cc, c cc • gen d p y cc) = H := by
      apply homog_coeff_ext (sum_gen_isHomogeneous d p hd y c) hH
      intro α
      rw [← mulVecLin_eq]
      exact congrFun hc α
    rw [← hGH, Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, rfl⟩
  · intro hle t
    have hHmem : polyOfVec t ∈ Submodule.span C (Set.range (gen d p y)) :=
      hle (by rw [mem_homogeneousSubmodule]; exact polyOfVec_isHomogeneous t)
    rw [Submodule.mem_span_range_iff_exists_fun] at hHmem
    obtain ⟨c, hc⟩ := hHmem
    refine ⟨c, ?_⟩
    funext α
    rw [mulVecLin_eq, hc, coeff_polyOfVec]

/-- The uniform bound is positive. -/
theorem bound_pos : 0 < bound k₁ d := by rw [bound]; positivity

/-- The big degree `N` is positive. -/
theorem bigDeg_pos : 0 < bigDeg k₁ d := by
  rw [bigDeg]; exact Nat.mul_pos (Nat.succ_pos k₁) (bound_pos d)

/-- **Bridge B, easy direction.** If every degree-`N` homogeneous polynomial lies in the span of the
generators, then the only common zero of the `P_i(·, y)` is the origin: each coordinate power
`X_{i'}^N` lies in the ideal generated by the `P_i(·, y)`, so vanishes at any common zero. -/
theorem only_zero_of_homog_le (y : Fin (k₂ + 1) → C)
    (hle : homogeneousSubmodule (Fin (k₁ + 1)) C (bigDeg k₁ d) ≤
        Submodule.span C (Set.range (gen d p y)))
    (x : Fin (k₁ + 1) → C) (hx : ∀ i, eval x (map (eval y) (p i)) = 0) : x = 0 := by
  have hg : ∀ cc, eval x (gen d p y cc) = 0 := by
    intro cc; simp only [gen, map_mul, hx, mul_zero]
  funext i'
  show x i' = 0
  have hXmem : (X i' : MvPolynomial (Fin (k₁ + 1)) C) ^ (bigDeg k₁ d) ∈
      Submodule.span C (Set.range (gen d p y)) := by
    apply hle
    rw [mem_homogeneousSubmodule]
    have h : ((X i' : MvPolynomial (Fin (k₁ + 1)) C) ^ (bigDeg k₁ d)).IsHomogeneous
        (1 * bigDeg k₁ d) := (isHomogeneous_X C i').pow (bigDeg k₁ d)
    rwa [one_mul] at h
  rw [Submodule.mem_span_range_iff_exists_fun] at hXmem
  obtain ⟨c, hc⟩ := hXmem
  have hev : eval x ((X i' : MvPolynomial (Fin (k₁ + 1)) C) ^ (bigDeg k₁ d)) = 0 := by
    rw [← hc, map_sum]
    exact Finset.sum_eq_zero fun cc _ => by rw [smul_eq_C_mul, map_mul, hg cc, mul_zero]
  rw [map_pow, eval_X] at hev
  exact (pow_eq_zero_iff (bigDeg_pos d).ne').mp hev

/-- **Corollary 4.84, applied to a coordinate.** If the only common zero of the `P_j(·, y)` is the
origin, then for each coordinate `X_{i'}` there is `n ≤ bound` with `X_{i'}^n ∈ Ideal(P_j(·, y))`,
via homogeneous combinations. -/
theorem cor84_coord [IsAlgClosed C] [CharZero C] (hd : ∀ i, (p i).IsHomogeneous (d i))
    (y : Fin (k₂ + 1) → C)
    (hzero : ∀ x : Fin (k₁ + 1) → C, (∀ i, eval x (map (eval y) (p i)) = 0) → x = 0)
    (i' : Fin (k₁ + 1)) :
    ∃ (n : ℕ) (H : Fin s → MvPolynomial (Fin (k₁ + 1)) C),
      n ≤ bound k₁ d ∧ (∀ j, (H j).IsHomogeneous (n - d j)) ∧ (∀ j, d j ≤ n) ∧
        (X i') ^ n = ∑ j, H j * map (eval y) (p j) := by
  have hvanish : ∀ x : Fin (k₁ + 1) → C,
      (∀ j, aeval x (map (eval y) (p j)) = 0) →
        aeval x (X i' : MvPolynomial (Fin (k₁ + 1)) C) = 0 := by
    intro x hx
    rw [aeval_X, hzero x hx]; rfl
  obtain ⟨n, H, hn_bd, hH_hom, hd_le, hrel⟩ :=
    corollary_4_84 (C := C) (Finset.univ.sup d) (fun j => map (eval y) (p j)) d
      (fun j => map_eval_isHomogeneous d p hd y j) (fun j => Finset.le_sup (Finset.mem_univ j))
      (X i') 1 one_pos (isHomogeneous_X C i') hvanish
  refine ⟨n, H, hn_bd, fun j => ?_, fun j => ?_, ?_⟩
  · have := hH_hom j; rwa [mul_one] at this
  · have := hd_le j; rwa [mul_one] at this
  · rw [hrel]

/-- A homogeneous polynomial `Q` of degree `N - d j` times `P_j(·, y)` lies in the span of the
generators: expand `Q` into degree-`(N - d j)` monomials, each `X^β · P_j(·, y)` being a generator. -/
theorem poly_mul_Pval_mem (y : Fin (k₂ + 1) → C) (Q : MvPolynomial (Fin (k₁ + 1)) C) (j : Fin s)
    (hQ : Q.IsHomogeneous (bigDeg k₁ d - d j)) :
    Q * map (eval y) (p j) ∈ Submodule.span C (Set.range (gen d p y)) := by
  rw [Q.as_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro β hβ
  have hβdeg : β.degree = bigDeg k₁ d - d j := by
    rw [Finsupp.degree_eq_weight_one]; exact hQ (mem_support_iff.mp hβ)
  have heq : (monomial β (Q.coeff β) : MvPolynomial (Fin (k₁ + 1)) C) * map (eval y) (p j)
      = Q.coeff β • gen d p y ⟨j, ⟨β, hβdeg⟩⟩ := by
    simp only [gen]
    rw [show (monomial β (Q.coeff β) : MvPolynomial (Fin (k₁ + 1)) C)
        = Q.coeff β • monomial β 1 from by rw [smul_monomial, smul_eq_mul, mul_one], smul_mul_assoc]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, ⟨β, hβdeg⟩⟩, rfl⟩)

/-- **The key step.** If the only common zero is the origin, every degree-`N` monomial `X^dd` lies in
the span of the generators. Pigeonhole gives a coordinate `i'` with `dd_{i'} ≥ bound ≥ n_{i'}`, so
`X^dd = X^{dd'} · X_{i'}^{n_{i'}} = ∑_j (X^{dd'} H_j) · P_j(·, y)`, each term a span member. -/
theorem key [IsAlgClosed C] [CharZero C] (hd : ∀ i, (p i).IsHomogeneous (d i))
    (y : Fin (k₂ + 1) → C)
    (hzero : ∀ x : Fin (k₁ + 1) → C, (∀ i, eval x (map (eval y) (p i)) = 0) → x = 0)
    (dd : Fin (k₁ + 1) →₀ ℕ) (hdeg : dd.degree = bigDeg k₁ d) :
    monomial dd (1 : C) ∈ Submodule.span C (Set.range (gen d p y)) := by
  have hsum : ∑ _i : Fin (k₁ + 1), bound k₁ d ≤ ∑ i : Fin (k₁ + 1), dd i := by
    have e1 : ∑ _i : Fin (k₁ + 1), bound k₁ d = bigDeg k₁ d := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, bigDeg]
    have e2 : ∑ i : Fin (k₁ + 1), dd i = bigDeg k₁ d := by rw [← Finsupp.degree_eq_sum, hdeg]
    exact (e1.trans e2.symm).le
  obtain ⟨i', _, hi'⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  obtain ⟨n, H, hn_bd, hH_hom, hd_le, hrel⟩ := cor84_coord d p hd y hzero i'
  have hn_le : n ≤ dd i' := le_trans hn_bd hi'
  have hsingle_le : Finsupp.single i' n ≤ dd := Finsupp.single_le_iff.mpr hn_le
  set dd' := dd - Finsupp.single i' n with hdd'
  have hsplit : dd = dd' + Finsupp.single i' n := by rw [hdd', tsub_add_cancel_of_le hsingle_le]
  have hmon : (monomial dd (1 : C)) = monomial dd' 1 * (X i') ^ n := by
    rw [hsplit, monomial_add_single]
  have hadd : (dd' + Finsupp.single i' n).degree = dd'.degree + n := by
    simp only [Finsupp.degree_eq_sum, Finsupp.add_apply, Finset.sum_add_distrib]
    congr 1
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_single]
  have hdd'deg : dd'.degree + n = bigDeg k₁ d := by rw [← hadd, ← hsplit, hdeg]
  rw [hmon, hrel, Finset.mul_sum]
  apply Submodule.sum_mem
  intro j _
  rw [← mul_assoc]
  have hdj : d j ≤ n := hd_le j
  have hQ : (monomial dd' (1 : C) * H j).IsHomogeneous (bigDeg k₁ d - d j) := by
    have h1 : (monomial dd' (1 : C)).IsHomogeneous dd'.degree := isHomogeneous_monomial _ rfl
    have h2 := h1.mul (hH_hom j)
    rwa [show dd'.degree + (n - d j) = bigDeg k₁ d - d j from by omega] at h2
  exact poly_mul_Pval_mem d p y _ j hQ

/-- **Bridge B, hard direction** (Corollary 4.84). If the only common zero of the `P_i(·, y)` is the
origin, then every degree-`N` homogeneous polynomial lies in the span of the generators. -/
theorem homog_le_of_only_zero [IsAlgClosed C] [CharZero C] (hd : ∀ i, (p i).IsHomogeneous (d i))
    (y : Fin (k₂ + 1) → C)
    (hzero : ∀ x : Fin (k₁ + 1) → C, (∀ i, eval x (map (eval y) (p i)) = 0) → x = 0) :
    homogeneousSubmodule (Fin (k₁ + 1)) C (bigDeg k₁ d) ≤
      Submodule.span C (Set.range (gen d p y)) := by
  intro H hH
  rw [mem_homogeneousSubmodule] at hH
  rw [H.as_sum]
  apply Submodule.sum_mem
  intro dd hdd
  have hdeg : dd.degree = bigDeg k₁ d := by
    rw [Finsupp.degree_eq_weight_one]; exact hH (mem_support_iff.mp hdd)
  rw [show (monomial dd (H.coeff dd) : MvPolynomial (Fin (k₁ + 1)) C) = H.coeff dd • monomial dd 1
      from by rw [smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (key d p hd y hzero dd hdeg)

/-- **Bridges A + B** (coefficient translation + Corollary 4.84). `M_N(y)` is *not* surjective
exactly when the `P_i(·, y)` have a common nonzero zero in `C^{k₁+1}`. -/
theorem not_surjAt_iff_common_zero [IsAlgClosed C] [CharZero C]
    (hd : ∀ i, (p i).IsHomogeneous (d i)) (y : Fin (k₂ + 1) → C) :
    ¬ SurjAt d p y ↔
      ∃ x : Fin (k₁ + 1) → C, x ≠ 0 ∧ ∀ i, eval x (map (eval y) (p i)) = 0 := by
  rw [surjAt_iff_homog_le d p hd y,
    show (homogeneousSubmodule (Fin (k₁ + 1)) C (bigDeg k₁ d) ≤
          Submodule.span C (Set.range (gen d p y)))
        ↔ (∀ x : Fin (k₁ + 1) → C, (∀ i, eval x (map (eval y) (p i)) = 0) → x = 0) from
      ⟨only_zero_of_homog_le d p y, homog_le_of_only_zero d p hd y⟩]
  push Not
  constructor
  · rintro ⟨x, hx, hne⟩; exact ⟨x, hne, hx⟩
  · rintro ⟨x, hne, hx⟩; exact ⟨x, hx, hne⟩

/-- Every entry of the elimination matrix is homogeneous in `Y` of degree `e (c.1)`. -/
theorem elimMatrix_isHomogeneous (e : Fin s → ℕ)
    (he : ∀ i γ, ((p i).coeff γ).IsHomogeneous (e i))
    (α : Mon k₁ (bigDeg k₁ d)) (c : Σ i : Fin s, Mon k₁ (bigDeg k₁ d - d i)) :
    (elimMatrix d p α c).IsHomogeneous (e c.1) := by
  rw [elimMatrix, coeff_monomial_mul']
  split_ifs with h
  · rw [one_mul]
    exact he c.1 _
  · exact isHomogeneous_zero _ _ _

/-- Each maximal minor is homogeneous in `Y`: column `(i, β)` contributes entries homogeneous of
degree `e i`, so a fixed maximal minor is homogeneous of degree `∑` of the selected columns' `e i`. -/
theorem minors_homogeneous (e : Fin s → ℕ)
    (he : ∀ i γ, ((p i).coeff γ).IsHomogeneous (e i)) :
    ∀ Q ∈ minors d p, ∃ m, Q.IsHomogeneous m := by
  classical
  rw [minors]
  simp only [Finset.forall_mem_image, Finset.mem_univ, forall_true_left]
  intro f
  refine ⟨∑ j : Mon k₁ (bigDeg k₁ d), e (f j).1, ?_⟩
  rw [Minor, Matrix.det_apply]
  rw [← mem_homogeneousSubmodule]
  apply Submodule.sum_mem
  intro σ _
  apply zsmul_mem
  rw [mem_homogeneousSubmodule]
  apply IsHomogeneous.prod
  intro j _
  rw [Matrix.submatrix_apply, id]
  exact elimMatrix_isHomogeneous d p e he _ _

/-- Unfold `minors` as a `∀` over embeddings. -/
theorem forall_mem_minors_iff (y : Fin (k₂ + 1) → C) :
    (∀ Q ∈ minors d p, eval y Q = 0) ↔ ∀ f, eval y (Minor d p f) = 0 := by
  classical
  rw [minors]
  simp only [Finset.forall_mem_image, Finset.mem_univ, forall_true_left]

/-- **The affine-cone elimination theorem** (algebraic core of BPR Theorem 4.103). Over an
algebraically closed field of characteristic zero, the `Y`-locus where the homogeneous (in `X`)
system `p_i(·, y)` has a common nonzero zero is cut out by finitely many `Y`-homogeneous polynomials
(the maximal minors of the elimination matrix). -/
theorem elimination [IsAlgClosed C] [CharZero C]
    (hd : ∀ i, (p i).IsHomogeneous (d i)) (e : Fin s → ℕ)
    (he : ∀ i γ, ((p i).coeff γ).IsHomogeneous (e i)) :
    ∃ Qs : Finset (MvPolynomial (Fin (k₂ + 1)) C),
      (∀ Q ∈ Qs, ∃ m, Q.IsHomogeneous m) ∧
        ∀ y : Fin (k₂ + 1) → C,
          (∀ Q ∈ Qs, eval y Q = 0) ↔
            ∃ x : Fin (k₁ + 1) → C, x ≠ 0 ∧ ∀ i, eval x (map (eval y) (p i)) = 0 :=
  ⟨minors d p, minors_homogeneous d p e he, fun y => by
    rw [forall_mem_minors_iff, ← not_surjAt_iff_forall_minor, not_surjAt_iff_common_zero d p hd y]⟩

end Elimination

end Azurite.BPR.Chapter4
