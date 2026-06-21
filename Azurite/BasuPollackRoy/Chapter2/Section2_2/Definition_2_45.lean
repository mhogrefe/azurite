import Azurite.BasuPollackRoy.Chapter2.Section2_2.Definition_2_45.Internal

/-!
# BPR Definition 2.45: Virtual Roots

The **virtual roots** of a polynomial `P ∈ R[X]` of degree `p` are defined
inductively on `p`:

- If `p = 0`, `P` has no virtual roots.
- Otherwise, let `y_1 ≤ … ≤ y_{p−1}` be the virtual roots of `P'`. Partition
  the real line into `I_1 = (−∞, y_1]`, `I_i = [y_{i−1}, y_i]` for
  `2 ≤ i ≤ p − 1`, and `I_p = [y_{p−1}, +∞)`. The virtual root `x_i ∈ I_i`
  is the unique point where `|P|` attains its minimum on `I_i`.

The virtual roots are produced by a structurally recursive subtype-valued
helper `virtualRootsAux`, and the five defining properties are exposed
individually:

1. `length_virtualRoots`
2. `sorted_virtualRoots`
3. `signConstantOnGaps_virtualRoots`
4. `interlaced_virtualRoots` (when `derivative P ≠ 0`)
5. `argminPartition_virtualRoots` (when `derivative P ≠ 0`)

Uniqueness is expressed via unbundled characterisations.

The underlying structural definitions (`Interlaced`, `SignConstantOnGaps`,
`IsArgminAbsOn`, `ArgminPartition`, `ArgminPartitionFrom`) and all supporting
machinery live in the sub-namespace `Azurite.BPR.VirtualRoots.Internal` and
are re-exported here.
-/

namespace Azurite.BPR.VirtualRoots

open Polynomial Azurite.BPR Azurite.BPR.Proposition2_21 Azurite.BPR.Proposition2_27

export Internal
  (Interlaced SignConstantOnGaps IsArgminAbsOn ArgminPartition ArgminPartitionFrom)

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Recursive construction of `virtualRoots` -/

/-- Recursive construction of `virtualRoots` on `P.natDegree`. Returns a
    subtype carrying the internal `IsVirtualRootsList` witness together with
    the derivative interlacing bundle. This is a private implementation
    detail: the public API unpacks the five properties from `.property`. -/
private noncomputable def virtualRootsAux
    (hIVP : HasIntermediateValueProperty R) :
    ∀ (n : ℕ) (P : R[X]), P.natDegree = n → P ≠ 0 →
      { xs : List R //
        Internal.IsVirtualRootsList P xs ∧
          (derivative P = 0 ∨
            ∃ ys : List R,
              Internal.IsVirtualRootsList (derivative P) ys ∧
              Interlaced xs ys ∧
              ArgminPartition P xs ys) }
  | 0, P, hn, hP =>
      ⟨[], Internal.isVirtualRootsList_nil_of_natDegree_zero hn hP,
        Or.inl (Polynomial.derivative_of_natDegree_zero hn)⟩
  | n + 1, P, hn, hP => by
      have hdeg_pos : 0 < P.natDegree := by rw [hn]; omega
      have hdP_deg : (derivative P).natDegree = n := by
        have h : (derivative P).degree = (P.natDegree - 1 : ℕ) :=
          Polynomial.degree_derivative hdeg_pos.ne'
        have h' : (derivative P).natDegree = P.natDegree - 1 :=
          Polynomial.natDegree_eq_of_degree_eq_some h
        rw [h', hn]; omega
      have hdP_ne : derivative P ≠ 0 := by
        intro heq
        have := Polynomial.derivative_eq_zero.mp heq
        omega
      let hrec := virtualRootsAux hIVP n (derivative P) hdP_deg hdP_ne
      let ys : List R := hrec.val
      have hys : Internal.IsVirtualRootsList (derivative P) ys :=
        hrec.property.1
      have hlen : ys.length + 1 = P.natDegree := by
        rw [hys.length_eq, hdP_deg, hn]
      have hex :=
        Internal.exists_virtualRootsList_of_ys_general
          hIVP hdeg_pos hys hlen
      let xs : List R := hex.choose
      have hxs_and : Internal.IsVirtualRootsList P xs ∧
          Interlaced xs ys := hex.choose_spec
      have hxs : Internal.IsVirtualRootsList P xs := hxs_and.1
      have hxs_aux :
          Internal.IsVirtualRootsListAux (n + 1) P xs := by
        have h : Internal.IsVirtualRootsListAux P.natDegree P xs := hxs
        rw [hn] at h; exact h
      refine ⟨xs, hxs, ?_⟩
      rcases hxs_aux.argmin_wit_succ with hnil | hex2
      · exfalso
        have := hxs.length_eq
        rw [hnil, hn] at this
        simp at this
      · right
        refine ⟨ys, hys, ?_⟩
        have hys'_spec :
            Internal.IsVirtualRootsList (derivative P) hex2.choose := by
          unfold Internal.IsVirtualRootsList
          rw [hdP_deg]; exact hex2.choose_spec.1
        have hys_eq : ys = hex2.choose :=
          Internal.IsVirtualRootsList.unique hIVP hys hys'_spec
        refine ⟨?_, ?_⟩
        · rw [hys_eq]; exact hex2.choose_spec.2.1
        · rw [hys_eq]; exact hex2.choose_spec.2.2

/-- The **virtual roots** of a nonzero polynomial `P`, as a list, produced by
    an explicit recursion on `P.natDegree`. -/
noncomputable def virtualRoots (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) : List R :=
  (virtualRootsAux hIVP P.natDegree P rfl hP).val

/-- Internal: the bundled witness attached to `virtualRoots`. -/
private theorem virtualRoots_property (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) :
    Internal.IsVirtualRootsList P (virtualRoots hIVP hP) ∧
      (derivative P = 0 ∨
        ∃ ys : List R,
          Internal.IsVirtualRootsList (derivative P) ys ∧
          Interlaced (virtualRoots hIVP hP) ys ∧
          ArgminPartition P (virtualRoots hIVP hP) ys) :=
  (virtualRootsAux hIVP P.natDegree P rfl hP).property

/-! ### The five defining properties -/

/-- **Property 1.** The number of virtual roots equals `natDegree P`. -/
theorem length_virtualRoots (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) : (virtualRoots hIVP hP).length = P.natDegree :=
  (virtualRoots_property hIVP hP).1.length_eq

/-- **Property 2.** The virtual roots are sorted. -/
theorem sorted_virtualRoots (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) : (virtualRoots hIVP hP).Pairwise (· ≤ ·) :=
  (virtualRoots_property hIVP hP).1.sorted

/-- **Property 3.** `P` has constant sign on each gap between consecutive
    virtual roots. -/
theorem signConstantOnGaps_virtualRoots (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) : SignConstantOnGaps P (virtualRoots hIVP hP) :=
  (virtualRoots_property hIVP hP).1.sign_const

/-- **Property 4 (interlacing).** When `derivative P ≠ 0`, the virtual roots
    of `P` and of `derivative P` interlace. -/
theorem interlaced_virtualRoots (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (hdP : derivative P ≠ 0) :
    Interlaced (virtualRoots hIVP hP) (virtualRoots hIVP hdP) := by
  rcases (virtualRoots_property hIVP hP).2 with heq | ⟨ys, hys, hinter, _⟩
  · exact absurd heq hdP
  · have hys_eq : ys = virtualRoots hIVP hdP :=
      Internal.IsVirtualRootsList.unique hIVP hys
        (virtualRoots_property hIVP hdP).1
    rw [← hys_eq]; exact hinter

/-- **Property 5 (argmin partition).** When `derivative P ≠ 0`, each virtual
    root of `P` minimises `|P|` on its designated interval. -/
theorem argminPartition_virtualRoots (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (hdP : derivative P ≠ 0) :
    ArgminPartition P (virtualRoots hIVP hP) (virtualRoots hIVP hdP) := by
  rcases (virtualRoots_property hIVP hP).2 with heq | ⟨ys, hys, _, hargmin⟩
  · exact absurd heq hdP
  · have hys_eq : ys = virtualRoots hIVP hdP :=
      Internal.IsVirtualRootsList.unique hIVP hys
        (virtualRoots_property hIVP hdP).1
    rw [← hys_eq]; exact hargmin

/-! ### Uniqueness -/

/-- **Uniqueness from properties (derivative nonzero case).** Any list `xs`
    satisfying the five defining properties of virtual roots equals
    `virtualRoots hIVP hP`. -/
theorem virtualRoots_eq_of_properties_of_derivative_ne_zero
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (hdP : derivative P ≠ 0) {xs : List R}
    (_hlen : xs.length = P.natDegree)
    (_hsort : xs.Pairwise (· ≤ ·))
    (_hsign : SignConstantOnGaps P xs)
    (hinter : Interlaced xs (virtualRoots hIVP hdP))
    (hargmin : ArgminPartition P xs (virtualRoots hIVP hdP)) :
    xs = virtualRoots hIVP hP := by
  have hdeg : P.natDegree ≠ 0 := fun h =>
    hdP (Polynomial.derivative_of_natDegree_zero h)
  obtain ⟨m, hm⟩ : ∃ m, P.natDegree = m + 1 := Nat.exists_eq_succ_of_ne_zero hdeg
  have hdP_deg : (derivative P).natDegree = m := by
    have h1 : (derivative P).degree = (P.natDegree - 1 : ℕ) :=
      Polynomial.degree_derivative (p := P) (by rw [hm]; omega)
    have h2 : (derivative P).natDegree = P.natDegree - 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some h1
    rw [h2, hm]; omega
  have hys_spec :
      Internal.IsVirtualRootsList (derivative P) (virtualRoots hIVP hdP) :=
    (virtualRoots_property hIVP hdP).1
  have hys_aux :
      Internal.IsVirtualRootsListAux m (derivative P)
        (virtualRoots hIVP hdP) := by
    unfold Internal.IsVirtualRootsList at hys_spec
    rw [hdP_deg] at hys_spec; exact hys_spec
  have hxs_spec : Internal.IsVirtualRootsList P xs := by
    unfold Internal.IsVirtualRootsList
    rw [hm]
    refine ⟨_hlen, _hsort, _hsign, Or.inr ⟨virtualRoots hIVP hdP,
      hys_aux, hinter, hargmin⟩⟩
  have hnew_spec :
      Internal.IsVirtualRootsList P (virtualRoots hIVP hP) :=
    (virtualRoots_property hIVP hP).1
  exact Internal.IsVirtualRootsList.unique hIVP hxs_spec hnew_spec

/-- **Uniqueness from properties (zero-degree case).** When `P.natDegree = 0`,
    `virtualRoots hIVP hP = []`. -/
theorem virtualRoots_eq_nil_of_natDegree_zero
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (hn : P.natDegree = 0) :
    virtualRoots hIVP hP = [] := by
  have hlen : (virtualRoots hIVP hP).length = 0 := by
    rw [length_virtualRoots, hn]
  exact List.length_eq_zero_iff.mp hlen

/-- **Uniqueness from properties (derivative zero case).** When
    `derivative P = 0`, any list of the correct length is forced to be `[]`
    by the degree constraint. -/
theorem virtualRoots_eq_of_properties_of_derivative_zero
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (hdP : derivative P = 0) {xs : List R}
    (hlen : xs.length = P.natDegree) :
    xs = virtualRoots hIVP hP := by
  have hn : P.natDegree = 0 := by
    by_contra hne
    have : derivative P ≠ 0 := by
      intro heq
      have := Polynomial.derivative_eq_zero.mp heq
      exact hne this
    exact this hdP
  have hxs_nil : xs = [] := List.length_eq_zero_iff.mp (by rw [hlen, hn])
  rw [hxs_nil, virtualRoots_eq_nil_of_natDegree_zero hIVP hP hn]

/-! ### Iterated derivative -/

/-- **BPR unnumbered corollary.** Every virtual root of `P` is a root of some
    iterated derivative of `P`. -/
theorem virtualRoots_root_of_derivative (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) :
    ∀ x ∈ virtualRoots hIVP hP, ∃ k : ℕ, ((derivative)^[k] P).eval x = 0 := by
  intro x _
  refine ⟨P.natDegree + 1, ?_⟩
  rw [Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)]
  simp

/-! ### Virtual multiplicity -/

/-- The **virtual multiplicity** of `x` with respect to `P`, denoted `v(P, x)`
    in BPR: the number of times `x` appears in the virtual roots list. -/
noncomputable def virtualMultiplicity (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (x : R) : ℕ :=
  (virtualRoots hIVP hP).count x

/-- If `x` is not a virtual root of `P`, its virtual multiplicity is zero. -/
theorem virtualMultiplicity_eq_zero_of_not_mem
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) {x : R} (hx : x ∉ virtualRoots hIVP hP) :
    virtualMultiplicity hIVP hP x = 0 :=
  List.count_eq_zero.mpr hx

/-! ### Unnumbered corollaries of the virtual multiplicity definition

The following four results record how the virtual multiplicity at a point `c`
relates to the virtual multiplicity at `c` for the derivative `P'`. BPR
collects them as immediate consequences of the definition rather than
numbering them.

#### Erratum: BPR Definition 2.45, "moreover" clause on virtual multiplicity

Following Definition 2.45, BPR asserts:

> Note that if `x` is a virtual root of `P′` with virtual multiplicity `ν`
> with respect to `P`, the virtual multiplicity of `x` with respect to `P′`
> can only be `ν`, `ν + 1` or `ν − 1`. **Moreover, if `x` is a root of `P′`,
> the virtual multiplicity of `x` with respect to `P′` is necessarily
> `ν + 1`.**

The first claim (the three-way case split) is correct and formalized as
`virtualMultiplicity_derivative_cases` below. The "moreover" refinement,
however, is **false** in general — there is an unnoted counterexample:

**Counterexample:** Take `P = X² + 1` over any real closed field, `x = 0`.
- `P′ = 2X`, so `virtualRoots(P′) = [0]` and `x = 0` is a virtual root of
  `P′` satisfying `P′.eval 0 = 0`.
- `virtualRoots(X² + 1) = [0, 0]`: this list is forced, since any virtual
  roots list of `X² + 1` must have length `2`, every entry must be a root
  of some iterated derivative (only candidate: `0`, from `P′ = 2X`), and
  `SignConstantOnGaps` is trivially satisfied since `X² + 1 > 0` everywhere.
- Hence `ν = v(P, 0) = 2` and `v(P′, 0) = 1`, giving `v(P′, 0) = ν − 1`,
  not `ν + 1`.

The phenomenon is that a polynomial with no real roots can still have
"spurious" virtual roots — argmins of `|P|` on each interval where `P`
does not vanish — and `X² + 1` stacks two such argmins at the same point.
The extra hypothesis "`x` is not a root of `P`" does not rescue the claim
(the counterexample above already satisfies `P.eval 0 = 1 ≠ 0`).

Because the claim as stated is not a theorem of the real closed field
axioms, we do not formalize it. Downstream uses in BPR should instead rely
on the correct three-way bound (`virtualMultiplicity_derivative_cases`). -/

/-- **Trichotomy bound.** The virtual multiplicities of `x` with respect
    to `P` and `P'` differ by at most `1`: `ν(P', x) ∈ {ν(P, x) − 1, ν(P, x),
    ν(P, x) + 1}`. -/
theorem virtualMultiplicity_derivative_cases
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (hdP : derivative P ≠ 0) (x : R) :
    (virtualRoots hIVP hdP).count x + 1 = virtualMultiplicity hIVP hP x ∨
    (virtualRoots hIVP hdP).count x = virtualMultiplicity hIVP hP x ∨
    (virtualRoots hIVP hdP).count x = virtualMultiplicity hIVP hP x + 1 := by
  have hinter := interlaced_virtualRoots hIVP hP hdP
  have hsort := sorted_virtualRoots hIVP hdP
  have hbound := Internal.Interlaced.count_diff_le_one hinter hsort x
  unfold virtualMultiplicity
  omega

/-- **Root case.** If `x` is a root of `P`, then the virtual multiplicity of
    `x` with respect to `P` exceeds the virtual multiplicity of `x` with
    respect to `P'` by exactly `1`. -/
theorem virtualMultiplicity_derivative_of_root
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (hdP : derivative P ≠ 0) {x : R} (hx : P.eval x = 0) :
    (virtualRoots hIVP hdP).count x + 1 = virtualMultiplicity hIVP hP x := by
  have hinter := interlaced_virtualRoots hIVP hP hdP
  have hargmin := argminPartition_virtualRoots hIVP hP hdP
  have hys_sort := sorted_virtualRoots hIVP hdP
  have hxs_sg := signConstantOnGaps_virtualRoots hIVP hP
  have hys_sg := signConstantOnGaps_virtualRoots hIVP hdP
  exact Internal.count_eq_of_root hIVP hinter hys_sort hargmin
    hxs_sg hys_sg hx

/-- **No-derivative-root case.** If `x` is not a root of any iterated
    derivative `P^{(k)}` (`k ∈ ℕ`), then its virtual multiplicity with respect
    to `P` is zero. Contrapositively, every virtual root of `P` is a root of
    some iterated derivative — this is `virtualRoots_root_of_derivative`. -/
theorem virtualMultiplicity_eq_zero_of_no_derivative_root
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) {x : R}
    (h : ∀ k : ℕ, ((derivative)^[k] P).eval x ≠ 0) :
    virtualMultiplicity hIVP hP x = 0 := by
  apply virtualMultiplicity_eq_zero_of_not_mem
  intro hx
  obtain ⟨k, hk⟩ := virtualRoots_root_of_derivative hIVP hP x hx
  exact h k hk

/-- **Non-root sign formula.** If `P.eval c ≠ 0`, let `ν :=
    (derivative P).rootMultiplicity c`. The difference `v(P, c) - v(P', c)`
    (which lies in `{-1, 0, 1}` by the trichotomy) is determined by the
    parity of `ν` and, when `ν` is odd, the sign of `P(c) · P^{(ν+1)}(c)`:

    * `ν` even → `v(P, c) = v(P', c)`.
    * `ν` odd and `P(c) · P^{(ν+1)}(c) > 0` → `v(P, c) = v(P', c) + 1`.
    * `ν` odd and `P(c) · P^{(ν+1)}(c) < 0` → `v(P', c) = v(P, c) + 1`.

    Combined with `virtualMultiplicity_derivative_of_root` (case `P(c) = 0`),
    this gives a complete characterisation of how `v(·, c)` changes upon
    differentiation. -/
theorem virtualMultiplicity_diff_of_not_root
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (hdP : derivative P ≠ 0)
    {c : R} (hPc : P.eval c ≠ 0) :
    (virtualMultiplicity hIVP hP c : ℤ) -
        ((virtualRoots hIVP hdP).count c : ℤ) =
      if Even ((derivative P).rootMultiplicity c) then 0
      else if 0 < P.eval c *
          ((⇑derivative)^[(derivative P).rootMultiplicity c + 1] P).eval c
        then 1 else -1 := by
  have hinter := interlaced_virtualRoots hIVP hP hdP
  have hargmin := argminPartition_virtualRoots hIVP hP hdP
  have hys_sort := sorted_virtualRoots hIVP hdP
  have hys_sg := signConstantOnGaps_virtualRoots hIVP hdP
  have hdiff := Internal.count_diff_of_not_root hIVP hdP hinter hys_sort
    hargmin hys_sg hPc
  unfold virtualMultiplicity
  rw [hdiff]
  rfl

end Azurite.BPR.VirtualRoots
