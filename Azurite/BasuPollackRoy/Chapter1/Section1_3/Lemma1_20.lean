import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_13
import Azurite.BasuPollackRoy.Chapter1.Section1_3.LeafFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Lemma1_19
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Posgcd
import Azurite.BasuPollackRoy.Chapter1.Section1_3.TRems

/-! # BPR Section 1.3 — Lemma 1.20: correctness of `posgcd`

BPR's Lemma 1.20:

> For all `y ∈ C^k`, there exists one and only one `(G, 𝒞) ∈ posgcd(𝒫)`
> such that `y ∈ Reali(𝒞)`. Moreover, `y ∈ Reali(𝒞)` implies that
> `G_y` is a greatest common divisor of `𝒫_y`.

Three statements:
* `posgcd_covering`: existence ("for all `y`, there exists ...");
* `posgcd_unique`: uniqueness ("one and only one");
* `posgcd_gcd`: gcd correctness ("`G_y` is a gcd of `𝒫_y`").
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ}

section Lemma_1_20

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]
variable {C : Type*} [Field C]

/-- BPR Lemma 1.20 (gcd correctness): for each `(G, 𝒞) ∈ posgcd(Ps)`
and every `y ∈ Reali(𝒞)`, the specialization `G_y` is a GCD of the
family `Ps_y` of specialized polynomials. -/
theorem posgcd_gcd
    [Algebra D C]
    (Ps : List (Polynomial (MvPolynomial (Fin k) D)))
    {G : Polynomial (MvPolynomial (Fin k) D)}
    {𝒞 : Formula (Fin k) (FieldAtom (Fin k) D)}
    (hmem : (G, 𝒞) ∈ posgcd Ps)
    (y : Fin k → C)
    (hy : y ∈ 𝒞.realization (C := C)) :
    IsListGCD (G.map (MvPolynomial.aeval y).toRingHom)
      (Ps.map (Polynomial.map (MvPolynomial.aeval y).toRingHom)) := by
  induction Ps generalizing G 𝒞 with
  | nil =>
    simp only [posgcd, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨by simp, fun _ _ => by simp⟩
  | cons P rest ih =>
    simp only [posgcd, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hmem
    obtain ⟨⟨Q, C_q⟩, hQC_mem, path, hpath_mem, hG_eq, h𝒞_eq⟩ := hmem
    subst hG_eq; subst h𝒞_eq
    simp only [Formula.realization_and, Set.mem_inter_iff] at hy
    obtain ⟨hy_C, hy_leaf⟩ := hy
    have ih' := ih hQC_mem hy_C
    have hgcd := leafFormula_gcd P Q hpath_mem y hy_leaf
    set φ := (MvPolynomial.aeval (R := D) y).toRingHom
    refine ⟨?_, ?_⟩
    · intro P' hP'
      simp only [List.map_cons, List.mem_cons] at hP'
      rcases hP' with rfl | hP'
      · exact hgcd.1
      · exact dvd_trans hgcd.2.1 (ih'.1 _ hP')
    · intro E hE
      simp only [List.map_cons, List.mem_cons, forall_eq_or_imp] at hE
      obtain ⟨hE_P, hE_rest⟩ := hE
      have hE_Q : E ∣ Q.map φ := ih'.2 E hE_rest
      exact hgcd.2.2 E hE_P hE_Q

/-- BPR Lemma 1.20 (covering): every `y ∈ C^k` is in `Reali(𝒞)` for
some `(G, 𝒞) ∈ posgcd(Ps)`. Requires `algebraMap D C` injective. -/
theorem posgcd_covering
    [Algebra D C]
    (hinj : Function.Injective (algebraMap D C))
    (Ps : List (Polynomial (MvPolynomial (Fin k) D)))
    (y : Fin k → C) :
    ∃ G 𝒞, (G, 𝒞) ∈ posgcd Ps ∧ y ∈ 𝒞.realization (C := C) := by
  induction Ps with
  | nil =>
    refine ⟨0, Formula.trueFormula, ?_, ?_⟩
    · simp [posgcd]
    · simp [Formula.trueFormula]
  | cons P rest ih =>
    obtain ⟨Q, C_q, hQC_mem, hy_C⟩ := ih
    obtain ⟨path, hpath_mem, hy_leaf⟩ := leafFormula_covering hinj P Q y
    refine ⟨pathLeafParent P path, C_q.and (leafFormula P Q path), ?_, ?_⟩
    · simp only [posgcd, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      exact ⟨⟨Q, C_q⟩, hQC_mem, path, hpath_mem, rfl, rfl⟩
    · simp only [Formula.realization_and, Set.mem_inter_iff]
      exact ⟨hy_C, hy_leaf⟩

/-- BPR Lemma 1.20 (uniqueness): if `(G, 𝒞)` and `(G', 𝒞')` are both in
`posgcd Ps` and some `y ∈ C^k` lies in both `𝒞.realization` and
`𝒞'.realization`, then the two pairs are equal. Combined with
`posgcd_covering`, this gives BPR's "exists one and only one". -/
theorem posgcd_unique
    [Algebra D C]
    (Ps : List (Polynomial (MvPolynomial (Fin k) D)))
    {G G' : Polynomial (MvPolynomial (Fin k) D)}
    {𝒞 𝒞' : Formula (Fin k) (FieldAtom (Fin k) D)}
    (hmem : (G, 𝒞) ∈ posgcd Ps)
    (hmem' : (G', 𝒞') ∈ posgcd Ps)
    (y : Fin k → C)
    (hy : y ∈ 𝒞.realization (C := C))
    (hy' : y ∈ 𝒞'.realization (C := C)) :
    (G, 𝒞) = (G', 𝒞') := by
  induction Ps generalizing G G' 𝒞 𝒞' with
  | nil =>
    simp only [posgcd, List.mem_singleton] at hmem hmem'
    rw [hmem, hmem']
  | cons P rest ih =>
    simp only [posgcd, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      at hmem hmem'
    obtain ⟨⟨Q, C_q⟩, hQC_mem, path, hpath_mem, hG_eq, h𝒞_eq⟩ := hmem
    obtain ⟨⟨Q', C_q'⟩, hQC_mem', path', hpath_mem', hG_eq', h𝒞_eq'⟩ := hmem'
    subst hG_eq; subst h𝒞_eq; subst hG_eq'; subst h𝒞_eq'
    simp only [Formula.realization_and, Set.mem_inter_iff] at hy hy'
    obtain ⟨hy_C, hy_leaf⟩ := hy
    obtain ⟨hy_C', hy_leaf'⟩ := hy'
    -- IH on the sub-pair: the (Q, C_q) coming from posgcd rest is unique
    have hQC_eq : (Q, C_q) = (Q', C_q') :=
      ih hQC_mem hQC_mem' hy_C hy_C'
    obtain ⟨rfl, rfl⟩ : Q = Q' ∧ C_q = C_q' := by
      rw [Prod.mk.injEq] at hQC_eq; exact hQC_eq
    -- leafFormula_disjoint contrapositive: distinct paths ⇒ disjoint realizations,
    -- so y in both ⇒ paths equal
    have hpath_eq : path = path' := by
      by_contra hne
      have hdisj := leafFormula_disjoint (C := C) P Q hpath_mem hpath_mem' hne
      have : y ∈ (leafFormula P Q path).realization (C := C) ∩
                 (leafFormula P Q path').realization (C := C) :=
        ⟨hy_leaf, hy_leaf'⟩
      rw [hdisj] at this; exact this.elim
    subst hpath_eq
    rfl

end Lemma_1_20

end Azurite.BPR
