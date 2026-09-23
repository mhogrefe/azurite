import Azurite.AzMvPolynomial.SquarefreeFactorization
import Azurite.AzMvPolynomial.Equiv.TowerGcd
import Azurite.AzMvPolynomial.Equiv.IntContentMul
import Azurite.AzPolynomial.Equiv.SquarefreeFactorizationUFD

/-!
# Correctness of multivariate Yun square-free factorization (Phase 2)

This file collects the correctness results for `mvSquarefreeFactorization`
(the recursive Yun of `AzMvPolynomial.SquarefreeFactorization`).

## What is proved

* `mvSquarefreeFactorization_sorted` — the output polynomials are `≤`-sorted in
  the canonical `AzMvPolynomial` order (a direct consequence of the final
  `mergeSort`, independent of the arithmetic).

## The tower coefficient ring is now a UFD / normalized gcd monoid

The earlier field-vs-UFD obstacle (the univariate Yun correctness being stated
only over a `[Field K]`) has been resolved on two fronts:

* the univariate Yun correctness was generalized to characteristic-zero UFD
  coefficients in `Azurite/AzPolynomial/Equiv/SquarefreeFactorizationUFD.lean`
  (`Azurite.AzPolynomial.UFD.squarefreeFactorization_prod`, parameterized by a
  gcd-lawfulness hypothesis `hgcd_law`), and
* the tower coefficient ring `R := AzMvPolynomial n AzInt ord` was equipped
  (`Azurite/AzMvPolynomial/Equiv/TowerGcd.lean`) with the
  `UniqueFactorizationMonoid`, `NormalizedGCDMonoid` and `CharZero` instances,
  with the transported `GCDMonoid.gcd` proven *equal* to the computable
  `AzMvPolynomial.gcd` (`GCDMonoid_gcd_eq`, `toPoly_finSuccEquiv_gcd`).

Consequently `tower_hgcd_law` below discharges the univariate `hgcd_law` for the
tower `GcdImpl`, and `squarefreeFactorization_tower_prod` is the univariate
product identity **specialized to the tower ring** — the direct payoff and the
engine for the (recursive) multivariate product.

## What is proved here

* `mvSquarefreeFactorization_sorted` — output polynomials `≤`-sorted (from the
  final `mergeSort`).
* `tower_hgcd_law` — the tower `GcdImpl.gcd` matches Mathlib's `GCDMonoid.gcd`
  in `Polynomial R`.
* `squarefreeFactorization_tower_prod` — univariate Yun product identity over
  the tower ring `R` (primitive + normalized input).
* `prodPow` and its **invariance** under `mergeByMult` (`mergeByMult_prodPow`)
  and under the final `mergeSort` (`mergeSort_prodPow`) — the list-combinatorial
  half of the multivariate product identity.

## Residual: `mvSquarefreeFactorization_prod`

The recursive multivariate product identity is *unblocked in principle* by the
above but not yet assembled. The remaining obstacle is a **normalization**
mismatch, not a field obstacle: the `x₀`-primitive part `pp := primitivePart P`
is generally **not normalized** (its `x₀`-leading coefficient need not be a
normalized element of `R`), so `toPoly (finSuccEquiv pp)` fails the `hnorm`
hypothesis of `squarefreeFactorization_tower_prod`. The mathematically correct
statement is therefore the **`Associated`** form `Associated (prodPow …) P`
(square-free factorization up to a unit), whose proof needs:

1. an `Associated`-conclusion variant of the univariate UFD product
   (`hprim` only, dropping `hnorm`) added to `SquarefreeFactorizationUFD.lean`;
2. a flat `AzMvPolynomial (n+1)`-level content–primitive-part identity
   `(embed (content P)) * primitivePart P = P` (the nested-model version
   `toNested_content_mul_primitivePart` is available and can be descended);
3. the identification `renameInjective · Fin.succ = finSuccEquivSymm ∘ C` of the
   content embedding with the constant-in-`x₀` tower embedding;
4. the induction on `n` combining the two `prodPow` invariance lemmas above.
-/

namespace Azurite.AzMvPolynomial

open Azurite

/-- A `mergeSort` by the first component (through `LinearOrder`) yields a list
whose first components are `≤`-`Pairwise`. -/
private theorem mergeSort_pairwise_le {α : Type _} [LinearOrder α] (l : List (α × ℕ)) :
    (l.mergeSort (fun a b => decide (a.1 ≤ b.1))).Pairwise (fun a b => a.1 ≤ b.1) := by
  have h := List.pairwise_mergeSort
    (le := fun a b : α × ℕ => decide (a.1 ≤ b.1))
    (fun x y z hxy hyz => by rw [decide_eq_true_eq] at hxy hyz ⊢; exact le_trans hxy hyz)
    (fun x y => by rcases le_total x.1 y.1 with h | h <;> simp [h])
    l
  exact h.imp (fun hxy => by rwa [decide_eq_true_eq] at hxy)

/-- **Canonically sorted output** (correctness #4): the square-free parts of
`mvSquarefreeFactorization P` are `≤`-`Pairwise` in the `AzMvPolynomial`
`LinearOrder` — the output is in canonical (ascending) order. Immediate from
the final `mergeSort`; independent of the (blocked) product/square-free/coprime
facts. -/
theorem mvSquarefreeFactorization_sorted {n : ℕ} {ord : MonomialOrder}
    (P : AzMvPolynomial n AzInt ord) :
    (mvSquarefreeFactorization P).Pairwise (fun a b => a.1 ≤ b.1) := by
  match n, P with
  | 0, _ => exact List.Pairwise.nil
  | (m + 1), P => exact mergeSort_pairwise_le _

/-! ### The tower gcd is lawful; the univariate product over the tower ring -/

variable {n : ℕ} {ord : MonomialOrder}

/-- Round trip of the `x₀`-peel iso. -/
theorem finSuccEquiv_finSuccEquivSymm (P : AzPolynomial (AzMvPolynomial n AzInt ord)) :
    finSuccEquiv (finSuccEquivSymm P) = P :=
  (finSuccAlgEquiv (R := AzInt) (n := n) (ord := ord)).apply_symm_apply P

/-- **The tower `GcdImpl` is lawful**: the computable tower gcd equals Mathlib's
normalized `GCDMonoid.gcd` in `Polynomial (AzMvPolynomial n AzInt ord)`. This is
the `hgcd_law` hypothesis of the univariate UFD-Yun correctness, discharged for
the tower ring via `AzMvPolynomial.toPoly_finSuccEquiv_gcd`. -/
theorem tower_hgcd_law (P Q : AzPolynomial (AzMvPolynomial n AzInt ord)) :
    AzPolynomial.toPoly (AzPolynomial.gcd P Q)
      = GCDMonoid.gcd (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) := by
  show AzPolynomial.toPoly
      (finSuccEquiv (AzMvPolynomial.gcd (finSuccEquivSymm P) (finSuccEquivSymm Q))) = _
  rw [toPoly_finSuccEquiv_gcd, finSuccEquiv_finSuccEquivSymm, finSuccEquiv_finSuccEquivSymm]

/-- **Univariate Yun product identity over the tower ring** (GCL Algorithm 8.2,
correctness 1, specialized to `R := AzMvPolynomial n AzInt ord`): for a primitive
normalized `a : AzPolynomial R`, the product of the output polynomials raised to
their exponents is `a`. This is `UFD.squarefreeFactorization_prod` with the tower
`hgcd_law` discharged; it is the engine for the recursive multivariate product. -/
theorem squarefreeFactorization_tower_prod
    (a : AzPolynomial (AzMvPolynomial n AzInt ord))
    (hprim : (AzPolynomial.toPoly a).IsPrimitive)
    (hnorm : normalize (AzPolynomial.toPoly a) = AzPolynomial.toPoly a) :
    ((AzPolynomial.squarefreeFactorization a).map
      (fun gi => AzPolynomial.toPoly gi.1 ^ gi.2)).prod = AzPolynomial.toPoly a :=
  Azurite.AzPolynomial.UFD.squarefreeFactorization_prod tower_hgcd_law a hprim hnorm

/-! ### Product-of-powers and its invariance under `mergeByMult` / `mergeSort`

The list-combinatorial half of the multivariate product identity: the product
`∏ gᵢ^{eᵢ}` of a factor list is unchanged by the multiplicity-grouping
`mergeByMult` and by the final canonical `mergeSort`. -/

/-- The product of the entries of a factor list, each raised to its multiplicity. -/
def prodPow (l : List (AzMvPolynomial n AzInt ord × ℕ)) : AzMvPolynomial n AzInt ord :=
  (l.map (fun ge => ge.1 ^ ge.2)).prod

/-- `insertMult` adds one `g ^ e` factor to the product. -/
theorem insertMult_prodPow (acc : List (AzMvPolynomial n AzInt ord × ℕ))
    (g : AzMvPolynomial n AzInt ord) (e : ℕ) :
    prodPow (insertMult acc g e) = g ^ e * prodPow acc := by
  induction acc with
  | nil => simp [prodPow, insertMult]
  | cons a rest ih =>
    obtain ⟨g', e'⟩ := a
    rw [insertMult]
    by_cases he : e' = e
    · rw [ite_eq_left he, he]
      simp only [prodPow, List.map_cons, List.prod_cons, mul_pow]; ring
    · rw [ite_eq_right he]
      simp only [prodPow, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih]; ring

/-- Folding `insertMult` multiplies the two product-of-powers. -/
theorem foldl_insertMult_prodPow (l : List (AzMvPolynomial n AzInt ord × ℕ)) :
    ∀ init, prodPow (l.foldl (fun acc ge => insertMult acc ge.1 ge.2) init)
      = prodPow l * prodPow init := by
  induction l with
  | nil => intro init; simp [prodPow]
  | cons a rest ih =>
    intro init
    rw [List.foldl_cons, ih (insertMult init a.1 a.2), insertMult_prodPow]
    simp only [prodPow, List.map_cons, List.prod_cons]; ring

/-- **`mergeByMult` preserves the product-of-powers.** -/
theorem mergeByMult_prodPow (l : List (AzMvPolynomial n AzInt ord × ℕ)) :
    prodPow (mergeByMult l) = prodPow l := by
  rw [mergeByMult, foldl_insertMult_prodPow]; simp [prodPow]

/-- **`mergeSort` preserves the product-of-powers.** -/
theorem mergeSort_prodPow (l : List (AzMvPolynomial n AzInt ord × ℕ)) (r) :
    prodPow (l.mergeSort r) = prodPow l :=
  ((List.mergeSort_perm l r).map _).prod_eq

/-- The product-of-powers distributes over list concatenation. -/
theorem prodPow_append (l₁ l₂ : List (AzMvPolynomial n AzInt ord × ℕ)) :
    prodPow (l₁ ++ l₂) = prodPow l₁ * prodPow l₂ := by
  simp [prodPow, List.map_append, List.prod_append]

/-! ### The `x₀`-peel iso applied to the factor lists

Everything below transports the recursion through the ring iso
`peelEquiv n : AzMvPolynomial (n+1) ≃+* Polynomial (AzMvPolynomial n)`
(`= toPoly ∘ finSuccEquiv`), reducing the multivariate product identity to the
already-established univariate one (`squarefreeFactorization_prod_associated`,
over the tower coefficient ring `R := AzMvPolynomial n AzInt ord`). -/

/-- Primitivity reflects along a coefficient ring isomorphism. -/
theorem isPrimitive_of_map_isPrimitive {R S : Type _} [CommRing R] [CommRing S] (e : R ≃+* S)
    {p : Polynomial R} (h : (p.map (e : R →+* S)).IsPrimitive) : p.IsPrimitive := by
  intro r hr
  have hdvd : (Polynomial.C r).map (e : R →+* S) ∣ p.map (e : R →+* S) :=
    map_dvd (Polynomial.mapRingHom (e : R →+* S)) hr
  rw [Polynomial.map_C] at hdvd
  simpa using (h _ hdvd).map (e.symm : S →+* R)

set_option maxHeartbeats 1600000 in
/-- **The peeled content–primitive-part identity**: descended to
`Polynomial (AzMvPolynomial n)`, `peelEquiv P` is the content times the peel of
the primitive part. -/
theorem peelEquiv_content_mul_primitivePart (P : AzMvPolynomial (n + 1) AzInt ord) :
    peelEquiv n P
      = Polynomial.C (AzMvPolynomial.content P) * peelEquiv n (AzMvPolynomial.primitivePart P) := by
  have hC : (Polynomial.C (toNested (ord := ord) n (AzMvPolynomial.content P)) :
        Polynomial (NestedPoly n))
      = Polynomial.map (nestedRingEquiv (ord := ord) n : AzMvPolynomial n AzInt ord →+* NestedPoly n)
          (Polynomial.C (AzMvPolynomial.content P)) := by
    rw [Polynomial.map_C]; exact congrArg Polynomial.C (toNested_eq n _)
  have hkey := congrArg AzPolynomial.toPoly (toNested_content_mul_primitivePart P)
  rw [AzPolynomial.toPoly_mul, AzPolynomial.toPoly_C, toPoly_toNested_succ, toPoly_toNested_succ,
    hC, ← Polynomial.map_mul] at hkey
  have hinj := Polynomial.map_injective
    (nestedRingEquiv (ord := ord) n : AzMvPolynomial n AzInt ord →+* NestedPoly n)
    (nestedRingEquiv (ord := ord) n).injective
  have hres := hinj hkey
  rw [peelEquiv_apply, peelEquiv_apply]
  exact hres.symm

set_option maxHeartbeats 1600000 in
/-- The peel of the primitive part is primitive (Mathlib `IsPrimitive` in
`Polynomial (AzMvPolynomial n)`), for `P ≠ 0`. -/
theorem peelEquiv_primitivePart_isPrimitive (P : AzMvPolynomial (n + 1) AzInt ord) (hP : P ≠ 0) :
    (peelEquiv n (primitivePart P)).IsPrimitive := by
  apply isPrimitive_of_map_isPrimitive (modelEquiv n)
  have h1 : Polynomial.map (modelEquiv (ord := ord) n : AzMvPolynomial n AzInt ord →+* ModelPoly n)
      (peelEquiv n (primitivePart P))
      = (modelEquiv (n + 1) (primitivePart P) : Polynomial (ModelPoly n)) :=
    (modelEquiv_succ n (primitivePart P)).symm
  rw [h1, modelEquiv_apply, towerBridge_toNested_primitivePart hP, ← modelEquiv_apply]
  exact Polynomial.isPrimitive_primPart _

/-- The constant-in-`x₀` embedding `renameInjective · Fin.succ` is the
`finSuccEquivSymm` of a coefficient constant. -/
theorem finSuccEquivSymm_C (g : AzMvPolynomial n AzInt ord) :
    finSuccEquivSymm (AzPolynomial.C g) = renameInjective g Fin.succ (Fin.succ_injective n) := by
  by_cases hg : g = 0
  · subst hg
    have hz : renameInjective (0 : AzMvPolynomial n AzInt ord) Fin.succ (Fin.succ_injective n) = 0 := by
      apply toMvPoly_injective
      rw [toMvPoly_renameInjective, toMvPoly_zero]; exact map_zero _
    rw [show (AzPolynomial.C (0 : AzMvPolynomial n AzInt ord)) = 0 from by simp [AzPolynomial.C], hz]
    show (0 : AzPolynomial (AzMvPolynomial n AzInt ord)).coeffs.foldr _ 0 = 0
    rfl
  · unfold AzMvPolynomial.finSuccEquivSymm
    rw [show AzPolynomial.C g
        = (⟨#[g], by simp [hg]⟩ : AzPolynomial (AzMvPolynomial n AzInt ord)) from by
        rw [AzPolynomial.C, dite_eq_right hg]]
    show (#[g] : Array (AzMvPolynomial n AzInt ord)).foldr _ 0 = _
    rw [← Array.foldr_toList, show (#[g] : Array (AzMvPolynomial n AzInt ord)).toList = [g] from rfl]
    simp only [List.foldr_cons, List.foldr_nil, zero_mul, add_zero]

/-- `finSuccEquiv` of the constant-in-`x₀` embedding is the coefficient constant. -/
theorem finSuccEquiv_embed (g : AzMvPolynomial n AzInt ord) :
    finSuccEquiv (renameInjective g Fin.succ (Fin.succ_injective n)) = AzPolynomial.C g := by
  rw [← finSuccEquivSymm_C, finSuccEquiv_finSuccEquivSymm]

/-- `peelEquiv` inverts `finSuccEquivSymm` up to `toPoly`. -/
theorem peelEquiv_finSuccEquivSymm (g : AzPolynomial (AzMvPolynomial n AzInt ord)) :
    peelEquiv n (finSuccEquivSymm g) = AzPolynomial.toPoly g := by
  rw [peelEquiv_apply, finSuccEquiv_finSuccEquivSymm]

/-- `peelEquiv` of the constant-in-`x₀` embedding is `Polynomial.C`. -/
theorem peelEquiv_embed (g : AzMvPolynomial n AzInt ord) :
    peelEquiv n (renameInjective g Fin.succ (Fin.succ_injective n)) = Polynomial.C g := by
  rw [peelEquiv_apply, finSuccEquiv_embed, AzPolynomial.toPoly_C]

/-- `peelEquiv` distributes over `prodPow` as a product of peeled powers. -/
theorem peelEquiv_prodPow (l : List (AzMvPolynomial (n + 1) AzInt ord × ℕ)) :
    peelEquiv n (prodPow l) = (l.map (fun ge => peelEquiv n ge.1 ^ ge.2)).prod := by
  rw [prodPow, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro ge _
  simp [Function.comp, map_pow]

/-- `Associated` reflects along the ring iso `peelEquiv`. -/
theorem associated_of_peelEquiv {X Y : AzMvPolynomial (n + 1) AzInt ord}
    (h : Associated (peelEquiv n X) (peelEquiv n Y)) : Associated X Y := by
  have := h.map (peelEquiv (n := n) (ord := ord)).symm.toRingHom.toMonoidHom
  simpa using this

/-- **`intContent = 1` is invariant under the constant-in-`x₀` embedding**
(variable renaming preserves ℤ-primitivity: reduction mod every prime commutes
with the injective renaming). -/
theorem intContent_renameInjective_eq_one_iff (g : AzMvPolynomial n AzInt ord) :
    intContent (renameInjective g Fin.succ (Fin.succ_injective n)) = 1 ↔ intContent g = 1 := by
  rw [intContent_eq_one_iff, intContent_eq_one_iff]
  have himg : intImg (renameInjective g Fin.succ (Fin.succ_injective n))
      = MvPolynomial.rename Fin.succ (intImg g) := by
    rw [intImg, intImg, ringEquivMvPolynomialInt_apply, ringEquivMvPolynomialInt_apply,
      toMvPoly_renameInjective, MvPolynomial.map_rename]
  refine forall_congr' (fun p => imp_congr_right (fun _ => ?_))
  rw [himg, redp, redp, MvPolynomial.map_rename]
  constructor
  · intro h hz; exact h (by rw [hz, map_zero])
  · intro h hz
    exact h ((MvPolynomial.rename_injective Fin.succ (Fin.succ_injective n)).eq_iff.mp
      (by rw [hz, map_zero]))

/-- **Base case (`n = 0`)**: a ℤ-primitive `0`-variable polynomial is a unit
(`±1`). -/
theorem base_isUnit (P : AzMvPolynomial 0 AzInt ord) (hP : intContent P = 1) : IsUnit P := by
  rw [intContent_eq_one_iff] at hP
  set c : ℤ := (MvPolynomial.isEmptyRingEquiv ℤ (Fin 0)) (intImg P) with hc
  have hPC : intImg P = MvPolynomial.C c := by
    rw [hc, ← MvPolynomial.isEmptyRingEquiv_symm_apply, RingEquiv.symm_apply_apply]
  have hunit_c : IsUnit c := by
    rw [Int.isUnit_iff_natAbs_eq, Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hpd
    have : Fact p.Prime := ⟨hp⟩
    apply hP p hp
    rw [hPC, redp, MvPolynomial.map_C, MvPolynomial.C_eq_zero]
    have hdvd : (p : ℤ) ∣ c := (Int.natCast_dvd_natCast.mpr hpd).trans (Int.natAbs_dvd.mpr dvd_rfl)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mpr hdvd
  have hu_img : IsUnit (intImg P) := by rw [hPC]; exact hunit_c.map MvPolynomial.C
  have hu := hu_img.map (ringEquivMvPolynomialInt (n := 0) (ord := ord)).symm.toRingHom
  rwa [intImg, show (ringEquivMvPolynomialInt (n := 0) (ord := ord)).symm.toRingHom
      (ringEquivMvPolynomialInt P) = P from
    (ringEquivMvPolynomialInt (n := 0) (ord := ord)).symm_apply_apply P] at hu

-- `mvSquarefreeFactorization` was defined (in `AzMvPolynomial.SquarefreeFactorization`)
-- with the **default** `PolynomialDerivative` instance, because the tower
-- `CharZero (AzMvPolynomial n AzInt ord)` instance that unlocks the high-priority
-- `…OfCharZeroOfNoZeroDivisors` derivative is only available downstream (in
-- `Equiv.TowerGcd`). Fresh resolution here would pick the high-priority instance,
-- so `squarefreeFactorization` calls below would not match the def's unfolding
-- (a genuine, non-defeq divergence of the `derivative` field). Disabling the
-- high instance for the remainder of the file keeps everything on the default
-- instance, matching the def; the two derivatives agree coefficient-wise, so
-- correctness (over the coefficient laws) is unaffected.
attribute [-instance] AzPolynomial.instPolynomialDerivativeOfCharZeroOfNoZeroDivisors

/-- Clean unfolding of the `n = m+1` case as a **proven equation** whose RHS is
spelled explicitly. Rewriting with this is a syntactic substitution (no defeq),
so it avoids the `whnf` blow-up that reconciling the raw structural-recursion
unfold with a hand-written form would trigger. -/
theorem mvSquarefreeFactorization_succ {m : ℕ} (P : AzMvPolynomial (m + 1) AzInt ord) :
    mvSquarefreeFactorization P =
      (mergeByMult
        (((AzPolynomial.squarefreeFactorization (finSuccEquiv (primitivePart P))).map
            (fun ge => (finSuccEquivSymm ge.1, ge.2)))
          ++ ((mvSquarefreeFactorization (content P)).map
            (fun ge => (renameInjective ge.1 Fin.succ (Fin.succ_injective m), ge.2))))).mergeSort
        (fun a b => a.1 ≤ b.1) := by
  rw [mvSquarefreeFactorization]

/-- The final combination of the recursion step, stated with the two
product-of-powers `A` (pp-factors) and `B` (content-factors) as **opaque**
arguments. Extracting them as variables keeps the `peelEquiv`-image defeq in
`exact` purely syntactic, avoiding the `whnf` blow-up that unfolding the
tower-model `content`/`primitivePart` would otherwise cause. -/
theorem mv_prod_combine {m : ℕ} (P A B : AzMvPolynomial (m + 1) AzInt ord)
    (hpp : Associated (peelEquiv m A) (peelEquiv m (primitivePart P)))
    (hcc : Associated (peelEquiv m B) (Polynomial.C (content P))) :
    Associated (A * B) P := by
  apply associated_of_peelEquiv
  rw [map_mul, peelEquiv_content_mul_primitivePart P, mul_comm (Polynomial.C (content P))]
  exact hpp.mul_mul hcc

set_option maxHeartbeats 400000 in
/-- **The multivariate square-free factorization product identity** (GCL
Algorithm 8.2, multivariate, correctness 1): for a ℤ-primitive input
`P : AzMvPolynomial n AzInt ord`, the product of the output square-free parts
raised to their multiplicities is `P` **up to a unit**. Proved by structural
recursion on the variable count `n`, transporting each recursion step through
the `x₀`-peel ring iso `peelEquiv` down to the univariate UFD-Yun product
identity over the tower coefficient ring. -/
theorem mvSquarefreeFactorization_prod : ∀ {n : ℕ} (P : AzMvPolynomial n AzInt ord),
    intContent P = 1 → Associated (prodPow (mvSquarefreeFactorization P)) P := by
  intro n
  induction n with
  | zero =>
    intro P hP
    rw [show mvSquarefreeFactorization P = [] from rfl, prodPow, List.map_nil, List.prod_nil]
    exact (associated_one_iff_isUnit.mpr (base_isUnit P hP)).symm
  | succ m ih =>
    intro P hP
    have hP0 : P ≠ 0 := by
      rintro rfl
      rw [show intContent (0 : AzMvPolynomial (m + 1) AzInt ord) = 0 from rfl] at hP
      exact absurd hP (by decide)
    -- Step 2: the content is ℤ-primitive (embed of content divides `P`), so the IH applies
    have hEmbedDvd : renameInjective (content P) Fin.succ (Fin.succ_injective m) ∣ P := by
      refine ⟨primitivePart P, ?_⟩
      apply (peelEquiv m).injective
      rw [map_mul, peelEquiv_embed, peelEquiv_content_mul_primitivePart P]
    have hcContent : intContent (content P) = 1 :=
      (intContent_renameInjective_eq_one_iff (content P)).mp
        (intContent_eq_one_of_dvd hEmbedDvd hP)
    -- Step C: the pp-factors' peel is associated to the primitive part (univariate Yun)
    have hpp : Associated
        (peelEquiv m (prodPow ((AzPolynomial.squarefreeFactorization
          (finSuccEquiv (primitivePart P))).map (fun ge => (finSuccEquivSymm ge.1, ge.2)))))
        (peelEquiv m (primitivePart P)) := by
      have hprim : (AzPolynomial.toPoly (finSuccEquiv (primitivePart P))).IsPrimitive := by
        rw [← peelEquiv_apply]; exact peelEquiv_primitivePart_isPrimitive P hP0
      have hassoc := Azurite.AzPolynomial.UFD.squarefreeFactorization_prod_associated
        tower_hgcd_law (finSuccEquiv (primitivePart P)) hprim
      rw [peelEquiv_prodPow, List.map_map]
      have hmap : ((AzPolynomial.squarefreeFactorization (finSuccEquiv (primitivePart P))).map
            ((fun ge => peelEquiv m ge.1 ^ ge.2) ∘ fun ge => (finSuccEquivSymm ge.1, ge.2)))
          = (AzPolynomial.squarefreeFactorization (finSuccEquiv (primitivePart P))).map
              (fun ge => AzPolynomial.toPoly ge.1 ^ ge.2) := by
        apply List.map_congr_left
        intro ge _
        simp [Function.comp, peelEquiv_finSuccEquivSymm]
      rw [hmap, peelEquiv_apply]
      exact hassoc
    -- Step D: the content-factors' peel is `C` of the content, associated via the IH
    have hcc : Associated
        (peelEquiv m (prodPow ((mvSquarefreeFactorization (content P)).map
          (fun ge => (renameInjective ge.1 Fin.succ (Fin.succ_injective m), ge.2)))))
        (Polynomial.C (content P)) := by
      have hcalc : peelEquiv m (prodPow ((mvSquarefreeFactorization (content P)).map
            (fun ge => (renameInjective ge.1 Fin.succ (Fin.succ_injective m), ge.2))))
          = Polynomial.C (prodPow (mvSquarefreeFactorization (content P))) := by
        rw [peelEquiv_prodPow, List.map_map, prodPow, map_list_prod, List.map_map]
        congr 1
        apply List.map_congr_left
        intro ge _
        simp [Function.comp, peelEquiv_embed, map_pow]
      rw [hcalc]
      exact (ih (content P) hcContent).map
        (Polynomial.C : AzMvPolynomial m AzInt ord →+* _).toMonoidHom
    -- Step E: unravel the merge/sort combinatorics and combine
    have heq : prodPow (mvSquarefreeFactorization P)
        = prodPow ((AzPolynomial.squarefreeFactorization (finSuccEquiv (primitivePart P))).map
            (fun ge => (finSuccEquivSymm ge.1, ge.2)))
          * prodPow ((mvSquarefreeFactorization (content P)).map
            (fun ge => (renameInjective ge.1 Fin.succ (Fin.succ_injective m), ge.2))) := by
      rw [mvSquarefreeFactorization_succ, mergeSort_prodPow, mergeByMult_prodPow, prodPow_append]
    rw [heq]
    exact mv_prod_combine P _ _ hpp hcc

/-! ### Squarefreeness and pairwise coprimality of `mvSquarefreeFactorization`

Both are captured by one invariant on the factor list — every `.1` squarefree
*and* the list pairwise `IsRelPrime` — carried through the `mergeByMult`/`mergeSort`
combinatorics. The base list `ppFactors ++ cFactors` satisfies it: pp-factors from
the tower univariate Yun (normalize-free), c-factors from the induction hypothesis,
and pp↔c coprime because a pp-factor involves `x₀` (its `x₀`-tower image is a
positive-degree primitive polynomial) while a c-factor does not (a constant). -/

/-- Transfer of `Squarefree` across a `RingEquiv`. -/
theorem squarefree_ringEquiv {M N : Type _} [CommRing M] [CommRing N]
    (e : M ≃+* N) {x : M} : Squarefree (e x) ↔ Squarefree x := by
  constructor
  · intro h y hyy
    exact (isUnit_map_iff e y).mp (h (e y) (by rw [← map_mul]; exact map_dvd e hyy))
  · intro h y hyy
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul] at hyy
    exact (isUnit_map_iff e z).mpr (h z ((map_dvd_iff e).mp hyy))

/-- Transfer of `IsRelPrime` across a `RingEquiv`. -/
theorem isRelPrime_ringEquiv {M N : Type _} [CommRing M] [CommRing N]
    (e : M ≃+* N) {x y : M} : IsRelPrime (e x) (e y) ↔ IsRelPrime x y := by
  constructor
  · intro h d hdx hdy
    exact (isUnit_map_iff e d).mp (h (map_dvd e hdx) (map_dvd e hdy))
  · intro h d hdx hdy
    obtain ⟨c, rfl⟩ := e.surjective d
    exact (isUnit_map_iff e c).mpr (h ((map_dvd_iff e).mp hdx) ((map_dvd_iff e).mp hdy))

/-- A primitive polynomial is coprime to any (nonzero) constant — the key to
pp↔c coprimality (a pp-factor's `x₀`-image is primitive; a c-factor is a constant). -/
theorem isRelPrime_C_of_isPrimitive {S : Type _} [CommRing S] [IsDomain S]
    {p : Polynomial S} (hp : p.IsPrimitive) {c : S} (hc : c ≠ 0) :
    IsRelPrime p (Polynomial.C c) := by
  intro d hdp hdC
  have hCne : (Polynomial.C c : Polynomial S) ≠ 0 := by simpa using hc
  have hd0 : d.natDegree = 0 :=
    Nat.le_zero.mp (by rw [← Polynomial.natDegree_C c]; exact Polynomial.natDegree_le_of_dvd hdC hCne)
  rw [Polynomial.eq_C_of_natDegree_eq_zero hd0] at hdp ⊢
  exact ((Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hp) (d.coeff 0) hdp).map Polynomial.C

/-- `Polynomial.C` sends squarefree to squarefree (constants carry no new square
factors) — used for c-factors, whose `x₀`-image is `C` of a lower-variable factor. -/
theorem squarefree_C_of {S : Type _} [CommRing S] [IsDomain S] {x : S}
    (hx : Squarefree x) : Squarefree (Polynomial.C x) := by
  intro d hdd
  have hCx0 : (Polynomial.C x : Polynomial S) ≠ 0 := by simpa using hx.ne_zero
  have hd0 : d.natDegree = 0 := Nat.le_zero.mp (by
    rw [← Polynomial.natDegree_C x]
    exact Polynomial.natDegree_le_of_dvd ((dvd_mul_right d d).trans hdd) hCx0)
  rw [Polynomial.eq_C_of_natDegree_eq_zero hd0] at hdd ⊢
  rw [← Polynomial.C_mul] at hdd
  have : d.coeff 0 * d.coeff 0 ∣ x := by
    have := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hdd 0; simpa using this
  exact (hx _ this).map Polynomial.C

/-- `Polynomial.C` sends coprime to coprime. -/
theorem isRelPrime_C_C_of {S : Type _} [CommRing S] [IsDomain S] {x y : S}
    (h : IsRelPrime x y) : IsRelPrime (Polynomial.C x) (Polynomial.C y) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Polynomial.C_0]
    exact isRelPrime_zero_left.mpr ((isRelPrime_zero_left.mp h).map Polynomial.C)
  · intro d hdx hdy
    have hCx0 : (Polynomial.C x : Polynomial S) ≠ 0 := by simpa using hx0
    have hd0 : d.natDegree = 0 :=
      Nat.le_zero.mp (by rw [← Polynomial.natDegree_C x]; exact Polynomial.natDegree_le_of_dvd hdx hCx0)
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd0] at hdx hdy ⊢
    have hdx' : d.coeff 0 ∣ x := by have := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hdx 0; simpa using this
    have hdy' : d.coeff 0 ∣ y := by have := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hdy 0; simpa using this
    exact (h hdx' hdy').map Polynomial.C

/-- Coprimality with a fixed `x` survives `insertMult`. -/
theorem insertMult_isRelPrime (x g : AzMvPolynomial n AzInt ord) (e : ℕ)
    (hxg : IsRelPrime x g) :
    ∀ (acc : List (AzMvPolynomial n AzInt ord × ℕ)),
      (∀ ge ∈ acc, IsRelPrime x ge.1) → ∀ ge ∈ insertMult acc g e, IsRelPrime x ge.1 := by
  intro acc
  induction acc with
  | nil => intro _ ge hge; simp only [insertMult, List.mem_singleton] at hge; subst hge; exact hxg
  | cons a rest ih =>
    intro hacc ge hge
    obtain ⟨g', e'⟩ := a
    simp only [insertMult] at hge
    split at hge
    · rw [List.mem_cons] at hge
      rcases hge with h | h
      · subst h; exact hxg.mul_right (hacc (g', e') (by simp))
      · exact hacc ge (List.mem_cons_of_mem _ h)
    · rw [List.mem_cons] at hge
      rcases hge with h | h
      · subst h; exact hacc (g', e') (by simp)
      · exact ih (fun ge hge => hacc ge (List.mem_cons_of_mem _ hge)) ge h

/-- `insertMult` preserves the "all squarefree + pairwise coprime" invariant when
inserting a squarefree `g` coprime to the accumulator (merging keeps squarefreeness
via `squarefree_mul_iff`, coprimality via `IsRelPrime.mul_left`). -/
theorem insertMult_inv (g : AzMvPolynomial n AzInt ord) (e : ℕ) (hg : Squarefree g) :
    ∀ (acc : List (AzMvPolynomial n AzInt ord × ℕ)),
      (∀ ge ∈ acc, IsRelPrime g ge.1) → (∀ ge ∈ acc, Squarefree ge.1) →
      acc.Pairwise (fun a b => IsRelPrime a.1 b.1) →
      (∀ ge ∈ insertMult acc g e, Squarefree ge.1) ∧
        (insertMult acc g e).Pairwise (fun a b => IsRelPrime a.1 b.1) := by
  intro acc
  induction acc with
  | nil =>
    intro _ _ _
    exact ⟨by intro ge hge; simp only [insertMult, List.mem_singleton] at hge; subst hge; exact hg,
      by simp [insertMult]⟩
  | cons a rest ih =>
    intro hcop hsf hpair
    obtain ⟨g', e'⟩ := a
    rw [List.pairwise_cons] at hpair
    simp only [insertMult]
    split
    · refine ⟨?_, ?_⟩
      · intro ge hge
        rw [List.mem_cons] at hge
        rcases hge with h | h
        · subst h; exact squarefree_mul_iff.mpr ⟨hcop (g',e') (by simp), hg, hsf (g',e') (by simp)⟩
        · exact hsf ge (List.mem_cons_of_mem _ h)
      · rw [List.pairwise_cons]
        exact ⟨fun b hb => (hcop b (List.mem_cons_of_mem _ hb)).mul_left (hpair.1 b hb), hpair.2⟩
    · obtain ⟨ihsf, ihpair⟩ := ih (fun ge hge => hcop ge (List.mem_cons_of_mem _ hge))
        (fun ge hge => hsf ge (List.mem_cons_of_mem _ hge)) hpair.2
      refine ⟨?_, ?_⟩
      · intro ge hge
        rw [List.mem_cons] at hge
        rcases hge with h | h
        · subst h; exact hsf (g',e') (by simp)
        · exact ihsf ge h
      · rw [List.pairwise_cons]
        exact ⟨insertMult_isRelPrime g' g e (hcop (g',e') (by simp)).symm rest hpair.1, ihpair⟩

/-- Folding `insertMult` over a squarefree + pairwise-coprime list (each element
coprime to the initial accumulator) preserves the invariant. -/
theorem foldl_insertMult_inv :
    ∀ (l init : List (AzMvPolynomial n AzInt ord × ℕ)),
      (∀ ge ∈ l, Squarefree ge.1) → l.Pairwise (fun a b => IsRelPrime a.1 b.1) →
      (∀ ge ∈ init, Squarefree ge.1) → init.Pairwise (fun a b => IsRelPrime a.1 b.1) →
      (∀ a ∈ l, ∀ b ∈ init, IsRelPrime a.1 b.1) →
      (∀ ge ∈ l.foldl (fun acc ge => insertMult acc ge.1 ge.2) init, Squarefree ge.1) ∧
        (l.foldl (fun acc ge => insertMult acc ge.1 ge.2) init).Pairwise
          (fun a b => IsRelPrime a.1 b.1) := by
  intro l
  induction l with
  | nil => intro init _ _ hisf hipair _; exact ⟨hisf, hipair⟩
  | cons a rest ih =>
    intro init hsf hpair hisf hipair hcross
    rw [List.pairwise_cons] at hpair
    simp only [List.foldl_cons]
    obtain ⟨isf', ipair'⟩ := insertMult_inv a.1 a.2 (hsf a (by simp)) init
      (fun b hb => (hcross a (by simp) b hb)) hisf hipair
    refine ih (insertMult init a.1 a.2)
      (fun ge hge => hsf ge (List.mem_cons_of_mem _ hge)) hpair.2 isf' ipair' ?_
    intro b hb c hc
    exact insertMult_isRelPrime b.1 a.1 a.2 (hpair.1 b hb).symm init
      (fun d hd => hcross b (List.mem_cons_of_mem _ hb) d hd) c hc

/-- `mergeByMult` preserves the "all squarefree + pairwise coprime" invariant. -/
theorem mergeByMult_inv (l : List (AzMvPolynomial n AzInt ord × ℕ))
    (hsf : ∀ ge ∈ l, Squarefree ge.1) (hpair : l.Pairwise (fun a b => IsRelPrime a.1 b.1)) :
    (∀ ge ∈ mergeByMult l, Squarefree ge.1) ∧
      (mergeByMult l).Pairwise (fun a b => IsRelPrime a.1 b.1) :=
  foldl_insertMult_inv l [] hsf hpair (by simp) List.Pairwise.nil (by simp)

/-- The final `mergeSort` preserves the invariant (it is a permutation, and both
membership and pairwise-`IsRelPrime` — a symmetric relation — are `Perm`-invariant). -/
theorem mergeSort_inv (l : List (AzMvPolynomial n AzInt ord × ℕ)) (r)
    (hsf : ∀ ge ∈ l, Squarefree ge.1) (hpair : l.Pairwise (fun a b => IsRelPrime a.1 b.1)) :
    (∀ ge ∈ l.mergeSort r, Squarefree ge.1) ∧
      (l.mergeSort r).Pairwise (fun a b => IsRelPrime a.1 b.1) := by
  have hperm := List.mergeSort_perm l r
  exact ⟨fun ge hge => hsf ge (hperm.mem_iff.mp hge),
    (hperm.pairwise_iff
      (fun {a b : AzMvPolynomial n AzInt ord × ℕ} (h : IsRelPrime a.1 b.1) => h.symm)).mpr hpair⟩

set_option maxHeartbeats 800000 in
/-- **Squarefreeness and pairwise coprimality together** (GCL Algorithm 8.2,
multivariate, correctness 2 & 3): for a ℤ-primitive input, every factor of
`mvSquarefreeFactorization P` is squarefree and the factors are pairwise
`IsRelPrime`. Proved by one induction on the variable count, threading the joint
invariant through `mergeByMult`/`mergeSort`. -/
theorem mvSquarefreeFactorization_squarefree_coprime :
    ∀ {n : ℕ} (P : AzMvPolynomial n AzInt ord), intContent P = 1 →
      (∀ ge ∈ mvSquarefreeFactorization P, Squarefree ge.1) ∧
        (mvSquarefreeFactorization P).Pairwise (fun a b => IsRelPrime a.1 b.1) := by
  intro n
  induction n with
  | zero =>
    intro P _
    rw [show mvSquarefreeFactorization P = [] from rfl]
    exact ⟨by simp, List.Pairwise.nil⟩
  | succ m ih =>
    intro P hP
    have hP0 : P ≠ 0 := by
      rintro rfl
      rw [show intContent (0 : AzMvPolynomial (m + 1) AzInt ord) = 0 from rfl] at hP
      exact absurd hP (by decide)
    have hEmbedDvd : renameInjective (content P) Fin.succ (Fin.succ_injective m) ∣ P := by
      refine ⟨primitivePart P, ?_⟩
      apply (peelEquiv m).injective
      rw [map_mul, peelEquiv_embed, peelEquiv_content_mul_primitivePart P]
    have hcContent : intContent (content P) = 1 :=
      (intContent_renameInjective_eq_one_iff (content P)).mp
        (intContent_eq_one_of_dvd hEmbedDvd hP)
    have hprim : (AzPolynomial.toPoly (finSuccEquiv (primitivePart P))).IsPrimitive := by
      rw [← peelEquiv_apply]; exact peelEquiv_primitivePart_isPrimitive P hP0
    have hpp_sf := Azurite.AzPolynomial.UFD.squarefreeFactorization_squarefree'
      tower_hgcd_law (finSuccEquiv (primitivePart P)) hprim
    have hpp_pair := Azurite.AzPolynomial.UFD.squarefreeFactorization_pairwise_coprime'
      tower_hgcd_law (finSuccEquiv (primitivePart P)) hprim
    obtain ⟨hc_sf, hc_pair⟩ := ih (content P) hcContent
    have hA : ∀ ge ∈ (AzPolynomial.squarefreeFactorization (finSuccEquiv (primitivePart P))).map
          (fun ge => (finSuccEquivSymm ge.1, ge.2))
        ++ (mvSquarefreeFactorization (content P)).map
          (fun ge => (renameInjective ge.1 Fin.succ (Fin.succ_injective m), ge.2)),
        Squarefree ge.1 := by
      intro ge hge
      rw [List.mem_append] at hge
      rcases hge with hge | hge
      · obtain ⟨gi, hgi, rfl⟩ := List.mem_map.mp hge
        exact (squarefree_ringEquiv (peelEquiv m)).mp
          (by rw [peelEquiv_finSuccEquivSymm]; exact (hpp_sf gi hgi).1)
      · obtain ⟨cj, hcj, rfl⟩ := List.mem_map.mp hge
        exact (squarefree_ringEquiv (peelEquiv m)).mp
          (by rw [peelEquiv_embed]; exact squarefree_C_of (hc_sf cj hcj))
    have hB : ((AzPolynomial.squarefreeFactorization (finSuccEquiv (primitivePart P))).map
          (fun ge => (finSuccEquivSymm ge.1, ge.2))
        ++ (mvSquarefreeFactorization (content P)).map
          (fun ge => (renameInjective ge.1 Fin.succ (Fin.succ_injective m), ge.2))).Pairwise
        (fun a b => IsRelPrime a.1 b.1) := by
      rw [List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.pairwise_map]
        exact hpp_pair.imp fun {gi gj} h => (isRelPrime_ringEquiv (peelEquiv m)).mp
          (by rw [peelEquiv_finSuccEquivSymm, peelEquiv_finSuccEquivSymm]; exact h)
      · rw [List.pairwise_map]
        exact hc_pair.imp fun {cj cj'} h => (isRelPrime_ringEquiv (peelEquiv m)).mp
          (by rw [peelEquiv_embed, peelEquiv_embed]; exact isRelPrime_C_C_of h)
      · intro a ha b hb
        obtain ⟨gi, hgi, rfl⟩ := List.mem_map.mp ha
        obtain ⟨cj, hcj, rfl⟩ := List.mem_map.mp hb
        refine (isRelPrime_ringEquiv (peelEquiv m)).mp ?_
        rw [peelEquiv_finSuccEquivSymm, peelEquiv_embed]
        exact isRelPrime_C_of_isPrimitive (hpp_sf gi hgi).2 (hc_sf cj hcj).ne_zero
    rw [mvSquarefreeFactorization_succ]
    obtain ⟨hmsf, hmpair⟩ := mergeByMult_inv _ hA hB
    exact mergeSort_inv _ _ hmsf hmpair

/-- **Squarefreeness** (GCL Algorithm 8.2, multivariate, correctness 2). -/
theorem mvSquarefreeFactorization_squarefree {n : ℕ} (P : AzMvPolynomial n AzInt ord)
    (hP : intContent P = 1) : ∀ ge ∈ mvSquarefreeFactorization P, Squarefree ge.1 :=
  (mvSquarefreeFactorization_squarefree_coprime P hP).1

/-- **Pairwise coprimality** (GCL Algorithm 8.2, multivariate, correctness 3): over
the non-Bézout UFD `AzMvPolynomial n AzInt ord` the right notion is `IsRelPrime`. -/
theorem mvSquarefreeFactorization_pairwise_coprime {n : ℕ} (P : AzMvPolynomial n AzInt ord)
    (hP : intContent P = 1) :
    (mvSquarefreeFactorization P).Pairwise (fun a b => IsRelPrime a.1 b.1) :=
  (mvSquarefreeFactorization_squarefree_coprime P hP).2

/-! ### The exact product identity under a normalized input

The algorithm is sign-faithful — its factors match neither `P` nor `normalize P`
on non-normalized input (only up to a unit). Adding `normalize P = P` (matching the
univariate `_prod`'s `hnorm`) pins the product down exactly, using the EXACT tower
product (not the `_associated` variant). The recursion preserves normalization:
`primitivePart P` and `content P` stay normalized (verified below). -/

/-- `modelEquiv` intertwines `normalize` (its `NormalizedGCDMonoid` is transported
along it). -/
theorem modelEquiv_normalize (X : AzMvPolynomial n AzInt ord) :
    normalize (modelEquiv n X) = modelEquiv n (normalize X) := by
  have h := (modelEquiv (ord := ord) n).transfer_normalize X
  rw [h, RingEquiv.apply_symm_apply]

/-- `normalize` commutes with `Polynomial.C`. -/
theorem normalize_C_poly {S : Type _} [CommRing S] [IsDomain S]
    [StrongNormalizedGCDMonoid S] (x : S) :
    normalize (Polynomial.C x) = Polynomial.C (normalize x) := by
  rw [normalize_apply, normalize_apply, Polynomial.coe_normUnit, Polynomial.leadingCoeff_C,
    ← Polynomial.C_mul]

/-- **`primPart` of a normalized polynomial is normalized** (generic): from
`p = C(content p)·primPart p`, `normalize (content p) = content p`, and cancelling. -/
theorem normalize_primPart_of_normalize {S : Type _} [CommRing S] [IsDomain S]
    [StrongNormalizedGCDMonoid S] {q : Polynomial S} (hq0 : q ≠ 0)
    (hqn : normalize q = q) :
    normalize q.primPart = q.primPart := by
  have hcontent0 : q.content ≠ 0 := fun h => hq0 (Polynomial.content_eq_zero_iff.mp h)
  have hC0 : (Polynomial.C q.content : Polynomial S) ≠ 0 :=
    fun h => hcontent0 (Polynomial.C_eq_zero.mp h)
  have hcnorm : normalize q.content = q.content := Polynomial.normalize_content
  have hqeq : q = Polynomial.C q.content * q.primPart := q.eq_C_content_mul_primPart
  have h1 : normalize q = Polynomial.C q.content * normalize q.primPart := by
    conv_lhs => rw [hqeq]
    rw [normalize_mul, normalize_C_poly, hcnorm]
  exact mul_left_cancel₀ hC0 (h1.symm.trans (hqn.trans hqeq))

/-- **Sub-fact 2**: the `x₀`-content is normalized (it is the normalized gcd). -/
theorem content_normalize (P : AzMvPolynomial (n + 1) AzInt ord) :
    normalize (AzMvPolynomial.content P) = AzMvPolynomial.content P := by
  apply (modelEquiv n).injective
  rw [← modelEquiv_normalize]
  have hmc : modelEquiv n (AzMvPolynomial.content P) = (modelEquiv (n + 1) P).content := by
    rw [modelEquiv_apply, AzMvPolynomial.towerBridge_toNested_content, ← modelEquiv_apply]
  rw [hmc, Polynomial.normalize_content]

/-- **Sub-fact 1**: when `P` is normalized, its `x₀`-primitive part is normalized
(as a polynomial over `AzMvPolynomial n`, via the `x₀`-peel). Proved at the model
tower: `modelEquiv (primitivePart P) = primPart (modelEquiv P)`, and `primPart` of a
normalized polynomial is normalized. -/
theorem tower_normalize_primitivePart (P : AzMvPolynomial (n + 1) AzInt ord) (hP0 : P ≠ 0)
    (hnorm : normalize P = P) :
    normalize (peelEquiv n (primitivePart P)) = peelEquiv n (primitivePart P) := by
  set e := (modelEquiv (ord := ord) n : AzMvPolynomial n AzInt ord →+* ModelPoly n) with he
  have hf_inj : Function.Injective (Polynomial.map e) :=
    Polynomial.map_injective e (modelEquiv n).injective
  apply hf_inj
  rw [map_normalize]
  have hqnorm : normalize (modelEquiv (n + 1) P) = modelEquiv (n + 1) P := by
    rw [modelEquiv_normalize, hnorm]
  have hq0 : (modelEquiv (n + 1) P) ≠ 0 := by
    simpa using (modelEquiv (ord := ord) (n + 1)).injective.ne hP0
  have hmp_pp : Polynomial.map e (peelEquiv n (primitivePart P))
      = (modelEquiv (n + 1) P).primPart := by
    rw [peelEquiv_apply, ← modelEquiv_succ, modelEquiv_apply,
      AzMvPolynomial.towerBridge_toNested_primitivePart hP0, ← modelEquiv_apply]
  rw [hmp_pp]
  exact normalize_primPart_of_normalize hq0 hqnorm

set_option maxHeartbeats 800000 in
/-- **The exact multivariate square-free factorization product** (GCL Algorithm 8.2,
multivariate): for a ℤ-primitive AND normalized input, the product of the factor
powers is exactly `P` (the `Associated` identity pinned down by `hnorm`). Uses the
EXACT univariate tower product; normalization is preserved through the recursion
(`tower_normalize_primitivePart`, `content_normalize`). -/
theorem mvSquarefreeFactorization_prod_eq :
    ∀ {n : ℕ} (P : AzMvPolynomial n AzInt ord), intContent P = 1 → normalize P = P →
      prodPow (mvSquarefreeFactorization P) = P := by
  intro n
  induction n with
  | zero =>
    intro P hP hnorm
    rw [show mvSquarefreeFactorization P = [] from rfl, prodPow, List.map_nil, List.prod_nil]
    exact (hnorm.symm.trans (normalize_eq_one.mpr (base_isUnit P hP))).symm
  | succ m ih =>
    intro P hP hnorm
    have hP0 : P ≠ 0 := by
      rintro rfl
      rw [show intContent (0 : AzMvPolynomial (m + 1) AzInt ord) = 0 from rfl] at hP
      exact absurd hP (by decide)
    have hEmbedDvd : renameInjective (content P) Fin.succ (Fin.succ_injective m) ∣ P := by
      refine ⟨primitivePart P, ?_⟩
      apply (peelEquiv m).injective
      rw [map_mul, peelEquiv_embed, peelEquiv_content_mul_primitivePart P]
    have hcContent : intContent (content P) = 1 :=
      (intContent_renameInjective_eq_one_iff (content P)).mp
        (intContent_eq_one_of_dvd hEmbedDvd hP)
    have hcnorm : normalize (content P) = content P := content_normalize P
    have hprim : (AzPolynomial.toPoly (finSuccEquiv (primitivePart P))).IsPrimitive := by
      rw [← peelEquiv_apply]; exact peelEquiv_primitivePart_isPrimitive P hP0
    have hnorm_tower : normalize (AzPolynomial.toPoly (finSuccEquiv (primitivePart P)))
        = AzPolynomial.toPoly (finSuccEquiv (primitivePart P)) := by
      rw [← peelEquiv_apply]; exact tower_normalize_primitivePart P hP0 hnorm
    have hpp_peel : peelEquiv m (prodPow ((AzPolynomial.squarefreeFactorization
          (finSuccEquiv (primitivePart P))).map (fun ge => (finSuccEquivSymm ge.1, ge.2))))
        = peelEquiv m (primitivePart P) := by
      rw [peelEquiv_prodPow, List.map_map]
      have hmap : ((AzPolynomial.squarefreeFactorization (finSuccEquiv (primitivePart P))).map
            ((fun ge => peelEquiv m ge.1 ^ ge.2) ∘ fun ge => (finSuccEquivSymm ge.1, ge.2)))
          = (AzPolynomial.squarefreeFactorization (finSuccEquiv (primitivePart P))).map
              (fun ge => AzPolynomial.toPoly ge.1 ^ ge.2) := by
        apply List.map_congr_left
        intro ge _
        simp [Function.comp, peelEquiv_finSuccEquivSymm]
      rw [hmap, peelEquiv_apply]
      exact Azurite.AzPolynomial.UFD.squarefreeFactorization_prod
        tower_hgcd_law (finSuccEquiv (primitivePart P)) hprim hnorm_tower
    have hcc_peel : peelEquiv m (prodPow ((mvSquarefreeFactorization (content P)).map
          (fun ge => (renameInjective ge.1 Fin.succ (Fin.succ_injective m), ge.2))))
        = Polynomial.C (content P) := by
      have hcalc : peelEquiv m (prodPow ((mvSquarefreeFactorization (content P)).map
            (fun ge => (renameInjective ge.1 Fin.succ (Fin.succ_injective m), ge.2))))
          = Polynomial.C (prodPow (mvSquarefreeFactorization (content P))) := by
        rw [peelEquiv_prodPow, List.map_map, prodPow, map_list_prod, List.map_map]
        congr 1
        apply List.map_congr_left
        intro ge _
        simp [Function.comp, peelEquiv_embed, map_pow]
      rw [hcalc, ih (content P) hcContent hcnorm]
    have heq : prodPow (mvSquarefreeFactorization P)
        = prodPow ((AzPolynomial.squarefreeFactorization (finSuccEquiv (primitivePart P))).map
            (fun ge => (finSuccEquivSymm ge.1, ge.2)))
          * prodPow ((mvSquarefreeFactorization (content P)).map
            (fun ge => (renameInjective ge.1 Fin.succ (Fin.succ_injective m), ge.2))) := by
      rw [mvSquarefreeFactorization_succ, mergeSort_prodPow, mergeByMult_prodPow, prodPow_append]
    rw [heq]
    apply (peelEquiv m).injective
    rw [map_mul, hpp_peel, hcc_peel, mul_comm, ← peelEquiv_content_mul_primitivePart]

end Azurite.AzMvPolynomial
