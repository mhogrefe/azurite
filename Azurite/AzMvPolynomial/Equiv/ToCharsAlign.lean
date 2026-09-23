/-
  Cross-dimension printer alignment for the univariate embedding.

  `AzPolynomial.toChars P` renders `P` by lifting it into a one-variable
  `AzMvPolynomial` (variable index `0`, ordering `.Degrevlex`) and printing
  with the `XyzVar 1` scheme (so the variable prints as `x`).  This file shows
  that the exact same character list results from lifting `P` into variable `0`
  of an `n`-variable `AzMvPolynomial` under *any* monomial ordering and printing
  with `XyzVar n`:

  `(AzPolynomial.toChars P).toList = toCharsWith (XyzVar n) (P.toAzMvPolynomial ⟨0,hn⟩ ord)`.

  The lift populates only coordinate `0`; the always-zero extra coordinates emit
  nothing, and both `XyzVar 1` and `XyzVar n` name variable `0` as `x`, so the
  two renderings are byte-identical.
-/
import Azurite.AzPolynomial.ToString
import Azurite.AzMvPolynomial.Equiv.CompareEmbed

namespace Azurite

/-! ### Primitive: `filterMap` selecting a single unique index -/

private theorem filterMap_single {α β : Type} [DecidableEq α] (l : List α) (a : α) (c : β)
    (hmem : a ∈ l) (hnodup : l.Nodup) :
    l.filterMap (fun i => if i = a then some c else none) = [c] := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    rw [List.nodup_cons] at hnodup
    by_cases hx : x = a
    · have hxs : a ∉ xs := hx ▸ hnodup.1
      have hrest : xs.filterMap (fun i => if i = a then some c else none) = [] := by
        rw [List.filterMap_eq_nil_iff]; intro i hi
        exact ite_eq_right (fun (h : i = a) => hxs (h ▸ hi))
      rw [List.filterMap_cons_some (b := c) (by simp [hx]), hrest]
    · rw [List.filterMap_cons_none (by simp [hx])]
      exact ih ((List.mem_cons.mp hmem).resolve_left (Ne.symm hx)) hnodup.2

/-! ### The variable at index `0` prints as `x` under `XyzVar` -/

private theorem xyz_varChars_zero (m : ℕ) [Fact (m ≤ 26)] (h : 0 < m) :
    (ParsableVar.toChars (Var.ofFin (⟨0, h⟩ : Fin m) : XyzVar m)) = ['x'] := by
  show [(XyzVar.ofIndex (Fact.out) (⟨0, h⟩ : Fin m)).ch] = ['x']
  simp only [XyzVar.ofIndex]
  decide +kernel

/-! ### `MonicMonomial`-level: `xᵢ^k` prints the same regardless of dimension -/

/-- The `XyzVar`-rendering of the monic monomial `x₀^k` depends only on `k`. -/
private theorem monic_charsWith_ofVarPow
    {m : ℕ} [Fact (m ≤ 26)] {ord : MonomialOrder} (h : 0 < m) (k : ℕ) :
    (MonicMonomial.ofVarPow (⟨0, h⟩ : Fin m) k : MonicMonomial m ord).toCharsWith (XyzVar m)
      = (if k = 0 then [] else if k = 1 then ['x'] else ['x'] ++ '^' :: natToChars k) := by
  unfold MonicMonomial.toCharsWith
  simp only [MonicMonomial.ofVarPow_exponent]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [ite_eq_right hk]
    have hfun : (fun i : Fin m =>
        if (if (⟨0, h⟩ : Fin m) = i then k else 0) = 0 then none
        else if (if (⟨0, h⟩ : Fin m) = i then k else 0) = 1
          then some (ParsableVar.toChars (Var.ofFin i : XyzVar m))
          else some (ParsableVar.toChars (Var.ofFin i : XyzVar m) ++
            '^' :: natToChars (if (⟨0, h⟩ : Fin m) = i then k else 0)))
        = fun i => if i = (⟨0, h⟩ : Fin m)
            then some (if k = 1 then (['x'] : List Char) else ['x'] ++ '^' :: natToChars k)
            else none := by
      funext i
      by_cases hi : (⟨0, h⟩ : Fin m) = i
      · subst hi
        simp only [ite_true, xyz_varChars_zero]
        by_cases hk1 : k = 1 <;> simp [hk, hk1]
      · simp only [ite_eq_right hi, ite_eq_right (Ne.symm hi), ite_true]
    rw [hfun, filterMap_single _ (⟨0, h⟩ : Fin m) _ (List.mem_finRange _) (List.nodup_finRange _)]
    simp [List.intercalate]

/-! ### `Monomial`-level: `c · x₀^k` prints the same regardless of dimension -/

private theorem ofVarPow_ne_one {m : ℕ} {ord : MonomialOrder} (h : 0 < m) (k : ℕ) (hk : k ≠ 0) :
    (MonicMonomial.ofVarPow (⟨0, h⟩ : Fin m) k : MonicMonomial m ord) ≠ 1 := by
  intro he
  have hx := congrArg (fun v => v.exponents[(⟨0, h⟩ : Fin m)]) he
  simp only [MonicMonomial.ofVarPow_exponent] at hx
  simp at hx
  exact hk hx

private theorem monomial_charsWith_eq {R : Type _} [Semiring R] [DecidableEq R]
    [NeZero (1 : R)] [ParsableCoeff R]
    {m₁ m₂ : ℕ} [Fact (m₁ ≤ 26)] [Fact (m₂ ≤ 26)] {ord₁ ord₂ : MonomialOrder}
    (h1 : 0 < m₁) (h2 : 0 < m₂) (c : {c : R // c ≠ 0}) (k : ℕ) :
    (⟨c, MonicMonomial.ofVarPow (⟨0, h1⟩ : Fin m₁) k⟩ :
        Monomial m₁ R ord₁).toCharsWith (XyzVar m₁)
      = (⟨c, MonicMonomial.ofVarPow (⟨0, h2⟩ : Fin m₂) k⟩ :
        Monomial m₂ R ord₂).toCharsWith (XyzVar m₂) := by
  by_cases hk : k = 0
  · subst hk
    simp [Monomial.toCharsWith, MonicMonomial.ofVarPow_zero]
  · unfold Monomial.toCharsWith
    rw [ite_eq_right (ofVarPow_ne_one h1 k hk), ite_eq_right (ofVarPow_ne_one h2 k hk)]
    simp only [monic_charsWith_ofVarPow]

/-! ### `termsBelow`-level: the mapped char-lists agree -/

private theorem termsBelow_map_charsWith_eq {R : Type _} [Semiring R] [LinearOrder R]
    [NeZero (1 : R)] [ParsableCoeff R]
    {m₁ m₂ : ℕ} [Fact (m₁ ≤ 26)] [Fact (m₂ ≤ 26)] {ord₁ ord₂ : MonomialOrder}
    (h1 : 0 < m₁) (h2 : 0 < m₂) (coeffs : Array R) (N : ℕ) :
    (termsBelow (⟨0, h1⟩ : Fin m₁) coeffs (ord := ord₁) N).map
        (fun t => t.toCharsWith (XyzVar m₁))
      = (termsBelow (⟨0, h2⟩ : Fin m₂) coeffs (ord := ord₂) N).map
        (fun t => t.toCharsWith (XyzVar m₂)) := by
  induction N with
  | zero => simp [termsBelow_zero]
  | succ k ih =>
    rw [termsBelow_succ, termsBelow_succ]
    by_cases hc : (coeffs[k]?).getD 0 = 0
    · rw [dite_eq_left hc, dite_eq_left hc]; exact ih
    · rw [dite_eq_right hc, dite_eq_right hc, List.map_cons, List.map_cons, ih,
        monomial_charsWith_eq h1 h2 ⟨_, hc⟩ k]

/-! ### Poly-level: the two `toCharsWith` outputs agree -/

private theorem toCharsWith_toAzMv_eq {R : Type _} [Semiring R] [LinearOrder R]
    [NeZero (1 : R)] [ParsableCoeff R]
    {m₁ m₂ : ℕ} [Fact (m₁ ≤ 26)] [Fact (m₂ ≤ 26)] {ord₁ ord₂ : MonomialOrder}
    (h1 : 0 < m₁) (h2 : 0 < m₂) (P : AzPolynomial R) :
    (P.toAzMvPolynomial (⟨0, h1⟩ : Fin m₁) ord₁).toCharsWith (XyzVar m₁)
      = (P.toAzMvPolynomial (⟨0, h2⟩ : Fin m₂) ord₂).toCharsWith (XyzVar m₂) := by
  have hmap : (termsBelow (⟨0, h1⟩ : Fin m₁) P.coeffs (ord := ord₁) P.coeffs.size).map
        (fun t => t.toCharsWith (XyzVar m₁))
      = (termsBelow (⟨0, h2⟩ : Fin m₂) P.coeffs (ord := ord₂) P.coeffs.size).map
        (fun t => t.toCharsWith (XyzVar m₂)) :=
    termsBelow_map_charsWith_eq h1 h2 P.coeffs P.coeffs.size
  -- the emptiness flags coincide (the mapped lists are equal ⇒ same `isEmpty`)
  have key : (termsBelow (⟨0, h1⟩ : Fin m₁) P.coeffs (ord := ord₁) P.coeffs.size).isEmpty
      = (termsBelow (⟨0, h2⟩ : Fin m₂) P.coeffs (ord := ord₂) P.coeffs.size).isEmpty := by
    have h := congrArg List.isEmpty hmap
    simpa only [List.isEmpty_map] using h
  have hEmpty : (P.toAzMvPolynomial (⟨0, h1⟩ : Fin m₁) ord₁).terms.isEmpty
      = (P.toAzMvPolynomial (⟨0, h2⟩ : Fin m₂) ord₂).terms.isEmpty := by
    rw [← Array.isEmpty_toList, ← Array.isEmpty_toList,
      image_terms_toList, image_terms_toList]
    exact key
  unfold AzMvPolynomial.toCharsWith
  rw [image_terms_toList, image_terms_toList, hEmpty, hmap]

/-! ### The alignment theorem -/

/-- Cross-dimension printer alignment: `AzPolynomial.toChars P` (which renders
`P` via a one-variable lift printed with `XyzVar 1`) produces exactly the char
list obtained by lifting `P` into variable `0` of an `n`-variable polynomial
under any monomial ordering and printing with `XyzVar n`. -/
theorem AzMvPolynomial.toChars_toAzMvPolynomial_align
    {n : ℕ} (hn : 0 < n) [Fact (n ≤ 26)] {ord : MonomialOrder}
    (P : AzPolynomial AzInt) :
    (AzPolynomial.toChars P).toList
      = AzMvPolynomial.toCharsWith (XyzVar n) (P.toAzMvPolynomial (⟨0, hn⟩ : Fin n) ord) := by
  rw [AzPolynomial.toChars, AzMvPolynomial.toStrWith, String.toList_ofList]
  exact toCharsWith_toAzMv_eq Nat.zero_lt_one hn P

end Azurite
