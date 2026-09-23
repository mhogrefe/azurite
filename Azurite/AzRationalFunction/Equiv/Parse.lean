import Azurite.AzRationalFunction.Parse
import Azurite.AzRationalFunction.Equiv.Basic
import Azurite.AzPolynomial.ParseToString
import Batteries.Tactic.OpenPrivate

/-!
# Round-trip: `parse (toString r) = some r`

The string form of a canonical rational function parses back to it. Two
ingredients:

* **display correctness** — `ofNumDen (displayNum r) (displayDen r) = r`
  (the displayed integer fraction re-normalizes to the original), proved
  semantically through `toRatFunc`;
* **string plumbing** — the polynomial printer emits no `/`, `(`, or `)`,
  so `splitSlash` finds exactly the separator `/` and `stripParens` strips
  exactly the wrapping parentheses.
-/

namespace Azurite.AzRationalFunction

open Polynomial
open Azurite.AzPolynomial (parseAzPolynomial)

/-! ### Display correctness -/

private theorem algebraMapQ_eq_C' :
    algebraMap ℚ (RatFunc ℚ) = (RatFunc.C : ℚ →+* RatFunc ℚ) :=
  RingHom.ext_rat _ _

/-- The fused image of a scalar multiple. -/
private theorem toPolyQ_smul (c : AzInt) (p : Azurite.AzPolynomial AzInt) :
    toPolyQ (c • p) = Polynomial.C ((c.toInt : ℚ)) * toPolyQ p := by
  rw [toPolyQ, toPolyQ, Azurite.AzPolynomial.toPoly_smul, Polynomial.smul_eq_C_mul,
    Polynomial.map_mul, Polynomial.map_C]
  rfl

/-- The displayed denominator is nonzero. -/
theorem displayDen_ne_zero (r : AzRationalFunction) : displayDen r ≠ 0 := by
  intro h0
  have h1 : toPolyQ (displayDen r) = 0 := by
    rw [h0, toPolyQ, toPoly_zero, Polynomial.map_zero]
  rw [displayDen, toPolyQ_smul] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · have h3 : (((⟨true, r.factor.den, fun _ => rfl⟩ : AzInt).toInt : ℚ)) = 0 :=
      Polynomial.C_eq_zero.mp h2
    have h4 : ((r.factor.den.toNat : ℤ) : ℚ) = 0 := h3
    have h5 : r.factor.den.toNat = 0 := by exact_mod_cast h4
    exact r.factor.den_nz (Azurite.AzNat.toNat_injective (by rw [h5]; rfl))
  · exact toPolyQ_den_ne_zero r h2

/-- **Display correctness**: re-normalizing the displayed integer fraction
recovers the original rational function. -/
theorem ofNumDen_displayNum_displayDen (r : AzRationalFunction) :
    ofNumDen (displayNum r) (displayDen r) = r := by
  apply toRatFunc_injective
  rw [toRatFunc_ofNumDen _ _ (displayDen_ne_zero r), displayNum, displayDen,
    toPolyQ_smul, toPolyQ_smul]
  have hfac : Azurite.AzRat.toRat r.factor
      = (((⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt).toInt : ℚ))
        / (((⟨true, r.factor.den, fun _ => rfl⟩ : AzInt).toInt : ℚ)) := by
    rw [← Rat.num_div_den (Azurite.AzRat.toRat r.factor)]
    have hnum : (Azurite.AzRat.toRat r.factor).num
        = (⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt).toInt := rfl
    have hden : (((Azurite.AzRat.toRat r.factor).den : ℤ))
        = (⟨true, r.factor.den, fun _ => rfl⟩ : AzInt).toInt := rfl
    rw [hnum, ← hden]
    norm_cast
  rw [show toRatFunc r = algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat r.factor)
      * (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.num)
        / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.den)) from rfl,
    hfac, algebraMapQ_eq_C', map_div₀, ← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C,
    div_mul_div_comm, ← map_mul, ← map_mul]

/-! ### Character-class facts about the polynomial printer

The printer emits only digits, `x`-family variable letters, and the syntax
characters `+ - * ^`. In particular `(` (ASCII 40), `)` (41), and `/` (47)
never occur — the facts the string plumbing needs. -/

private theorem bad_notin_coeff {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47) (z : AzInt) :
    b ∉ (ParsableCoeff.toChars z : List Char) := by
  intro hmem
  have h1 : (ParsableCoeff.toChars z : List Char) = AzInt.toChars z := rfl
  rw [h1] at hmem
  rcases Azurite.AzInt.mem_toChars_digit_or_dash z b hmem with h2 | ⟨h3, h4⟩
  · rw [h2] at hb
    exact absurd hb (by decide)
  · have h5 : ('0' : Char).toNat = 48 := rfl
    have h6 : ('9' : Char).toNat = 57 := rfl
    omega

private theorem bad_notin_monic {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47) {ord : MonomialOrder}
    (m : MonicMonomial 1 ord) : b ∉ m.toCharsWith (XyzVar 1) := by
  apply Azurite.MonicMonomial.char_notin_toCharsWith
  · intro v hv
    have h1 : (ParsableVar.toChars v : List Char) = [v.ch] := rfl
    rw [h1] at hv
    have h2 : b = v.ch := List.mem_singleton.mp hv
    have h3 := v.is_valid.1
    have h4 : ('a' : Char).toNat = 97 := rfl
    rw [← h2] at h3
    omega
  · intro k
    exact Azurite.AzPolynomial.not_mem_natToChars_of_not_digit b (Or.inl (by omega)) k
  · intro h
    rw [h] at hb
    exact absurd hb (by decide)
  · intro h
    rw [h] at hb
    exact absurd hb (by decide)

private theorem bad_notin_monomialChars {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47) {ord : MonomialOrder}
    (m : Monomial 1 AzInt ord) : b ∉ m.toCharsWith (XyzVar 1) := by
  intro hmem
  unfold Azurite.Monomial.toCharsWith at hmem
  split at hmem
  · exact bad_notin_coeff hb _ hmem
  · split at hmem
    · exact bad_notin_monic hb _ hmem
    · split at hmem
      · -- a negative-one coefficient constant is available
        split at hmem
        · rcases List.mem_cons.mp hmem with h2 | h2
          · rw [h2] at hb
            exact absurd hb (by decide)
          · exact bad_notin_monic hb _ h2
        · rcases List.mem_append.mp hmem with h2 | h2
          · rcases List.mem_append.mp h2 with h3 | h3
            · exact bad_notin_coeff hb _ h3
            · rw [List.mem_singleton.mp h3] at hb
              exact absurd hb (by decide)
          · exact bad_notin_monic hb _ h2
      · rcases List.mem_append.mp hmem with h2 | h2
        · rcases List.mem_append.mp h2 with h3 | h3
          · exact bad_notin_coeff hb _ h3
          · rw [List.mem_singleton.mp h3] at hb
            exact absurd hb (by decide)
        · exact bad_notin_monic hb _ h2

private theorem bad_notin_joinAux {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47) (ms : List (List Char))
    (h : ∀ m ∈ ms, b ∉ m) : b ∉ Azurite.joinMonomialsAux ms := by
  induction ms with
  | nil =>
    intro hmem
    exact absurd hmem (by simp [Azurite.joinMonomialsAux])
  | cons m ms ih =>
    intro hmem
    unfold Azurite.joinMonomialsAux at hmem
    simp only [List.append_assoc, List.mem_append] at hmem
    rcases hmem with h1 | h1 | h1
    · -- the separator: `[]` or `['+']`
      split at h1
      · exact absurd h1 (by simp)
      · rw [List.mem_singleton.mp h1] at hb
        exact absurd hb (by decide)
    · exact h m List.mem_cons_self h1
    · exact ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) h1

private theorem bad_notin_join {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47) (ms : List (List Char))
    (h : ∀ m ∈ ms, b ∉ m) : b ∉ Azurite.joinMonomials ms := by
  cases ms with
  | nil =>
    intro hmem
    exact absurd hmem (by simp [Azurite.joinMonomials])
  | cons m ms =>
    intro hmem
    unfold Azurite.joinMonomials at hmem
    rcases List.mem_append.mp hmem with h1 | h1
    · exact h m List.mem_cons_self h1
    · exact bad_notin_joinAux hb ms (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) h1

private theorem bad_notin_mvChars {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47) {ord : MonomialOrder}
    (q : AzMvPolynomial 1 AzInt ord) :
    b ∉ AzMvPolynomial.toCharsWith (XyzVar 1) q := by
  unfold AzMvPolynomial.toCharsWith
  split
  · exact bad_notin_coeff hb 0
  · apply bad_notin_join hb
    intro mchars hmem
    obtain ⟨mono, _, rfl⟩ := List.mem_map.mp hmem
    exact bad_notin_monomialChars hb mono

/-- The polynomial printer never emits `(`, `)`, or `/`. -/
private theorem bad_notin_polyChars {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47)
    (p : Azurite.AzPolynomial AzInt) :
    b ∉ (Azurite.AzPolynomial.toChars p).toList := by
  unfold Azurite.AzPolynomial.toChars
  rw [AzMvPolynomial.toStrWith, String.toList_ofList]
  exact bad_notin_mvChars hb _

private theorem h40 : ('(' : Char).toNat = 40 ∨ ('(' : Char).toNat = 41
    ∨ ('(' : Char).toNat = 47 := by decide

private theorem h41 : (')' : Char).toNat = 40 ∨ (')' : Char).toNat = 41
    ∨ (')' : Char).toNat = 47 := by decide

private theorem h47 : ('/' : Char).toNat = 40 ∨ ('/' : Char).toNat = 41
    ∨ ('/' : Char).toNat = 47 := by decide

/-! ### `splitSlash` on printer output

`splitSlashAux` is private to `Parse.lean`; `open private` (Batteries) makes
it nameable here so the traversal lemmas can be stated and proved. -/

open private splitSlashAux from Azurite.AzRationalFunction.Parse

private theorem splitSlash_eq (cs : List Char) :
    splitSlash cs = splitSlashAux cs [] := rfl

private theorem myAux_slash (t : List Char) (acc : List Char) :
    splitSlashAux ('/' :: t) acc = some (acc.reverse, t) :=
  rfl

private theorem myAux_cons_other {c : Char} (h3 : c ≠ '/') (t : List Char)
    (acc : List Char) :
    splitSlashAux (c :: t) acc = splitSlashAux t (c :: acc) := by
  conv_lhs => unfold splitSlashAux
  split
  · rename_i heq
    exact absurd heq (by simp)
  · rename_i t' heq
    injection heq with h1 h2
    exact absurd h1 h3
  · rename_i c' t' hne heq
    injection heq with h1 h2
    rw [h1, h2]

/-- Traverse a slash-free run: the characters transfer to the accumulator. -/
private theorem myAux_run (cs : List Char) (hs : '/' ∉ cs) :
    ∀ (rest : List Char) (acc : List Char),
      splitSlashAux (cs ++ rest) acc = splitSlashAux rest (cs.reverse ++ acc) := by
  induction cs with
  | nil =>
    intro rest acc
    simp
  | cons c t ih =>
    intro rest acc
    have hc3 : c ≠ '/' := fun h => hs (h ▸ List.mem_cons_self)
    rw [List.cons_append, myAux_cons_other hc3,
      ih (fun h => hs (List.mem_cons_of_mem _ h)) rest (c :: acc)]
    simp

/-- No slash: `splitSlash` returns `none`. -/
private theorem splitSlash_none (cs : List Char) (hs : '/' ∉ cs) :
    splitSlash cs = none := by
  rw [splitSlash_eq]
  have h1 := myAux_run cs hs [] []
  rw [List.append_nil] at h1
  rw [h1]
  rfl

/-- Splitting a slash-free word followed by `/`. -/
private theorem splitSlash_bare (cs : List Char) (hs : '/' ∉ cs) (rest : List Char) :
    splitSlash (cs ++ '/' :: rest) = some (cs, rest) := by
  rw [splitSlash_eq, myAux_run cs hs ('/' :: rest) [], myAux_slash]
  simp

/-! ### `stripParens` on printer output -/

private theorem stripParens_of_no_open (cs : List Char) (h : '(' ∉ cs) :
    stripParens cs = cs := by
  unfold stripParens
  split
  · exact absurd List.mem_cons_self h
  · rfl

private theorem stripParens_paren (cs : List Char) :
    stripParens ('(' :: cs ++ [')']) = cs := by
  show (match (cs ++ [')']).getLast? with
    | some ')' => (cs ++ [')']).dropLast
    | _ => '(' :: cs ++ [')']) = cs
  rw [List.getLast?_concat]
  show (cs ++ [')']).dropLast = cs
  rw [List.dropLast_concat]

/-! ### The wrapped components -/

private theorem ofList_toList (s : String) : String.ofList s.toList = s := by
  apply String.toList_inj.mp
  rw [String.toList_ofList]

/-- The two facts the parser needs about a wrapped component: it splits off
cleanly before a `/`, and it strips back to the raw printer output. -/
private theorem wrap_facts (p : Azurite.AzPolynomial AzInt) :
    (∀ rest, splitSlash ((wrapComponent p).toList ++ '/' :: rest)
        = some ((wrapComponent p).toList, rest))
    ∧ stripParens ((wrapComponent p).toList)
        = (Azurite.AzPolynomial.toChars p).toList := by
  unfold wrapComponent
  split
  · exact ⟨fun rest => splitSlash_bare _ (bad_notin_polyChars h47 p) rest,
      stripParens_of_no_open _ (bad_notin_polyChars h40 p)⟩
  · have hlist : ("(" ++ Azurite.AzPolynomial.toChars p ++ ")").toList
        = '(' :: (Azurite.AzPolynomial.toChars p).toList ++ [')'] := by
      rw [String.toList_append, String.toList_append]
      rfl
    rw [hlist]
    have hs : '/' ∉ ('(' :: (Azurite.AzPolynomial.toChars p).toList ++ [')']) := by
      intro hmem
      rcases List.mem_cons.mp hmem with h1 | h1
      · exact absurd h1 (by decide)
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact bad_notin_polyChars h47 p h2
        · exact absurd (List.mem_singleton.mp h2) (by decide)
    exact ⟨fun rest => splitSlash_bare _ hs rest, stripParens_paren _⟩

/-- The same two facts for the denominator wrapping rule (the branch proofs
do not depend on the wrapping condition, only on the two possible shapes). -/
private theorem wrapDen_facts (p : Azurite.AzPolynomial AzInt) :
    (∀ rest, splitSlash ((wrapDenominator p).toList ++ '/' :: rest)
        = some ((wrapDenominator p).toList, rest))
    ∧ stripParens ((wrapDenominator p).toList)
        = (Azurite.AzPolynomial.toChars p).toList := by
  unfold wrapDenominator
  split
  · exact ⟨fun rest => splitSlash_bare _ (bad_notin_polyChars h47 p) rest,
      stripParens_of_no_open _ (bad_notin_polyChars h40 p)⟩
  · have hlist : ("(" ++ Azurite.AzPolynomial.toChars p ++ ")").toList
        = '(' :: (Azurite.AzPolynomial.toChars p).toList ++ [')'] := by
      rw [String.toList_append, String.toList_append]
      rfl
    rw [hlist]
    have hs : '/' ∉ ('(' :: (Azurite.AzPolynomial.toChars p).toList ++ [')']) := by
      intro hmem
      rcases List.mem_cons.mp hmem with h1 | h1
      · exact absurd h1 (by decide)
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact bad_notin_polyChars h47 p h2
        · exact absurd (List.mem_singleton.mp h2) (by decide)
    exact ⟨fun rest => splitSlash_bare _ hs rest, stripParens_paren _⟩

/-- Printer output contains no slash at all. -/
private theorem splitSlash_wrap_none (p : Azurite.AzPolynomial AzInt) :
    splitSlash ((Azurite.AzPolynomial.toChars p).toList) = none :=
  splitSlash_none _ (bad_notin_polyChars h47 p)

/-! ### The round-trip -/

/-- **Round-trip**: parsing the string form of a canonical rational function
recovers it. -/
theorem parse_toString (r : AzRationalFunction) : parse (toString r) = some r := by
  by_cases hd1 : displayDen r = 1
  · -- denominator `1`: the string is just the numerator
    rw [toString, ite_eq_left (by rw [beq_iff_eq]; exact hd1), parse, splitSlash_wrap_none,
      stripParens_of_no_open _ (bad_notin_polyChars h40 _), ofList_toList,
      Azurite.AzPolynomial.parseAzPolynomial_toChars, Option.map_some]
    have h1 : ofPolynomial (displayNum r) = r := by
      show ofNumDen (displayNum r) 1 = r
      rw [← hd1]
      exact ofNumDen_displayNum_displayDen r
    rw [h1]
  · -- fraction form
    rw [toString, ite_eq_right (fun h => hd1 (beq_iff_eq.mp h)), parse]
    have hcs : (wrapComponent (displayNum r) ++ "/"
          ++ wrapDenominator (displayDen r)).toList
        = (wrapComponent (displayNum r)).toList
          ++ '/' :: (wrapDenominator (displayDen r)).toList := by
      rw [String.toList_append, String.toList_append]
      simp
    rw [hcs, (wrap_facts (displayNum r)).1 _]
    show (do
      let n ← parseAzPolynomial
        (String.ofList (stripParens (wrapComponent (displayNum r)).toList))
      let d ← parseAzPolynomial
        (String.ofList (stripParens (wrapDenominator (displayDen r)).toList))
      if d = 0 then none else some (ofNumDen n d)) = some r
    rw [(wrap_facts (displayNum r)).2, (wrapDen_facts (displayDen r)).2, ofList_toList,
      ofList_toList, Azurite.AzPolynomial.parseAzPolynomial_toChars,
      Azurite.AzPolynomial.parseAzPolynomial_toChars]
    show (if displayDen r = 0 then none
      else some (ofNumDen (displayNum r) (displayDen r))) = some r
    rw [ite_eq_right (displayDen_ne_zero r), ofNumDen_displayNum_displayDen r]

end Azurite.AzRationalFunction
