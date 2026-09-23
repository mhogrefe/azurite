import Azurite.AzMvRationalFunction.Parse
import Azurite.AzMvRationalFunction.Equiv.Basic
import Azurite.AzMvPolynomial.ParseToString
import Batteries.Tactic.OpenPrivate

/-!
# Round-trip: `parseStrWith F (toStrWith F r) = some r`

The string form of a canonical multivariate rational function parses back to
it. Two ingredients (mirroring univariate `AzRationalFunction`):

* **display correctness** — `ofNumDen (displayNum r) (displayDen r) = r`,
  proved semantically through `toMvRatFunc`;
* **string plumbing** — the multivariate polynomial printer (for a naming
  scheme `F` whose variable characters avoid `(`, `)`, `/`) emits none of
  those, so `splitSlash` finds exactly the separator `/` and `stripParens`
  strips exactly the wrapping parentheses.
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-! ### Display correctness -/

/-- The fused `ℚ[x⃗]`-image of a scalar multiple. -/
theorem toMvPolyQ_smul (c : AzInt) (p : AzMvPolynomial n AzInt ord) :
    toMvPolyQ (c • p) = MvPolynomial.C ((c.toInt : ℚ)) * toMvPolyQ p := by
  rw [toMvPolyQ_eq_map, toMvPoly_smul, Algebra.smul_def, map_mul, ← toMvPolyQ_eq_map]
  congr 1
  rw [show (algebraMap AzInt (MvPolynomial (Fin n) AzInt)) c = MvPolynomial.C c from rfl,
    MvPolynomial.map_C]
  rfl

/-- The displayed denominator is nonzero. -/
theorem displayDen_ne_zero (r : AzMvRationalFunction n ord) : displayDen r ≠ 0 := by
  intro h0
  have h1 : toMvPolyQ (displayDen r) = 0 := by rw [h0, toMvPolyQ_zero]
  rw [displayDen, toMvPolyQ_smul] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · have h3 : (((⟨true, r.factor.den, fun _ => rfl⟩ : AzInt).toInt : ℚ)) = 0 :=
      MvPolynomial.C_eq_zero.mp h2
    have h4 : ((r.factor.den.toNat : ℤ) : ℚ) = 0 := h3
    have h5 : r.factor.den.toNat = 0 := by exact_mod_cast h4
    exact r.factor.den_nz (Azurite.AzNat.toNat_injective (by rw [h5]; rfl))
  · exact toMvPolyQ_den_ne_zero r h2

/-- **Display correctness**: re-normalizing the displayed integer fraction
recovers the original rational function. -/
theorem ofNumDen_displayNum_displayDen (r : AzMvRationalFunction n ord) :
    ofNumDen (displayNum r) (displayDen r) = r := by
  apply toMvRatFunc_injective
  rw [toMvRatFunc_ofNumDen _ _ (displayDen_ne_zero r), displayNum, displayDen,
    toMvPolyQ_smul, toMvPolyQ_smul]
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
  rw [show toMvRatFunc r = algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ))
        (Azurite.AzRat.toRat r.factor)
      * (algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (toMvPolyQ r.num)
        / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (toMvPolyQ r.den)) from rfl,
    hfac, map_div₀, algebraMapQ_C, algebraMapQ_C, map_mul, map_mul,
    div_mul_div_comm]

/-! ### Character-class facts about the multivariate polynomial printer

The printer emits only coefficient digits/`-`, variable characters (from the
naming scheme `F`), and the syntax characters `+ - * ^`. Given that `F`'s
variable characters avoid `(` (40), `)` (41), `/` (47), none of those three
ever occur — the facts the string plumbing needs. -/

section CharClass

variable (F : Type _) [LinearOrder F] [ParsableVar F n]

private theorem bad_notin_coeff {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47) (z : AzInt) :
    b ∉ (ParsableCoeff.toChars z : List Char) := by
  intro hmem
  have h1 : (ParsableCoeff.toChars z : List Char) = AzInt.toChars z := rfl
  rw [h1] at hmem
  rcases Azurite.AzInt.mem_toChars_digit_or_dash z b hmem with h2 | ⟨h3, h4⟩
  · rw [h2] at hb; exact absurd hb (by decide)
  · have h5 : ('0' : Char).toNat = 48 := rfl
    have h6 : ('9' : Char).toNat = 57 := rfl
    omega

private theorem bad_notin_monic {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47)
    (hF : ∀ v : F, b ∉ (ParsableVar.toChars v : List Char))
    (m : MonicMonomial n ord) : b ∉ m.toCharsWith F := by
  apply Azurite.MonicMonomial.char_notin_toCharsWith
  · exact hF
  · intro k
    exact Azurite.AzPolynomial.not_mem_natToChars_of_not_digit b (Or.inl (by omega)) k
  · intro h; rw [h] at hb; exact absurd hb (by decide)
  · intro h; rw [h] at hb; exact absurd hb (by decide)

private theorem bad_notin_monomialChars {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47)
    (hF : ∀ v : F, b ∉ (ParsableVar.toChars v : List Char))
    (m : Monomial n AzInt ord) : b ∉ m.toCharsWith F := by
  intro hmem
  unfold Azurite.Monomial.toCharsWith at hmem
  split at hmem
  · exact bad_notin_coeff hb _ hmem
  · split at hmem
    · exact bad_notin_monic F hb hF _ hmem
    · split at hmem
      · split at hmem
        · rcases List.mem_cons.mp hmem with h2 | h2
          · rw [h2] at hb; exact absurd hb (by decide)
          · exact bad_notin_monic F hb hF _ h2
        · rcases List.mem_append.mp hmem with h2 | h2
          · rcases List.mem_append.mp h2 with h3 | h3
            · exact bad_notin_coeff hb _ h3
            · rw [List.mem_singleton.mp h3] at hb; exact absurd hb (by decide)
          · exact bad_notin_monic F hb hF _ h2
      · rcases List.mem_append.mp hmem with h2 | h2
        · rcases List.mem_append.mp h2 with h3 | h3
          · exact bad_notin_coeff hb _ h3
          · rw [List.mem_singleton.mp h3] at hb; exact absurd hb (by decide)
        · exact bad_notin_monic F hb hF _ h2

private theorem bad_notin_joinAux {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47) (ms : List (List Char))
    (h : ∀ m ∈ ms, b ∉ m) : b ∉ Azurite.joinMonomialsAux ms := by
  induction ms with
  | nil => intro hmem; exact absurd hmem (by simp [Azurite.joinMonomialsAux])
  | cons m ms ih =>
    intro hmem
    unfold Azurite.joinMonomialsAux at hmem
    simp only [List.append_assoc, List.mem_append] at hmem
    rcases hmem with h1 | h1 | h1
    · split at h1
      · exact absurd h1 (by simp)
      · rw [List.mem_singleton.mp h1] at hb; exact absurd hb (by decide)
    · exact h m List.mem_cons_self h1
    · exact ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) h1

private theorem bad_notin_join {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47) (ms : List (List Char))
    (h : ∀ m ∈ ms, b ∉ m) : b ∉ Azurite.joinMonomials ms := by
  cases ms with
  | nil => intro hmem; exact absurd hmem (by simp [Azurite.joinMonomials])
  | cons m ms =>
    intro hmem
    unfold Azurite.joinMonomials at hmem
    rcases List.mem_append.mp hmem with h1 | h1
    · exact h m List.mem_cons_self h1
    · exact bad_notin_joinAux hb ms (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) h1

/-- The multivariate polynomial printer never emits `(`, `)`, or `/`. -/
private theorem bad_notin_polyChars {b : Char}
    (hb : b.toNat = 40 ∨ b.toNat = 41 ∨ b.toNat = 47)
    (hF : ∀ v : F, b ∉ (ParsableVar.toChars v : List Char))
    (p : AzMvPolynomial n AzInt ord) : b ∉ AzMvPolynomial.toCharsWith F p := by
  unfold AzMvPolynomial.toCharsWith
  split
  · exact bad_notin_coeff hb 0
  · apply bad_notin_join hb
    intro mchars hmem
    obtain ⟨mono, _, rfl⟩ := List.mem_map.mp hmem
    exact bad_notin_monomialChars F hb hF mono

end CharClass

/-! ### `splitSlash` / `stripParens` on printer output -/

private theorem h40 : ('(' : Char).toNat = 40 ∨ ('(' : Char).toNat = 41
    ∨ ('(' : Char).toNat = 47 := by decide

private theorem h47 : ('/' : Char).toNat = 40 ∨ ('/' : Char).toNat = 41
    ∨ ('/' : Char).toNat = 47 := by decide

open private splitSlashAux from Azurite.AzMvRationalFunction.Parse

private theorem splitSlash_eq (cs : List Char) : splitSlash cs = splitSlashAux cs [] := rfl

private theorem myAux_slash (t : List Char) (acc : List Char) :
    splitSlashAux ('/' :: t) acc = some (acc.reverse, t) := rfl

private theorem myAux_cons_other {c : Char} (h3 : c ≠ '/') (t : List Char) (acc : List Char) :
    splitSlashAux (c :: t) acc = splitSlashAux t (c :: acc) := by
  conv_lhs => unfold splitSlashAux
  split
  · rename_i heq; exact absurd heq (by simp)
  · rename_i t' heq; injection heq with h1 h2; exact absurd h1 h3
  · rename_i c' t' hne heq; injection heq with h1 h2; rw [h1, h2]

private theorem myAux_run (cs : List Char) (hs : '/' ∉ cs) :
    ∀ (rest : List Char) (acc : List Char),
      splitSlashAux (cs ++ rest) acc = splitSlashAux rest (cs.reverse ++ acc) := by
  induction cs with
  | nil => intro rest acc; simp
  | cons c t ih =>
    intro rest acc
    have hc3 : c ≠ '/' := fun h => hs (h ▸ List.mem_cons_self)
    rw [List.cons_append, myAux_cons_other hc3,
      ih (fun h => hs (List.mem_cons_of_mem _ h)) rest (c :: acc)]
    simp

private theorem splitSlash_none (cs : List Char) (hs : '/' ∉ cs) : splitSlash cs = none := by
  rw [splitSlash_eq]
  have h1 := myAux_run cs hs [] []
  rw [List.append_nil] at h1
  rw [h1]; rfl

private theorem splitSlash_bare (cs : List Char) (hs : '/' ∉ cs) (rest : List Char) :
    splitSlash (cs ++ '/' :: rest) = some (cs, rest) := by
  rw [splitSlash_eq, myAux_run cs hs ('/' :: rest) [], myAux_slash]; simp

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

/-! ### The round-trip -/

section Roundtrip

variable (F : Type _) [LinearOrder F] [ParsableVar F n]

/-- Every `ParsableVar` naming scheme avoids `(` in its variable characters:
`(` is a reserved (`isPolySyntaxChar`) character. -/
private theorem var_no_open (v : F) : ('(' : Char) ∉ (ParsableVar.toChars v : List Char) :=
  fun h => ParsableVar.toChars_no_syntax v '(' h (by decide)

/-- Every `ParsableVar` naming scheme avoids `/` in its variable characters:
`/` is a reserved (`isPolySyntaxChar`) character. -/
private theorem var_no_slash (v : F) : ('/' : Char) ∉ (ParsableVar.toChars v : List Char) :=
  fun h => ParsableVar.toChars_no_syntax v '/' h (by decide)

/-- The two facts the parser needs about a wrapped numerator component: it
splits off cleanly before a `/`, and it strips back to the raw printer output. -/
private theorem wrap_facts
    (hFo : ∀ v : F, ('(' : Char) ∉ (ParsableVar.toChars v : List Char))
    (hFs : ∀ v : F, ('/' : Char) ∉ (ParsableVar.toChars v : List Char))
    (p : AzMvPolynomial n AzInt ord) :
    (∀ rest, splitSlash (wrapComponent F p ++ '/' :: rest) = some (wrapComponent F p, rest))
    ∧ stripParens (wrapComponent F p) = AzMvPolynomial.toCharsWith F p := by
  unfold wrapComponent
  split
  · exact ⟨fun rest => splitSlash_bare _ (bad_notin_polyChars F h47 hFs p) rest,
      stripParens_of_no_open _ (bad_notin_polyChars F h40 hFo p)⟩
  · have hs : '/' ∉ ('(' :: AzMvPolynomial.toCharsWith F p ++ [')']) := by
      intro hmem
      rcases List.mem_cons.mp hmem with h1 | h1
      · exact absurd h1 (by decide)
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact bad_notin_polyChars F h47 hFs p h2
        · exact absurd (List.mem_singleton.mp h2) (by decide)
    exact ⟨fun rest => splitSlash_bare _ hs rest, stripParens_paren _⟩

/-- The same two facts for the denominator wrapping rule. -/
private theorem wrapDen_facts
    (hFo : ∀ v : F, ('(' : Char) ∉ (ParsableVar.toChars v : List Char))
    (hFs : ∀ v : F, ('/' : Char) ∉ (ParsableVar.toChars v : List Char))
    (p : AzMvPolynomial n AzInt ord) :
    (∀ rest, splitSlash (wrapDenominator F p ++ '/' :: rest) = some (wrapDenominator F p, rest))
    ∧ stripParens (wrapDenominator F p) = AzMvPolynomial.toCharsWith F p := by
  unfold wrapDenominator
  split
  · exact ⟨fun rest => splitSlash_bare _ (bad_notin_polyChars F h47 hFs p) rest,
      stripParens_of_no_open _ (bad_notin_polyChars F h40 hFo p)⟩
  · have hs : '/' ∉ ('(' :: AzMvPolynomial.toCharsWith F p ++ [')']) := by
      intro hmem
      rcases List.mem_cons.mp hmem with h1 | h1
      · exact absurd h1 (by decide)
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact bad_notin_polyChars F h47 hFs p h2
        · exact absurd (List.mem_singleton.mp h2) (by decide)
    exact ⟨fun rest => splitSlash_bare _ hs rest, stripParens_paren _⟩

/-- **Round-trip**: parsing the char-list form of a canonical multivariate
rational function recovers it, for any `ParsableVar` naming scheme `F`. The
grammar reserves `(`, `)`, `/` (they are `isPolySyntaxChar`), so a naming
scheme's variable characters automatically avoid them — no side hypotheses. -/
theorem parseWith_toCharsWith
    (r : AzMvRationalFunction n ord) :
    parseWith F (toCharsWith F r) = some r := by
  have hFo : ∀ v : F, ('(' : Char) ∉ (ParsableVar.toChars v : List Char) := var_no_open F
  have hFs : ∀ v : F, ('/' : Char) ∉ (ParsableVar.toChars v : List Char) := var_no_slash F
  by_cases hd1 : displayDen r = 1
  · rw [toCharsWith, ite_eq_left (by rw [beq_iff_eq]; exact hd1), parseWith,
      splitSlash_none _ (bad_notin_polyChars F h47 hFs _),
      stripParens_of_no_open _ (bad_notin_polyChars F h40 hFo _),
      AzMvPolynomial.parseWith_toCharsWith, Option.map_some]
    have h1 : ofMvPolynomial (displayNum r) = r := by
      show ofNumDen (displayNum r) 1 = r
      rw [← hd1]; exact ofNumDen_displayNum_displayDen r
    rw [h1]
  · rw [toCharsWith, ite_eq_right (fun h => hd1 (beq_iff_eq.mp h)), parseWith,
      (wrap_facts F hFo hFs (displayNum r)).1 _]
    show (do
      let nm ← AzMvPolynomial.parseWith (R := AzInt) (ord := ord) F
        (stripParens (wrapComponent F (displayNum r)))
      let dm ← AzMvPolynomial.parseWith (R := AzInt) (ord := ord) F
        (stripParens (wrapDenominator F (displayDen r)))
      if dm = 0 then none else some (ofNumDen nm dm)) = some r
    rw [(wrap_facts F hFo hFs (displayNum r)).2, (wrapDen_facts F hFo hFs (displayDen r)).2,
      AzMvPolynomial.parseWith_toCharsWith, AzMvPolynomial.parseWith_toCharsWith]
    show (if displayDen r = 0 then none
      else some (ofNumDen (displayNum r) (displayDen r))) = some r
    rw [ite_eq_right (displayDen_ne_zero r), ofNumDen_displayNum_displayDen r]

/-- **String round-trip**: `parseStrWith F (toStrWith F r) = some r`, for any
`ParsableVar` naming scheme `F` — hypothesis-free. -/
theorem parseStrWith_toStrWith
    (r : AzMvRationalFunction n ord) :
    parseStrWith F (toStrWith F r) = some r := by
  rw [parseStrWith, toStrWith, String.toList_ofList]
  exact parseWith_toCharsWith F r

end Roundtrip

end Azurite.AzMvRationalFunction
