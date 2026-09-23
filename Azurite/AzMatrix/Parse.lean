/-
  `toChars` / `parseChars` for `AzMatrix`, round-trip proof, and `ToString`
  instance.

  Format: `"[r₀; r₁; …; r_{m-1}]"` where each row `rᵢ` is a comma-space-separated
  element list (no surrounding brackets on rows). For `m = 0 ∨ n = 0`, the
  representation is `"[]"`.
-/
import Azurite.AzVector.Parse
import Azurite.AzMatrix.Basic

namespace Azurite

namespace AzMatrix

open AzVector (parseElementsN parseElementsN_intercalate
  takeWhile_ne_sep_append dropWhile_ne_sep_append)

variable {R : Type _} [ParsableElement R] {m n : ℕ}

/-- The unique matrix when `m = 0`. -/
def emptyRows : AzMatrix R 0 n := AzMatrix.ofFn (fun i _ => i.elim0)

/-- The unique matrix when `n = 0`. -/
def emptyCols : AzMatrix R m 0 := AzMatrix.ofFn (fun _ j => j.elim0)

/-- Serialize a matrix as a character list:
    `"[r₀; r₁; …; r_{m-1}]"`, or `"[]"` when `m = 0 ∨ n = 0`. -/
def toChars (M : AzMatrix R m n) : List Char :=
  if m = 0 ∨ n = 0 then ['[', ']']
  else
    '[' :: List.intercalate [';', ' ']
      (M.toLists.map (fun row =>
        List.intercalate [',', ' '] (row.map ParsableElement.toChars))) ++ [']']

/-- Length-aware parser for a semicolon-space-separated row list (without
    surrounding brackets). Each row is parsed as a length-`n` element list. -/
def parseRowsN (n : ℕ) :
    ℕ → List Char → Option (List (List R))
  | 0, [] => some []
  | 0, _ :: _ => none
  | 1, cs => (parseElementsN n cs).map ([·])
  | m + 2, cs =>
    match cs.dropWhile (· != ';') with
    | ';' :: ' ' :: rest =>
      (parseElementsN n (cs.takeWhile (· != ';'))).bind
        (fun row => (parseRowsN n (m + 1) rest).map (row :: ·))
    | _ => none

/-- Parse a character list as a matrix of dimensions `m × n`. -/
def parseChars (cs : List Char) : Option (AzMatrix R m n) :=
  if hm : m = 0 then
    if cs = ['[', ']'] then some (hm ▸ emptyRows) else none
  else if hn : n = 0 then
    if cs = ['[', ']'] then some (hn ▸ emptyCols) else none
  else
    match cs with
    | '[' :: rest =>
      match rest.reverse with
      | ']' :: body_rev =>
        (parseRowsN n m body_rev.reverse).bind (fun rows =>
          if hrl : rows.length = m then
            if hcl : ∀ r ∈ rows, r.length = n then
              some (AzMatrix.ofLists rows hrl hcl)
            else none
          else none)
      | _ => none
    | _ => none

/-- Parse a string as a matrix. -/
@[inline] def parseStr (s : String) : Option (AzMatrix R m n) := parseChars s.toList

/-! ### Round-trip lemmas -/

/-- No `;` appears in the intercalated char-rep of a row of elements. -/
private lemma no_semi_in_intercalate_row : ∀ (row : List R),
    ';' ∉ List.intercalate [',', ' '] (row.map ParsableElement.toChars)
  | [] => List.not_mem_nil
  | [r] => by
    simp only [List.map_cons, List.map_nil, List.intercalate_singleton]
    exact ParsableElement.toChars_no_semicolon r
  | r :: r' :: rs => by
    rw [show ((r :: r' :: rs).map ParsableElement.toChars : List (List Char)) =
      ParsableElement.toChars r :: (r' :: rs).map ParsableElement.toChars from rfl,
      List.intercalate_cons_of_ne_nil (by simp)]
    intro hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · rw [List.mem_append] at hc
      rcases hc with hc | hc
      · exact ParsableElement.toChars_no_semicolon r hc
      · revert hc; decide
    · exact no_semi_in_intercalate_row (r' :: rs) hc

/-- `parseRowsN` correctly parses an intercalated list of row char-reps when
    the expected row count matches and every row has the expected length. -/
lemma parseRowsN_intercalate :
    ∀ (rows : List (List R)),
      (∀ row ∈ rows, row.length = n) →
      parseRowsN n rows.length
        (List.intercalate [';', ' '] (rows.map (fun row =>
          List.intercalate [',', ' '] (row.map ParsableElement.toChars)))) =
        some rows
  | [], _ => rfl
  | [row], hlen => by
    simp only [List.length_singleton, List.map_cons, List.map_nil,
      List.intercalate_singleton]
    show parseRowsN n 1
      (List.intercalate [',', ' '] (row.map ParsableElement.toChars)) = some [row]
    have hrow : row.length = n := hlen row (List.mem_singleton.mpr rfl)
    have h := parseElementsN_intercalate row
    rw [hrow] at h
    simp [parseRowsN, h]
  | row :: row' :: rs, hlen => by
    have hnc_row : ';' ∉ List.intercalate [',', ' '] (row.map ParsableElement.toChars) :=
      no_semi_in_intercalate_row row
    have hmap_ne :
        ((row' :: rs).map
          (fun r => List.intercalate [',', ' '] (r.map ParsableElement.toChars))) ≠ [] := by
      simp
    show parseRowsN n (rs.length + 2)
        (List.intercalate [';', ' '] ((row :: row' :: rs).map
          (fun r => List.intercalate [',', ' '] (r.map ParsableElement.toChars)))) =
        some (row :: row' :: rs)
    rw [show ((row :: row' :: rs).map
        (fun r => List.intercalate [',', ' '] (r.map ParsableElement.toChars)) :
        List (List Char)) =
      (List.intercalate [',', ' '] (row.map ParsableElement.toChars)) ::
        ((row' :: rs).map
          (fun r => List.intercalate [',', ' '] (r.map ParsableElement.toChars))) from rfl,
      List.intercalate_cons_of_ne_nil hmap_ne]
    set rowChars := List.intercalate [',', ' '] (row.map ParsableElement.toChars)
        with hrowChars_def
    set body := List.intercalate [';', ' '] ((row' :: rs).map
        (fun r => List.intercalate [',', ' '] (r.map ParsableElement.toChars)))
        with hbody_def
    have h_reassoc : rowChars ++ [';', ' '] ++ body = rowChars ++ ([';', ' '] ++ body) := by
      rw [List.append_assoc]
    have htake : (rowChars ++ [';', ' '] ++ body).takeWhile (· != ';') = rowChars := by
      rw [h_reassoc, takeWhile_ne_sep_append _ _ _ hnc_row]
      show rowChars ++ (';' :: ' ' :: body).takeWhile (· != ';') = rowChars
      simp [List.takeWhile]
    have hdrop : (rowChars ++ [';', ' '] ++ body).dropWhile (· != ';') = ';' :: ' ' :: body := by
      rw [h_reassoc, dropWhile_ne_sep_append _ _ _ hnc_row]
      show (';' :: ' ' :: body).dropWhile (· != ';') = ';' :: ' ' :: body
      simp [List.dropWhile]
    have hrow : row.length = n := hlen row (by simp)
    have hparse : parseElementsN n rowChars = some row := by
      rw [hrowChars_def]
      have h := parseElementsN_intercalate row
      rw [hrow] at h
      exact h
    show (match (rowChars ++ [';', ' '] ++ body).dropWhile (· != ';') with
          | ';' :: ' ' :: rest =>
            (parseElementsN n ((rowChars ++ [';', ' '] ++ body).takeWhile (· != ';'))).bind
              (fun row => (parseRowsN n (rs.length + 1) rest).map (row :: ·))
          | _ => none) = some (row :: row' :: rs)
    rw [hdrop, htake, hparse]
    have hih : parseRowsN n (rs.length + 1) body = some (row' :: rs) := by
      rw [hbody_def]
      exact parseRowsN_intercalate (row' :: rs)
        (fun r hr => hlen r (by simp [hr]))
    simp [hih]

/-! ### Round-trip theorem -/

omit [ParsableElement R] in
/-- Lemma: when `m = 0`, every `AzMatrix R m n` equals `emptyRows`. -/
private lemma eq_emptyRows (hm : m = 0) (M : AzMatrix R m n) :
    M = hm ▸ (emptyRows : AzMatrix R 0 n) := by
  subst hm
  ext i j
  exact i.elim0

omit [ParsableElement R] in
/-- Lemma: when `n = 0`, every `AzMatrix R m n` equals `emptyCols`. -/
private lemma eq_emptyCols (hn : n = 0) (M : AzMatrix R m n) :
    M = hn ▸ (emptyCols : AzMatrix R m 0) := by
  subst hn
  ext i j
  exact j.elim0

/-- Lemma: when `m = 0 ∨ n = 0`, `toLists M = []` or has empty rows so that
    the intercalated string is `[]`. -/
private lemma toChars_of_degenerate (M : AzMatrix R m n) (h : m = 0 ∨ n = 0) :
    toChars M = ['[', ']'] := by
  unfold toChars
  rw [ite_eq_left h]

/-- Round-trip: `parseChars` is a left inverse of `toChars`. -/
theorem parseChars_toChars (M : AzMatrix R m n) : parseChars (toChars M) = some M := by
  by_cases hm : m = 0
  · rw [toChars_of_degenerate M (Or.inl hm)]
    unfold parseChars
    rw [dite_eq_left hm, ite_eq_left rfl]
    congr 1
    exact (eq_emptyRows hm M).symm
  · by_cases hn : n = 0
    · rw [toChars_of_degenerate M (Or.inr hn)]
      unfold parseChars
      rw [dite_eq_right hm, dite_eq_left hn, ite_eq_left rfl]
      congr 1
      exact (eq_emptyCols hn M).symm
    · -- Non-degenerate case: m > 0, n > 0
      unfold parseChars toChars
      rw [ite_eq_right (by tauto : ¬(m = 0 ∨ n = 0))]
      set body := List.intercalate [';', ' '] (M.toLists.map (fun row =>
          List.intercalate [',', ' '] (row.map ParsableElement.toChars))) with hbody
      show (if hm' : m = 0 then _
            else if hn' : n = 0 then _
            else match '[' :: (body ++ [']']) with
              | '[' :: rest =>
                match rest.reverse with
                | ']' :: body_rev =>
                  (parseRowsN n m body_rev.reverse).bind (fun rows =>
                    if hrl : rows.length = m then
                      if hcl : ∀ r ∈ rows, r.length = n then
                        some (AzMatrix.ofLists rows hrl hcl)
                      else none
                    else none)
                | _ => none
              | _ => none) = some M
      rw [dite_eq_right hm, dite_eq_right hn]
      show (match (body ++ [']']).reverse with
        | ']' :: body_rev =>
          (parseRowsN n m body_rev.reverse).bind (fun rows =>
            if hrl : rows.length = m then
              if hcl : ∀ r ∈ rows, r.length = n then
                some (AzMatrix.ofLists rows hrl hcl)
              else none
            else none)
        | _ => none) = some M
      rw [show (body ++ [']']).reverse = ']' :: body.reverse from by simp]
      show ((parseRowsN n m body.reverse.reverse).bind (fun rows =>
            if hrl : rows.length = m then
              if hcl : ∀ r ∈ rows, r.length = n then
                some (AzMatrix.ofLists rows hrl hcl)
              else none
            else none)) = some M
      rw [List.reverse_reverse]
      have hlen : M.toLists.length = m := M.toLists_length
      have hrowlen : ∀ row ∈ M.toLists, row.length = n :=
        fun _ h => AzMatrix.mem_toLists_length h
      have hpr : parseRowsN n m body = some M.toLists := by
        rw [hbody]
        have h := parseRowsN_intercalate M.toLists hrowlen
        rw [hlen] at h
        exact h
      rw [hpr]
      show (if hrl : M.toLists.length = m then
              if hcl : ∀ r ∈ M.toLists, r.length = n then
                some (AzMatrix.ofLists M.toLists hrl hcl)
              else none
            else none) = some M
      rw [dite_eq_left hlen, dite_eq_left hrowlen]
      congr 1
      exact AzMatrix.ofLists_toLists M

end AzMatrix

/-! ### ToString instance -/

instance {R : Type _} [ParsableElement R] {m n : ℕ} : ToString (AzMatrix R m n) where
  toString M := String.ofList (AzMatrix.toChars M)

end Azurite
