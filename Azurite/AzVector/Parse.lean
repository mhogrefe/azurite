/-
  `toChars` / `parseChars` for `AzVector`, round-trip proof, and `ToString`
  instance.

  Format: `"[e₀, e₁, …, e_{n-1}]"` — outer brackets, elements joined by
  `", "` (comma + space). For `n = 0`, the representation is `"[]"`.
-/
import Azurite.AzVector.ParsableElement
import Azurite.AzVector.Basic

namespace Azurite

namespace AzVector

variable {R : Type _} [ParsableElement R] {n : ℕ}

/-- Convert a vector to a list. Inverse of `AzVector.ofList`. -/
def toList (v : AzVector R n) : List R := v.data.toList

omit [ParsableElement R] in
@[simp] theorem toList_length (v : AzVector R n) : v.toList.length = n := by
  simp [toList]

/-- Serialize a vector as a character list: `"[e₀, e₁, …, e_{n-1}]"`. -/
def toChars (v : AzVector R n) : List Char :=
  '[' :: List.intercalate [',', ' '] (v.toList.map ParsableElement.toChars) ++ [']']

/-- Length-aware parser for a comma-space-separated element list (without
    brackets). Recurses structurally on the expected element count `n`. -/
def parseElementsN [ParsableElement R] :
    ℕ → List Char → Option (List R)
  | 0, [] => some []
  | 0, _ :: _ => none
  | 1, cs => (ParsableElement.parseChars cs).map ([·])
  | n + 2, cs =>
    match cs.dropWhile (· != ',') with
    | ',' :: ' ' :: rest =>
      (ParsableElement.parseChars (cs.takeWhile (· != ','))).bind
        (fun r => (parseElementsN (n + 1) rest).map (r :: ·))
    | _ => none

/-- Parse a character list as a vector of length `n`. -/
def parseChars (cs : List Char) : Option (AzVector R n) :=
  match cs with
  | '[' :: rest =>
    match rest.reverse with
    | ']' :: body_rev =>
      match parseElementsN n body_rev.reverse with
      | none => none
      | some elems =>
        if h : elems.length = n then some (AzVector.ofList elems h) else none
    | _ => none
  | _ => none

/-- Parse a string as a vector. -/
@[inline] def parseStr (s : String) : Option (AzVector R n) := parseChars s.toList

/-! ### Round-trip lemmas -/

lemma takeWhile_ne_sep_append (sep : Char) (xs ys : List Char) (h : sep ∉ xs) :
    (xs ++ ys).takeWhile (· != sep) = xs ++ ys.takeWhile (· != sep) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ sep := fun heq => h (heq ▸ List.mem_cons_self ..)
    have hne : (x != sep) = true := by simp [hx]
    simp [hne, ih (fun hc => h (List.mem_cons_of_mem _ hc))]

lemma dropWhile_ne_sep_append (sep : Char) (xs ys : List Char) (h : sep ∉ xs) :
    (xs ++ ys).dropWhile (· != sep) = ys.dropWhile (· != sep) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ sep := fun heq => h (heq ▸ List.mem_cons_self ..)
    have hne : (x != sep) = true := by simp [hx]
    simp [hne, ih (fun hc => h (List.mem_cons_of_mem _ hc))]

/-- `parseElementsN` correctly parses an intercalated list of element
    char-representations when the expected length matches. -/
lemma parseElementsN_intercalate :
    ∀ (xs : List R),
      parseElementsN xs.length
        (List.intercalate [',', ' '] (xs.map ParsableElement.toChars)) = some xs
  | [] => rfl
  | [r] => by
    simp only [List.length_singleton, List.map_cons, List.map_nil,
      List.intercalate_singleton]
    show parseElementsN 1 (ParsableElement.toChars r) = some [r]
    simp [parseElementsN, ParsableElement.parse_toChars]
  | r :: r' :: rs => by
    have hnc_r : ',' ∉ ParsableElement.toChars r := ParsableElement.toChars_no_comma r
    have hmap_ne : ((r' :: rs).map ParsableElement.toChars) ≠ [] := by simp
    show parseElementsN (rs.length + 2)
        (List.intercalate [',', ' '] ((r :: r' :: rs).map ParsableElement.toChars)) =
        some (r :: r' :: rs)
    rw [show ((r :: r' :: rs).map ParsableElement.toChars : List (List Char)) =
      ParsableElement.toChars r :: ((r' :: rs).map ParsableElement.toChars) from rfl,
      List.intercalate_cons_of_ne_nil hmap_ne]
    set tcr := ParsableElement.toChars r with htcr_def
    set body := List.intercalate [',', ' '] ((r' :: rs).map ParsableElement.toChars)
        with hbody_def
    have h_reassoc : tcr ++ [',', ' '] ++ body = tcr ++ ([',', ' '] ++ body) := by
      rw [List.append_assoc]
    have htake : (tcr ++ [',', ' '] ++ body).takeWhile (· != ',') = tcr := by
      rw [h_reassoc, takeWhile_ne_sep_append _ _ _ hnc_r]
      show tcr ++ (',' :: ' ' :: body).takeWhile (· != ',') = tcr
      simp [List.takeWhile]
    have hdrop : (tcr ++ [',', ' '] ++ body).dropWhile (· != ',') = ',' :: ' ' :: body := by
      rw [h_reassoc, dropWhile_ne_sep_append _ _ _ hnc_r]
      show (',' :: ' ' :: body).dropWhile (· != ',') = ',' :: ' ' :: body
      simp [List.dropWhile]
    have hparse : ParsableElement.parseChars tcr = some r := ParsableElement.parse_toChars r
    show (match (tcr ++ [',', ' '] ++ body).dropWhile (· != ',') with
          | ',' :: ' ' :: rest =>
            (ParsableElement.parseChars ((tcr ++ [',', ' '] ++ body).takeWhile (· != ','))).bind
              (fun r => (parseElementsN (rs.length + 1) rest).map (r :: ·))
          | _ => none) = some (r :: r' :: rs)
    rw [hdrop, htake, hparse]
    have hih : parseElementsN (rs.length + 1) body = some (r' :: rs) := by
      rw [hbody_def]
      exact parseElementsN_intercalate (r' :: rs)
    simp [hih]

/-- Round-trip: `parseChars` is a left inverse of `toChars`. -/
theorem parseChars_toChars (v : AzVector R n) : parseChars (toChars v) = some v := by
  unfold parseChars toChars
  set body := List.intercalate [',', ' '] (v.toList.map ParsableElement.toChars) with hbody
  -- '[' :: body ++ [']'] matches the '[' :: rest pattern with rest = body ++ [']']
  show (match '[' :: (body ++ [']']) with
    | '[' :: rest =>
      match rest.reverse with
      | ']' :: body_rev =>
        match parseElementsN n body_rev.reverse with
        | none => none
        | some elems =>
          if h : elems.length = n then some (AzVector.ofList elems h) else none
      | _ => none
    | _ => none) = some v
  -- Step through the matches
  show (match (body ++ [']']).reverse with
    | ']' :: body_rev =>
      match parseElementsN n body_rev.reverse with
      | none => none
      | some elems =>
        if h : elems.length = n then some (AzVector.ofList elems h) else none
    | _ => none) = some v
  rw [show (body ++ [']']).reverse = ']' :: body.reverse from by simp]
  show (match parseElementsN n body.reverse.reverse with
    | none => none
    | some elems =>
      if h : elems.length = n then some (AzVector.ofList elems h) else none) = some v
  rw [List.reverse_reverse]
  have hlen : v.toList.length = n := toList_length v
  have hpn : parseElementsN n body = some v.toList := by
    rw [hbody]
    have h := parseElementsN_intercalate v.toList
    rw [hlen] at h
    exact h
  rw [hpn]
  show (if h : v.toList.length = n then some (AzVector.ofList v.toList h) else none) = some v
  rw [dif_pos hlen]
  rfl

end AzVector

/-! ### ToString instance -/

instance {R : Type _} [ParsableElement R] {n : ℕ} : ToString (AzVector R n) where
  toString v := String.ofList (AzVector.toChars v)

end Azurite
