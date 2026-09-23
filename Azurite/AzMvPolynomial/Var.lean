/-
  Variable types for multivariate polynomials.
-/
import Mathlib.Order.Fin.Basic
import Azurite.AzPolynomial.StringLemmas

namespace Azurite

open AzPolynomial in
private theorem charOfNat_toNat_small (n : ℕ) (h : n < 55296) :
    (Char.ofNat n).toNat = n := by
  have : n.isValidChar = true := by simp [Nat.isValidChar]; omega
  simp only [Char.ofNat, this, ↓reduceDIte]
  simp [Char.ofNatAux, Char.toNat, UInt32.toNat]

/-- A typeclass for multivariate polynomial variable types with `n` variables.
    Requires a linear ordering and a bijection to `Fin n`. -/
class Var (α : Type _) (n : outParam ℕ) [LinearOrder α] where
  /-- Convert a variable to its index in `Fin n`. -/
  toFin : α → Fin n
  /-- Convert an index in `Fin n` to a variable. -/
  ofFin : Fin n → α
  /-- `ofFin` is a left inverse of `toFin`. -/
  ofFin_toFin : ∀ v : α, ofFin (toFin v) = v
  /-- `toFin` is a left inverse of `ofFin`. -/
  toFin_ofFin : ∀ i : Fin n, toFin (ofFin i) = i

namespace Var

variable {α : Type _} {n : ℕ} [LinearOrder α] [inst : Var α n]

theorem toFin_injective : Function.Injective (inst.toFin) := by
  intro a b h
  have := congr_arg inst.ofFin h
  simp [inst.ofFin_toFin] at this
  exact this

theorem ofFin_injective : Function.Injective (inst.ofFin) := by
  intro a b h
  have := congr_arg inst.toFin h
  simp [inst.toFin_ofFin] at this
  exact this

/-- The bijection between a variable type and `Fin n`. -/
def equiv : α ≃ Fin n where
  toFun := inst.toFin
  invFun := inst.ofFin
  left_inv := inst.ofFin_toFin
  right_inv := inst.toFin_ofFin

section Embed

variable {β : Type _} {m : ℕ} [LinearOrder β] [inst₂ : Var β m]

/-- Embed variables from a smaller set into a larger one via `Fin.castLE`.
    Works generically for any two `Var` instances. -/
def embed (h : n ≤ m) (v : α) : β :=
  inst₂.ofFin (Fin.castLE h (inst.toFin v))

/-- The Fin-level map induced by `embed` is `Fin.castLE`, which is strictly monotone.
    This is the key fact needed by `AzMvPolynomial.renameMonotone`. -/
theorem embed_fin_strictMono (h : n ≤ m) :
    StrictMono (fun i : Fin n => inst₂.toFin (Var.embed h (inst.ofFin i) : β)) := by
  intro a b hab
  simp only [embed, inst₂.toFin_ofFin, inst.toFin_ofFin, Fin.castLE_lt_castLE_iff]
  exact hab

/-- `Var.embed` is injective. -/
theorem embed_injective (h : n ≤ m) : Function.Injective (Var.embed h : α → β) := by
  intro v₁ v₂ hv
  have h1 := congr_arg inst₂.toFin hv
  simp only [embed, inst₂.toFin_ofFin, Fin.castLE_inj] at h1
  exact inst.toFin_injective h1

end Embed

end Var


/-- A character reserved by the serialization grammar, which a variable name may
    not contain: ASCII digits, `+`, `-`, `*`, `^`, and the rational-function
    structure characters `(`, `)`, `/`. (Coefficient heads — digits and `-` — are
    still in this set; the `/` inside a rational coefficient like `1/2` is
    consumed by `ParsableCoeff.parseChars`, not routed on here. The name is
    retained for historical continuity.) -/
def isPolySyntaxChar (c : Char) : Prop :=
  (c.toNat ≥ '0'.toNat ∧ c.toNat ≤ '9'.toNat) ∨ c = '+' ∨ c = '-' ∨ c = '*' ∨ c = '^'
    ∨ c = '(' ∨ c = ')' ∨ c = '/'

instance : DecidablePred isPolySyntaxChar := fun c => by
  unfold isPolySyntaxChar; infer_instance

/-- Extension of `Var` for variable types that can be serialized/deserialized
    as character sequences that do not collide with polynomial syntax. -/
class ParsableVar (α : Type _) (n : outParam ℕ) [LinearOrder α] extends Var α n where
  toChars : α → List Char
  parseChars : List Char → Option α
  parse_toChars : ∀ v : α, parseChars (toChars v) = some v
  toChars_nonempty : ∀ v : α, toChars v ≠ []
  toChars_no_syntax : ∀ v : α, ∀ c ∈ toChars v, ¬ isPolySyntaxChar c

/-- Convert a natural number to a list of Unicode subscript digit characters (₀₁₂...). -/
def natToSubscriptChars (n : ℕ) : List Char :=
  (natToChars n).map (fun c => Char.ofNat (c.toNat - '0'.toNat + '₀'.toNat))

/-- Parse a list of Unicode subscript digit characters (₀..₉) to a natural number.
    Rejects any character outside the Unicode subscript-digit range — without this
    guard, `Nat`-truncated subtraction silently maps every ASCII character to `'0'`
    (so e.g. `"_5"` would parse as `0` instead of failing). -/
def parseSubscriptChars (cs : List Char) : Option ℕ :=
  if cs.all (fun c => decide (c.toNat ≥ '₀'.toNat ∧ c.toNat ≤ '₉'.toNat)) then
    parseNatChars (cs.map (fun c => Char.ofNat (c.toNat - '₀'.toNat + '0'.toNat)))
  else
    none

private theorem subscript_unsubscript_digit (c : Char)
    (hge : 48 ≤ c.toNat) (hle : c.toNat ≤ 57) :
    Char.ofNat ((Char.ofNat (c.toNat - 48 + 8320)).toNat - 8320 + 48) = c := by
  rw [charOfNat_toNat_small (c.toNat - 48 + 8320) (by omega)]
  have : c.toNat - 48 + 8320 - 8320 + 48 = c.toNat := by omega
  rw [this]; exact Char.ofNat_toNat c

private theorem subscript_map_cancel (l : List Char)
    (h : ∀ c ∈ l, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    l.map (fun c => Char.ofNat ((Char.ofNat (c.toNat - 48 + 8320)).toNat - 8320 + 48)) = l := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨subscript_unsubscript_digit hd (h hd (.head _)).1 (h hd (.head _)).2,
           ih (fun c hc => h c (.tail _ hc))⟩

open AzPolynomial in
theorem mem_natToSubscriptChars_range (n : ℕ) (c : Char) (h : c ∈ natToSubscriptChars n) :
    c.toNat ≥ 8320 ∧ c.toNat ≤ 8329 := by
  simp only [natToSubscriptChars, List.mem_map] at h
  obtain ⟨d, hd, rfl⟩ := h
  have ⟨hge, hle⟩ := mem_natToChars_only_digits n d hd
  simp only [show ('0' : Char).toNat = 48 from by decide,
             show ('9' : Char).toNat = 57 from by decide,
             show ('₀' : Char).toNat = 8320 from by decide] at hge hle ⊢
  constructor <;> (rw [charOfNat_toNat_small (d.toNat - 48 + 8320) (by omega)]; omega)

open AzPolynomial in
theorem parseSubscriptChars_natToSubscriptChars (n : ℕ) :
    parseSubscriptChars (natToSubscriptChars n) = some n := by
  unfold parseSubscriptChars
  have hall : (natToSubscriptChars n).all
      (fun c => decide (c.toNat ≥ '₀'.toNat ∧ c.toNat ≤ '₉'.toNat)) = true := by
    rw [List.all_eq_true]
    intro c hc
    have ⟨h1, h2⟩ := mem_natToSubscriptChars_range n c hc
    simp only [decide_eq_true_eq,
      show ('₀' : Char).toNat = 8320 from by decide,
      show ('₉' : Char).toNat = 8329 from by decide]
    exact ⟨h1, h2⟩
  rw [ite_eq_left hall]
  unfold natToSubscriptChars
  simp only [List.map_map, Function.comp_def,
    show ('0' : Char).toNat = 48 from by decide,
    show ('₀' : Char).toNat = 8320 from by decide]
  rw [subscript_map_cancel _ (fun c hc => by
    have := mem_natToChars_only_digits n c hc
    constructor <;> [exact (by decide : ('0' : Char).toNat = 48) ▸ this.1;
                     exact (by decide : ('9' : Char).toNat = 57) ▸ this.2])]
  exact parseNatChars_natToChars n

/-- Convert a natural number to a string of Unicode subscript digits. -/
private def natToSubscript (n : ℕ) : String := String.ofList (natToSubscriptChars n)

private theorem lowercase_not_syntax (c : Char) (hge : c.toNat ≥ 97) (hle : c.toNat ≤ 122) :
    ¬ isPolySyntaxChar c := by
  simp only [isPolySyntaxChar, not_or, not_and,
    show ('0' : Char).toNat = 48 from by decide,
    show ('9' : Char).toNat = 57 from by decide]
  refine ⟨fun _ => by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; simp [h] at hge)

private theorem subscript_not_syntax (c : Char) (hge : c.toNat ≥ 8320) (hle : c.toNat ≤ 8329) :
    ¬ isPolySyntaxChar c := by
  simp only [isPolySyntaxChar, not_or, not_and,
    show ('0' : Char).toNat = 48 from by decide,
    show ('9' : Char).toNat = 57 from by decide]
  refine ⟨fun _ => by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; simp [h] at hge)

/-- A variable indexed by `Fin n`, displayed as `x₀`, `x₁`, etc. -/
@[ext]
structure IndexedVar (n : ℕ) where
  val : Fin n

namespace IndexedVar

/-- Shorthand constructor: `X 5` creates an `IndexedVar` with index 5. -/
abbrev X {n : ℕ} (i : Fin n) : IndexedVar n := ⟨i⟩

instance {n : ℕ} : LinearOrder (IndexedVar n) :=
  LinearOrder.lift' (fun v => v.val) (fun _ _ h => IndexedVar.ext h)

instance {n : ℕ} : Ord (IndexedVar n) where
  compare a b := compare a.val b.val

instance {n : ℕ} : ToString (IndexedVar n) where
  toString v := s!"x{natToSubscript v.val}"

instance {n : ℕ} : Repr (IndexedVar n) where
  reprPrec v _ := s!"X{natToSubscript v.val}"

def toChars {n : ℕ} (v : IndexedVar n) : List Char :=
  ['x'] ++ natToSubscriptChars v.val

def parse {n : ℕ} (cs : List Char) : Option (IndexedVar n) :=
  match cs with
  | 'x' :: rest => do
    let k ← parseSubscriptChars rest
    if h : k < n then some ⟨⟨k, h⟩⟩ else none
  | _ => none

theorem parse_toChars {n : ℕ} (v : IndexedVar n) :
    IndexedVar.parse (IndexedVar.toChars v) = some v := by
  simp only [toChars, parse, List.cons_append, List.nil_append]
  rw [parseSubscriptChars_natToSubscriptChars]
  simp [v.val.isLt]

instance {n : ℕ} : Var (IndexedVar n) n where
  toFin v := v.val
  ofFin i := ⟨i⟩
  ofFin_toFin _ := rfl
  toFin_ofFin _ := rfl

/-- Trivial `Var` instance for `Fin n` itself. -/
instance {n : ℕ} : Var (Fin n) n where
  toFin i := i
  ofFin i := i
  ofFin_toFin _ := rfl
  toFin_ofFin _ := rfl

instance {n : ℕ} : ParsableVar (IndexedVar n) n where
  toChars v := ['x'] ++ natToSubscriptChars v.val
  parseChars cs := match cs with
    | 'x' :: rest => do
      let k ← parseSubscriptChars rest
      if h : k < n then some ⟨⟨k, h⟩⟩ else none
    | _ => none
  parse_toChars v := by
    simp only [List.cons_append, List.nil_append]
    rw [parseSubscriptChars_natToSubscriptChars]
    simp [v.val.isLt]
  toChars_nonempty _ := by simp
  toChars_no_syntax v c hc := by
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact lowercase_not_syntax 'x' (by decide) (by decide)
    · have ⟨hge, hle⟩ := mem_natToSubscriptChars_range v.val c hc
      exact subscript_not_syntax c hge hle

end IndexedVar

private theorem uppercase_not_syntax (c : Char) (hge : c.toNat ≥ 65) (hle : c.toNat ≤ 90) :
    ¬ isPolySyntaxChar c := by
  simp only [isPolySyntaxChar, not_or, not_and,
    show ('0' : Char).toNat = 48 from by decide,
    show ('9' : Char).toNat = 57 from by decide]
  refine ⟨fun _ => by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; simp [h] at hge hle)

/-- A variable indexed by `Fin n`, displayed as `X₀`, `X₁`, etc. (capital X). -/
@[ext]
structure IndexedCapsVar (n : ℕ) where
  val : Fin n
  deriving DecidableEq

namespace IndexedCapsVar

/-- Shorthand constructor: `X 5` creates an `IndexedCapsVar` with index 5. -/
abbrev X {n : ℕ} (i : Fin n) : IndexedCapsVar n := ⟨i⟩

instance {n : ℕ} : LinearOrder (IndexedCapsVar n) :=
  LinearOrder.lift' (fun v => v.val) (fun _ _ h => IndexedCapsVar.ext h)

instance {n : ℕ} : Ord (IndexedCapsVar n) where
  compare a b := compare a.val b.val

instance {n : ℕ} : ToString (IndexedCapsVar n) where
  toString v := s!"X{natToSubscript v.val}"

instance {n : ℕ} : Repr (IndexedCapsVar n) where
  reprPrec v _ := s!"X{natToSubscript v.val}"

def toChars {n : ℕ} (v : IndexedCapsVar n) : List Char :=
  ['X'] ++ natToSubscriptChars v.val

def parse {n : ℕ} (cs : List Char) : Option (IndexedCapsVar n) :=
  match cs with
  | 'X' :: rest => do
    let k ← parseSubscriptChars rest
    if h : k < n then some ⟨⟨k, h⟩⟩ else none
  | _ => none

theorem parse_toChars {n : ℕ} (v : IndexedCapsVar n) :
    IndexedCapsVar.parse (IndexedCapsVar.toChars v) = some v := by
  simp only [toChars, parse, List.cons_append, List.nil_append]
  rw [parseSubscriptChars_natToSubscriptChars]
  simp [v.val.isLt]

instance {n : ℕ} : Var (IndexedCapsVar n) n where
  toFin v := v.val
  ofFin i := ⟨i⟩
  ofFin_toFin _ := rfl
  toFin_ofFin _ := rfl

instance {n : ℕ} : ParsableVar (IndexedCapsVar n) n where
  toChars v := ['X'] ++ natToSubscriptChars v.val
  parseChars cs := match cs with
    | 'X' :: rest => do
      let k ← parseSubscriptChars rest
      if h : k < n then some ⟨⟨k, h⟩⟩ else none
    | _ => none
  parse_toChars v := by
    simp only [List.cons_append, List.nil_append]
    rw [parseSubscriptChars_natToSubscriptChars]
    simp [v.val.isLt]
  toChars_nonempty _ := by simp
  toChars_no_syntax v c hc := by
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact uppercase_not_syntax 'X' (by decide) (by decide)
    · have ⟨hge, hle⟩ := mem_natToSubscriptChars_range v.val c hc
      exact subscript_not_syntax c hge hle

end IndexedCapsVar

/-- A variable named by a lowercase letter: `'a'`, `'b'`, `'c'`, ..., `'z'`.
    `n` is the number of variables in scope (at most 26).
    Stores the raw character, so construction is natural: `⟨'a', by omega⟩`. -/
structure AbcVar (n : ℕ) where
  ch : Char
  is_valid : ch.toNat ≥ 'a'.toNat ∧ ch.toNat ≤ 'z'.toNat ∧ ch.toNat - 'a'.toNat < n
  deriving DecidableEq

namespace AbcVar

/-- The zero-based index of this variable (0 for 'a', 1 for 'b', etc.). -/
def index {n : ℕ} (v : AbcVar n) : Fin n :=
  ⟨v.ch.toNat - 'a'.toNat, v.is_valid.2.2⟩

private theorem index_injective {n : ℕ} : Function.Injective (index : AbcVar n → Fin n) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [index, Fin.mk.injEq] at h
  congr 1; rw [← Char.ofNat_toNat a, ← Char.ofNat_toNat b]; congr 1; omega

instance {n : ℕ} : LinearOrder (AbcVar n) :=
  LinearOrder.lift' index index_injective

instance {n : ℕ} : Ord (AbcVar n) where
  compare a b := compare a.index b.index

instance {n : ℕ} : ToString (AbcVar n) where
  toString v := String.ofList [v.ch]

instance {n : ℕ} : Repr (AbcVar n) where
  reprPrec v _ := s!"'{v.ch}'"

def toChars {n : ℕ} (v : AbcVar n) : List Char := [v.ch]

def parse {n : ℕ} (c : Char) : Option (AbcVar n) :=
  if h : c.toNat ≥ 'a'.toNat ∧ c.toNat ≤ 'z'.toNat ∧ c.toNat - 'a'.toNat < n then
    some ⟨c, h⟩
  else none

theorem parse_toChars {n : ℕ} (v : AbcVar n) :
    AbcVar.parse v.ch = some v := by
  simp only [parse, dite_eq_left v.is_valid]

/-- Construct an `AbcVar` from a `Fin n` index (0 → 'a', 1 → 'b', etc.). -/
def ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) : AbcVar n :=
  ⟨Char.ofNat ('a'.toNat + i.val), by
    simp only [show ('a' : Char).toNat = 97 from by decide,
               show ('z' : Char).toNat = 122 from by decide]
    rw [charOfNat_toNat_small (97 + i.val) (by omega)]
    omega⟩

theorem ofIndex_index {n : ℕ} (hn : n ≤ 26) (v : AbcVar n) :
    AbcVar.ofIndex hn (AbcVar.index v) = v := by
  simp only [ofIndex, index]
  congr 1
  have hge := v.is_valid.1
  simp only [show ('a' : Char).toNat = 97 from by decide] at hge ⊢
  rw [show 97 + (v.ch.toNat - 97) = v.ch.toNat from by omega]
  exact Char.ofNat_toNat v.ch

theorem index_ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) :
    AbcVar.index (AbcVar.ofIndex hn i) = i := by
  simp only [index, ofIndex]
  ext
  simp only [show ('a' : Char).toNat = 97 from by decide]
  rw [charOfNat_toNat_small (97 + i.val) (by omega)]
  omega

instance {n : ℕ} [Fact (n ≤ 26)] : Var (AbcVar n) n where
  toFin := index
  ofFin := ofIndex (Fact.out)
  ofFin_toFin := ofIndex_index (Fact.out)
  toFin_ofFin := index_ofIndex (Fact.out)

instance {n : ℕ} [Fact (n ≤ 26)] : ParsableVar (AbcVar n) n where
  toChars v := [v.ch]
  parseChars cs := match cs with
    | [c] => if h : c.toNat ≥ 'a'.toNat ∧ c.toNat ≤ 'z'.toNat ∧ c.toNat - 'a'.toNat < n then
        some ⟨c, h⟩
      else none
    | _ => none
  parse_toChars v := by simp only [dite_eq_left v.is_valid]
  toChars_nonempty _ := by simp
  toChars_no_syntax v c hc := by
    simp at hc; subst hc
    have hge := v.is_valid.1; have hle := v.is_valid.2.1
    simp only [show ('a' : Char).toNat = 97 from by decide,
               show ('z' : Char).toNat = 122 from by decide] at hge hle
    exact lowercase_not_syntax v.ch hge hle


end AbcVar

/-- A variable named by an uppercase letter: `'A'`, `'B'`, `'C'`, ..., `'Z'`.
    `n` is the number of variables in scope (at most 26).
    Stores the raw character, so construction is natural: `⟨'A', by omega⟩`. -/
structure AbcCapsVar (n : ℕ) where
  ch : Char
  is_valid : ch.toNat ≥ 'A'.toNat ∧ ch.toNat ≤ 'Z'.toNat ∧ ch.toNat - 'A'.toNat < n
  deriving DecidableEq

namespace AbcCapsVar

/-- The zero-based index of this variable (0 for 'A', 1 for 'B', etc.). -/
def index {n : ℕ} (v : AbcCapsVar n) : Fin n :=
  ⟨v.ch.toNat - 'A'.toNat, v.is_valid.2.2⟩

private theorem index_injective {n : ℕ} : Function.Injective (index : AbcCapsVar n → Fin n) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [index, Fin.mk.injEq] at h
  congr 1; rw [← Char.ofNat_toNat a, ← Char.ofNat_toNat b]; congr 1; omega

instance {n : ℕ} : LinearOrder (AbcCapsVar n) :=
  LinearOrder.lift' index index_injective

instance {n : ℕ} : Ord (AbcCapsVar n) where
  compare a b := compare a.index b.index

instance {n : ℕ} : ToString (AbcCapsVar n) where
  toString v := String.ofList [v.ch]

instance {n : ℕ} : Repr (AbcCapsVar n) where
  reprPrec v _ := s!"'{v.ch}'"

def toChars {n : ℕ} (v : AbcCapsVar n) : List Char := [v.ch]

def parse {n : ℕ} (c : Char) : Option (AbcCapsVar n) :=
  if h : c.toNat ≥ 'A'.toNat ∧ c.toNat ≤ 'Z'.toNat ∧ c.toNat - 'A'.toNat < n then
    some ⟨c, h⟩
  else none

theorem parse_toChars {n : ℕ} (v : AbcCapsVar n) :
    AbcCapsVar.parse v.ch = some v := by
  simp only [parse, dite_eq_left v.is_valid]

/-- Construct an `AbcCapsVar` from a `Fin n` index (0 → 'A', 1 → 'B', etc.). -/
def ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) : AbcCapsVar n :=
  ⟨Char.ofNat ('A'.toNat + i.val), by
    simp only [show ('A' : Char).toNat = 65 from by decide,
               show ('Z' : Char).toNat = 90 from by decide]
    rw [charOfNat_toNat_small (65 + i.val) (by omega)]
    omega⟩

theorem ofIndex_index {n : ℕ} (hn : n ≤ 26) (v : AbcCapsVar n) :
    AbcCapsVar.ofIndex hn (AbcCapsVar.index v) = v := by
  simp only [ofIndex, index]
  congr 1
  have hge := v.is_valid.1
  simp only [show ('A' : Char).toNat = 65 from by decide] at hge ⊢
  rw [show 65 + (v.ch.toNat - 65) = v.ch.toNat from by omega]
  exact Char.ofNat_toNat v.ch

theorem index_ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) :
    AbcCapsVar.index (AbcCapsVar.ofIndex hn i) = i := by
  simp only [index, ofIndex]
  ext
  simp only [show ('A' : Char).toNat = 65 from by decide]
  rw [charOfNat_toNat_small (65 + i.val) (by omega)]
  omega

instance {n : ℕ} [Fact (n ≤ 26)] : Var (AbcCapsVar n) n where
  toFin := index
  ofFin := ofIndex (Fact.out)
  ofFin_toFin := ofIndex_index (Fact.out)
  toFin_ofFin := index_ofIndex (Fact.out)

instance {n : ℕ} [Fact (n ≤ 26)] : ParsableVar (AbcCapsVar n) n where
  toChars v := [v.ch]
  parseChars cs := match cs with
    | [c] => if h : c.toNat ≥ 'A'.toNat ∧ c.toNat ≤ 'Z'.toNat ∧ c.toNat - 'A'.toNat < n then
        some ⟨c, h⟩
      else none
    | _ => none
  parse_toChars v := by simp only [dite_eq_left v.is_valid]
  toChars_nonempty _ := by simp
  toChars_no_syntax v c hc := by
    simp at hc; subst hc
    have hge := v.is_valid.1; have hle := v.is_valid.2.1
    simp only [show ('A' : Char).toNat = 65 from by decide,
               show ('Z' : Char).toNat = 90 from by decide] at hge hle
    exact uppercase_not_syntax v.ch hge hle

end AbcCapsVar

/-- Maps an abc-index (0 = 'a', ..., 25 = 'z') to an xyz-rank:
    x(0), y(1), z(2), w(3), v(4), ..., a(25).
    This generalizes the convention where the 4th spatial axis is 'w'. -/
private def xyzRank (abcIdx : ℕ) : ℕ :=
  if abcIdx ≥ 23 then abcIdx - 23 else 25 - abcIdx

/-- Inverse of `xyzRank`: maps an xyz-rank back to an abc-index. -/
private def xyzUnrank (rank : ℕ) : ℕ :=
  if rank < 3 then rank + 23 else 25 - rank

private theorem xyzRank_xyzUnrank (r : ℕ) (h : r < 26) :
    xyzRank (xyzUnrank r) = r := by
  simp [xyzRank, xyzUnrank]; split <;> split <;> omega

private theorem xyzUnrank_xyzRank (i : ℕ) (h : i ≤ 25) :
    xyzUnrank (xyzRank i) = i := by
  simp [xyzRank, xyzUnrank]; split <;> split <;> omega

/-- A variable with ordering x, y, z, w, v, u, ..., a.
    Stores the raw character with a validity proof.
    Construction: `⟨'x', by omega⟩`, `⟨'y', by omega⟩`, etc. -/
structure XyzVar (n : ℕ) where
  ch : Char
  is_valid : ch.toNat ≥ 'a'.toNat ∧ ch.toNat ≤ 'z'.toNat ∧
    xyzRank (ch.toNat - 'a'.toNat) < n
  deriving DecidableEq

namespace XyzVar

/-- The zero-based xyz-rank of this variable (0 for 'x', 1 for 'y', 2 for 'z', 3 for 'w', ...). -/
def index {n : ℕ} (v : XyzVar n) : Fin n :=
  ⟨xyzRank (v.ch.toNat - 'a'.toNat), v.is_valid.2.2⟩

theorem xyzRank_injective :
    ∀ a b : ℕ, a ≤ 25 → b ≤ 25 → xyzRank a = xyzRank b → a = b := by
  intro a b ha hb h; simp [xyzRank] at h; split at h <;> split at h <;> omega

private theorem index_injective {n : ℕ} : Function.Injective (index : XyzVar n → Fin n) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [index, Fin.mk.injEq] at h
  simp only [show 'a'.toNat = 97 from by decide,
             show 'z'.toNat = 122 from by decide] at ha hb h ⊢
  have hab := xyzRank_injective _ _ (by omega) (by omega) h
  congr 1; rw [← Char.ofNat_toNat a, ← Char.ofNat_toNat b]; congr 1; omega

instance {n : ℕ} : LinearOrder (XyzVar n) :=
  LinearOrder.lift' index index_injective

instance {n : ℕ} : Ord (XyzVar n) where
  compare a b := compare a.index b.index

instance {n : ℕ} : ToString (XyzVar n) where
  toString v := String.ofList [v.ch]

instance {n : ℕ} : Repr (XyzVar n) where
  reprPrec v _ := s!"'{v.ch}'"

def toChars {n : ℕ} (v : XyzVar n) : List Char := [v.ch]

def parse {n : ℕ} (c : Char) : Option (XyzVar n) :=
  if h : c.toNat ≥ 'a'.toNat ∧ c.toNat ≤ 'z'.toNat ∧
      xyzRank (c.toNat - 'a'.toNat) < n then
    some ⟨c, h⟩
  else none

theorem parse_toChars {n : ℕ} (v : XyzVar n) :
    XyzVar.parse v.ch = some v := by
  simp only [parse, dite_eq_left v.is_valid]

/-- Construct an `XyzVar` from a `Fin n` rank (0 → 'x', 1 → 'y', 2 → 'z', 3 → 'w', ...). -/
def ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) : XyzVar n :=
  ⟨Char.ofNat ('a'.toNat + xyzUnrank i.val), by
    simp only [show ('a' : Char).toNat = 97 from by decide,
               show ('z' : Char).toNat = 122 from by decide]
    have hunrank_le : xyzUnrank i.val ≤ 25 := by simp [xyzUnrank]; split <;> omega
    rw [charOfNat_toNat_small (97 + xyzUnrank i.val) (by omega)]
    refine ⟨by omega, by omega, ?_⟩
    rw [show 97 + xyzUnrank i.val - 97 = xyzUnrank i.val from by omega]
    rw [xyzRank_xyzUnrank i.val (by omega)]
    exact i.isLt⟩

theorem ofIndex_index {n : ℕ} (hn : n ≤ 26) (v : XyzVar n) :
    XyzVar.ofIndex hn (XyzVar.index v) = v := by
  simp only [ofIndex, index]
  congr 1
  have hge := v.is_valid.1; have hle := v.is_valid.2.1
  simp only [show ('a' : Char).toNat = 97 from by decide,
             show ('z' : Char).toNat = 122 from by decide] at hge hle ⊢
  rw [xyzUnrank_xyzRank (v.ch.toNat - 97) (by omega)]
  rw [show 97 + (v.ch.toNat - 97) = v.ch.toNat from by omega]
  exact Char.ofNat_toNat v.ch

theorem index_ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) :
    XyzVar.index (XyzVar.ofIndex hn i) = i := by
  simp only [index, ofIndex]
  ext
  simp only [show ('a' : Char).toNat = 97 from by decide]
  have hunrank_le : xyzUnrank i.val ≤ 25 := by simp [xyzUnrank]; split <;> omega
  rw [charOfNat_toNat_small (97 + xyzUnrank i.val) (by omega)]
  rw [show 97 + xyzUnrank i.val - 97 = xyzUnrank i.val from by omega]
  rw [xyzRank_xyzUnrank i.val (by omega)]

instance {n : ℕ} [Fact (n ≤ 26)] : Var (XyzVar n) n where
  toFin := index
  ofFin := ofIndex (Fact.out)
  ofFin_toFin := ofIndex_index (Fact.out)
  toFin_ofFin := index_ofIndex (Fact.out)

instance {n : ℕ} [Fact (n ≤ 26)] : ParsableVar (XyzVar n) n where
  toChars v := [v.ch]
  parseChars cs := match cs with
    | [c] => if h : c.toNat ≥ 'a'.toNat ∧ c.toNat ≤ 'z'.toNat ∧
        xyzRank (c.toNat - 'a'.toNat) < n then
        some ⟨c, h⟩
      else none
    | _ => none
  parse_toChars v := by simp only [dite_eq_left v.is_valid]
  toChars_nonempty _ := by simp
  toChars_no_syntax v c hc := by
    simp at hc; subst hc
    have hge := v.is_valid.1; have hle := v.is_valid.2.1
    simp only [show ('a' : Char).toNat = 97 from by decide,
               show ('z' : Char).toNat = 122 from by decide] at hge hle
    exact lowercase_not_syntax v.ch hge hle


end XyzVar

/-- A variable with ordering X, Y, Z, W, V, U, ..., A (capital letters).
    Stores the raw character with a validity proof.
    Construction: `⟨'X', by omega⟩`, `⟨'Y', by omega⟩`, etc. -/
structure XyzCapsVar (n : ℕ) where
  ch : Char
  is_valid : ch.toNat ≥ 'A'.toNat ∧ ch.toNat ≤ 'Z'.toNat ∧
    xyzRank (ch.toNat - 'A'.toNat) < n
  deriving DecidableEq

namespace XyzCapsVar

/-- The zero-based xyz-rank of this variable (0 for 'X', 1 for 'Y', 2 for 'Z', 3 for 'W', ...). -/
def index {n : ℕ} (v : XyzCapsVar n) : Fin n :=
  ⟨xyzRank (v.ch.toNat - 'A'.toNat), v.is_valid.2.2⟩

private theorem index_injective {n : ℕ} : Function.Injective (index : XyzCapsVar n → Fin n) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [index, Fin.mk.injEq] at h
  simp only [show 'A'.toNat = 65 from by decide,
             show 'Z'.toNat = 90 from by decide] at ha hb h ⊢
  have hab := XyzVar.xyzRank_injective _ _ (by omega) (by omega) h
  have : a = b := by rw [← Char.ofNat_toNat a, ← Char.ofNat_toNat b]; congr 1; omega
  subst this; rfl

instance {n : ℕ} : LinearOrder (XyzCapsVar n) :=
  LinearOrder.lift' index index_injective

instance {n : ℕ} : Ord (XyzCapsVar n) where
  compare a b := compare a.index b.index

instance {n : ℕ} : ToString (XyzCapsVar n) where
  toString v := String.ofList [v.ch]

instance {n : ℕ} : Repr (XyzCapsVar n) where
  reprPrec v _ := s!"'{v.ch}'"

def toChars {n : ℕ} (v : XyzCapsVar n) : List Char := [v.ch]

def parse {n : ℕ} (c : Char) : Option (XyzCapsVar n) :=
  if h : c.toNat ≥ 'A'.toNat ∧ c.toNat ≤ 'Z'.toNat ∧
      xyzRank (c.toNat - 'A'.toNat) < n then
    some ⟨c, h⟩
  else none

theorem parse_toChars {n : ℕ} (v : XyzCapsVar n) :
    XyzCapsVar.parse v.ch = some v := by
  simp only [parse, dite_eq_left v.is_valid]

/-- Construct an `XyzCapsVar` from a `Fin n` rank (0 → 'X', 1 → 'Y', 2 → 'Z', 3 → 'W', ...). -/
def ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) : XyzCapsVar n :=
  ⟨Char.ofNat ('A'.toNat + xyzUnrank i.val), by
    simp only [show ('A' : Char).toNat = 65 from by decide,
               show ('Z' : Char).toNat = 90 from by decide]
    have hunrank_le : xyzUnrank i.val ≤ 25 := by simp [xyzUnrank]; split <;> omega
    rw [charOfNat_toNat_small (65 + xyzUnrank i.val) (by omega)]
    refine ⟨by omega, by omega, ?_⟩
    rw [show 65 + xyzUnrank i.val - 65 = xyzUnrank i.val from by omega]
    rw [xyzRank_xyzUnrank i.val (by omega)]
    exact i.isLt⟩

theorem ofIndex_index {n : ℕ} (hn : n ≤ 26) (v : XyzCapsVar n) :
    XyzCapsVar.ofIndex hn (XyzCapsVar.index v) = v := by
  simp only [ofIndex, index]
  congr 1
  have hge := v.is_valid.1; have hle := v.is_valid.2.1
  simp only [show ('A' : Char).toNat = 65 from by decide,
             show ('Z' : Char).toNat = 90 from by decide] at hge hle ⊢
  rw [xyzUnrank_xyzRank (v.ch.toNat - 65) (by omega)]
  rw [show 65 + (v.ch.toNat - 65) = v.ch.toNat from by omega]
  exact Char.ofNat_toNat v.ch

theorem index_ofIndex {n : ℕ} (hn : n ≤ 26) (i : Fin n) :
    XyzCapsVar.index (XyzCapsVar.ofIndex hn i) = i := by
  simp only [index, ofIndex]
  ext
  simp only [show ('A' : Char).toNat = 65 from by decide]
  have hunrank_le : xyzUnrank i.val ≤ 25 := by simp [xyzUnrank]; split <;> omega
  rw [charOfNat_toNat_small (65 + xyzUnrank i.val) (by omega)]
  rw [show 65 + xyzUnrank i.val - 65 = xyzUnrank i.val from by omega]
  rw [xyzRank_xyzUnrank i.val (by omega)]

instance {n : ℕ} [Fact (n ≤ 26)] : Var (XyzCapsVar n) n where
  toFin := index
  ofFin := ofIndex (Fact.out)
  ofFin_toFin := ofIndex_index (Fact.out)
  toFin_ofFin := index_ofIndex (Fact.out)

instance {n : ℕ} [Fact (n ≤ 26)] : ParsableVar (XyzCapsVar n) n where
  toChars v := [v.ch]
  parseChars cs := match cs with
    | [c] => if h : c.toNat ≥ 'A'.toNat ∧ c.toNat ≤ 'Z'.toNat ∧
        xyzRank (c.toNat - 'A'.toNat) < n then
        some ⟨c, h⟩
      else none
    | _ => none
  parse_toChars v := by simp only [dite_eq_left v.is_valid]
  toChars_nonempty _ := by simp
  toChars_no_syntax v c hc := by
    simp at hc; subst hc
    have hge := v.is_valid.1; have hle := v.is_valid.2.1
    simp only [show ('A' : Char).toNat = 65 from by decide,
               show ('Z' : Char).toNat = 90 from by decide] at hge hle
    exact uppercase_not_syntax v.ch hge hle

end XyzCapsVar

/-! ### Greek letter helpers -/

/-- Map a Greek lowercase char to its 0-based index
    (0 = α, ..., 16 = ρ, 17 = σ, ..., 23 = ω), skipping ς (U+03C2 = 962). -/
private def greekCharIndex (c : Char) : ℕ :=
  if c.toNat ≤ 961 then c.toNat - 945 else c.toNat - 946

/-- Map a 0-based index to a Greek lowercase char. -/
private def greekCharOfIndex (i : ℕ) : Char :=
  Char.ofNat (if i ≤ 16 then i + 945 else i + 946)

private theorem greekCharIndex_greekCharOfIndex (i : ℕ) (hi : i < 24) :
    greekCharIndex (greekCharOfIndex i) = i := by
  simp only [greekCharIndex, greekCharOfIndex]
  split
  · simp only [charOfNat_toNat_small (i + 945) (by omega)]
    split <;> omega
  · simp only [charOfNat_toNat_small (i + 946) (by omega)]
    split <;> omega

private theorem greekCharOfIndex_greekCharIndex (c : Char)
    (hge : c.toNat ≥ 945) (hle : c.toNat ≤ 969) (hne : c.toNat ≠ 962) :
    greekCharOfIndex (greekCharIndex c) = c := by
  simp only [greekCharOfIndex, greekCharIndex]
  split
  · -- c.toNat ≤ 961
    rename_i h
    have idx_le : c.toNat - 945 ≤ 16 := by omega
    rw [ite_eq_left idx_le]
    rw [show c.toNat - 945 + 945 = c.toNat from by omega]
    exact Char.ofNat_toNat c
  · -- c.toNat > 961
    rename_i h; push Not at h
    have idx_gt : ¬ (c.toNat - 946 ≤ 16) := by omega
    rw [ite_eq_right idx_gt]
    rw [show c.toNat - 946 + 946 = c.toNat from by omega]
    exact Char.ofNat_toNat c

private theorem greekCharIndex_bound (c : Char)
    (hge : c.toNat ≥ 945) (hle : c.toNat ≤ 969) :
    greekCharIndex c < 24 := by
  simp only [greekCharIndex]; split <;> omega

private theorem greekCharOfIndex_valid (i : ℕ) (hi : i < 24) :
    (greekCharOfIndex i).toNat ≥ 945 ∧ (greekCharOfIndex i).toNat ≤ 969 ∧
    (greekCharOfIndex i).toNat ≠ 962 := by
  simp only [greekCharOfIndex]
  split
  · rw [charOfNat_toNat_small (i + 945) (by omega)]; omega
  · rw [charOfNat_toNat_small (i + 946) (by omega)]; omega

private theorem greekCharIndex_injective :
    ∀ a b : Char, a.toNat ≥ 945 → a.toNat ≤ 969 → a.toNat ≠ 962 →
    b.toNat ≥ 945 → b.toNat ≤ 969 → b.toNat ≠ 962 →
    greekCharIndex a = greekCharIndex b → a = b := by
  intro a b ha1 ha2 _ hb1 hb2 _ h
  simp only [greekCharIndex] at h
  rw [← Char.ofNat_toNat a, ← Char.ofNat_toNat b]; congr 1
  split at h <;> split at h <;> omega

private theorem greek_not_syntax (c : Char) (hge : c.toNat ≥ 945) :
    ¬ isPolySyntaxChar c := by
  simp only [isPolySyntaxChar, not_or, not_and,
    show ('0' : Char).toNat = 48 from by decide,
    show ('9' : Char).toNat = 57 from by decide]
  refine ⟨fun _ => by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; simp [h] at hge)

/-! ### GreekVar -/

/-- A variable named by a lowercase Greek letter: α, β, γ, ..., ρ, σ, ..., ω
    (24 letters, skipping ς). `n` is the number of variables in scope (at most 24).
    Stores the raw character with a validity proof. -/
structure GreekVar (n : ℕ) where
  ch : Char
  is_valid : ch.toNat ≥ 945 ∧ ch.toNat ≤ 969 ∧ ch.toNat ≠ 962 ∧
    greekCharIndex ch < n
  deriving DecidableEq

namespace GreekVar

/-- The zero-based index of this variable (0 for α, 1 for β, ..., 23 for ω). -/
def index {n : ℕ} (v : GreekVar n) : Fin n :=
  ⟨greekCharIndex v.ch, v.is_valid.2.2.2⟩

private theorem index_injective {n : ℕ} : Function.Injective (index : GreekVar n → Fin n) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [index, Fin.mk.injEq] at h
  have := greekCharIndex_injective a b ha.1 ha.2.1 ha.2.2.1 hb.1 hb.2.1 hb.2.2.1 h
  subst this; rfl

instance {n : ℕ} : LinearOrder (GreekVar n) :=
  LinearOrder.lift' index index_injective

instance {n : ℕ} : Ord (GreekVar n) where
  compare a b := compare a.index b.index

instance {n : ℕ} : ToString (GreekVar n) where
  toString v := String.ofList [v.ch]

instance {n : ℕ} : Repr (GreekVar n) where
  reprPrec v _ := s!"'{v.ch}'"

def toChars {n : ℕ} (v : GreekVar n) : List Char := [v.ch]

def parse {n : ℕ} (c : Char) : Option (GreekVar n) :=
  if h : c.toNat ≥ 945 ∧ c.toNat ≤ 969 ∧ c.toNat ≠ 962 ∧
      greekCharIndex c < n then
    some ⟨c, h⟩
  else none

theorem parse_toChars {n : ℕ} (v : GreekVar n) :
    GreekVar.parse v.ch = some v := by
  simp only [parse, dite_eq_left v.is_valid]

/-- Construct a `GreekVar` from a `Fin n` index (0 → α, 1 → β, ..., 23 → ω). -/
def ofIndex {n : ℕ} (hn : n ≤ 24) (i : Fin n) : GreekVar n :=
  ⟨greekCharOfIndex i.val, by
    have hv := greekCharOfIndex_valid i.val (by omega)
    refine ⟨hv.1, hv.2.1, hv.2.2, ?_⟩
    rw [greekCharIndex_greekCharOfIndex i.val (by omega)]
    exact i.isLt⟩

theorem ofIndex_index {n : ℕ} (hn : n ≤ 24) (v : GreekVar n) :
    GreekVar.ofIndex hn (GreekVar.index v) = v := by
  simp only [ofIndex, index]
  congr 1
  exact greekCharOfIndex_greekCharIndex v.ch v.is_valid.1 v.is_valid.2.1 v.is_valid.2.2.1

theorem index_ofIndex {n : ℕ} (hn : n ≤ 24) (i : Fin n) :
    GreekVar.index (GreekVar.ofIndex hn i) = i := by
  simp only [index, ofIndex]
  ext
  have hv := greekCharOfIndex_valid i.val (by omega)
  exact greekCharIndex_greekCharOfIndex i.val (by omega)

instance {n : ℕ} [Fact (n ≤ 24)] : Var (GreekVar n) n where
  toFin := index
  ofFin := ofIndex (Fact.out)
  ofFin_toFin := ofIndex_index (Fact.out)
  toFin_ofFin := index_ofIndex (Fact.out)

instance {n : ℕ} [Fact (n ≤ 24)] : ParsableVar (GreekVar n) n where
  toChars v := [v.ch]
  parseChars cs := match cs with
    | [c] => if h : c.toNat ≥ 945 ∧ c.toNat ≤ 969 ∧ c.toNat ≠ 962 ∧
          greekCharIndex c < n then
        some ⟨c, h⟩
      else none
    | _ => none
  parse_toChars v := by simp only [dite_eq_left v.is_valid]
  toChars_nonempty _ := by simp
  toChars_no_syntax v c hc := by
    simp at hc; subst hc
    exact greek_not_syntax v.ch v.is_valid.1

end GreekVar

/-! ### Greek capital letter helpers -/

/-- Map a Greek uppercase char to its 0-based index
    (0 = Α, ..., 16 = Ρ, 17 = Σ, ..., 23 = Ω), skipping unassigned U+03A2 (930). -/
private def greekCapsCharIndex (c : Char) : ℕ :=
  if c.toNat ≤ 929 then c.toNat - 913 else c.toNat - 914

/-- Map a 0-based index to a Greek uppercase char. -/
private def greekCapsCharOfIndex (i : ℕ) : Char :=
  Char.ofNat (if i ≤ 16 then i + 913 else i + 914)

private theorem greekCapsCharIndex_greekCapsCharOfIndex (i : ℕ) (hi : i < 24) :
    greekCapsCharIndex (greekCapsCharOfIndex i) = i := by
  simp only [greekCapsCharIndex, greekCapsCharOfIndex]
  split
  · simp only [charOfNat_toNat_small (i + 913) (by omega)]
    split <;> omega
  · simp only [charOfNat_toNat_small (i + 914) (by omega)]
    split <;> omega

private theorem greekCapsCharOfIndex_greekCapsCharIndex (c : Char)
    (hge : c.toNat ≥ 913) (hle : c.toNat ≤ 937) (hne : c.toNat ≠ 930) :
    greekCapsCharOfIndex (greekCapsCharIndex c) = c := by
  simp only [greekCapsCharOfIndex, greekCapsCharIndex]
  split
  · rename_i h
    have idx_le : c.toNat - 913 ≤ 16 := by omega
    rw [ite_eq_left idx_le]
    rw [show c.toNat - 913 + 913 = c.toNat from by omega]
    exact Char.ofNat_toNat c
  · rename_i h; push Not at h
    have idx_gt : ¬ (c.toNat - 914 ≤ 16) := by omega
    rw [ite_eq_right idx_gt]
    rw [show c.toNat - 914 + 914 = c.toNat from by omega]
    exact Char.ofNat_toNat c

private theorem greekCapsCharIndex_bound (c : Char)
    (hge : c.toNat ≥ 913) (hle : c.toNat ≤ 937) :
    greekCapsCharIndex c < 24 := by
  simp only [greekCapsCharIndex]; split <;> omega

private theorem greekCapsCharOfIndex_valid (i : ℕ) (hi : i < 24) :
    (greekCapsCharOfIndex i).toNat ≥ 913 ∧ (greekCapsCharOfIndex i).toNat ≤ 937 ∧
    (greekCapsCharOfIndex i).toNat ≠ 930 := by
  simp only [greekCapsCharOfIndex]
  split
  · rw [charOfNat_toNat_small (i + 913) (by omega)]; omega
  · rw [charOfNat_toNat_small (i + 914) (by omega)]; omega

private theorem greekCapsCharIndex_injective :
    ∀ a b : Char, a.toNat ≥ 913 → a.toNat ≤ 937 → a.toNat ≠ 930 →
    b.toNat ≥ 913 → b.toNat ≤ 937 → b.toNat ≠ 930 →
    greekCapsCharIndex a = greekCapsCharIndex b → a = b := by
  intro a b ha1 ha2 _ hb1 hb2 _ h
  simp only [greekCapsCharIndex] at h
  rw [← Char.ofNat_toNat a, ← Char.ofNat_toNat b]; congr 1
  split at h <;> split at h <;> omega

private theorem greekCaps_not_syntax (c : Char) (hge : c.toNat ≥ 913) :
    ¬ isPolySyntaxChar c := by
  simp only [isPolySyntaxChar, not_or, not_and,
    show ('0' : Char).toNat = 48 from by decide,
    show ('9' : Char).toNat = 57 from by decide]
  refine ⟨fun _ => by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; simp [h] at hge)

/-! ### GreekCapsVar -/

/-- A variable named by an uppercase Greek letter: Α, Β, Γ, ..., Ρ, Σ, ..., Ω
    (24 letters, skipping unassigned U+03A2). `n` is the number of variables in scope (at most 24).
    Stores the raw character with a validity proof. -/
structure GreekCapsVar (n : ℕ) where
  ch : Char
  is_valid : ch.toNat ≥ 913 ∧ ch.toNat ≤ 937 ∧ ch.toNat ≠ 930 ∧
    greekCapsCharIndex ch < n
  deriving DecidableEq

namespace GreekCapsVar

/-- The zero-based index of this variable (0 for Α, 1 for Β, ..., 23 for Ω). -/
def index {n : ℕ} (v : GreekCapsVar n) : Fin n :=
  ⟨greekCapsCharIndex v.ch, v.is_valid.2.2.2⟩

private theorem index_injective {n : ℕ} : Function.Injective (index : GreekCapsVar n → Fin n) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [index, Fin.mk.injEq] at h
  have := greekCapsCharIndex_injective a b ha.1 ha.2.1 ha.2.2.1 hb.1 hb.2.1 hb.2.2.1 h
  subst this; rfl

instance {n : ℕ} : LinearOrder (GreekCapsVar n) :=
  LinearOrder.lift' index index_injective

instance {n : ℕ} : Ord (GreekCapsVar n) where
  compare a b := compare a.index b.index

instance {n : ℕ} : ToString (GreekCapsVar n) where
  toString v := String.ofList [v.ch]

instance {n : ℕ} : Repr (GreekCapsVar n) where
  reprPrec v _ := s!"'{v.ch}'"

def toChars {n : ℕ} (v : GreekCapsVar n) : List Char := [v.ch]

def parse {n : ℕ} (c : Char) : Option (GreekCapsVar n) :=
  if h : c.toNat ≥ 913 ∧ c.toNat ≤ 937 ∧ c.toNat ≠ 930 ∧
      greekCapsCharIndex c < n then
    some ⟨c, h⟩
  else none

theorem parse_toChars {n : ℕ} (v : GreekCapsVar n) :
    GreekCapsVar.parse v.ch = some v := by
  simp only [parse, dite_eq_left v.is_valid]

/-- Construct a `GreekCapsVar` from a `Fin n` index (0 → Α, 1 → Β, ..., 23 → Ω). -/
def ofIndex {n : ℕ} (hn : n ≤ 24) (i : Fin n) : GreekCapsVar n :=
  ⟨greekCapsCharOfIndex i.val, by
    have hv := greekCapsCharOfIndex_valid i.val (by omega)
    refine ⟨hv.1, hv.2.1, hv.2.2, ?_⟩
    rw [greekCapsCharIndex_greekCapsCharOfIndex i.val (by omega)]
    exact i.isLt⟩

theorem ofIndex_index {n : ℕ} (hn : n ≤ 24) (v : GreekCapsVar n) :
    GreekCapsVar.ofIndex hn (GreekCapsVar.index v) = v := by
  simp only [ofIndex, index]
  congr 1
  exact greekCapsCharOfIndex_greekCapsCharIndex v.ch v.is_valid.1 v.is_valid.2.1 v.is_valid.2.2.1

theorem index_ofIndex {n : ℕ} (hn : n ≤ 24) (i : Fin n) :
    GreekCapsVar.index (GreekCapsVar.ofIndex hn i) = i := by
  simp only [index, ofIndex]
  ext
  have hv := greekCapsCharOfIndex_valid i.val (by omega)
  exact greekCapsCharIndex_greekCapsCharOfIndex i.val (by omega)

instance {n : ℕ} [Fact (n ≤ 24)] : Var (GreekCapsVar n) n where
  toFin := index
  ofFin := ofIndex (Fact.out)
  ofFin_toFin := ofIndex_index (Fact.out)
  toFin_ofFin := index_ofIndex (Fact.out)

instance {n : ℕ} [Fact (n ≤ 24)] : ParsableVar (GreekCapsVar n) n where
  toChars v := [v.ch]
  parseChars cs := match cs with
    | [c] => if h : c.toNat ≥ 913 ∧ c.toNat ≤ 937 ∧ c.toNat ≠ 930 ∧
          greekCapsCharIndex c < n then
        some ⟨c, h⟩
      else none
    | _ => none
  parse_toChars v := by simp only [dite_eq_left v.is_valid]
  toChars_nonempty _ := by simp
  toChars_no_syntax v c hc := by
    simp at hc; subst hc
    exact greekCaps_not_syntax v.ch v.is_valid.1

end GreekCapsVar

/-! ### ListVar: variables defined by an arbitrary list -/

/-- A variable type defined by an arbitrary list of distinct objects.
    The position in the list determines the ordering: first element = index 0 = smallest.
    Users must provide `Fact l.Nodup` to ensure the labels are distinct.

    Example usage:
    ```
    def myVars : List String := ["x", "y", "z"]
    instance : Fact myVars.Nodup := ⟨by decide⟩
    -- Now `ListVar myVars` is a `Var` with 3 variables
    ``` -/
@[ext]
structure ListVar {α : Type} (l : List α) where
  val : Fin l.length
  deriving DecidableEq

namespace ListVar

instance {α : Type} {l : List α} : LinearOrder (ListVar l) :=
  LinearOrder.lift' (fun v => v.val) (fun _ _ h => ListVar.ext h)

instance {α : Type} {l : List α} : Ord (ListVar l) where
  compare a b := compare a.val b.val

instance {α : Type} [ToString α] {l : List α} : ToString (ListVar l) where
  toString v := toString (l.get v.val)

instance {α : Type} [Repr α] {l : List α} : Repr (ListVar l) where
  reprPrec v p := reprPrec (l.get v.val) p

/-- The label (list element) corresponding to this variable. -/
def label {α : Type} {l : List α} (v : ListVar l) : α := l.get v.val

instance {α : Type} {l : List α} [Fact l.Nodup] : Var (ListVar l) l.length where
  toFin v := v.val
  ofFin i := ⟨i⟩
  ofFin_toFin _ := rfl
  toFin_ofFin _ := rfl

/-- The conditions under which `ListVar l` supports parsing:
    1. The `toString` representations (as char lists) are pairwise distinct
    2. Each representation is nonempty
    3. No character in any representation is a polynomial syntax character

    This predicate is decidable, so users can write `instance : Fact (ListVarParsable l) := ⟨by decide⟩`. -/
def ListVarParsable {α : Type} [ToString α] (l : List α) : Prop :=
  (l.map (fun a => (toString a).toList)).Nodup ∧
  (∀ a ∈ l, (toString a).toList ≠ []) ∧
  (∀ a ∈ l, ∀ c ∈ (toString a).toList, ¬ isPolySyntaxChar c)

instance {α : Type} [ToString α] [DecidableEq α] (l : List α) :
    Decidable (ListVarParsable l) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Search for a char list in the toString representations of a list.
    Returns the index of the first match, or `none`. -/
private def findByToString [ToString α] : List α → List Char → Option ℕ
  | [], _ => none
  | a :: as, cs =>
    if (toString a).toList = cs then some 0
    else (findByToString as cs).map (· + 1)

private theorem findByToString_self [ToString α] :
    ∀ (l : List α) (i : ℕ) (hi : i < l.length),
    (l.map (fun a => (toString a).toList)).Nodup →
    findByToString l ((toString (l.get ⟨i, hi⟩)).toList) = some i := by
  intro l
  induction l with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | cons a as ih =>
    intro i hi hnodup
    rw [List.map_cons, List.nodup_cons] at hnodup
    simp only [findByToString]
    cases i with
    | zero => simp [List.get]
    | succ j =>
      have hj : j < as.length := by simp [List.length_cons] at hi; omega
      simp only [List.get_cons_succ]
      have hne : (toString a).toList ≠ (toString (as.get ⟨j, hj⟩)).toList := by
        intro heq
        have hmem := @List.mem_map_of_mem _ _ as _ (fun a => (toString a).toList) (List.get_mem as ⟨j, hj⟩)
        exact hnodup.1 (heq ▸ hmem)
      rw [ite_eq_right hne, ih j hj hnodup.2]
      simp [Option.map]

private theorem findByToString_lt [ToString α] :
    ∀ (l : List α) (cs : List Char) (i : ℕ),
    findByToString l cs = some i → i < l.length := by
  intro l
  induction l with
  | nil => intro cs i h; simp [findByToString] at h
  | cons a as ih =>
    intro cs i h
    simp only [findByToString] at h
    split at h
    · simp at h; subst h; simp [List.length_cons]
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      have := ih cs j hj
      simp only [List.length_cons]
      omega

instance {α : Type} [ToString α] {l : List α}
    [Fact l.Nodup] [Fact (ListVarParsable l)] :
    ParsableVar (ListVar l) l.length where
  toChars v := (toString (l.get v.val)).toList
  parseChars cs :=
    let idx := findByToString l cs
    idx.bind (fun i => if hi : i < l.length then some ⟨⟨i, hi⟩⟩ else none)
  parse_toChars v := by
    have hp := (Fact.out : ListVarParsable l)
    have hrw := findByToString_self l v.val.val v.val.isLt hp.1
    simp only [Option.bind, hrw, v.val.isLt, dite_true]
  toChars_nonempty v := by
    have hp := (Fact.out : ListVarParsable l)
    exact hp.2.1 (l.get v.val) (List.get_mem l v.val)
  toChars_no_syntax v c hc := by
    have hp := (Fact.out : ListVarParsable l)
    exact hp.2.2 (l.get v.val) (List.get_mem l v.val) c hc

end ListVar

end Azurite
