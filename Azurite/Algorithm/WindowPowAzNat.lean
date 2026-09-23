/-
  **Fixed-window exponentiation with an `AzNat` exponent.**  `slidingWindowPowAzNat`
  is plain square-and-multiply; here the exponent is read in windows of `w = 5`
  bits (`getBitsAsLimb`, limb-level) against a table of `a^0, …, a^31`, so an
  `s`-bit exponent costs `s` squarings and about `s/5 + 31` multiplications
  instead of `s` squarings and `s/2` multiplications.  Correctness
  (`windowPowAzNat_eq_pow`) is in `Azurite/Algorithm/Equiv/WindowPowAzNat.lean`.
-/
import Azurite.Algorithm.SlidingWindowPow
import Azurite.AzNat.GetBits
import Azurite.AzNat.Size

namespace Azurite

variable {M : Type _} [Mul M] [One M] [Square M]

/-- The window width. -/
def windowW : ℕ := 5

/-- The table `a^0, …, a^(2^w − 1)`, by repeated multiplication. -/
def powTable (a : M) (w : ℕ) : Array M :=
  ((List.range (2 ^ w)).foldl (fun (st : Array M × M) _ => (st.1.push st.2, st.2 * a)) (#[], 1)).1

/-- Process the windows `j − 1, …, 0` (bits `[i·w, i·w + w)`), from the top. -/
def windowPowAux (table : Array M) (e : AzNat) : ℕ → M → M
  | 0, r => r
  | j + 1, r =>
    let r' := squareN r windowW
    let d := e.getBitsAsLimb (j * windowW) (j * windowW + windowW) (by unfold windowW; omega)
    windowPowAux table e j (r' * table.getD d.toNat 1)

/-- **Fixed-window exponentiation** `a ^ e` for an `AzNat` exponent. -/
def windowPowAzNat (a : M) (e : AzNat) : M :=
  windowPowAux (powTable a windowW) e ((e.size + windowW - 1) / windowW) 1

end Azurite
