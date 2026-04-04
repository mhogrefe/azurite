import Azurite.AzNat.Equiv.Basic

namespace Azurite

def natToCharsAux (fuel : ℕ) (n : ℕ) (acc : List Char) : List Char :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    if n = 0 then acc
    else
      let digit := Char.ofNat ('0'.toNat + (n % 10))
      natToCharsAux f (n / 10) (digit :: acc)

def natToChars (n : ℕ) : List Char :=
  if n = 0 then ['0']
  else natToCharsAux n n []

namespace AzNat

def toChars (n : AzNat) : List Char :=
  natToChars (toNat n)

instance : ToString AzNat where
  toString n := String.ofList (toChars n)

end AzNat
end Azurite
