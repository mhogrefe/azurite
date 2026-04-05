import Mathlib
import Azurite.AzNat.Equiv.Compare

namespace Azurite.AzNat

instance : WellFoundedRelation AzNat where
  rel := (· < ·)
  wf := InvImage.wf (·.toNat) Nat.lt_wfRel.wf

instance : WellFoundedLT AzNat where
  wf := by
    have h : WellFounded (fun (a b : AzNat) => a.toNat < b.toNat) := InvImage.wf toNat wellFounded_lt
    apply WellFounded.intro
    intro a
    -- Wait, if `a < b ↔ a.toNat < b.toNat`, the relation is exactly the Inverse Image!
    sorry

end Azurite.AzNat
