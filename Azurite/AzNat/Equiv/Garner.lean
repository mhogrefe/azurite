/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Correctness of the limb-level Garner reconstruction: on positive,
  pairwise coprime moduli, `(garner ms ns).toNat` equals the proven
  reference `CP.garner` (`toNat_garner`), so the reference
  specification transfers verbatim:

  * `garner_lt` — the result lies in `[0, M−1]`;
  * `garner_modEq` — it has the given residues;
  * `eq_garner_of_modEq` — and it is the UNIQUE such value.

  The bridge is by induction along the loop, exchanging
  `AzNat.invMod` for `CP.invMod` at each step (`toNat_invMod`, which
  needs the running-product coprimality — hence the pairwise
  hypothesis on the bridge, unlike the hypothesis-free step
  bridge `toNat_garnerStep`).
-/
import Azurite.AzNat.Garner
import Azurite.AzNat.Equiv.InvMod
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.RingEquiv

namespace Azurite

namespace AzNat

theorem toNat_garnerStep (mᵢ μ c nᵢ x : AzNat) :
    (garnerStep mᵢ μ c nᵢ x).toNat
      = CP.garnerStep mᵢ.toNat μ.toNat c.toNat nᵢ.toNat x.toNat := by
  rw [garnerStep, CP.garnerStep, toNat_add, toNat_mul, toNat_mod,
    toNat_mul, toNat_add, toNat_mod, toNat_sub, toNat_mod]

theorem toNat_garnerLoop (μ : AzNat) (ms : List AzNat) :
    ∀ (x : AzNat) (ns : List AzNat), (∀ m ∈ ms, 0 < m.toNat) →
    (∀ m ∈ ms, Nat.Coprime μ.toNat m.toNat) →
    (ms.map toNat).Pairwise Nat.Coprime →
    (garnerLoop x (garnerPrecomp μ ms) ns).toNat
      = CP.garnerLoop x.toNat (CP.garnerPrecomp μ.toNat (ms.map toNat))
          (ns.map toNat) := by
  induction ms generalizing μ with
  | nil =>
    intro x ns _ _ _
    cases ns <;> rfl
  | cons mᵢ ms ih =>
    intro x ns hpos hcoμ hco
    match ns with
    | [] => rfl
    | nᵢ :: ns =>
      have hmᵢ : 0 < mᵢ.toNat := hpos mᵢ (by simp)
      have hc : Nat.Coprime μ.toNat mᵢ.toNat := hcoμ mᵢ (by simp)
      have hhead : (garnerStep mᵢ μ (invMod μ mᵢ) nᵢ x).toNat
          = CP.garnerStep mᵢ.toNat μ.toNat (CP.invMod μ.toNat mᵢ.toNat)
              nᵢ.toNat x.toNat := by
        rw [toNat_garnerStep, toNat_invMod hc hmᵢ]
      have hpair := List.pairwise_cons.mp hco
      have htail := ih (μ * mᵢ) (garnerStep mᵢ μ (invMod μ mᵢ) nᵢ x) ns
        (fun m hm => hpos m (List.mem_cons_of_mem _ hm))
        (fun m hm => by
          rw [toNat_mul]
          exact (Nat.Coprime.mul_right
            (hcoμ m (List.mem_cons_of_mem _ hm)).symm
            (hpair.1 m.toNat (List.mem_map_of_mem hm)).symm).symm)
        hpair.2
      show (garnerLoop (garnerStep mᵢ μ (invMod μ mᵢ) nᵢ x)
          (garnerPrecomp (μ * mᵢ) ms) ns).toNat = _
      rw [htail, hhead, toNat_mul]
      rfl

/-- **The bridge**: on positive, pairwise coprime moduli the
limb-level Garner agrees with the proven reference. -/
theorem toNat_garner (ms ns : List AzNat)
    (hpos : ∀ m ∈ ms, 0 < m.toNat)
    (hco : (ms.map toNat).Pairwise Nat.Coprime) :
    (garner ms ns).toNat = CP.garner (ms.map toNat) (ns.map toNat) := by
  match ms, ns with
  | [], _ => cases ns <;> rfl
  | m₀ :: ms', [] => rfl
  | m₀ :: ms', n₀ :: ns' =>
    have hpair := List.pairwise_cons.mp hco
    have hprod : ((m₀ :: ms').prod).toNat = ((m₀ :: ms').map toNat).prod := by
      have h := map_list_prod toNatRingHom (m₀ :: ms')
      rwa [show ⇑toNatRingHom = toNat from funext fun _ => rfl] at h
    show (garnerLoop (n₀ % m₀) (garnerPrecomp m₀ ms') ns'
        % (m₀ :: ms').prod).toNat = _
    rw [toNat_mod, hprod,
      toNat_garnerLoop m₀ ms' (n₀ % m₀) ns'
        (fun m hm => hpos m (List.mem_cons_of_mem _ hm))
        (fun m hm => hpair.1 m.toNat (List.mem_map_of_mem hm))
        hpair.2,
      toNat_mod]
    rfl

/-- **Correctness, part 1** (transferred): the result lies in
`[0, M−1]`. -/
theorem garner_lt (ms ns : List AzNat)
    (hpos : ∀ m ∈ ms, 0 < m.toNat)
    (hco : (ms.map toNat).Pairwise Nat.Coprime) :
    (garner ms ns).toNat < (ms.map toNat).prod := by
  rw [toNat_garner ms ns hpos hco]
  exact CP.garner_lt _ _ (by simpa using hpos)

/-- **Correctness, part 2** (transferred): the result has the given
residues. -/
theorem garner_modEq (ms ns : List AzNat)
    (hpos : ∀ m ∈ ms, 0 < m.toNat)
    (hco : (ms.map toNat).Pairwise Nat.Coprime) :
    ∀ p ∈ ms.zip ns, (garner ms ns).toNat ≡ p.2.toNat [MOD p.1.toNat] := by
  intro p hp
  rw [toNat_garner ms ns hpos hco]
  have hmem : (p.1.toNat, p.2.toNat) ∈ (ms.map toNat).zip (ns.map toNat) := by
    rw [List.zip_map]
    exact List.mem_map_of_mem hp
  exact CP.garner_modEq _ _ (by simpa using hpos) hco _ hmem

/-- **Uniqueness** (transferred): any `x < M` with the given residues
IS the limb-level result. -/
theorem eq_garner_of_modEq (ms ns : List AzNat)
    (hpos : ∀ m ∈ ms, 0 < m.toNat)
    (hco : (ms.map toNat).Pairwise Nat.Coprime)
    (hlen : ms.length ≤ ns.length) {x : ℕ}
    (hlt : x < (ms.map toNat).prod)
    (hx : ∀ p ∈ ms.zip ns, x ≡ p.2.toNat [MOD p.1.toNat]) :
    x = (garner ms ns).toNat := by
  rw [toNat_garner ms ns hpos hco]
  refine CP.eq_garner_of_modEq _ _ (by simpa using hpos) hco
    (by simpa using hlen) hlt ?_
  intro q hq
  rw [List.zip_map, List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact hx p hp

end AzNat

end Azurite
