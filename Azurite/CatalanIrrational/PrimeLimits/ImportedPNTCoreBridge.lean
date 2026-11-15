/-
Copyright © 2026 Mikhail Hogrefe

Uses code adopted from the OpenAI mathematics repository (<https://github.com/openai/math>,
commit 4eaee87,
`lean/OAI/NumberTheory/Catalan/PrimeLimits/ImportedPNTCoreBridge.lean`),
licensed under the Apache License, Version 2.0.

     Copyright © 2026 OpenAI

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Azurite.CatalanIrrational.PNT.Catalan.Consequences

namespace OAI


noncomputable section
namespace Zeta5.W12.ImportedPNTCoreBridge
open Filter Asymptotics
open scoped Topology BigOperators

theorem psi_eq_actual_vonMangoldt_sum (R : ℝ) :
    Chebyshev.psi R =
      ∑ n ∈ Finset.Ioc 0 ⌊R⌋₊, ArithmeticFunction.vonMangoldt n := rfl

theorem theta_eq_actual_primeLog_sum (R : ℝ) :
    Chebyshev.theta R =
      ∑ p ∈ Finset.Ioc 0 ⌊R⌋₊ with p.Prime, Real.log (p : ℝ) := rfl

theorem ratio_tendsto_one_of_isEquivalent_id (f : ℝ → ℝ)
    (h : Asymptotics.IsEquivalent atTop f (fun R : ℝ => R)) :
    Tendsto (fun R : ℝ => f R / R) atTop (𝓝 1) := by
  exact (Asymptotics.isEquivalent_iff_tendsto_one
    (u := f) (v := fun R : ℝ => R) (eventually_ne_atTop (0 : ℝ))).mp h

theorem psi_ratio_tendsto_one :
    Tendsto (fun R : ℝ => Chebyshev.psi R / R) atTop (𝓝 1) :=
  ratio_tendsto_one_of_isEquivalent_id Chebyshev.psi CatalanPNT.WeakPNT''

theorem theta_ratio_tendsto_one :
    Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1) :=
  ratio_tendsto_one_of_isEquivalent_id Chebyshev.theta CatalanPNT.chebyshev_asymptotic

theorem primeLog_sum_ratio_tendsto_one :
    Tendsto (fun R : ℝ =>
      (∑ p ∈ Finset.Ioc 0 ⌊R⌋₊ with p.Prime, Real.log (p : ℝ)) / R)
      atTop (𝓝 1) := theta_ratio_tendsto_one

end Zeta5.W12.ImportedPNTCoreBridge

end

end OAI
