/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.LinearAlgebra.SModEq.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime

/-!
# BPR §4.4 (Polynomial Ideals) — preliminary definitions

The opening definitions of BPR §4.4 are all provided by Mathlib; this module collects the
relevant declarations (and anchors them in the Azurite import graph for the blueprint):

* an **ideal** `I` of a (commutative) ring `A` is `Ideal A` — a subset containing `0`, closed
  under addition (`Ideal.add_mem`) and under multiplication by any element of `A`
  (`Ideal.mul_mem_left`);
* **congruence modulo `I`**, written `a ≡ b [SMOD I]`, is `SModEq I`, characterized by
  `SModEq.sub_mem : a ≡ b [SMOD I] ↔ a - b ∈ I`;
* congruence modulo `I` is compatible with the ring operations: `SModEq.add` for addition and
  `SModEq.mul` for multiplication — the latter being exactly BPR's identity
  `a₁ a₂ - b₁ b₂ = a₁ (a₂ - b₂) + b₂ (a₁ - b₁) ∈ I`;
* the **quotient ring** `A / I` is `A ⧸ I` with ring structure `Ideal.Quotient.commRing`; the
  natural surjection sending an element to its class is the ring homomorphism
  `Ideal.Quotient.mk I : A →+* A ⧸ I` (so the sum/product of two classes is the class of the
  sum/product of representatives — `map_add`/`map_mul` — i.e. the operations are well defined);
* the **radical** of `I` is `Ideal.radical I` (an `Ideal A`), with
  `Ideal.mem_radical_iff : a ∈ I.radical ↔ ∃ m, a ^ m ∈ I`;
* a **prime ideal** is `Ideal.IsPrime I`, with `Ideal.IsPrime.mem_or_mem`
  (`x * y ∈ I → x ∈ I ∨ y ∈ I`) and `Ideal.isPrime_iff` (Mathlib additionally requires
  `I ≠ ⊤`, the usual convention that a prime ideal is proper).
-/
