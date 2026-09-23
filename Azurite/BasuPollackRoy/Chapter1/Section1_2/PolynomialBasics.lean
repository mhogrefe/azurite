/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Section 1.2: Polynomial Basics

In this section, $C$ is an algebraically closed field, $D$ is a subring
of $C$, and $K$ is the quotient field of $D$.

The **degree** of a polynomial is defined in
`Mathlib.Algebra.Polynomial.Degree.Defs`:

```
def Polynomial.degree : Polynomial R → WithBot ℕ :=
  fun p ↦ p.support.max
```

The degree uses `WithBot ℕ`, so the zero polynomial has degree `⊥`
(minus infinity). There is also `natDegree`, which maps `⊥` to `0`:

```
def Polynomial.natDegree : Polynomial R → ℕ :=
  fun p ↦ WithBot.unbotD 0 p.degree
```

The **coefficient** of `X^n` in a polynomial is defined in
`Mathlib.Algebra.Polynomial.Basic`:

```
def Polynomial.coeff : Polynomial R → ℕ → R :=
  fun x ↦ match x with
  | { toFinsupp := p} => ⇑p
```

A polynomial is represented as a `Finsupp ℕ R` (a finitely-supported
function `ℕ → R`), so `coeff p n` is evaluation of that function at `n`.

The **leading coefficient** is defined in
`Mathlib.Algebra.Polynomial.Degree.Defs`:

```
def Polynomial.leadingCoeff : Polynomial R → R :=
  fun p ↦ p.coeff p.natDegree
```
-/
