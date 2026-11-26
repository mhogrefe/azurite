/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.CertTool

/-!
# `lake exe ecpp_cert <pari|flint> <file>`

Elliptic curve primality certificates in the formats for exchange; see
`Azurite/ECPP/CertTool.lean`.
-/

def main (args : List String) : IO UInt32 := Azurite.ECPP.certMain args
