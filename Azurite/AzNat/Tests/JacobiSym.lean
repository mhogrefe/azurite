/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.JacobiSym
import Azurite.AzNat.ParseBase

namespace Azurite.AzNat

/-! `#guard` tests for the `AzNat` Jacobi symbol on multi-limb inputs. -/

-- 2^127 − 1 is prime and ≡ 7 (mod 8): (2 / M127) = 1; 3 is a nonresidue mod M127
#guard jacobi (ofNat 2) (AzNat.parse "170141183460469231731687303715884105727").get! = 1
#guard jacobi (ofNat 3) (AzNat.parse "170141183460469231731687303715884105727").get! = -1
-- a prime ≡ 5 (mod 8) around 2^89: (2/p) = −1 (p = 2^89 − 1 is a Mersenne prime ≡ 7 mod 8 so use it: (2/p) = 1)
#guard jacobi (ofNat 2) (AzNat.parse "618970019642690137449562111").get! = 1
-- the paper's 247-digit prime: n ≡ 1 (mod 4) with u = 0, the (c1) discriminant 4a; (−1/n) = 1
#guard jacobi (AzNat.parse "3876504335317997501469391035319109708663589625180623029822890926723711514115245155566479256098717968310496836053912513303910310541847025911281558587559700056356937703949226241396723616837470247248135048208451745439902122005282381436679587515252272").get!
  (AzNat.parse "3876504335317997501469391035319109708663589625180623029822890926723711514115245155566479256098717968310496836053912513303910310541847025911281558587559700056356937703949226241396723616837470247248135048208451745439902122005282381436679587515252273").get! = 1
-- squares are residues; a multiple of the modulus gives 0
#guard jacobi (AzNat.parse "1524157875019052100").get! (AzNat.parse "170141183460469231731687303715884105727").get! = 1
#guard jacobi (AzNat.parse "340282366920938463463374607431768211454").get! (AzNat.parse "170141183460469231731687303715884105727").get! = 0
-- small cross-check against the ℕ reference on a grid of odd moduli
#guard (List.range 40).all fun a => (List.range 30).all fun k =>
  jacobi (ofNat a) (ofNat (2 * k + 1)) = jacobiNat a (2 * k + 1)

end Azurite.AzNat
