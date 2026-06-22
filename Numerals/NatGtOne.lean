/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

namespace NumeralAux

def NatGtOne := { n : Nat // 1 < n}

def n : NatGtOne := ⟨2, by decide⟩

end NumeralAux
