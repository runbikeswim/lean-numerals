/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

namespace NumeralAux

def NatGtOne := { n : Nat // 1 < n}

abbrev base2 : NatGtOne := ⟨2, by decide⟩
abbrev base8 : NatGtOne := ⟨8, by decide⟩
abbrev base10 : NatGtOne := ⟨10, by decide⟩
abbrev base16 : NatGtOne := ⟨16, by decide⟩

end NumeralAux
