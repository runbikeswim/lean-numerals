/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.NoTrailingZero
import Numerals.Prune

namespace NumeralAux

section OfNatAux

abbrev ofNatAux (n : Nat) (base : Nat) (hb : 1 < base) := prune [] n base hb

theorem isZeroAux_ofNatAux_iff_eq_zero {n base : Nat} (hb : 1 < base) :
  isZeroAux (ofNatAux n base hb) ↔ n = 0 := by
  constructor
  · intro h
    simp only [ofNatAux] at h
    have h1 : noTrailingZero (prune [] n base hb) := noTrailingZero_prune_nil
    have h2 : (prune [] n base hb) = [] := (isZeroAux_iff_eq_nil_of_noTrailingZero h1).mp h
    exact ((prune_eq_nil_iff_eq_nil_and_eq_zero hb).mp h2).right
  · intro h
    simp only [h, ofNatAux, prune, isZeroAux, equivAux]

end OfNatAux

end NumeralAux
