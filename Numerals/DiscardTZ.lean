/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Cons

namespace NumeralAux

section DiscardTZ

/-
returns a equivalent list without trailing zeros
-/
def discardTZAux (a : List Nat) :=
  match a with
  | [] => []
  | x::xs => consAux x (discardTZAux xs)

theorem discardTZAux_nil_eq_nil : discardTZAux [] = [] := by
  unfold discardTZAux
  rfl

theorem noTrailingZeroAux_discardTZAux {a : List Nat} :
  noTrailingZeroAux (discardTZAux a) := by
  induction a with
  | nil => simp only [discardTZAux_nil_eq_nil, noTrailingZeroAux_nil]
  | cons x xs ih =>
    unfold discardTZAux
    exact noTrailingZeroAux_consAux_of ih

/-
`discardTZAux` preserves `allDigitsLtBase`
-/
theorem allDigitsLtBase_discardTZAux {base: Nat} {a : List Nat} (ha : allDigitsLtBase a base) :
  allDigitsLtBase (discardTZAux a) base := by
  induction a with
  | nil => exact allDigitsLtBase_nil
  | cons x xs ih =>
    unfold discardTZAux
    have hx : x < base := (allDigitsLtBase_cons_iff.mp ha).left
    have hxs : allDigitsLtBase (discardTZAux xs) base := ih (allDigitsLtBase_cons_iff.mp ha).right
    exact allDigitsLtBase_consAux_of hx hxs

/-
the result of `discardTZAux` is equivalent (with respect to `equivAux`) to the input
-/
theorem equivAux_discardTZAux {a : List Nat} : equivAux (discardTZAux a) a := by
  induction a with
  | nil => simp only [discardTZAux, equivAux_refl]
  | cons x xs ih =>
    simp only [discardTZAux]
    exact equivAux_consAux_cons_of_equivAux ih

end DiscardTZ

end NumeralAux
