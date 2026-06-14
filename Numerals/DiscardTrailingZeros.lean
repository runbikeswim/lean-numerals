/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Cons

namespace NumeralAux

section DiscardTrailingZeros

/--
returns a equivalent list without trailing zeros
-/
def discardTrailingZeros (a : List Nat) :=
  match a with
  | [] => []
  | x::xs => consAux x (discardTrailingZeros xs)

theorem discardTrailingZeros_nil_eq_nil : discardTrailingZeros [] = [] := by
  unfold discardTrailingZeros
  rfl

theorem noTrailingZero_discardTrailingZeros {a : List Nat} :
  noTrailingZero (discardTrailingZeros a) := by
  induction a with
  | nil => simp only [discardTrailingZeros_nil_eq_nil, noTrailingZero_nil]
  | cons x xs ih =>
    unfold discardTrailingZeros
    exact noTrailingZero_consAux_of ih

/--
`discardTrailingZeros` preserves `allDigitsLtBase`
-/
theorem allDigitsLtBase_discardTrailingZeros {base: Nat} {a : List Nat} (ha : allDigitsLtBase a base) :
  allDigitsLtBase (discardTrailingZeros a) base := by
  induction a with
  | nil => exact allDigitsLtBase_nil
  | cons x xs ih =>
    unfold discardTrailingZeros
    have hx : x < base := (allDigitsLtBase_cons_iff.mp ha).left
    have hxs : allDigitsLtBase (discardTrailingZeros xs) base := ih (allDigitsLtBase_cons_iff.mp ha).right
    exact allDigitsLtBase_consAux_of hx hxs

/--
the result of `discardTrailingZeros` is equivalent (with respect to `equivAux`) to the input
-/
theorem equivAux_discardTrailingZeros {a : List Nat} : equivAux (discardTrailingZeros a) a := by
  induction a with
  | nil => simp only [discardTrailingZeros, equivAux_refl]
  | cons x xs ih =>
    simp only [discardTrailingZeros]
    exact equivAux_consAux_cons_of_equivAux ih

end DiscardTrailingZeros

end NumeralAux
