/-
Copyright (c) 2025 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Lemmas

set_option linter.all true
/-
TODO: remove and resolve
-/
set_option linter.missingDocs false

/-!
# Numerals

`Numeral` provides theorems and algorithms for the representation of natural numbers in a
[positional numeral system](https://en.wikipedia.org/wiki/List_of_numeral_systems#Standard_positional_numeral_systems)
for an arbitrary basis larger than one.
-/

section Numerals

/--
`Numeral` provides a representation of a natural number in positional notation for `base`, with `digits`
in _reverse_ (little-endian) order. `base` can be any number larger than one, which is ensured by `baseGtOne`.
`allDigitsLtBase` asserts that every digit is less than `base`.
Via `noTrailingZero`, it is ensured that there are no trailing zeros. By this, every natural
number has a unique representation for the given `base`.
`0` can be represented in two ways: either digits equals`[]` or `[0]`, which is independent of `base`
-/
structure Numeral (base : Nat) (hb : 1 < base) where
  digits : List Nat
  allDigitsLtBase : allDigitsLtBase digits base
  noTrailingZero : noTrailingZero digits
  deriving Repr

/--
Numbers in binary representation
-/
abbrev Numeral2 := Numeral 2 (by decide)

/--
Numbers in octal representation
-/
abbrev Numeral8 := Numeral 8 (by decide)

/--
Numbers in decimal representation
-/
abbrev Numeral10 := Numeral 10 (by decide)

/--
Numbers in hexadecimal representation
-/
abbrev Numeral16 := Numeral 16 (by decide)

namespace Numeral

section Base

/--
returns the base of the provided numeral
-/
def base {base' : Nat} {hb' : 1 < base'} (_ : Numeral base' hb') : Nat := base'

end Base

section IsZero

/--
covers the two representations of zero as `Numeral`
-/
def isZero {base : Nat} {hb : 1 < base} (a : Numeral base hb) : Prop := isZeroAux a.digits

/--
makes `isZero` decidable
-/
def decIsZero {base : Nat} {hb : 1 < base} (a : Numeral base hb) : Decidable a.isZero := decIsZeroAux a.digits

/--
instance of class `Decidable` for `isZero`
-/
instance instIsZeroNumeral {base : Nat} {hb : 1 < base} (a : Numeral base hb) : Decidable (isZero a) := decIsZero a

end IsZero

section toNat

/-- -/
def toNat {base : Nat} {hb : 1 < base} (n : Numeral base hb) : Nat := toNatAux n.digits base

/-- -/
theorem toNat_eq_zero_iff {base : Nat} {hb : 1 < base} (n : Numeral base hb) :
  toNat n = 0 ↔ n.isZero := by
  unfold toNat isZero
  exact toNatAux_eq_zero_iff_isZeroAux hb

end toNat

section OfNat

/-- -/
def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : Numeral base hb where
  digits := ofNatAux n base hb
  allDigitsLtBase := allDigitsLtBase_prune
  noTrailingZero := noTrailingZero_prune_of_noTrailingZero noTrailingZero_nil


theorem ofNat_isZero_iff {n base : Nat} (hb : 1 < base) :
  (ofNat n base hb).isZero ↔ n = 0 := by
  simp only [isZero, ofNat]
  exact isZeroAux_ofNatAux_iff_eq_zero hb

/-- -/
theorem toNat_leftInverse_ofNat {n base : Nat} {hb : 1 < base} : toNat (ofNat n base hb) = n := by
  rw [toNat, ofNat, toNatAux_prune_eq_add_toNatAux, toNatAux_nil_eq, Nat.add_zero]

end OfNat

section Default

/-
zero (represented as `[]`) is the default `Numeral` - for any base
-/
instance instInhabitedNumeral {base : Nat} {hb : 1 < base} : Inhabited (Numeral base hb) := ⟨{
    digits := [],
    allDigitsLtBase := List.all_nil,
    noTrailingZero := noTrailingZero_nil
  }⟩

end Default

section ToString

/--
For base 2, 8, 10 or 16, the [binary](https://en.wikipedia.org/wiki/Binary_number),
[octal](https://en.wikipedia.org/wiki/Octal) or [hexadecimal](https://en.wikipedia.org/wiki/Hexadecimal)
representation of `n` is returned in the format that Lean uses for binary, octal, decimal or hexadecimal
constants.

For all other values of base, the list of digits - starting with the most significant - is
returned as sequence of natural numbers, separated by "," and succeeded by the
the value of `base` (all in decimal notation).
-/
def toString {base : Nat} {hb : 1 < base} (n : Numeral base hb) : String :=
  toStringAux n.digits base n.allDigitsLtBase

instance instToStringNumeral {base : Nat} {hb : 1 < base} : ToString (Numeral base hb) := ⟨toString⟩

end ToString

section Rebase

/-- -/
def rebase {base : Nat} {hb : 1 < base} (n : Numeral base hb) (toBase : Nat) (htb : 1 < toBase) : Numeral toBase htb :=
  ofNat (n.toNat) toBase htb

@[simp]
theorem rebase_base_eq_toBase {base : Nat} {hb : 1 < base} (n : Numeral base hb) (toBase : Nat) (htb : 1 < toBase) :
  (rebase n toBase htb).base = toBase := by
  unfold rebase ofNat toNat
  rfl

end Rebase

section Add

/-- -/
def hAdd {base : Nat} {hb : 1 < base} (a b : Numeral base hb) : Numeral base hb where
  digits := addAux a.digits b.digits 0 base hb
  allDigitsLtBase := allDigitsLtBase_addAux 0
  noTrailingZero := noTrailingZero_addAux_of a.noTrailingZero b.noTrailingZero hb

/-- -/
theorem hAdd_nil_iff_and_nil_nil {base : Nat} {hb : 1 < base} {a b : Numeral base hb}  :
  (hAdd a b).digits = [] ↔ a.digits = [] ∧ b.digits = [] := by
  unfold hAdd
  simp only [addAux_eq_nil_iff, true_and]

/-- -/
theorem hAdd_comm {base : Nat} {hb : 1 < base} (a b : Numeral base hb) : hAdd a b = hAdd b a := by
  unfold hAdd
  simp only [addAux_comm hb]

/-- -/
instance instCommutativeHAddNumerals {base : Nat} {hb : 1 < base} : Std.Commutative (α := Numeral base hb) hAdd :=
  ⟨hAdd_comm⟩

instance instHAddNumerals {base : Nat} {hb : 1 < base} : HAdd (Numeral base hb) (Numeral base hb) (Numeral base hb) := ⟨hAdd⟩

/-- -/
theorem toNat_add_left_distrib {base : Nat} {hb : 1 < base} {a b : Numeral base hb} :
  toNat (hAdd a b) = a.toNat + b.toNat := by
  unfold toNat hAdd
  simp only []
  exact toNatAux_addAux_left_distrib

end Add

end Numeral
end Numerals
