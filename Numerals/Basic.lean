/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Lemmas

/-!
# Numerals.Basic

-/

set_option linter.all true
/-
TODO: remove and resolve
-/
set_option linter.missingDocs false

/-!
# Numerals

`Numeral` provides theorems and algorithms for the representation of natural numbers in a
[positional numeral system](https://en.wikipedia.org/wiki/List_of_numeral_systems#Standard_positional_numeral_systems)
for an arbitrary basis (i.e. any natural number larger than one).
-/

section PreNumerals

/--
`PreNumeral` provides a representation of a natural number in positional notation for `base`, with `digits`
in _reverse_ (little-endian) order. `base` can be any number larger than one.
`allDigitsLtBase` asserts that every digit is less than `base`.

`PreNumeral`s can have leading zeros as in
```
def p : PreNumeral 10 (by decide) := {digits := [2, 1, 0], allDigitsLtBase := by decide}

```
which represents the `12` in base ten.
-/
structure PreNumeral (base : Nat) (hb : 1 < base) where
  digits : List Nat
  allDigitsLtBase : allDigitsLtBase digits base
  deriving Repr

end PreNumerals

section Base

/--
returns the base of the provided numeral
-/
def PreNumeral.base {base' : Nat} {hb' : 1 < base'} (_ : PreNumeral base' hb') : Nat := base'

end Base

section Numerals

/--
`Numeral` are `PreNumerals` without leading zeros, which is ensured by `noTrailingZero`.
By this, every natural number has a unique representation for the given `base`.
-/
structure Numeral (base : Nat) (hb : 1 < base) extends PreNumeral base hb where
  noTrailingZero : noTrailingZero digits
  deriving Repr

/--
Coercion of a `Numeral` into a `PreNumeral`.
-/
@[coe]
def toPreNumeral {base : Nat} {hb : 1 < base} (n : Numeral base hb) : PreNumeral base hb :=
  {digits := n.digits, allDigitsLtBase := n.allDigitsLtBase}

instance {base : Nat} {hb : 1 < base} : Coe (Numeral base hb) (PreNumeral base hb) where
  coe := toPreNumeral

/--
Converts a `PreNumeral` into a `toNumeral` by discarding (potentially present) trailing zeros.

Examples:
```
def p : PreNumeral 10 (by decide) := ⟨[1,9,0], by  decide⟩
#eval p -- { digits := [1, 9, 0], allDigitsLtBase := _ }

def n : Numeral 10 (by decide) := p.toNumeral
#eval n -- { toPreNumeral := { digits := [1, 9], allDigitsLtBase := _ }, noTrailingZero := _ }

def q : PreNumeral 10 (by decide) := n.toPreNumeral
#eval q -- { digits := [1, 9], allDigitsLtBase := _ }

def r : PreNumeral 10 (by decide) := n
#eval r -- { digits := [1, 9], allDigitsLtBase := _ }
```
-/
def PreNumeral.toNumeral {base : Nat} {hb : 1 < base} (p : PreNumeral base hb) :
  Numeral base hb where
  digits := discardTrailingZeros p.digits
  allDigitsLtBase := allDigitsLtBase_discardTrailingZeros p.allDigitsLtBase
  noTrailingZero :=  noTrailingZero_discardTrailingZeros

/--
PreNumerals in binary representation
-/
abbrev PreNumeral2 := PreNumeral 2 (by decide)

/--
Numerals in binary representation
-/
abbrev Numeral2 := Numeral 2 (by decide)

/--
PreNumerals in octal representation
-/
abbrev PreNumeral8 := PreNumeral 8 (by decide)

/--
Numerals in octal representation
-/
abbrev Numeral8 := Numeral 8 (by decide)

/--
Numerals in decimal representation
-/
abbrev Numeral10 := Numeral 10 (by decide)

/--
Numerals in hexadecimal representation
-/
abbrev Numeral16 := Numeral 16 (by decide)

namespace Numeral

section Base

def base {base' : Nat} {hb' : 1 < base'} (n : Numeral base' hb') : Nat := (n : PreNumeral base' hb').base

end Base

section Length

/--
provides the number of digits used by the given numeral
-/
def length {base : Nat} {hb : 1 < base} (n : Numeral base hb) : Nat := n.digits.length

end Length

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

def digitToString (digit base : Nat) (hd : digit < base) : String :=
  if g : base = 16 ∧ 10 ≤ digit then
    /- needed for avoiding "Missing cases"-error in the following match -/
    have : decide (digit < 16) := by
      rw [g.left] at hd
      simp only [hd, decide_true]
    match digit with
    | 10 => "a"
    | 11 => "b"
    | 12 => "c"
    | 13 => "d"
    | 14 => "e"
    | 15 => "f"
  else
    s!"{digit}"

def toStringAux (digits : List Nat) (base : Nat) (ha : allDigitsLtBase digits base) : String:=
  let s := natsToStrings (digits : List Nat) (base : Nat) (ha : allDigitsLtBase digits base)
  let r := if s = [] then ["0"] else s.reverse
  match base with
  | 2 => s!"0b{String.join r}"
  | 8 => s!"0o{String.join r}"
  | 10 => s!"{ String.join r}"
  | 16 => s!"0x{String.join r}"
  | _ => s!"{",".intercalate r}({base})"
  where natsToStrings (digits : List Nat) (base : Nat) (ha : allDigitsLtBase digits base) : List String :=
    match digits with
    | [] => []
    | x::xs =>
      have hxs : x < base ∧ allDigitsLtBase xs base := allDigitsLtBase_cons_iff.mp ha
      (digitToString x base hxs.left)::(natsToStrings xs base hxs.right)

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

theorem rebase_base_eq_toBase {base : Nat} {hb : 1 < base} (n : Numeral base hb) (toBase : Nat) (htb : 1 < toBase) :
  (rebase n toBase htb).base = toBase := by
  unfold rebase ofNat toNat
  rfl

end Rebase

section LE



end LE


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

section Sub

end Sub

end Numeral
end Numerals
