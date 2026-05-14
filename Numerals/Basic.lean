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
@[ext]
structure PreNumeral (base : Nat) (hb : 1 < base) where
  digits : List Nat
  allDigitsLtBase : allDigitsLtBase digits base
  deriving Repr

/--
PreNumerals in binary representation
-/
abbrev PreNumeral2 := PreNumeral 2 (by decide)

/--
PreNumerals in octal representation
-/
abbrev PreNumeral8 := PreNumeral 8 (by decide)

/--
PreNumerals in decimal representation
-/
abbrev PreNumeral10 := PreNumeral 10 (by decide)

/--
PreNumerals in hexadecimal representation
-/
abbrev PreNumeral16 := PreNumeral 16 (by decide)

namespace PreNumeral

/--
`[]` (i.e. _zero_) is the default `PreNumeral` - for any base
-/
instance instInhabitedPreNumeral {base : Nat} {hb : 1 < base} : Inhabited (PreNumeral base hb) := ⟨{
    digits := [],
    allDigitsLtBase := List.all_nil
  }⟩

theorem eq_iff_digits_eq {base : Nat} (hb : 1 < base) (a b : PreNumeral base hb) :
  a = b ↔ a.digits = b.digits := by
  constructor
  · intro h
    simp only [h]
  · intro h
    ext
    simp only [h]

def decEq {base : Nat} (hb : 1 < base) (a b : PreNumeral base hb) : Decidable (a = b) :=
  if h : a.digits = b.digits then
    isTrue ((eq_iff_digits_eq hb a b).mpr h)
  else
    have : a.digits ≠ b.digits → a ≠ b := (Classical.iff_iff_not_iff_not.mp (eq_iff_digits_eq hb a b)).mpr
    isFalse (this h)

instance instDecidableEqPreNumeral {base : Nat} {hb : 1 < base} (a b : PreNumeral base hb) : Decidable (a = b) :=
  decEq hb a b

/--
returns the base of the provided numeral
-/
def base {base' : Nat} {hb' : 1 < base'} (_ : PreNumeral base' hb') : Nat := base'

section IsZero
/--
`True` if the given `PreNumeral` is `0`
-/
def isZero {base : Nat} {hb : 1 < base} (a : PreNumeral base hb) : Prop := isZeroAux a.digits

/--
makes `isZero` decidable
-/
def decIsZero {base : Nat} {hb : 1 < base} (a : PreNumeral base hb) : Decidable a.isZero := decIsZeroAux a.digits

/--
instance of class `Decidable` for `isZero`
-/
instance instIsZeroPreNumeral {base : Nat} {hb : 1 < base} (a : PreNumeral base hb) : Decidable (isZero a) :=
  decIsZero a

end IsZero

/--
`True` if `a` has no trailing zeros

Examples:
```
#eval (⟨[], by decide⟩ : PreNumeral 10 (by decide)).hasNoTrailingZeros -- true
#eval (⟨[0], by decide⟩ : PreNumeral 10 (by decide)).hasNoTrailingZeros -- false
#eval (⟨[0,1,2], by decide⟩ : PreNumeral 10 (by decide)).hasNoTrailingZeros -- true
#eval (⟨[0,1,2,0], by decide⟩ : PreNumeral 10 (by decide)).hasNoTrailingZeros -- false
```
-/
def hasNoTrailingZeros {base : Nat} {hb : 1 < base} (a : PreNumeral base hb) : Prop :=
  noTrailingZero a.digits

def decHasNoTrailingZeros {base : Nat} {hb : 1 < base} (a : PreNumeral base hb) :
  Decidable (a.hasNoTrailingZeros) :=
  if h : noTrailingZero a.digits then
    isTrue h
  else
    isFalse h

instance instHasNoTrailingZeros {base : Nat} {hb : 1 < base} (a : PreNumeral base hb) :
  Decidable (a.hasNoTrailingZeros) := decHasNoTrailingZeros a

section ToNat_OfNat

/--
returns the value (of type `Nat`) of the given `PreNumeral`

Examples:
```
#eval (⟨[], by decide⟩ : PreNumeral 10 (by decide)).toNat -- 0
#eval (⟨[0], by decide⟩ : PreNumeral 10 (by decide)).toNat -- 0
#eval (⟨[0,1,2], by decide⟩ : PreNumeral 10 (by decide)).toNat -- 210
#eval (⟨[0,1,2,0], by decide⟩ : PreNumeral 10 (by decide)).toNat -- 210
```
-/
def toNat {base : Nat} {hb : 1 < base} (n : PreNumeral base hb) : Nat := toNatAux n.digits base

theorem toNat_eq_zero_iff {base : Nat} {hb : 1 < base} (n : PreNumeral base hb) :
  toNat n = 0 ↔ n.isZero := by
  unfold toNat isZero
  exact toNatAux_eq_zero_iff_isZeroAux hb

/--
returns a `PreNumeral` for the given number (of type `Nat`)

Examples:
```
#eval PreNumeral.ofNat 0 10 (by decide) -- { digits := [], allDigitsLtBase := _ }
#eval PreNumeral.ofNat 10 2 (by decide) -- { digits := [0, 1, 0, 1], allDigitsLtBase := _ }
#eval PreNumeral.ofNat (15 + 15 * 16) 16 (by decide) -- { digits := [15, 15], allDigitsLtBase := _ }
```
-/
def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : PreNumeral base hb where
  digits := ofNatAux n base hb
  allDigitsLtBase := allDigitsLtBase_prune

/--
`ofNat` returns a `PreNumeral` that `isZero` iff its input is `0`
-/
theorem ofNat_isZero_iff {n base : Nat} (hb : 1 < base) :
  (ofNat n base hb).isZero ↔ n = 0 := by
  simp only [isZero, ofNat]
  exact isZeroAux_ofNatAux_iff_eq_zero hb

/--
`toNat` is the inverse of `ofNat`
-/
theorem toNat_leftInverse_ofNat {n base : Nat} {hb : 1 < base} : (ofNat n base hb).toNat = n := by
  rw [toNat, ofNat, toNatAux_prune_eq_add_toNatAux, toNatAux_nil_eq, Nat.add_zero]

/--
For `PreNumerals` with trailing zeros, the `ofNat` is not the left inverse of `toNat`, since
trailing zeros are removed by applying `toNat`. The following example shows this for a very
simple case.
-/
example : ∃ p : PreNumeral10, (ofNat (p.toNat) 10 (by decide)) ≠ p := by
  let p : PreNumeral10 := ⟨[0], by decide⟩
  let q : PreNumeral10 := ⟨[], by decide⟩
  refine ⟨p, ?_⟩
  have : p.toNat = 0 := by decide
  rw [this]
  have : ofNat 0 10 (by decide) = q := by simp only [ofNat, ofNatAux, prune]; grind only
  rw [this]
  decide

end ToNat_OfNat

section Rebase

/--
returns a `PreNumeral` with the same value as the input but for a different `base`
-/
def rebase {base : Nat} {hb : 1 < base} (n : PreNumeral base hb) (toBase : Nat) (htb : 1 < toBase) :
  PreNumeral toBase htb := ofNat (n.toNat) toBase htb

/--
asserts that the result of `rebase` is a `PreNumeral` with `base` `toBase`
-/
theorem rebase_base_eq_toBase {base : Nat} {hb : 1 < base}
  (n : PreNumeral base hb) (toBase : Nat) (htb : 1 < toBase) :
  (rebase n toBase htb).base = toBase := by
  unfold rebase ofNat PreNumeral.toNat
  rfl

end Rebase

section Add

def hAdd {base : Nat} {hb : 1 < base} (a b : PreNumeral base hb) : PreNumeral base hb where
  digits := addAux a.digits b.digits 0 base hb
  allDigitsLtBase := allDigitsLtBase_addAux 0

instance instHAddPreNumerals {base : Nat} {hb : 1 < base} :
  HAdd (PreNumeral base hb) (PreNumeral base hb) (PreNumeral base hb) := ⟨hAdd⟩

theorem add_eq_hAdd  {base : Nat} {hb : 1 < base} (a b : PreNumeral base hb) : a + b = a.hAdd b := rfl

/-- -/
theorem hAdd_nil_iff_and_nil_nil {base : Nat} {hb : 1 < base} (a b : PreNumeral base hb) :
  (a + b).digits = [] ↔ a.digits = [] ∧ b.digits = [] := by
  simp only [add_eq_hAdd, hAdd, addAux_eq_nil_iff, true_and]

/-- -/
theorem hAdd_comm {base : Nat} {hb : 1 < base} (a b : PreNumeral base hb) :
  a + b = b + a := by
  simp only [add_eq_hAdd, hAdd, addAux_comm hb]

/-- -/
instance instCommutativeHAddPreNumerals {base : Nat} {hb : 1 < base} :
  Std.Commutative (α := PreNumeral base hb) hAdd := ⟨hAdd_comm⟩

/-- -/
theorem toNat_add_left_distrib {base : Nat} {hb : 1 < base} (a b : PreNumeral base hb) :
  (a + b).toNat = a.toNat + b.toNat := by
  simp only [add_eq_hAdd, PreNumeral.toNat, hAdd, toNatAux_addAux_left_distrib]

end Add

end PreNumeral
end PreNumerals

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
def PreNumeral.toString {base : Nat} {hb : 1 < base} (n : PreNumeral base hb) : String :=
  toStringAux n.digits base n.allDigitsLtBase

instance instToStringPreNumeral {base : Nat} {hb : 1 < base} : ToString (PreNumeral base hb) where
  toString := PreNumeral.toString

end ToString

section Numerals

/--
`Numeral` are `PreNumerals` without leading zeros, which is ensured by `noTrailingZero`.
By this, every natural number has a unique representation for the given `base`.
-/
@[ext]
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

/-
zero (represented by `[]`) is the default `Numeral` - for any base
-/
instance instInhabitedNumeral {base : Nat} {hb : 1 < base} : Inhabited (Numeral base hb) := ⟨{
    toPreNumeral := default,
    noTrailingZero := noTrailingZero_nil
  }⟩

instance instToStringNumeral {base : Nat} {hb : 1 < base} : ToString (Numeral base hb) where
  toString := fun n => n.toPreNumeral.toString

/--
Numerals in binary representation
-/
abbrev Numeral2 := Numeral 2 (by decide)

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

def n : Numeral10 := ⟨⟨[1,2,3], by decide⟩, by decide⟩

#eval n

/--
provides the number of digits used by the given `Numeral`
-/
def length {base : Nat} {hb : 1 < base} (n : Numeral base hb) : Nat := n.digits.length

def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : Numeral base hb where
  toPreNumeral := PreNumeral.ofNat n base hb
  noTrailingZero := noTrailingZero_prune_of_noTrailingZero noTrailingZero_nil

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

section Add

/-- -/
def hAdd {base : Nat} {hb : 1 < base} (a b : Numeral base hb) : Numeral base hb where
  toPreNumeral := a + b
  noTrailingZero := noTrailingZero_addAux_of a.noTrailingZero b.noTrailingZero hb

instance instHAddNumerals {base : Nat} {hb : 1 < base} :
  HAdd (Numeral base hb) (Numeral base hb) (Numeral base hb) := ⟨hAdd⟩

theorem add_eq_hAdd {base : Nat} {hb : 1 < base} (a b : Numeral base hb) : a + b = a.hAdd b := rfl

theorem toPreNumeral_add_distrib {base : Nat} {hb : 1 < base} (a b : Numeral base hb) :
  (a + b).toPreNumeral = a.toPreNumeral + b.toPreNumeral := rfl

theorem hAdd_comm {base : Nat} {hb : 1 < base} (a b : Numeral base hb) :
  a + b = b + a := by
  sorry

/-
instance instCommutativeHAddNumerals {base : Nat} {hb : 1 < base} :
  Std.Commutative (α := Numeral base hb) hAdd := ⟨PreNumeral.hAdd_comm⟩
-/

/-
theorem toNat_add_left_distrib {base : Nat} {hb : 1 < base} {a b : PreNumeral base hb} :
  (a.hAdd b).toNat = a.toNat + b.toNat := by
  unfold PreNumeral.toNat hAdd
  simp only []
  exact toNatAux_addAux_left_distrib
-/

end Add

section Sub

end Sub

end Numeral
end Numerals
