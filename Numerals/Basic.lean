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

section Prenumerals

/--
`Prenumeral` provides a representation of a natural number in positional notation for `base`, with `digits`
in _reverse_ (little-endian) order. `base` can be any number larger than one.
`ltBase` asserts that every digit is less than `base`.

`Prenumeral`s can have leading zeros as in
```
def p : Prenumeral 10 (by decide) := {digits := [2, 1, 0], ltBase := by decide}

```
which represents the `12` in base ten.
-/
@[ext]
structure Prenumeral (base : Nat) (hb : 1 < base) where
  digits : List Nat
  ltBase : allDigitsLtBase digits base
  deriving Repr

/--
Prenumerals in binary representation
-/
abbrev Prenumeral2 := Prenumeral 2 (by decide)

/--
Prenumerals in octal representation
-/
abbrev Prenumeral8 := Prenumeral 8 (by decide)

/--
Prenumerals in decimal representation
-/
abbrev Prenumeral10 := Prenumeral 10 (by decide)

/--
Prenumerals in hexadecimal representation
-/
abbrev Prenumeral16 := Prenumeral 16 (by decide)

namespace Prenumeral

/--

Example:
```
def p : Prenumeral 10 (by decide) := ofList [1, 2, 3, 0] (by decide)
#eval p -- { digits := [1, 2, 3, 0], ltBase := _ }
```
-/
def ofList {base: Nat} {hb: 1 < base} (a: List Nat) (ha : allDigitsLtBase a base) : Prenumeral base hb where
  digits := a
  ltBase := ha

/--
returns the base of the provided `Prenumeral`
-/
def base {base' : Nat} {hb' : 1 < base'} (_ : Prenumeral base' hb') : Nat := base'

/--
`[]` (i.e. _zero_) is the default `Prenumeral` - for any base
-/
instance instInhabitedPrenumeral {base : Nat} {hb : 1 < base} : Inhabited (Prenumeral base hb) := ⟨{
    digits := [],
    ltBase := List.all_nil
  }⟩

section Equality

/--
asserts that two `Prenumeral`s are equal iff their lists of digits are equal
-/
theorem eq_iff_digits_eq {base : Nat} (hb : 1 < base) (a b : Prenumeral base hb) :
  a = b ↔ a.digits = b.digits := by
  constructor
  · intro h
    simp only [h]
  · intro h
    ext
    simp only [h]

/--
decidable equality
-/
def decEq {base : Nat} (hb : 1 < base) (a b : Prenumeral base hb) : Decidable (a = b) :=
  if h : a.digits = b.digits then
    isTrue ((eq_iff_digits_eq hb a b).mpr h)
  else
    have : a.digits ≠ b.digits → a ≠ b := (Classical.iff_iff_not_iff_not.mp (eq_iff_digits_eq hb a b)).mpr
    isFalse (this h)

instance instDecidableEqPrenumeral {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : Decidable (a = b) :=
  decEq hb a b

end Equality

section Equivalence

/--
two `Prenumeral` if the same `base` are `equiv`alent, if they only differ with respect to leading zeros.
-/
def equiv {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : Prop :=
  equivAux a.digits b.digits

/--
`equiv` is an `Equivalence` i.e. [equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation)

Example:
```
#check equivalence_equiv.refl -- ∀ (x : Prenumeral ?m.1 ?m.2), x.equiv x
#check equivalence_equiv.symm -- equiv ?m.5 ?m.6 → equiv ?m.6 ?m.5
#check equivalence_equiv.trans -- equiv ?m.5 ?m.6 → equiv ?m.6 ?m.7 → equiv ?m.5 ?m.7
```
-/
theorem equivalence_equiv {base: Nat} {hb : 1 < base} :
  Equivalence (equiv : (Prenumeral base hb) → (Prenumeral base hb) → Prop) :=
    ⟨
      by unfold equiv; exact fun _ ↦ equivAux_refl,
      by unfold equiv; intro a b hab; exact equivAux_symm hab,
      by unfold equiv; intro a b c hab hbc; exact equivAux_trans hab hbc
    ⟩

instance instHasEquivPrenumeral {base : Nat} {hb : 1 < base} : HasEquiv (Prenumeral base hb) := ⟨equiv⟩

example {base: Nat} {hb : 1 < base} (a : Prenumeral base hb) : a ≈ a := by
  exact equivalence_equiv.refl a

example {base: Nat} {hb : 1 < base} (a b : Prenumeral base hb) : a ≈ b → b ≈ a := by
  exact equivalence_equiv.symm

example {base: Nat} {hb : 1 < base} (a b c : Prenumeral base hb) : a ≈ b → b ≈ c → a ≈ c:= by
  exact equivalence_equiv.trans

example {base: Nat} {hb : 1 < base} (a b c : Prenumeral base hb) : a ≈ b → c ≈ b → a ≈ c:= by
  intro hab hcb
  have hbc : b ≈ c := equivalence_equiv.symm hcb
  exact equivalence_equiv.trans hab hbc

end Equivalence

section IsZero
/--
`True` if the given `Prenumeral` is `0`
-/
def isZero {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : Prop := isZeroAux a.digits

/--
makes `isZero` decidable
-/
def decIsZero {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : Decidable a.isZero := decIsZeroAux a.digits

/--
instance of class `Decidable` for `isZero`
-/
instance instIsZeroPrenumeral {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : Decidable (isZero a) :=
  decIsZero a

end IsZero

section TrainingZeros

/--
`True` if `a` has no trailing zeros

Examples:
```
#eval (⟨[], by decide⟩ : Prenumeral 10 (by decide)).hasNoTrailingZeros -- true
#eval (⟨[0], by decide⟩ : Prenumeral 10 (by decide)).hasNoTrailingZeros -- false
#eval (⟨[0,1,2], by decide⟩ : Prenumeral 10 (by decide)).hasNoTrailingZeros -- true
#eval (⟨[0,1,2,0], by decide⟩ : Prenumeral 10 (by decide)).hasNoTrailingZeros -- false
```
-/
def hasNoTrailingZeros {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : Prop :=
  noTrailingZero a.digits

def decHasNoTrailingZeros {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) :
  Decidable (a.hasNoTrailingZeros) :=
  if h : noTrailingZero a.digits then
    isTrue h
  else
    isFalse h

instance instDecHasNoTrailingZeros {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) :
  Decidable (a.hasNoTrailingZeros) := decHasNoTrailingZeros a

end TrainingZeros

section LessThanOrEqualTo

/--
[_less than or equal to_](https://en.wikipedia.org/w/index.php?title=Inequality_(mathematics)&oldid=1351959378)
for `Prenumeral`s

```
def a : Prenumeral10 := default
def b : Prenumeral10 := ⟨[1], by decide⟩
def c : Prenumeral10 := ⟨[1, 0], by decide⟩
#check a ≤ b -- Prop
#eval a ≤ b -- true
#eval b ≤ a -- false
#eval b ≤ c -- true
#eval c ≤ b -- true
```
-/
def le {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : Prop :=
  leAux a.digits b.digits

instance instLePrenumeral {base : Nat} {hb : 1 < base} : LE (Prenumeral base hb) := ⟨le⟩

/--
`le` is a [Preorder](https://en.wikipedia.org/wiki/Preorder), i.e. a
[reflexive](https://en.wikipedia.org/wiki/Reflexive_relation) and
[transitive](https://en.wikipedia.org/wiki/Transitive_relation) relation.

Since `equiv a b` does **not** imply `a = b` for `Prenumeral`s, `le` is not
[antisymmetric](https://en.wikipedia.org/wiki/Antisymmetric_relation) - but
almost (see `equivAux_iff_leAux_and_leAux`).
-/
instance instLePrenumeralIsPreorder {base : Nat} {hb : 1 < base} : Std.IsPreorder (Prenumeral base hb) :=
  ⟨
    by unfold instLePrenumeral le; intro _ ; exact leAux_refl,
    by unfold instLePrenumeral le; intro a b c; exact leAux_trans
  ⟩

def decLe {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : Decidable (a ≤ b) :=
  if h : leAux a.digits b.digits then
    isTrue h
  else
    isFalse h

instance DecidableLE {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) :
  Decidable (a ≤ b) := decLe a b

end LessThanOrEqualTo

section ToNat_OfNat

/--
returns the value (of type `Nat`) of the given `Prenumeral`

Examples:
```
#eval (⟨[], by decide⟩ : Prenumeral 10 (by decide)).toNat -- 0
#eval (⟨[0], by decide⟩ : Prenumeral 10 (by decide)).toNat -- 0
#eval (⟨[0,1,2], by decide⟩ : Prenumeral 10 (by decide)).toNat -- 210
#eval (⟨[0,1,2,0], by decide⟩ : Prenumeral 10 (by decide)).toNat -- 210
```
-/
def toNat {base : Nat} {hb : 1 < base} (n : Prenumeral base hb) : Nat := toNatAux n.digits base

theorem toNat_eq_zero_iff_isZero {base : Nat} {hb : 1 < base} (n : Prenumeral base hb) :
  n.toNat = 0 ↔ n.isZero := by
  unfold toNat isZero
  exact toNatAux_eq_zero_iff_isZeroAux hb

/--
returns a `Prenumeral` for the given number (of type `Nat`)

Examples:
```
#eval Prenumeral.ofNat 0 10 (by decide) -- { digits := [], ltBase := _ }
#eval Prenumeral.ofNat 10 2 (by decide) -- { digits := [0, 1, 0, 1], ltBase := _ }
#eval Prenumeral.ofNat (15 + 15 * 16) 16 (by decide) -- { digits := [15, 15], ltBase := _ }
```
-/
def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : Prenumeral base hb where
  digits := ofNatAux n base hb
  ltBase := allDigitsLtBase_prune

/--
`ofNat` returns a `Prenumeral` that `isZero` iff its input is `0`
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
For `Prenumerals` with trailing zeros, `ofNat` is not the left inverse of `toNat`, since
trailing zeros are not preserved by `toNat`. The following example shows this for a very
simple case.
-/
example : ∃ p : Prenumeral10, (ofNat (p.toNat) 10 (by decide)) ≠ p := by
  let p : Prenumeral10 := ⟨[0], by decide⟩
  let q : Prenumeral10 := ⟨[], by decide⟩
  refine ⟨p, ?_⟩
  have : p.toNat = 0 := by decide
  rw [this]
  have : ofNat 0 10 (by decide) = q := by simp only [ofNat, ofNatAux, prune]; grind only
  rw [this]
  decide

end ToNat_OfNat

section Rebase

/--
returns a `Prenumeral` with the same value as the input but for a different `base`
-/
def rebase {base : Nat} {hb : 1 < base} (n : Prenumeral base hb) (toBase : Nat) (htb : 1 < toBase) :
  Prenumeral toBase htb := ofNat (n.toNat) toBase htb

/--
asserts that the result of `rebase` is a `Prenumeral` with `base` `toBase`
-/
theorem rebase_base_eq_toBase {base : Nat} {hb : 1 < base}
  (n : Prenumeral base hb) (toBase : Nat) (htb : 1 < toBase) :
  (rebase n toBase htb).base = toBase := by
  unfold rebase ofNat Prenumeral.toNat
  rfl

end Rebase

section Add

def hAdd {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : Prenumeral base hb where
  digits := addAux a.digits b.digits 0 base hb
  ltBase := allDigitsLtBase_addAux 0

instance instHAddPrenumerals {base : Nat} {hb : 1 < base} :
  HAdd (Prenumeral base hb) (Prenumeral base hb) (Prenumeral base hb) := ⟨hAdd⟩

/--
useful with `rw`-tactics
-/
theorem add_eq_hAdd  {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : a + b = a.hAdd b := rfl

/--
addition on `Prenumerals` is [commutative](https://en.wikipedia.org/wiki/Commutative_property)
-/
theorem add_comm {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) :
  a + b = b + a := by
  simp only [add_eq_hAdd, hAdd, addAux_comm hb]

instance instCommutativeHAddPrenumerals {base : Nat} {hb : 1 < base} :
  Std.Commutative (α := Prenumeral base hb) hAdd := ⟨add_comm⟩

theorem toNat_add_left_distrib {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) :
  (a + b).toNat = a.toNat + b.toNat := by
  simp only [add_eq_hAdd, Prenumeral.toNat, hAdd, toNatAux_addAux_left_distrib]

/--
the sum of two `Prenumeral`s `isZero` iff `isZero` holds for both of them
-/
theorem add_isZero_iff_isZero_and_isZero {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) :
  (a + b).isZero ↔ a.isZero ∧ b.isZero := by
  simp only [← toNat_eq_zero_iff_isZero, toNat_add_left_distrib]
  exact Nat.add_eq_zero_iff

end Add

end Prenumeral
end Prenumerals

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
def Prenumeral.toString {base : Nat} {hb : 1 < base} (n : Prenumeral base hb) : String :=
  toStringAux n.digits base n.ltBase

instance instToStringPrenumeral {base : Nat} {hb : 1 < base} : ToString (Prenumeral base hb) where
  toString := Prenumeral.toString

end ToString

section Numerals

/--
`Numeral` are `Prenumerals` without leading zeros, which is ensured by `noTrailingZero`.
By this, every natural number has a unique representation for the given `base`.
-/
@[ext]
structure Numeral (base : Nat) (hb : 1 < base) extends Prenumeral base hb where
  noTrailingZero : noTrailingZero digits
  deriving Repr

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

/--
Coercion of a `Numeral` into a `Prenumeral`.
-/
@[coe]
def toPrenumeral {base : Nat} {hb : 1 < base} (n : Numeral base hb) : Prenumeral base hb :=
  {digits := n.digits, ltBase := n.ltBase}

namespace Numeral

instance {base : Nat} {hb : 1 < base} : Coe (Numeral base hb) (Prenumeral base hb) where
  coe := toPrenumeral

/--
Converts a `Prenumeral` into a `toNumeral` by discarding (potentially present) trailing zeros.

Examples:
```
def p : Prenumeral 10 (by decide) := ⟨[1,9,0], by  decide⟩
#eval p -- { digits := [1, 9, 0], ltBase := _ }

def n : Numeral 10 (by decide) := p.toNumeral
#eval n -- { toPrenumeral := { digits := [1, 9], ltBase := _ }, noTrailingZero := _ }

def q : Prenumeral 10 (by decide) := n.toPrenumeral
#eval q -- { digits := [1, 9], ltBase := _ }

def r : Prenumeral 10 (by decide) := n
#eval r -- { digits := [1, 9], ltBase := _ }
```
-/
def Prenumeral.toNumeral {base : Nat} {hb : 1 < base} (p : Prenumeral base hb) :
  Numeral base hb where
  digits := discardTrailingZeros p.digits
  ltBase := allDigitsLtBase_discardTrailingZeros p.ltBase
  noTrailingZero :=  noTrailingZero_discardTrailingZeros

/-
zero (represented by `[]`) is the default `Numeral` - for any base
-/
instance instInhabitedNumeral {base : Nat} {hb : 1 < base} : Inhabited (Numeral base hb) := ⟨{
    toPrenumeral := default,
    noTrailingZero := noTrailingZero_nil
  }⟩

instance instToStringNumeral {base : Nat} {hb : 1 < base} : ToString (Numeral base hb) where
  toString := fun n => n.toPrenumeral.toString

def n : Numeral10 := ⟨⟨[1,2,3], by decide⟩, by decide⟩

#eval n

/--
provides the number of digits used by the given `Numeral`
-/
def length {base : Nat} {hb : 1 < base} (n : Numeral base hb) : Nat := n.digits.length

def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : Numeral base hb where
  toPrenumeral := Prenumeral.ofNat n base hb
  noTrailingZero := noTrailingZero_prune_of_noTrailingZero noTrailingZero_nil

section Add

/-- -/
def hAdd {base : Nat} {hb : 1 < base} (a b : Numeral base hb) : Numeral base hb where
  toPrenumeral := a + b
  noTrailingZero := noTrailingZero_addAux_of a.noTrailingZero b.noTrailingZero hb

instance instHAddNumerals {base : Nat} {hb : 1 < base} :
  HAdd (Numeral base hb) (Numeral base hb) (Numeral base hb) := ⟨hAdd⟩

theorem add_eq_hAdd {base : Nat} {hb : 1 < base} (a b : Numeral base hb) : a + b = a.hAdd b := rfl

theorem toPrenumeral_add_distrib {base : Nat} {hb : 1 < base} (a b : Numeral base hb) :
  (a + b).toPrenumeral = a.toPrenumeral + b.toPrenumeral := rfl

theorem add_comm {base : Nat} {hb : 1 < base} (a b : Numeral base hb) :
  a + b = b + a := by
  simp only [add_eq_hAdd, hAdd, Prenumeral.add_comm]

instance instCommutativeHAddNumerals {base : Nat} {hb : 1 < base} :
  Std.Commutative (α := Numeral base hb) hAdd := ⟨add_comm⟩

/-
theorem toNat_add_left_distrib {base : Nat} {hb : 1 < base} {a b : Prenumeral base hb} :
  (a.hAdd b).toNat = a.toNat + b.toNat := by
  unfold Prenumeral.toNat hAdd
  simp only []
  exact toNatAux_addAux_left_distrib
-/

end Add

section Sub

end Sub

end Numeral
end Numerals
