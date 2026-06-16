/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.ToNat
import Numerals.EquivIsZero
import Numerals.AllDigitsBase
import Numerals.NoTrailingZero
import Numerals.DiscardTrailingZeros
import Numerals.ToNatEquiv
import Numerals.OfNat
import Numerals.Prune
import Numerals.LeLt
import Numerals.Add
import Numerals.Sub
import Numerals.ToOfString
import Numerals.ListFinBase

open NumeralAux

/-!
# Numerals.Basic

`Numeral.Basic` provides two types for the representation of natural numbers in a
[positional numeral system](https://en.wikipedia.org/wiki/List_of_numeral_systems#Standard_positional_numeral_systems)
for an arbitrary basis (i.e. any natural number larger than one):
* `Prenumeral` for which _leading_ - actually _trailing_  zeros are permitted, which means that there are multiple `equiv`alent
  representations of the same natural number and
* `Numeral`, which is a subtype of `Prenumeral` but without ambiguity in the representation

In particular, it provides non-primitive functions for basic operations such as `add`ition and `sub`traction
of numerals and theorems that ensure that these functions are consistent with the respective operations on
[`Nat`](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/#Nat).
This is useful for proofing theorems that refer to the representation of natural numbers as
numerals in positional notation.

## Prenumeral

## Numeral

-/

set_option linter.all true
/-
TODO: remove and resolve
-/
set_option linter.missingDocs false

section Prenumerals

/--
`Prenumeral` provides a representation of a natural number in positional notation for `base`, with `digits`
in _reverse_ (little-endian) order. `base` can be any natural number larger than one.
`ltBase` asserts that all natural numbers in list `digits` are less than `base`.

`Prenumeral`s can have leading zeros as in
```
def p : Prenumeral 10 (by decide) := {digits := [2, 1, 0], ltBase := by decide}

```
which represents the number `12` in base ten.
-/
@[ext]
structure Prenumeral (base : Nat) (hb : 1 < base) where
  digits : List Nat
  ltBase : allDigitsLtBase digits base
  deriving Repr

/--
shorthand for `Prenumeral`s in binary representation
-/
abbrev Prenumeral2 := Prenumeral 2 (by decide)

/--
shorthand for `Prenumeral`s octal representation
-/
abbrev Prenumeral8 := Prenumeral 8 (by decide)

/--
shorthand for `Prenumeral`s decimal representation
-/
abbrev Prenumeral10 := Prenumeral 10 (by decide)

/--
shorthand for `Prenumeral`s hexadecimal representation
-/
abbrev Prenumeral16 := Prenumeral 16 (by decide)

/--

Example:
```
def p : Prenumeral 10 (by decide) := [1, 2, 3, 0].toPrenumeral (by decide)
#eval p -- { digits := [1, 2, 3, 0], ltBase := _ }
```
-/
def List.toPrenumeral {base: Nat} {hb: 1 < base} (a: List Nat) (ha : allDigitsLtBase a base) : Prenumeral base hb where
  digits := a
  ltBase := ha

namespace Prenumeral

/--
returns the base of the provided `Prenumeral`
-/
def base {base' : Nat} {hb' : 1 < base'} (_ : Prenumeral base' hb') : Nat := base'

abbrev zero {base : Nat} {hb : 1 < base} : Prenumeral base hb := {digits := [], ltBase := List.all_nil}

/--
`[]` (i.e. _zero_) is the default `Prenumeral` - for any base
-/
instance instInhabited {base : Nat} {hb : 1 < base} : Inhabited (Prenumeral base hb) := ⟨zero⟩

theorem zero_eq_default {base : Nat} {hb : 1 < base} : @zero base hb = default := rfl

/--
use `0` for zero

Example:
```
#eval (0 : Prenumeral 10 (by decide)) -- { digits := [], ltBase := _ }
```
-/
instance instZero {base : Nat} {hb : 1 < base} : Zero (Prenumeral base hb) := ⟨default⟩

theorem zero_eq_zero {base : Nat} {hb : 1 < base} : @zero base hb = 0 := rfl

abbrev one {base : Nat} {hb : 1 < base} : Prenumeral base hb where
  digits := [1]
  ltBase := by simp only [allDigitsLtBase, List.all, Bool.and_true, hb, decide_true]

/--
use `1` for one

Example:
```
#eval (1 : Prenumeral 10 (by decide)) -- { digits := [1], ltBase := _ }
```
-/
instance instOne {base : Nat} {hb : 1 < base} : One (Prenumeral base hb) where
  one := one

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

instance instDecidableEq {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : Decidable (a = b) :=
  decEq hb a b

end Equality

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

theorem zero_toNat_eq_zero {base : Nat} {hb : 1 < base} : (@zero base hb).toNat = 0 := toNatAux_nil_eq

/--
returns a `Prenumeral` for the given number (of type `Nat`)

Examples:
```
#eval @Prenumeral.ofNat 0 10 (by decide) -- { digits := [], ltBase := _ }
#eval @Prenumeral.ofNat 11 2 (by decide) -- { digits := [1, 1, 0, 1], ltBase := _ }
#eval @Prenumeral.ofNat (15 + 16) 16 (by decide) -- { digits := [15, 1], ltBase := _ }
```
-/
def ofNat (n : Nat) {base : Nat} {hb : 1 < base} : Prenumeral base hb where
  digits := ofNatAux n base hb
  ltBase := allDigitsLtBase_prune

theorem ofNat_zero_eq_zero {base : Nat} {hb : 1 < base} : @ofNat 0 base hb = zero := by
  unfold ofNat ofNatAux prune zero
  rfl

theorem ofNat_one_eq_one {base : Nat} {hb : 1 < base} : @ofNat 1 base hb = one := by
  unfold ofNat ofNatAux prune one
  have h1 : 1 / base = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hb)
  have h2 : 1 % base = 1 := by
    rw [Nat.mod_eq]
    simp only [Nat.pos_of_one_lt hb, true_and, Nat.not_le_of_lt hb, reduceIte]
  simp only [Nat.zero_add, h1, prune_nil_eq_nil, h2]

instance instOfNat {base : Nat} {hb : 1 < base} (n : Nat) : OfNat (Prenumeral base hb) n where
  ofNat := ofNat n

/--
`toNat` is the inverse of `ofNat`
-/
theorem toNat_leftInverse_ofNat {n base : Nat} {hb : 1 < base} : (@ofNat n base hb).toNat = n := by
  rw [toNat, ofNat, toNatAux_prune_eq_add_toNatAux, toNatAux_nil_eq, Nat.add_zero]

/--
For `Prenumerals` with trailing zeros, `ofNat` is not the left inverse of `toNat`, since
trailing zeros are not preserved by `toNat`. The following example shows this for a very
simple case.
-/
example : ∃ p : Prenumeral10, ofNat (p.toNat) ≠ p := by
  let p : Prenumeral10 := ⟨[0], by decide⟩
  let q : Prenumeral10 := ⟨[], by decide⟩
  refine ⟨p, ?_⟩
  have : p.toNat = 0 := by decide
  rw [this]
  have : ofNat 0 = q := by simp only [ofNat, ofNatAux, prune]; grind only
  rw [this]
  decide

end ToNat_OfNat

section Equivalence

/--
two `Prenumeral` if the same `base` are `equiv`alent, if they only differ with respect to leading zeros.
-/
def equiv {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : Prop :=
  equivAux a.digits b.digits

theorem toNat_eq_iff_equiv {base: Nat} {hb : 1 < base} (a b : Prenumeral base hb) :
  a.toNat = b.toNat ↔ equiv a b := by
  unfold toNat equiv
  exact toNatAux_eq_iff_equivAux a.ltBase b.ltBase hb

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

instance instHasEquiv {base : Nat} {hb : 1 < base} : HasEquiv (Prenumeral base hb) := ⟨equiv⟩

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

theorem not_equiv_iff_not_equiv {base: Nat} {hb : 1 < base} (a b : Prenumeral base hb) :
  ¬ a ≈ b ↔ ¬ b ≈ a := by
  simp only [equiv]
  exact not_equivAux_iff_not_equivAux

end Equivalence

section IsZero
/--
`True` if the given `Prenumeral` is `0`
-/
def isZero {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : Prop := isZeroAux a.digits

theorem toNat_eq_zero_iff_isZero {base : Nat} {hb : 1 < base} (n : Prenumeral base hb) :
  n.toNat = 0 ↔ n.isZero := by
  unfold toNat isZero
  exact toNatAux_eq_zero_iff_isZeroAux hb

/--
`ofNat` returns a `Prenumeral` that `isZero` iff its input is `0`
-/
theorem ofNat_isZero_iff_eq_zero {n base : Nat} (hb : 1 < base) :
  (@ofNat n base hb).isZero ↔ n = 0 := by
  unfold isZero ofNat
  exact isZeroAux_ofNatAux_iff_eq_zero hb

example : (@ofNat 0 10 (by decide)).isZero := by rw [ofNat_isZero_iff_eq_zero]

/--
makes `isZero` decidable
-/
def decIsZero {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : Decidable a.isZero := decIsZeroAux a.digits

/--
instance of class `Decidable` for `isZero`
-/
instance instDecIsZero {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : Decidable (isZero a) :=
  decIsZero a

example : (0 : Prenumeral10).isZero := by native_decide

end IsZero

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

instance instLe {base : Nat} {hb : 1 < base} : LE (Prenumeral base hb) := ⟨le⟩

theorem le_iff_toNat_le_toNat {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) :
  a ≤ b ↔ a.toNat ≤ b.toNat := by
  simp only [LE.le, le, toNat]
  exact leAux_iff_toNatAux_le_toNatAux hb a.ltBase b.ltBase

/--
`le` is a [Preorder](https://en.wikipedia.org/wiki/Preorder), i.e. a
[reflexive](https://en.wikipedia.org/wiki/Reflexive_relation) and
[transitive](https://en.wikipedia.org/wiki/Transitive_relation) relation.

Since `equiv a b` does **not** imply `a = b` for `Prenumeral`s, `le` is not
[antisymmetric](https://en.wikipedia.org/wiki/Antisymmetric_relation) - but
almost (see `equivAux_iff_leAux_and_leAux`).
-/
instance instLeIsPreorder {base : Nat} {hb : 1 < base} : Std.IsPreorder (Prenumeral base hb) :=
  ⟨
    by unfold instLe le; intro _ ; exact leAux_refl,
    by unfold instLe le; intro a b c; exact leAux_trans
  ⟩

instance instLeIsLinearPreorder {base : Nat} {hb : 1 < base} : Std.IsLinearPreorder (Prenumeral base hb) :=
  ⟨
    by intro a b; simp only [LE.le, le]; exact leAux_total
  ⟩

instance instTransLe {base : Nat} {hb : 1 < base} :
  Trans (· ≤ ·) (· ≤ ·) (fun a : Prenumeral base hb ↦ fun b : Prenumeral base hb ↦ a ≤ b) where
  trans := @instLeIsPreorder.le_trans

theorem zero_le {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : 0 ≤ a := by
  unfold instOfNat
  simp only [ofNat_zero_eq_zero, LE.le, le]
  exact leAux_nil

example {base : Nat} {hb : 1 < base} : (0 : Prenumeral base hb) ≤ 1 := zero_le 1

def decLe {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : Decidable (a ≤ b) :=
  if h : leAux a.digits b.digits then
    isTrue h
  else
    isFalse h

instance instDecLe {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) :
  Decidable (a ≤ b) := decLe a b

example : @zero 10 (by decide) ≤ @one 10 (by decide) := by decide
example : (0 : Prenumeral10) ≤ 1 := by native_decide
example : (1966 : Prenumeral10) ≤ (2026 : Prenumeral10) := by native_decide

end LessThanOrEqualTo

section Min

/--
Example:
```
#eval min (0 : Prenumeral 10 (by decide)) 1 -- { digits := [], ltBase := _ }
```
-/
instance instMin {base : Nat} {hb : 1 < base} : Min (Prenumeral base hb) := minOfLe

instance instMinEqOr {base : Nat} {hb : 1 < base} : Std.MinEqOr (Prenumeral base hb) where
  min_eq_or := by
    intro a b
    by_cases h: a ≤ b <;> simp only [Min.min, h, reduceIte, or_true, true_or]

end Min

section Max

/--
Example:
```
#eval max (0 : Prenumeral 10 (by decide)) 1 -- { digits := [1], ltBase := _ }
```
-/
instance instMax {base : Nat} {hb : 1 < base} : Max (Prenumeral base hb) := maxOfLe

instance instMaxEqOr {base : Nat} {hb : 1 < base} : Std.MaxEqOr (Prenumeral base hb) where
  max_eq_or := by
    intro a b
    by_cases h: a ≤ b <;> simp only [Max.max, h, reduceIte, or_true, true_or]

end Max

section LessThan

def lt {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : Prop :=
  ltAux a.digits b.digits

instance instLt {base : Nat} {hb : 1 < base} : LT (Prenumeral base hb) := ⟨lt⟩

theorem lt_iff_toNat_lt_toNat {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) :
  a < b ↔ a.toNat < b.toNat := by
  simp only [LT.lt, lt, toNat]
  exact ltAux_iff_toNatAux_lt_toNatAux hb a.ltBase b.ltBase

theorem lt_iff_le_and_not_le {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) :
  a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  simp only [LT.lt, lt, LE.le, le]
  exact ltAux_iff_leAux_and_not_leAux

instance instLawfulOrderLT {base : Nat} {hb : 1 < base}  : Std.LawfulOrderLT (Prenumeral base hb) :=
  ⟨lt_iff_le_and_not_le⟩

theorem le_irrefl {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : ¬ a < a := by
  simp only [LT.lt, lt]
  exact ltAux_irrefl

theorem lt_asymm {base : Nat} {hb : 1 < base} {a b : Prenumeral base hb} (h: a < b) : ¬ b < a := by
  simp only [LT.lt, lt] at h ⊢
  exact ltAux_asymm h

theorem lt_trans {base : Nat} {hb : 1 < base} {a b c : Prenumeral base hb} (ha: a < b) :
  b < c → a < c := by
  intro hb
  simp_all only [LT.lt, lt]
  exact ltAux_trans ha hb

instance instTransLt {base : Nat} {hb : 1 < base} :
  Trans (· < ·) (· < ·) (fun a : Prenumeral base hb ↦ fun b : Prenumeral base hb ↦ a < b) where
  trans := lt_trans

theorem lt_of_lt_of_le {base : Nat} {hb : 1 < base} {a b c : Prenumeral base hb}
  (ha: a < b) (hb: b ≤ c) : a < c := by
  exact ltAux_of_ltAux_of_leAux ha hb

instance instTransLtLe {base : Nat} {hb : 1 < base} :
  Trans (· < ·) (· ≤ ·) (fun a : Prenumeral base hb ↦ fun b : Prenumeral base hb ↦ a < b) where
  trans := by
    intro a b c ha hb
    exact lt_of_lt_of_le ha hb

theorem lt_of_le_of_lt {base : Nat} {hb : 1 < base} {a b c : Prenumeral base hb}
  (ha: a ≤ b) (hb: b < c) : a < c := by
  exact ltAux_of_leAux_of_ltAux ha hb

instance instTransLeLt {base : Nat} {hb : 1 < base} :
  Trans (· ≤ ·) (· < ·) (fun a : Prenumeral base hb ↦ fun b : Prenumeral base hb ↦ a < b) where
  trans := by
    intro a b c ha hb
    exact lt_of_le_of_lt ha hb

def decLt {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : Decidable (a < b) :=
  if h : ltAux a.digits b.digits then
    isTrue h
  else
    isFalse h

instance instDecLt {base : Nat} {hb : 1 < base} : DecidableLT (Prenumeral base hb) := decLt

example : @zero 10 (by decide) < @one 10 (by decide) := by native_decide

end LessThan

section HasTrailingZero

/--
`True` if `a` has no trailing zeros

Examples:
```
#eval (⟨[], by decide⟩ : Prenumeral 10 (by decide)).hasNoTrailingZero -- true
#eval (⟨[0], by decide⟩ : Prenumeral 10 (by decide)).hasNoTrailingZero -- false
#eval (⟨[0,1,2], by decide⟩ : Prenumeral 10 (by decide)).hasNoTrailingZero -- true
#eval (⟨[0,1,2,0], by decide⟩ : Prenumeral 10 (by decide)).hasNoTrailingZero -- false
```
-/
def hasNoTrailingZero {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : Prop :=
  noTrailingZero a.digits

def decHasNoTrailingZeros {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) :
  Decidable (a.hasNoTrailingZero) :=
  if h : noTrailingZero a.digits then
    isTrue h
  else
    isFalse h

instance instDecHasNoTrailingZeros {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) :
  Decidable (a.hasNoTrailingZero) := decHasNoTrailingZeros a

theorem eq_iff_equiv_of_hasNoTrailingZero {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb)
  (ha: a.hasNoTrailingZero) (hb: b.hasNoTrailingZero) :
  a = b ↔ equiv a b := by
  unfold hasNoTrailingZero at ha hb
  unfold equiv
  rw [eq_iff_digits_eq]
  exact eq_iff_equivAux_of_noTrailingZero ha hb

end HasTrailingZero

section DiscardTrailingZero

def discardTZ {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : Prenumeral base hb where
  digits := discardTrailingZeros a.digits
  ltBase := allDigitsLtBase_discardTrailingZeros a.ltBase

theorem discardTZ_equiv {base : Nat} {hb : 1 < base} (a : Prenumeral base hb) : a.discardTZ ≈ a := by
  simp only [discardTZ, equiv]
  exact equivAux_discardTrailingZeros

end DiscardTrailingZero

section Rebase

/--
returns a `Prenumeral` with the same value as the input but for a different `base`
-/
def rebase {base : Nat} {hb : 1 < base} (n : Prenumeral base hb) (toBase : Nat) (htb : 1 < toBase) :
  Prenumeral toBase htb := ofNat (n.toNat)

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

section Sub

def hSub {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : Prenumeral base hb :=
  if a ≤ b then
    {
      digits := [],
      ltBase := allDigitsLtBase_nil
    }
  else
    {
      digits := subAux a.digits b.digits 0 base
      ltBase := allDigitsLtBase_subAux a.digits b.digits a.ltBase
    }

instance instHSubPrenumerals {base : Nat} {hb : 1 < base} :
  HSub (Prenumeral base hb) (Prenumeral base hb) (Prenumeral base hb) := ⟨hSub⟩

theorem sub_eq_hSub  {base : Nat} {hb : 1 < base} (a b : Prenumeral base hb) : a - b = a.hSub b := rfl

theorem pos_toNat_sub_of_lt {base : Nat} {hb : 1 < base} {a b : Prenumeral base hb} (h : b < a) :
  0 < toNat (a - b) := by
  have : ¬ a ≤ b := ((lt_iff_le_and_not_le b a).mp h).right
  simp only [sub_eq_hSub, hSub, this, reduceIte, toNat]
  simp only [LT.lt, lt] at h
  exact pos_toNatAux_subAux_of_ltAux_of h hb a.ltBase b.ltBase

theorem pos_sub_of_lt {base : Nat} {hb : 1 < base} {a b : Prenumeral base hb} (h : b < a) :
  (@zero base hb) < a - b := by
  have : 0 < toNat (a - b) := pos_toNat_sub_of_lt h
  rw [← @zero_toNat_eq_zero base hb] at this
  exact (lt_iff_toNat_lt_toNat (@zero base hb) (a - b)).mpr this

example : zero < (10 : Prenumeral10) - (9 : Prenumeral10) := by
  have : (9 : Prenumeral10) < (10 : Prenumeral10) := by native_decide
  exact pos_sub_of_lt this

end Sub

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
def toString {base : Nat} {hb : 1 < base} (n : Prenumeral base hb) : String :=
  toStringAux n.digits base n.ltBase

instance instToStringPrenumeral {base : Nat} {hb : 1 < base} : ToString (Prenumeral base hb) where
  toString := toString

end ToString

section OfString

/--

Examples:
```
#eval @ofString? "0b10110" 2 (by decide) -- some { digits := [0, 1, 1, 0, 1], ltBase := _ }
#eval @ofString? "0o76543210" 8 (by decide) -- some { digits := [0, 1, 2, 3, 4, 5, 6, 7], ltBase := _ }
#eval @ofString? "9876543210" 10 (by decide) -- some { digits := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ltBase := _ }
#eval @ofString? "0xfedcba9876543210" 16 (by decide) -- some { digits := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ltBase := _ }
#eval @ofString? "(60)12,59,59" 60 (by decide) -- some { digits := [59, 59, 12], ltBase := _ }
#eval @ofString? "007" 10 (by decide) -- some { digits := [7, 0, 0], ltBase := _ }
#eval @ofString? "not a valid string" 10 (by decide) -- none
```
-/
def ofString? (s : String) {base : Nat} {hb : 1 < base} : Option (Prenumeral base hb) :=
  match parse s with
  | (_, .success d) =>
    if h : base = d.base then
      some {
        digits := (fromListFinBase d.digits).reverse,
        ltBase := by
          rw [h]
          simp only [allDigitsLtBase, List.all_reverse]
          exact allDigitsLtBase_fromListFinBase d.digits
      }
    else
      none
  | _ => none

def ofStringD (s : String) {base : Nat} {hb : 1 < base} : Prenumeral base hb := (ofString? s).getD default
def ofString! (s : String) {base : Nat} {hb : 1 < base} : Prenumeral base hb := (ofString? s).get!

end OfString

end Prenumeral
end Prenumerals

section Numerals

/--
`Numeral`s are `Prenumeral`s without leading zeros, which is ensured by `noTZ`, which stands for _has no trailing zeros_.
By this, every natural number has a unique representation for the given `base`.
-/
@[ext]
structure Numeral (base : Nat) (hb : 1 < base) extends Prenumeral base hb where
  noTZ : noTrailingZero digits
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
converts a `Prenumeral` into a `Numeral` by discarding (potentially present) trailing zeros

Examples:
```
def p : Prenumeral 10 (by decide) := ⟨[1,9,0], by  decide⟩
#eval p -- { digits := [1, 9, 0], ltBase := _ }

def n : Numeral 10 (by decide) := p.toNumeral
#eval n -- { toPrenumeral := { digits := [1, 9], ltBase := _ }, noTZ := _ }
```
-/
def Prenumeral.toNumeral {base : Nat} {hb : 1 < base} (p : Prenumeral base hb) :
  Numeral base hb where
  digits := discardTrailingZeros p.digits
  ltBase := allDigitsLtBase_discardTrailingZeros p.ltBase
  noTZ := noTrailingZero_discardTrailingZeros

/-
zero (represented by `[]`) is the default `Numeral` - for any base
-/
instance instInhabitedNumeral {base : Nat} {hb : 1 < base} : Inhabited (Numeral base hb) := ⟨{
    toPrenumeral := default,
    noTZ := noTrailingZero_nil
  }⟩

/--
Example:
```
def n : Numeral10 := ⟨⟨[1,2,3], by decide⟩, by decide⟩
#eval n.toString -- "321"
```
-/
instance instToStringNumeral {base : Nat} {hb : 1 < base} : ToString (Numeral base hb) where
  toString := fun n => n.toPrenumeral.toString

/--
provides the number of digits used by the given `Numeral`
-/
def length {base : Nat} {hb : 1 < base} (n : Numeral base hb) : Nat := n.digits.length

def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : Numeral base hb where
  toPrenumeral := Prenumeral.ofNat n
  noTZ := noTrailingZero_prune_of_noTrailingZero noTrailingZero_nil

section Add

def hAdd {base : Nat} {hb : 1 < base} (a b : Numeral base hb) : Numeral base hb where
  toPrenumeral := a + b
  noTZ := noTrailingZero_addAux_of a.noTZ b.noTZ hb

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
