/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.NatGtOne
import Numerals.ToNat
import Numerals.EquivIsZero
import Numerals.AllDigitsBase
import Numerals.NoTrailingZero
import Numerals.DiscardTZ
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
* `TZNumeral` for which _trailing_ (have the same effect as _leading_ zeros in regular numerals due to the inverted
  order in which digits are stored) zeros are permitted, which means that there are multiple `equiv`alent representations
  of the same natural number and
* `Numeral`, which is a subtype of `TZNumeral` but without ambiguity in the representation, which is achieved by excluding
  trailing zeros.

In particular, it provides non-primitive functions for basic operations such as `add`ition and `sub`traction
of numerals and theorems that ensure that these functions are consistent with the respective operations on
[`Nat`](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/#Nat).
This is useful for proofing theorems that refer to the representation of natural numbers as
numerals in positional notation.

## TZNumeral

## Numeral

-/

set_option linter.all true
/-
TODO: remove and resolve
-/
set_option linter.missingDocs false

section TZNumerals

/--
TODO: correct
`TZNumeral` provides a representation of a natural number in positional notation for `base`, with `digits`
in _reverse_ (little-endian) order. `base` can be any natural number larger than one.
`ltBase` asserts that all natural numbers in list `digits` are less than `base`.

`TZNumeral`s can have leading zeros as in
```
def p : TZNumeral 10 (by decide) := {digits := [2, 1, 0], ltBase := by decide}

```
which represents the number `12` in base ten.

@[ext]
structure TZNumeral (base : NatGtOne) where
  digits : List Nat
  ltBase : allDigitsLtBase digits base.val
  deriving Repr
-/

@[ext]
structure TZNumeral (base : NatGtOne) where
  digits : List (Fin base.val)
  deriving Repr

/--
shorthand for `TZNumeral`s in binary representation
-/
abbrev TZNumeral2 := TZNumeral ⟨2, by decide⟩

/--
shorthand for `TZNumeral`s octal representation
-/
abbrev TZNumeral8 := TZNumeral ⟨8,by decide⟩

/--
shorthand for `TZNumeral`s decimal representation
-/
abbrev TZNumeral10 := TZNumeral ⟨ 10, by decide⟩

/--
shorthand for `TZNumeral`s hexadecimal representation
-/
abbrev TZNumeral16 := TZNumeral ⟨16, by decide⟩

/--

Example:
```
def p : TZNumeral 10 (by decide) := [1, 2, 3, 0].toTZNumeral (by decide)
#eval p -- { digits := [1, 2, 3, 0], ltBase := _ }
```
-/
def List.toTZNumeral {base: NatGtOne} (a: List (Fin base.val)) : TZNumeral base where
  digits := a

namespace TZNumeral

/--
returns the base of the provided `TZNumeral`
-/
def base {base' : NatGtOne} (_ : TZNumeral base') : NatGtOne := base'

abbrev zero {base : NatGtOne} : TZNumeral base := ⟨[]⟩

/--
`[]` (i.e. _zero_) is the default `TZNumeral` - for any base
-/
instance instInhabited {base : NatGtOne} : Inhabited (TZNumeral base) := ⟨zero⟩

theorem zero_eq_default {base : NatGtOne} : @zero base = default := rfl

/--
use `0` for zero

Example:
```
#eval (0 : TZNumeral 10 (by decide)) -- { digits := [], ltBase := _ }
```
-/
instance instZero {base : NatGtOne} : Zero (TZNumeral base) := ⟨default⟩

theorem zero_eq_zero {base : NatGtOne} : @zero base = 0 := rfl

abbrev one {base : NatGtOne} : TZNumeral base where
  digits := [⟨1, base.property⟩ ]

/--
use `1` for one

Example:
```
#eval (1 : TZNumeral 10 (by decide)) -- { digits := [1], ltBase := _ }
```
-/
instance instOne {base : NatGtOne} : One (TZNumeral base) where
  one := one

section Equality

/--
asserts that two `TZNumeral`s are equal iff their lists of digits are equal
-/
theorem eq_iff_digits_eq {base : NatGtOne} (a b : TZNumeral base) :
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
def decEq {base : NatGtOne} (a b : TZNumeral base) : Decidable (a = b) :=
  if h : a.digits = b.digits then
    isTrue ((eq_iff_digits_eq a b).mpr h)
  else
    have : a.digits ≠ b.digits → a ≠ b := (Classical.iff_iff_not_iff_not.mp (eq_iff_digits_eq a b)).mpr
    isFalse (this h)

instance instDecidableEq {base : NatGtOne} (a b : TZNumeral base) : Decidable (a = b) :=
  decEq a b

end Equality

section ToNat_OfNat

/--
returns the value (of type `Nat`) of the given `TZNumeral`

Examples:
```
#eval (⟨[], by decide⟩ : TZNumeral10).toNat -- 0
#eval (⟨[0], by decide⟩ : TZNumeral10).toNat -- 0
#eval (⟨[0,1,2], by decide⟩ : TZNumeral10).toNat -- 210
#eval (⟨[0,1,2,0], by decide⟩ : TZNumeral10).toNat -- 210
```
-/
def toNat {base : NatGtOne} (n : TZNumeral base) : Nat :=
  toNatAux (fromListFinBase n.digits) base.val

theorem zero_toNat_eq_zero {base : NatGtOne} : (@zero base).toNat = 0 :=
  toNatAux_nil_eq

/--
returns a `TZNumeral` for the given number (of type `Nat`)

Examples:
```
#eval @TZNumeral.ofNat 0 ⟨10, by decide⟩  -- { digits := [] }
#eval @TZNumeral.ofNat 11 ⟨2, by decide⟩  -- { digits := [1, 1, 0, 1] }
#eval @TZNumeral.ofNat (15 + 16) ⟨16, by decide⟩  -- { digits := [15, 1] }
```
-/
def ofNat (n : Nat) {base : NatGtOne} : TZNumeral base where
  digits := toListFinBase (ofNatAux n base.val base.property) allDigitsLtBase_prune

theorem ofNat_zero_eq_zero {base : NatGtOne} : @ofNat 0 base = zero := by
  unfold ofNat ofNatAux prune zero
  rfl

theorem digits_zero_eq_nil  {base : NatGtOne} : @digits base 0 = [] := rfl

theorem ofNat_one_eq_one {base : NatGtOne} : @ofNat 1 base = one := by
  unfold ofNat one
  simp only [ofNatAux_eq_of_lt_base base.property, Nat.one_ne_zero, reduceIte]
  rfl

instance instOfNat {base : NatGtOne} (n : Nat) : OfNat (TZNumeral base) n where
  ofNat := ofNat n

/--
`toNat` is the inverse of `ofNat`
-/
theorem toNat_leftInverse_ofNat {n : Nat} {base : NatGtOne} : (@ofNat n base).toNat = n := by
  simp only [toNat, ofNat, fromListFinBase_toListFinBase_cancel (ofNatAux n base.val _) _]
  simp only [ofNatAux, toNatAux_prune_eq_add_toNatAux, toNatAux_nil_eq, Nat.add_zero]

theorem zero_eq_zero' {base : NatGtOne} : (0 : TZNumeral base) = zero := by
  unfold OfNat.ofNat instOfNat ofNat zero
  simp only [ofNatAux, prune, (toListFinBase_nil_iff_nil _ _ ).mpr _]

/--
For `TZNumerals` with trailing zeros, `ofNat` is not the left inverse of `toNat`, since
trailing zeros are not preserved by `toNat`. The following example shows this for a very
simple case.
-/
example : ∃ p : TZNumeral10, ofNat (p.toNat) ≠ p := by
  let p : TZNumeral10 := ⟨[0]⟩
  let q : TZNumeral10 := ⟨[]⟩
  refine ⟨p, ?_⟩
  have : p.toNat = 0 := by decide
  rw [this]
  have : ofNat 0 = q := by
    simp only [ofNat, ofNatAux, prune, (toListFinBase_nil_iff_nil _ _ ).mpr _]
    rfl
  rw [this]
  decide

end ToNat_OfNat

section Equivalence

/--
two `TZNumeral`s of the same `base` are `equiv`alent, if they only differ with respect to
_leading_ (or technically correctly, _trailing_) zeros.
-/
def equiv {base : NatGtOne} (a b : TZNumeral base) : Prop :=
  equivAux (fromListFinBase a.digits) (fromListFinBase b.digits)

theorem toNat_eq_iff_equiv {base: NatGtOne} (a b : TZNumeral base) :
  a.toNat = b.toNat ↔ equiv a b := by
  unfold toNat equiv
  exact toNatAux_eq_iff_equivAux (allDigitsLtBase_fromListFinBase a.digits)
    (allDigitsLtBase_fromListFinBase b.digits) base.property

/--
`equiv` is an `Equivalence` i.e. [equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation)

Example:
```
#check equivalence_equiv.refl -- ∀ (x : TZNumeral ?m.1), x.equiv x
#check equivalence_equiv.symm -- equiv ?m.4 ?m.5 → equiv ?m.5 ?m.4
#check equivalence_equiv.trans -- equiv ?m.4 ?m.5 → equiv ?m.5 ?m.6 → equiv ?m.4 ?m.6
```
-/
theorem equivalence_equiv {base: NatGtOne} :
  Equivalence (equiv : (TZNumeral base) → (TZNumeral base) → Prop) :=
  ⟨
    by unfold equiv; exact fun _ ↦ equivAux_refl,
    by unfold equiv; intro a b hab; exact equivAux_symm hab,
    by unfold equiv; intro a b c hab hbc; exact equivAux_trans hab hbc
  ⟩

instance instHasEquiv {base : NatGtOne} : HasEquiv (TZNumeral base) := ⟨equiv⟩

example {base: NatGtOne} (a : TZNumeral base) : a ≈ a := by
  exact equivalence_equiv.refl a

example {base: NatGtOne} (a b : TZNumeral base) : a ≈ b → b ≈ a := by
  exact equivalence_equiv.symm

example {base: NatGtOne} (a b c : TZNumeral base) : a ≈ b → b ≈ c → a ≈ c:= by
  exact equivalence_equiv.trans

example {base: NatGtOne} (a b c : TZNumeral base) : a ≈ b → c ≈ b → a ≈ c:= by
  intro hab hcb
  have hbc : b ≈ c := equivalence_equiv.symm hcb
  exact equivalence_equiv.trans hab hbc

theorem not_equiv_iff_not_equiv {base: NatGtOne} (a b : TZNumeral base) :
  ¬ a ≈ b ↔ ¬ b ≈ a := by
  simp only [equiv]
  exact not_equivAux_iff_not_equivAux

end Equivalence

section IsZero
/--
`True` if the given `TZNumeral` is `0`
-/
def isZero {base : NatGtOne} (a : TZNumeral base) : Prop := isZeroAux (fromListFinBase a.digits)

theorem equiv_zero_iff_isZero {base : NatGtOne} (a : TZNumeral base) : a ≈ 0 ↔ a.isZero := by
  rw [zero_eq_zero', isZero]
  exact equivAux_nil_iff_isZeroAux (fromListFinBase a.digits)

theorem toNat_eq_zero_iff_isZero {base : NatGtOne} (n : TZNumeral base) :
  n.toNat = 0 ↔ n.isZero := by
  unfold toNat isZero
  exact toNatAux_eq_zero_iff_isZeroAux base.property

/--
`ofNat` returns a `TZNumeral` that `isZero` iff its input is `0`
-/
theorem ofNat_isZero_iff_eq_zero {n : Nat} {base : NatGtOne} :
  (@ofNat n base).isZero ↔ n = 0 := by
  simp only [isZero, ofNat, fromListFinBase_toListFinBase_cancel]
  exact isZeroAux_ofNatAux_iff_eq_zero

example : (@ofNat 0 ⟨10, by decide⟩).isZero := by
  rw [ofNat_isZero_iff_eq_zero]

/--
makes `isZero` decidable
-/
def decIsZero {base : NatGtOne} (a : TZNumeral base) : Decidable a.isZero :=
  decIsZeroAux (fromListFinBase a.digits)

/--
instance of class `Decidable` for `isZero`
-/
instance instDecIsZero {base : NatGtOne} (a : TZNumeral base) : Decidable (isZero a) :=
  decIsZero a

example : (0 : TZNumeral10).isZero := by native_decide

end IsZero

section LessThanOrEqualTo

/--
[_less than or equal to_](https://en.wikipedia.org/w/index.php?title=Inequality_(mathematics)&oldid=1351959378)
for `TZNumeral`s

```
def a : TZNumeral10 := default
def b : TZNumeral10 := ⟨[1], by decide⟩
def c : TZNumeral10 := ⟨[1, 0], by decide⟩
#check a ≤ b -- Prop
#eval a ≤ b -- true
#eval b ≤ a -- false
#eval b ≤ c -- true
#eval c ≤ b -- true
```
-/
def le {base : NatGtOne} (a b : TZNumeral base) : Prop :=
  leAux (fromListFinBase a.digits) (fromListFinBase b.digits)

instance instLe {base : NatGtOne} : LE (TZNumeral base) := ⟨le⟩

theorem le_iff_toNat_le_toNat {base : NatGtOne} (a b : TZNumeral base) :
  a ≤ b ↔ a.toNat ≤ b.toNat := by
  simp only [LE.le, le, toNat]
  exact leAux_iff_toNatAux_le_toNatAux base.property
    (allDigitsLtBase_fromListFinBase a.digits) (allDigitsLtBase_fromListFinBase b.digits)

/--
`le` is a [Preorder](https://en.wikipedia.org/wiki/Preorder), i.e. a
[reflexive](https://en.wikipedia.org/wiki/Reflexive_relation) and
[transitive](https://en.wikipedia.org/wiki/Transitive_relation) relation.

Since `equiv a b` does **not** imply `a = b` for `TZNumeral`s, `le` is not
[antisymmetric](https://en.wikipedia.org/wiki/Antisymmetric_relation) - but
almost (see `equivAux_iff_leAux_and_leAux`).
-/
instance instLeIsPreorder {base : NatGtOne} : Std.IsPreorder (TZNumeral base) :=
  ⟨
    by unfold instLe le; intro _ ; exact leAux_refl,
    by unfold instLe le; intro a b c; exact leAux_trans
  ⟩

instance instLeIsLinearPreorder {base : NatGtOne} : Std.IsLinearPreorder (TZNumeral base) :=
  ⟨
    by intro a b; simp only [LE.le, le]; exact leAux_total
  ⟩

instance instTransLe {base : NatGtOne} :
  Trans (· ≤ ·) (· ≤ ·) (fun a : TZNumeral base ↦ fun b : TZNumeral base ↦ a ≤ b) where
  trans := @instLeIsPreorder.le_trans

theorem zero_le {base : NatGtOne} (a : TZNumeral base) : 0 ≤ a := by
  unfold instOfNat
  simp only [ofNat_zero_eq_zero, LE.le, le]
  exact leAux_nil

example {base : NatGtOne} : (0 : TZNumeral base) ≤ 1 := zero_le 1

def decLe {base : NatGtOne} (a b : TZNumeral base) : Decidable (a ≤ b) :=
  if h : leAux (fromListFinBase a.digits) (fromListFinBase b.digits) then
    isTrue h
  else
    isFalse h

instance instDecLe {base : NatGtOne} (a b : TZNumeral base) :
  Decidable (a ≤ b) := decLe a b

example : @zero ⟨10, by decide⟩  ≤ @one ⟨10, by decide⟩  := by decide
example : (0 : TZNumeral10) ≤ 1 := by native_decide
example : (1966 : TZNumeral10) ≤ (2026 : TZNumeral10) := by native_decide

end LessThanOrEqualTo

section Min

/--
Example:
```
#eval min (0 : TZNumeral 10 (by decide)) 1 -- { digits := [], ltBase := _ }
```
-/
instance instMin {base : NatGtOne} : Min (TZNumeral base) := minOfLe

instance instMinEqOr {base : NatGtOne} : Std.MinEqOr (TZNumeral base) where
  min_eq_or := by
    intro a b
    by_cases h: a ≤ b <;> simp only [Min.min, h, reduceIte, or_true, true_or]

end Min

section Max

/--
Example:
```
#eval max (0 : TZNumeral 10 (by decide)) 1 -- { digits := [1], ltBase := _ }
```
-/
instance instMax {base : NatGtOne} : Max (TZNumeral base) := maxOfLe

instance instMaxEqOr {base : NatGtOne} : Std.MaxEqOr (TZNumeral base) where
  max_eq_or := by
    intro a b
    by_cases h: a ≤ b <;> simp only [Max.max, h, reduceIte, or_true, true_or]

end Max

section LessThan

def lt {base : NatGtOne} (a b : TZNumeral base) : Prop :=
  ltAux (fromListFinBase a.digits) (fromListFinBase b.digits)

instance instLt {base : NatGtOne} : LT (TZNumeral base) := ⟨lt⟩

theorem lt_iff_toNat_lt_toNat {base : NatGtOne} (a b : TZNumeral base) :
  a < b ↔ a.toNat < b.toNat := by
  simp only [LT.lt, lt, toNat]
  exact ltAux_iff_toNatAux_lt_toNatAux base.property
    (allDigitsLtBase_fromListFinBase a.digits) (allDigitsLtBase_fromListFinBase b.digits)

theorem lt_iff_le_and_not_le {base : NatGtOne} (a b : TZNumeral base) :
  a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  simp only [LT.lt, lt, LE.le, le]
  exact ltAux_iff_leAux_and_not_leAux

instance instLawfulOrderLT {base : NatGtOne} : Std.LawfulOrderLT (TZNumeral base) :=
  ⟨lt_iff_le_and_not_le⟩

theorem le_irrefl {base : NatGtOne} (a : TZNumeral base) : ¬ a < a := by
  simp only [LT.lt, lt]
  exact ltAux_irrefl

theorem lt_asymm {base : NatGtOne} {a b : TZNumeral base} (h: a < b) : ¬ b < a := by
  simp only [LT.lt, lt] at h ⊢
  exact ltAux_asymm h

theorem lt_trans {base : NatGtOne} {a b c : TZNumeral base} (ha: a < b) :
  b < c → a < c := by
  intro hb
  simp_all only [LT.lt, lt]
  exact ltAux_trans ha hb

instance instTransLt {base : NatGtOne}:
  Trans (· < ·) (· < ·) (fun a : TZNumeral base ↦ fun b : TZNumeral base ↦ a < b) where
  trans := lt_trans

theorem lt_of_lt_of_le {base : NatGtOne} {a b c : TZNumeral base}
  (ha: a < b) (hb: b ≤ c) : a < c := by
  exact ltAux_of_ltAux_of_leAux ha hb

instance instTransLtLe {base : NatGtOne} :
  Trans (· < ·) (· ≤ ·) (fun a : TZNumeral base ↦ fun b : TZNumeral base ↦ a < b) where
  trans := by
    intro a b c ha hb
    exact lt_of_lt_of_le ha hb

theorem lt_of_le_of_lt {base : NatGtOne} {a b c : TZNumeral base}
  (ha: a ≤ b) (hb: b < c) : a < c := by
  exact ltAux_of_leAux_of_ltAux ha hb

instance instTransLeLt {base : NatGtOne} :
  Trans (· ≤ ·) (· < ·) (fun a : TZNumeral base ↦ fun b : TZNumeral base ↦ a < b) where
  trans := by
    intro a b c ha hb
    exact lt_of_le_of_lt ha hb

def decLt {base : NatGtOne} (a b : TZNumeral base) : Decidable (a < b) :=
  if h : ltAux (fromListFinBase a.digits) (fromListFinBase b.digits) then
    isTrue h
  else
    isFalse h

instance instDecLt {base : NatGtOne} : DecidableLT (TZNumeral base) := decLt

example : @zero ⟨10, by decide⟩  < @one ⟨10, by decide⟩ := by native_decide

end LessThan

section NoTrailingZero

def noTrailingZero {base : NatGtOne} (n : TZNumeral base) : Prop :=
  (h : n.digits ≠ []) → n.digits.getLast h ≠ ⟨0, Nat.pos_of_one_lt base.property⟩

theorem noTrailingZero_zero {base : NatGtOne} : (@zero base).noTrailingZero := by
  unfold zero noTrailingZero; intro; contradiction

theorem noTrailingZero_iff {base : NatGtOne} (n : TZNumeral base) :
  noTrailingZero n ↔ noTrailingZeroAux (fromListFinBase n.digits) := by
  constructor
  · intro h
    match g : n.digits with
    | [] => simp only [fromListFinBase]; exact noTrailingZeroAux_nil
    | x::xs =>
      simp only [g, noTrailingZero] at h
      unfold noTrailingZeroAux
      intro h1
      have h2 : x::xs ≠ [] := List.cons_ne_nil x xs
      have h3 : (x::xs).getLast h2 ≠ ⟨0, Nat.pos_of_one_lt base.property⟩ := h h2
      have h4 : ↑((x::xs).getLast h2) ≠ (0 : Nat) := (ne_iff_coe_ne _ _).mp h3
      have h5 : (fromListFinBase (x::xs)).getLast h1 ≠ 0 := by
        false_or_by_contra ; rename _ => h6
        rw [fromListFinBase_getLast_eq_getLast_of (x::xs) h2] at h6
        contradiction
      exact h5
  · intro h
    unfold noTrailingZero
    match g : n.digits with
    | [] => intro; contradiction
    | x::xs =>
      intro h1
      simp only [g, noTrailingZeroAux] at h
      have h2 : fromListFinBase (x :: xs) ≠ [] := (fromListFinBase_ne_nil_iff_ne_nil _).mpr h1
      have h3 : (fromListFinBase (x :: xs)).getLast h2 ≠ 0 := h h2
      false_or_by_contra ; rename _ => h4
      have h5 : (fromListFinBase (x :: xs)).getLast h2 = 0 := by
        simp only [fromListFinBase_getLast_eq_getLast_of (x::xs) h1, h4]
      contradiction

theorem neg_noTrailingZero_iff {base : NatGtOne} (n : TZNumeral base) :
  ¬ noTrailingZero n ↔ ¬ noTrailingZeroAux (fromListFinBase n.digits) :=
    Classical.iff_iff_not_iff_not.mp (noTrailingZero_iff n)

def decNoTrailingZero {base : NatGtOne} (n : TZNumeral base) : Decidable (noTrailingZero n) :=
  if g : noTrailingZeroAux (fromListFinBase n.digits) then
    isTrue ((noTrailingZero_iff n).mpr g)
  else
    isFalse ((neg_noTrailingZero_iff n).mpr g)

instance instDecNoTrailingZero {base : NatGtOne} (a : TZNumeral base) :
  Decidable (a.noTrailingZero) := decNoTrailingZero a

/--
`True` if `a` has no trailing zeros
-/
def hasNoTrailingZero {base : NatGtOne} (a : TZNumeral base) : Prop :=
  noTrailingZeroAux (fromListFinBase a.digits)

def decHasNoTrailingZeros {base : NatGtOne} (a : TZNumeral base) :
  Decidable (a.hasNoTrailingZero) :=
  if h : noTrailingZeroAux (fromListFinBase a.digits) then
    isTrue h
  else
    isFalse h

/--

Examples:
```
#eval (⟨[], by decide⟩ : TZNumeral10).hasNoTrailingZero -- true
#eval (⟨[0], by decide⟩ : TZNumeral10).hasNoTrailingZero -- false
#eval (⟨[0,1,2], by decide⟩ : TZNumeral10).hasNoTrailingZero -- true
#eval (⟨[0,1,2,0], by decide⟩ : TZNumeral10).hasNoTrailingZero -- false
```
-/
instance instDecHasNoTrailingZeros {base : NatGtOne} (a : TZNumeral base) :
  Decidable (a.hasNoTrailingZero) := decHasNoTrailingZeros a

theorem eq_iff_equiv_of_hasNoTrailingZero {base : NatGtOne} (a b : TZNumeral base)
  (ha: a.hasNoTrailingZero) (hb: b.hasNoTrailingZero) :
  a = b ↔ equiv a b := by
  unfold hasNoTrailingZero at ha hb
  unfold equiv
  rw [eq_iff_digits_eq]
  let h1 := eq_iff_equivAux_of_noTrailingZeroAux ha hb
  rwa [fromListFinBase_eq_iff_eq] at h1

end NoTrailingZero

section DiscardTrailingZero

def discardTZ {base : NatGtOne} (a : TZNumeral base) : TZNumeral base where
  digits :=
    toListFinBase (discardTZAux (fromListFinBase a.digits))
      (allDigitsLtBase_discardTZAux (allDigitsLtBase_fromListFinBase a.digits))

theorem discardTZ_equiv {base : NatGtOne} (a : TZNumeral base) : a.discardTZ ≈ a := by
  simp only [discardTZ, equiv, fromListFinBase_toListFinBase_cancel]
  exact equivAux_discardTZAux

end DiscardTrailingZero

section Rebase

/--
returns a `TZNumeral` with the same value as the input but for a different `base`
-/
def rebase {base : NatGtOne} (n : TZNumeral base) (toBase : NatGtOne) : TZNumeral toBase :=
  ofNat (n.toNat)

/--
asserts that the result of `rebase` is a `TZNumeral` with `base` `toBase`
-/
theorem rebase_base_eq_toBase {base : NatGtOne} (n : TZNumeral base) (toBase : NatGtOne)  :
  (rebase n toBase).base = toBase := by
  unfold rebase ofNat TZNumeral.toNat
  rfl

theorem toNat_rebase_eq_toNat {base : NatGtOne} (n : TZNumeral base) (toBase : NatGtOne) :
  toNat (rebase n toBase) = toNat n := by
  simp only [rebase, ofNat, toNat, fromListFinBase_toListFinBase_cancel, toNatAux_ofNatAux_cancel]

end Rebase

section Add

def hAdd {base : NatGtOne} (a b : TZNumeral base) : TZNumeral base where
  digits :=
    toListFinBase (
      addAux (fromListFinBase a.digits) (fromListFinBase b.digits) 0 base.val base.property
    ) (allDigitsLtBase_addAux 0)

instance instHAddTZNumerals {base : NatGtOne} :
  HAdd (TZNumeral base) (TZNumeral base) (TZNumeral base) := ⟨hAdd⟩

/--
useful with `rw`-tactics
-/
theorem add_eq_hAdd {base : NatGtOne} (a b : TZNumeral base) : a + b = a.hAdd b := rfl

/--
addition on `TZNumerals` is [commutative](https://en.wikipedia.org/wiki/Commutative_property)
-/
theorem add_comm {base : NatGtOne} (a b : TZNumeral base) :
  a + b = b + a := by
  simp only [add_eq_hAdd, hAdd, addAux_comm base.property]

instance instCommutativeHAddTZNumerals {base : NatGtOne} :
  Std.Commutative (α := TZNumeral base) hAdd := ⟨add_comm⟩

theorem toNat_add_left_distrib {base : NatGtOne} (a b : TZNumeral base) :
  (a + b).toNat = a.toNat + b.toNat := by
  simp only [add_eq_hAdd, TZNumeral.toNat, hAdd]
  simp only [fromListFinBase_toListFinBase_cancel, toNatAux_addAux_left_distrib]

/--
the sum of two `TZNumeral`s `isZero` iff `isZero` holds for both of them
-/
theorem add_isZero_iff_isZero_and_isZero {base : NatGtOne} (a b : TZNumeral base) :
  (a + b).isZero ↔ a.isZero ∧ b.isZero := by
  simp only [← toNat_eq_zero_iff_isZero, toNat_add_left_distrib]
  exact Nat.add_eq_zero_iff

end Add

section Sub

def hSub {base : NatGtOne} (a b : TZNumeral base) : TZNumeral base :=
  if a ≤ b then
    zero
  else
    ⟨
      toListFinBase (subAux (fromListFinBase a.digits) (fromListFinBase b.digits) 0 base.val)
        (allDigitsLtBase_subAux (fromListFinBase a.digits) (fromListFinBase b.digits)
          (allDigitsLtBase_fromListFinBase a.digits))
    ⟩

instance instHSubTZNumerals {base : NatGtOne} :
  HSub (TZNumeral base) (TZNumeral base) (TZNumeral base) := ⟨hSub⟩

theorem sub_eq_hSub {base : NatGtOne} (a b : TZNumeral base) : a - b = a.hSub b := rfl

theorem pos_toNat_sub_of_lt {base : NatGtOne} {a b : TZNumeral base} (h : b < a) :
  0 < toNat (a - b) := by
  have : ¬ a ≤ b := ((lt_iff_le_and_not_le b a).mp h).right
  simp only [LT.lt, lt] at h
  simp only [sub_eq_hSub, hSub, this, reduceIte, toNat, fromListFinBase_toListFinBase_cancel]
  exact pos_toNatAux_subAux_of_ltAux_of h base.property
    (allDigitsLtBase_fromListFinBase a.digits) (allDigitsLtBase_fromListFinBase b.digits)

theorem pos_sub_of_lt {base : NatGtOne} {a b : TZNumeral base} (h : b < a) : @zero base < a - b := by
  have : 0 < toNat (a - b) := pos_toNat_sub_of_lt h
  rw [← @zero_toNat_eq_zero base] at this
  exact (lt_iff_toNat_lt_toNat (@zero base) (a - b)).mpr this

example : zero < (10 : TZNumeral10) - (9 : TZNumeral10) := by
  have : (9 : TZNumeral10) < (10 : TZNumeral10) := by native_decide
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
def toString {base : NatGtOne} (n : TZNumeral base) : String :=
  let d := fromListFinBase n.digits
  have hd : allDigitsLtBase d base.val := allDigitsLtBase_fromListFinBase n.digits
  toStringAux d base.val hd

instance instToStringTZNumeral {base : NatGtOne} : ToString (TZNumeral base) where
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
def ofString? (s : String) {base : NatGtOne} : Option (TZNumeral base) :=
  match parse s with
  | (_, .success d) =>
    if h : d.base.val = base.val then
      some {
        digits := List.reverse (d.digits.map (fun i => Fin.cast h i))
      }
    else
      none
  | _ => none

def ofStringD (s : String) {base : NatGtOne} : TZNumeral base := (ofString? s).getD default
def ofString! (s : String) {base : NatGtOne} : TZNumeral base := (ofString? s).get!

end OfString

end TZNumeral
end TZNumerals

section Numerals

/--
`Numeral`s are `TZNumeral`s without leading zeros, which is ensured by `noTZ`, which stands for _has no trailing zeros_.
By this, every natural number has a unique representation for the given `base`.
-/
@[ext]
structure Numeral (base : NatGtOne) extends TZNumeral base where
  noTZ : toTZNumeral.noTrailingZero
  deriving Repr

/--
Numerals in binary representation
-/
abbrev Numeral2 := Numeral ⟨2, by decide⟩

/--
Numerals in octal representation
-/
abbrev Numeral8 := Numeral ⟨8, by decide⟩

/--
Numerals in decimal representation
-/
abbrev Numeral10 := Numeral ⟨10, by decide⟩

/--
Numerals in hexadecimal representation
-/
abbrev Numeral16 := Numeral ⟨16, by decide⟩

/-
TODO: remove
Coercion of a `Numeral` into a `TZNumeral`.

@[coe]
def toTZNumeral {base : NatGtOne} (n : Numeral base) : TZNumeral base := n.toTZNumeral
-/

namespace Numeral

instance {base : NatGtOne} : Coe (Numeral base) (TZNumeral base) where
  coe := toTZNumeral

/--
converts a `TZNumeral` into a `Numeral` by discarding (potentially present) trailing zeros

Examples:
```
def p : TZNumeral 10 (by decide) := ⟨[1,9,0], by  decide⟩
#eval p -- { digits := [1, 9, 0], ltBase := _ }

def n : Numeral 10 (by decide) := p.toNumeral
#eval n -- { toTZNumeral := { digits := [1, 9], ltBase := _ }, noTZ := _ }
```
-/
def TZNumeral.toNumeral {base : NatGtOne} (p : TZNumeral base) : Numeral base :=
  let d := discardTZAux (fromListFinBase p.digits)
  have h1 : allDigitsLtBase d base.val := allDigitsLtBase_discardTZAux (allDigitsLtBase_fromListFinBase p.digits)
  have h2 : noTrailingZeroAux d := noTrailingZeroAux_discardTZAux
  have h3 : noTrailingZeroAux (fromListFinBase (toListFinBase d h1)) := by
    rwa [fromListFinBase_toListFinBase_cancel d h1]
  {
    digits := toListFinBase d h1,
    noTZ := (TZNumeral.noTrailingZero_iff _).mpr h3
  }

/-
zero (represented by `[]`) is the default `Numeral` - for any base
-/
instance instInhabitedNumeral {base : NatGtOne} : Inhabited (Numeral base) :=
  ⟨{
    toTZNumeral := TZNumeral.zero,
    noTZ := TZNumeral.noTrailingZero_zero
  }⟩

/--
Example:
```
def n : Numeral10 := ⟨⟨[1,2,3], by decide⟩, by decide⟩
#eval n.toString -- "321"
```
-/
instance instToStringNumeral {base : NatGtOne} : ToString (Numeral base) where
  toString := fun n => n.toTZNumeral.toString

/--
provides the number of digits used by the given `Numeral`
-/
def length {base : NatGtOne} (n : Numeral base) : Nat := n.digits.length

def ofNat (n : Nat) (base : NatGtOne) : Numeral base where
  toTZNumeral := TZNumeral.ofNat n
  noTZ := by
    simp only [TZNumeral.noTrailingZero_iff, TZNumeral.ofNat, fromListFinBase_toListFinBase_cancel]
    exact noTrailingZeroAux_ofNatAux

section Add

def hAdd {base : NatGtOne} (a b : Numeral base) : Numeral base where
  toTZNumeral := a.toTZNumeral + b.toTZNumeral
  noTZ := by
    unfold TZNumeral.instHAddTZNumerals
    simp only [TZNumeral.noTrailingZero_iff, TZNumeral.hAdd, fromListFinBase_toListFinBase_cancel]
    have h1 : noTrailingZeroAux (fromListFinBase a.digits) := (TZNumeral.noTrailingZero_iff a.toTZNumeral).mp a.noTZ
    have h2 : noTrailingZeroAux (fromListFinBase b.digits) := (TZNumeral.noTrailingZero_iff b.toTZNumeral).mp b.noTZ
    exact noTrailingZeroAux_addAux_of h1 h2 base.property

instance instHAddNumerals {base : NatGtOne} :
  HAdd (Numeral base) (Numeral base) (Numeral base) := ⟨hAdd⟩

theorem add_eq_hAdd {base : NatGtOne} (a b : Numeral base) : a + b = a.hAdd b := rfl

theorem toTZNumeral_add_distrib {base : NatGtOne} (a b : Numeral base) :
  (a + b).toTZNumeral = a.toTZNumeral + b.toTZNumeral := rfl

theorem add_comm {base : NatGtOne} (a b : Numeral base) :
  a + b = b + a := by
  simp only [add_eq_hAdd, hAdd, TZNumeral.add_comm]

instance instCommutativeHAddNumerals {base : NatGtOne} :
  Std.Commutative (α := Numeral base) hAdd := ⟨add_comm⟩

/-
theorem toNat_add_left_distrib {base : Nat} {hb : 1 < base} {a b : TZNumeral base hb} :
  (a.hAdd b).toNat = a.toNat + b.toNat := by
  unfold TZNumeral.toNat hAdd
  simp only []
  exact toNatAux_addAux_left_distrib
-/

end Add

section Sub

end Sub

end Numeral
end Numerals
