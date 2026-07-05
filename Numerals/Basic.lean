/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Extra

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

-/

set_option linter.all true
/-
TODO: remove and resolve
-/
set_option linter.missingDocs false

section NatGtOne

def NatGtOne := { n : Nat // 1 < n} deriving DecidableEq

namespace NatGtOne

theorem val_pos (base : NatGtOne) : 0 < base.val :=
  (Nat.lt_trans (by decide)) base.property

def ofNat {base : NatGtOne} (n : Nat) : Fin base.val := ⟨n % base.val, Nat.mod_lt n base.val_pos⟩

instance instOfNat {base : NatGtOne} (n : Nat) : OfNat (Fin base.val) n := ⟨ofNat n⟩

theorem val_ne_zero (base : NatGtOne) : base.val ≠ 0 :=
  Nat.ne_zero_of_lt base.val_pos

def zero (base : NatGtOne) : Fin base.val := ⟨0, base.val_pos⟩

theorem zero_eq_zero {base : NatGtOne} : base.zero = ⟨0, base.val_pos⟩ := rfl

theorem eq_zero_iff_eq_zero {base : NatGtOne} (x : Fin base.val) : x = base.zero ↔ x = 0 := by
  simp only [zero_eq_zero, OfNat.ofNat, ofNat, (Nat.mod_eq_iff_lt base.val_ne_zero).mpr base.val_pos]

def one (base : NatGtOne) : Fin base.val := ⟨1, base.property⟩

theorem one_eq_one {base : NatGtOne} : base.one = ⟨1, base.property⟩ := rfl

theorem eq_one_iff_eq_one {base : NatGtOne} (x : Fin base.val) : x = base.one ↔ x = 1 := by
  simp only [one_eq_one, OfNat.ofNat, ofNat, (Nat.mod_eq_iff_lt base.val_ne_zero).mpr base.property]

theorem zero_ne_one {base : NatGtOne} : base.zero ≠ base.one := by
  simp only [ne_eq, zero_eq_zero, one_eq_one]
  simp only [Fin.mk.injEq, Nat.zero_ne_one, not_false_eq_true]

theorem one_ne_zero {base : NatGtOne} : base.one ≠ base.zero := Ne.symm zero_ne_one

end NatGtOne

section TZNumerals

/--
`TZNumeral` provides a representation of a natural number in positional notation for `base`, with `digits`
in _reverse_ (little-endian) order. `base` can be any natural number larger than one.

`TZNumeral`s can have leading zeros as in
```
def p : TZNumeral ⟨10, by decide⟩ := ⟨[2, 1, 0]⟩
```
which represents the number `12` in base ten.
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
abbrev TZNumeral10 := TZNumeral ⟨10, by decide⟩

/--
shorthand for `TZNumeral`s hexadecimal representation
-/
abbrev TZNumeral16 := TZNumeral ⟨16, by decide⟩

/--

Example:
```
def p : TZNumeral10 := [1, 2, 3, 0].toTZNumeral
#eval p -- { digits := [1, 2, 3, 0]}
```
-/
def List.toTZNumeral {base: NatGtOne} (a: List (Fin base.val)) : TZNumeral base where
  digits := a

namespace TZNumeral

/--
returns the base of the provided `TZNumeral`

Example:
```
def p : TZNumeral10 := [1, 2, 3, 0].toTZNumeral
#eval p.base -- 10
```
-/
def base {_base : NatGtOne} (_ : TZNumeral _base) : NatGtOne := _base

abbrev zero {base : NatGtOne} : TZNumeral base := ⟨[]⟩

/--
`zero` is the default `TZNumeral` - for any base
-/
instance instInhabited {base : NatGtOne} : Inhabited (TZNumeral base) := ⟨zero⟩

theorem zero_eq_default {base : NatGtOne} : @zero base = default := rfl

/--
use `0` for zero

Example:
```
#eval (0 : TZNumeral10) -- { digits := [] }
```
-/
instance instZero {base : NatGtOne} : Zero (TZNumeral base) := ⟨zero⟩

theorem zero_eq_zero {base : NatGtOne} : @zero base = 0 := rfl

abbrev one {base : NatGtOne} : TZNumeral base where
  digits := [base.one]

/--
use `1` for one

Example:
```
#eval (1 : TZNumeral10) -- { digits := [1] }
```
-/
instance instOne {base : NatGtOne} : One (TZNumeral base) where
  one := one

theorem one_eq_one {base : NatGtOne} : one = (⟨[⟨1, base.property⟩]⟩ : TZNumeral base) := rfl

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

theorem ne_iff_digits_ne {base : NatGtOne} (a b : TZNumeral base) :
  a ≠ b ↔ a.digits ≠ b.digits := Classical.iff_iff_not_iff_not.mp (eq_iff_digits_eq a b)

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

theorem digits_zero_eq_nil  {base : NatGtOne} : @digits base 0 = [] := rfl

end Equality

section cons

def cons {base : NatGtOne} (x : Fin base.val) (y : TZNumeral base) : TZNumeral base where
  digits := x :: (y.digits)

notation:68 x:67 " :: " y:67 => cons x y

theorem cons_zero_eq {base : NatGtOne} (x : Fin base.val) : x :: 0 = ⟨[x]⟩ := rfl

example : 5 :: (@zero ⟨10, by decide⟩ ) = { digits := [5] } := rfl
example : 5 :: (⟨[1,2,3]⟩ : TZNumeral10) = { digits := [5, 1, 2, 3] } := rfl

end cons

section NoTrailingZero

def noTrailingZero {base : NatGtOne} (n : TZNumeral base) : Prop :=
  (h : n.digits ≠ []) → n.digits.getLast h ≠ 0

theorem noTrailingZero_of_digits_eq_nil {base : NatGtOne} {n : TZNumeral base} (h : n.digits = []) :
  n.noTrailingZero := by
  unfold noTrailingZero; intro; contradiction

theorem zero_noTrailingZero {base : NatGtOne} : (@zero base).noTrailingZero :=
  noTrailingZero_of_digits_eq_nil (by simp only)

theorem noTrailingZero_of {base : NatGtOne} {n : TZNumeral base}
  (h1 : n.digits ≠ []) (h2 : n.digits.getLast h1 ≠ 0) :
  n.noTrailingZero := by
  unfold noTrailingZero
  exact (fun _ => h2)

theorem singleton_noTrailingZero_of {base : NatGtOne} {n : Fin base.val} (h : n ≠ 0) :
  (⟨[n]⟩ : TZNumeral base).noTrailingZero := by
  unfold noTrailingZero
  intro
  simp only [List.getLast_singleton]
  exact h

theorem one_noTrailingZero {base : NatGtOne} : (@one base).noTrailingZero := by
  rw [one_eq_one]
  have : ⟨1, base.property⟩ ≠ base.zero := by
    rw [← NatGtOne.one_eq_one]
    exact NatGtOne.one_ne_zero
  exact singleton_noTrailingZero_of this

theorem neg_noTrailingZero_of {base : NatGtOne} {n : TZNumeral base}
  (h1 : n.digits ≠ []) (h2 : n.digits.getLast h1 = 0) :
  ¬ n.noTrailingZero := by
  false_or_by_contra; rename _ => h3
  unfold noTrailingZero at h3
  exact absurd h2 (h3 h1)

theorem tail_noTrailingZero_and_of {base : NatGtOne} {x : Fin base.val} {xs : TZNumeral base}
  (h : (x :: xs).noTrailingZero) : xs.noTrailingZero ∧ (xs = 0 → x ≠ 0) := by
  if g: xs = 0 then
    simp only [g, cons_zero_eq] at h
    let h1 := h (List.cons_ne_nil x [])
    simp only [List.getLast_singleton] at h1
    simp only [g, true_imp_iff]
    exact And.intro zero_noTrailingZero h1
  else
    have h1 : x :: xs.digits ≠ [] := List.cons_ne_nil x xs.digits
    have h2 : (x :: xs.digits).getLast h1 ≠ 0 := h h1
    have h3 : xs.digits ≠ [] := by
      rwa [← zero_eq_zero, zero, eq_iff_digits_eq, ← ne_eq] at g
    have h4 : (x :: xs.digits).getLast h1 = xs.digits.getLast h3 := List.getLast_cons h3
    have h5 : xs.digits.getLast h3 ≠ 0 := by rwa [← h4]
    exact And.intro (noTrailingZero_of h3 h5) (fun t => absurd t g)

theorem cons_noTrailingZero_of {base : NatGtOne} {x : Fin base.val} {xs : TZNumeral base}
  (h : xs.noTrailingZero ∧ (xs = 0 → x ≠ 0)) : (x :: xs).noTrailingZero := by
  if g : xs = 0 then
    simp only [g, cons_zero_eq]
    exact singleton_noTrailingZero_of (h.right g)
  else
    have h1 : xs.digits ≠ [] := (ne_iff_digits_ne xs 0).mp g
    have h2 : xs.digits.getLast h1 ≠ 0 := by
      simp only [noTrailingZero] at h
      exact h.left h1
    have h3 : x :: xs.digits ≠ [] := List.cons_ne_nil x xs.digits
    have h4 : (x :: xs.digits).getLast h3 = xs.digits.getLast h1 := List.getLast_cons h1
    have h5 : (x :: xs.digits).getLast h3 ≠ 0 := by rwa [h4]
    exact noTrailingZero_of h3 h5

theorem cons_noTrailingZero_iff_tail_noTrailingZero_and {base : NatGtOne}
  {x : Fin base.val} {xs : TZNumeral base} :
  (x :: xs).noTrailingZero ↔ xs.noTrailingZero ∧ (xs = 0 → x ≠ 0) := by
  constructor
  · intro h
    exact tail_noTrailingZero_and_of h
  · intro h
    exact cons_noTrailingZero_of h

/--

Examples:
```
#eval (⟨[3,2,1]⟩ : TZNumeral10).noTrailingZero
#eval (⟨[3,2,1,0]⟩ : TZNumeral10).noTrailingZero
```
-/
def decNoTrailingZero {base : NatGtOne} (n : TZNumeral base) : Decidable (noTrailingZero n) :=
  if g1 : n.digits = [] then
    isTrue (noTrailingZero_of_digits_eq_nil g1)
  else
    if g2: n.digits.getLast g1 = 0 then
      isFalse (neg_noTrailingZero_of g1 g2)
    else
      isTrue (noTrailingZero_of g1 g2)

instance instDecNoTrailingZero {base : NatGtOne} (a : TZNumeral base) :
  Decidable (a.noTrailingZero) := decNoTrailingZero a

end NoTrailingZero

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

namespace Numeral

instance {base : NatGtOne} : Coe (Numeral base) (TZNumeral base) where
  coe := toTZNumeral

abbrev zero {base : NatGtOne} : Numeral base := {
      toTZNumeral := TZNumeral.zero,
      noTZ := TZNumeral.zero_noTrailingZero
    }

/-
zero (represented by `[]`) is the default `Numeral` - for any base
-/
instance instInhabitedNumeral {base : NatGtOne} : Inhabited (Numeral base) := ⟨zero⟩

/--
Example:
```
#eval (0 : Numeral10 ) -- { toTZNumeral := { digits := [] }, noTZ := _ }
```
-/
instance instZero {base : NatGtOne} : Zero (Numeral base) := ⟨zero⟩

abbrev one {base : NatGtOne} : Numeral base := {
      toTZNumeral := TZNumeral.one,
      noTZ := TZNumeral.one_noTrailingZero
    }

/--
use `1` for one

Example:
```
#eval (1 : Numeral10) -- { toTZNumeral := { digits := [1] }, noTZ := _ }
```
-/
instance instOne {base : NatGtOne} : One (Numeral base) where
  one := one

/--
provides the number of digits used by the given `Numeral`
-/
def length {base : NatGtOne} (n : Numeral base) : Nat := n.digits.length

end Numeral
end Numerals
