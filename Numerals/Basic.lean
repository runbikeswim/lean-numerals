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
* `TZNumeral` for which _trailing_ zeros (having the same effect as _leading_ zeros in regular numerals due to the inverted
  order in which digits are stored) are permitted, which means that there are multiple equivalent representations
  of the same natural number and
* `Numeral`, which is a subtype of `TZNumeral` but without ambiguity in the representation, which is achieved by excluding
  trailing zeros.

In particular, it provides non-primitive functions for basic operations such as addition and subtraction
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

abbrev FinBase {base : NatGtOne} : Type := Fin base.val

namespace NatGtOne

abbrev Fin (base : NatGtOne) : Type := @FinBase base

theorem val_pos {base : NatGtOne} : 0 < base.val :=
  (Nat.lt_trans (by decide)) base.property

theorem val_ne_zero {base : NatGtOne} : base.val ≠ 0 :=
  Nat.ne_zero_of_lt base.val_pos

def zero {base : NatGtOne} : base.Fin := ⟨0, base.val_pos⟩

def one {base : NatGtOne} : base.Fin := ⟨1, base.property⟩

instance instNeZeroNatGtOne (base : NatGtOne) : NeZero base.val := ⟨base.val_ne_zero⟩

end NatGtOne

namespace Fin

theorem eq_zero_of_le_zero {base : NatGtOne} {a : base.Fin} (h : a ≤ base.zero) :
  a = base.zero := Fin.le_antisymm h (Fin.zero_le a)

theorem le_zero_iff' {base : NatGtOne} {y : base.Fin} : y ≤ 0 ↔ y = 0 :=
  Iff.intro Fin.eq_zero_of_le_zero (fun h => by rw [h]; exact Fin.le_refl 0)

end Fin

namespace FinBase

theorem eq_iff_eq_val {base : NatGtOne} {a b : base.Fin} : a = b ↔ a.val = b.val := by
  constructor
  · intro h
    rw [h]
  · intro h
    ext
    assumption

theorem zero_eq_zero {base : NatGtOne} : base.zero = ⟨0, base.val_pos⟩ := rfl

theorem one_eq_one {base : NatGtOne} : base.one = ⟨1, base.property⟩ := rfl

theorem zero_ne_one {base : NatGtOne} : base.zero ≠ base.one := by
  simp only [ne_eq, zero_eq_zero, one_eq_one]
  intro h
  simp only [eq_iff_eq_val] at h
  contradiction

theorem one_ne_zero {base : NatGtOne} : base.one ≠ base.zero := Ne.symm zero_ne_one

def ofNat {base : NatGtOne} (n : Nat) : @FinBase base := ⟨n % base.val, Nat.mod_lt n base.val_pos⟩

theorem ofNat_toNat_eq_n {base : NatGtOne} (n : Nat) : (@ofNat base n).toNat = n % base.val := by
  simp only [ofNat, Fin.toNat]

theorem ofNat_coe_cancel {base : NatGtOne} {x : base.Fin} : ofNat ↑x = x :=
  Fin.ofNat_val_eq_self x

instance {base : NatGtOne} (n : Nat) : OfNat (base.Fin) n := ⟨ofNat n⟩

theorem ofNat_mod_eq {base : NatGtOne} (n : Nat) : @ofNat base (n % base.val) = ofNat n := by
  simp only [ofNat, Nat.mod_mod]

theorem eq_zero_iff_eq_zero {base : NatGtOne} (x : base.Fin) : x = 0 ↔ x = @ofNat base 0 := by
  simp only [OfNat.ofNat, ofNat, (Nat.mod_eq_iff_lt base.val_ne_zero).mpr base.val_pos]

theorem ofNat_ne_zero_of_div_zero_of_ne {base : NatGtOne} {n : Nat} (h1 : n / base.val = 0) (h2 : n ≠ 0) :
  @ofNat base n ≠ 0 := by
  unfold ofNat
  have : n % base.val ≠ 0 := Nat.mod_ne_zero_of_one_lt_of_div_zero_of_ne base.property h1 h2
  intro h
  simp only [eq_iff_eq_val] at h
  contradiction

theorem eq_one_iff_eq_one {base : NatGtOne} (x : base.Fin) : x = base.one ↔ x = @ofNat base 1 := by
  simp only [FinBase.one_eq_one, OfNat.ofNat, ofNat, (Nat.mod_eq_iff_lt base.val_ne_zero).mpr base.property]

end FinBase
end NatGtOne

section List

namespace List

def toListNatAux {base : NatGtOne} (l : List base.Fin) : List Nat := l.map (fun e => e.toNat)

theorem toListNatAux_nil_eq {base : NatGtOne} : @List.toListNatAux base [] = [] := by
  simp only [toListNatAux, map_nil]

theorem toListNatAux_singleton_eq {base : NatGtOne} {a : Fin base.val} :
  @List.toListNatAux base [a] = [↑a] := by
  simp only [List.toListNatAux, List.map_singleton]
  rfl

theorem cons_toListNatAux_eq {base : NatGtOne} {a : Fin base.val} {as : List base.Fin} :
  (a::as).toListNatAux = ↑a :: as.toListNatAux := by
  simp only [List.toListNatAux, List.map_cons]
  rfl

end List
end List

section NumeralsThatCanHaveTrailingZeros

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
  digits : List base.Fin
  deriving Repr

abbrev base2 : NatGtOne := ⟨2, by decide⟩

/--
shorthand for `TZNumeral`s in binary representation
-/
abbrev TZNumeral2 := TZNumeral base2

abbrev base8 : NatGtOne := ⟨8, by decide⟩

/--
shorthand for `TZNumeral`s octal representation
-/
abbrev TZNumeral8 := TZNumeral base8

abbrev base10 : NatGtOne := ⟨10, by decide⟩

/--
shorthand for `TZNumeral`s decimal representation
-/
abbrev TZNumeral10 := TZNumeral ⟨10, by decide⟩

abbrev base16 : NatGtOne := ⟨16, by decide⟩

/--
shorthand for `TZNumeral`s hexadecimal representation
-/
abbrev TZNumeral16 := TZNumeral base16

instance instCoeList_baseFinToTZNumeral {base : NatGtOne} : Coe (List base.Fin) (TZNumeral base) where
  coe := fun l : List base.Fin ↦ {digits := l}

/--

Example:
```
def p : TZNumeral10 := [1, 2, 3, 0].toTZNumeral
#eval p -- { digits := [1, 2, 3, 0]}
```
-/
def List.toTZNumeral {base: NatGtOne} (a: List Nat) : TZNumeral base where
  digits := a.map (fun e : Nat => FinBase.ofNat e)

namespace TZNumeral

section Base
/--
returns the base of the provided `TZNumeral`

Example:
```
def p : TZNumeral10 := [1, 2, 3, 0].toTZNumeral
#eval p.base -- 10
```
-/
def base {_base : NatGtOne} (_ : TZNumeral _base) : NatGtOne := _base

end Base

section Zero

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

theorem digits_zero_eq_nil  {base : NatGtOne} : digits 0 = ([] : List base.Fin) := rfl

end Zero

section One

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
theorem one_eq_one' {base : NatGtOne} : one = (1 : TZNumeral base) := rfl

theorem digits_one_eq_singleton_one {base : NatGtOne} : digits 1 = [base.one] := rfl

end One

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

theorem eq_zero_of_digits_eq_nil {base : NatGtOne} (a : TZNumeral base) (h : a.digits = []) : a = 0 := by
  simp only [eq_iff_digits_eq, OfNat.ofNat, Zero.zero]; assumption

/--
decidable equality
-/
def decEq {base : NatGtOne} (a b : TZNumeral base) : Decidable (a = b) :=
  if g : a.digits = b.digits then
    isTrue ((eq_iff_digits_eq a b).mpr g)
  else
    isFalse ((ne_iff_digits_ne a b).mpr g)

instance instDecidableEq {base : NatGtOne} (a b : TZNumeral base) : Decidable (a = b) :=
  decEq a b

end Equality

section Length

/--
provides the number of digits used by the given `TZNumeral`
-/
def length {base : NatGtOne} (n : TZNumeral base) : Nat := n.digits.length

end Length

section Cons

/--
puts `x` as additional digit in front of the digits of `y`
-/
def cons {base : NatGtOne} (x : Fin base.val) (y : TZNumeral base) : TZNumeral base where
  digits := List.cons x (y.digits)

theorem cons_zero_eq {base : NatGtOne} (x : Fin base.val) : cons x 0 = ⟨[x]⟩ := rfl

theorem cons_ne_zero {base : NatGtOne} (x : Fin base.val) (y : TZNumeral base) :
  cons x y ≠ 0 := by
  intro h1
  rw [eq_iff_digits_eq, digits_zero_eq_nil] at h1
  have h2 : (cons x y).digits = x :: y.digits := by simp only [cons]
  have h3 : (cons x y).digits ≠ [] := by rw [h2]; exact List.cons_ne_nil x y.digits
  exact absurd h1 h3

def uncons {base : NatGtOne} (a : TZNumeral base) (h : a ≠ 0) : base.Fin × (TZNumeral base) :=
  match g : a.digits with
  | [] => absurd (eq_zero_of_digits_eq_nil a g) h
  | x::xs => (x, ⟨xs⟩)

theorem uncons_cons_cancel {base : NatGtOne} (x : Fin base.val) (y : TZNumeral base) :
  uncons (cons x y) (cons_ne_zero x y) = (x,y) := by
  simp only [uncons, cons]

end Cons

section ToListNat

abbrev toListNat {base : NatGtOne} (n : TZNumeral base) : List Nat :=  n.digits.toListNatAux

theorem zero_toList_eq_nil {base : NatGtOne} : (@zero base).toListNat = [] := by
  simp only [toListNat, List.toListNatAux_nil_eq]

theorem toList_singleton_eq {base : NatGtOne} {a : Fin base.val} :
  @toListNat base ⟨[a]⟩ = [↑a] := by
  simp only [toListNat, List.toListNatAux_singleton_eq]

theorem cons_toList_eq_coe_cons_toList {base : NatGtOne} {a : Fin base.val} {as : TZNumeral base} :
  (cons a as).toListNat = ↑ a :: as.toListNat := by
  simp only [cons, toListNat, List.cons_toListNatAux_eq]

end ToListNat

section NoTrailingZero

def noTrailingZero {base : NatGtOne} (n : TZNumeral base) : Prop :=
  helper base n.digits where
  helper (base : NatGtOne) (d : List base.Fin) := (h : d ≠ []) → d.getLast h ≠ 0

theorem noTrailingZero_helper_nil {base : NatGtOne} : noTrailingZero.helper base [] := by
  unfold noTrailingZero.helper; intro; contradiction

theorem noTrailingZero_nil {base : NatGtOne} : noTrailingZero (@zero base):=
  noTrailingZero_helper_nil

theorem zero_noTrailingZero {base : NatGtOne} : (@zero base).noTrailingZero :=
  noTrailingZero_helper_nil

theorem noTrailingZero_of_digits_eq_nil {base : NatGtOne} {n : TZNumeral base} (h : n.digits = []) :
  n.noTrailingZero := by
    simp only [noTrailingZero, h]
    exact noTrailingZero_helper_nil

theorem noTrailingZero_helper_of {base : NatGtOne} {n : List base.Fin}
  (h1 : n ≠ []) (h2 : n.getLast h1 ≠ 0) : noTrailingZero.helper base n := fun _ : n ≠ [] ↦ h2

theorem noTrailingZero_of {base : NatGtOne} {n : TZNumeral base}
  (h1 : n.digits ≠ []) (h2 : n.digits.getLast h1 ≠ 0) :
  n.noTrailingZero := noTrailingZero_helper_of h1 h2

theorem noTrailingZero_helper_singleton_of {base : NatGtOne} {n : base.Fin} (h : n ≠ 0) :
  noTrailingZero.helper base [n] := by
  intro
  simp only [List.getLast_singleton]
  exact h

theorem noTrailingZero_singleton_of {base : NatGtOne} {n : base.Fin} (h : n ≠ 0) :
  noTrailingZero ⟨[n]⟩ := noTrailingZero_helper_singleton_of h

theorem one_noTrailingZero {base : NatGtOne} : (@one base).noTrailingZero := by
  rw [one_eq_one]
  exact noTrailingZero_singleton_of FinBase.one_ne_zero

theorem neg_noTrailingZero_helper_of {base : NatGtOne} {n : List base.Fin}
  (h1 : n ≠ []) (h2 : n.getLast h1 = 0) :
  ¬ noTrailingZero.helper base n := by
  intro h3
  exact absurd h2 (h3 h1)

theorem neg_noTrailingZero_of {base : NatGtOne} {n : TZNumeral base}
  (h1 : n.digits ≠ []) (h2 : n.digits.getLast h1 = 0) :
  ¬ n.noTrailingZero := neg_noTrailingZero_helper_of h1 h2

theorem ne_zero_of_noTrailingZero_helper_singleton {base : NatGtOne} {n : base.Fin}
  (h : noTrailingZero.helper base [n]) : n ≠ 0 := by
  simp only [noTrailingZero.helper, List.getLast_singleton] at h
  exact h (List.cons_ne_nil n [])

theorem ne_zero_of_noTrailingZero_singleton {base : NatGtOne} {n : base.Fin}
  (h : noTrailingZero ⟨[n]⟩) : n ≠ 0 := ne_zero_of_noTrailingZero_helper_singleton h

theorem noTrailingZero_helper_cons_of {base : NatGtOne} {x : base.Fin} {xs : List base.Fin}
  (h : noTrailingZero.helper base xs ∧ (xs = [] → x ≠ 0)) : noTrailingZero.helper base (x::xs) := by
  simp only [noTrailingZero.helper] at ⊢ h
  intro _
  if g : xs = [] then
    simp only [g, List.getLast_singleton (List.cons_ne_nil x [])]
    exact h.right g
  else
    rw [List.getLast_cons g]
    exact h.left g

theorem cons_noTrailingZero_of {base : NatGtOne} {x : base.Fin} {xs : TZNumeral base}
  (h : xs.noTrailingZero ∧ (xs = 0 → x ≠ 0)) : (cons x xs).noTrailingZero := by
  simp only [noTrailingZero, cons, eq_iff_digits_eq, OfNat.ofNat, Zero.zero] at ⊢ h
  exact noTrailingZero_helper_cons_of h

theorem tail_noTrailingZero_helper_and_of {base : NatGtOne} {x : base.Fin} {xs : List base.Fin}
  (h : noTrailingZero.helper base (x::xs)) : noTrailingZero.helper base xs ∧ (xs = [] → x ≠ 0) := by
  if g: xs = [] then
    simp only [g] at ⊢ h
    exact And.intro noTrailingZero_helper_nil (fun _ : True ↦ ne_zero_of_noTrailingZero_helper_singleton h)
  else
    simp only [noTrailingZero.helper] at ⊢ h
    have h1 : (x :: xs).getLast (List.cons_ne_nil x xs) ≠ 0 := h (List.cons_ne_nil x xs)
    have h2 : xs.getLast g ≠ 0 := by rwa [List.getLast_cons g] at h1
    exact And.intro (fun _ : xs ≠ [] ↦ h2) (fun t: xs = [] ↦ absurd t g)

theorem tail_noTrailingZero_and_of {base : NatGtOne} {x : base.Fin} {xs : TZNumeral base}
  (h : (cons x xs).noTrailingZero) : xs.noTrailingZero ∧ (xs = 0 → x ≠ 0) := by
  simp only [noTrailingZero, OfNat.ofNat, Zero.zero, eq_iff_digits_eq]
  exact tail_noTrailingZero_helper_and_of h

theorem cons_noTrailingZero_helper_iff_tail_noTrailingZero_helper_and {base : NatGtOne}
  {x : Fin base.val} {xs : List base.Fin} :
  noTrailingZero.helper base (x::xs) ↔ noTrailingZero.helper base xs ∧ (xs = [] → x ≠ 0) :=
  Iff.intro tail_noTrailingZero_helper_and_of noTrailingZero_helper_cons_of

theorem cons_noTrailingZero_iff_tail_noTrailingZero_and {base : NatGtOne}
  {x : Fin base.val} {xs : TZNumeral base} :
  (cons x xs).noTrailingZero ↔ xs.noTrailingZero ∧ (xs = 0 → x ≠ 0) :=
  Iff.intro tail_noTrailingZero_and_of cons_noTrailingZero_of

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

end NumeralsThatCanHaveTrailingZeros

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

section ToTZNumeral

instance instCoeNumeralToTZNumeral {base : NatGtOne} : Coe (Numeral base) (TZNumeral base) where
  coe := toTZNumeral

end ToTZNumeral

section Zero

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

theorem zero_eq_zero {base : NatGtOne} : @zero base = 0 := rfl
theorem zero_toTZNumeral_eq_TZNumeral_zero {base : NatGtOne} : (@zero base).toTZNumeral = TZNumeral.zero := rfl

end Zero

section One

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

theorem one_eq_one {base : NatGtOne} : one = ⟨@TZNumeral.one base, TZNumeral.one_noTrailingZero⟩ := rfl
theorem one_eq_one' {base : NatGtOne} : one = (1 : Numeral base) := rfl

end One

section Equality

theorem eq_iff_toTZNumeral_eq {base : NatGtOne} (a b : Numeral base) :
  a = b ↔ a.toTZNumeral = b.toTZNumeral := by
  constructor
  · intro h
    simp only [h]
  · intro h
    ext
    simp only [h]

theorem ne_iff_toTZNumeral_ne {base : NatGtOne} (a b : Numeral base) :
  a ≠ b ↔ a.toTZNumeral ≠ b.toTZNumeral :=
  Classical.iff_iff_not_iff_not.mp (eq_iff_toTZNumeral_eq a b)

def decEq {base : NatGtOne} (a b : Numeral base) : Decidable (a = b) :=
  if g : a.toTZNumeral = b.toTZNumeral then
    isTrue ((eq_iff_toTZNumeral_eq a b).mpr g)
  else
    isFalse ((ne_iff_toTZNumeral_ne a b).mpr g)

instance instDecidableEq {base : NatGtOne} (a b : Numeral base) : Decidable (a = b) :=
  decEq a b

end Equality

section Cons

/--
puts `x` as additional digit in front of the digits of `y` if it will not create
trailing zeros
-/
def cons {base : NatGtOne} (x : Fin base.val) (y : Numeral base) : Numeral base :=
  if g : x = 0 ∧ y = 0 then
    y -- do not create trailing zeros
  else
    have h1 : x ≠ 0 ∨ y ≠ 0 := Decidable.not_and_iff_not_or_not.mp g
    have h2 : y.toTZNumeral = 0 → x ≠ 0 := by
      intro h
      cases h1 with
      | inl _ => assumption
      | inr _ =>
        rw [← TZNumeral.zero_eq_zero, ← zero_toTZNumeral_eq_TZNumeral_zero, ← eq_iff_toTZNumeral_eq] at h
        contradiction
    have h3 : (TZNumeral.cons x (y.toTZNumeral)).noTrailingZero :=
      TZNumeral.cons_noTrailingZero_of (And.intro y.noTZ h2)
    ⟨TZNumeral.cons x y, h3⟩

end Cons

end Numeral

end Numerals
