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

section Numerals

/--
`Numeral` provides a representation of a natural number in positional notation for `base`, with `digits`
in _reverse_ (little-endian) order. `base` can be any number larger than one, which is ensured by `baseGtOne`.
`allDigitsLtBase` asserts that every digit is less than `base`.
Via `noTrailingZeros`, it is ensured that there are no trailing zeros, so except for zero, every natural
number has a unique representation for the given `base`.
`0` can be represented in two ways: either digits equals`[]` or `[0]`, which is independent of `base`
-/
structure Numeral (base : Nat) (hb : 1 < base) where
  digits : List Nat
  allDigitsLtBase : allDigitsLtBase digits base
  noTrailingZeros : noTrailingZeros digits
  deriving Repr

abbrev Numeral2 := Numeral 2 (by decide)
abbrev Numeral8 := Numeral 8 (by decide)
abbrev Numeral10 := Numeral 10 (by decide)
abbrev Numeral16 := Numeral 16 (by decide)

namespace Numeral

section Base

/--
-/
def base {base' : Nat} {hb' : 1 < base'} (_ : Numeral base' hb') : Nat := base'

end Base

section IsZero

/--
covers the two representations of zero as `Numeral`
-/
def isZero {base : Nat} {hb : 1 < base} (a : Numeral base hb) : Prop := isZeroAux a.digits

/-!
-/
def decIsZero {base : Nat} {hb : 1 < base} (a : Numeral base hb) : Decidable a.isZero := decIsZeroAux a.digits

/-!
-/
instance instIstZeroNumeral {base : Nat} {hb : 1 < base} (a : Numeral base hb) : Decidable (isZero a) := decIsZero a

end IsZero

section Default

/-!
-/
instance instInhabitedNumeral {base : Nat} {hb : 1 < base} : Inhabited (Numeral base hb) := ⟨{
    digits := [0],
    allDigitsLtBase := by
      have : 0 < base := Nat.pos_of_one_lt hb
      rwa [allDigitsLtBase.eq_def, List.all, List.all_nil, Bool.and_true, decide_eq_true],
    noTrailingZeros := by
      rw [noTrailingZeros.eq_def]
      intro _ _
      contradiction,
  }⟩

end Default

section ToString

/--
If the base is 10, the sequence of digits in [decimal notation](https://en.wikipedia.org/wiki/Decimal#Decimal_notation)
is returned.

For base 2, 8 or 16, the [binary](https://en.wikipedia.org/wiki/Binary_number),
[octal](https://en.wikipedia.org/wiki/Octal) or [hexadecimal](https://en.wikipedia.org/wiki/Hexadecimal)
representation of `n` followed by the value of `base` (in decimal notation) is returned.

For all other values of base, the list of digits - starting with the most significant - is
returned as sequence of natural numbers, separated by "," and succeeded by the
the value of `base` (all in decimal notation).
-/
def toString {base : Nat} {hb : 1 < base} (n : Numeral base hb) : String :=
  helper (normalizeDigits n.digits) base
    (normalizeDigits_allLtBase_of_allLtBase hb n.allDigitsLtBase) where
  helper (digits : List Nat) (base : Nat) (ha : digits.all (· < base)) :=
    match base with
    | 2
    | 8  => s!"{String.join (digits.map (s!"{·}"))}({base})"
    | 10 => s!"{String.join (digits.map (s!"{·}"))}"
    | 16 => s!"{String.join (digits.mapWithAll (· < 16) ha toHexDigit)}(16)"
    | _  => ",".intercalate (digits.map (fun d : Nat => s!"{d}")) ++ s!"({base})"

/-!
-/
instance instToStringNumeral {base : Nat} {hb : 1 < base} : ToString (Numeral base hb) := ⟨toString⟩

end ToString

section toNat

/-!
-/
def toNat {base : Nat} {hb : 1 < base} (n : Numeral base hb) : Nat := toNatAux n.digits base

/-!
-/
theorem toNat_eq_zero_iff {base : Nat} {hb : 1 < base} (n : Numeral base hb) :
  toNat n = 0 ↔ n.isZero := by
  rw [toNat.eq_def]
  exact toNatAux_eq_zero_iff n.noTrailingZeros hb

end toNat

section OfNat

/-!
-/
def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : Numeral base hb where
  digits := prune [] n base hb
  allDigitsLtBase := allDigitsLtBase_prune
  noTrailingZeros := noTrailingZeros_prune_of (noTrailingZeros_of_nil rfl)

/-!
-/
theorem ofNat_isZero_iff (n : Nat) {base : Nat} (hb : 1 < base) :
  (ofNat n base hb).isZero ↔ n = 0 := by
  constructor
  · intro h
    rw [isZero.eq_def, ofNat.eq_def] at h
    match gn : n with
    | 0 => rfl
    | k + 1 =>
      simp only [] at h
      cases h with
      | inl hl => rw [prune_eq_nil_iff] at hl; exact hl.right
      | inr hr => rw [prune_eq_zero_iff] at hr; exact hr.right
  · intro h
    simp only [h, ofNat, isZero, prune_of_nil_zero rfl rfl hb]
    exact isZeroAux_of_nil

/-!
-/
theorem toNat_leftInverse_ofNat {n base : Nat} {hb : 1 < base} : toNat (ofNat n base hb) = n := by
  rw [toNat, ofNat, toNatAux_prune_eq, toNatAux_nil_eq_zero, Nat.add_zero]

end OfNat

section Rebase

/-!
-/
def rebase {base : Nat} {hb : 1 < base} (n : Numeral base hb) (toBase : Nat) (htb : 1 < toBase) : Numeral toBase htb :=
  ofNat (n.toNat) toBase htb

@[simp]
theorem rebase_base_eq_toBase {base : Nat} {hb : 1 < base} (n : Numeral base hb) (toBase : Nat) (htb : 1 < toBase) :
  (rebase n toBase htb).base = toBase := by
  unfold rebase ofNat toNat
  rfl

end Rebase

section Add

/-!
-/
def hAdd {base : Nat} {hb : 1 < base} (a b : Numeral base hb) : Numeral base hb where
  digits := addAux a.digits b.digits 0 base hb
  allDigitsLtBase := allDigitsLtBase_addAux 0
  noTrailingZeros := noTrailingZeros_addAux_of_noTrailingZeros a.noTrailingZeros b.noTrailingZeros hb

/-!
-/
theorem hAdd_nil_iff_and_nil_nil {base : Nat} {hb : 1 < base} {a b : Numeral base hb}  :
  (hAdd a b).digits = [] ↔ a.digits = [] ∧ b.digits = [] := by
  unfold hAdd
  simp only [addAux_eq_nil_iff, true_and]

/-!
-/
theorem hAdd_comm {base : Nat} {hb : 1 < base} (a b : Numeral base hb) : hAdd a b = hAdd b a := by
  unfold hAdd
  simp only [addAux_comm hb]

/-!
-/
instance instCommutativeHAddNumerals {base : Nat} {hb : 1 < base} : Std.Commutative (α := Numeral base hb) hAdd :=
  ⟨hAdd_comm⟩

/-!
-/
instance instHAddNumerals {base : Nat} {hb : 1 < base} : HAdd (Numeral base hb) (Numeral base hb) (Numeral base hb) := ⟨hAdd⟩

/-!
-/
theorem toNat_add_left_distrib {base : Nat} {hb : 1 < base} {a b : Numeral base hb} :
  toNat (hAdd a b) = a.toNat + b.toNat := by
  unfold toNat hAdd
  simp only []
  exact toNatAux_addAux_left_distrib

end Add

end Numeral
end Numerals

section NumeralsWithBase

/-!
-/
structure NumeralWithBase  where
  base : Nat
  oneLtBase : 1 < base
  val : Numeral base oneLtBase
  deriving Repr

namespace Numeral

/-!
-/
def toWithBase {base : Nat} {hb : 1 < base} (a : Numeral base hb) : NumeralWithBase where
  base := base
  oneLtBase := hb
  val := a

end Numeral

end NumeralsWithBase
