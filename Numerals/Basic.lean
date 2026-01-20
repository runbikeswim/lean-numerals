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

/-!
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

abbrev Numeral2 := Numeral 2 (by decide)
abbrev Numeral8 := Numeral 8 (by decide)
abbrev Numeral10 := Numeral 10 (by decide)
abbrev Numeral16 := Numeral 16 (by decide)

namespace Numeral

section IsZero

/-!
covers the two representations of zero as `Numeral`
-/
def isZero {base : Nat} {hb : 1 < base} (a : Numeral base hb) : Prop := a.digits = [] ∨ a.digits = [0]

def decIsZero {base : Nat} {hb : 1 < base} (a : Numeral base hb) : Decidable a.isZero :=
  if h : a.digits = [] ∨ a.digits = [0] then
    isTrue h
  else
    isFalse h

instance instIstZeroNumeral {base : Nat} {hb : 1 < base} (a : Numeral base hb) : Decidable (isZero a) := decIsZero a

end IsZero

section Default

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

#check Numeral 10 (by decide)

end Default

section ToString

/-!
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

instance instToStringNumeral {base : Nat} {hb : 1 < base} : ToString (Numeral base hb) := ⟨toString⟩

end ToString

section toNat

def toNat {base : Nat} {hb : 1 < base} (n : Numeral base hb) : Nat := toNatAux n.digits base

theorem toNat_eq_zero_iff {base : Nat} {hb : 1 < base} (n : Numeral base hb) :
  toNat n = 0 ↔ n.isZero := by
  constructor
  · intro h
    rw [toNat] at h
    sorry
  · intro h
    sorry

end toNat

section OfNat

def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : Numeral base hb where
  digits := prune [] n base hb
  allDigitsLtBase := allDigitsLtBase_prune
  noTrailingZeros := noTrailingZeros_prune_of (noTrailingZeros_of_nil rfl)

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
    simp only [h, ofNat, isZero, prune_of_nil_zero rfl rfl hb, true_or]

theorem toNat_leftInverse_ofNat {n base : Nat} {hb : 1 < base} : toNat (ofNat n base hb) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    if h : n = 0 then
      have : (ofNat n base hb).isZero := (ofNat_isZero_iff n hb).mpr h
      sorry
    else
      sorry

    /-
      unfold ofNat
      have : addAux [] [] 0 base hb = [] :=
        (addAux_eq_nil_iff hb).mpr (And.intro rfl (And.intro rfl rfl))
      simp only [h, this]
      unfold toNat toNatAux
      rfl
    else
      have h0 : 0 < n := Nat.pos_iff_ne_zero.mpr h
      have h1 : n / base * base ≤ n := Nat.div_mul_le_self n base
      have h2 : n = n % base + (n / base) * base := by rw [Nat.mod_eq_sub_div_mul, Nat.sub_add_cancel h1]
      unfold ofNat toNat at ⊢ ih
      simp only at ⊢ ih
      if g: n % base = 0 then
        have h3 : base ≤ n := Nat.le_of_mod_lt (by rwa [← g] at h0)
        rw [addAux_eq_cons_zero_addAux_of_eq_nil_of_eq_nil n rfl rfl hb (And.intro h3 g)]
        rw [toNatAux_cons, ih (n / base) (Nat.div_lt_self h0 hb)]
        rw [Nat.zero_add, Nat.mul_div_eq_iff_dvd.mpr (Nat.dvd_of_mod_eq_zero g)]
      else
        have h3 : 0 < n % base := Nat.pos_iff_ne_zero.mpr g
        have h4 : n % base < base := Nat.mod_lt n (Nat.lt_trans (by decide) hb)
        rw [h2, addAux_add_eq_append_addAux_addAux (n % base) (n / base) rfl rfl hb (And.intro h3 h4)]
        rw [addAux_eq_singleton (n % base) rfl rfl hb (And.intro h3 h4), List.singleton_append]
        rw [toNatAux_cons, ih (n / base) (Nat.div_lt_self h0 hb)]
        simp only [Nat.mul_comm]
-/
end OfNat

/-
TODO : change to new type definition

section Rebase


def rebase (n : Numeral) (base : Nat) (hb : 1 < base) : Numeral :=
  ofNat (n.toNat) base hb

@[simp]
theorem rebase_base_eq_base (n : Numeral) (base : Nat) (hb : 1 < base) : (rebase n base hb).base = base := by
  unfold rebase ofNat toNat
  rfl

end Rebase

section Add

def add (a b : Numeral) (_: a.base = b.base) : Numeral where
  digits := addAux a.digits b.digits 0 a.base a.baseGtOne
  base := a.base
  baseGtOne := a.baseGtOne
  allDigitsLtBase := all_addAux_digits_lt_base 0 a.baseGtOne
  noTrailingZeros := addAux_noTrailingZeros_of_noTrailingZeros 0 a.noTrailingZeros b.noTrailingZeros a.baseGtOne

theorem add_nil_iff_and_nil_nil {a b : Numeral} (h : a.base = b.base) :
  (add a b h).digits = [] ↔ a.digits = [] ∧ b.digits = [] := by
  unfold add
  simp only [addAux_eq_nil_iff, true_and]

theorem add_zero_iff_or_zero_zero {a b : Numeral} (h : a.base = b.base) :
  (add a b h).digits = [0]
    ↔ a.digits = [0] ∧ b.digits = [] ∨ a.digits = [] ∧ b.digits = [0] ∨ a.digits = [0] ∧ b.digits = [0] := by
  unfold add
  simp only [addAux_eq_zero_iff, true_and]

theorem add_comm {a b : Numeral} (h : a.base = b.base) : add a b h = add b a (by simp only [h]) := by
  have hblt : (b.digits.all fun x ↦ decide (x < b.base)) = true := b.allDigitsLtBase
  have hblt' : (b.digits.all fun x ↦ decide (x < a.base)) = true := by rwa [← h] at hblt
  have hd : addAux a.digits b.digits 0 a.base a.baseGtOne = addAux b.digits a.digits 0 a.base a.baseGtOne :=
    addAux_comm a.baseGtOne
  unfold add
  simp only [hd]
  simp only [h]

def hAdd (a b : Numeral) : Numeral :=
  if h : a.base = b.base then
    add a b h
  else
    if a.base < b.base then
      add (rebase a b.base b.baseGtOne) b rfl
    else
      add a (rebase b a.base a.baseGtOne) rfl

theorem hAdd_comm (a b : Numeral) : hAdd a b = hAdd b a := by
  unfold hAdd
  if  h : a.base = b.base then
    simp only [h]
    exact add_comm h
  else
    if g : a.base < b.base then
      have g' : ¬ b.base < a.base := Nat.not_lt_of_gt g
      simp only [h, ↓reduceDIte, g, ↓reduceIte, eq_comm, g']
      have harb : (rebase a b.base b.baseGtOne).base = b.base :=
        rebase_base_eq_base a b.base b.baseGtOne
      exact add_comm harb
    else
      have he : a.base = b.base ↔ b.base = a.base := eq_comm
      have h' : ¬b.base = a.base := (iff_iff_iff_not_not.mp he).mp h
      have g' : b.base ≤ a.base := Nat.le_of_not_lt g
      have g'' : b.base < a.base := Nat.lt_of_le_of_ne g' h'
      simp only [h, g, g'', ↓reduceDIte, ↓reduceIte, eq_comm]
      have hbrb : (rebase b a.base a.baseGtOne).base = a.base :=
        rebase_base_eq_base b a.base a.baseGtOne
      exact add_comm hbrb

instance instCommutativeHAddNumerals : Std.Commutative hAdd := ⟨hAdd_comm⟩
instance instHAddNumerals : HAdd Numeral Numeral Numeral := ⟨hAdd⟩

theorem toNat_add_left_distrib_of_nil {a b : Numeral} (h : a.base = b.base) (hbn : b.digits = []) :
  toNat (add a b h) = a.toNat + b.toNat := by
  simp only [add, toNat]
  rw [Numeral.addAux.eq_def, hbn]
  match ga: a.digits with
  | [] =>
    have : toNatAux [] a.base = 0 := toNatAux_nil_eq_zero
    simp_all only []
  | x::xs =>
    have h1 : a.digits.all (· < a.base) := a.allDigitsLtBase
    have h2 : (x :: xs).all (· < a.base) := by rwa [ga] at h1
    have h3 : x < a.base ∧ xs.all (· < a.base) := allDigitsLtBase_cons.mp h2
    have h4 : x / a.base = 0 := Nat.div_eq_zero_iff.mpr (.inr h3.left)
    have h5 : x % a.base = x := (Nat.mod_eq_iff_lt (Nat.ne_zero_of_lt a.baseGtOne)).mpr h3.left
    have h6 : addAux xs [] 0 a.base a.baseGtOne = xs :=
      addAux_eq_of_nil_of_zero 0 h3.right rfl rfl a.baseGtOne
    have h7 : toNatAux [] b.base = 0 := toNatAux_nil_eq_zero
    simp only [] -- condense match
    rw [Nat.add_zero, h4, h5, h6, h7, Nat.add_zero]

theorem toNat_add_left_distrib {a b : Numeral} (h : a.base = b.base) :
  toNat (add a b h) = a.toNat + b.toNat := by
  unfold toNat add
  simp only [← h]
  exact toNatAux_addAux_left_distrib 0 a.baseGtOne

end Add

-/
end Numeral
end Numerals
