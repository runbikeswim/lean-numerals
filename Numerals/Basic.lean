/-
Copyright (c) 2025 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Corollaries

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
structure Numeral where
  digits : List Nat
  base: Nat := 10
  baseGtOne : 1 < base
  allDigitsLtBase : digits.all (· < base)
  noTrailingZeros : (h : digits ≠ []) → digits ≠ [0] → digits.getLast h ≠ 0
deriving Repr, DecidableEq

section AlternativeTypes

inductive Numeral' : Nat → Type where
  | nil : (base : Nat) → (hb : 1 < base ) → Numeral' base
  | cons : (m : Nat) → {base : Nat} → (n : Numeral' base) → (hn : m < base) → Numeral' base

structure Numeral'' (base : Nat := 10) (hb : 1 < base) where
  digits : List Nat
  allDigitsLtBase : digits.all (· < base)
  noTrailingZeros : (h : digits ≠ []) → digits ≠ [0] → digits.getLast h ≠ 0

end AlternativeTypes

namespace Numeral

section Groundwork

/-!
covers the two representations of zero as `Numeral`
-/
def isZero (a : Numeral) : Prop := a.digits = [] ∨ a.digits = [0]

def decIsZero (a : Numeral) : Decidable a.isZero :=
  if h : a.digits = [] ∨ a.digits = [0] then
    isTrue h
  else
    isFalse h

instance instDecidableIsZero {a : Numeral} : Decidable a.isZero := a.decIsZero

instance instInhabitedNumeral : Inhabited Numeral := ⟨{
    digits := [0],
    base := 10,
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, List.cons_ne_self,
                        not_false_eq_true, not_true_eq_false,
                        List.getLast_singleton, imp_self]
  }⟩

/-!
returns the hexadecimal digit of a number between 0 and 15 (including)

The use of `decide (digit < 16)` as type of `h` - instead of the
more straightforward `digit < 16` - is motivated by
https://github.com/leanprover/lean4/issues/9292.
-/
def toHexDigit (digit : Nat) (h : decide (digit < 16)) : String :=
  match digit with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => s!"{digit}"
  | 10 => "a"
  | 11 => "b"
  | 12 => "c"
  | 13 => "d"
  | 14 => "e"
  | 15 => "f"

/-!
maps an empty list of digits to `[0]` or reverses them otherwise
-/
def normalizeDigits (a : List Nat) : List Nat := if a = [] then [0] else a.reverse

/-!
asserts that `normalizeDigits` only returns `[0]` or the reversed input
-/
theorem normalizeDigits_eq_or {a : List Nat} :
  normalizeDigits a = [0] ∨ (normalizeDigits a) = a.reverse := by
  by_cases ha : a = [] <;> simp only [normalizeDigits, ha, reduceIte, true_or, or_true]

/-!
asserts that all digits returned by `normalizeDigits_allLtBase_of_allLtBase` are less than
`base` if this holds true for the input
-/
theorem normalizeDigits_allLtBase_of_allLtBase {a : List Nat} {base : Nat} (hb : 1 < base) (haa : a.all (· < base)):
  (normalizeDigits a).all (· < base) := by
  have g : normalizeDigits a = [0] ∨ (normalizeDigits a) = a.reverse := normalizeDigits_eq_or
  cases g with
  | inl hl =>
    have : decide (0 < base) = true := by rw [decide_eq_true_eq]; exact Nat.lt_trans (by decide) hb
    rwa [hl, List.all, List.all_nil, Bool.and_true]
  | inr hr => rwa [hr, List.all_reverse]

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
def toString (n : Numeral) : String :=
  helper (normalizeDigits n.digits) n.base
    (normalizeDigits_allLtBase_of_allLtBase n.baseGtOne n.allDigitsLtBase) where
  helper (digits : List Nat) (base : Nat) (ha : digits.all (· < base)) :=
    match base with
    | 2
    | 8  => s!"{String.join (digits.map (s!"{·}"))}({base})"
    | 10 => s!"{String.join (digits.map (s!"{·}"))}"
    | 16 => s!"{String.join (digits.mapWithAll (· < 16) ha toHexDigit)}(16)"
    | _  => ",".intercalate (digits.map (fun d : Nat => s!"{d}")) ++ s!"({base})"

instance instToStringNumeral : ToString Numeral := ⟨toString⟩

@[simp]
def allDigitsLtBase_cons {n base : Nat} {a : List Nat} :
  (n::a).all (· < base) ↔ n < base ∧ a.all (· < base) := by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]

end Groundwork

section TrailingZeros

theorem noTrailingZeros_cons_of_ne_zero (n : Nat) {a : List Nat} (hdnz : a ≠ [0])
  (hdntz : (hdnn : a ≠ []) → a ≠ [0] → a.getLast hdnn ≠ 0):
  (h : n::a ≠ []) → n::a ≠ [0] → (n::a).getLast h ≠ 0 := by
  intro h hndnz
  match a with
  | [] =>
    have hnn : ¬n = 0 := by rwa [← List.singleton_inj]
    rwa [List.getLast_singleton h]
  | head::tail =>
    rw [List.getLast_cons_cons]
    exact (hdntz (List.cons_ne_nil head tail)) hdnz

theorem ne_zero_of_noTrailingZeros_cons {n : Nat} {a : List Nat}
  (hntz : (h : n::a ≠ []) → n::a ≠ [0] → (n::a).getLast h ≠ 0) : a ≠ [0] := by
  have h : n::a ≠ [] := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  if g : n::a = [0] then
    simp only [(List.cons_singleton_iff_and_eq_nil.mp g).right,
      ne_eq, List.ne_cons_self, not_false_eq_true]
  else
    false_or_by_contra; rename _ => hc
    have h1 : a ≠ [] := by simp only [hc, ne_eq, List.cons_ne_self, not_false_eq_true]
    have h2 : (n :: a).getLast h ≠ 0 := hntz h g
    have h3 : a.getLast h1 ≠ 0 := by rwa [List.getLast_cons h1] at h2
    have h4 : a.getLast h1 = 0 := by simp only [hc, List.getLast_singleton]
    contradiction

@[simp]
theorem noTrailingZeros_of_noTrailingZeros_cons {n : Nat} {a : List Nat}
  (hntc : (h : n::a ≠ []) → n::a ≠ [0] → (n::a).getLast h ≠ 0) :
  (hdnn : a ≠ []) → a ≠ [0] → a.getLast hdnn ≠ 0 := by
  intro hdnn hdnz
  have h1 : n::a ≠ [] := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  have h2 : n::a ≠ [0] := by
    false_or_by_contra; rename _ => hc
    exact absurd (List.cons_singleton_iff_and_eq_nil.mp hc).right hdnn
  have h3 : (n::a).getLast h1 = a.getLast hdnn := List.getLast_cons hdnn
  have h4 : (n::a).getLast h1 ≠ 0 := hntc h1 h2
  rwa [h3] at h4

end TrailingZeros

section ToNatAux

/-
tail recursive
-/
def toNatAux (a : List Nat) (base factor acc : Nat) : Nat × Nat :=
  match a with
  | [] => (factor, acc)
  | x::xs => toNatAux xs base (factor * base) (x * factor + acc)

def toNatAux' (a : List Nat) (base : Nat) : Nat :=
  (helper a base 1 0).snd where
  helper (a : List Nat) (base factor acc : Nat) : Nat × Nat :=
    match a with
    | [] => (factor, acc)
    | x::xs => helper xs base (factor * base) (x * factor + acc)

/-
not tail recursive
-/
def toNatAux'' (a : List Nat) (base : Nat) : Nat  :=
  match a with
  | [] => 0
  | x::xs => x + base * (toNatAux'' xs base)

theorem toNatAux_nil {base factor acc : Nat} : toNatAux [] base factor acc = (factor, acc) := by
  unfold toNatAux
  rfl

theorem toNatAux'_helper_nil {base factor acc : Nat} : toNatAux'.helper [] base factor acc  = (factor, acc) := by
  unfold toNatAux'.helper
  rfl

theorem toNatAux'_nil_eq_zero {base : Nat} : toNatAux' [] base = 0 := by
  unfold toNatAux'
  rfl

theorem toNatAux_factor_acc {a : List Nat} {base factor acc : Nat} :
  (toNatAux a base factor acc).snd = acc + factor * (toNatAux a base 1 0).snd := by
  induction a generalizing factor acc with
  | nil => simp_all only [toNatAux_nil, Nat.mul_zero, Nat.add_zero]
  | cons head tail ih =>
    unfold toNatAux
    simp only [Nat.one_mul, Nat.mul_one, Nat.add_zero]
    rw [ih, Nat.add_comm (head * factor) acc]
    rw (occs := .pos [2]) [ih]
    rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm]

theorem toNatAux_cons_acc {a : List Nat} {n base : Nat} :
  (toNatAux (n::a) base 1 0).snd = (toNatAux (0::a) base 1 n).snd := by
  unfold toNatAux
  simp only [Nat.one_mul, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.add_zero]

theorem toNatAux_cons {a : List Nat} {n base : Nat} :
  (toNatAux (n::a) base 1 0).snd = n + base * (toNatAux a base 1 0).snd := by
  rw [Numeral.toNatAux.eq_def]
  simp only [Nat.one_mul, Nat.mul_one, Nat.add_zero]
  exact toNatAux_factor_acc

theorem toNatAux'_helper_factor_acc {a : List Nat} {base factor acc : Nat} :
  (toNatAux'.helper a base factor acc).snd = acc + factor * (toNatAux'.helper a base 1 0).snd := by
  induction a generalizing factor acc with
  | nil => simp_all only [toNatAux'_helper_nil, Nat.mul_zero, Nat.add_zero]
  | cons head tail ih =>
    unfold toNatAux'.helper
    simp only [Nat.one_mul, Nat.mul_one, Nat.add_zero]
    rw [ih, Nat.add_comm (head * factor) acc]
    rw (occs := .pos [2]) [ih]
    rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm]

theorem toNatAux'_cons {xs : List Nat} {x base : Nat} :
  toNatAux' (x::xs) base = x + base * toNatAux' xs base := by
  rw [toNatAux'.eq_def, toNatAux'.helper.eq_def]
  simp only [Nat.one_mul, Nat.mul_one, Nat.add_zero]
  rw [toNatAux'.eq_def]
  exact toNatAux'_helper_factor_acc

theorem toNatAux_cons_factor_acc {a : List Nat} {n base factor acc : Nat} :
  (toNatAux (n::a) base factor acc).snd =
    acc + factor * n + factor * base * (toNatAux a base 1 0).snd := by
  rw [toNatAux_factor_acc, toNatAux_cons, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

theorem toNatAux'_cons_eq {xs : List Nat} {x base : Nat} :
  toNatAux' (x::xs) base  = x + base * (toNatAux' xs base) := by
  rw [toNatAux'.eq_def, toNatAux'.helper.eq_def]
  simp only []
  rw [toNatAux'.eq_def, toNatAux'_helper_factor_acc, Nat.mul_one, Nat.one_mul, Nat.add_zero]

end ToNatAux

section toNat

def toNat (n : Numeral) : Nat := (toNatAux n.digits n.base 1 0).snd

end toNat

section Prune

def prune (a : List Nat) (n base : Nat) (hb : 1 < base) : List Nat :=
  match a, n with
  | [], 0 => []
  | [], k + 1 =>
    -- for asserting termination
    have h : 0 < (k + 1) := Nat.zero_lt_succ k
    have : (k + 1) / base < k + 1 := Nat.div_lt_self h hb
    ((k + 1) % base)::(prune [] ((k + 1) / base) base hb)
  | x::xs, n => ((x + n) % base)::(prune xs ((x + n) / base) base hb)
  termination_by (a.length, n)

theorem toNatAux'_prune_eq_add_toNatAux' {a : List Nat} {n base : Nat} (hb : 1 < base) :
  toNatAux' (prune a n base hb) base = n + toNatAux' a base := by
  induction a generalizing n with
  | nil =>
    induction n using Nat.strongRecOn with
    | _ l ihl =>
      match gl : l with
      | 0 =>
        rw [prune.eq_def, toNatAux'.eq_def, toNatAux'.helper.eq_def]
        simp_all only [Nat.not_lt_zero, false_implies, implies_true, Nat.add_zero]
      | k + 1 =>
        have h1 : (k + 1) / base < k + 1 := Nat.div_lt_self (Nat.succ_pos k) hb
        rw [prune.eq_def, toNatAux'_cons_eq, ihl ((k + 1) / base) h1, Nat.mul_add, ← Nat.add_assoc]
        rw [Nat.mod_add_div (k + 1) base, toNatAux'_nil_eq_zero, Nat.mul_zero]
  | cons x xs iha =>
    rw [prune.eq_def]
    simp only [toNatAux'_cons, iha, Nat.mul_add, ← Nat.add_assoc, Nat.mod_add_div (x + n) base, Nat.add_comm]

end Prune

section AddDigits

def addDigits : List Nat → List Nat → List Nat
  | [], [] => []
  | x::xs, [] => x::xs
  | [], y::ys => y::ys
  | x::xs, y::ys => (x + y)::(addDigits xs ys)

end AddDigits

section AddAux

def addAux (a b : List Nat) (n base : Nat) (hb : 1 < base) : List Nat :=
  match a, b, hn: n with
  | [], [], 0 => []
  | [], [], k + 1 =>
    -- for asserting termination
    have h : 0 < (k + 1) := Nat.zero_lt_succ k
    have : (k + 1) / base < k + 1 := Nat.div_lt_self h hb
    ((k + 1) % base)::(addAux [] [] ((k + 1) / base) base hb)
  | x::xs, [], n => ((x + n) % base)::(addAux xs [] ((x + n) / base) base hb)
  | [], y::ys, n => ((y + n) % base)::(addAux [] ys ((y + n) / base) base hb)
  | x::xs, y::ys, n => ((x + y + n) % base)::(addAux xs ys ((x + y + n) / base) base hb)
  termination_by (a.length + b.length, n)

theorem addAux_eq_prune_addDigits {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = prune (addDigits a b) n base hb := by
  induction a generalizing b n with
  | nil =>
    induction b generalizing n with
    | nil =>
      induction n using Nat.strongRecOn with
      | _ l ihk =>
        if hl : l = 0 then
          rw [hl, addDigits.eq_def, addAux.eq_def, prune.eq_def]
        else
          rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
          have h1 : 0 < l := Nat.zero_lt_of_ne_zero hl
          have h2 : l / base < l := Nat.div_lt_self h1 hb
          have h3 : addAux [] [] (l / base) base hb = prune [] (l / base) base hb := by
            rw [ihk (l / base) h2, addDigits.eq_def]
          match hl : l with
          | 0 => simp only []
          | k + 1 => simp only [h3]
    | cons y ys ihy =>
      rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
      simp only []
      have h1 : addDigits [] ys = ys := by
          rw [addDigits.eq_def]
          match hys : ys with
          | [] => simp only []
          | y'::ys' => simp only []
      have h2 : addAux [] ys ((y + n) / base) base hb = prune ys ((y + n) / base) base hb := by
        rw [h1] at ihy
        exact ihy
      rw [List.cons.injEq]
      exact And.intro rfl h2
  | cons x xs ihx =>
    match hb : b with
    | [] =>
      rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
      simp only []
      have h1 : addDigits xs [] = xs := by
        rw [addDigits.eq_def]
        match hxs : xs with
        | [] => simp only []
        | x'::xs' => simp only []
      rw [List.cons.injEq]
      rw (occs := .pos [2]) [← h1]
      exact And.intro rfl ihx
    | y::ys  =>
      rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
      simp only []
      rw [List.cons.injEq]
      exact And.intro rfl ihx

theorem addAux_eq_nil_iff {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = [] ↔ n = 0 ∧ a = [] ∧ b = [] := by
  constructor
  · intro h
    match ga : a, gb : b, gn : n with
    | [], [], 0 => simp only [and_self]
    | [], [], k + 1 => simp only [addAux, reduceCtorEq] at h
    | x::xs, [], n => simp only [addAux, reduceCtorEq] at h
    | [], y::ys, n => simp only [addAux, reduceCtorEq] at h
    | x::xs, y::ys, n => simp only [addAux, reduceCtorEq] at h
  · intro h
    simp only [h.right.left, h.right.right, h.left, addAux]

theorem addAux_eq_singleton {a b : List Nat} (n : Nat) {base : Nat}
  (han : a = []) (hbn : b = []) (hb : 1 < base) (hn : 0 < n ∧ n < base) :
  addAux a b n base hb = [n] := by
  have hnm : n % base = n := Nat.mod_eq_of_lt hn.right
  have hln : 0 < n := hn.left
  have hnd : n / base = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hn.right)
  rw [Numeral.addAux.eq_def]
  match ga : a, gb : b, gn: n with
  | [], [], k + 1 => simp only [List.cons.injEq, hnm, true_and, hnd, addAux_eq_nil_iff hb]

theorem addAux_comm {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = addAux b a n base hb := by
  fun_induction addAux a b n base hb with
  | case1 => rw [addAux]
  | case2 => rw [addAux]
  | case3 _ _ _ ih => rw [addAux]; rw [ih]
  | case4 _ _ _ ih => rw [addAux]; rw [ih]
  | case5 x _ y _ _ ih => rw [addAux]; rw [ih]; rw [Nat.add_comm y x]

theorem toNatAux_addAux_nil_nil_eq {a b : List Nat} {n base : Nat} (hb : 1 < base) (hae : a = []) (hbe : b = []) :
  (toNatAux (addAux a b n base hb) base 1 0).snd = n := by
  induction n using Nat.strongRecOn with
  | _ l ih =>
    if hl : l = 0 then
      rw [addAux.eq_def]
      simp only [Nat.succ_eq_add_one]
      match ga : a, gb : b, gl: l with
      | [], [], 0 => simp only [toNatAux]
    else
      have h1 : 0 < l := Nat.zero_lt_of_ne_zero hl
      have h2 : l / base < l := Nat.div_lt_self h1 hb
      rw [addAux.eq_def]
      match ga : a, gb : b, gl: l with
      | [], [], k + 1 =>
        simp only []
        rw [toNatAux_cons, ih ((k + 1) / base) h2]
        exact Nat.mod_add_div (k + 1) base

theorem toNatAux_addAux_eq_of_zero {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  (toNatAux (addAux a b 0 base hb) base 1 0).snd =
    match a, b with
    | [], [] => 0
    | x::xs, [] => x + base * (toNatAux (addAux xs [] 0 base hb) base 1 0).snd
    | [], y::ys => y + base * (toNatAux (addAux [] ys 0 base hb) base 1 0).snd
    | x::xs, y::ys => x + y + base * (toNatAux (addAux xs ys 0 base hb) base 1 0).snd := by
  induction a with
  | nil =>
    induction b with
    | nil =>
      have h1 : addAux [] [] 0 base hb = [] := by rw [addAux.eq_def]
      have h2 : (toNatAux [] base 1 0).snd = 0 := by rw [toNatAux.eq_def]
      rw [h1, h2]
    | cons y' ys' ihy =>
      sorry
  | cons x' xs' ihx =>
    induction b with
    | nil =>
      sorry
    | cons y' ys' ihy =>
      sorry

theorem toNatAux_addAux_eq {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  (toNatAux (addAux a b n base hb) base 1 0).snd =
    match a, b with
    | [], [] => n
    | x::xs, [] => x + n + base * (toNatAux (addAux xs [] 0 base hb) base 1 0).snd
    | [], y::ys => y + n + base * (toNatAux (addAux [] ys 0 base hb) base 1 0).snd
    | x::xs, y::ys => x + y + n + base * (toNatAux (addAux xs ys 0 base hb) base 1 0).snd := by
  induction n using Nat.strongRecOn with
  | _ l ih =>
    if hl : l = 0 then
      sorry
    else
      sorry

theorem addAux_nil_zero_eq {a b : List Nat} {n base : Nat} (hn : n = 0) (hb : 1 < base)
  (halt : a.all (· < base)) (hbn : b = []):
  addAux a b n base hb = a := by
  fun_induction addAux a b n base hb with
  | case1 => rfl
  | case2 => contradiction
  | case3 x xs n ih =>
    have hxm : x % base = x := Nat.mod_eq_of_lt (allDigitsLtBase_cons.mp halt).left
    have hxd : (x + n) / base = 0 := by
      rw [hn, Nat.add_zero]
      exact Nat.div_eq_of_lt (allDigitsLtBase_cons.mp halt).left
    rw [ih hxd (allDigitsLtBase_cons.mp halt).right hbn, hn, Nat.add_zero, hxm]
  | case4 => contradiction
  | case5 => contradiction

theorem all_addAux_digits_lt_base {a b : List Nat} (n : Nat) {base : Nat} (hb : 1 < base) :
  (addAux a b n base hb ).all (· < base) := by
  have hb0 : 0 < base := Nat.lt_trans (by decide) hb
  fun_induction addAux with
  | case1 => exact List.all_nil
  | case2 k _ _ ih =>
    simp only [List.all_cons, Nat.mod_lt k.succ hb0, decide_true, ih, Bool.and_self]
  | case3 x _ n ih =>
    simp only [List.all_cons, Nat.mod_lt (x + n) hb0, decide_true, ih, Bool.and_self]
  | case4 y _ n ih =>
    simp only [List.all_cons, Nat.mod_lt (y + n) hb0, decide_true, ih, Bool.and_self]
  | case5 x _ y _ n ih =>
    simp only [List.all_cons, Nat.mod_lt (x + y + n) hb0, decide_true, ih, Bool.and_self]

theorem addAux_eq_zero_iff {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = [0] ↔ n = 0 ∧ (a = [0] ∧ b = [] ∨ a = [] ∧ b = [0] ∨ a = [0] ∧ b = [0]) := by
  rw [Numeral.addAux.eq_def]
  constructor
  · intro h
    match ga : a, gb : b, gn : n with
    | [], [], 0 => contradiction
    | [], [], k + 1 =>
      have h1 : (k + 1) % base = 0 := (List.cons_eq_cons.mp h).left
      have h2 : (k + 1) / base = 0 := ((addAux_eq_nil_iff hb).mp (List.cons_eq_cons.mp h).right).left
      have h3 : (k + 1) % base = k + 1 := Nat.mod_eq_of_lt (Nat.lt_of_div_eq_zero (Nat.gt_zero_of_gt_one hb) h2)
      have h4 : k + 1 = 0 := by rwa [h3] at h1
      contradiction
    | x::xs, [], n =>
      have h1 : (x + n) % base = 0 := (List.cons_eq_cons.mp h).left
      have h2 : xs = [] := ((addAux_eq_nil_iff hb).mp (List.cons_eq_cons.mp h).right).right.left
      have h3 : (x + n) / base = 0 := ((addAux_eq_nil_iff hb).mp (List.cons_eq_cons.mp h).right).left
      have h4 : (x + n) < base := Nat.lt_of_div_eq_zero (Nat.gt_zero_of_gt_one hb) h3
      have h5 : (x + n) = 0 := by rwa [Nat.mod_eq_of_lt h4] at h1
      have h6 : x = 0 ∧ n = 0 := Nat.add_eq_zero_iff.mp h5
      have h7 : x::xs = [0] := by rw [List.cons.injEq]; exact And.intro h6.left h2
      exact And.intro h6.right (.inl (And.intro h7 rfl))
    | [], y::ys, n =>
      have h1 : (y + n) % base = 0 := (List.cons_eq_cons.mp h).left
      have h2 : ys = [] := ((addAux_eq_nil_iff hb).mp (List.cons_eq_cons.mp h).right).right.right
      have h3 : (y + n) / base = 0 := ((addAux_eq_nil_iff hb).mp (List.cons_eq_cons.mp h).right).left
      have h4 : (y + n) < base := Nat.lt_of_div_eq_zero (Nat.gt_zero_of_gt_one hb) h3
      have h5 : (y + n) = 0 := by rwa [Nat.mod_eq_of_lt h4] at h1
      have h6 : y = 0 ∧ n = 0 := Nat.add_eq_zero_iff.mp h5
      have h7 : y::ys = [0] := by rw [List.cons.injEq]; exact And.intro h6.left h2
      exact And.intro h6.right (.inr (.inl (And.intro rfl h7)))
    | x::xs, y::ys, n =>
      have h1 : (x + y + n) % base = 0 := (List.cons_eq_cons.mp h).left
      have h2 : xs = [] ∧ ys = [] := ((addAux_eq_nil_iff hb).mp (List.cons_eq_cons.mp h).right).right
      have h3 : (x + y + n) / base = 0 := ((addAux_eq_nil_iff hb).mp (List.cons_eq_cons.mp h).right).left
      have h4 : (x + y + n) < base := Nat.lt_of_div_eq_zero (Nat.gt_zero_of_gt_one hb) h3
      have h5 : (x + y + n) = 0 := by rwa [Nat.mod_eq_of_lt h4] at h1
      have h6 : x = 0 ∧ y = 0 ∧ n = 0 := by rwa [Nat.add_eq_zero_iff, Nat.add_eq_zero_iff, and_assoc] at h5
      have h7 : x::xs = [0] := by rw [List.cons.injEq]; exact And.intro h6.left h2.left
      have h8 : y::ys = [0] := by rw [List.cons.injEq]; exact And.intro h6.right.left h2.right
      exact And.intro h6.right.right (.inr (.inr (And.intro h7 h8)))
  · intro h
    match ga : a, gb : b, gn : n with
    | [], [], 0 =>
      simp only [List.ne_cons_self, and_true, and_false, and_self, or_self] at h
    | [], [], k + 1 =>
      simp only [Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, List.ne_cons_self, and_true, and_self, or_self] at h
    | x::xs, [], n =>
      simp_all only [List.cons.injEq, and_true, reduceCtorEq, List.ne_cons_self, and_self, and_false, or_self, or_false,
        Nat.add_zero, Nat.zero_mod, Nat.zero_div, addAux]
    | [], y::ys, n =>
      simp_all only [List.ne_cons_self, reduceCtorEq, and_self, List.cons.injEq, true_and, false_and, or_false, false_or,
        Nat.add_zero, Nat.zero_mod, Nat.zero_div, addAux]
    | x::xs, y::ys, n =>
      simp_all only [List.cons.injEq, reduceCtorEq, and_false, false_and, false_or, Nat.add_zero,
        Nat.zero_mod, Nat.zero_div, addAux]

theorem addAux_ne_zero_of_ne_zero_of_ne_zero {a b : List Nat}
  (hanz : a ≠ [0]) (hbnz : b ≠ [0]) (n : Nat) {base : Nat} (hb : 1 < base) :
  addAux a b n base hb ≠ [0] := by
  have : ¬(n = 0 ∧ (a = [0] ∧ b = [] ∨ a = [] ∧ b = [0] ∨ a = [0] ∧ b = [0])) := by
      rw [
        Classical.not_and_iff_not_or_not, not_or, Classical.not_and_iff_not_or_not, not_or,
        Classical.not_and_iff_not_or_not, Classical.not_and_iff_not_or_not, ← ne_eq, ← ne_eq, ← ne_eq,
      ]
      exact .inr (And.intro (.inl hanz) (And.intro (.inr hbnz) (.inl hanz)))
  exact (iff_iff_iff_not_not.mp (addAux_eq_zero_iff hb)).mpr this

theorem addAux_noTrailingZeros_of_noTrailingZeros {a b : List Nat} (n : Nat) {base : Nat}
  (hantz : (h : a ≠ []) → a ≠ [0] → a.getLast h ≠ 0)
  (hbntz : (h : b ≠ []) → b ≠ [0] → b.getLast h ≠ 0)
  (hb : 1 < base) :
  (h : addAux a b n base hb ≠ []) → addAux a b n base hb ≠ [0] → (addAux a b n base hb).getLast h ≠ 0 := by
  have h0 : ([] : List Nat) ≠ [0] := by decide
  fun_induction addAux with
  | case1 => intro _; contradiction
  | case2 k hn0 hltn ih =>
    have h1 : addAux [] [] ((k + 1) / base) base hb ≠ [0] :=
      addAux_ne_zero_of_ne_zero_of_ne_zero h0 h0 ((k + 1) / base) hb
    exact noTrailingZeros_cons_of_ne_zero (k.succ % base) h1 (ih hantz hbntz)
  | case3 x xs n ih =>
    have h1 : xs ≠ [0] := ne_zero_of_noTrailingZeros_cons hantz
    have h2 : (h : xs ≠ []) → xs ≠ [0] → xs.getLast h ≠ 0 := noTrailingZeros_of_noTrailingZeros_cons hantz
    have h3 : addAux xs [] ((x + n) / base) base hb ≠ [0] :=
      addAux_ne_zero_of_ne_zero_of_ne_zero h1 h0 ((x + n) / base) hb
    exact noTrailingZeros_cons_of_ne_zero ((x + n) % base) h3 (ih h2 hbntz)
  | case4 y ys n ih =>
    have h1 : ys ≠ [0] := ne_zero_of_noTrailingZeros_cons hbntz
    have h2 : (h : ys ≠ []) → ys ≠ [0] → ys.getLast h ≠ 0 := noTrailingZeros_of_noTrailingZeros_cons hbntz
    have h3 : addAux [] ys ((y + n) / base) base hb ≠ [0] :=
      addAux_ne_zero_of_ne_zero_of_ne_zero h0 h1 ((y + n) / base) hb
    exact noTrailingZeros_cons_of_ne_zero ((y + n) % base) h3 (ih hantz h2)
  | case5 x xs y ys n ih =>
    have h1 : xs ≠ [0] := ne_zero_of_noTrailingZeros_cons hantz
    have h2 : (h : xs ≠ []) → xs ≠ [0] → xs.getLast h ≠ 0 := noTrailingZeros_of_noTrailingZeros_cons hantz
    have h3 : ys ≠ [0] := ne_zero_of_noTrailingZeros_cons hbntz
    have h4 : (h : ys ≠ []) → ys ≠ [0] → ys.getLast h ≠ 0 := noTrailingZeros_of_noTrailingZeros_cons hbntz
    have h5 : addAux xs ys ((x + y + n) / base) base hb ≠ [0] :=
      addAux_ne_zero_of_ne_zero_of_ne_zero h1 h3 ((x + y + n) / base) hb
    let  := ih h2 h4
    exact noTrailingZeros_cons_of_ne_zero ((x + y + n) % base) h5 (ih h2 h4)

theorem addAux_cons_nil_eq_cons_addAux {xs : List Nat} {x base n : Nat} (hb : 1 < base) :
  addAux (x::xs) [] n base hb = ((x + n) % base)::(addAux xs [] ((x + n) / base) base hb) := by
  rw [Numeral.addAux.eq_def]

theorem addAux_cons_cons_eq_cons_addAux {xs ys : List Nat} {x y base n : Nat} (hb : 1 < base) :
  addAux (x::xs) (y::ys) n base hb = ((x + y + n) % base)::(addAux xs ys ((x + y + n) / base) base hb) := by
  rw [Numeral.addAux.eq_def]

theorem addAux_eq_cons_zero_addAux_of_eq_nil_of_eq_nil {a b : List Nat} (n : Nat) {base : Nat}
  (han : a = []) (hbn : b = []) (hb : 1 < base) (hn : base ≤ n ∧ n % base = 0) :
  addAux a b n base hb = 0::(addAux a b (n / base) base hb) := by
  rw [Numeral.addAux.eq_def]
  have hne : n ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr (Nat.pos_of_one_lt (Nat.lt_of_lt_of_le hb hn.left))
  match ga : a, gb : b, gn : n with
  | [], [], k + 1 => simp only [hn.right]
  | [], [], 0 | x::xs, [], n | [], y::ys, n | x::xs, y::ys, n => contradiction

theorem addAux_eq_cons_zero_addAux_of_eq_nil_of_eq_nil' (n : Nat) {base : Nat} (hb : 1 < base)
  (hn : base ≤ n ∧ n % base = 0) :
  addAux [] [] n base hb = 0::(addAux [] [] (n / base) base hb) := by
  rw [Numeral.addAux.eq_def]
  have hne : n ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr (Nat.pos_of_one_lt (Nat.lt_of_lt_of_le hb hn.left))
  match gn : n with
  | 0 => contradiction
  | k + 1 => simp only [hn.right]

theorem addAux_nil_nil_eq_cons_addAux_of_zero_lt {n base : Nat} (hn : 0 < n) (hb : 1 < base) :
  addAux [] [] n base hb = (n % base)::(addAux [] [] (n / base) base hb) := by
  rw [Numeral.addAux.eq_def]
  match gn : n with
  | 0 => contradiction
  | k + 1 => simp_all only [Nat.zero_lt_succ, Nat.succ_eq_add_one]

theorem addAux_add_eq_append_addAux_addAux {a b : List Nat} (n m : Nat) {base : Nat}
  (han : a = []) (hbn : b = []) (hb : 1 < base) (hn : 0 < n ∧ n < base) :
  addAux a b (n + m * base) base hb = addAux a b n base hb ++ addAux a b m base hb := by
  have hb': 0 < base := Nat.lt_trans (by decide) hb
  have hs : addAux a b n base hb = [n] := addAux_eq_singleton n han hbn hb hn
  have hac : addAux a b n base hb ++ addAux a b m base hb = n::(addAux a b m base hb) := by
    rw [hs, List.singleton_append]
  have hgz : 0 < n + m * base := by
    calc 0 < n := hn.left
      _ ≤ n + m * base := Nat.le_add_right n (m * base)
  have hns : n + m * base ≠ 0 := Nat.ne_zero_of_lt hgz
  have hde : (n + m * base) / base = m := Nat.div_add_mul_eq n m hn.right
  have hme : (n + m * base) % base = n := Nat.mod_add_mul_eq n m hn.right
  rw [hac, Numeral.addAux.eq_def]
  simp [han, hbn]
  match gn : n + m * base with
  | 0 => contradiction
  | k + 1 =>
    simp only []
    rw [Nat.succ_eq_add_one] at gn
    rw [← gn, hde, hme]

theorem addAux_eq_of_nil_of_zero {a b : List Nat} (n : Nat) {base : Nat}
  (halt : a.all (· < base)) (hbn : b = []) (hn : n = 0) (hb : 1 < base) :
  addAux a b n base hb = a := by
  induction a with
  | nil => rw [hbn, hn]; exact (addAux_eq_nil_iff hb).mpr (And.intro rfl (And.intro rfl rfl))
  | cons head tail ih =>
    rw [Numeral.addAux.eq_def]
    match ga : head :: tail, gb : b, gn : n with
    | [], [], 0 | [], [], k + 1 => contradiction
    | x::xs, [], n' =>
      have h1 : head = x ∧ tail = xs := List.cons_eq_cons.mp ga
      have h2 : head < base ∧ tail.all (· < base) := allDigitsLtBase_cons.mp halt
      have h3 : x < base ∧ xs.all (· < base) := by rwa [h1.left, h1.right] at h2
      have h4 : x / base = 0 := Nat.div_eq_zero_iff.mpr (.inr h3.left)
      have h5 : x % base = x := (Nat.mod_eq_iff_lt (Nat.ne_zero_of_lt hb)).mpr h3.left
      simp only []
      rw [hn, Nat.add_zero, h4, h5, ← h1.left, ← h1.right, ← hn, ih h2.right]
    | [], y::ys, n | x::xs, y::ys, n => contradiction

theorem addAux_cons_nil_eq_addAux {xs : List Nat} {x n base : Nat} (hb : 1 < base) :
  addAux (x::xs) [] n base hb = addAux (0::xs) [] (x + n) base hb := by
  unfold addAux
  rw [Nat.zero_add]

theorem addAux_cons_cons_eq_addAux {xs ys: List Nat} {x y n base : Nat} (hb : 1 < base) :
  addAux (x::xs) (y::ys) n base hb = addAux (0::xs) (0::ys) (x + y + n) base hb := by
  unfold addAux
  rw [Nat.zero_add]

def a : List Nat := [11,2]
def b : List Nat := [3,2,1]
def bs : Nat := 13
def hb : 1 < bs := by decide
def acc : Nat := 15
def n : Nat := 12
def m : Nat := 13

theorem tbd02 {xs ys : List Nat} {x y n base : Nat} (hb : 1 < base) :
  (toNatAux (addAux (x::xs) (y::ys) n base hb) base 1 0).snd = (toNatAux (addAux (x::xs) (y::ys) 0 base hb) base 1 n).snd := by
  rw [Numeral.addAux.eq_def]
  simp only []
  induction n using Nat.strongRecOn with
  | ind n ih =>
    if h : n = 0 then
      rw [h, Nat.add_zero]
      rw (occs := .pos [2]) [addAux.eq_def]
      simp only []
      rw [Nat.add_zero]
    else
      if g : (x + y + n) < base then
        sorry
      else
        sorry

theorem tbd01 {a b : List Nat} {n m base factor acc : Nat} (hb : 1 < base) :
  (toNatAux (n % base::(addAux a b (n / base) base hb)) base 1 (m + acc)).snd =
    (toNatAux ((n + m) % base::(addAux a b ((n + m) / base) base hb)) base 1 acc).snd := by
    rw [toNatAux_cons_factor_acc, Nat.one_mul, Nat.one_mul, toNatAux_cons_factor_acc, Nat.one_mul, Nat.one_mul]
    -- (toNatAux (addAux a b (n / base) base hb) base 1 0)
    sorry

theorem toNatAux_addAux_cons_zero_eq {a b: List Nat} {n base factor : Nat} (hb : 1 < base) :
  (toNatAux (addAux (0::a) (0::b) 0 base hb) base factor n).snd =
    (toNatAux (addAux a b 0 base hb) base (base * factor) n).snd := by
  rw [Numeral.addAux.eq_def]
  simp only [Nat.zero_add, Nat.zero_mod, Nat.zero_div]
  rw [toNatAux_cons_factor_acc, Nat.mul_zero, Nat.add_zero, ← toNatAux_factor_acc, Nat.mul_comm]

theorem toNat_addAux_eq {a b: List Nat} (n acc : Nat) {base : Nat}
  (hb : 1 < base) (halt : a.all (· < base)) (hblt : b.all (· < base)) :
  (toNatAux (addAux a b n base hb) base 1 acc).snd =
    (toNatAux (addAux a b 0 base hb) base 1 (n + acc)).snd := by
  have h1 : addAux [] [] 0 base hb = [] := (addAux_eq_nil_iff hb).mpr (And.intro rfl (And.intro rfl rfl))
  rw [Numeral.addAux.eq_def]
  match ga : a, gb : b, gn : n with
  | [], [], 0 =>
    simp only [h1, Nat.zero_add]
  | [], [], k + 1 =>
    simp_all only [List.all_nil, Nat.succ_eq_add_one]
    induction k + 1 using Nat.strongRecOn generalizing acc with
    | _ n' ih =>
      simp only [toNatAux_cons_factor_acc, Nat.one_mul, toNatAux_nil]
      if hn : n' < base then
        rw [Nat.div_eq_of_lt hn, h1, Nat.mod_eq_of_lt hn, toNatAux_nil]
        simp only [Nat.mul_zero, Nat.add_zero, Nat.add_comm]
      else
        have h2 : 0 < n' := Nat.lt_of_lt_of_le (Nat.lt_trans (by decide) hb) (Nat.le_of_not_lt hn)
        have h3 : n' / base < n' := Nat.div_lt_self h2 hb
        have h4 : (toNatAux ((n' / base) % base :: addAux [] [] ((n' / base) / base) base hb) base 1 0).snd =
          (toNatAux [] base 1 (n' / base)).snd := ih (n' / base) h3 0
        have h5 : 0 < n' / base  := Nat.div_pos (Nat.le_of_not_lt hn) (Nat.lt_trans (by decide) hb)
        have h6 : (toNatAux (addAux [] [] (n' / base) base hb) base 1 0).snd = (toNatAux [] base 1 (n' / base)).snd := by
          rw [addAux_nil_nil_eq_cons_addAux_of_zero_lt h5 hb, h4]
        rw [h6, toNatAux_nil]
        simp only [] -- eliminate .snd
        rw [Nat.add_assoc, Nat.mod_add_div n' base, Nat.add_comm]
  | x::xs, [], n => simp_all; sorry
    /-
      ⊢ (toNatAux ((x + n) % base :: addAux xs [] ((x + n) / base) base hb) base 1 acc).snd =
          (toNatAux (addAux (x :: xs) [] 0 base hb) base 1 (n + acc)).snd

      going backwards
      (toNatAux (addAux (x :: xs) [] 0 base hb) base 1 (n + acc)).snd = <x < base>
        (toNatAux x::(addAux xs [] 0 base hb) base 1 (n + acc)).snd = <tbd>
          (toNatAux (x + n)::(addAux xs [] 0 base hb) base 1 acc).snd = <(x + n) % base + (x + n) / base ) = (x + n)>
            (toNatAux ((x + n) % base)::(addAux xs [] ((x + n) / base) base hb) base 1 acc).snd
    -/
  | [], y::ys, l => simp only []; sorry
  | x::xs, y::ys, l =>
    simp only []
    /-
      ⊢ (toNatAux ((x + y + l) % base :: addAux xs ys ((x + y + l) / base) base hb) base 1 acc).snd =
          (toNatAux (addAux (x :: xs) (y :: ys) 0 base hb) base 1 (l + acc)).snd
TODO:
      (toNatAux (addAux (x :: xs) (y :: ys) 0 base hb) base 1 (l + acc)).snd = <addAux_cons_cons_eq_cons_addAux with n = 0>
        (toNatAux ((x + y) % base)::(addAux xs ys ((x + y) / base) base hb) base 1 (l + acc)).snd = <tbd>
          (toNatAux ((x + y + l) % base)::(addAux xs ys ((x + y + l) / base) base hb) base 1 acc).snd
    -/
    sorry

/-
blueprint for toNatAux_addAux_left_distrib

(toNatAux (addAux x::xs y::ys n base hb) base 1 0).snd = <addAux_cons_cons_eq_addAux ✅>
  (toNatAux (addAux 0::xs 0::ys (x + y + n) base hb) base 1 0).snd = <toNat_addAux_eq ❌>
    (toNatAux (addAux 0::xs 0::ys 0 base hb) base 1 (x + y + n)).snd = <toNatAux_addAux_cons_zero_eq ✅>
      (toNatAux (addAux xs ys 0 base hb) base base (x + y + n)).snd = <toNatAux_factor_acc ✅>
        (x + y + n) + base * (toNatAux (addAux xs ys 0 base hb) base).snd  =
          (toNatAux (addAux xs ys 0 base hb) base base 0).snd + (x + y + n) = <ih‼️>
            (toNatAux xs base base 0).snd + (toNatAux ys base base 0).snd + x + y + n <toNatAux_addAux_cons_zero_eq ✅>
              (toNatAux 0::xs base 1 0).snd + (toNatAux 0::ys base 1 0).snd + x + y + n <Nat.add_comm>
                (toNatAux 0::xs base 1 0).snd + x + (toNatAux 0::ys base 1 0).snd + y + n <toNatAux_factor_acc ✅>
                  (toNatAux 0::xs base 1 x).snd + (toNatAux 0::ys base 1 y).snd + n <toNatAux_cons_acc ✅>
                    (toNatAux x::xs base 1 0).snd + (toNatAux y::ys base 1 0).snd + n


  toNatAux (addAux xs ys ((x + y + (n + m)) / base) base hb) base (factor * base)
    ((x + y + (n + m)) % base * factor + acc) =
  toNatAux (addAux xs ys ((x + y + n) / base) base hb) base (factor * base) ((x + y + n) % base * factor + (m + acc))
-/

theorem toNatAux_addAux_left_distrib {a b : List Nat} (n : Nat) {base : Nat} (hb : 1 < base):
  (toNatAux (addAux a b n base hb) base 1 0).snd =
    (toNatAux a base 1 0).snd + (toNatAux b base 1 0).snd + n := by
  unfold toNatAux addAux
  induction ga : a with
  | nil =>
    induction gb : b with
    | nil => simp_all; sorry
    | cons y ys ihb => simp_all; sorry
  | cons x xs iha =>
    induction gb : b with
    | nil => simp_all; sorry
    | cons y ys ihb => simp_all; sorry

end AddAux

section OfNat

def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : Numeral where
  digits := addAux [] [] n base hb -- prune [] n base hb
  base := base
  baseGtOne := hb
  allDigitsLtBase := all_addAux_digits_lt_base n hb
  noTrailingZeros := addAux_noTrailingZeros_of_noTrailingZeros n (by decide) (by decide) hb

theorem toNat_leftInverse_ofNat {n base : Nat} (hb : 1 < base) : toNat (ofNat n base hb) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    if h : n = 0 then
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

end OfNat

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
    have : toNatAux [] a.base 1 0 = (1, 0) := by rw [toNatAux_nil]
    simp_all only []
  | x::xs =>
    have h1 : a.digits.all (· < a.base) := a.allDigitsLtBase
    have h2 : (x :: xs).all (· < a.base) := by rwa [ga] at h1
    have h3 : x < a.base ∧ xs.all (· < a.base) := allDigitsLtBase_cons.mp h2
    have h4 : x / a.base = 0 := Nat.div_eq_zero_iff.mpr (.inr h3.left)
    have h5 : x % a.base = x := (Nat.mod_eq_iff_lt (Nat.ne_zero_of_lt a.baseGtOne)).mpr h3.left
    have h6 : addAux xs [] 0 a.base a.baseGtOne = xs :=
      addAux_eq_of_nil_of_zero 0 h3.right rfl rfl a.baseGtOne
    have h7 : (toNatAux [] b.base 1 0).snd = 0 := by rw [toNatAux_nil]
    simp only [] -- condense match
    rw [Nat.add_zero, h4, h5, h6, h7, Nat.add_zero]

theorem toNat_add_left_distrib {a b : Numeral} (h : a.base = b.base) :
  toNat (add a b h) = a.toNat + b.toNat := by
  unfold toNat add
  simp only [← h]
  exact toNatAux_addAux_left_distrib 0 a.baseGtOne

end Add

section SubAux

def subAuxCarry (x y base carry: Nat) (hb : 1 < base) : Nat × Nat :=
  if h : y ≤ x then
    (x - y, carry)
  else
    have h1 : x < y := Nat.lt_of_not_le h
    have h2 : x < x + base := Nat.lt_add_of_pos_right (Nat.lt_trans (by decide) hb)
    have : y - (x + base) < y - x := Nat.sub_lt_sub_left h1 h2
    subAuxCarry (x + base) y base (carry + 1) hb
  termination_by y - x

def cons? {α : Type} (a : α) (b : Option (List α)) : Option (List α) :=
  match b with
  | none => none
  | some l => some (a::l)

def subAux (a b : List Nat) (n base : Nat) (hb : 1 < base) : Option (List Nat) :=
  match a, b, n with
  | [], [], 0 => some []
  | [], [], _ + 1 => none
  | x::xs, [], n =>
    let (s, carry) := subAuxCarry x n base 0 hb
    cons? s (subAux xs [] carry base hb)
  | [], y::ys, n =>
    let (s, carry) := subAuxCarry y n base 0 hb
    cons? s (subAux ys [] carry base hb)
  | x::xs, y::ys, n =>
    let (s, carry) := subAuxCarry x (y + n) base 0 hb
    cons? s (subAux xs ys carry base hb)
  termination_by a.length + b.length

def discardTrailingZeros (a : List Nat) :=
  (helper a.reverse).reverse where
    helper : List Nat → List Nat
    | [] => []
    | [0] => [0]
    | 0::r => helper r
    | r => r

end SubAux

end Numeral
end Numerals
