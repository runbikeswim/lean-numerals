/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.AllDigitsBase
import Numerals.NoTrailingZero
import Numerals.Prune

namespace NumeralAux

section AddDigits

def addDigits : List Nat → List Nat → List Nat
  | [], [] => []
  | x::xs, [] => x::xs
  | [], y::ys => y::ys
  | x::xs, y::ys => (x + y)::(addDigits xs ys)

theorem addDigits_nil_eq {a : List Nat} : addDigits a [] = a := by
  rw [addDigits.eq_def]
  match ha : a with
  | [] | x::xs => rfl

theorem addDigits_eq_nil_iff_eq_nil_and_eq_nil {a b : List Nat} :
  addDigits a b = [] ↔ a = [] ∧ b = [] := by
  constructor
  · intro h
    match ga : a, gb : b with
    | [], [] => exact And.intro rfl rfl
    | x::xs, [] | [], y::ys | x::xs, y::ys => contradiction
  . intro h
    match a, b with | [], [] => rfl

theorem addDigits_cons_cons_eq_add_cons_addDigits {x y : Nat} {xs ys : List Nat} :
  addDigits (x::xs) (y::ys) = (x + y)::addDigits xs ys := rfl

theorem addDigits_comm {a b : List Nat} : addDigits a b = addDigits b a := by
  induction a generalizing b with
  | nil => match b with | [] | v::vs => rfl
  | cons u us iha =>
    match b with
    | [] => rfl
    | v::vs  =>
      unfold addDigits
      rw [List.cons.injEq, Nat.add_comm u v]
      exact And.intro rfl iha

end AddDigits

section NoTrailingZeroAux_AddDigits

theorem noTrailingZeroAux_addDigits_of {a b : List Nat}
  (hantz : noTrailingZeroAux a) (hbntz : noTrailingZeroAux b) :
  noTrailingZeroAux (addDigits a b) := by
  induction a generalizing b with
  | nil =>
    match b with
    | [] => intro _ ; contradiction
    | y::ys =>
      simp only [addDigits_comm, addDigits_nil_eq]
      exact hbntz
  | cons x xs ih =>
    match b with
    | [] => simp only [addDigits_nil_eq]; exact hantz
    | y::ys =>
      rw [noTrailingZeroAux_cons_iff_noTrailingZeroAux_and] at hantz hbntz
      have : noTrailingZeroAux (addDigits xs ys) := ih hantz.left hbntz.left
      simp only [addDigits_cons_cons_eq_add_cons_addDigits, noTrailingZeroAux_cons_iff_noTrailingZeroAux_and]
      simp only [this, true_and, addDigits_eq_nil_iff_eq_nil_and_eq_nil]
      intro h
      have h1 : 0 < x := Nat.pos_iff_ne_zero.mpr (hantz.right h.left)
      have h2 : 0 < x + y := Nat.add_pos_left h1 y
      exact Nat.pos_iff_ne_zero.mp h2

end NoTrailingZeroAux_AddDigits

section ToNatAux_AddDigits

theorem toNatAux_addDigits_left_distrib {a b : List Nat} {base : Nat} :
  toNatAux (addDigits a b) base = (toNatAux a base) + (toNatAux b base) := by
  have h1 : toNatAux [] base = 0 := by rw [toNatAux.eq_def, toNatAux.helper.eq_def]
  induction a generalizing b with
  | nil =>
    have h2 : addDigits [] b = b := by rw [addDigits.eq_def]; match b with | [] | v::vs => rfl
    rw [h2, h1, Nat.zero_add]
  | cons u us iha =>
    rw [addDigits.eq_def]
    match b with
    | [] => simp only [h1, Nat.add_zero]
    | v::vs =>
      simp only [toNatAux_cons_eq, iha]
      rw [Nat.add_assoc, Nat.add_comm, Nat.mul_add]
      rw (occs := .pos [3]) [Nat.add_comm]
      rw [← Nat.add_assoc]
      rw (occs := .pos [2, 1]) [Nat.add_comm]
      rw (occs := .pos [2]) [Nat.add_comm]
      rw [← Nat.add_assoc]

end ToNatAux_AddDigits

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

theorem addAux_eq_nil_iff {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = [] ↔ n = 0 ∧ a = [] ∧ b = [] := by
  constructor
  · intro h
    match ga : a, gb : b, gn : n with
    | [], [], 0 => simp only [and_self]
    | [], [], k + 1
    | x::xs, [], n
    | [], y::ys, n
    | x::xs, y::ys, n => simp only [addAux, reduceCtorEq] at h
  · intro h
    simp only [h.right.left, h.right.right, h.left, addAux]

theorem addAux_eq_singleton_of (n : Nat) {base : Nat}
  (hb : 1 < base) (hn : 0 < n ∧ n < base) :
  addAux [] [] n base hb = [n] := by
  have h1 : n % base = n := Nat.mod_eq_of_lt hn.right
  have h2 : 0 < n := hn.left
  have h3 : n / base = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hn.right)
  rw [addAux.eq_def]
  match n with
  | k + 1 => simp only [List.cons.injEq, h1, true_and, h3, addAux_eq_nil_iff hb]

theorem addAux_comm {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = addAux b a n base hb := by
  fun_induction addAux a b n base hb with
  | case1 => rw [addAux]
  | case2 => rw [addAux]
  | case3 _ _ _ ih => rw [addAux]; rw [ih]
  | case4 _ _ _ ih => rw [addAux]; rw [ih]
  | case5 x _ y _ _ ih => rw [addAux]; rw [ih]; rw [Nat.add_comm y x]

end AddAux

section AddAux_AllDigitsLtBase

theorem addAux_nil_of_allDigitsLtBase {a : List Nat} {base : Nat} (hb : 1 < base) (ha: allDigitsLtBase a base) :
  addAux [] a 0 base hb = a := by
  induction a with
  | nil => simp only [addAux]
  | cons x xs ih =>
    have h1 : x < base ∧ allDigitsLtBase xs base := allDigitsLtBase_cons_iff.mp ha
    have h2 : x % base = x := Nat.mod_eq_of_lt h1.left
    have h3 : x / base = 0 := Nat.div_eq_of_lt h1.left
    have h4 : addAux [] xs 0 base hb = xs := ih h1.right
    simp only [addAux, Nat.add_zero, h2, h3, h4]

/-
shows that `allDigitsLtBase a base` is necessary in `addAux_nil_of_allDigitsLtBase`, illustrating
that `addAux` returns _normalized_ lists for which `allDigitsLtBase` is true.
-/
example : addAux [] [10, 0] 0 10 (by decide) = [0, 1] := by
  simp only [addAux, Nat.add_zero, Nat.mod_self, Nat.zero_lt_succ, Nat.div_self]
  simp only [Nat.zero_add, Nat.one_mod, Nat.reduceDiv, addAux]

end AddAux_AllDigitsLtBase

section AddAux_Prune_AddDigits

theorem addAux_nil_eq_prune_addDigits_nil {a : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux [] a n base hb = prune (addDigits [] a) n base hb := by
  induction a generalizing n with
  | nil =>
    induction n using Nat.strongRecOn with
    | _ l ihk =>
      rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
      if hl : l = 0 then
        rw [hl]
      else
        have h1 : l / base < l := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hl) hb
        have h2 : addAux [] [] (l / base) base hb = prune [] (l / base) base hb := by
          rw [ihk (l / base) h1, addDigits.eq_def]
        match hl : l with
        | 0 => simp only
        | k + 1 => simp only [h2]
  | cons y ys ihy =>
    rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
    simp only
    rw [List.cons.injEq]
    have h1 : addDigits [] ys = ys := by rw [addDigits_comm]; exact addDigits_nil_eq
    have h2 : addAux [] ys ((y + n) / base) base hb = prune ys ((y + n) / base) base hb := by
      rw [h1] at ihy
      exact ihy
    exact And.intro rfl h2

theorem addAux_eq_prune_addDigits {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = prune (addDigits a b) n base hb := by
  induction a generalizing b n with
  | nil => exact addAux_nil_eq_prune_addDigits_nil hb
  | cons x xs ihx =>
    rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
    match hb : b with
    | [] =>
      simp only
      rw [List.cons.injEq]
      have : addDigits xs [] = xs := addDigits_nil_eq
      rw (occs := .pos [2]) [← this]
      exact And.intro rfl ihx
    | y::ys  =>
      simp only
      rw [List.cons.injEq]
      exact And.intro rfl ihx

/-
alternative proof for `addAux_comm`
-/
example {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = addAux b a n base hb := by
  rw [addAux_eq_prune_addDigits, addDigits_comm, addAux_eq_prune_addDigits]

end AddAux_Prune_AddDigits

section AllDigitsLtBase_AddAux

theorem allDigitsLtBase_addAux {a b : List Nat} (n : Nat) {base : Nat} {hb : 1 < base} :
  allDigitsLtBase (addAux a b n base hb) base := by
  rw [addAux_eq_prune_addDigits hb]
  exact allDigitsLtBase_prune

end AllDigitsLtBase_AddAux

section NoTrailingZeroAux_AddAux

theorem noTrailingZeroAux_addAux_of {a b : List Nat} {n base : Nat}
  (hantz : noTrailingZeroAux a) (hbntz : noTrailingZeroAux b) (hb : 1 < base) :
  noTrailingZeroAux (addAux a b n base hb) := by
  have : noTrailingZeroAux (addDigits a b) := noTrailingZeroAux_addDigits_of hantz hbntz
  rw [addAux_eq_prune_addDigits hb]
  exact noTrailingZeroAux_prune_of_noTrailingZeroAux this

end NoTrailingZeroAux_AddAux

section ToNatAux_AddAux

theorem toNatAux_addAux_left_distrib {a b : List Nat} {base : Nat} {hb : 1 < base} :
  toNatAux (addAux a b 0 base hb) base = (toNatAux a base) + (toNatAux b base) := by
  rw [addAux_eq_prune_addDigits hb, toNatAux_prune_eq_add_toNatAux hb, toNatAux_addDigits_left_distrib, Nat.zero_add]

end ToNatAux_AddAux

section AddAux_IsZeroAux

theorem isZeroAux_addAux_iff_iZeroAux_and_is_zeroAux {a b : List Nat} {base : Nat} (hb : 1 < base) :
  isZeroAux (addAux a b 0 base hb) ↔ isZeroAux a ∧ isZeroAux b := by
  rw [← toNatAux_eq_zero_iff_isZeroAux hb, ← toNatAux_eq_zero_iff_isZeroAux hb, ← toNatAux_eq_zero_iff_isZeroAux hb]
  rw [toNatAux_addAux_left_distrib]
  exact Nat.add_eq_zero_iff

end AddAux_IsZeroAux

end NumeralAux
