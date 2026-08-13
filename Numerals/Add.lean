/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic
import Numerals.Prune

namespace TZNumeral

section AddDigits

def addDigits {base : NatGtOne} (a b : TZNumeral base) : List Nat :=
  helper base a.digits b.digits where
  helper (base : NatGtOne) : List base.Fin → List base.Fin → List Nat
  | [], [] => []
  | x::xs, [] => ↑x::(helper base xs [])
  | [], y::ys => ↑y::(helper base [] ys)
  | x::xs, y::ys => (↑x + ↑y)::(helper base xs ys)

theorem addDigits_helper_cons_ne_nil {base : NatGtOne} {x : base.Fin} {xs b : List base.Fin} :
  addDigits.helper base (x::xs) b ≠ [] := by
  match b with
  | [] =>
    simp only [addDigits.helper]
    exact List.cons_ne_nil (↑x : Nat) (addDigits.helper base xs [])
  | y::ys =>
    simp only [addDigits.helper]
    exact List.cons_ne_nil (↑x + ↑y : Nat) (addDigits.helper base xs ys)

theorem cons_addDigits_ne_nil {base : NatGtOne} {x : base.Fin} {xs b : TZNumeral base} :
  (cons x xs).addDigits b ≠ [] := addDigits_helper_cons_ne_nil

theorem addDigits_helper_nil_comm {base : NatGtOne} {a : List base.Fin} :
  addDigits.helper base a [] = addDigits.helper base [] a := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [addDigits.helper, ih]

theorem addDigits_helper_comm {base : NatGtOne} {a b : List base.Fin} :
  addDigits.helper base a b = addDigits.helper base b a := by
  induction a generalizing b with
  | nil => simp only [addDigits_helper_nil_comm]
  | cons x xs ih =>
    match b with
    | [] => simp only [addDigits_helper_nil_comm]
    | y::ys => simp only [addDigits.helper, Nat.add_comm, ih]

theorem addDigits_comm {base : NatGtOne} {a b : TZNumeral base} :
  a.addDigits b = b.addDigits a := addDigits_helper_comm

theorem addDigits_helper_nil_eq_map_coe {base : NatGtOne} {a : List base.Fin} :
  addDigits.helper base a [] = a.map (↑·) := by
  induction a with
  | nil => simp only [addDigits.helper, List.map_nil]
  | cons x xs ih =>
    simp only [addDigits.helper, List.map_cons, ih]

theorem addDigits_zero_eq_digits_map_coe {base : NatGtOne} {a : TZNumeral base} :
  a.addDigits 0 = a.digits.map (↑·) := addDigits_helper_nil_eq_map_coe

theorem addDigits_helper_nil_iff_eq_nil_and_eq_nil {base : NatGtOne} {a b : List base.Fin} :
  addDigits.helper base a b = [] ↔ a = [] ∧ b = [] := by
  constructor
  · intro h
    match a, b with
    | [], [] => exact And.intro rfl rfl
    | x::xs, b =>
      have : addDigits.helper base (x :: xs) b ≠ [] := addDigits_helper_cons_ne_nil
      contradiction
    | [], y::ys =>
      have : addDigits.helper base [] (y::ys) ≠ [] := by
        rw [← addDigits_helper_nil_comm]
        exact addDigits_helper_cons_ne_nil
      contradiction
  . intro h
    simp only [h.left, h.right, addDigits.helper]

theorem addDigits_nil_iff_eq_zero_and_eq_zero {base : NatGtOne} {a b : TZNumeral base} :
  a.addDigits b = [] ↔ a = 0 ∧ b = 0 := by
  simp only [OfNat.ofNat, eq_iff_digits_eq, Zero.zero]
  exact addDigits_helper_nil_iff_eq_nil_and_eq_nil

theorem addDigits_helper_cons_cons_eq {base : NatGtOne} {x y : base.Fin} {xs ys : List base.Fin} :
  addDigits.helper base (x::xs) (y::ys) = (↑x + ↑y : Nat)::(addDigits.helper base xs ys) := by
  simp only [addDigits.helper]

end AddDigits

section NoTrailingZero_AddDigits

end NoTrailingZero_AddDigits

end TZNumeral

namespace Numeral


end Numeral
