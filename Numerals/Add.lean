/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic
import Numerals.ToNat
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

theorem addDigits_helper_nil_eq_toListNatAux {base : NatGtOne} {a : List base.Fin} :
  addDigits.helper base a [] = a.toListNatAux := by
  induction a with
  | nil => simp only [addDigits.helper, List.toListNatAux, List.map_nil]
  | cons x xs ih =>
    simp only [addDigits.helper, List.toListNatAux, List.map_cons, ih]
    exact List.cons_eq_cons.mpr (And.intro rfl rfl)

theorem addDigits_zero_eq_toListAux {base : NatGtOne} {a : TZNumeral base} :
  a.addDigits 0 = a.toListNat := addDigits_helper_nil_eq_toListNatAux

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

theorem toNat_helper_addDigits_helper_left_distrib {base : NatGtOne} {a b : List base.Fin} :
  toNat.helper base (addDigits.helper base a b) 1 0
    = (toNat.helper base a.toListNatAux 1 0) + (toNat.helper base b.toListNatAux 1 0) := by
  induction a generalizing b with
  | nil =>
    simp only [toListNatAux_nil_eq_nil, addDigits_helper_comm, addDigits_helper_nil_eq_toListNatAux]
    simp only [toNat_helper_nil_eq, Nat.zero_add]
  | cons x xs ih =>
    match b with
    | [] =>
      simp only [toListNatAux_nil_eq_nil, addDigits_helper_nil_eq_toListNatAux]
      simp only [toNat_helper_nil_eq, Nat.add_zero]
    | y::ys =>
      simp only [addDigits_helper_cons_cons_eq, cons_toListNatAux_eq_coe_cons_toList]
      simp only [toNat_helper_cons_eq, ih, Nat.mul_add]
      calc ↑x + ↑y + (base.val * toNat.helper base xs.toListNatAux 1 0 + base.val * toNat.helper base ys.toListNatAux 1 0)
          = ↑x + ↑y + base.val * toNat.helper base xs.toListNatAux 1 0 + base.val * toNat.helper base ys.toListNatAux 1 0
            := by rw [← Nat.add_assoc]
        _ = ↑x + (↑y + base.val * toNat.helper base xs.toListNatAux 1 0) + base.val * toNat.helper base ys.toListNatAux 1 0
            := by rw [← Nat.add_assoc]
        _ = ↑x + (base.val * toNat.helper base xs.toListNatAux 1 0 + ↑y) + base.val * toNat.helper base ys.toListNatAux 1 0
            := by rw (occs := .pos [3]) [Nat.add_comm]
        _ = ↑x + base.val * toNat.helper base xs.toListNatAux 1 0 + ↑y + base.val * toNat.helper base ys.toListNatAux 1 0
            := by rw [← Nat.add_assoc]
        _ = ↑x + base.val * toNat.helper base xs.toListNatAux 1 0 + (↑y + base.val * toNat.helper base ys.toListNatAux 1 0)
            := by rw [← Nat.add_assoc]

end NoTrailingZero_AddDigits

section Add

def add {base : NatGtOne} (n m : TZNumeral base) (k : Nat) : TZNumeral base where
  digits := helper base n.digits m.digits k where
  helper (base : NatGtOne) (a b : List base.Fin) (n : Nat) : List base.Fin :=
  match a, b, n with
  | [], [], 0 => []
  | [], [], k + 1 =>
    -- for asserting termination
    have h : 0 < k + 1 := Nat.zero_lt_succ k
    have : (k + 1) / base.val < k + 1 := Nat.div_lt_self h base.property
    FinBase.ofNat (k + 1) :: helper base [] [] ((k + 1) / base.val)
  | x::xs, [], n => FinBase.ofNat (x + n) :: helper base xs [] ((x + n) / base.val)
  | [], y::ys, n => FinBase.ofNat (y + n) :: helper base [] ys ((y + n) / base.val)
  | x::xs, y::ys, n => FinBase.ofNat (x + y + n) :: helper base xs ys ((x + y + n) / base.val)
  termination_by (a.length + b.length, n)

end Add

end TZNumeral

namespace Numeral


end Numeral
