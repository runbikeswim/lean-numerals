/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic
import Numerals.ToNat
import Numerals.Prune
import Numerals.OfNat
import Numerals.Equiv

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
  a.addDigits 0 = a.toListNat := by
  simp only [OfNat.ofNat, ofNat, addDigits, toListNat, prune_nil_zero_eq_zero]
  exact addDigits_helper_nil_eq_toListNatAux

theorem addDigits_helper_eq_nil_iff_eq_nil_and_eq_nil {base : NatGtOne} {a b : List base.Fin} :
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

theorem addDigits_eq_nil_iff_eq_zero_and_eq_zero {base : NatGtOne} {a b : TZNumeral base} :
  a.addDigits b = [] ↔ a = 0 ∧ b = 0 := by
  simp only [OfNat.ofNat, eq_iff_digits_eq, OfNat.ofNat, ofNat, prune_nil_zero_eq_zero]
  exact addDigits_helper_eq_nil_iff_eq_nil_and_eq_nil

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
    simp only [toListNatAux_nil_eq, addDigits_helper_comm, addDigits_helper_nil_eq_toListNatAux]
    simp only [toNat_helper_nil_eq, Nat.zero_add]
  | cons x xs ih =>
    match b with
    | [] =>
      simp only [toListNatAux_nil_eq, addDigits_helper_nil_eq_toListNatAux]
      simp only [toNat_helper_nil_eq, Nat.add_zero]
    | y::ys =>
      simp only [addDigits_helper_cons_cons_eq, cons_toListNatAux_eq]
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

def hAdd {base : NatGtOne} (n m : TZNumeral base) : TZNumeral base where
  digits := helper base n.digits m.digits 0 where
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

instance instHAddTZNumerals {base : NatGtOne} :
  HAdd (TZNumeral base) (TZNumeral base) (TZNumeral base) := ⟨hAdd⟩

theorem hAdd_helper_eq_nil_iff {base : NatGtOne} {a b : List base.Fin} {n : Nat} :
  hAdd.helper base a b n = [] ↔ a = [] ∧ b = [] ∧ n = 0 := by
  constructor
  · intro h
    match a, b, n with
    | [], [], 0 => simp only [and_self]
    | [], [], k + 1 | x::xs, [], n | [], y::ys, n | x::xs, y::ys, n =>
      simp only [hAdd.helper, reduceCtorEq] at h
  · intro h
    simp only [h.left, h.right.left, h.right.right, hAdd.helper]

theorem add_eq_zero_iff {base : NatGtOne} {a b : TZNumeral base} :
  a + b = 0 ↔ a = 0 ∧ b = 0 := by
  simp only [HAdd.hAdd, hAdd, OfNat.ofNat, ofNat, prune_nil_zero_eq_zero, zero, eq_iff_digits_eq]
  constructor
  · intro h
    have : a.digits = [] ∧ b.digits = [] ∧ 0 = 0 := hAdd_helper_eq_nil_iff.mp h
    exact And.intro this.left this.right.left
  · intro h
    have : hAdd.helper base a.digits b.digits 0 = [] :=
      hAdd_helper_eq_nil_iff.mpr (And.intro h.left (And.intro h.right rfl))
    exact this

theorem equiv_helper_nil_hAdd_helper_nil_of_equiv_helper_nil {base : NatGtOne} {a : List base.Fin}
  (h: equiv.helper base [] a) : equiv.helper base [] (hAdd.helper base [] a 0) := by
  induction a with
  | nil =>
    have :  hAdd.helper base [] [] 0 = [] := hAdd_helper_eq_nil_iff.mpr (And.intro rfl (And.intro rfl rfl))
    simp only [this, equiv_helper_nil_nil]
  | cons x xs ih =>
    simp only [hAdd.helper]
    simp only [equiv.helper] at ⊢ h
    simp only [h.left, Nat.add_zero, FinBase.ofNat, OfNat.ofNat, Nat.zero_mod, Nat.zero_div, true_and]
    exact ih h.right

theorem equiv_helper_nil_of_equiv_helper_nil_hAdd_helper_nil_of {base : NatGtOne} {a : List base.Fin}
  (h : equiv.helper base [] (hAdd.helper base [] a 0)) : equiv.helper base [] a := by
  induction a with
  | nil => exact equiv_helper_nil_nil
  | cons x xs ih =>
    simp only [hAdd.helper, equiv.helper] at ⊢ h
    simp only [FinBase.ofNat, Nat.add_zero, Nat.mod_eq_of_lt (Fin.isLt x), Fin.eta] at h
    simp only [h.left, true_and, FinBase.ofNat, Nat.zero_mod, OfNat.ofNat, Nat.zero_div] at ⊢ h
    exact ih h

theorem equiv_helper_nil_hAdd_helper_nil_iff_equiv_helper_nil {base : NatGtOne} {a : List base.Fin} :
  equiv.helper base [] (hAdd.helper base [] a 0) ↔ equiv.helper base [] a :=
  Iff.intro equiv_helper_nil_of_equiv_helper_nil_hAdd_helper_nil_of equiv_helper_nil_hAdd_helper_nil_of_equiv_helper_nil

theorem zero_equiv_zero_add_iff_zero_equiv {base : NatGtOne} {a : TZNumeral base} : 0 ≈ (0 + a) ↔ 0 ≈ a := by
  simp only [equiv, HAdd.hAdd, hAdd, OfNat.ofNat, ofNat, prune_nil_zero_eq_zero]
  exact @equiv_helper_nil_hAdd_helper_nil_iff_equiv_helper_nil base a.digits

end Add

end TZNumeral

namespace Numeral

end Numeral
