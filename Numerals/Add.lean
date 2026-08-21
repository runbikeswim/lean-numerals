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
    simp only [List.toListNatAux_nil_eq, addDigits_helper_comm, addDigits_helper_nil_eq_toListNatAux]
    simp only [toNat_helper_nil_eq, Nat.zero_add]
  | cons x xs ih =>
    match b with
    | [] =>
      simp only [List.toListNatAux_nil_eq, addDigits_helper_nil_eq_toListNatAux]
      simp only [toNat_helper_nil_eq, Nat.add_zero]
    | y::ys =>
      simp only [addDigits_helper_cons_cons_eq, List.cons_toListNatAux_eq]
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

theorem hAdd_helper_nil_nil_eq {base : NatGtOne} {n : Nat} (h : n ≠ 0) :
  hAdd.helper base [] [] n = FinBase.ofNat n :: hAdd.helper base [] [] (n / base.val) := by
  match n with
  | 0 => contradiction
  | k + 1 => simp only [hAdd.helper]

theorem hAdd_helper_nil_comm {base : NatGtOne} {a : List base.Fin} {n : Nat} :
  hAdd.helper base a [] n = hAdd.helper base [] a n := by
  induction a generalizing n with
  | nil => rfl
  | cons x xs ih => simp only [hAdd.helper, ih]

theorem hAdd_helper_comm {base : NatGtOne} {a b : List base.Fin} {n : Nat} :
  hAdd.helper base a b n = hAdd.helper base b a n := by
  induction a generalizing b n with
  | nil => simp only [hAdd_helper_nil_comm]
  | cons x xs ih =>
    match b, n with
    | [], n => simp only [hAdd_helper_nil_comm]
    | y::ys, n => simp only [hAdd.helper, Nat.add_comm, ih]

theorem add_comm {base : NatGtOne} {a b : TZNumeral base} :
  a + b = b + a := by
  simp only [HAdd.hAdd, hAdd, eq_iff_digits_eq]
  exact hAdd_helper_comm

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

theorem not_equiv_helper_nil_hAdd_helper_nil_nil_of_ne_zero {base : NatGtOne} {n : Nat} (h : n ≠ 0) :
  ¬ equiv.helper base [] (hAdd.helper base [] [] n) := by
  induction n using Nat.strongRecOn with
  | _ l ih =>
    if g: l < base.val then
      simp only [hAdd_helper_nil_nil_eq h, equiv.helper, not_and]
      intro h1
      have h2 : l % base.val = l := (Nat.mod_eq_iff_lt base.val_ne_zero).mpr g
      have h3 : l = 0 := by
        simp only [OfNat.ofNat, FinBase.ofNat, h2, Fin.eq_mk_iff_val_eq, Nat.zero_mod] at h1
        assumption
      exact absurd h3 h
    else
      simp only [hAdd_helper_nil_nil_eq h, equiv.helper, not_and]
      intro h1
      have h2 : 0 < l := Nat.pos_of_ne_zero h
      have h3 : l / base.val < l := Nat.div_lt_self h2 base.property
      have h4 : l / base.val ≠ 0 := Nat.div_ne_zero_iff.mpr (And.intro base.val_ne_zero (Nat.le_of_not_lt g))
      exact ih (l / base.val) h3 h4

theorem equiv_helper_nil_and_eq_zero_of_equiv_helper_nil_hAdd_helper_nil {base : NatGtOne}
  {a : List base.Fin} {n : Nat} (h : equiv.helper base [] (hAdd.helper base [] a n)) :
  equiv.helper base [] a ∧ n = 0 := by
  induction a generalizing n with
  | nil =>
    if g : n = 0 then
      exact And.intro equiv_helper_nil_nil g
    else
      exact absurd h (not_equiv_helper_nil_hAdd_helper_nil_nil_of_ne_zero g)
  | cons x xs ih =>
    simp only [hAdd.helper] at h
    simp only [equiv.helper] at ⊢ h
    have h1 : (↑x + n) % base.val = 0 := by
      rw [FinBase.ofNat] at h
      exact Eq.symm (Fin.eq_mk_iff_val_eq.mp (Eq.symm h.left))
    have h2 : equiv.helper base [] xs ∧ ((↑x + n) / base.val) = 0 := ih h.right
    have h3 : ↑x + n = 0 := by
      rw [← Nat.mod_add_div (↑x + n) base.val, h1, h2.right, Nat.zero_add, Nat.mul_zero]
    have h4 : x = 0 := Fin.eq_mk_iff_val_eq.mpr (Nat.add_eq_zero_iff.mp h3).left
    exact And.intro (And.intro h4 h2.left) (Nat.add_eq_zero_iff.mp h3).right

theorem equiv_helper_nil_of_equiv_helper_nil_hAdd_helper_nil {base : NatGtOne} {a : List base.Fin}
  (h : equiv.helper base [] (hAdd.helper base [] a 0)) : equiv.helper base [] a :=
  (equiv_helper_nil_and_eq_zero_of_equiv_helper_nil_hAdd_helper_nil h).left

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

theorem equiv_helper_nil_hAdd_helper_nil_nil_of_eq_zero {base : NatGtOne} {n : Nat} (h : n = 0) :
  equiv.helper base [] (hAdd.helper base [] [] n) := by
  rw [h]
  exact equiv_helper_nil_hAdd_helper_nil_of_equiv_helper_nil equiv_helper_nil_nil

theorem equiv_helper_nil_hAdd_helper_nil_iff_equiv_helper_nil {base : NatGtOne} {a : List base.Fin} {n : Nat}:
  equiv.helper base [] (hAdd.helper base [] a n) ↔ equiv.helper base [] a ∧ n = 0 := by
  constructor
  · exact equiv_helper_nil_and_eq_zero_of_equiv_helper_nil_hAdd_helper_nil
  · intro h
    rw [h.right]
    exact equiv_helper_nil_hAdd_helper_nil_of_equiv_helper_nil h.left

theorem zero_equiv_zero_add_iff_zero_equiv {base : NatGtOne} {a : TZNumeral base} : 0 ≈ (0 + a) ↔ 0 ≈ a := by
  simp only [equiv, HAdd.hAdd, hAdd, OfNat.ofNat, ofNat, prune_nil_zero_eq_zero]
  exact
    Iff.intro
      (fun t ↦ ((@equiv_helper_nil_hAdd_helper_nil_iff_equiv_helper_nil base a.digits 0).mp t).left)
      (fun t ↦ ((@equiv_helper_nil_hAdd_helper_nil_iff_equiv_helper_nil base a.digits 0).mpr (And.intro t rfl)))

theorem equiv_helper_nil_hAdd_helper_of_equiv_helper_nil_and_equiv_helper_nil {base : NatGtOne} {a b : List base.Fin}
  (h: equiv.helper base [] a ∧ equiv.helper base [] b) : equiv.helper base [] (hAdd.helper base a b 0) := by
  induction a generalizing b with
  | nil => exact equiv_helper_nil_hAdd_helper_nil_of_equiv_helper_nil h.right
  | cons x xs ih =>
    match b with
    | [] =>
      rw [hAdd_helper_comm]
      exact equiv_helper_nil_hAdd_helper_nil_of_equiv_helper_nil h.left
    | y::ys =>
      simp only [hAdd.helper, equiv.helper, Nat.add_zero] at ⊢ h
      have h1 : ↑x + ↑y = (0 : Nat) := by
        simp only [h.left.left, h.right.left, Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, and_self]
        rfl
      simp only [h1, FinBase.ofNat, OfNat.ofNat, Nat.zero_div, FinBase.ofNat, Nat.zero_mod, true_and]
      exact ih (And.intro h.left.right h.right.right)

theorem equiv_helper_nil_and_equiv_helper_nil_and_eq_zero_of_equiv_helper_nil_hAdd_helper {base : NatGtOne} {a b : List base.Fin} {n : Nat}
  (h : equiv.helper base [] (hAdd.helper base a b n)) : equiv.helper base [] a ∧ equiv.helper base [] b ∧ n = 0 := by
  induction a generalizing b n with
  | nil =>
    have : equiv.helper base [] b ∧ n = 0 := equiv_helper_nil_and_eq_zero_of_equiv_helper_nil_hAdd_helper_nil h
    exact And.intro equiv_helper_nil_nil this
  | cons x xs ih =>
    match b with
    | [] =>
      rw [hAdd_helper_comm] at h
      have : equiv.helper base [] (x::xs) ∧ n = 0 := equiv_helper_nil_and_eq_zero_of_equiv_helper_nil_hAdd_helper_nil h
      exact And.intro this.left (And.intro  equiv_helper_nil_nil this.right)
    | y::ys =>
      simp only [hAdd.helper, equiv.helper] at ⊢ h
      have h1 : (↑x + ↑y + n) % base.val = 0 := by
        rw [FinBase.ofNat] at h
        exact Eq.symm (Fin.eq_mk_iff_val_eq.mp (Eq.symm h.left))
      have h2 : equiv.helper base [] xs ∧ equiv.helper base [] ys ∧ ((↑x + ↑y+ n) / base.val) = 0 := ih h.right
      have h3 : ↑x + ↑y + n = 0 := by
        rw [← Nat.mod_add_div (↑x + ↑y + n) base.val, h1, h2.right.right, Nat.zero_add, Nat.mul_zero]
      have h4 : n = 0 := (Nat.add_eq_zero_iff.mp h3).right
      have h5 : x = 0 ∧ y = 0 := by
        rw [h4, Nat.add_zero, Nat.add_eq_zero_iff] at h3
        rwa [← @Fin.eq_mk_iff_val_eq base.val x 0 base.val_pos, ← @Fin.eq_mk_iff_val_eq base.val y 0 base.val_pos] at h3
      have h6 : x = 0 ∧ equiv.helper base [] xs := And.intro h5.left h2.left
      have h7 : y = 0 ∧ equiv.helper base [] ys := And.intro h5.right h2.right.left
      exact And.intro h6 (And.intro h7 h4)

theorem equiv_helper_nil_hAdd_helper_iff_equiv_helper_nil_and_equiv_helper_nil_and_eq_zero {base : NatGtOne} {a b : List base.Fin} {n : Nat}:
  equiv.helper base [] (hAdd.helper base a b n) ↔ equiv.helper base [] a ∧ equiv.helper base [] b ∧ n = 0 := by
  constructor
  · exact equiv_helper_nil_and_equiv_helper_nil_and_eq_zero_of_equiv_helper_nil_hAdd_helper
  · intro h
    rw [h.right.right]
    exact equiv_helper_nil_hAdd_helper_of_equiv_helper_nil_and_equiv_helper_nil (And.intro h.left h.right.left)

theorem zero_equiv_add_iff_zero_equiv_and_zero_equiv {base : NatGtOne} {a b : TZNumeral base} : 0 ≈ (a + b) ↔ 0 ≈ a ∧ 0 ≈ b := by
  simp only [equiv, HAdd.hAdd, hAdd, OfNat.ofNat, ofNat, prune_nil_zero_eq_zero]
  exact
    Iff.intro
      (fun t ↦ let r := equiv_helper_nil_hAdd_helper_iff_equiv_helper_nil_and_equiv_helper_nil_and_eq_zero.mp t; And.intro r.left r.right.left)
      (fun t ↦ equiv_helper_nil_hAdd_helper_iff_equiv_helper_nil_and_equiv_helper_nil_and_eq_zero.mpr (And.intro t.left (And.intro t.right rfl)))

end Add

section Add_Prune

theorem hAdd_helper_nil_eq_prune_helper_addDigits_helper_nil {base : NatGtOne} {a : List base.Fin} {n : Nat} :
  hAdd.helper base [] a n = prune.helper base (addDigits.helper base [] a) n := by
  induction a generalizing n with
  | nil =>
    induction n using Nat.strongRecOn with
    | _ l ih =>
      rw [addDigits.helper.eq_def, hAdd.helper.eq_def, prune.helper.eq_def]
      if hl : l = 0 then
        rw [hl]
      else
        have h1 : l / base.val < l := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hl) base.property
        have h2 : hAdd.helper base [] [] (l / base.val) = prune.helper base [] (l / base.val)  := by
          rw [ih (l / base.val) h1, addDigits.helper.eq_def]
        match l with | k + 1 => simp only [h2]
  | cons y ys ih =>
    simp only [addDigits.helper, hAdd.helper, prune.helper, List.cons.injEq, true_and]
    exact ih

theorem hAdd_helper_eq_prune_helper_addDigits_helper {base : NatGtOne} {a b : List base.Fin} {n : Nat} :
  hAdd.helper base a b n = prune.helper base (addDigits.helper base a b) n := by
  induction a generalizing b n with
  | nil => exact hAdd_helper_nil_eq_prune_helper_addDigits_helper_nil
  | cons x xs ih =>
    rw [addDigits.helper.eq_def, hAdd.helper.eq_def, prune.helper.eq_def]
    match b with | [] | y::ys  => simp only [List.cons.injEq, true_and]; exact ih

theorem add_eq_prune_addDigits {base : NatGtOne} {a b : TZNumeral base} :
  a + b = prune (addDigits a b) 0 := by
  simp only [HAdd.hAdd, hAdd, prune, addDigits, eq_iff_digits_eq]
  exact hAdd_helper_eq_prune_helper_addDigits_helper

end Add_Prune

end TZNumeral

namespace Numeral

end Numeral
