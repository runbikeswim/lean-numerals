/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic
import Numerals.Equiv

namespace TZNumeral

section LessThanOrEqualTo

def le {base : NatGtOne} (n m : TZNumeral base) : Prop :=
  helper base n.digits m.digits where
  helper (base : NatGtOne) : List base.Fin → List base.Fin → Prop
  | [], _ => True
  | x::xs, [] => x = 0 ∧ helper base xs []
  | x::xs, y::ys => if equiv.helper base xs ys then x ≤ y else helper base xs ys

instance instLe {base : NatGtOne} : LE (TZNumeral base) := ⟨le⟩

theorem le_helper_nil {base : NatGtOne} {a : List base.Fin} : le.helper base [] a := by
  simp only [le.helper]

theorem zero_le {base : NatGtOne} {n : TZNumeral base} : 0 ≤ n := @le_helper_nil base n.digits

theorem le_helper_refl {base : NatGtOne} {a : List base.Fin} : le.helper base a a := by
  match a with
  | [] => simp only [le.helper]
  | x::xs =>
    simp only [le.helper, equiv_helper_refl, reduceIte, Fin.le_refl]

theorem le_refl {base : NatGtOne} {a : TZNumeral base} : a ≤ a := by
  simp only [LE.le, le]
  exact le_helper_refl

theorem le_helper_cons_iff {base : NatGtOne} {x y : base.Fin} {xs ys : List base.Fin} :
  le.helper base (x::xs) (y::ys) ↔ if equiv.helper base xs ys then x ≤ y else le.helper base xs ys := by
  rfl

section Equiv_LessThanOrEqualTo

theorem not_equiv_helper_of_le_helper_cons_of_not_le {base : NatGtOne} {x y : base.Fin} {xs ys : List base.Fin}
  (hl : le.helper base (x::xs) (y::ys)) (hn : ¬ x ≤ y) : ¬ equiv.helper base xs ys := by
  have : if equiv.helper base xs ys then x ≤ y else le.helper base xs ys := le_helper_cons_iff.mp hl
  intro hc
  simp only [hc, reduceIte] at this
  contradiction

theorem not_equiv_of_le_cons_of_not_le {base : NatGtOne} {x y : base.Fin} {xs ys : TZNumeral base}
  (hl : (cons x xs) ≤ (cons y ys)) (hn : ¬ x ≤ y) : ¬ xs ≈ ys := not_equiv_helper_of_le_helper_cons_of_not_le hl hn

theorem le_helper_of_equiv_helper {base : NatGtOne} {a b : List base.Fin} (h : equiv.helper base a b) :
  le.helper base a b := by
  induction a generalizing b with
  | nil => exact le_helper_nil
  | cons x xs ih =>
    match b with
    | [] =>
      simp only [equiv.helper] at h
      simp only [le.helper]
      exact And.intro h.left (ih h.right)
    | y::ys =>
      simp only [equiv.helper] at h
      simp only [le.helper, h.right, reduceIte, h.left, Fin.le_refl]

theorem le_of_equiv {base : NatGtOne} {a b : TZNumeral base} (h : a ≈ b) :
  a ≤ b := le_helper_of_equiv_helper h

theorem equiv_helper_nil_of_le_helper_nil {base : NatGtOne} {a : List base.Fin} (h : le.helper base a []) :
  equiv.helper base [] a  := by
  induction a with
  | nil  => exact equiv_helper_refl
  | cons x xs ih =>
    rw [equiv.helper.eq_def]
    rw [le.helper.eq_def] at h
    simp only at ih h ⊢
    exact And.intro h.left (ih h.right)

theorem equiv_zero_of_le_zero {base : NatGtOne} {a : TZNumeral base} (h : a ≤ 0) : 0 ≈ a :=
  equiv_helper_nil_of_le_helper_nil h

theorem le_helper_nil_iff_equiv_helper_nil {base : NatGtOne} {a : List base.Fin} :
  le.helper base a [] ↔ equiv.helper base [] a :=
  Iff.intro equiv_helper_nil_of_le_helper_nil (le_helper_of_equiv_helper ∘ equiv_helper_symm)

theorem le_zero_iff_equiv_zero {base : NatGtOne} {a : TZNumeral base} :
  a ≤ 0 ↔ 0 ≈ a := Iff.intro equiv_zero_of_le_zero (le_of_equiv ∘ equiv_symm)

end Equiv_LessThanOrEqualTo

theorem equiv_helper_iff_le_helper_and_le_helper {base : NatGtOne} {a b : List base.Fin} :
  equiv.helper base a b ↔ le.helper base a b ∧ le.helper base b a := by
  constructor
  · intro h
    have h1 : le.helper base a b := le_helper_of_equiv_helper h
    have h2 : le.helper base b a := le_helper_of_equiv_helper (equiv_helper_symm h)
    exact And.intro h1 h2
  · intro h
    induction a generalizing b with
    | nil =>
      unfold le.helper at h
      match b with
      | [] => exact equiv_helper_refl
      | x::xs =>
        rw [equiv.helper.eq_def]
        simp only [true_and] at ⊢ h
        exact And.intro h.left (equiv_helper_nil_of_le_helper_nil h.right)
    | cons x xs ih =>
      match b with
      | [] =>
        have : equiv.helper base [] (x :: xs) := equiv_helper_nil_of_le_helper_nil h.left
        exact equiv_helper_symm this
      | y::ys =>
        unfold le.helper at h
        unfold equiv.helper
        if g : equiv.helper base xs ys then
          simp only [g, equiv_helper_symm, reduceIte] at h
          simp only [Fin.le_antisymm h.left h.right, g, true_and]
        else
          have : ¬ equiv.helper base ys xs := not_equiv_helper_of_not_equiv_helper g
          simp only [g, reduceIte, this] at h
          have : equiv.helper base xs ys := ih h
          contradiction

theorem equiv_iff_le_and_le {base : NatGtOne} {a b : TZNumeral base} :
  a ≈ b ↔ a ≤ b ∧  b ≤ a := equiv_helper_iff_le_helper_and_le_helper

theorem le_helper_total {base : NatGtOne} {a b : List base.Fin} :
  le.helper base a b ∨ le.helper base b a := by
  induction a generalizing b with
  | nil => exact .inl (le_helper_nil)
  | cons x xs ih =>
    match b with
    | [] => exact .inr (le_helper_nil)
    | y::ys =>
      if g1 : equiv.helper base xs ys then
        if g2 : x ≤ y then
          have : le.helper base (x::xs) (y::ys) := by simp only [le.helper, g1, g2, reduceIte]
          exact .inl this
        else
          have h1 : equiv.helper base ys xs := equiv_helper_symm g1
          have h2 : y ≤ x := Nat.le_of_not_le g2
          have : le.helper base (y::ys) (x::xs) := by simp only [le.helper, h1, h2, reduceIte]
          exact .inr this
      else
        have g2 : ¬ equiv.helper base ys xs := not_equiv_helper_of_not_equiv_helper g1
        simp only [le.helper, g1, g2, reduceIte]
        exact ih

theorem le_total {base : NatGtOne} {a b : TZNumeral base} :
   a ≤ b ∨ b ≤ a := le_helper_total

section LessThanOrEqualTo_Equiv

theorem le_helper_of_le_helper_of_equiv_helper {base : NatGtOne} {a b c : List base.Fin}
  (hab : le.helper base a b) (hbc : equiv.helper base b c): le.helper base a c := by
  induction a generalizing b c with
  | nil => exact le_helper_nil
  | cons x xs ih =>
    match b, c with
    | [], [] => simp_all only
    | y::ys, [] =>
      unfold le.helper at hab ⊢
      unfold equiv.helper at hbc
      if g : equiv.helper base xs ys then
        simp only [g, reduceIte, hbc.left] at hab
        have h1 : x = 0 := Fin.eq_zero_of_le_zero hab
        have h2 : le.helper base xs ys := le_helper_of_equiv_helper g
        have h3 : le.helper base xs [] := ih  h2 hbc.right
        exact And.intro h1 h3
      else
        simp only [g, reduceIte, hbc.left] at hab
        have h1 : le.helper base xs [] := ih hab hbc.right
        have h2 : equiv.helper base xs [] := equiv_helper_symm (equiv_helper_nil_of_le_helper_nil h1)
        have h3 : equiv.helper base xs ys := equiv_helper_trans h2 (equiv_helper_symm hbc.right)
        contradiction
    | [], z::zs =>
      have : equiv.helper base (x :: xs) [] := equiv_helper_symm (equiv_helper_nil_of_le_helper_nil hab)
      have : equiv.helper base (x :: xs) (z :: zs) := equiv_helper_trans this hbc
      exact le_helper_of_equiv_helper this
    | y::ys, z::zs =>
      unfold le.helper at hab ⊢
      unfold equiv.helper at hbc
      if g1 : equiv.helper base xs ys then
        simp only [g1, reduceIte, hbc.left] at hab
        if g2 : equiv.helper base xs zs then
          simp only [g2, reduceIte]
          exact hab
        else
          simp only [g2, reduceIte]
          have : equiv.helper base xs zs := equiv_helper_trans g1 hbc.right
          contradiction
      else
        simp only [g1, reduceIte] at hab
        if g2 : equiv.helper base xs zs then
          simp only [g2, reduceIte]
          have : equiv.helper base xs ys := equiv_helper_trans g2 (equiv_helper_symm hbc.right)
          contradiction
        else
          simp only [g2, reduceIte]
          exact ih hab hbc.right

end LessThanOrEqualTo_Equiv

end LessThanOrEqualTo

section LessThan

end LessThan
