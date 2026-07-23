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

theorem zero_le {base : NatGtOne} {n : TZNumeral base} : 0 ≤ n := by
  simp only [OfNat.ofNat, LE.le, le, Zero.zero]
  exact le_helper_nil

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

end LessThanOrEqualTo

section Equiv_LessThanOrEqualTo

theorem not_equiv_helper_of_le_helper_cons_of_not_le {base : NatGtOne} {x y : base.Fin} {xs ys : List base.Fin}
  (hl : le.helper base (x::xs) (y::ys)) (hn : ¬ x ≤ y) : ¬ equiv.helper base xs ys := by
  have : if equiv.helper base xs ys then x ≤ y else le.helper base xs ys := le_helper_cons_iff.mp hl
  intro hc
  simp only [hc, reduceIte] at this
  contradiction

theorem not_equiv_of_le_cons_of_not_le {base : NatGtOne} {x y : base.Fin} {xs ys : TZNumeral base}
  (hl : (cons x xs) ≤ (cons y ys)) (hn : ¬ x ≤ y) : ¬ xs ≈ ys := by
  simp only [HasEquiv.Equiv, instHasEquiv, equiv]
  simp only [LE.le, le, cons] at hl
  exact not_equiv_helper_of_le_helper_cons_of_not_le hl hn

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
  a ≤ b := by
  simp only [LE.le, le]
  simp only [HasEquiv.Equiv, instHasEquiv, equiv] at h
  exact le_helper_of_equiv_helper h

theorem equiv_helper_nil_of_le_helper_nil {base : NatGtOne} {a : List base.Fin} (h : le.helper base a []) :
  equiv.helper base [] a  := by
  induction a with
  | nil  => exact equiv_helper_refl
  | cons x xs ih =>
    rw [equiv.helper.eq_def]
    rw [le.helper.eq_def] at h
    simp only at ih h ⊢
    exact And.intro h.left (ih h.right)

theorem equiv_zero_of_le_zero {base : NatGtOne} {a : TZNumeral base} (h : a ≤ 0) : 0 ≈ a := by
  simp only [HasEquiv.Equiv, instHasEquiv, equiv, OfNat.ofNat, Zero.zero]
  simp only [LE.le, le] at h
  exact equiv_helper_nil_of_le_helper_nil h

theorem le_helper_nil_iff_equiv_helper_nil {base : NatGtOne} {a : List base.Fin} :
  le.helper base a [] ↔ equiv.helper base [] a := by
  constructor
  · intro h
    exact equiv_helper_nil_of_le_helper_nil h
  · intro h
    exact le_helper_of_equiv_helper (equiv_helper_symm h)

theorem le_zero_iff_equiv_zero {base : NatGtOne} {a : TZNumeral base} :
  a ≤ 0 ↔ 0 ≈ a := Iff.intro (equiv_zero_of_le_zero ·) (le_of_equiv ∘ (equiv_symm ·))

end Equiv_LessThanOrEqualTo

section LessThan

end LessThan
