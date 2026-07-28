/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic
import Numerals.ToNat

namespace TZNumeral

section Equivalence

def equiv {base : NatGtOne} (a b : TZNumeral base) : Prop :=
  helper base a.digits b.digits where
  helper (base : NatGtOne) : List base.Fin → List base.Fin → Prop
  | [], [] => True
  | x::xs, [] => x = 0 ∧ helper base xs []
  | [], y::ys => y = 0 ∧ helper base [] ys
  | x::xs, y::ys => x = y ∧ helper base xs ys

instance instHasEquiv {base : NatGtOne} : HasEquiv (TZNumeral base) := ⟨equiv⟩

theorem equiv_iff_equiv_helper_digits {base : NatGtOne} {a b : TZNumeral base} :
  a ≈ b ↔ equiv.helper base a.digits b.digits := by simp only [equiv]

theorem equiv_helper_cons_iff {base : NatGtOne} {x y : Fin base.val} {xs ys : List base.Fin} :
  equiv.helper base (x::xs) (y::ys) ↔ x = y ∧ equiv.helper base xs ys := by
  simp only [equiv.helper]

theorem equiv_cons_iff {base : NatGtOne} {x y : Fin base.val} {xs ys : TZNumeral base} :
  (cons x xs) ≈ (cons y ys) ↔ x = y ∧ xs ≈ ys := by
  simp only [equiv, cons]
  exact equiv_helper_cons_iff

theorem equiv_helper_nil_iff {base : NatGtOne} {a : List base.Fin} :
  equiv.helper base [] a ↔ a.all (· == 0) := by
  induction a with
  | nil =>
    simp only [List.all_nil, equiv.helper]
  | cons x xs ih =>
    simp only [equiv.helper, List.all_cons, Bool.and_eq_true, ih, beq_iff_eq]

theorem equiv_zero_iff {base : NatGtOne} {a : TZNumeral base} : 0 ≈ a ↔ a.digits.all (· == 0) := by
  simp only [equiv, ← zero_eq_zero]
  exact equiv_helper_nil_iff

theorem ne_zero_of_not_zero_equiv {base : NatGtOne} {a : TZNumeral base} (h : ¬ 0 ≈ a) : a ≠ 0 := by
  intro hc
  have : a.digits.all (· == 0) := by rw [hc]; exact List.all_nil
  exact absurd (equiv_zero_iff.mpr this) h

theorem equiv_helper_refl {base : NatGtOne} {a : List base.Fin} : equiv.helper base a a := by
  induction a  with
  | nil =>
    simp only [equiv.helper]
  | cons x xs ih =>
    simp only [equiv.helper, ih, true_and]

theorem equiv_refl {base : NatGtOne} {a : TZNumeral base} : a ≈ a := by
  exact equiv_helper_refl

theorem equiv_helper_symm {base : NatGtOne} {a b : List base.Fin}
  (hab : equiv.helper base a b) : equiv.helper base b a := by
  induction a generalizing b with
  | nil =>
    induction b with
    | nil => exact hab
    | cons y ys ihy =>
      unfold equiv.helper at ⊢ hab
      exact And.intro hab.left (ihy hab.right)
  | cons x xs ihx =>
    match b with
    | [] | y::ys =>
      unfold equiv.helper at ⊢ hab
      rw [hab.left]
      exact And.intro rfl (ihx hab.right)

theorem equiv_helper_iff_equiv_helper {base : NatGtOne} {a b : List base.Fin} :
  equiv.helper base a b ↔ equiv.helper base b a :=
  Iff.intro (equiv_helper_symm ·) (equiv_helper_symm ·)

theorem equiv_symm {base : NatGtOne} {a b : TZNumeral base} (hab : a ≈ b) : b ≈ a := by
  exact equiv_helper_symm hab

theorem equiv_iff_equiv {base : NatGtOne} {a b : TZNumeral base} : a ≈ b ↔ b ≈ a :=
  Iff.intro (equiv_symm ·) (equiv_symm ·)

theorem equiv_helper_trans_nil {base : NatGtOne} {a b : List base.Fin}
  (ha : equiv.helper base [] a) (hab : equiv.helper base a b) : equiv.helper base [] b := by
  induction a generalizing b with
  | nil => exact hab
  | cons x xs ih =>
    unfold equiv.helper at ha hab
    match b with
    | [] =>
      simp only at hab
      exact ih ha.right hab.right
    | z::zs =>
      unfold equiv.helper
      simp only at ⊢ hab
      have : z = 0 := by rw [ha.left] at hab; exact (Eq.symm hab.left)
      exact And.intro this (ih ha.right hab.right)

theorem equiv_helper_trans {base : NatGtOne} {a b c : List base.Fin}
  (hab : equiv.helper base a b) (hbc : equiv.helper base b c) : equiv.helper base a c := by
  induction a generalizing b c with
  | nil => exact equiv_helper_trans_nil hab hbc
  | cons x xs ihx =>
    unfold equiv.helper at ⊢ hab hbc
    match b, c with
    | [], [] => simp only at ⊢ hab hbc; exact hab
    | y::ys, [] =>
      simp only at ⊢ hab hbc
      rw [hbc.left] at hab
      exact And.intro hab.left (ihx hab.right hbc.right)
    | [], z::zs =>
      simp only at ⊢ hab hbc
      rw [hab.left, hbc.left]
      exact And.intro rfl (ihx hab.right hbc.right)
    | y::ys, z::zs =>
      simp only at ⊢ hab hbc
      rw [hab.left, ← hbc.left]
      exact And.intro rfl (ihx hab.right hbc.right)

theorem equiv_trans {base : NatGtOne} {a b c : TZNumeral base}
  (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c := by
  exact equiv_helper_trans hab hbc

theorem equivalence {base: NatGtOne} :
  Equivalence (equiv : (TZNumeral base) → (TZNumeral base) → Prop) :=
  ⟨
    by unfold equiv; exact fun _ ↦ equiv_refl,
    by unfold equiv; intro a b hab; exact equiv_symm hab,
    by unfold equiv; intro a b c hab hbc; exact equiv_trans hab hbc
  ⟩

theorem not_equiv_helper_of_not_equiv_helper {base : NatGtOne} {a b : List base.Fin}
  (h : ¬ equiv.helper base a b) : ¬ equiv.helper base b a := by
  intro h1
  have : equiv.helper base a b := equiv_helper_symm h1
  contradiction

theorem not_equiv_of_not_equiv {base : NatGtOne} {a b : TZNumeral base}
  (h : ¬ a ≈ b) : ¬ b ≈ a := not_equiv_helper_of_not_equiv_helper h

theorem not_equiv_helper_of_equiv_helper_of_not_equiv_helper {base : NatGtOne} {a b c : List base.Fin}
  (hab : equiv.helper base a b) (hbc : ¬ equiv.helper base b c) : ¬ equiv.helper base a c := by
  intro hac
  have : equiv.helper base b c := equiv_helper_trans (equiv_helper_symm hab) hac
  contradiction

theorem not_equiv_of_equiv_of_not_equiv {base : NatGtOne} {a b c : TZNumeral base}
  (hab : a ≈ b) (hbc : ¬ b ≈ c) : ¬ a ≈ c := not_equiv_helper_of_equiv_helper_of_not_equiv_helper hab hbc

def decEquiv_helper_zero {base : NatGtOne} (a : List base.Fin) :  Decidable (equiv.helper base [] a) :=
  if g : a.all (· == 0) then
    have : equiv.helper base [] a := equiv_zero_iff.mpr g
    isTrue this
  else
    have : ¬ equiv.helper base [] a := (Classical.iff_iff_not_iff_not.mp equiv_zero_iff).mpr g
    isFalse this

def decEquiv_helper {base : NatGtOne} (a b : List base.Fin) : Decidable (equiv.helper base a b) :=
  match a, b with
  | [], [] => isTrue (equiv_helper_refl)
  | [], y::ys => decEquiv_helper_zero (y::ys)
  | x::xs, [] =>
    match decEquiv_helper_zero (x::xs) with
    | isTrue p => isTrue (equiv_helper_symm p)
    | isFalse p =>
      have : ¬ equiv.helper base (x::xs) [] := (Classical.iff_iff_not_iff_not.mp equiv_helper_iff_equiv_helper).mp p
      isFalse this
  | x::xs, y::ys =>
    if g : x = y then
      match decEquiv_helper xs ys with
      | isTrue p =>
        have : equiv.helper base (x::xs) (y::ys) := equiv_helper_cons_iff.mpr (And.intro g p)
        isTrue this
      | isFalse p =>
        have h1 : ¬ (x = y ∧ equiv.helper base xs ys) := Classical.not_and_iff_not_or_not.mpr (.inr p)
        have h2 : ¬ equiv.helper base (x::xs) (y::ys) :=
          (Classical.iff_iff_not_iff_not.mp equiv_helper_cons_iff).mpr h1
        isFalse h2
    else
      have h1 : ¬ (x = y ∧ equiv.helper base xs ys) := Classical.not_and_iff_not_or_not.mpr (.inl g)
      have h2 : ¬ equiv.helper base (x::xs) (y::ys) :=
        (Classical.iff_iff_not_iff_not.mp equiv_helper_cons_iff).mpr h1
      isFalse h2

instance instDecEquivHelper (base : NatGtOne) (a b : List base.Fin) : Decidable (equiv.helper base a b) :=
  decEquiv_helper a b

def decEquiv {base : NatGtOne} (a b : TZNumeral base) : Decidable (a ≈ b) :=
  match decEquiv_helper a.digits b.digits with
  | isTrue p => isTrue (equiv_iff_equiv_helper_digits.mpr p)
  | isFalse p => isFalse ((Classical.iff_iff_not_iff_not.mp equiv_iff_equiv_helper_digits).mpr p)

instance instDecEquiv {base : NatGtOne} (a b : TZNumeral base) : Decidable (a ≈ b) := decEquiv a b

#eval (⟨[1, 2, 3]⟩ : TZNumeral10) ≈ ⟨[1, 2, 3, 0, 0]⟩
#eval (⟨[1, 2, 3]⟩ : TZNumeral10) ≈ ⟨[2, 3, 0, 0]⟩

end Equivalence

section ToNat_Equiv

theorem toNat_helper_eq_zero_of {base : NatGtOne} {a : List base.Fin} (h: equiv.helper base [] a) :
  toNat.helper base a 1 0 = 0 := by
  induction a with
  | nil => exact toNat_helper_nil_eq
  | cons x xs ih =>
    simp only [equiv_helper_nil_iff, List.all_cons, Bool.and_eq_true] at h
    have h1 : x = 0 := beq_iff_eq.mp h.left
    have h2 : toNat.helper base xs 1 0 = 0 := ih (equiv_helper_nil_iff.mpr h.right)
    simp only [toNat_helper_cons_eq, h1, h2, Nat.add_eq_zero_iff, Fin.val_eq_zero_iff]
    simp only [Nat.mul_zero, and_true]
    rfl

theorem toNat_eq_zero_of {base : NatGtOne} {a : TZNumeral base} (h: 0 ≈ a) :
  a.toNat = 0 := toNat_helper_eq_zero_of h

end ToNat_Equiv

end TZNumeral
