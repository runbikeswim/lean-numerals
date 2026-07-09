/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic

section Equivalence

namespace TZNumeral

def equiv {base : NatGtOne} (a b : TZNumeral base) : Prop :=
  helper a.digits b.digits where
  helper : List (Fin base.val) → List (Fin base.val) → Prop
  | [], [] => True
  | x::xs, [] => x = 0 ∧ helper xs []
  | [], y::ys => y = 0 ∧ helper [] ys
  | x::xs, y::ys => x = y ∧ helper xs ys

instance instHasEquiv {base : NatGtOne} : HasEquiv (TZNumeral base) := ⟨equiv⟩

theorem equiv_iff_equiv_helper_digits {base : NatGtOne} {a b : TZNumeral base} :
  a ≈ b ↔ equiv.helper a.digits b.digits := by simp only [equiv]

theorem equiv_helper_cons_iff {base : NatGtOne} {x y : Fin base.val} {xs ys : List (Fin base.val)} :
  equiv.helper (x::xs) (y::ys) ↔ x = y ∧ equiv.helper xs ys := by
  simp only [equiv.helper]

theorem equiv_cons_iff {base : NatGtOne} {x y : Fin base.val} {xs ys : TZNumeral base} :
  (cons x xs) ≈ (cons y ys) ↔ x = y ∧ xs ≈ ys := by
  simp only [equiv, cons]
  exact equiv_helper_cons_iff

theorem equiv_zero_iff {base : NatGtOne} {a : TZNumeral base} : 0 ≈ a ↔ a.digits.all (· == 0) := by
  simp only [equiv, ← zero_eq_zero]
  induction a.digits with
  | nil =>
    simp only [List.all_nil, equiv.helper]
  | cons x xs ih =>
    simp only [equiv.helper, List.all_cons, Bool.and_eq_true, ih, beq_iff_eq]

theorem ne_zero_of_not_zero_equiv {base : NatGtOne} {a : TZNumeral base} (h : ¬ 0 ≈ a) : a ≠ 0 := by
  false_or_by_contra; rename _ => hc
  have : a.digits.all (· == 0) := by rw [hc]; exact List.all_nil
  exact absurd (equiv_zero_iff.mpr this) h

theorem equiv_helper_refl {base : NatGtOne} {a : List (Fin base.val)} : equiv.helper a a := by
  induction a  with
  | nil =>
    simp only [equiv.helper]
  | cons x xs ih =>
    simp only [equiv.helper, ih, true_and]

theorem equiv_refl {base : NatGtOne} {a : TZNumeral base} : a ≈ a := by
  unfold instHasEquiv equiv
  exact equiv_helper_refl

theorem equiv_helper_symm {base : NatGtOne} {a b : List (Fin base.val)} (hab : equiv.helper a b) : equiv.helper b a := by
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

theorem equiv_helper_iff_equiv_helper {base : NatGtOne} {a b : List (Fin base.val)} : equiv.helper a b ↔ equiv.helper b a :=
  Iff.intro (equiv_helper_symm ·) (equiv_helper_symm ·)

theorem equiv_symm {base : NatGtOne} {a b : TZNumeral base} (hab : a ≈ b) : b ≈ a := by
  unfold instHasEquiv equiv at ⊢ hab
  exact equiv_helper_symm hab

theorem equiv_iff_equiv {base : NatGtOne} {a b : TZNumeral base} : a ≈ b ↔ b ≈ a :=
  Iff.intro (equiv_symm ·) (equiv_symm ·)

theorem equiv_helper_trans_nil {base : NatGtOne} {a b : List (Fin base.val)}
  (ha : equiv.helper [] a) (hab : equiv.helper a b) : equiv.helper [] b := by
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

theorem equiv_helper_trans {base : NatGtOne} {a b c : List (Fin base.val)}
  (hab : equiv.helper a b) (hbc : equiv.helper b c) : equiv.helper a c := by
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
  unfold instHasEquiv equiv at ⊢ hab hbc
  exact equiv_helper_trans hab hbc

def equivalence {base: NatGtOne} :
  Equivalence (equiv : (TZNumeral base) → (TZNumeral base) → Prop) :=
  ⟨
    by unfold equiv; exact fun _ ↦ equiv_refl,
    by unfold equiv; intro a b hab; exact equiv_symm hab,
    by unfold equiv; intro a b c hab hbc; exact equiv_trans hab hbc
  ⟩

theorem not_equiv_of_not_equiv {base : NatGtOne} {a b : TZNumeral base}
  (h : ¬ a ≈ b) : ¬ b ≈ a := by
  false_or_by_contra; rename _ => h1
  have : a ≈ b := equivalence.symm h1
  contradiction

theorem not_equiv_of_equiv_of_not_equiv {base : NatGtOne} {a b c : TZNumeral base}
  (hab : a ≈ b) (hbc : ¬ b ≈ c) : ¬ a ≈ c := by
  false_or_by_contra; rename _ => hac
  have : b ≈ c := equivalence.trans (equivalence.symm hab) hac
  contradiction

def decEquiv_helper_zero {base : NatGtOne} (a : List (Fin base.val)) :  Decidable (equiv.helper [] a) :=
  if g : a.all (· == 0) then
    have : equiv.helper [] a := equiv_zero_iff.mpr g
    isTrue this
  else
    have : ¬ equiv.helper [] a := (Classical.iff_iff_not_iff_not.mp equiv_zero_iff).mpr g
    isFalse this

def decEquiv_helper {base : NatGtOne} (a b : List (Fin base.val)) : Decidable (equiv.helper a b) :=
  match a, b with
  | [], [] => isTrue (equiv_helper_refl)
  | [], y::ys => decEquiv_helper_zero (y::ys)
  | x::xs, [] =>
    match decEquiv_helper_zero (x::xs) with
    | isTrue p => isTrue (equiv_helper_symm p)
    | isFalse p =>
      have : ¬ equiv.helper (x::xs) [] := (Classical.iff_iff_not_iff_not.mp equiv_helper_iff_equiv_helper).mp p
      isFalse this
  | x::xs, y::ys =>
    if g : x = y then
      match decEquiv_helper xs ys with
      | isTrue p =>
        have : equiv.helper (x::xs) (y::ys) := equiv_helper_cons_iff.mpr (And.intro g p)
        isTrue this
      | isFalse p =>
        have h1 : ¬ (x = y ∧ equiv.helper xs ys) := Classical.not_and_iff_not_or_not.mpr (.inr p)
        have h2 : ¬ equiv.helper (x::xs) (y::ys) :=
          (Classical.iff_iff_not_iff_not.mp equiv_helper_cons_iff).mpr h1
        isFalse h2
    else
      have h1 : ¬ (x = y ∧ equiv.helper xs ys) := Classical.not_and_iff_not_or_not.mpr (.inl g)
      have h2 : ¬ equiv.helper (x::xs) (y::ys) :=
        (Classical.iff_iff_not_iff_not.mp equiv_helper_cons_iff).mpr h1
      isFalse h2

def decEquiv {base : NatGtOne} (a b : TZNumeral base) : Decidable (a ≈ b) :=
  match decEquiv_helper a.digits b.digits with
  | isTrue p => isTrue (equiv_iff_equiv_helper_digits.mpr p)
  | isFalse p => isFalse ((Classical.iff_iff_not_iff_not.mp equiv_iff_equiv_helper_digits).mpr p)

instance instdecEquiv {base : NatGtOne} (a b : TZNumeral base) : Decidable (a ≈ b) := decEquiv a b

#eval (⟨[1, 2, 3]⟩ : TZNumeral10) ≈ ⟨[1, 2, 3, 0, 0]⟩
#eval (⟨[1, 2, 3]⟩ : TZNumeral10) ≈ ⟨[2, 3, 0, 0]⟩

end TZNumeral

end Equivalence
