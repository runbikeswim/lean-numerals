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
  cons x xs ≈ cons y ys ↔ x = y ∧ xs ≈ ys := by
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
  Iff.intro equiv_helper_symm equiv_helper_symm

theorem equiv_symm {base : NatGtOne} {a b : TZNumeral base} (hab : a ≈ b) : b ≈ a := by
  exact equiv_helper_symm hab

theorem equiv_iff_equiv {base : NatGtOne} {a b : TZNumeral base} : a ≈ b ↔ b ≈ a :=
  Iff.intro equiv_symm equiv_symm

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

theorem not_equiv_helper_of_not_equiv_helper_of_equiv_helper {base : NatGtOne} {a b c : List base.Fin}
  (hab : ¬ equiv.helper base a b) (hbc : equiv.helper base b c) : ¬ equiv.helper base a c := by
  intro hac
  have : equiv.helper base a b := equiv_helper_trans hac (equiv_helper_symm hbc)
  contradiction

theorem not_equiv_of_not_equiv_of_equiv {base : NatGtOne} {a b c : TZNumeral base}
  (hab : ¬ a ≈ b) (hbc : b ≈ c) : ¬ a ≈ c := not_equiv_helper_of_not_equiv_helper_of_equiv_helper hab hbc

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
  decEquiv_helper a.digits b.digits

instance instDecEquiv {base : NatGtOne} (a b : TZNumeral base) : Decidable (a ≈ b) := decEquiv a b

end Equivalence

section Equiv_NoTrailingZero

theorem eq_nil_of_equiv_helper_nil_of_noTrailingZero_helper {base : NatGtOne} {a : List base.Fin}
  (he : equiv.helper base [] a) (hn : noTrailingZero.helper base a) : a = [] := by
  match g : a with
  | [] => rfl
  | x::xs =>
    have h1 : x::xs ≠ [] := List.cons_ne_nil x xs
    have h2 : (x::xs).all (· = 0) := equiv_helper_nil_iff.mp he
    have h3 : (x::xs).getLast h1 = 0 :=
      beq_iff_eq.mp (List.getLast_true_of_all_true_of_ne_nil (x::xs) (· == 0) h2 h1)
    have h5 : (x::xs).getLast h1 ≠ 0 := by
      unfold noTrailingZero.helper at hn
      exact hn h1
    contradiction

theorem eq_zero_of_equiv_zero_of_noTrailingZero {base : NatGtOne} {a : TZNumeral base}
  (he : 0 ≈ a) (hn : noTrailingZero a) : a = 0 := by
  simp only [OfNat.ofNat, Zero.zero, zero, noTrailingZero, equiv, eq_iff_digits_eq] at ⊢ he hn
  exact eq_nil_of_equiv_helper_nil_of_noTrailingZero_helper he hn

theorem eq_of_equiv_helper_of_noTrailingZero_helper {base : NatGtOne} {a b : List base.Fin} (he : equiv.helper base a b)
(hna : noTrailingZero.helper base a) (hnb : noTrailingZero.helper base b) : a = b := by
  induction a generalizing b with
  | nil => exact Eq.symm (eq_nil_of_equiv_helper_nil_of_noTrailingZero_helper he hnb)
  | cons x xs ih =>
    match gb : b with
    | [] => exact eq_nil_of_equiv_helper_nil_of_noTrailingZero_helper (equiv_helper_symm he) hna
    | y::ys =>
      have h1 : x = y ∧ equiv.helper base xs ys := equiv_helper_cons_iff.mp he
      sorry

end Equiv_NoTrailingZero

section ToNat_Equiv

theorem toNat_helper_eq_zero_of_equiv_helper_nil {base : NatGtOne} {a : List base.Fin}
  (h: equiv.helper base [] a) : toNat.helper base a 1 0 = 0 := by
  induction a with
  | nil => exact toNat_helper_nil_eq
  | cons x xs ih =>
    simp only [equiv_helper_nil_iff, List.all_cons, Bool.and_eq_true] at h
    have h1 : x = 0 := beq_iff_eq.mp h.left
    have h2 : toNat.helper base xs 1 0 = 0 := ih (equiv_helper_nil_iff.mpr h.right)
    simp only [toNat_helper_cons_eq, h1, h2, Nat.add_eq_zero_iff, Fin.val_eq_zero_iff]
    simp only [Nat.mul_zero, and_true]
    rfl

theorem toNat_eq_zero_of_toNat_zero {base : NatGtOne} {a : TZNumeral base} (h: 0 ≈ a) :
  a.toNat = 0 := toNat_helper_eq_zero_of_equiv_helper_nil h

theorem toNat_helper_eq_of_equiv_helper {base : NatGtOne} {a b : List base.Fin} (h: equiv.helper base a b) :
  toNat.helper base a 1 0 = toNat.helper base b 1 0 := by
  induction a generalizing b with
  | nil => simp only [toNat_helper_eq_zero_of_equiv_helper_nil h, toNat_helper_nil_eq]
  | cons x xs ih =>
    match b with
    | [] => simp only [toNat_helper_eq_zero_of_equiv_helper_nil (equiv_helper_symm h), toNat_helper_nil_eq]
    | y::ys =>
      simp only [equiv_helper_cons_iff] at h
      simp only [toNat_helper_cons_eq]
      simp only [h.left, ih h.right]

theorem toNat_eq_of_equiv {base : NatGtOne} {a b : TZNumeral base} (h: a ≈ b) :
  a.toNat = b.toNat := toNat_helper_eq_of_equiv_helper h

theorem equiv_helper_nil_of_toNat_helper_zero {base : NatGtOne} {a : List base.Fin}
  (h: toNat.helper base a 1 0 = 0) : equiv.helper base [] a:= by
  induction a with
  | nil => exact equiv_helper_refl
  | cons x xs ih =>
    simp only [toNat_helper_cons_eq] at h
    have h1 : x = 0 := Fin.eq_of_val_eq (Nat.eq_zero_of_add_eq_zero_right h)
    have h2 : base.val = 0 ∨ toNat.helper base xs 1 0 = 0 :=
      Nat.zero_eq_mul.mp (Eq.symm (Nat.eq_zero_of_add_eq_zero_left h))
    have h3 : toNat.helper base xs 1 0 = 0 := by
      cases h2 with
      | inl h2l => exact absurd h2l base.val_ne_zero
      | inr h2r => exact h2r
    have h4 : equiv.helper base [] xs := ih h3
    have h5 : (xs.all fun x ↦ x == 0) = true := equiv_helper_nil_iff.mp h4
    simp only [equiv_helper_nil_iff, List.all_cons, Bool.and_eq_true]
    exact And.intro (beq_iff_eq.mpr h1) h5

theorem equiv_zero_of_toNat_zero {base : NatGtOne} {a : TZNumeral base} (h: a.toNat = 0) :
  0 ≈ a := equiv_helper_nil_of_toNat_helper_zero h

theorem equiv_helper_of_toNat_helper_eq {base : NatGtOne} {a b : List base.Fin}
  (h: toNat.helper base a 1 0 = toNat.helper base b 1 0) :
  equiv.helper base a b := by
  induction a generalizing b with
  | nil => rw [toNat_helper_nil_eq] at h; exact equiv_helper_nil_of_toNat_helper_zero (Eq.symm h)
  | cons x xs ih =>
    match g: b with
    | [] =>
      rw [toNat_helper_nil_eq] at h
      exact equiv_helper_symm (equiv_helper_nil_of_toNat_helper_zero h)
    | y::ys =>
      simp only [toNat_helper_cons_eq] at h
      simp only [equiv_helper_cons_iff]
      have : x.val = y.val ∧ toNat.helper base xs 1 0 = toNat.helper base ys 1 0 :=
        (Nat.add_mul_eq_iff_eq_and_eq_of (Fin.isLt x) (Fin.isLt y)).mp h
      exact And.intro (Fin.eq_of_val_eq this.left) (ih this.right)

theorem equiv_of_toNat_eq {base : NatGtOne} {a b : TZNumeral base}
  (h: a.toNat = b.toNat) : a ≈ b := equiv_helper_of_toNat_helper_eq h

theorem equiv_helper_iff_toNat__helper_eq {base : NatGtOne} {a b : List base.Fin} :
  equiv.helper base a b ↔ toNat.helper base a 1 0 = toNat.helper base b 1 0 :=
  Iff.intro toNat_helper_eq_of_equiv_helper equiv_helper_of_toNat_helper_eq

theorem equiv_iff_toNat_eq {base : NatGtOne} {a b : TZNumeral base} :
  a ≈ b ↔ a.toNat = b.toNat := equiv_helper_iff_toNat__helper_eq

end ToNat_Equiv

end TZNumeral

namespace Numeral

def equiv {base : NatGtOne} (a b : Numeral base) : Prop := a.toTZNumeral ≈ b.toTZNumeral

instance instHasEquiv {base : NatGtOne} : HasEquiv (Numeral base) := ⟨equiv⟩

theorem eq_zero_of_zero_equiv {base : NatGtOne} {a : Numeral base} (h : 0 ≈ a) : a = 0 := by
  have : a.toTZNumeral = 0 := TZNumeral.eq_zero_of_equiv_zero_of_noTrailingZero h a.noTZ
  exact (eq_iff_toTZNumeral_eq a 0).mpr this

theorem eq_of_equiv {base : NatGtOne} {a b : Numeral base} (h : a ≈ b) : a = b := by
  induction ga : a.digits generalizing b with
  | nil =>
    have h1 : 0 ≈ a := TZNumeral.equiv_zero_iff.mpr (by rw [ga]; exact List.all_nil)
    have h2 : 0 ≈ b := TZNumeral.equiv_trans h1 h
    rw [eq_zero_of_zero_equiv h1, eq_zero_of_zero_equiv h2]
  | cons x xs ih =>
    match gb : b.digits with
    | [] =>
      have h1 : 0 ≈ b := TZNumeral.equiv_zero_iff.mpr (by rw [gb]; exact List.all_nil)
      have h2 : 0 ≈ a := TZNumeral.equiv_trans h1 (TZNumeral.equiv_symm h)
      rw [eq_zero_of_zero_equiv h1, eq_zero_of_zero_equiv h2]
    | y::ys =>
      have h1 : TZNumeral.cons x xs ≈ TZNumeral.cons y ys := by
        simp only [TZNumeral.cons, TZNumeral.equiv]
        simp only [equiv, TZNumeral.equiv, ga, gb] at h
        assumption
      have h2 : x = y ∧ (xs : TZNumeral base) ≈ ys := TZNumeral.equiv_cons_iff.mp h1
      have h3 : TZNumeral.noTrailingZero.helper base xs := by sorry
      have h4 : TZNumeral.noTrailingZero.helper base ys := by sorry
      let p : Numeral base := ⟨xs, h3⟩
      let q : Numeral base := ⟨ys, h4⟩
      have h5 : p ≈ q := by sorry
      have h6 : p.digits = xs := sorry
      have h7 : p = q := sorry -- ih h5 h6
      have h9 : xs = ys := by
        sorry
      simp only [eq_iff_toTZNumeral_eq, TZNumeral.eq_iff_digits_eq, ga, gb]
      exact List.cons_eq_cons.mpr (And.intro h2.left h9)

end Numeral
