/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic
import Numerals.ToNat
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

theorem le_refl {base : NatGtOne} (a : TZNumeral base) : a ≤ a := by
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

/--
`le.helper` is _almost_ [antisymmetric](https://w.wiki/Srqa)
-/
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

/--
`le` is _almost_ [antisymmetric](https://w.wiki/Srqa)
-/
theorem equiv_iff_le_and_le {base : NatGtOne} {a b : TZNumeral base} :
  a ≈ b ↔ a ≤ b ∧ b ≤ a := equiv_helper_iff_le_helper_and_le_helper

end Equiv_LessThanOrEqualTo

theorem le_helper_total {base : NatGtOne} {a b : List base.Fin} :
  le.helper base a b ∨ le.helper base b a := by
  induction a generalizing b with
  | nil => exact .inl le_helper_nil
  | cons x xs ih =>
    match b with
    | [] => exact .inr le_helper_nil
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

theorem le_total {base : NatGtOne} (a b : TZNumeral base) :
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

theorem le_of_le_of_equiv {base : NatGtOne} {a b c : TZNumeral base}
  (hab : a ≤ b) (hbc : b ≈ c): a ≤ c := le_helper_of_le_helper_of_equiv_helper hab hbc

theorem le_helper_of_equiv_helper_of_le_helper {base : NatGtOne} {a b c : List base.Fin}
  (hab : equiv.helper base a b) (hbc : le.helper base b c): le.helper base a c := by
  induction a generalizing b c with
  | nil => exact le_helper_nil
  | cons x xs ih =>
    match b, c with
    | [], [] =>
      simp only [equiv.helper] at hab
      simp only [le.helper, And.intro hab.left (ih hab.right hbc), and_true]
    | y::ys, [] =>
      simp only [equiv.helper] at hab
      simp only [le.helper] at hbc ⊢
      simp only [hab.left, hbc.left, true_and, ih hab.right hbc.right]
    | [], z::zs =>
      simp only [equiv.helper] at hab
      simp only [le.helper] at hbc ⊢
      if h : equiv.helper base xs zs then
        simp only [h, reduceIte, hab.left]
        exact Fin.zero_le z
      else
        simp only [h, reduceIte]
        exact ih hab.right le_helper_nil
    | y::ys, z::zs =>
      simp only [equiv.helper] at hab
      simp only [le.helper] at hbc
      if h : equiv.helper base ys zs then
        simp only [h, reduceIte] at hbc
        simp only [le.helper, equiv_helper_trans hab.right h, reduceIte]
        rwa [hab.left]
      else
        simp only [h, reduceIte] at hbc
        have : ¬ equiv.helper base xs zs := not_equiv_helper_of_equiv_helper_of_not_equiv_helper hab.right h
        simp only [le.helper, this, reduceIte, ih hab.right hbc]

theorem le_of_equiv_of_le {base : NatGtOne} {a b c : TZNumeral base}
  (hab : a ≈ b) (hbc : b ≤ c): a ≤ c := le_helper_of_equiv_helper_of_le_helper hab hbc

theorem equiv_helper_and_equiv_helper_of_le_helper_of_le_helper_of_equiv_helper
  {base : NatGtOne} {a b c : List base.Fin}
  (hab : le.helper base a b) (hbc : le.helper base b c) (hac : equiv.helper base a c) :
  equiv.helper base a b ∧ equiv.helper base b c := by
  have h1 : le.helper base b a := le_helper_of_le_helper_of_equiv_helper hbc (equiv_helper_symm hac)
  have h2 : equiv.helper base a b := equiv_helper_iff_le_helper_and_le_helper.mpr (And.intro hab h1)
  have h3 : le.helper base c b := le_helper_of_equiv_helper_of_le_helper (equiv_helper_symm hac) hab
  have h4 : equiv.helper base b c := equiv_helper_iff_le_helper_and_le_helper.mpr (And.intro hbc h3)
  exact And.intro h2 h4

theorem equiv_and_equiv_of_le_of_le_of_equiv {base : NatGtOne} {a b c : TZNumeral base}
  (hab : a ≤ b) (hbc : b ≤ c) (hac : a ≈ c) : a ≈ b ∧ b ≈ c :=
  equiv_helper_and_equiv_helper_of_le_helper_of_le_helper_of_equiv_helper hab hbc hac

end LessThanOrEqualTo_Equiv

/--
shows that [transitivity](https://w.wiki/MqgX) of `le.helper` can be shown by only using its definition and
theorems from `Nat`
-/
theorem le_helper_trans {base : NatGtOne} {a b c : List base.Fin}
  (hab : le.helper base a b) (hbc : le.helper base b c) : le.helper base a c := by
  induction a generalizing b c with
  | nil => exact le_helper_nil
  | cons x xs ihx =>
    match b, c with
    | [], [] => unfold le.helper at hab ⊢; simp_all only [and_true]
    | y::ys, [] =>
      have : equiv.helper base (y::ys) [] := equiv_helper_symm (equiv_helper_nil_of_le_helper_nil hbc)
      exact le_helper_of_le_helper_of_equiv_helper hab this
    | [], z::zs =>
      have : equiv.helper base (x::xs) [] := equiv_helper_symm (equiv_helper_nil_of_le_helper_nil hab)
      exact le_helper_of_equiv_helper_of_le_helper this hbc
    | y::ys, z::zs =>
      unfold le.helper at hab hbc ⊢
      if gxy : equiv.helper base xs ys then
        if gyz : equiv.helper base ys zs then
          have : equiv.helper base xs zs := equiv_helper_trans gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact Nat.le_trans hab hbc
        else
          have : ¬ equiv.helper base xs zs := not_equiv_helper_of_equiv_helper_of_not_equiv_helper gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact ihx (le_helper_of_equiv_helper gxy) hbc
      else
        if gyz : equiv.helper base ys zs then
          have : ¬ equiv.helper base xs zs := not_equiv_helper_of_not_equiv_helper_of_equiv_helper gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact ihx hab (le_helper_of_equiv_helper gyz)
        else
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          have : ¬ equiv.helper base xs zs := by
            false_or_by_contra; rename _ => hc
            exact absurd (equiv_helper_and_equiv_helper_of_le_helper_of_le_helper_of_equiv_helper hab hbc hc).left gxy
          simp only [this, reduceIte]
          exact ihx hab hbc

theorem le_trans {base : NatGtOne} {a b c : TZNumeral base} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  le_helper_trans hab hbc

instance instIsPreorderLe {base : NatGtOne} : Std.IsPreorder (TZNumeral base) where
  le_refl := le_refl
  le_trans _ _ _ := le_trans

instance instIsLinearPreorderLe {base : NatGtOne} : Std.IsLinearPreorder (TZNumeral base) where
  le_total := le_total

section ToNat_LessThanOrEqualTo

theorem toNat_helper_le_of_le_helper {base : NatGtOne} {a b : List base.Fin}
  (h : le.helper base a b) : toNat.helper base a 1 0 ≤ toNat.helper base b 1 0 := by
  induction a generalizing b with
  | nil => simp only [toNat_helper_nil_eq, Nat.zero_le]
  | cons x xs ih =>
    match b with
    | [] =>
      have : equiv.helper base [] (x::xs) := equiv_helper_nil_of_le_helper_nil h
      have : toNat.helper base (x :: xs) 1 0 = 0 := toNat_helper_eq_zero_of_equiv_helper_nil this
      simp only [this, Nat.zero_le]
    | y::ys =>
      simp only [le_helper_cons_iff] at h
      simp only [toNat_helper_cons_eq]
      if g : equiv.helper base xs ys then
        simp only [g, reduceIte] at h
        have : toNat.helper base xs 1 0 ≤ toNat.helper base ys 1 0 :=
            ih (le_helper_of_equiv_helper g)
        calc ↑x + base.val * toNat.helper base xs 1 0 ≤ ↑y + base.val * toNat.helper base xs 1 0 :=
            Nat.add_le_add_right h (base.val * toNat.helper base xs 1 0)
          _ ≤ ↑y + base.val * toNat.helper base ys 1 0 :=
            Nat.add_le_add_left (Nat.mul_le_mul_left base.val this) ↑y
      else
        simp only [g, reduceIte] at h
        have h1 : ↑x < base.val := Fin.isLt x
        have h2 : toNat.helper base xs 1 0 ≤ toNat.helper base ys 1 0 := ih h
        have h3 : toNat.helper base xs 1 0 ≠ toNat.helper base ys 1 0 := by
          intro hc
          exact absurd (equiv_helper_of_toNat_helper_eq hc) g
        have h4 : toNat.helper base xs 1 0 < toNat.helper base ys 1 0 := Nat.lt_of_le_of_ne h2 h3
        exact Nat.le_of_lt (Nat.add_mul_lt_of_lt_of_lt h4 h1)

theorem toNat_le_of_le {base : NatGtOne} {a b : TZNumeral base} (h : a ≤ b) : a.toNat ≤ b.toNat :=
  toNat_helper_le_of_le_helper h

theorem le_helper_of_toNat_helper_le {base : NatGtOne} {a b : List base.Fin}
  (h : toNat.helper base a 1 0 ≤ toNat.helper base b 1 0) : le.helper base a b := by
  induction a generalizing b with
  | nil => exact le_helper_nil
  | cons x xs ih =>
    match b with
    | [] =>
      simp only [toNat_helper_nil_eq, Nat.le_zero] at h
      rw (occs := .pos [2])[← @toNat_helper_nil_eq base 1 0] at h
      exact le_helper_of_equiv_helper (equiv_helper_of_toNat_helper_eq h)
    | y::ys =>
      simp only [toNat_helper_cons_eq] at h
      simp only [le.helper]
      if g: equiv.helper base xs ys then
        simp only [g, reduceIte]
        rw [toNat_helper_eq_of_equiv_helper g] at h
        exact Nat.le_of_add_le_add_right h
      else
        simp only [g, reduceIte]
        have h1 : toNat.helper base xs 1 0 ≠ toNat.helper base ys 1 0 := by
          intro hc
          exact absurd (equiv_helper_of_toNat_helper_eq hc) g
        have h2 : toNat.helper base xs 1 0 ≤ toNat.helper base ys 1 0 :=
          (Nat.add_mul_le_iff_le_of h1 (Fin.isLt x) (Fin.isLt y)).mp h
        exact ih h2

theorem le_of_toNat_le {base : NatGtOne} {a b : TZNumeral base}
  (h : a.toNat ≤ b.toNat) : a ≤ b := le_helper_of_toNat_helper_le h

theorem le_helper_iff_toNat_helper_le {base : NatGtOne} {a b : List base.Fin} :
  le.helper base a b ↔ toNat.helper base a 1 0 ≤ toNat.helper base b 1 0 :=
  Iff.intro toNat_helper_le_of_le_helper le_helper_of_toNat_helper_le

theorem le_iff_toNat_le {base : NatGtOne} {a b : TZNumeral base} : a ≤ b ↔ a.toNat ≤ b.toNat :=
  le_helper_iff_toNat_helper_le

end ToNat_LessThanOrEqualTo


/--
gives a much shorter proof to `le_helper_trans`, but also without giving the same insight why the
definition of `le.helper` leads to [transitivity](https://w.wiki/MqgX)
-/
example {base : NatGtOne} {a b c : List base.Fin}
  (hab : le.helper base a b) (hbc : le.helper base b c) : le.helper base a c := by
  rw [le_helper_iff_toNat_helper_le] at ⊢ hab hbc
  exact Nat.le_trans hab hbc

def decLe_helper {base : NatGtOne} (a b : List base.Fin) : Decidable (le.helper base a b) :=
  match a, b with
  | [], [] =>
    isTrue le_helper_refl
  | x::xs, [] =>
    if g : x = 0 then
      match decLe_helper xs [] with
      | isFalse p =>
        have : ¬ le.helper base (x::xs) [] := by
          simp only [le.helper, not_and]
          intro _
          exact p
        isFalse this
      | isTrue p =>
        have : le.helper base (x::xs) [] := by
          simp only [le.helper, g, p, true_and]
        isTrue this
    else
      have : ¬ le.helper base (x::xs) [] := by
        simp only [le.helper, not_and]
        intro _
        contradiction
      isFalse this
  | [], y::ys =>
    have : le.helper base [] (y::ys) := by simp only [le.helper]
    isTrue this
  | x::xs, y::ys =>
    match decEquiv_helper xs ys with
    | isFalse p =>
      match decLe_helper xs ys with
      | isFalse q =>
        have : ¬ le.helper base (x::xs) (y::ys) := by
          simp only [le.helper, p, reduceIte, q, not_false_eq_true]
        isFalse this
      | isTrue q =>
        have : le.helper base (x::xs) (y::ys) := by
          simp only [le.helper, p, reduceIte, q]
        isTrue this
    | isTrue p =>
      if g : x ≤ y then
        have : le.helper base (x::xs) (y::ys) := by
          simp only [le.helper, p, reduceIte, g]
        isTrue this
      else
        have : ¬ le.helper base (x::xs) (y::ys) := by
          simp only [le.helper, p, reduceIte, g, not_false_eq_true]
        isFalse this

instance instDecLeHelper (base : NatGtOne) (a b : List base.Fin) : Decidable (le.helper base a b) :=
  decLe_helper a b

def decLe {base : NatGtOne} (a b : TZNumeral base) : Decidable (a ≤ b) :=
  decLe_helper a.digits b.digits

instance instDecLe {base : NatGtOne} (a b : TZNumeral base) : Decidable (a ≤ b) := decLe a b

example : ([].toTZNumeral : TZNumeral10) ≤ [].toTZNumeral := by decide
example : ([].toTZNumeral : TZNumeral10) ≤ [0].toTZNumeral := by decide
example : ([].toTZNumeral : TZNumeral10) ≤ [1].toTZNumeral := by decide
example : ([1].toTZNumeral : TZNumeral10) ≤ [1].toTZNumeral  := by decide
example : ¬ ([1].toTZNumeral : TZNumeral10) ≤ [0].toTZNumeral := by decide

end LessThanOrEqualTo

section LessThan

def lt {base : NatGtOne} (n m : TZNumeral base) : Prop :=
  helper base n.digits m.digits where
  helper (base : NatGtOne) (a b : List base.Fin) :=
  match a, b with
  | _, [] => False
  | [], y::ys => 0 < y ∨ helper base [] ys
  | x::xs, y::ys => x < y ∧ ¬ helper base ys xs ∨ helper base xs ys
  termination_by a.length + b.length

instance instLt {base : NatGtOne} : LT (TZNumeral base) := ⟨lt⟩

theorem not_lt_helper_cons_nil {base : NatGtOne} {x : base.Fin} {xs : List base.Fin} :
  ¬ lt.helper base (x::xs) [] := by
  simp only [lt.helper, not_false_eq_true]

theorem not_lt_cons_zero {base : NatGtOne} {x : base.Fin} {xs : TZNumeral base} :
  ¬ (cons x xs) < 0 := not_lt_helper_cons_nil

theorem lt_helper_irrefl {base : NatGtOne} (a : List base.Fin) : ¬ lt.helper base a a  := by
  induction a with
  | nil => simp only [lt.helper, not_false_eq_true]
  | cons x xs ih =>
    simp only [lt.helper]
    intro hc
    cases hc with
    | inl hcl => exact absurd hcl.left (Fin.lt_irrefl x)
    | inr hcr => contradiction

theorem lt_irrefl {base : NatGtOne} (a : TZNumeral base) : ¬ a < a :=
  lt_helper_irrefl a.digits

theorem lt_of {base : NatGtOne} {x y : base.Fin} {xs ys : List base.Fin}
  (ha : x < y ∧ ¬ lt.helper base ys xs ∨ lt.helper base xs ys)
  (hbl : y < x ∧ ¬lt.helper base xs ys) : x < y := by
  have : ¬lt.helper base xs ys := hbl.right
  have : x < y ∧ ¬lt.helper base ys xs := Or.resolve_right ha this
  exact this.left

end LessThan
