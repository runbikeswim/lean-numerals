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
  | x::xs => simp only [le.helper, equiv_helper_refl, reduceIte, Fin.le_refl]

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
  (h : le.helper base a b) : toNat.helper base a.toListNatAux 1 0 ≤ toNat.helper base b.toListNatAux 1 0 := by
  induction a generalizing b with
  | nil =>
    simp only [List.toListNatAux_nil_eq, toNat_helper_nil_eq, Nat.zero_le]
  | cons x xs ih =>
    match b with
    | [] =>
      have : equiv.helper base [] (x::xs) := equiv_helper_nil_of_le_helper_nil h
      have : toNat.helper base (x :: xs).toListNatAux 1 0 = 0 := toNat_helper_eq_zero_of_equiv_helper_nil this
      simp only [this, Nat.zero_le]
    | y::ys =>
      simp only [le_helper_cons_iff] at h
      simp only [List.cons_toListNatAux_eq, toNat_helper_cons_eq]
      if g : equiv.helper base xs ys then
        simp only [g, reduceIte] at h
        have : toNat.helper base xs.toListNatAux 1 0 ≤ toNat.helper base ys.toListNatAux 1 0 :=
            ih (le_helper_of_equiv_helper g)
        calc ↑x + base.val * toNat.helper base xs.toListNatAux 1 0 ≤ ↑y + base.val * toNat.helper base xs.toListNatAux 1 0 :=
            Nat.add_le_add_right h (base.val * toNat.helper base xs.toListNatAux 1 0)
          _ ≤ ↑y + base.val * toNat.helper base ys.toListNatAux 1 0 :=
            Nat.add_le_add_left (Nat.mul_le_mul_left base.val this) ↑y
      else
        simp only [g, reduceIte] at h
        have h1 : ↑x < base.val := Fin.isLt x
        have h2 : toNat.helper base xs.toListNatAux 1 0 ≤ toNat.helper base ys.toListNatAux 1 0 := ih h
        have h3 : toNat.helper base xs.toListNatAux 1 0 ≠ toNat.helper base ys.toListNatAux 1 0 := by
          intro hc
          exact absurd (equiv_helper_of_toNat_helper_eq hc) g
        have h4 : toNat.helper base xs.toListNatAux 1 0 < toNat.helper base ys.toListNatAux 1 0 := Nat.lt_of_le_of_ne h2 h3
        exact Nat.le_of_lt (Nat.add_mul_lt_of_lt_of_lt h4 h1)

theorem toNat_le_of_le {base : NatGtOne} {a b : TZNumeral base} (h : a ≤ b) : a.toNat ≤ b.toNat :=
  toNat_helper_le_of_le_helper h

theorem le_helper_of_toNat_helper_le {base : NatGtOne} {a b : List base.Fin}
  (h : toNat.helper base a.toListNatAux 1 0 ≤ toNat.helper base b.toListNatAux 1 0) : le.helper base a b := by
  induction a generalizing b with
  | nil => exact le_helper_nil
  | cons x xs ih =>
    match b with
    | [] =>
      simp only [List.toListNatAux_nil_eq, toNat_helper_nil_eq, Nat.le_zero] at h
      rw (occs := .pos [2])[← @toNat_helper_nil_eq base 1 0] at h
      exact le_helper_of_equiv_helper (equiv_helper_of_toNat_helper_eq h)
    | y::ys =>
      simp only [List.cons_toListNatAux_eq, toNat_helper_cons_eq] at h
      simp only [le.helper]
      if g: equiv.helper base xs ys then
        simp only [g, reduceIte]
        rw [toNat_helper_eq_of_equiv_helper g] at h
        exact Nat.le_of_add_le_add_right h
      else
        simp only [g, reduceIte]
        have h1 : toNat.helper base xs.toListNatAux 1 0 ≠ toNat.helper base ys.toListNatAux 1 0 := by
          intro hc
          exact absurd (equiv_helper_of_toNat_helper_eq hc) g
        have h2 : toNat.helper base xs.toListNatAux 1 0 ≤ toNat.helper base ys.toListNatAux 1 0 :=
          (Nat.add_mul_le_iff_le_of h1 (Fin.isLt x) (Fin.isLt y)).mp h
        exact ih h2

theorem le_of_toNat_le {base : NatGtOne} {a b : TZNumeral base}
  (h : a.toNat ≤ b.toNat) : a ≤ b := le_helper_of_toNat_helper_le h

theorem le_helper_iff_toNat_helper_le {base : NatGtOne} {a b : List base.Fin} :
  le.helper base a b ↔ toNat.helper base a.toListNatAux 1 0 ≤ toNat.helper base b.toListNatAux 1 0 :=
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

example : (⟨[]⟩ : TZNumeral base10) ≤ (⟨[]⟩ : TZNumeral base10):= by decide
example : (⟨[]⟩ : TZNumeral base10) ≤ (⟨[0]⟩ : TZNumeral base10):= by decide
example : (⟨[]⟩ : TZNumeral base10) ≤ (⟨[1]⟩ : TZNumeral base10):= by decide
example : (⟨[1]⟩ : TZNumeral base10) ≤ (⟨[1]⟩ : TZNumeral base10):= by decide
example : ¬ (⟨[1]⟩ : TZNumeral base10) ≤ (⟨[0]⟩ : TZNumeral base10):= by decide

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
    | inr hcr => exact absurd hcr ih

theorem lt_irrefl {base : NatGtOne} (a : TZNumeral base) : ¬ a < a :=
  lt_helper_irrefl a.digits

theorem lt_of_helper {base : NatGtOne} {x y : base.Fin} {xs ys : List base.Fin}
  (ha : x < y ∧ ¬ lt.helper base ys xs ∨ lt.helper base xs ys)
  (hbl : y < x ∧ ¬ lt.helper base xs ys) : x < y := by
  have : ¬lt.helper base xs ys := hbl.right
  have : x < y ∧ ¬lt.helper base ys xs := Or.resolve_right ha this
  exact this.left

theorem not_lt_helper_of {base : NatGtOne}  {x y : base.Fin} {xs ys : List base.Fin}
  (h : x < y ∧ ¬lt.helper base ys xs ∨ lt.helper base xs ys)
  (ih: ∀ {b : List base.Fin}, lt.helper base xs b → ¬ lt.helper base b xs)
  (hbr : lt.helper base ys xs) : ¬ lt.helper base ys xs := by
  have : ¬ lt.helper base xs ys := by
    intro hc
    exact absurd hbr (ih hc)
  have : x < y ∧ ¬lt.helper base ys xs := Or.resolve_right h this
  exact this.right

theorem lt_helper_asymm {base : NatGtOne} {a b : List base.Fin} (h : lt.helper base a b) :
  ¬ lt.helper base b a := by
  induction a generalizing b with
  | nil => simp only [lt.helper, not_false_eq_true]
  | cons x xs ih =>
    match b with
    | [] => simp only [lt.helper] at ⊢ h
    | y::ys =>
      intro hb
      simp only [lt.helper] at h hb
      cases hb with
      | inl hbl => exact absurd (lt_of_helper h hbl) (Nat.not_lt_of_lt hbl.left)
      | inr hbr => exact absurd hbr (not_lt_helper_of h ih hbr)

theorem lt_asymm {base : NatGtOne} {a b : TZNumeral base} (ha : a < b) : ¬ b < a :=
  lt_helper_asymm ha

theorem lt_helper_nil_of_lt_helper {base : NatGtOne} {a b : List base.Fin} (h : lt.helper base a b) :
  lt.helper base [] b := by
  induction a generalizing b with
  | nil => assumption
  | cons x xs ih =>
    rw [lt.helper.eq_def] at ⊢ h
    match gb : b with
    | [] => simp only at ⊢ h
    | y::ys =>
      simp only at ⊢ h
      cases h with
      | inl hl =>
        have : 0 < y := Nat.zero_lt_of_lt hl.left
        exact .inl this
      | inr hr =>
        have : lt.helper base [] ys := ih hr
        exact .inr this

section Equiv_LessThan

theorem not_equiv_helper_nil_of_lt_helper_nil {base : NatGtOne} {a : List base.Fin}
  (h : lt.helper base [] a) : ¬ equiv.helper base [] a := by
  induction a with
  | nil =>
    have : ¬ lt.helper base [] [] := lt_helper_irrefl []
    contradiction
  | cons y ys ih =>
    simp only [lt.helper] at h
    have : 0 < y ↔ y ≠ 0 := Fin.pos_iff_ne_zero
    simp only [equiv.helper, Classical.not_and_iff_not_or_not, ← this]
    cases h with
    | inl hl => exact .inl hl
    | inr hr => exact .inr (ih hr)

theorem not_equiv_zero_of_lt_zero {base : NatGtOne} {a : TZNumeral base}
  (h : 0 < a) : ¬ 0 ≈ a := not_equiv_helper_nil_of_lt_helper_nil h

theorem not_equiv_helper_of_lt_helper {base : NatGtOne} {a b : List base.Fin} (h : lt.helper base a b) :
  ¬ equiv.helper base a b := by
  induction a generalizing b with
  | nil => exact not_equiv_helper_nil_of_lt_helper_nil h
  | cons x xs ih =>
    match b with
    | [] => rw [lt.helper.eq_def] at h; contradiction
    | y::ys =>
      simp only [lt.helper] at h
      simp only [equiv.helper, Classical.not_and_iff_not_or_not]
      cases h with
      | inl hl => exact .inl (Fin.ne_of_lt hl.left)
      | inr hr => exact .inr (ih hr)

theorem not_equiv_of_lt {base : NatGtOne} {a b : TZNumeral base} (h : a < b) : ¬ a ≈ b :=
  not_equiv_helper_of_lt_helper h

theorem not_lt_helper_nil_of_equiv_helper_nil {base : NatGtOne} {a : List base.Fin}
  (h : equiv.helper base [] a) : ¬ lt.helper base [] a := by
  induction a with
  | nil => exact lt_helper_irrefl []
  | cons y ys ih =>
    unfold equiv.helper at h
    simp only [lt.helper, not_or, Fin.not_lt]
    exact And.intro (Fin.le_zero_iff'.mpr h.left) (ih h.right)

theorem not_lt_zero_of_equiv_zero {base : NatGtOne} {a : TZNumeral base} (h : 0 ≈ a) : ¬ 0 < a :=
  not_lt_helper_nil_of_equiv_helper_nil h

theorem not_lt_helper_of_equiv_helper {base : NatGtOne} {a b : List base.Fin} (h : equiv.helper base a b) :
  ¬ lt.helper base a b := by
  induction a generalizing b with
  | nil => exact not_lt_helper_nil_of_equiv_helper_nil h
  | cons x xs ih =>
    match b with
    | [] => simp only [lt.helper, not_false_eq_true]
    | y::ys =>
      simp only [equiv.helper] at h
      simp only [lt.helper, not_or, Classical.not_and_iff_not_or_not, Classical.not_not]
      have : ¬ x < y := by rw [h.left]; exact Nat.lt_irrefl y
      exact And.intro (.inl this) (ih h.right)

theorem not_lt_of_equiv {base : NatGtOne} {a b : TZNumeral base} (h : a ≈ b) : ¬ a < b :=
  not_lt_helper_of_equiv_helper h

theorem lt_helper_nil_of_not_equiv_helper_nil {base : NatGtOne} {a : List base.Fin}
  (h : ¬ equiv.helper base [] a) : lt.helper base [] a := by
  induction a with
  | nil => unfold equiv.helper at h; simp only [not_true] at h
  | cons x xs ih =>
    unfold equiv.helper at h
    simp only [Classical.not_and_iff_not_or_not] at h
    unfold lt.helper
    cases h with
    | inl hl => exact .inl (Fin.pos_iff_ne_zero.mpr hl)
    | inr hr =>
      have : ¬ lt.helper base xs [] := by simp only [lt.helper, not_false_eq_true]
      exact .inr (ih hr)

theorem lt_zero_of_not_equiv_zero_of_not_lt_zero {base : NatGtOne} {a : TZNumeral base}
  (h : ¬ 0 ≈ a) : 0 < a := lt_helper_nil_of_not_equiv_helper_nil h

theorem lt_helper_of_not_equiv_helper_of_not_lt_helper {base : NatGtOne} {a b : List base.Fin}
  (h1 : ¬ equiv.helper base a b) (h2 : ¬ lt.helper base b a) : lt.helper base a b := by
  induction a generalizing b with
  | nil => exact lt_helper_nil_of_not_equiv_helper_nil h1
  | cons x xs ihx =>
    unfold equiv.helper at h1
    match g : b with
    | [] =>
      simp only [Classical.not_and_iff_not_or_not] at h1
      simp only [not_or, lt.helper] at h2
      cases h1 with
      | inl h1l =>
        have : x.val = 0 := Nat.eq_zero_of_not_pos h2.left
        exact absurd (Fin.eq_mk_iff_val_eq.mpr this) h1l
      | inr h1r =>
        have : lt.helper base xs [] := ihx h1r h2.right
        simp only [lt.helper] at this -- False
    | y::ys =>
      simp only [Classical.not_and_iff_not_or_not] at h1
      unfold lt.helper at ⊢ h2
      simp_all only [not_or, not_and, Classical.not_not, not_false_eq_true, and_true]
      if g : x < y then
        exact .inl g
      else
        cases h1 with
        | inl h1l =>
          have h1l' : ¬y = x := by rwa [← ne_eq, ne_comm, ne_eq] at h1l
          have : y < x := Or.resolve_left (Fin.eq_or_lt_of_le (Nat.le_of_not_lt g)) h1l'
          exact .inr (h2.left this)
        | inr h1r => exact .inr (ihx h1r h2.right)

theorem lt_of_not_equiv_of_not_lt {base : NatGtOne} {a b : TZNumeral base}
  (h1 : ¬ a ≈ b) (h2 : ¬ b < a) : a < b := lt_helper_of_not_equiv_helper_of_not_lt_helper h1 h2

theorem equiv_helper_of_not_lt_helper_and_not_lt_helper {base : NatGtOne} {a b : List base.Fin}
  (h : ¬ lt.helper base a b ∧ ¬ lt.helper base b a) : equiv.helper base a b := by
  false_or_by_contra; rename _ => hc
  exact absurd (lt_helper_of_not_equiv_helper_of_not_lt_helper hc h.right) h.left

theorem equiv_of_not_lt_and_not_lt {base : NatGtOne} {a b : TZNumeral base}
  (h : ¬ a < b ∧ ¬ b < a) : a ≈ b := equiv_helper_of_not_lt_helper_and_not_lt_helper h

end Equiv_LessThan

section LessThanOrEqual_LessThan

theorem le_helper_of_lt_helper {base : NatGtOne} {a b : List base.Fin} (h : lt.helper base a b) :
  le.helper base a b := by
  induction a generalizing b with
  | nil => exact le_helper_nil
  | cons x xs ih =>
    match b with
    | [] => exact absurd h (not_lt_helper_cons_nil)
    | y::ys =>
      simp only [lt.helper] at h
      simp only [le.helper]
      if g : lt.helper base xs ys then
        have : ¬ equiv.helper base xs ys := not_equiv_helper_of_lt_helper g
        simp only [this, reduceIte, ih g]
      else
        have h1 : x < y ∧ ¬lt.helper base ys xs := Or.resolve_right h g
        have h2 : equiv.helper base xs ys := equiv_helper_of_not_lt_helper_and_not_lt_helper (And.intro g h1.right)
        simp only [h2, reduceIte, Fin.le_of_lt h1.left]

theorem le_of_lt {base : NatGtOne} {a b : TZNumeral base} (h : a < b) : a ≤ b :=
  le_helper_of_lt_helper h

theorem le_helper_iff_not_lt_helper {base : NatGtOne} {a b : List base.Fin} :
  le.helper base a b ↔ ¬ lt.helper base b a := by
  induction a generalizing b with
  | nil => unfold le.helper lt.helper; simp only [not_false_eq_true]
  | cons x xs ih =>
    unfold le.helper lt.helper
    match b with
    | [] =>
      have : x = 0 ↔ x ≤ 0 := by
        constructor
        · intro h
          simp only [h, Fin.le_refl]
        · intro h
          exact Fin.eq_zero_of_le_zero h
      simp only [not_or, Fin.not_lt, this, ih]
    | y::ys =>
      simp only [not_or, Classical.not_and_iff_not_or_not, Classical.not_not, Fin.not_lt, ih]
      constructor
      · intro h
        if g : equiv.helper base xs ys then
          simp [g] at h
          have : ¬lt.helper base ys xs := ih.mp (le_helper_of_equiv_helper g)
          exact And.intro (.inl h) this
        else
          simp [g] at h
          have : lt.helper base xs ys := lt_helper_of_not_equiv_helper_of_not_lt_helper g h
          exact And.intro (.inr this) h
      · intro h
        if g : lt.helper base xs ys then
          have : ¬ equiv.helper base xs ys := not_equiv_helper_of_lt_helper g
          simp only [this, reduceIte, h.right, not_false_eq_true]
        else
          have : equiv.helper base xs ys := equiv_helper_of_not_lt_helper_and_not_lt_helper (And.intro g h.right)
          simp only [this, reduceIte]
          exact Or.resolve_right h.left g

theorem le_iff_not_lt {base : NatGtOne} {a b : TZNumeral base} : a ≤ b ↔ ¬ b < a :=
  le_helper_iff_not_lt_helper

theorem lt_helper_iff_le_helper_and_not_equiv_helper {base : NatGtOne} {a b : List base.Fin} :
  lt.helper base a b ↔ le.helper base a b ∧ ¬ equiv.helper base a b := by
  constructor
  · intro h
    exact And.intro (le_helper_of_lt_helper h) (not_equiv_helper_of_lt_helper h)
  · intro h
    have : ¬ lt.helper base b a := le_helper_iff_not_lt_helper.mp h.left
    exact lt_helper_of_not_equiv_helper_of_not_lt_helper h.right this

theorem lt_iff_le_and_not_equiv {base : NatGtOne} {a b : TZNumeral base} : a < b ↔ a ≤ b ∧ ¬ a ≈ b :=
  lt_helper_iff_le_helper_and_not_equiv_helper

theorem lt_helper_of_lt_helper_of_le_helper {base : NatGtOne} {a b c : List base.Fin}
  (hab : lt.helper base a b) (hbc : le.helper base b c) : lt.helper base a c := by
  have h1 : le.helper base a c := le_helper_trans (le_helper_of_lt_helper hab) hbc
  have h2 : equiv.helper base a c → equiv.helper base a b ∧ equiv.helper base b c := by
    intro h
    exact equiv_helper_and_equiv_helper_of_le_helper_of_le_helper_of_equiv_helper (le_helper_of_lt_helper hab) hbc h
  have h3 : equiv.helper base a c → ¬ lt.helper base a b := by
    intro h
    exact not_lt_helper_of_equiv_helper (h2 h).left
  have h4 : ¬ equiv.helper base a c := fun h : equiv.helper base a c => absurd hab (h3 h)
  exact lt_helper_iff_le_helper_and_not_equiv_helper.mpr (And.intro h1 h4)

theorem lt_of_lt_of_le {base : NatGtOne} {a b c : TZNumeral base}
  (hab : a < b) (hbc : b ≤ c) : a < c := lt_helper_of_lt_helper_of_le_helper hab hbc

theorem lt_helper_of_le_helper_of_lt_helper {base : NatGtOne} {a b c : List base.Fin}
  (hab : le.helper base a b) (hbc : lt.helper base b c) : lt.helper base a c := by
  have h1 : le.helper base a c := le_helper_trans hab (le_helper_of_lt_helper hbc)
  have h2 : equiv.helper base a c → equiv.helper base a b ∧ equiv.helper base b c := by
    intro h
    exact equiv_helper_and_equiv_helper_of_le_helper_of_le_helper_of_equiv_helper hab (le_helper_of_lt_helper hbc) h
  have h3 : equiv.helper base a c → ¬ lt.helper base b c := by
    intro h
    exact not_lt_helper_of_equiv_helper (h2 h).right
  have h4 : ¬ equiv.helper base a c := fun h : equiv.helper base a c => absurd hbc (h3 h)
  exact lt_helper_iff_le_helper_and_not_equiv_helper.mpr (And.intro h1 h4)

theorem lt_of_le_of_lt {base : NatGtOne} {a b c : TZNumeral base}
  (hab : a ≤ b) (hbc : b < c) : a < c := lt_helper_of_le_helper_of_lt_helper hab hbc

theorem lt_helper_iff_le_helper_and_not_le_helper {base : NatGtOne} {a b : List base.Fin} :
  lt.helper base a b ↔ le.helper base a b ∧ ¬ le.helper base b a := by
  constructor
  · intro h
    have : lt.helper base a b ↔ ¬ le.helper base b a := by
      rw [Classical.iff_iff_not_iff_not, Classical.not_not, iff_comm]
      exact le_helper_iff_not_lt_helper
    have : ¬ le.helper base b a := this.mp h
    exact And.intro (le_helper_of_lt_helper h) this
  · intro h
    have : ¬ equiv.helper base a b := by
      false_or_by_contra; rename _ => hc
      exact absurd (equiv_helper_iff_le_helper_and_le_helper.mp hc).right h.right
    exact lt_helper_iff_le_helper_and_not_equiv_helper.mpr (And.intro h.left this)

theorem lt_iff_le_and_not_le {base : NatGtOne} {a b : TZNumeral base} : a < b ↔ a ≤ b ∧ ¬ b ≤ a :=
  lt_helper_iff_le_helper_and_not_le_helper

instance instLawfulOrderLT {base : NatGtOne} : Std.LawfulOrderLT (TZNumeral base) where
  lt_iff a b := @lt_iff_le_and_not_le base a b

end LessThanOrEqual_LessThan

section ToNat_LessThan

theorem toNat_helper_lt_toNat_helper_of_lt_helper {base : NatGtOne} {a b : List base.Fin} (h : lt.helper base a b) :
  toNat.helper base a.toListNatAux 1 0 < toNat.helper base b.toListNatAux  1 0 := by
  have h1 : toNat.helper base a.toListNatAux  1 0 ≤ toNat.helper base b.toListNatAux  1 0 :=
    toNat_helper_le_of_le_helper (le_helper_of_lt_helper h)
  have h2 : ¬ equiv.helper base a b := not_equiv_helper_of_lt_helper h
  have h3 : toNat.helper base a.toListNatAux  1 0 = toNat.helper base b.toListNatAux  1 0 ↔ equiv.helper base a b :=
    Iff.symm equiv_helper_iff_toNat__helper_eq
  have h4 : ¬ toNat.helper base a.toListNatAux 1 0 = toNat.helper base b.toListNatAux  1 0 :=
    (Classical.iff_iff_not_iff_not.mp h3).mpr h2
  exact Nat.lt_of_le_of_ne h1 h4

theorem toNat_lt_toNat_of_lt {base : NatGtOne} {a b : TZNumeral base} (h : a < b) : a.toNat < b.toNat :=
  toNat_helper_lt_toNat_helper_of_lt_helper h

theorem lt_helper_of_toNat_helper_lt_toNat_helper {base : NatGtOne} {a b : List base.Fin}
  (h : toNat.helper base a.toListNatAux  1 0 < toNat.helper base b.toListNatAux  1 0) : lt.helper base a b := by
  have h1 : toNat.helper base a.toListNatAux  1 0 ≤ toNat.helper base b.toListNatAux  1 0 := Nat.le_of_lt h
  have h2 : ¬ toNat.helper base a.toListNatAux  1 0 = toNat.helper base b.toListNatAux  1 0 := Nat.ne_of_lt h
  have h3 : toNat.helper base a.toListNatAux  1 0 = toNat.helper base b.toListNatAux  1 0 ↔ equiv.helper base a b :=
    Iff.symm equiv_helper_iff_toNat__helper_eq
  have h4 : ¬ equiv.helper base a b := (Classical.iff_iff_not_iff_not.mp h3).mp h2
  exact lt_helper_iff_le_helper_and_not_equiv_helper.mpr (And.intro (le_helper_of_toNat_helper_le h1) h4)

theorem lt_of_toNat_lt_toNat {base : NatGtOne} {a b : TZNumeral base} (h : a.toNat < b.toNat) : a < b :=
  lt_helper_of_toNat_helper_lt_toNat_helper h

theorem lt_helper_iff_toNat_helper_lt_toNat_helper {base : NatGtOne} {a b : List base.Fin} :
  lt.helper base a b ↔ toNat.helper base a.toListNatAux 1 0 < toNat.helper base b.toListNatAux  1 0 :=
    Iff.intro toNat_helper_lt_toNat_helper_of_lt_helper lt_helper_of_toNat_helper_lt_toNat_helper

theorem lt_iff_toNat_lt {base : NatGtOne} {a b : TZNumeral base} : a < b ↔ a.toNat < b.toNat :=
  lt_helper_iff_toNat_helper_lt_toNat_helper

end ToNat_LessThan

theorem lt_helper_trans {base : NatGtOne} {a b c : List base.Fin}
  (hab : lt.helper base a b) (hbc : lt.helper base b c) : lt.helper base a c := by
  induction a generalizing b c with
  | nil => exact lt_helper_nil_of_lt_helper hbc
  | cons x xs ihx =>
    unfold lt.helper at hab hbc ⊢
    match b, c with
    | [], [] | y::ys, [] | [], z::zs => simp_all only
    | y::ys, z::zs =>
      simp only at hab hbc ⊢
      rw [← le_helper_iff_not_lt_helper] at hab hbc ⊢
      if gxy : lt.helper base xs ys then
        if gyz : lt.helper base ys zs then
          exact .inr (ihx gxy gyz)
        else
          simp only [gyz, or_false] at hbc
          exact .inr (lt_helper_of_lt_helper_of_le_helper gxy hbc.right)
      else
        if gyz : lt.helper base ys zs then
          simp only [gxy, or_false] at hab
          exact .inr (lt_helper_of_le_helper_of_lt_helper hab.right gyz)
        else
          simp only [gxy, gyz, or_false] at hab hbc
          exact .inl (And.intro (Nat.lt_trans hab.left hbc.left) (le_helper_trans hab.right hbc.right))

theorem lt_trans {base : NatGtOne} {a b c : TZNumeral base}
  (hab : a < b) (hbc : b < c) : a < c := lt_helper_trans hab hbc

def decLt_helper {base : NatGtOne} (a b : List base.Fin) : Decidable (lt.helper base a b) :=
  match ga : a, gb : b with
  | x, [] =>
    have : ¬ lt.helper base x [] := by rw [lt.helper.eq_def]; simp only [not_false_eq_true]
    isFalse this
  | [], y::ys =>
    if g : 0 < y then
      have : lt.helper base [] (y::ys) := by
        rw [lt.helper.eq_def]
        simp only [g, true_or]
      isTrue this
    else
      match decLt_helper [] ys with
      | isFalse p =>
        have : ¬ lt.helper base [] (y::ys) := by
          rw [lt.helper.eq_def]
          simp only [g, p, false_or, not_false_eq_true]
        isFalse this
      | isTrue p =>
        have : lt.helper base [] (y::ys) := by
          rw [lt.helper.eq_def]
          simp only [g, p, false_or]
        isTrue this
  | x::xs, y::ys =>
    if gxy : x < y then
      match gxsys : decLt_helper ys xs with
      | isFalse p =>
        have : lt.helper base (x::xs) (y::ys) := by
          rw [lt.helper.eq_def]
          simp only [gxy, p, not_false_eq_true, true_and, true_or]
        isTrue this
      | isTrue p =>
        have : ¬ lt.helper base (x::xs) (y::ys) := by
          rw [lt.helper.eq_def]
          simp only [gxy, p, not_true_eq_false, and_false, false_or]
          exact lt_helper_asymm p
        isFalse this
    else
      match decLt_helper xs ys with
      | isFalse p =>
        have : ¬ lt.helper base (x::xs) (y::ys) := by
          rw [lt.helper.eq_def]
          simp only [gxy, false_and, false_or, p, not_false_eq_true]
        isFalse this
      | isTrue p =>
        have : lt.helper base (x::xs) (y::ys) := by
          rw [lt.helper.eq_def]
          simp only [gxy, false_and, false_or, p]
        isTrue this
  termination_by a.length + b.length

instance decInstLt_helper {base : NatGtOne} (a b : List base.Fin) : Decidable (lt.helper base a b) := decLt_helper a b

def decLt {base : NatGtOne} (a b : TZNumeral base) : Decidable (a < b) :=
  decLt_helper a.digits b.digits

instance decInstLt {base : NatGtOne} (a b : TZNumeral base) : Decidable (a < b) := decLt a b

end LessThan

end TZNumeral

namespace Numeral

def le {base : NatGtOne} (n m : Numeral base) : Prop := n.toTZNumeral ≤ m.toTZNumeral

instance instLe {base : NatGtOne} : LE (Numeral base) := ⟨le⟩

theorem le_refl {base : NatGtOne} (n : Numeral base) : n ≤ n :=
  TZNumeral.le_refl n.toTZNumeral

theorem le_trans {base : NatGtOne} {n m k: Numeral base} (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k :=
  TZNumeral.le_trans hnm hmk

theorem le_antisymm {base : NatGtOne} {n m : Numeral base} : n ≤ m → m ≤ n → n = m := by
  intro h1 h2
  have : n.toTZNumeral ≈ m.toTZNumeral := TZNumeral.equiv_iff_le_and_le.mpr (And.intro h1 h2)
  exact eq_of_equiv this

theorem le_total {base : NatGtOne} (n m : Numeral base) : n ≤ m ∨ m ≤ n:=
  TZNumeral.le_total n.toTZNumeral m.toTZNumeral

instance instLeIsLinearOrder {base : NatGtOne} : Std.IsLinearOrder (Numeral base) where
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total := le_total

theorem le_iff_toNat_le {base : NatGtOne} {a b : Numeral base} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  exact TZNumeral.le_helper_iff_toNat_helper_le

def lt {base : NatGtOne} (n m : Numeral base) : Prop := n.toTZNumeral < m.toTZNumeral

instance instLt {base : NatGtOne} : LT (Numeral base) := ⟨lt⟩

theorem lt_iff_le_and_not_le {base : NatGtOne} {a b : Numeral base} : a < b ↔ a ≤ b ∧ ¬ b ≤ a :=
  TZNumeral.lt_helper_iff_le_helper_and_not_le_helper

instance instLawfulOrderLT {base : NatGtOne} : Std.LawfulOrderLT (Numeral base) where
  lt_iff a b := @lt_iff_le_and_not_le base a b

theorem lt_iff_toNat_lt {base : NatGtOne} {a b : Numeral base} : a < b ↔ a.toNat < b.toNat :=
  TZNumeral.lt_helper_iff_toNat_helper_lt_toNat_helper

end Numeral
