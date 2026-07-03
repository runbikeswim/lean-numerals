/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.EquivIsZero
import Numerals.AllDigitsBase
import Numerals.ToNatEquiv

namespace NumeralAux

section LeAux

def leAux (a b : List Nat) : Prop :=
  match a, b with
  | [], _ => True
  | x::xs, [] => x = 0 ∧ leAux xs []
  | x::xs, y::ys => if equivAux xs ys then x ≤ y else leAux xs ys

theorem leAux_nil {a : List Nat} : leAux [] a := by simp only [leAux]

theorem leAux_refl {a : List Nat} : leAux a a := by
  match a with
  | [] => simp only [leAux]
  | x::xs => simp only [leAux, equivAux_refl, reduceIte, Nat.le_refl]

theorem leAux_cons_iff {x y : Nat} {xs ys : List Nat} :
  leAux (x::xs) (y::ys) ↔ if equivAux xs ys then x ≤ y else leAux xs ys := by
  rw [leAux.eq_def]

section Equiv_LeAux

theorem not_equivAux_of_leAux_cons_of_ne_le {x y : Nat} {xs ys : List Nat}
  (hl : leAux (x::xs) (y::ys)) (hn : ¬ x ≤ y) : ¬ equivAux xs ys := by
  have : if equivAux xs ys then x ≤ y else leAux xs ys := leAux_cons_iff.mp hl
  false_or_by_contra; rename _ => hc
  simp only [hc, reduceIte] at this
  contradiction

theorem leAux_of_equivAux {a b : List Nat} (h : equivAux a b) : leAux a b := by
  induction a generalizing b with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b with
    | [] =>
      simp only [equivAux] at h
      simp only [leAux]
      exact And.intro h.left (ih h.right)
    | y::ys =>
      simp only [equivAux] at h
      simp only [leAux, h.right, reduceIte, h.left, Nat.le_refl]

theorem equivAux_nil_of_leAux_nil {a : List Nat} (h : leAux a []) : equivAux [] a  := by
  induction a with
  | nil  => exact equivAux_refl
  | cons x xs ih =>
    rw [equivAux.eq_def]
    rw [leAux.eq_def] at h
    simp only at ih h ⊢
    exact And.intro h.left (ih h.right)

theorem leAux_nil_iff_equivAux_nil {a : List Nat} : leAux a [] ↔ equivAux [] a := by
  constructor
  · intro h
    exact equivAux_nil_of_leAux_nil h
  · intro h
    exact leAux_of_equivAux (equivAux_symm h)

end Equiv_LeAux

/-
`leAux` is _almost_ antisymmetric
-/
theorem equivAux_iff_leAux_and_leAux {a b : List Nat}:
  equivAux a b ↔ leAux a b ∧ leAux b a := by
  constructor
  · intro h
    have h1 : leAux a b := leAux_of_equivAux h
    have h2 : leAux b a := leAux_of_equivAux (equivAux_symm h)
    exact And.intro h1 h2
  · intro h
    induction a generalizing b with
    | nil =>
      unfold leAux at h
      match b with
      | [] => exact equivAux_refl
      | x::xs =>
        rw [equivAux.eq_def]
        simp only [true_and] at ⊢ h
        exact And.intro h.left (equivAux_nil_of_leAux_nil h.right)
    | cons x xs ih =>
      match b with
      | [] =>
        have : equivAux [] (x :: xs) := equivAux_nil_of_leAux_nil h.left
        exact equivAux_symm this
      | y::ys =>
        unfold leAux at h
        unfold equivAux
        if g : equivAux xs ys then
          simp only [g, equivAux_symm, reduceIte] at h
          simp only [Nat.le_antisymm h.left h.right, g, true_and]
        else
          have : ¬ equivAux ys xs := not_equivAux_iff_not_equivAux.mp g
          simp only [g, reduceIte, this] at h
          have : equivAux xs ys := ih h
          contradiction

theorem leAux_total {a b : List Nat} : leAux a b ∨ leAux b a := by
  induction a generalizing b with
  | nil => exact .inl (leAux_nil)
  | cons x xs ih =>
    match b with
    | [] => exact .inr (leAux_nil)
    | y::ys =>
      if g1 : equivAux xs ys then
        if g2 : x ≤ y then
          have : leAux (x::xs) (y::ys) := by simp only [leAux, g1, g2, reduceIte]
          exact .inl this
        else
          have h1 : equivAux ys xs := equivAux_symm g1
          have h2 : y ≤ x := Nat.le_of_not_le g2
          have : leAux (y::ys) (x::xs) := by simp only [leAux, h1, h2, reduceIte]
          exact .inr this
      else
        have g2 : ¬ equivAux ys xs := not_equivAux_iff_not_equivAux.mp g1
        simp only [leAux, g1, g2, reduceIte]
        exact ih

section LeAux_Equiv

theorem leAux_of_leAux_of_equivAux {a b c : List Nat} (hab : leAux a b) (hbc : equivAux b c): leAux a c := by
  induction a generalizing b c with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b, c with
    | [], [] => simp_all only
    | y::ys, [] =>
      unfold leAux at hab ⊢
      unfold equivAux at hbc
      if g : equivAux xs ys then
        simp only [g, reduceIte, hbc.left] at hab
        have h1 : x = 0 := Nat.eq_zero_of_le_zero hab
        have h2 : leAux xs ys := leAux_of_equivAux g
        have h3 : leAux xs [] := ih  h2 hbc.right
        exact And.intro h1 h3
      else
        simp only [g, reduceIte, hbc.left] at hab
        have h1 : leAux xs [] := ih hab hbc.right
        have h2 : equivAux xs [] := equivAux_symm (equivAux_nil_of_leAux_nil h1)
        have h3 : equivAux xs ys := equivAux_trans h2 (equivAux_symm hbc.right)
        contradiction
    | [], z::zs =>
      have : equivAux (x :: xs) [] := equivAux_symm (equivAux_nil_of_leAux_nil hab)
      have : equivAux (x :: xs) (z :: zs) := equivAux_trans this hbc
      exact leAux_of_equivAux this
    | y::ys, z::zs =>
      unfold leAux at hab ⊢
      unfold equivAux at hbc
      if g1 : equivAux xs ys then
        simp only [g1, reduceIte, hbc.left] at hab
        if g2 : equivAux xs zs then
          simp only [g2, reduceIte]
          exact hab
        else
          simp only [g2, reduceIte]
          have : equivAux xs zs := equivAux_trans g1 hbc.right
          contradiction
      else
        simp only [g1, reduceIte] at hab
        if g2 : equivAux xs zs then
          simp only [g2, reduceIte]
          have : equivAux xs ys := equivAux_trans g2 (equivAux_symm hbc.right)
          contradiction
        else
          simp only [g2, reduceIte]
          exact ih hab hbc.right

theorem leAux_of_equivAux_of_leAux {a b c : List Nat} (hab : equivAux a b) (hbc : leAux b c): leAux a c := by
  induction a generalizing b c with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b, c with
    | [], [] =>
      simp only [equivAux] at hab
      simp only [leAux, And.intro hab.left (ih hab.right hbc), and_true]
    | y::ys, [] =>
      simp only [equivAux] at hab
      simp only [leAux] at hbc ⊢
      simp only [hab.left, hbc.left, true_and, (ih hab.right hbc.right)]
    | [], z::zs =>
      simp only [equivAux] at hab
      simp only [leAux] at hbc ⊢
      if h : equivAux xs zs then
        simp only [h, reduceIte, hab.left, Nat.zero_le]
      else
        simp only [h, reduceIte]
        have : leAux [] zs := leAux_nil
        exact ih hab.right this
    | y::ys, z::zs =>
      simp only [equivAux] at hab
      simp only [leAux] at hbc
      if h : equivAux ys zs then
        simp only [h, reduceIte] at hbc
        simp only [leAux, equivAux_trans hab.right h, reduceIte]
        rwa [hab.left]
      else
        simp only [h, reduceIte] at hbc
        have : ¬ equivAux xs zs := not_equivAux_of_equivAux_of_not_equivAux hab.right h
        simp only [leAux, this, reduceIte, ih hab.right hbc]

theorem equivAux_and_equivAux_of_leAux_of_leAux_of_equivAux {a b c : List Nat}
  (hab : leAux a b) (hbc : leAux b c) (hac : equivAux a c) : equivAux a b ∧ equivAux b c := by
  have h1 : leAux b a := leAux_of_leAux_of_equivAux hbc (equivAux_symm hac)
  have h2 : equivAux a b := equivAux_iff_leAux_and_leAux.mpr (And.intro hab h1)
  have h3 : leAux c b := leAux_of_equivAux_of_leAux (equivAux_symm hac) hab
  have h4 : equivAux b c := equivAux_iff_leAux_and_leAux.mpr (And.intro hbc h3)
  exact And.intro h2 h4

end LeAux_Equiv

section ToNatAux_LeAux

theorem toNatAux_le_of_leAux {a b : List Nat} {base : Nat} (h : leAux a b) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  toNatAux a base ≤ toNatAux b base := by
  induction a generalizing b with
  | nil => simp only [toNatAux_nil_eq, Nat.zero_le]
  | cons x xs ih =>
    match b with
    | [] =>
      have : isZeroAux (x::xs) := equivAux_nil_of_leAux_nil h
      have : toNatAux (x :: xs) base = 0 := (toNatAux_eq_zero_iff_isZeroAux hb).mpr this
      simp only [this, Nat.zero_le]
    | y::ys =>
      simp only [leAux_cons_iff] at h
      simp only [toNatAux_cons_eq]
      if g : equivAux xs ys then
        simp only [g, reduceIte] at h
        simp only [toNatAux_eq_of_equivAux g hb, Nat.add_le_add_right h (base * toNatAux ys base)]
      else
        simp only [g, reduceIte] at h
        have h1 : x < base ∧ xs.all (· < base) := allDigitsLtBase_cons_iff.mp halt
        have h2 : y < base ∧ ys.all (· < base) := allDigitsLtBase_cons_iff.mp hblt
        have h3 : toNatAux xs base ≤ toNatAux ys base := ih h h1.right h2.right
        have h4 : toNatAux xs base ≠ toNatAux ys base :=
          (Classical.iff_iff_not_iff_not.mp (toNatAux_eq_iff_equivAux h1.right h2.right hb)).mpr g
        have h3 : toNatAux xs base < toNatAux ys base := Nat.lt_of_le_of_ne h3 h4
        exact Nat.le_of_lt (Nat.add_mul_lt_of_lt_of_lt h3 h1.left)

theorem leAux_of_toNatAux_le_toNatAux_of {a b : List Nat} {base : Nat}
  (h : toNatAux a base ≤ toNatAux b base) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) : leAux a b := by
  induction a generalizing b with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b with
    | [] =>
      have : toNatAux [] base = 0 := toNatAux_nil_eq
      simp only [toNatAux_nil_eq, Nat.le_zero, toNatAux_eq_zero_iff_isZeroAux hb, isZeroAux, equivAux_iff_equivAux] at h
      exact leAux_of_equivAux h
    | y::ys =>
      simp only [toNatAux_cons_eq] at h
      simp only [leAux]
      if g : equivAux xs ys then
        simp only [g, reduceIte]
        rw [toNatAux_eq_of_equivAux g hb] at h
        exact Nat.le_of_add_le_add_right h
      else
        have halt' : x < base ∧ xs.all (· < base) := allDigitsLtBase_cons_iff.mp halt
        have hblt' : y < base ∧ ys.all (· < base) := allDigitsLtBase_cons_iff.mp hblt
        simp only [g, reduceIte]
        have : toNatAux xs base ≠ toNatAux ys base := by
          false_or_by_contra; rename _ => hc
          exact absurd (equivAux_of_toNatAux_eq hc halt'.right hblt'.right hb) g
        have : toNatAux xs base ≤ toNatAux ys base :=
          (Nat.add_mul_le_iff_le_of this halt'.left hblt'.left).mp h
        exact ih this halt'.right hblt'.right

theorem leAux_iff_toNatAux_le_toNatAux {a b : List Nat} {base : Nat} (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  leAux a b ↔ (toNatAux a base) ≤ (toNatAux b base) := by
  constructor
  · intro h
    exact toNatAux_le_of_leAux h hb halt hblt
  · intro h
    exact leAux_of_toNatAux_le_toNatAux_of h hb halt hblt

end ToNatAux_LeAux

theorem leAux_trans {a b c : List Nat} (hab : leAux a b) (hbc : leAux b c) : leAux a c := by
  induction a generalizing b c with
  | nil => exact leAux_nil
  | cons x xs ihx =>
    match b, c with
    | [], [] => unfold leAux at hab ⊢; simp_all only [and_true]
    | y::ys, [] =>
      have : equivAux (y::ys) [] := equivAux_symm (equivAux_nil_of_leAux_nil hbc)
      exact leAux_of_leAux_of_equivAux hab this
    | [], z::zs =>
      have : equivAux (x::xs) [] := equivAux_symm (equivAux_nil_of_leAux_nil hab)
      exact leAux_of_equivAux_of_leAux this hbc
    | y::ys, z::zs =>
      unfold leAux at hab hbc ⊢
      if gxy : equivAux xs ys then
        if gyz : equivAux ys zs then
          have : equivAux xs zs := equivAux_trans gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact Nat.le_trans hab hbc
        else
          have : ¬ equivAux xs zs := not_equivAux_of_equivAux_of_not_equivAux gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact ihx (leAux_of_equivAux gxy) hbc
      else
        if gyz : equivAux ys zs then
          have : ¬ equivAux xs zs := not_equivAux_of_not_equivAux_of_equivAux gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact ihx hab (leAux_of_equivAux gyz)
        else
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          have : ¬ equivAux xs zs := by
            false_or_by_contra; rename _ => hc
            exact absurd (equivAux_and_equivAux_of_leAux_of_leAux_of_equivAux hab hbc hc).left gxy
          simp only [this, reduceIte]
          exact ihx hab hbc

def decLeAux (a b : List Nat) : Decidable (leAux a b) :=
  match a, b with
  | [], [] =>
    have : leAux [] [] := leAux_refl
    isTrue this
  | x::xs, [] =>
    if g : x = 0 then
      match decLeAux xs [] with
      | isFalse p =>
        have : ¬ leAux (x::xs) [] := by
          simp only [leAux, not_and]
          intro _
          exact p
        isFalse this
      | isTrue p =>
        have : leAux (x::xs) [] := by
          simp only [leAux, g, p, true_and]
        isTrue this
    else
      have : ¬ leAux (x::xs) [] := by
        simp only [leAux, not_and]
        intro _
        contradiction
      isFalse this
  | [], y::ys =>
    have : leAux [] (y::ys) := by simp only [leAux]
    isTrue this
  | x::xs, y::ys =>
    match decEquivAux xs ys with
    | isFalse p =>
      match decLeAux xs ys with
      | isFalse q =>
        have : ¬ leAux (x::xs) (y::ys) := by
          simp only [leAux, p, reduceIte, q, not_false_eq_true]
        isFalse this
      | isTrue q =>
        have : leAux (x::xs) (y::ys) := by
          simp only [leAux, p, reduceIte, q]
        isTrue this
    | isTrue p =>
      if g : x ≤ y then
        have : leAux (x::xs) (y::ys) := by
          simp only [leAux, p, reduceIte, g]
        isTrue this
      else
        have : ¬ leAux (x::xs) (y::ys) := by
          simp only [leAux, p, reduceIte, g, not_false_eq_true]
        isFalse this

instance instLeAux (a b : List Nat) : Decidable (leAux a b) := decLeAux a b

example : leAux [] [] := by decide
example : leAux [] [0] := by decide
example : leAux [] [1] := by decide
example : leAux [1] [1] := by native_decide
example : ¬ leAux [1] [0] := by native_decide

end LeAux

section LtAux

def ltAux (a b : List Nat) : Prop :=
  match a, b with
  | _, [] => False
  | [], y::ys => 0 < y ∨ ltAux [] ys
  | x::xs, y::ys => x < y ∧ ¬ ltAux ys xs ∨ ltAux xs ys
  termination_by a.length + b.length

theorem not_ltAux_cons_nil {x : Nat} {xs : List Nat} : ¬ ltAux (x::xs) [] := by
  simp only [ltAux, not_false_eq_true]

theorem ltAux_irrefl {a : List Nat} : ¬ ltAux a a  := by
  induction a with
  | nil => simp only [ltAux, not_false_eq_true]
  | cons x xs ih =>
    rw [ltAux.eq_def]
    match ga: x::xs, gb : x::xs with
    | _, [] => simp only [not_false_eq_true]
    | [], v::vs => rw [← gb]; simp only [not_or, ih, not_false_eq_true, and_true, Nat.lt_irrefl]
    | u::us, v::vs =>
      have : xs = vs := (List.cons.inj gb).right
      intro h
      simp only [← this, Nat.lt_irrefl, false_and, false_or] at h
      contradiction

theorem lt_of {x y : Nat} {xs ys : List Nat}
  (ha : x < y ∧ ¬ltAux ys xs ∨ ltAux xs ys) (hbl : y < x ∧ ¬ltAux xs ys) : x < y := by
  have : ¬ltAux xs ys := hbl.right
  have : x < y ∧ ¬ltAux ys xs := Or.resolve_right ha this
  exact this.left

theorem not_ltAux_of {x y : Nat} {xs ys : List Nat} (ha : x < y ∧ ¬ltAux ys xs ∨ ltAux xs ys)
  (ih: ∀ {b : List Nat}, ltAux xs b → ¬ ltAux b xs) (hbr : ltAux ys xs) : ¬ ltAux ys xs := by
  have : ¬ ltAux xs ys := by
    intro h
    exact absurd hbr (ih h)
  have : x < y ∧ ¬ltAux ys xs := Or.resolve_right ha this
  exact this.right

theorem ltAux_asymm {a b : List Nat} (ha : ltAux a b) : ¬ ltAux b a := by
  induction a generalizing b with
  | nil => simp only [ltAux, not_false_eq_true]
  | cons x xs ih =>
    match b with
    | [] => simp only [ltAux] at ⊢ ha
    | y::ys =>
      intro hb
      simp only [ltAux] at ha hb
      cases hb with
      | inl hbl => exact absurd (lt_of ha hbl) (Nat.not_lt_of_lt hbl.left)
      | inr hbr => exact absurd hbr (not_ltAux_of ha ih hbr)

theorem ltAux_nil_of_ltAux {a b : List Nat} (h : ltAux a b) : ltAux [] b := by
  induction a generalizing b with
  | nil => assumption
  | cons x xs ih =>
    rw [ltAux.eq_def] at ⊢ h
    match gb : b with
    | [] => simp only at ⊢ h
    | y::ys =>
      simp only at ⊢ h
      cases h with
      | inl hl =>
        have : 0 < y := Nat.zero_lt_of_lt hl.left
        exact .inl this
      | inr hr =>
        have : ltAux [] ys := ih hr
        exact .inr this

theorem ltAux_nil_iff_ltAux_zero {a : List Nat} : ltAux [] a ↔ ltAux [0] a:= by
  constructor <;>
  · intro h
    match a with
    | [] => simp only [ltAux] at h
    | x::xs => simp only [ltAux, not_false_eq_true, and_true] at ⊢ h; exact h

theorem ltAux_of_ltAux_cons {x : Nat} {xs ys : List Nat} (h : ltAux (x::xs) (x::ys)) : ltAux xs ys := by
  unfold ltAux at h
  have : ¬ (x < x ∧ ¬ltAux ys xs) := by
    simp only [not_and, Nat.lt_irrefl x]
    intro
    contradiction
  exact Or.resolve_left h this

section Equiv_LtAux

theorem not_equivAux_nil_of_ltAux_nil {a : List Nat} (h : ltAux [] a) : ¬ equivAux [] a := by
  induction a with
  | nil =>
    have : ¬ ltAux [] [] := ltAux_irrefl
    contradiction
  | cons y ys ih =>
    simp only [ltAux] at h
    have : ¬ y = 0 ↔ 0 < y := by
      constructor
      · intro hl
        rw [← ne_eq] at hl
        exact Nat.pos_of_ne_zero hl
      · intro hr
        have : y ≠ 0 := Nat.ne_zero_of_lt hr
        rwa [ne_eq y 0] at this
    simp only [equivAux, Classical.not_and_iff_not_or_not, this]
    cases h with
    | inl hl => exact .inl hl
    | inr hr => exact .inr (ih hr)

theorem not_equivAux_of_ltAux {a b : List Nat} (h : ltAux a b) : ¬ equivAux a b := by
  induction a generalizing b with
  | nil => exact not_equivAux_nil_of_ltAux_nil h
  | cons x xs ih =>
    match b with
    | [] => rw [ltAux.eq_def] at h; contradiction
    | y::ys =>
      simp only [ltAux] at h
      simp only [equivAux, Classical.not_and_iff_not_or_not]
      cases h with
      | inl hl => exact .inl (Nat.ne_of_lt hl.left)
      | inr hr => exact .inr (ih hr)

theorem not_ltAux_nil_of_equivAux_nil {a : List Nat} (h : equivAux [] a) : ¬ ltAux [] a := by
  induction a with
  | nil => exact ltAux_irrefl
  | cons y ys ih =>
    unfold equivAux at h
    simp only [ltAux, not_or, Nat.not_lt, Nat.le_zero]
    exact And.intro h.left (ih h.right)

theorem not_ltAux_of_equivAux {a b : List Nat} (h : equivAux a b) : ¬ ltAux a b := by
  induction a generalizing b with
  | nil => exact not_ltAux_nil_of_equivAux_nil h
  | cons x xs ih =>
    match b with
    | [] => simp only [ltAux, not_false_eq_true]
    | y::ys =>
      simp only [equivAux] at h
      simp only [ltAux, not_or, Classical.not_and_iff_not_or_not, Classical.not_not]
      have : ¬ x < y := by rw [h.left]; exact Nat.lt_irrefl y
      exact And.intro (.inl this) (ih h.right)

theorem ltAux_nil_of_not_equivAux_nil_of_not_ltAux_nil {a : List Nat}
  (h1 : ¬ equivAux [] a) (h2 : ¬ ltAux a []) : ltAux [] a := by
  induction a with
  | nil => unfold equivAux at h1; simp only [not_true] at h1
  | cons x xs ih =>
    unfold equivAux at h1
    simp only [Classical.not_and_iff_not_or_not] at h1
    unfold ltAux
    cases h1 with
    | inl h1l =>
      have : 0 < x := Nat.zero_lt_of_ne_zero h1l
      exact .inl this
    | inr h1r =>
      have : ¬ ltAux xs [] := by simp only [ltAux, not_false_eq_true]
      exact .inr (ih h1r this)

theorem ltAux_of_not_equivAux_of_not_ltAux {a b : List Nat}
  (h1 : ¬ equivAux a b) (h2 : ¬ ltAux b a) : ltAux a b := by
  induction a generalizing b with
  | nil => exact ltAux_nil_of_not_equivAux_nil_of_not_ltAux_nil h1 h2
  | cons x xs ihx =>
    unfold equivAux at h1
    match b with
    | [] =>
      simp only [Classical.not_and_iff_not_or_not] at h1
      unfold ltAux at ⊢ h2
      simp only [not_or, Nat.not_lt, Nat.le_zero_eq] at h1 h2
      have : ¬¬x = 0 := not_not_intro h2.left
      have : ¬equivAux xs [] := Or.resolve_left h1 this
      have : ltAux xs [] := ihx this h2.right
      have : False := by simp only [ltAux] at this
      contradiction
    | y::ys =>
      simp only [Classical.not_and_iff_not_or_not] at h1
      unfold ltAux at ⊢ h2
      simp_all only [not_or, not_and, Classical.not_not, not_false_eq_true, and_true]
      if g : x < y then
        exact .inl g
      else
        cases h1 with
        | inl h1l =>
          have h1l' : ¬y = x := by rwa [← ne_eq, ne_comm, ne_eq] at h1l
          have : y ≤ x := Nat.le_of_not_lt g
          have : y < x := Nat.lt_of_le_of_ne this h1l'
          exact .inr (h2.left this)
        | inr h1r => exact .inr (ihx h1r h2.right)

theorem equivAux_of_not_ltAux_and_not_ltAux {a b : List Nat} (h : ¬ ltAux a b ∧ ¬ ltAux b a) : equivAux a b := by
  false_or_by_contra; rename _ => hc
  exact absurd (ltAux_of_not_equivAux_of_not_ltAux hc h.right) h.left

end Equiv_LtAux

section LeAux_LtAux

theorem leAux_of_ltAux {a b : List Nat} (h : ltAux a b) : leAux a b := by
  induction a generalizing b with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b with
    | [] => exact absurd h (not_ltAux_cons_nil)
    | y::ys =>
      simp only [ltAux] at h
      simp only [leAux]
      if g : ltAux xs ys then
        have : ¬ equivAux xs ys := not_equivAux_of_ltAux g
        simp only [this, reduceIte, ih g]
      else
        have h1 : x < y ∧ ¬ltAux ys xs := Or.resolve_right h g
        have h2 : equivAux xs ys := equivAux_of_not_ltAux_and_not_ltAux (And.intro g h1.right)
        simp only [h2, reduceIte, Nat.le_of_lt h1.left]

theorem leAux_iff_not_ltAux {a b : List Nat} : leAux a b ↔ ¬ ltAux b a := by
  induction a generalizing b with
  | nil => unfold leAux ltAux; simp only [not_false_eq_true]
  | cons x xs ih =>
    unfold leAux ltAux
    match b with
    | [] =>
      have : x = 0 ↔ x ≤ 0 := by
        constructor
        · intro h
          simp only [h, Nat.le_refl]
        · intro h
          exact Nat.eq_zero_of_le_zero h
      simp only [not_or, Nat.not_lt, this, ih]
    | y::ys =>
      simp only [not_or, Classical.not_and_iff_not_or_not, Classical.not_not, Nat.not_lt, ih]
      constructor
      · intro h
        if g : equivAux xs ys then
          simp [g] at h
          have : ¬ltAux ys xs := ih.mp (leAux_of_equivAux g)
          exact And.intro (.inl h) this
        else
          simp [g] at h
          have : ltAux xs ys := ltAux_of_not_equivAux_of_not_ltAux g h
          exact And.intro (.inr this) h
      · intro h
        if g : ltAux xs ys then
          have : ¬ equivAux xs ys := not_equivAux_of_ltAux g
          simp only [this, reduceIte, h.right, not_false_eq_true]
        else
          have : equivAux xs ys := equivAux_of_not_ltAux_and_not_ltAux (And.intro g h.right)
          simp only [this, reduceIte]
          exact Or.resolve_right h.left g

theorem ltAux_iff_leAux_and_not_equivAux {a b : List Nat} : ltAux a b ↔ leAux a b ∧ ¬ equivAux a b := by
  constructor
  · intro h
    exact And.intro (leAux_of_ltAux h) (not_equivAux_of_ltAux h)
  · intro h
    have : ¬ ltAux b a := leAux_iff_not_ltAux.mp h.left
    exact ltAux_of_not_equivAux_of_not_ltAux h.right this

theorem ltAux_of_ltAux_of_leAux {a b c : List Nat} (hab : ltAux a b) (hbc : leAux b c) : ltAux a c := by
  have h1 : leAux a c := leAux_trans (leAux_of_ltAux hab) hbc
  have h2 : equivAux a c → equivAux a b ∧ equivAux b c := by
    intro h
    exact equivAux_and_equivAux_of_leAux_of_leAux_of_equivAux (leAux_of_ltAux hab) hbc h
  have h3 : equivAux a c → ¬ ltAux a b := by
    intro h
    exact not_ltAux_of_equivAux (h2 h).left
  have h4 : ¬ equivAux a c := fun h : equivAux a c => absurd hab (h3 h)
  exact ltAux_iff_leAux_and_not_equivAux.mpr (And.intro h1 h4)

theorem ltAux_of_leAux_of_ltAux {a b c : List Nat} (hab : leAux a b) (hbc : ltAux b c) : ltAux a c := by
  have h1 : leAux a c := leAux_trans hab (leAux_of_ltAux hbc)
  have h2 : equivAux a c → equivAux a b ∧ equivAux b c := by
    intro h
    exact equivAux_and_equivAux_of_leAux_of_leAux_of_equivAux hab (leAux_of_ltAux hbc) h
  have h3 : equivAux a c → ¬ ltAux b c := by
    intro h
    exact not_ltAux_of_equivAux (h2 h).right
  have h4 : ¬ equivAux a c := fun h : equivAux a c => absurd hbc (h3 h)
  exact ltAux_iff_leAux_and_not_equivAux.mpr (And.intro h1 h4)

/-
asserts that `ltAux` and `leAux` are a basis for an instance of class `Std.LawfulOrderLT`
-/
theorem ltAux_iff_leAux_and_not_leAux {a b : List Nat} : ltAux a b ↔ leAux a b ∧ ¬ leAux b a := by
  constructor
  · intro h
    have : ltAux a b ↔ ¬ leAux b a := by
      rw [Classical.iff_iff_not_iff_not, Classical.not_not, iff_comm]
      exact leAux_iff_not_ltAux
    have : ¬ leAux b a := this.mp h
    exact And.intro (leAux_of_ltAux h) this
  · intro h
    have : ¬ equivAux a b := by
      false_or_by_contra; rename _ => hc
      exact absurd (equivAux_iff_leAux_and_leAux.mp hc).right h.right
    exact ltAux_iff_leAux_and_not_equivAux.mpr (And.intro h.left this)

end LeAux_LtAux

section ToNatAux_LtAux

theorem toNatAux_lt_toNatAux_of_ltAux {a b : List Nat} {base : Nat} (h : ltAux a b) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  toNatAux a base < toNatAux b base := by
  have h1 : toNatAux a base ≤ toNatAux b base := toNatAux_le_of_leAux (leAux_of_ltAux h) hb halt hblt
  have h2 : ¬ equivAux a b := not_equivAux_of_ltAux h
  have h3 : toNatAux a base = toNatAux b base ↔ equivAux a b := toNatAux_eq_iff_equivAux halt hblt hb
  have h4 : ¬ toNatAux a base = toNatAux b base := (Classical.iff_iff_not_iff_not.mp h3).mpr h2
  exact Nat.lt_of_le_of_ne h1 h4

theorem ltAux_of_toNatAux_lt_toNatAux {a b : List Nat} {base : Nat}
  (h : toNatAux a base < toNatAux b base) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  ltAux a b := by
  have h1 : toNatAux a base ≤ toNatAux b base := Nat.le_of_lt h
  have h2 : ¬ toNatAux a base = toNatAux b base := Nat.ne_of_lt h
  have h3 : toNatAux a base = toNatAux b base ↔ equivAux a b := toNatAux_eq_iff_equivAux halt hblt hb
  have h4 : ¬ equivAux a b := (Classical.iff_iff_not_iff_not.mp h3).mp h2
  exact ltAux_iff_leAux_and_not_equivAux.mpr (And.intro (leAux_of_toNatAux_le_toNatAux_of h1 hb halt hblt) h4)

theorem ltAux_iff_toNatAux_lt_toNatAux {a b : List Nat} {base : Nat} (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  ltAux a b ↔ toNatAux a base < toNatAux b base := by
  constructor
  · intro h
    exact toNatAux_lt_toNatAux_of_ltAux h hb halt hblt
  · intro h
    exact ltAux_of_toNatAux_lt_toNatAux h hb halt hblt

end ToNatAux_LtAux

theorem ltAux_trans {a b c : List Nat} (hab : ltAux a b) (hbc : ltAux b c) : ltAux a c := by
  induction a generalizing b c with
  | nil => exact ltAux_nil_of_ltAux hbc
  | cons x xs ihx =>
    unfold ltAux at hab hbc ⊢
    match b, c with
    | [], [] | y::ys, [] | [], z::zs => simp_all only
    | y::ys, z::zs =>
      simp only at hab hbc ⊢
      rw [← leAux_iff_not_ltAux] at hab hbc ⊢
      if gxy : ltAux xs ys then
        if gyz : ltAux ys zs then
          exact .inr (ihx gxy gyz)
        else
          simp only [gyz, or_false] at hbc
          exact .inr (ltAux_of_ltAux_of_leAux gxy hbc.right)
      else
        if gyz : ltAux ys zs then
          simp only [gxy, or_false] at hab
          exact .inr (ltAux_of_leAux_of_ltAux hab.right gyz)
        else
          simp only [gxy, gyz, or_false] at hab hbc
          exact .inl (And.intro (Nat.lt_trans hab.left hbc.left) (leAux_trans hab.right hbc.right))

def decLtAux (a b : List Nat) : Decidable (ltAux a b) :=
  match ga : a, gb : b with
  | x, [] =>
    have : ¬ ltAux x [] := by rw [ltAux.eq_def]; simp only [not_false_eq_true]
    isFalse this
  | [], y::ys =>
    if g : 0 < y then
      have : ltAux [] (y::ys) := by
        rw [ltAux.eq_def]
        simp only [g, true_or]
      isTrue this
    else
      match decLtAux [] ys with
      | isFalse p =>
        have : ¬ ltAux [] (y::ys) := by
          rw [ltAux.eq_def]
          simp only [g, p, false_or, not_false_eq_true]
        isFalse this
      | isTrue p =>
        have : ltAux [] (y::ys) := by
          rw [ltAux.eq_def]
          simp only [g, p, false_or]
        isTrue this
  | x::xs, y::ys =>
    if gxy : x < y then
      match gxsys : decLtAux ys xs with
      | isFalse p =>
        have : ltAux (x::xs) (y::ys) := by
          rw [ltAux.eq_def]
          simp only [gxy, p, not_false_eq_true, true_and, true_or]
        isTrue this
      | isTrue p =>
        have : ¬ ltAux (x::xs) (y::ys) := by
          rw [ltAux.eq_def]
          simp only [gxy, p, not_true_eq_false, and_false, false_or]
          exact ltAux_asymm p
        isFalse this
    else
      match decLtAux xs ys with
      | isFalse p =>
        have : ¬ ltAux (x::xs) (y::ys) := by
          rw [ltAux.eq_def]
          simp only [gxy, false_and, false_or, p, not_false_eq_true]
        isFalse this
      | isTrue p =>
        have : ltAux (x::xs) (y::ys) := by
          rw [ltAux.eq_def]
          simp only [gxy, false_and, false_or, p]
        isTrue this
  termination_by a.length + b.length

instance instLtAux (a b : List Nat) : Decidable (ltAux a b) := decLtAux a b

end LtAux

end NumeralAux
