/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Extra
import Numerals.ToNat

namespace NumeralAux

section EquivAux

/-
Equivalence for lists of natural numbers - two lists are _equivalent_ if they only
differ with respect to _trailing zeros_.

`equivAux` is an [equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation) on
`List Nat` - which is asserted by theorems `equivAux_refl`, `equivAux_symm` and `equivAux_trans`.

Examples:
```
#eval equivAux [0, 1, 0] [0, 1] -- true
#eval equivAux [0, 1, 0] [1, 0] -- false
#eval equivAux [1, 1, 0] [11] -- false
```
-/
def equivAux (a b : List Nat) : Prop :=
  match a, b with
  | [], [] => True
  | x::xs, [] => x = 0 ∧ equivAux xs []
  | [], y::ys => y = 0 ∧ equivAux [] ys
  | x::xs, y::ys => x = y ∧ equivAux xs ys

theorem equivAux_nil_nil : equivAux [] [] := by simp only [equivAux]

theorem equivAux_cons_iff {x y : Nat} {xs ys : List Nat} : equivAux (x::xs) (y::ys) ↔ x = y ∧ equivAux xs ys := by
  simp only [equivAux]

theorem equivAux_nil_iff (a : List Nat) : equivAux [] a ↔ a.all (· == 0) := by
  induction a with
  | nil => simp only [equivAux, List.all_nil]
  | cons x xs ih =>
    simp only [equivAux, List.all_cons, Bool.and_eq_true, Nat.beq_eq_true_eq]
    have hmp : x = 0 ∧ equivAux [] xs → x = 0 ∧ (xs.all fun x ↦ x == 0) = true :=
      fun t ↦ And.intro t.left (ih.mp t.right)
    have hmpr : x = 0 ∧ (xs.all fun x ↦ x == 0) = true → x = 0 ∧ equivAux [] xs :=
      fun t ↦ And.intro t.left (ih.mpr t.right)
    exact Iff.intro hmp hmpr

/-
[Reflexivity](https://en.wikipedia.org/wiki/Reflexive_relation) for `equivAux`.

Together with `equivAux_symm` and `equivAux_trans` this ensures that `equivAux` is an
[equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation).
-/
theorem equivAux_refl {a : List Nat} : equivAux a a := by
  induction a with
  | nil => simp only [equivAux]
  | cons x xs ih =>
    simp only [equivAux, ih, true_and]

/-
[Symmetry](https://en.wikipedia.org/wiki/Symmetric_relation) for `equivAux`.

Together with `equivAux_refl` and `equivAux_trans` this ensures that `equivAux` is an
[equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation).
-/
theorem equivAux_symm {a b : List Nat} (hab : equivAux a b) : equivAux b a := by
  induction a generalizing b with
  | nil =>
    induction b with
    | nil => exact hab
    | cons y ys ihy =>
      unfold equivAux at ⊢ hab
      exact And.intro hab.left (ihy hab.right)
  | cons x xs ihx =>
    match b with
    | [] | y::ys =>
      unfold equivAux at ⊢ hab
      rw [hab.left]
      exact And.intro rfl (ihx hab.right)

/-
This lemma makes it possible to apply the `rw`-tactic.
-/
theorem equivAux_iff_equivAux {a b : List Nat} : equivAux a b ↔ equivAux b a :=
  Iff.intro (equivAux_symm ·) (equivAux_symm ·)

/-
[Transitivity](https://en.wikipedia.org/wiki/Transitive_relation) for `equivAux` with
`[] : List Nat` as first and two arbitrary parameters of type `List Nat` as second
and third element.
-/
theorem equivAux_trans_nil {a b : List Nat} (ha : equivAux [] a) (hab : equivAux a b) : equivAux [] b := by
  induction a generalizing b with
    | nil => exact hab
    | cons x xs ih =>
      unfold equivAux at ha hab
      match b with
      | [] =>
        simp only at hab
        exact ih ha.right hab.right
      | z::zs =>
        unfold equivAux
        simp only at ⊢ hab
        have : z = 0 := by rw [ha.left] at hab; exact (Eq.symm hab.left)
        exact And.intro this (ih ha.right hab.right)

/-
[Transitivity](https://en.wikipedia.org/wiki/Transitive_relation) for `equivAux`.

Together with `equivAux_refl` and `equivAux_symm` this ensures that `equivAux` is an
[equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation).
-/
theorem equivAux_trans {a b c : List Nat} (hab : equivAux a b) (hbc : equivAux b c) : equivAux a c := by
  induction a generalizing b c with
  | nil => exact equivAux_trans_nil hab hbc
  | cons x xs ihx =>
    unfold equivAux at ⊢ hab hbc
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

theorem not_equivAux_iff_not_equivAux {a b : List Nat} : ¬ equivAux a b ↔ ¬ equivAux b a :=
  Classical.iff_iff_not_iff_not.mp equivAux_iff_equivAux

theorem equivAux_cons_nil_of_equivAux_nil {xs : List Nat} (h : equivAux xs []) : equivAux (0::xs) [] := by
  unfold equivAux
  exact And.intro rfl h

theorem all_eq_zero_of_equivAux_nil {a : List Nat} (h : equivAux a []) : a.all (· = 0) := by
  induction a with
  | nil => exact List.all_nil
  | cons x xs ih =>
    simp only [equivAux] at h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact And.intro h.left (ih h.right)

theorem not_equivAux_cons_of_lt {x y : Nat} {xs ys : List Nat} (h : x < y) : ¬ equivAux (x::xs) (y::ys) := by
  have : x ≠ y := Nat.ne_of_lt h
  simp only [equivAux, Classical.not_and_iff_not_or_not]
  exact .inl this

theorem not_equivAux_of_equivAux_of_not_equivAux {a b c : List Nat}
  (hab : equivAux a b) (hbc : ¬ equivAux b c) : ¬ equivAux a c := by
  false_or_by_contra; rename _ => hac
  have : equivAux b c := equivAux_trans (equivAux_symm hab) hac
  contradiction

theorem not_equivAux_of_not_equivAux_of_equivAux {a b c : List Nat}
  (hab : ¬ equivAux a b) (hbc : equivAux b c) : ¬ equivAux a c := by
  false_or_by_contra; rename _ => hac
  have : equivAux a b := equivAux_trans hac (equivAux_symm hbc)
  contradiction

theorem equivAux_cons_iff_eq_and_equivAux {x y : Nat} {xs ys : List Nat} :
  equivAux (x::xs) (y::ys) ↔ x = y ∧ equivAux xs ys := by
  rw [equivAux]

/-
Decidable equivalence as defined by `equivAux` of a parameter
of type `List Nat` with `[] : List Nat`.
-/
def decEquivAux_nil (a : List Nat) : Decidable (equivAux [] a)  :=
  if g : a.all (· == 0) then
    have : equivAux [] a := (equivAux_nil_iff a).mpr g
    isTrue this
  else
    -- (iff_iff_not_iff_not.mp (equivAux_nil_iff a)).mpr g
    have : ¬ equivAux [] a ↔ ¬ a.all (· == 0) := Classical.iff_iff_not_iff_not.mp (equivAux_nil_iff a)
    have : ¬ equivAux [] a := this.mpr g
    isFalse this

instance instdecEquivAuxNil {a : List Nat} : Decidable (equivAux [] a) := decEquivAux_nil a

example : equivAux [] [] := by decide
example : equivAux [] [0, 0, 0, 0] := by decide
example : ¬ equivAux [] [1] := by decide
example : ¬ equivAux [] [1, 1, 0, 0] := by decide

/-
Decidable equivalence as defined by `equivAux` for two arbitrary parameters of type `List Nat`.
-/
def decEquivAux (a b : List Nat) : Decidable (equivAux a b)  :=
  match a, b with
  | [], [] => isTrue equivAux_refl
  | x::xs, [] =>
    if g : equivAux [] (x::xs) then
      isTrue (equivAux_symm g)
    else
      have : ¬ equivAux (x::xs) [] := (Classical.iff_iff_not_iff_not.mp equivAux_iff_equivAux).mp g
      isFalse this
  | [], y::ys => decEquivAux_nil (y::ys)
  | x::xs, y::ys =>
    if g : x = y then
      match decEquivAux xs ys with
      | isTrue p =>
        have : equivAux (x::xs) (y::ys) := equivAux_cons_iff.mpr (And.intro g p)
        isTrue this
      | isFalse p =>
        have : ¬ equivAux (x::xs) (y::ys) := by
          intro h
          exact absurd (equivAux_cons_iff.mp h).right p
        isFalse this
    else
      have : ¬ equivAux (x::xs) (y::ys) := by
        intro h
        exact absurd (equivAux_cons_iff.mp h).left g
      isFalse this

  termination_by a.length + b.length

instance instDecEquivAux {a b : List Nat} : Decidable (equivAux a b) := decEquivAux a b

example : ¬ equivAux [] [1] := by decide
example : equivAux [1] [1, 0] := by native_decide
example : equivAux [1, 1, 0, 0] [1, 1] := by native_decide
example : ¬ equivAux [1] [1, 2] := by native_decide

end EquivAux

section IsZeroAux

/-
A value of type `List Nat` is considered a representation of _zero_, if is is
equivalent with respect to `equivAux` to the empty list, means means that all elements of
the list must be `0 : Nat`.

This property is independent of the `base` of the respective numeral.
-/
abbrev isZeroAux (a : List Nat) : Prop := equivAux [] a

/-
`[] : List Nat` is itself a representation of _zero_.
-/
theorem isZeroAux_nil : isZeroAux [] := equivAux_refl

theorem ne_nil_of_not_isZeroAux {a : List Nat} (h : ¬ isZeroAux a) : a ≠ [] :=
  match a with
  | [] => absurd isZeroAux_nil h
  | x::xs => List.cons_ne_nil x xs

/-
A non-empty list can only be a representation of _zero_, if its head is `0 : Nat`
and the tail is also a representation of _zero_.
-/
theorem isZeroAux_cons_iff_eq_zero_and_isZeroAux {x : Nat} {xs : List Nat} :
  isZeroAux (x::xs) ↔ x = 0 ∧ isZeroAux xs:= by
  unfold isZeroAux
  rw [equivAux.eq_def]

/-
This lemma is used in the proof of `toNatAux_eq_zero_iff_isZeroAux`.
-/
theorem isZeroAux_of_toNatAux_eq_zero {a : List Nat} {base : Nat} (h: toNatAux a base = 0) (hb : 1 < base) :
  isZeroAux a := by
  induction a with
  | nil =>
    rw [toNatAux] at h
    simp only [isZeroAux, equivAux_refl]
  | cons x xs ih =>
    rw [toNatAux_cons_eq] at h
    have h1 : x = 0 ∧ base * (toNatAux xs base) = 0 := Nat.eq_zero_of_add_eq_zero h
    have h2 : toNatAux xs base = 0 :=
      Or.resolve_left (Nat.zero_eq_mul.mp (Eq.symm h1.right)) (Nat.ne_zero_of_lt hb)
    have h3 : isZeroAux xs := ih h2
    exact isZeroAux_cons_iff_eq_zero_and_isZeroAux.mpr (And.intro h1.left h3)

/-
This lemma is used in the proofs of `toNatAux_eq_zero_iff_isZeroAux`
and `toNatAux_subAux_left_distrib_of_leAux`.

It is inverse implication of `isZeroAux_of_toNatAux_eq_zero`.
-/
theorem toNatAux_eq_zero_of_isZeroAux {a : List Nat} {base : Nat} (h: isZeroAux a) :
  toNatAux a base = 0 := by
  induction a with
  | nil => exact toNatAux_nil_eq
  | cons x xs ih =>
    rw [isZeroAux_cons_iff_eq_zero_and_isZeroAux] at h
    rw [toNatAux_cons_eq]
    have : toNatAux xs base = 0 := ih h.right
    rw [this, h.left, Nat.zero_add, Nat.mul_zero]

/-
This lemma makes it possible to use the `rw`-tactic.
-/
theorem toNatAux_eq_zero_iff_isZeroAux {a : List Nat} {base : Nat} (hb : 1 < base) :
  toNatAux a base = 0 ↔ isZeroAux a := by
  constructor
  · intro h
    exact isZeroAux_of_toNatAux_eq_zero h hb
  · intro h
    exact toNatAux_eq_zero_of_isZeroAux h

def decIsZeroAux (a : List Nat) : Decidable (isZeroAux a) := decEquivAux [] a

instance instIsZero (a : List Nat) : Decidable (isZeroAux a) := decIsZeroAux a

end IsZeroAux

end NumeralAux
