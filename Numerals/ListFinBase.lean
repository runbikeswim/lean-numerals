/-
Copyright (c) 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Extra
import Numerals.NatGtOne
import Numerals.AllDigitsBase

namespace NumeralAux

section FinBase

theorem eq_iff_coe_eq {base : Nat} (a b : Fin base) : a = b ↔ (a : Nat) = (b : Nat):= by
  constructor
  · intro h
    simp only [h]
  · intro h
    ext
    simp only [h]

theorem ne_iff_coe_ne {base : Nat} (a b : Fin base) : a ≠ b ↔ (a : Nat) ≠ (b : Nat) :=
  Classical.iff_iff_not_iff_not.mp (eq_iff_coe_eq a b)

end FinBase

section ListFinBase

def toListFinBase {base : Nat} (a : List Nat) (ha : allDigitsLtBase a base) : List (Fin base) :=
  match a with
  | [] => []
  | x::xs =>
    have : x < base ∧ allDigitsLtBase xs base := allDigitsLtBase_cons_iff.mp ha
    ⟨x, this.left⟩ :: toListFinBase xs this.right

theorem toListFinBase_nil_iff_nil {base : Nat} (a : List Nat) (ha : allDigitsLtBase a base) :
  toListFinBase a ha = [] ↔ a = [] := by
  constructor
  · intro h
    match g : a with
    | [] => rfl
    | x::xs =>
      simp only [toListFinBase] at h
      contradiction
  · intro h
    simp only [h, toListFinBase]

theorem toListFinBase_ne_nil_iff_ne_nil {base : Nat} (a : List Nat) (ha : allDigitsLtBase a base) :
  toListFinBase a ha ≠ [] ↔ a ≠ [] := by
    rw [Ne, Ne, ← Classical.iff_iff_not_iff_not]
    exact toListFinBase_nil_iff_nil a ha

theorem toListFinBase_cons {x base : Nat} {xs : List Nat} (ha : allDigitsLtBase (x::xs) base) :
  toListFinBase (x::xs) ha =
    ⟨x, (allDigitsLtBase_cons_iff.mp ha).left⟩ :: toListFinBase xs (allDigitsLtBase_cons_iff.mp ha).right := rfl

theorem toListFinBase_getLast_eq_getLast_of {base : Nat} (a : List Nat)
  (ha : allDigitsLtBase a base) (hn: a ≠ []) :
  ↑((toListFinBase a ha).getLast ((toListFinBase_ne_nil_iff_ne_nil a ha).mpr hn))
    = a.getLast hn := by
  induction a with
  | nil => contradiction
  | cons x xs ih =>
    match g : xs with
    | [] => simp only [List.getLast_singleton, toListFinBase]
    | y::ys =>
      have h1 : allDigitsLtBase (y :: ys) base := (allDigitsLtBase_cons_iff.mp ha).right
      have h2 : y::ys ≠ [] := List.cons_ne_nil y ys
      simp only [List.getLast_cons h2, toListFinBase_cons ha]
      exact ih h1 h2

def fromListFinBase {base : Nat} (a : List (Fin base)) : List Nat :=
  match a with
  | [] => []
  | x::xs => ↑x :: fromListFinBase xs

theorem fromListFinBase_nil_eq_nil {base : Nat} : fromListFinBase ([] : List (Fin base)) = [] := by
  rfl

theorem fromListFinBase_nil_iff_nil {base : Nat} (a : List (Fin base)) :
  fromListFinBase a = [] ↔ a = [] := by
  constructor
  · intro h
    match g : a with
    | [] => rfl
    | x::xs => contradiction
  · intro h
    simp only [h, fromListFinBase_nil_eq_nil]

theorem fromListFinBase_ne_nil_iff_ne_nil {base : Nat} (a : List (Fin base)) :
  fromListFinBase a ≠ [] ↔ a ≠ [] := by
    rw [Ne, Ne, ← Classical.iff_iff_not_iff_not]
    exact fromListFinBase_nil_iff_nil a

theorem fromListFinBase_cons {base : Nat} (x : Fin base) (xs : List (Fin base)) :
  fromListFinBase (x::xs) = ↑x :: fromListFinBase xs := by rfl

theorem fromListFinBase_eq_iff_eq {base : Nat} (a b : List (Fin base)) :
  fromListFinBase a = fromListFinBase b ↔ a = b := by
  constructor
  · intro h
    induction b generalizing a with
    | nil =>
      rw [fromListFinBase_nil_eq_nil] at h
      exact (fromListFinBase_nil_iff_nil a).mp h
    | cons y ys ih =>
      match a with
      | [] => contradiction
      | x::xs =>
        simp only [fromListFinBase_cons x xs, fromListFinBase_cons y ys] at h
        let h1 := List.cons_eq_cons.mp h
        have h2 : x = y := (eq_iff_coe_eq x y).mpr h1.left
        have h3 : xs = ys := (ih xs) h1.right
        exact List.cons_eq_cons.mpr (And.intro h2 h3)
  · intro h
    rw [h]

theorem fromListFinBase_getLast_eq_getLast_of {base : Nat} (a : List (Fin base)) (hn: a ≠ []) :
  (fromListFinBase a).getLast ((fromListFinBase_ne_nil_iff_ne_nil a).mpr hn)
    = ↑(a.getLast hn) := by
  induction a with
  | nil => exact absurd rfl hn
  | cons x xs ih =>
    match g : xs with
    | [] => simp only [List.getLast_singleton, fromListFinBase]
    | y::ys =>
      have : y::ys ≠ [] := List.cons_ne_nil y ys
      simp only [List.getLast_cons this, fromListFinBase_cons x (y::ys)]
      exact ih this

theorem fromListFinBase_getLast_ne_nil_iff {base : NatGtOne} (a : List (Fin base.val)) (hn: a ≠ []) :
  (fromListFinBase a).getLast ((fromListFinBase_ne_nil_iff_ne_nil a).mpr hn) ≠ 0 ↔
    a.getLast hn ≠ ⟨0, Nat.lt_trans (by decide) base.property⟩  := by
    constructor
    · intro h
      false_or_by_contra; rename _ => h1
      have h2 : (fromListFinBase a).getLast ((fromListFinBase_ne_nil_iff_ne_nil a).mpr hn) = 0 := by
        simp only [eq_iff_coe_eq] at h1
        rwa [fromListFinBase_getLast_eq_getLast_of a hn]
      contradiction
    · intro h
      false_or_by_contra; rename _ => h1
      have h2 : a.getLast hn = ⟨0, Nat.lt_trans (by decide) base.property⟩  := by
        simp only [eq_iff_coe_eq, ← fromListFinBase_getLast_eq_getLast_of a hn]
        assumption
      contradiction

theorem allDigitsLtBase_fromListFinBase {base : Nat} (a : List (Fin base)) :
  allDigitsLtBase (fromListFinBase a) base := by
  induction a with
  | nil => unfold fromListFinBase; simp only [allDigitsLtBase_nil]
  | cons x xs ih =>
    have hx : x < base := Fin.isLt x
    exact allDigitsLtBase_cons_iff.mpr (And.intro hx ih)

theorem fromListFinBase_toListFinBase_cancel {base : Nat} (a : List Nat) (h : allDigitsLtBase a base) :
  fromListFinBase (toListFinBase a h) = a := by
  induction a with
  | nil => simp only [toListFinBase, fromListFinBase]
  | cons x xs ih =>
    simp only [toListFinBase, fromListFinBase, ih]

theorem toListFinBase_fromListFinBase_cancel {base : Nat} (a : List (Fin base)) :
  toListFinBase (fromListFinBase a) (allDigitsLtBase_fromListFinBase a) = a := by
  induction a with
  | nil => simp only [toListFinBase, fromListFinBase]
  | cons x xs ih =>
    simp only [toListFinBase, fromListFinBase, ih]

end ListFinBase

end NumeralAux
