/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.EquivIsZero

namespace NumeralAux

section NoTrailingZero

/-
a list of numbers without trailing zeros is the shortest and thus simplest
representative of equivalent lists (with respect to `equivAux`)
-/
def noTrailingZero (a : List Nat) : Prop := (h : a ≠ []) → a.getLast h ≠ 0

def decNoTrailingZero (a : List Nat) : Decidable (noTrailingZero a) :=
  if g1 : a = [] then
    have : noTrailingZero a := by
      rw [noTrailingZero.eq_def]
      intro _
      contradiction
    isTrue this
  else
    if g2 : a.getLast g1 = 0 then
      have : ¬ noTrailingZero a := by
        rw [noTrailingZero.eq_def]
        intro h
        exact absurd g2 (h g1)
      isFalse this
    else
      have : noTrailingZero a := by
        rw [noTrailingZero.eq_def]
        intro _
        exact g2
      isTrue this

instance instNoTrailingZero (a : List Nat) : Decidable (noTrailingZero a) := decNoTrailingZero a

/-
the empty list has no trailing zeros
-/
theorem noTrailingZero_nil : noTrailingZero [] := by
  rw [noTrailingZero.eq_def]
  intro hnn
  contradiction

/-
a singleton has trailing zeros iff the number in the list is `0`
-/
theorem noTrailingZero_singleton_iff_ne_zero {n : Nat} : noTrailingZero [n] ↔ n ≠ 0 := by
  rw [noTrailingZero.eq_def]
  constructor
  · intro h
    have : [n] ≠ [] := List.cons_ne_nil n []
    have : [n].getLast this ≠ 0 := h this
    rwa [List.getLast_singleton] at this
  · intro h _
    rwa [List.getLast_singleton]

theorem noTrailingZero_tail_and_of {x : Nat} {xs : List Nat}
  (h : noTrailingZero (x::xs)) : noTrailingZero xs ∧ (xs = [] → x ≠ 0) := by
  simp only [noTrailingZero] at h ⊢
  have h1 : x :: xs ≠ [] := List.cons_ne_nil x xs
  have h2 : (x :: xs).getLast h1 ≠ 0 := h h1
  if g : xs = [] then
    have h3 : [x].getLast (List.cons_ne_nil x []) ≠ 0 := by
      simp only [g] at h2
      exact h2
    have h4 : [x].getLast (List.cons_ne_nil x []) = x := List.getLast_singleton (List.cons_ne_nil x [])
    have h5 : x ≠ 0 := by rwa [← h4] at h3
    exact And.intro (fun t : xs ≠ [] => absurd g t) (fun _ : xs = [] => h5)
  else
    rw [List.getLast_cons g] at h2
    exact And.intro (fun _ : xs ≠ [] => h2) (fun t : xs = [] => absurd t g)

theorem noTrailingZero_cons_of {x : Nat} {xs : List Nat}
  (h : noTrailingZero xs ∧ (xs = [] → x ≠ 0)) : noTrailingZero (x::xs) := by
  simp only [noTrailingZero] at h ⊢
  intro _
  if g : xs = [] then
    simp only [g, List.getLast_singleton (List.cons_ne_nil x [])]
    exact h.right g
  else
    rw [List.getLast_cons g]
    exact h.left g

theorem noTrailingZero_cons_iff_noTrailingZero_and {x : Nat} {xs : List Nat} :
  noTrailingZero (x::xs) ↔ noTrailingZero xs ∧ (xs = [] → x ≠ 0) := by
  constructor
  · intro h
    exact noTrailingZero_tail_and_of h
  · intro h
    exact noTrailingZero_cons_of h

end NoTrailingZero

section NoTrailingZero_EquivAux

theorem eq_nil_of_noTrailingZero_of_equivAux {a : List Nat}
  (hantz : noTrailingZero a) (hea: equivAux a []) : a = [] := by
  match a with
  | [] => rfl
  | x::xs =>
    have : (x::xs).all (· = 0) := all_eq_zero_of_equivAux_nil hea
    have h : (x::xs).getLast (List.cons_ne_nil x xs) = 0 := by
      rw [← beq_iff_eq]
      exact List.getLast_true_of_all_true_of_ne_nil (x::xs) (· == 0) this (List.cons_ne_nil x xs)
    have h': (x::xs).getLast (List.cons_ne_nil x xs) ≠ 0 := by
      unfold noTrailingZero at hantz
      exact hantz (List.cons_ne_nil x xs)
    exact absurd h h'

theorem eq_of_noTrailingZero_of_equivAux {a b : List Nat}
  (hantz : noTrailingZero a) (hbntz : noTrailingZero b) (habe: equivAux a b) : a = b := by
  induction a generalizing b with
  | nil =>
    have : equivAux b [] := equivAux_symm habe
    exact Eq.symm (eq_nil_of_noTrailingZero_of_equivAux hbntz this)
  | cons x xs ih =>
    match b with
    | [] => exact eq_nil_of_noTrailingZero_of_equivAux hantz habe
    | y::ys =>
      have hxs : noTrailingZero xs := (noTrailingZero_tail_and_of hantz).left
      have hys : noTrailingZero ys := (noTrailingZero_tail_and_of hbntz).left
      have heq : x = y ∧ equivAux xs ys := by
        simp only [equivAux] at habe
        exact habe
      have hes : xs = ys := ih hxs hys heq.right
      have he : x = y := heq.left
      exact List.cons_eq_cons.mpr (And.intro he hes)

theorem eq_iff_equivAux_of_noTrailingZero {a b : List Nat}
  (hantz : noTrailingZero a) (hbntz : noTrailingZero b) :
  a = b ↔ equivAux a b := by
  constructor
  · intro h
    rw [← h]
    exact equivAux_refl
  · intro h
    exact eq_of_noTrailingZero_of_equivAux hantz hbntz h

end NoTrailingZero_EquivAux

section NoTrailingZero_IsZeroAux

theorem isZeroAux_iff_eq_nil_of_noTrailingZero {a : List Nat} (hantz : noTrailingZero a) :
  isZeroAux a ↔ a = [] := by
  constructor
  · intro h
    induction a with
    | nil => rfl
    | cons x xs ih =>
      rw [noTrailingZero_cons_iff_noTrailingZero_and] at hantz
      rw [isZeroAux_cons_iff_eq_zero_and_isZeroAux] at h
      exact absurd h.left (hantz.right (ih hantz.left h.right))
  · intro h
    rw [h]
    exact isZeroAux_nil

end NoTrailingZero_IsZeroAux

end NumeralAux
