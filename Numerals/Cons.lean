/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.EquivIsZero
import Numerals.AllDigitsBase
import Numerals.NoTrailingZero

namespace NumeralAux

section ConsAux

def consAux (n : Nat) (a : List Nat) : List Nat :=
  match n, a with
  | 0, [] => []
  | k + 1, [] => [k + 1]
  | n, x::xs => n::x::xs

theorem consAux_zero_nil_eq : consAux 0 [] = [] := by
  simp only [consAux]

theorem consAux_succ_nil_eq {n : Nat} : consAux (n + 1) [] = [n + 1] := by
  simp only [consAux]

theorem consAux_cons_eq {n x : Nat} {xs : List Nat} : consAux n (x::xs) = n::x::xs := by
  simp only [consAux]

theorem equivAux_consAux_cons {n : Nat} {a : List Nat} :
  equivAux (consAux n a) (n::a) := by
  match gn : n, ga : a with
  | 0, [] => simp only [consAux_zero_nil_eq, equivAux, true_and]
  | k + 1, [] => simp only [consAux_succ_nil_eq, equivAux, true_and]
  | n, x::xs => simp only [consAux, equivAux_refl]

theorem equivAux_consAux_consAux_nil_of_equivAux_nil {n : Nat} {a : List Nat} (h : equivAux a []) :
  equivAux (consAux n a) (consAux n []) := by
  match n, a with
  | _, [] => exact equivAux_refl
  | 0, x::xs =>
    simp only [consAux_cons_eq, consAux_zero_nil_eq]
    exact equivAux_cons_nil_of_equivAux_nil h
  | k + 1, x::xs  =>
    simp only [consAux_cons_eq, consAux_succ_nil_eq]
    exact equivAux_cons_iff_eq_and_equivAux.mpr (And.intro rfl h)

theorem equivAux_consAux_consAux_of_equivAux {n : Nat} {a b : List Nat} (h : equivAux a b) :
  equivAux (consAux n a) (consAux n b) := by
  match n, a, b with
  | _, _, [] => exact equivAux_consAux_consAux_nil_of_equivAux_nil h
  | _, [], _ =>
    rw [equivAux_iff_equivAux] at ⊢ h
    exact equivAux_consAux_consAux_nil_of_equivAux_nil h
  | _, x::xs, y::ys =>
    simp only [equivAux_cons_iff_eq_and_equivAux] at h
    simp only [consAux, equivAux_cons_iff_eq_and_equivAux, true_and]
    assumption

theorem equivAux_consAux_singleton_of_equivAux_nil {n : Nat} {a : List Nat} (h : equivAux a []) :
  equivAux (consAux n a) [n] := by
  match n, a with
  | 0, [] =>
    simp only [consAux_zero_nil_eq]
    exact equivAux_iff_equivAux.mp (equivAux_cons_nil_of_equivAux_nil h)
  | k + 1, [] =>
    simp only [consAux_succ_nil_eq]
    exact equivAux_refl
  | _, x::xs =>
    simp only [consAux_cons_eq]
    exact equivAux_cons_iff_eq_and_equivAux.mpr (And.intro rfl h)

theorem equivAux_consAux_cons_of_equivAux {n : Nat} {a b : List Nat} (h : equivAux a b) :
  equivAux (consAux n a) (n::b) := by
  match n, a, b with
  | _, _, [] => exact equivAux_consAux_singleton_of_equivAux_nil h
  | 0, [], _ =>
    simp only [consAux_zero_nil_eq]
    exact equivAux_iff_equivAux.mp (equivAux_cons_nil_of_equivAux_nil (equivAux_iff_equivAux.mp h))
  | k + 1, [], _ =>
    simp only [consAux_succ_nil_eq]
    exact equivAux_cons_iff_eq_and_equivAux.mpr (And.intro rfl h)
  | _, x::xs, y::ys =>
    simp only [consAux_cons_eq]
    exact equivAux_cons_iff_eq_and_equivAux.mpr (And.intro rfl h)

theorem allDigitsLtBase_consAux_of {n base: Nat} {a : List Nat}
  (hn : n < base) (ha : allDigitsLtBase a base) :
  allDigitsLtBase (consAux n a) base := by
  unfold consAux
  match gn: n, ga: a with
  | 0, [] => simp only; exact allDigitsLtBase_nil
  | k + 1, [] => simp only; exact allDigitsLtBase_singleton hn
  | n, x::xs => simp only; exact allDigitsLtBase_cons_iff.mpr (And.intro hn ha)

theorem noTrailingZero_consAux_of {n : Nat} {a : List Nat} (ha : noTrailingZero a) :
  noTrailingZero (consAux n a) := by
  unfold consAux
  match gn: n, ga: a with
  | 0, [] => simp only; exact noTrailingZero_nil
  | k + 1, [] => simp only; exact noTrailingZero_singleton_iff_ne_zero.mpr (Nat.succ_ne_zero k)
  | n, x::xs =>
    simp only
    have : x::xs = [] → n ≠ 0 := fun t : x::xs = [] => absurd t (List.cons_ne_nil x xs)
    exact noTrailingZero_cons_of (And.intro ha this)

end ConsAux

end NumeralAux
