/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.ToNat
import Numerals.EquivIsZero
import Numerals.AllDigitsBase

namespace NumeralAux

section ToNatAux_Equiv

theorem toNatAux_eq_of_equivAux {a b : List Nat} {base : Nat} (h : equivAux a b) (hb : 1 < base) :
  toNatAux a base = toNatAux b base := by
  induction a generalizing b with
  | nil =>
    have : toNatAux b base = 0 ↔ isZeroAux b := toNatAux_eq_zero_iff_isZeroAux hb
    rw [isZeroAux.eq_def, eq_comm] at this
    simp only [toNatAux_nil_eq, this, h]
  | cons x xs ih =>
    match b with
    | [] =>
      have : toNatAux (x::xs) base = 0 ↔ isZeroAux (x::xs) := toNatAux_eq_zero_iff_isZeroAux hb
      rw [isZeroAux.eq_def,  equivAux_iff_equivAux] at this
      simp only [toNatAux_nil_eq, this, h]
    | y::ys =>
      simp only [equivAux] at h
      simp only [toNatAux_cons_eq, h.left, ih h.right]

theorem equivAux_of_toNatAux_eq {a b : List Nat} {base : Nat}
  (h : toNatAux a base = toNatAux b base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) (hb : 1 < base) :
  equivAux a b := by
  induction a generalizing b with
  | nil =>
    have : toNatAux b base = 0 ↔ isZeroAux b := toNatAux_eq_zero_iff_isZeroAux hb
    rw [isZeroAux.eq_def, eq_comm] at this
    rw [toNatAux_nil_eq] at h
    exact this.mp h
  | cons x xs ih =>
    match b with
    | [] =>
      have : toNatAux (x::xs) base = 0 ↔ isZeroAux (x::xs) := toNatAux_eq_zero_iff_isZeroAux hb
      rw [isZeroAux.eq_def,  equivAux_iff_equivAux] at this
      rw [toNatAux_nil_eq] at h
      exact this.mp h
    | y::ys =>
      have halt' : x < base ∧ allDigitsLtBase xs base := allDigitsLtBase_cons_iff.mp halt
      have hblt' : y < base ∧ allDigitsLtBase ys base := allDigitsLtBase_cons_iff.mp hblt
      simp only [toNatAux_cons_eq] at h
      simp only [equivAux]
      have : x = y ∧ toNatAux xs base = toNatAux ys base :=
        (Nat.add_mul_eq_iff_eq_and_eq_of halt'.left hblt'.left).mp h
      exact And.intro this.left (ih this.right halt'.right hblt'.right)

theorem toNatAux_eq_iff_equivAux {a b : List Nat} {base : Nat}
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) (hb : 1 < base) :
  toNatAux a base = toNatAux b base ↔ equivAux a b := by
  constructor
  · intro h
    exact equivAux_of_toNatAux_eq h halt hblt hb
  · intro h
    exact toNatAux_eq_of_equivAux h hb

example {a b : List Nat} {base : Nat} (ha : a = [11]) (hb : b = [1,1]) (hbase : base = 10) :
  toNatAux a base = toNatAux b base ∧ ¬ equivAux a b := by
  have : toNatAux a base = toNatAux b base := by rw [ha, hb, hbase]; decide
  match decEquivAux a b with
  | isFalse q => exact And.intro this q
  | isTrue q =>
    rw [ha, hb] at q
    simp only [equivAux, Nat.succ_ne_self, false_and, and_false] at q

end ToNatAux_Equiv

end NumeralAux
