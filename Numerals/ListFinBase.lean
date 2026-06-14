/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.AllDigitsBase

namespace NumeralAux

section ListFinBase

def toListFinBase {base : Nat} (a : List Nat) (h : allDigitsLtBase a base) : List (Fin base) :=
  match a with
  | [] => []
  | x::xs =>
    have : x < base := (allDigitsLtBase_cons_iff.mp h).left
    ⟨x,this⟩ :: toListFinBase xs (allDigitsLtBase_cons_iff.mp h).right

def fromListFinBase {base : Nat} (a : List (Fin base)) : List Nat :=
  match a with
  | [] => []
  | x::xs => ↑x :: fromListFinBase xs

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
