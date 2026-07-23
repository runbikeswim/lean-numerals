/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic
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

theorem zero_le {base : NatGtOne} {n : TZNumeral base} : 0 ≤ n := by
  simp only [OfNat.ofNat, LE.le, le, Zero.zero]
  exact le_helper_nil

theorem le_helper_refl {base : NatGtOne} {a : List base.Fin} : le.helper base a a := by
  match a with
  | [] => simp only [le.helper]
  | x::xs =>
    simp only [le.helper, equiv_helper_refl, reduceIte, Fin.le_refl]

theorem le_refl {base : NatGtOne} {a : TZNumeral base} : a ≤ a := by
  simp only [LE.le, le]
  exact le_helper_refl

theorem le_helper_cons_iff {base : NatGtOne} {x y : base.Fin} {xs ys : List base.Fin} :
  le.helper base (x::xs) (y::ys) ↔ if equiv.helper base xs ys then x ≤ y else le.helper base xs ys := by
  rfl

end LessThanOrEqualTo

section LessThan

end LessThan
