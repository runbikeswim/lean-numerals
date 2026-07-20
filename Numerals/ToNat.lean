/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Extra
import Numerals.Basic

section toNat

namespace TZNumeral

def toNat {base : NatGtOne} (n : TZNumeral base) : Nat :=
  helper base n.toListNat 1 0 where
  helper (base : NatGtOne) (a : List Nat) (factor acc : Nat) : Nat  :=
    match a with
    | [] => acc
    | x::xs => helper base xs (factor * base.val) (x * factor + acc)

theorem toNat_helper_nil_eq {base : NatGtOne} {factor acc : Nat} :
  @toNat.helper base [] factor acc = acc := rfl

theorem toNat_helper_eq {base : NatGtOne} {a : List Nat} {factor acc : Nat} :
  toNat.helper base a factor acc = acc + factor * (toNat.helper base a 1 0) := by
  induction a generalizing factor acc with
  | nil => simp_all only [toNat_helper_nil_eq, Nat.mul_zero, Nat.add_zero]
  | cons head tail ih =>
    unfold toNat.helper
    simp only [Nat.one_mul, Nat.mul_one, Nat.add_zero]
    rw [ih, Nat.add_comm (head * factor) acc]
    rw (occs := .pos [2]) [ih]
    rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm]

theorem toNat_zero_eq_zero {base : NatGtOne} : @toNat base zero = 0 := rfl

theorem toNat_helper_cons_eq {base : NatGtOne} {x : Nat} {xs : List Nat}  :
  toNat.helper base (x::xs) 1 0 = x + base.val * (toNat.helper base xs 1 0) := by
  simp only [toNat.helper, Nat.one_mul, Nat.add_zero, Nat.mul_one]
  rw [toNat_helper_eq]

theorem toNat_cons_eq {base : NatGtOne} {x : base.Fin} {xs : TZNumeral base}  :
  toNat (cons x xs) = x + base.val * (toNat xs) := by
  simp only [toNat, cons, toListNat, List.toListNatAux, List.map_cons, toNat_helper_cons_eq]
  rfl

end TZNumeral

end toNat
