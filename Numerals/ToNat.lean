/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

namespace NumeralAux

section ToNatAux

/-
Returns value of the numeral represented by the lists of digits (little-endian) with respect to `basis`.

Examples:
```
#eval toNatAux [0, 1, 0] 2 -- 2
#eval toNatAux [0, 11, 7] 10 -- 810
```
-/
def toNatAux (a : List Nat) (base : Nat) : Nat :=
  (helper a base 1 0).snd where
    helper (a : List Nat) (base factor acc : Nat) : Nat × Nat :=
      match a with
      | [] => (factor, acc)
      | x::xs => helper xs base (factor * base) (x * factor + acc)

theorem toNatAux_helper_nil_eq {base factor acc : Nat} : toNatAux.helper [] base factor acc = (factor, acc) := by
  unfold toNatAux.helper
  rfl

theorem toNatAux_helper_snd_eq {a : List Nat} {base factor acc : Nat} :
  (toNatAux.helper a base factor acc).snd = acc + factor * (toNatAux.helper a base 1 0).snd := by
  induction a generalizing factor acc with
  | nil => simp_all only [toNatAux_helper_nil_eq, Nat.mul_zero, Nat.add_zero]
  | cons head tail ih =>
    unfold toNatAux.helper
    simp only [Nat.one_mul, Nat.mul_one, Nat.add_zero]
    rw [ih, Nat.add_comm (head * factor) acc]
    rw (occs := .pos [2]) [ih]
    rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm]

theorem toNatAux_nil_eq {base : Nat} : toNatAux [] base = 0 := by
  unfold toNatAux
  rfl

theorem toNatAux_cons_eq {xs : List Nat} {x base : Nat} :
  toNatAux (x::xs) base = x + base * (toNatAux xs base) := by
  rw [toNatAux.eq_def, toNatAux.helper.eq_def]
  simp only
  rw [toNatAux.eq_def, toNatAux_helper_snd_eq, Nat.mul_one, Nat.one_mul, Nat.add_zero]

end ToNatAux

end NumeralAux
