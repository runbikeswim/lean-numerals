/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic
import Numerals.Orders

namespace TZNumeral

def hSub {base : NatGtOne} (a b : TZNumeral base) : TZNumeral base where
  digits := if a ≤ b then [] else helper base a.digits b.digits base.zero where
  helper (base : NatGtOne) (a b : List base.Fin) (carry : base.Fin) : List base.Fin :=
    let rec checkForCarry (base : NatGtOne) (x y carry : base.Fin) (xs ys : List base.Fin) : List base.Fin :=
      if g : y.val + carry.val ≤ x.val  then
        -- assert that the value is not changed via the cast to `Fin base.val` which performs ... % base.val
        have : x.val - y.val - carry.val < base.val := by
          calc x.val - y.val - carry.val ≤ x.val - y.val := Nat.sub_le (x.val - y.val) carry.val
            _ ≤ x.val := Nat.sub_le x.val y.val
            _ < base.val := x.isLt
        -- for the head of the list, explicitly construct an element of `Fin base.val` instead of using the cast from `Nat` to `Fin base.val` which would provide the same result
        ⟨x.val - y.val - carry.val, this⟩::(helper base xs ys base.zero)
      else
        have : base.val + x.val - y.val - carry.val < base.val := by
          calc base.val + x.val - y.val - carry.val = base.val + x.val - (y.val + carry.val) := by simp [Nat.sub_add_eq (base.val + x.val) y.val carry.val]
            _ < base.val + x.val - x.val := Nat.sub_lt_sub_left (Nat.lt_add_of_pos_left base.val_pos) (Nat.lt_of_not_le g)
            _ = base.val := by simp only [Nat.add_sub_cancel]
        ⟨base.val + x.val - y.val - carry.val, this⟩::(helper base xs ys base.one)
    match a, b with
    | [], _ => []
    | x::xs, [] => checkForCarry base x base.zero carry xs []
    | x::xs, y::ys => checkForCarry base x y carry xs ys

def a : TZNumeral base10 := ⟨[0, 0, 1]⟩
def b : TZNumeral base10 := ⟨[8, 9]⟩

#eval hSub a b

instance {base : NatGtOne} : HSub (TZNumeral base) (TZNumeral base) (TZNumeral base) := ⟨hSub⟩
#synth HSub (TZNumeral base10) (TZNumeral base10) (TZNumeral base10)

#eval a - b

def a' : Numeral base10 := ⟨a, by decide⟩
def b' : Numeral base10 := ⟨b, by decide⟩

instance {base : NatGtOne} : HSub (Numeral base) (Numeral base) (TZNumeral base) := ⟨fun n ↦ fun m ↦ n.hSub m⟩
#synth HSub (Numeral base10) (Numeral base10) (TZNumeral base10)

instance {base : NatGtOne} : HSub (TZNumeral base) (Numeral base) (TZNumeral base) := ⟨fun n ↦ fun m ↦ n.hSub m⟩
#synth HSub (TZNumeral base10) (Numeral base10) (TZNumeral base10)

instance {base : NatGtOne} : HSub (Numeral base) (TZNumeral base) (TZNumeral base) := ⟨fun n ↦ fun m ↦ n.hSub m⟩
#synth HSub (Numeral base10) (TZNumeral base10) (TZNumeral base10)

#eval a' - b'
#eval a - b'
#eval a' - b

end TZNumeral
