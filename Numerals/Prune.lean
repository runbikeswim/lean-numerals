/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.AllDigitsBase
import Numerals.NoTrailingZero

namespace NumeralAux

section Prune

def prune (a : List Nat) (n base : Nat) (hb : 1 < base) : List Nat :=
  match a, n with
  | [], 0 => []
  | [], k + 1 =>
    -- for asserting termination
    have h : 0 < (k + 1) := Nat.zero_lt_succ k
    have : (k + 1) / base < k + 1 := Nat.div_lt_self h hb
    ((k + 1) % base)::(prune [] ((k + 1) / base) base hb)
  | x::xs, n => ((x + n) % base)::(prune xs ((x + n) / base) base hb)
  termination_by (a.length, n)

theorem prune_nil_eq_nil {base : Nat} (hb : 1 < base) :
  prune [] 0 base hb = [] := by
  rw [prune.eq_def]

theorem prune_eq_nil_iff_eq_nil_and_eq_zero {a : List Nat} {n base : Nat}  (hb : 1 < base) :
  prune a n base hb = [] ↔ a = [] ∧ n = 0 := by
  constructor
  · intro h
    match a, n with
    | [], 0 => exact And.intro rfl rfl
    | [], k + 1 | x::xs, n => simp only [prune, List.cons_ne_nil] at h
  · intro h
    simp only [h.left, h.right, prune_nil_eq_nil]

theorem prune_nil_eq_cons_of_pos {n base : Nat} (hn : 0 < n) (hb : 1 < base) :
  prune [] n base hb = (n % base)::(prune [] (n / base) base hb) := by
  match n with | 0 => contradiction | k + 1 => rw [prune.eq_def]

end Prune

section AllDigitsLtBase_Prune

theorem allDigitsLtBase_prune {a : List Nat} {n base : Nat} {hb : 1 < base} :
  allDigitsLtBase (prune a n base hb) base := by
  induction a generalizing n with
  | nil =>
    induction n using Nat.strongRecOn with
    | _ l ihl =>
      match gl : l with
      | 0 =>
        rw [prune.eq_def]
        simp only [allDigitsLtBase_nil]
      | k + 1 =>
        rw [prune.eq_def]
        simp only [allDigitsLtBase_cons_iff]
        have h1 : (k + 1) / base < (k + 1) := Nat.div_lt_self (Nat.succ_pos k) hb
        exact And.intro (Nat.mod_lt (k + 1) (Nat.lt_trans (by decide) hb)) (ihl ((k + 1) / base) h1)
  | cons x xs iha =>
    rw [prune.eq_def]
    simp only [allDigitsLtBase_cons_iff]
    exact And.intro (Nat.mod_lt (x + n) (Nat.lt_trans (by decide) hb)) iha

end AllDigitsLtBase_Prune

section NoTrailingZero_Prune

theorem noTrailingZero_prune_nil {n base : Nat} {hb : 1 < base} : noTrailingZero (prune [] n base hb) := by
  induction n using Nat.strongRecOn with
  | _ l ihl =>
    match gl : l with
      | 0 => rw [prune.eq_def]; simp only [noTrailingZero_nil]
      | k + 1 =>
        simp only [prune]
        have h1 : (k + 1) / base < k + 1  := Nat.div_lt_self (Nat.succ_pos k) hb
        if g : (k + 1) / base = 0 then
          have h2 : prune [] ((k + 1) / base) base hb = [] := (prune_eq_nil_iff_eq_nil_and_eq_zero hb).mpr (And.intro rfl g)
          have h3 : (k + 1) % base ≠ 0 := Nat.mod_ne_zero_of_one_lt_of_div_zero_of_ne hb g (Nat.succ_ne_zero k)
          have h4 : noTrailingZero (prune [] ((k + 1) / base) base hb)
                      ∧ (prune [] ((k + 1) / base) base hb = [] → (k + 1) % base ≠ 0) :=
            And.intro (ihl ((k + 1) / base) h1) (fun _ : prune [] ((k + 1) / base) base hb = [] => h3)
          exact noTrailingZero_cons_of h4
        else
          have h2 : ¬(([] : List Nat) = [] ∧ (k + 1) / base = 0) := by
            intro h
            exact absurd h.right g
          have h3 : prune [] ((k + 1) / base) base hb ≠ [] :=
            Classical.imp_iff_not_imp_not.mp (prune_eq_nil_iff_eq_nil_and_eq_zero hb).mp h2
          have h4 : noTrailingZero (prune [] ((k + 1) / base) base hb)
                      ∧ (prune [] ((k + 1) / base) base hb = [] → (k + 1) % base ≠ 0) :=
            And.intro (ihl ((k + 1) / base) h1) (fun t : prune [] ((k + 1) / base) base hb = [] => absurd t h3)
          exact noTrailingZero_cons_of h4

theorem noTrailingZero_prune_of_noTrailingZero {a : List Nat} {n base : Nat} {hb : 1 < base} (hntz : noTrailingZero a) :
  noTrailingZero (prune a n base hb) := by
  induction a generalizing n with
  | nil => exact noTrailingZero_prune_nil
  | cons x xs iha =>
    simp only [prune]
    have h1 : noTrailingZero xs ∧ (xs = [] → x ≠ 0) := noTrailingZero_cons_iff_noTrailingZero_and.mp hntz
    have h2 : noTrailingZero (prune xs ((x + n) / base) base hb) := iha h1.left
    simp only [noTrailingZero_cons_iff_noTrailingZero_and, h2, true_and]
    intro h
    simp only [prune_eq_nil_iff_eq_nil_and_eq_zero] at h
    have h3 : x ≠ 0 := h1.right h.left
    have h4 : 0 < x := Nat.pos_of_ne_zero h3
    have h5 : 0 < x + n := Nat.add_pos_left h4 n
    have h6 : x + n ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr h5
    exact Nat.mod_ne_zero_of_one_lt_of_div_zero_of_ne hb h.right h6

end NoTrailingZero_Prune

section ToNatAux_Prune

theorem toNatAux_prune_eq_add_toNatAux {a : List Nat} {n base : Nat} (hb : 1 < base) :
  toNatAux (prune a n base hb) base = n + toNatAux a base := by
  induction a generalizing n with
  | nil =>
    induction n using Nat.strongRecOn with
    | _ l ihl =>
      match gl : l with
      | 0 =>
        rw [prune.eq_def, toNatAux.eq_def, toNatAux.helper.eq_def]
        simp_all only [Nat.not_lt_zero, false_implies, implies_true, Nat.add_zero]
      | k + 1 =>
        have : (k + 1) / base < k + 1 := Nat.div_lt_self (Nat.succ_pos k) hb
        rw [prune.eq_def, toNatAux_cons_eq, ihl ((k + 1) / base) this, Nat.mul_add, ← Nat.add_assoc]
        rw [Nat.mod_add_div (k + 1) base, toNatAux_nil_eq, Nat.mul_zero]
  | cons x xs iha =>
    rw [prune.eq_def, toNatAux_cons_eq, iha, Nat.mul_add, ← Nat.add_assoc]
    rw [Nat.mod_add_div, toNatAux_cons_eq, ← Nat.add_assoc]
    rw (occs := [2]) [Nat.add_comm]

end ToNatAux_Prune

end NumeralAux
