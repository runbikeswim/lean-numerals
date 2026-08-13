/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Extra
import Numerals.Basic
import Numerals.ToNat

namespace TZNumeral

section Prune

def prune {base : NatGtOne} (a : List Nat) (n : Nat) : TZNumeral base where
  digits := helper base (a : List Nat) (n : Nat) where
  helper (base : NatGtOne) (a : List Nat) (n : Nat) : List base.Fin :=
    match a, n with
    | [], 0 => []
    | [], k + 1 =>
      -- for asserting termination
      have h : 0 < (k + 1) := Nat.zero_lt_succ k
      have : (k + 1) / base.val < k + 1 := Nat.div_lt_self h base.property
      FinBase.ofNat (k + 1) :: helper base [] ((k + 1) / base.val)
    | x::xs, n => FinBase.ofNat (x + n) :: helper base xs ((x + n) / base.val)
    termination_by (a.length, n)

theorem prune_helper_nil_zero_eq_nil {base : NatGtOne} :
  prune.helper base [] 0 = ([] : List base.Fin) := by
  simp only [prune.helper]

theorem prune_nil_zero_eq_zero {base : NatGtOne} : prune [] 0 = @zero base := by
  simp only [prune, prune_helper_nil_zero_eq_nil]

theorem prune_helper_eq_nil_iff_eq_nil_and_eq_zero {base : NatGtOne} {a : List Nat} {n : Nat} :
  prune.helper base a n = ([] : List base.Fin) ↔ a = [] ∧ n = 0 := by
  constructor
  · intro h
    match a, n with
    | [], 0 => exact And.intro rfl rfl
    | [], k + 1 | x::xs, n => simp only [prune.helper, List.cons_ne_nil] at h
  · intro h
    simp only [h.left, h.right, prune_helper_nil_zero_eq_nil]

theorem prune_helper_cons_eq {base : NatGtOne} {x n : Nat} {xs : List Nat} :
  prune.helper base (x :: xs) n = FinBase.ofNat (x + n) :: prune.helper base xs ((x + n) / base.val) := by
  simp only [prune.helper]

theorem prune_eq_zero_iff_eq_nil_and_eq_zero {base : NatGtOne} {a : List Nat} {n : Nat} :
  prune a n = @zero base ↔ a = [] ∧ n = 0 := by
  simp only [prune, zero, eq_iff_digits_eq]
  exact prune_helper_eq_nil_iff_eq_nil_and_eq_zero

theorem prune_helper_nil_eq_cons_of_pos {base : NatGtOne} {n : Nat} (hn : 0 < n)  :
  @prune.helper base [] n = FinBase.ofNat n :: (prune.helper base [] (n / base.val) ) := by
  match n with
  | 0 => contradiction
  | k + 1 => simp only [prune.helper]

theorem prune_nil_eq_cons_of_pos {base : NatGtOne} {n : Nat} (hn : 0 < n) :
  @prune base [] n = cons (FinBase.ofNat n) (prune [] (n / base.val) ) := by
  simp only [prune, cons, eq_iff_digits_eq]
  exact prune_helper_nil_eq_cons_of_pos hn

theorem prune_helper_toListAux_eq {base : NatGtOne} {a : List base.Fin} :
  prune.helper base a.toListNatAux 0 = a := by
  induction a with
  | nil => simp only [toListNatAux_nil_eq_nil, prune_helper_nil_zero_eq_nil]
  | cons x xs ih =>
    have h1 : ↑x / base.val = 0 := Nat.div_eq_zero_iff.mpr (.inr (Fin.is_lt x))
    have h2 : FinBase.ofNat ↑x = x := Fin.ofNat_val_eq_self x
    simp only [cons_toListNatAux_eq_coe_cons_toList, prune_helper_cons_eq, Nat.add_zero, h1, ih, h2]

theorem prune_toListNat_zero_cancel {base : NatGtOne} {a : TZNumeral base} : prune a.toListNat 0 = a := by
  simp only [prune, prune_helper_toListAux_eq]

theorem prune_helper_of_lt {base : NatGtOne} {n : Nat} (hn : n < base.val) :
  prune.helper base [] n = if n = 0 then [] else [⟨n, hn⟩] := by
  match n with
  | 0 => simp only [prune.helper, reduceIte]
  | k + 1 =>
    simp only [prune.helper, Nat.div_eq_zero_iff.mpr (.inr hn), Nat.succ_ne_zero, reduceIte]
    simp only [FinBase.ofNat, (Nat.mod_eq_iff_lt base.val_ne_zero).mpr hn]

theorem prune_of_lt {base : NatGtOne} {n : Nat} (hn : n < base.val) :
  prune [] n = if n = 0 then 0 else ⟨[⟨n, hn⟩]⟩ := by
  simp only [prune, eq_iff_digits_eq, ← zero_eq_zero, zero, prune_helper_of_lt hn]
  match n with
  | 0 => simp only [reduceIte]
  | k + 1 => simp only [Nat.succ_ne_zero, reduceIte]

end Prune

section NoTrailingZero_Prune

theorem noTrailingZero_helper_prune_helper_nil {base : NatGtOne} {n : Nat} :
  noTrailingZero.helper base (prune.helper base [] n) := by
  induction n using Nat.strongRecOn with
  | _ l ihl =>
    match gl : l with
    | 0 => simp only [prune_helper_nil_zero_eq_nil]; exact noTrailingZero_helper_nil
    | k + 1 =>
      simp only [prune.helper]
      have h1 : (k + 1) / base.val < k + 1  := Nat.div_lt_self (Nat.succ_pos k) base.property
      if g : (k + 1) / base.val = 0 then
        have h2 : prune.helper base [] ((k + 1) / base.val) = [] :=
          (@prune_helper_eq_nil_iff_eq_nil_and_eq_zero base).mpr (And.intro rfl g)
        have h3 : FinBase.ofNat (k + 1) ≠ base.zero :=
          FinBase.ofNat_ne_zero_of_div_zero_of_ne g (Nat.succ_ne_zero k)
        have h4 : noTrailingZero.helper base (prune.helper base [] ((k + 1) / base.val))
                    ∧ (@prune.helper base [] ((k + 1) / base.val)  = [] → FinBase.ofNat (k + 1) ≠ base.zero) :=
          And.intro (ihl ((k + 1) / base.val) h1) (fun _ : prune.helper base [] ((k + 1) / base.val) = [] => h3)
        exact noTrailingZero_helper_cons_of h4
      else
        have h2 : ¬(([] : List Nat) = [] ∧ (k + 1) / base.val = 0) := by
          intro h
          exact absurd h.right g
        have h3 : @prune.helper base [] ((k + 1) / base.val) ≠ [] :=
          Classical.imp_iff_not_imp_not.mp prune_helper_eq_nil_iff_eq_nil_and_eq_zero.mp h2
        have h4 : noTrailingZero.helper base (prune.helper base [] ((k + 1) / base.val) )
                    ∧ (prune.helper base [] ((k + 1) / base.val)  = [] → FinBase.ofNat (k + 1) ≠ base.zero) :=
          And.intro (ihl ((k + 1) / base.val) h1) (fun t : prune.helper base [] ((k + 1) / base.val) = [] => absurd t h3)
        exact noTrailingZero_helper_cons_of h4

theorem prune_nil_noTrailingZero {base : NatGtOne} {n : Nat} : (@prune base [] n).noTrailingZero := by
  unfold prune noTrailingZero
  exact noTrailingZero_helper_prune_helper_nil

end NoTrailingZero_Prune

section ToNat_Prune

theorem toNat_helper_prune_helper_nil_eq {base : NatGtOne} {n : Nat} :
  toNat.helper base (prune.helper base [] n) 1 0 = n := by
  induction n using Nat.strongRecOn with
  | _ l ih =>
    match gl : l with
    | 0 => simp only [prune_helper_nil_zero_eq_nil, toNat.helper]
    | k + 1 =>
      have : (k + 1) / base.val < k + 1 := Nat.div_lt_self (Nat.succ_pos k) base.property
      simp only [prune.helper, toNat_helper_cons_eq]
      simp only [ih ((k + 1) / base.val) this, FinBase.ofNat]
      rw [Nat.add_comm]
      exact Nat.div_add_mod (k + 1) base.val

theorem toNat_helper_prune_helper_eq_add_toNat_helper {base : NatGtOne} {a : List Nat} {n : Nat} :
  toNat.helper base (prune.helper base a n) 1 0 = n + (toNat.helper base (prune.helper base a 0) 1 0) := by
  induction a generalizing n with
  | nil => simp only [toNat_helper_prune_helper_nil_eq, Nat.add_zero]
  | cons x xs ih =>
    simp only [prune_helper_cons_eq, toNat_helper_cons_eq, FinBase.ofNat, Nat.add_zero]
    rw [@ih ((x + n) / base.val), @ih (x / base.val), Nat.mul_add, ← Nat.add_assoc, Nat.mul_add]
    rw (occs := .pos [2]) [← Nat.add_assoc]
    rw [Nat.mod_add_div (x + n) base.val, Nat.mod_add_div x base.val, ← Nat.add_assoc]
    rw (occs := .pos [2]) [Nat.add_comm]

theorem toNat_prune_eq_add_toNat_prune_zero {base : NatGtOne} {a : TZNumeral base} {n : Nat}  :
  @toNat base (prune a.toListNat n) = n + @toNat base (prune a.toListNat 0) := by
  simp only [prune, toNat, toListNat]
  exact toNat_helper_prune_helper_eq_add_toNat_helper

theorem toNat_prune_eq_add_toNat {base : NatGtOne} {a : TZNumeral base} {n : Nat}  :
  @toNat base (prune a.toListNat n) = n + a.toNat := by
  rw [toNat_prune_eq_add_toNat_prune_zero]
  simp only [prune_toListNat_zero_cancel]

theorem toNat_prune_nil_eq_add_toNat {base : NatGtOne} {n : Nat}  :
  @toNat base (prune [] n) = n := @toNat_prune_eq_add_toNat base zero n

end ToNat_Prune

end TZNumeral
