/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic
import Numerals.Orders

namespace TZNumeral

def hSub {base : NatGtOne} (a b : TZNumeral base) : TZNumeral base where
  digits := if a ≤ b then [] else helper base a.digits b.digits 0 where
  helper (base : NatGtOne) (a b : List base.Fin) (n : Nat) : List base.Fin :=
    let rec checkForCarry (base : NatGtOne) (x y : base.Fin) (xs ys : List base.Fin) (n : Nat) : List base.Fin :=
      let n' := n % base.val
      if g : y.val + n' ≤ x.val then
        -- assert that the value is not changed via the cast to `Fin base.val` which performs ... % base.val
        have : x.val - y.val - n' < base.val := Nat.sub_sub_lt_of y.val n' x.isLt
        -- for the head of the list, explicitly construct an element of `Fin base.val` instead of using the cast from `Nat` to `Fin base.val` which would provide the same result
        ⟨x.val - y.val - n', this⟩ :: (helper base xs ys (n / base.val))
      else
        have : base.val + x.val - y.val - n' < base.val := Nat.add_sub_sub_lt_of_not_le base.val_pos g
        ⟨base.val + x.val - y.val - n', this⟩ :: (helper base xs ys (1 + n / base.val))
    match a, b with
    | [], _ => []
    | x::xs, [] => checkForCarry base x base.zero xs [] n
    | x::xs, y::ys => checkForCarry base x y xs ys n

instance {base : NatGtOne} : HSub (TZNumeral base) (TZNumeral base) (TZNumeral base) := ⟨hSub⟩
instance {base : NatGtOne} : HSub (Numeral base) (Numeral base) (TZNumeral base) := ⟨fun n ↦ fun m ↦ n.hSub m⟩
instance {base : NatGtOne} : HSub (TZNumeral base) (Numeral base) (TZNumeral base) := ⟨fun n ↦ fun m ↦ n.hSub m⟩
instance {base : NatGtOne} : HSub (Numeral base) (TZNumeral base) (TZNumeral base) := ⟨fun n ↦ fun m ↦ n.hSub m⟩

theorem hSub_helper_nil_eq {base : NatGtOne} {a : List base.Fin} : hSub.helper base a [] 0 = a := by
  induction a with
  | nil => rw [hSub.helper.eq_def]
  | cons x xs ih =>
    rw [hSub.helper.eq_def]
    simp only [hSub.helper.checkForCarry, NatGtOne.zero_coe_eq, Nat.zero_add, Nat.sub_zero]
    simp only [Nat.zero_mod, Nat.add_zero, Nat.zero_le, ↓reduceDIte, Nat.sub_zero, Fin.eta]
    simp only [Nat.zero_div, List.cons.injEq, true_and]
    exact ih

theorem zero_sub {base : NatGtOne} {a : TZNumeral base} : 0 - a = 0 := by
  simp only [HSub.hSub, hSub, zero_le, reduceIte]
  simp only [OfNat.ofNat, Zero.zero]

theorem sub_zero_of_zero_equiv {base : NatGtOne} {a : TZNumeral base} (h : 0 ≈ a) : a - 0 = 0 := by
  simp only [HSub.hSub, hSub, le_zero_iff_equiv_zero, h, reduceIte]
  simp only [OfNat.ofNat, Zero.zero]

theorem sub_zero_of_not_zero_equiv {base : NatGtOne} {a : TZNumeral base} (h : ¬ 0 ≈ a) : a - 0 = a := by
  simp only [HSub.hSub, hSub, le_zero_iff_equiv_zero, h, reduceIte, eq_iff_digits_eq]
  exact hSub_helper_nil_eq

theorem sub_zero_equiv {base : NatGtOne} {a : TZNumeral base} : a - 0 ≈ a := by
  if g : 0 ≈ a then
    simp only [sub_zero_of_zero_equiv g]
    exact g
  else
    simp only [sub_zero_of_not_zero_equiv g]
    exact equiv_refl

example {base : NatGtOne} : ∃ (a : TZNumeral base), a - 0 ≠ a := by
  let a : TZNumeral base := ⟨[base.zero]⟩
  have h1 : 0 ≈ a := by
    rw [equiv_zero_iff]
    simp only [a, List.all_eq_true, List.forall_mem_singleton, beq_iff_eq]
    simp only [NatGtOne.zero, OfNat.ofNat, FinBase.ofNat, Nat.zero_mod]
  have h2 : 0 ≠ a := by
    intro h
    simp only [OfNat.ofNat, Zero.zero, zero, a, eq_iff_digits_eq] at h
    exact absurd (Eq.symm h) (List.cons_ne_nil _ [])
  have h3 : a - 0 ≠ a := by rw [sub_zero_of_zero_equiv h1]; exact h2
  exact Exists.intro a h3

theorem sub_eq_zero_of_le {base : NatGtOne} {a b : TZNumeral base} (h: a ≤ b) : a - b = 0 := by
  simp only [HSub.hSub, hSub, h, reduceIte]
  simp only [OfNat.ofNat, Zero.zero]

theorem sub_eq_zero_of_equiv {base : NatGtOne} {a b : TZNumeral base} (h: a ≈ b) : a - b = 0 :=
  sub_eq_zero_of_le (le_of_equiv h)

theorem sub_eq_zero_of_eq {base : NatGtOne} {a b : TZNumeral base} (h: a = b) : a - b = 0 := by
  rw [←h]
  exact sub_eq_zero_of_equiv equiv_refl

theorem hSub_helper_cons_nil_eq {base : NatGtOne} {x : base.Fin} {xs : List base.Fin} {n : Nat}:
  hSub.helper base (x::xs) [] n =
    if g : n % base.val ≤ x.val then
      have : x.val - n % base.val < base.val := Nat.sub_sub_lt_of 0 (n % base.val) x.isLt
      ⟨x.val - n % base.val, this⟩ :: hSub.helper base xs [] (n / base.val)
    else
      have : base.val + x.val - n % base.val < base.val := Nat.add_sub_lt_of_not_le base.val_pos g
      ⟨base.val + x.val - n % base.val, this⟩ :: hSub.helper base xs [] (1 + n / base.val) := by
  simp only [hSub.helper, hSub.helper.checkForCarry, NatGtOne.zero]
  simp only [Nat.zero_add, Nat.sub_zero]

theorem hSub_helper_succ_cons_succ_cons_eq {base : NatGtOne} {x y : base.Fin} {xs ys : List base.Fin} {n : Nat}
  (hx : x.val + 1 < base.val) (hy : y.val + 1 < base.val) :
  hSub.helper base (⟨x.val + 1, hx⟩ :: xs) (⟨y.val + 1, hy⟩ :: ys) n
    = hSub.helper base (x :: xs) (y :: ys) n := by
  unfold hSub.helper hSub.helper.checkForCarry
  if g : y.val + n % base.val ≤ x.val  then
    have : y.val + 1 + n % base.val ≤ x.val + 1 := by
      rw [Nat.add_assoc]
      rw (occs := .pos [2]) [Nat.add_comm]
      rw [← Nat.add_assoc]
      simp only [Nat.add_le_add_right g 1]
    simp only [g, this, reduceDIte, Nat.add_sub_add_right x.val 1 y.val]
  else
    have h1 : x.val < y.val + n % base.val := Nat.lt_of_not_le g
    have h2 : x.val + 1 < y.val + 1 + n % base.val := by
      rw [Nat.add_assoc]
      rw (occs := .pos [3]) [Nat.add_comm]
      rw [← Nat.add_assoc]
      simp only [Nat.add_lt_add_right h1 1]
    have h3 : ¬ y.val + 1 + n % base.val ≤ x.val + 1 := Nat.not_le_of_lt h2
    simp only [g, h3, reduceDIte, ← Nat.add_assoc, Nat.add_sub_add_right (base.val + x.val) 1 y.val]

theorem hSub_helper_checkForCarry_succ_eq_of_lt_lt {base : NatGtOne} {x y : base.Fin}
  {xs ys : List base.Fin} {n : Nat} (hy : y.val + 1 < base.val) (hn : n + 1 < base.val) :
  hSub.helper.checkForCarry base x ⟨Fin.toNat y + 1, hy⟩ xs ys n = hSub.helper.checkForCarry base x y xs ys (n + 1) := by
  have h1 : n < base.val := Nat.lt_of_succ_lt hn
  have h2 : (n + 1) % base.val = n + 1 := Nat.mod_eq_of_lt hn
  have h3 : n % base.val = n := Nat.mod_eq_of_lt h1
  have h4 : ↑y + 1 + n = ↑y + (n + 1) := by
    calc ↑y + 1 + n = ↑y + (1 + n) := Nat.add_assoc ↑y 1 n
      _ = ↑y + (n + 1) := by rw [Nat.add_comm 1 n]
  have h5 : ↑x - (↑y + 1) - n = ↑x - ↑y - (n + 1) := by
    calc ↑x - (↑y + 1) - n = ↑x - ↑y - 1 - n := by rw [Nat.sub_add_eq ↑x ↑y 1]
      _ = ↑x - ↑y - (1 + n) := by rw [← Nat.sub_add_eq (↑x - ↑y) 1 n]
      _ = ↑x - ↑y - (n + 1) := by rw [Nat.add_comm 1 n]
  have h6 : base.val + ↑x - (↑y + 1) - n = base.val + ↑x - ↑y - (n + 1) := by
    calc base.val + ↑x - (↑y + 1) - n = base.val + ↑x - ↑y - 1 - n := by rw [Nat.sub_add_eq (base.val + ↑x) ↑y 1]
      _ = base.val + ↑x - ↑y - (1 + n) := by rw [← Nat.sub_add_eq (base.val + ↑x - ↑y) 1 n]
      _ = base.val + ↑x - ↑y - (n + 1) := by rw [Nat.add_comm 1 n]
  unfold hSub.helper.checkForCarry
  simp only [h2, h3, h4]
  split
  · rename _ => g1; split
    · rename _=> g2 -- case isTrue.isTrue
      simp only [Fin.toNat_eq_val, List.cons.injEq, Fin.mk.injEq]
      simp only [Nat.div_eq_zero_iff.mpr (.inr h1), Nat.div_eq_zero_iff.mpr (.inr hn), and_true]
      exact h5
    · rename _=> g2; exact absurd g1 g2
  · rename _=> g1; split
    · rename _=> g2; exact absurd g2 g1
    · rename _=> g2 -- case isFalse.isFalse
      simp only [Fin.toNat_eq_val, List.cons.injEq, Fin.mk.injEq]
      simp only [Nat.div_eq_zero_iff.mpr (.inr h1), Nat.div_eq_zero_iff.mpr (.inr hn), and_true]
      exact h6

theorem hSub_helper_checkForCarry_succ_eq_of_lt_eq {base : NatGtOne} {x y : base.Fin}
  {xs ys : List base.Fin} {n : Nat} (hy : y.val + 1 < base.val) :
  hSub.helper.checkForCarry base x ⟨Fin.toNat y + 1, hy⟩ xs ys n = hSub.helper.checkForCarry base x y xs ys (n + 1) := by
  simp only [hSub.helper.checkForCarry]
  split
  · rename _ => g1; simp only [Fin.toNat] at g1; split
    · rename _=> g2 -- case isTrue.isTrue
      simp
      sorry
    · rename _=> g2
      simp
      sorry
  · rename _=> g1; simp only [Fin.toNat] at g1; split
    · rename _=> g2
      simp
      sorry
    · rename _=> g2 -- case isFalse.isFalse
      simp
      sorry

def x : base10.Fin := ⟨9, by  decide⟩
#eval x

def xs : List  base10.Fin := [base10.one]
#eval xs

def y : base10.Fin := base10.zero
#eval y

def ys : List base10.Fin := [base10.zero]
#eval ys

def n : Nat := 9
#eval n

#eval ↑x - (Fin.toNat y + 1) - n
#eval ↑x - ↑y

#eval hSub.helper.checkForCarry base10 x (y + 1) xs ys n
#eval hSub.helper.checkForCarry base10 x y xs ys (n + 1)

#eval hSub.helper base10 xs ys (n / base10.val)
#eval hSub.helper base10 xs ys ((n + 1) / base10.val)

#eval hSub.helper base10 xs ys 0
#eval hSub.helper base10 xs ys 1
#eval hSub.helper base10 xs ys 2
#eval hSub.helper base10 xs ys 3

theorem hSub_helper_checkForCarry_succ_eq_of {base : NatGtOne} {x y : base.Fin}
  {xs ys : List base.Fin} {n : Nat} (h : y.val + 1 < base.val) :
  hSub.helper.checkForCarry base x ⟨Fin.toNat y + 1, h⟩ xs ys n = hSub.helper.checkForCarry base x y xs ys (n + 1) := by
  induction n using Nat.strongRecOn generalizing x y xs ys with
  | _ l ih =>
    unfold hSub.helper.checkForCarry
    if g : l = 0 then
      rw [g]
      simp only [Nat.zero_mod, Nat.zero_div, Nat.sub_zero, Nat.zero_add]
      simp only [Nat.mod_eq_of_lt base.property, Nat.div_eq_of_lt base.property, Nat.add_zero]
      rfl
    else
      sorry

theorem hSub_helper_succ_cons_eq_of {base : NatGtOne} {y : base.Fin} {a ys : List base.Fin} {n : Nat} (h : y.val + 1 < base.val) :
  hSub.helper base a (⟨y + 1, h⟩ :: ys) n = hSub.helper base a (y :: ys) (n + 1) := by
  unfold hSub.helper
  match a with
  | [] => simp only
  | x :: xs => simp only ; sorry

/-
  unfold hSub.helper hSub.helper.checkForCarry
  have h1 : y.val + 1 + n = y.val + (n + 1) := by
    rw [Nat.add_assoc]
    rw (occs := .pos [2]) [Nat.add_comm]
  -- https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Div/Lemmas.html#Nat.add_mod_eq_sub
  match a with
  | [] => simp only
  | x::xs =>
    if g : y.val + 1 + n ≤ x.val then
      have h2 : y.val + (n + 1) ≤ x.val := by rwa [← h1]
      simp only [Fin.toNat_eq_val, Nat.sub_add_eq, Nat.sub_right_comm]
      -- ↑y + 1 + n % base.val = ↑y + (n + 1) % base.val
      sorry
    else
      have h2 : ¬ y.val + (n + 1) ≤ x.val := by rwa [← h1]
      simp only [Fin.toNat_eq_val, g, Nat.sub_add_eq, Nat.sub_right_comm]
      sorry
-/

theorem hSub_helper_add_cons_eq {base : NatGtOne} {n : Nat} {y : base.Fin} {a ys : List base.Fin} {n : Nat} (h : y.val + n < base.val)  :
  hSub.helper base a (⟨y.val + n, h⟩ :: ys) n = hSub.helper base a (y :: ys) n := by sorry


end TZNumeral
