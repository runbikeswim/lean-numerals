/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.EquivIsZero
import Numerals.AllDigitsBase
import Numerals.NoTrailingZero
import Numerals.LeLt

namespace NumeralAux

section SubAux

def subAux (a b : List Nat) (n base : Nat) : List Nat :=
  let rec helper (x y n base : Nat) (xs ys : List Nat) :=
    if y + n ≤ x then
      (x - y - n)::(subAux xs ys 0 base)
    else
      (base + x - y - n)::(subAux xs ys 1 base)
  match a, b with
  | [], _ => []
  | x::xs, [] => helper x 0 n base xs []
  | x::xs, y::ys => helper x y n base xs ys

theorem subAux_nil_eq_nil {a : List Nat} {n base : Nat} : subAux [] a n base = [] := by
  simp only [subAux]

theorem subAux_nil_eq {a : List Nat} {base : Nat} : subAux a [] 0 base = a := by
  induction a with
  | nil => simp only [subAux]
  | cons x xs ih =>
    simp only [subAux, subAux.helper, Nat.zero_add, Nat.zero_le, reduceIte, Nat.sub_zero, ih]

theorem subAux_cons_nil_eq {x n base : Nat} {xs : List Nat} :
  subAux (x::xs) [] n base =
    (if n ≤ x then
      (x - n)::(subAux xs [] 0 base)
    else
      (base + x - n)::(subAux xs [] 1 base)) := by
  simp only [subAux, subAux.helper, Nat.zero_add, Nat.sub_zero]

theorem subAux_cons_cons_eq {x y n base : Nat} {xs ys : List Nat} :
  subAux (x::xs) (y::ys) n base =
    (if y + n ≤ x then
      (x - y - n)::(subAux xs ys 0 base)
    else
      (base + x - y - n)::(subAux xs ys 1 base)) := by
  simp only [subAux, subAux.helper]

theorem subAux_succ_cons_succ_cons_eq {x y n base : Nat} {xs ys : List Nat} :
  subAux ((x + 1)::xs) ((y + 1)::ys) n base = subAux (x::xs) (y::ys) n base := by
  unfold subAux subAux.helper
  if g : y + n ≤ x then
    have : y + 1 + n ≤ x + 1 := by
      rw [Nat.add_assoc]
      rw (occs := .pos [2]) [Nat.add_comm]
      rw [← Nat.add_assoc]
      simp only [Nat.add_le_add_right g 1]
    simp only [g, this, reduceIte, Nat.add_sub_add_right x 1 y]
  else
    have h1 : x < y + n := Nat.lt_of_not_le g
    have h2 : x + 1 < y + 1 + n := by
      rw [Nat.add_assoc]
      rw (occs := .pos [3]) [Nat.add_comm]
      rw [← Nat.add_assoc]
      simp only [Nat.add_lt_add_right h1 1]
    have h3 : ¬ y + 1 + n ≤ x + 1 := Nat.not_le_of_lt h2
    simp only [g, h3, reduceIte, ← Nat.add_assoc, Nat.add_sub_add_right (base + x) 1 y]

theorem subAux_succ_cons_eq {y n base : Nat} {a ys : List Nat} :
  subAux a ((y + 1)::ys) n base = subAux a (y::ys) (n + 1) base := by
  unfold subAux subAux.helper
  have h1 : y + 1 + n = y + (n + 1) := by
    rw [Nat.add_assoc]
    rw (occs := .pos [2]) [Nat.add_comm]
  match a with
  | [] => simp only
  | x::xs =>
    simp only
    if g : y + 1 + n ≤ x then
      have : y + (n + 1) ≤ x := by rwa [← h1]
      simp only [g, this, reduceIte]
      rw [Nat.sub_sub]
      rw (occs := .pos [3]) [Nat.add_comm]
      rw [Nat.sub_sub, Nat.add_assoc]
    else
      have h2 : ¬ y + (n + 1) ≤ x := by rwa [← h1]
      simp only [g, h2, reduceIte, Nat.sub_sub]
      rw (occs := .pos [1]) [Nat.add_assoc]
      rw (occs := .pos [3]) [Nat.add_comm]

theorem subAux_add_cons_eq {y n m base : Nat} {a ys : List Nat} :
  subAux a ((y + m)::ys) n base = subAux a (y::ys) (n + m) base := by
  induction m generalizing a y ys n with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
    rw [← Nat.add_assoc, subAux_succ_cons_eq, ih, Nat.add_assoc, Nat.add_comm 1 k, ← Nat.add_assoc]

theorem subAux_succ_cons_succ_eq {x n base : Nat} {xs b : List Nat} :
  subAux ((x + 1)::xs) b (n + 1) base = subAux (x::xs) b n base := by
  match b with
  | [] =>
    simp only [subAux, subAux.helper, Nat.zero_add, Nat.sub_zero]
    if g : n ≤ x then
      have h1 : n + 1 ≤ x + 1 := Nat.add_le_add_right g 1
      have h2 : x + 1 - (n + 1) = (x - n) := Nat.add_sub_add_right x 1 n
      simp only [g, h1, reduceIte, h2]
    else
      have h1 : x < n := Nat.lt_of_not_le g
      have h2 : x + 1 < n + 1 := Nat.add_lt_add_iff_right.mpr h1
      have h3 : ¬ n + 1 ≤ x + 1 := Nat.not_le_of_lt h2
      simp only [g, h3, reduceIte, ← Nat.add_assoc, Nat.add_sub_add_right (base + x) 1 n]
  | y::ys =>
    have h1 : subAux ((x + 1)::xs) (y::ys) (n + 1) base = subAux ((x + 1)::xs) ((y + 1)::ys) n base := by
      rw [subAux_succ_cons_eq]
    have h2 : subAux ((x + 1)::xs) ((y + 1)::ys) n base = subAux (x::xs) (y::ys) n base := by
      rw [subAux_succ_cons_succ_cons_eq]
    rw [h1, h2]

theorem subAux_cons_eq_subAux_sub_cons_zero_of {x n base : Nat} {xs b : List Nat} (h : n ≤ x) :
  subAux (x::xs) b n base = subAux ((x - n)::xs) b 0 base := by
  induction n generalizing x xs b with
  | zero => simp only [Nat.sub_zero]
  | succ k ih =>
    have h1 : 1 ≤ x := Nat.le_trans (Nat.le_add_left 1 k) h
    have h2 : x - 1 + 1 = x := Nat.sub_add_cancel h1
    have h3 : k ≤ x - 1 := Nat.le_sub_of_add_le h
    have h4 : subAux (x::xs) b (k + 1) base = subAux ((x - 1)::xs) b k base := by
      rw [← h2, subAux_succ_cons_succ_eq, Nat.add_sub_cancel]
    rw [h4, ih h3, Nat.add_comm, Nat.sub_add_eq x 1 k]

theorem subAux_singleton_zero_eq {a : List Nat} {n base : Nat} : subAux a [n] 0 base = subAux a [] n base := by
  unfold subAux subAux.helper
  match a with
  | [] => simp only
  | x::xs => simp only [Nat.add_zero, Nat.zero_add, Nat.sub_zero]

end SubAux

section EquivAux_SubAux

theorem equivAux_subAux_nil_of_equivAux {a b : List Nat} {base : Nat} (h: equivAux a b) :
  equivAux (subAux a b 0 base) [] := by
  induction b generalizing a with
  | nil => rwa [subAux_nil_eq]
  | cons y ys ih =>
    match a with
    | [] => simp only [subAux_nil_eq_nil, equivAux_refl]
    | x::xs =>
      rw [equivAux_cons_iff_eq_and_equivAux] at h
      simp only [← h.left, subAux_cons_cons_eq, Nat.add_zero, Nat.le_refl, reduceIte, Nat.sub_zero, Nat.sub_self]
      exact equivAux_cons_nil_of_equivAux_nil (ih h.right)

end EquivAux_SubAux

section ToNatAux_SubAux

theorem toNatAux_subAux_nil_zero_eq_zero {a : List Nat} {base : Nat} :
  toNatAux (subAux [] a 0 base) base = 0 := by
  unfold subAux toNatAux toNatAux.helper
  rfl

theorem toNatAux_subAux_nil_one_eq_of {a : List Nat} {base : Nat} (hntza : noTrailingZeroAux a) (hb : 1 < base) :
  toNatAux (subAux a [] 1 base) base = toNatAux a base - 1 := by
  induction a with
  | nil => simp only [subAux_nil_eq_nil, toNatAux_nil_eq]
  | cons x xs ih =>
    simp only [subAux,subAux.helper, Nat.zero_add, Nat.sub_zero]
    if g : 1 ≤ x then
      simp only [g, reduceIte, subAux_nil_eq, toNatAux_cons_eq, Nat.sub_add_comm g]
    else
      have h1 : 1 ≤ base := Nat.le_of_lt hb
      have h2 : x = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp g)
      have h3 : noTrailingZeroAux xs ∧ (xs = [] → x ≠ 0) := noTrailingZeroAux_tail_and_of hntza
      have h4 : xs ≠ [] := by
        false_or_by_contra; rename _ => hc
        exact absurd h2 (h3.right hc)
      have h5 : ¬ isZeroAux xs := by
        false_or_by_contra; rename _ => hc
        exact absurd ((isZeroAux_iff_eq_nil_of_noTrailingZeroAux h3.left).mp hc) h4
      have h6 : toNatAux xs base ≠ 0 := by
         false_or_by_contra; rename _ => hc
         exact absurd ((toNatAux_eq_zero_iff_isZeroAux hb).mp hc) h5
      have h7 : 1 ≤ toNatAux xs base := Nat.one_le_iff_ne_zero.mpr h6
      have h8 : base ≤ base * toNatAux xs base := by
        rw (occs := .pos [1]) [← Nat.mul_one base]
        exact Nat.mul_le_mul_left base h7
      have h9 : base * toNatAux xs base + (base - 1) = base * toNatAux xs base - 1 + base := by
        rw [← Nat.add_sub_assoc h1 (base * toNatAux xs base)]
        rw [Nat.sub_add_comm (Nat.le_trans h1 h8)]
      simp only [h2, Nat.le_zero_eq, Nat.succ_ne_self, reduceIte, Nat.add_zero]
      simp only [toNatAux_cons_eq, Nat.zero_add]
      simp only [ih h3.left, Nat.mul_sub_left_distrib, Nat.mul_one, Nat.add_comm]
      simp only [← Nat.sub_add_comm h8, h9, Nat.add_sub_cancel]

/-
this example shows that `noTrailingZeroAux a` is neccesary in `toNatAux_subAux_nil_one_eq_of`
-/
example : toNatAux (subAux [0] [] 1 10) 10 ≠ (toNatAux [0] 10) - 1 := by
  have h1 : toNatAux (subAux [0] [] 1 10) 10 = 9 := by
    simp only [subAux, subAux.helper, Nat.zero_add, Nat.le_zero_eq]
    simp only [Nat.succ_ne_self, ↓reduceIte, Nat.add_zero, Nat.sub_zero]
    decide
  have h2 : (toNatAux [0] 10) - 1 = 0 := by
    simp only [toNatAux]
    decide
  rw [h1, h2]
  decide

theorem pos_toNatAux_subAux_of_ltAux_of {a b : List Nat} {base : Nat} (h : ltAux b a)
  (hb : 1 < base) (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  0 < toNatAux (subAux a b 0 base) base := by
  induction b generalizing a with
  | nil => simp only [subAux_nil_eq]; exact toNatAux_lt_toNatAux_of_ltAux h hb hblt halt
  | cons y ys ih =>
    match a with
    | [] => exact absurd h (not_ltAux_cons_nil)
    | x::xs =>
      if g1 : y = x  then
        have h1 : ltAux ys xs := by
          rw [g1] at h
          exact ltAux_of_ltAux_cons h
        have h2 : allDigitsLtBase xs base := (allDigitsLtBase_cons_iff.mp halt).right
        have h3 : allDigitsLtBase ys base := (allDigitsLtBase_cons_iff.mp hblt).right
        have h4 : 0 < base := Nat.lt_trans (by decide) hb
        simp only [subAux_cons_cons_eq, Nat.add_zero, Nat.sub_zero, g1, Nat.le_refl]
        simp only [reduceIte, toNatAux_cons_eq, Nat.sub_self, Nat.zero_add]
        rw [← Nat.mul_zero base]
        simp only [Nat.mul_lt_mul_left h4]
        exact ih h1 h2 h3
      else
        simp only [subAux_cons_cons_eq, Nat.add_zero, Nat.sub_zero]
        if g2 : y ≤ x then
          have h1 : y < x := Nat.lt_of_le_of_ne g2 g1
          have h2 : 0 < x - y := Nat.sub_pos_of_lt h1
          simp only [g2, reduceIte, toNatAux_cons_eq]
          exact Nat.lt_add_right (base * toNatAux (subAux xs ys 0 base) base) h2
        else
          have h1 : y < base := (allDigitsLtBase_cons_iff.mp hblt).left
          have h2 : 0 < base - y := Nat.sub_pos_of_lt h1
          have h3 : 0 < base - y + x := Nat.lt_add_right x h2
          have h4 : 0 < base + x - y := by rwa [Nat.sub_add_comm (Nat.le_of_lt h1)]
          simp only [g2, reduceIte, toNatAux_cons_eq]
          exact Nat.lt_add_right (base * toNatAux (subAux xs ys 1 base) base) h4

theorem toNatAux_subAux_one_eq_of {a b : List Nat} {base : Nat}
  (h : ltAux b a) (hntza : noTrailingZeroAux a)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) (hb : 1 < base) :
  toNatAux (subAux a b 1 base) base = toNatAux (subAux a b 0 base) base - 1 := by
  induction b generalizing a with
  | nil =>
    rw [subAux_nil_eq]
    exact toNatAux_subAux_nil_one_eq_of hntza hb
  | cons y ys ih =>
    match a with
    | [] => simp only [subAux_nil_eq_nil, toNatAux_nil_eq]
    | x::xs =>
      simp only [subAux_cons_cons_eq]
      if g1 : y + 1 ≤ x then
        have h1 : 1 ≤ x - y := by
          rw [Nat.add_comm] at g1
          exact Nat.le_sub_of_add_le g1
        have h2 : y ≤ y + 1 := Nat.le_succ y
        have h3 : y ≤ x := Nat.le_trans h2 g1
        simp only [g1, Nat.add_zero, Nat.sub_zero, h3, reduceIte, toNatAux_cons_eq, Nat.sub_add_comm h1]
      else
        simp only [g1, reduceIte, Nat.add_zero, Nat.sub_zero]
        if g2 : x = y then
          have h1 : 1 ≤ base := Nat.le_of_lt hb
          have h2 : ltAux ys xs := by
            rw [g2] at h
            exact ltAux_of_ltAux_cons h
          have h3 : noTrailingZeroAux xs := (noTrailingZeroAux_tail_and_of hntza).left
          have h4 : allDigitsLtBase xs base := (allDigitsLtBase_cons_iff.mp halt).right
          have h5 : allDigitsLtBase ys base := (allDigitsLtBase_cons_iff.mp hblt).right
          have h6 : toNatAux (subAux xs ys 1 base) base = toNatAux (subAux xs ys 0 base) base - 1 :=
            ih h2 h3 h4 h5
          have h7 : ¬ equivAux xs ys := by
            rw [equivAux_iff_equivAux]
            exact not_equivAux_of_ltAux h2
          have h8 : 1 ≤ toNatAux (subAux xs ys 0 base) base :=
            Nat.succ_le_of_lt (pos_toNatAux_subAux_of_ltAux_of h2 hb h4 h5)
          have h9 : base ≤ base * toNatAux (subAux xs ys 0 base) base := by
            rw (occs := .pos [1])[← Nat.mul_one base]
            exact Nat.mul_le_mul_left base h8
          simp only [g2, Nat.le_refl, reduceIte, Nat.add_sub_cancel, toNatAux_cons_eq, Nat.sub_self, Nat.zero_add, h6]
          simp only [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.sub_add_comm h1, ← Nat.add_sub_assoc h9 base]
          simp only [Nat.add_sub_cancel_left]
        else
          have h1 : x < y + 1 := Nat.lt_of_not_le g1
          have h2 : x ≤ y := Nat.le_of_lt_succ h1
          have h3 : ¬ y ≤ x := by
            false_or_by_contra; rename _ => hc
            exact absurd (Nat.le_antisymm h2 hc) g2
          have h4 : y < base := (allDigitsLtBase_cons_iff.mp hblt).left
          have h5 : 0 < base - y := Nat.sub_pos_of_lt h4
          have h6 : 0 < base - y + x := Nat.lt_add_right x h5
          have h7 : 0 < base + x - y := by rwa [Nat.sub_add_comm (Nat.le_of_lt h4)]
          have h8 : 1 ≤ base + x - y := Nat.succ_le_of_lt h7
          simp only [h3, reduceIte, toNatAux_cons_eq, Nat.sub_add_comm h8]

theorem toNatAux_subAux_left_distrib_of_equivAux {a b : List Nat} {base : Nat} (h : equivAux a b) (hb : 1 < base) :
  toNatAux (subAux a b 0 base) base = (toNatAux a base) - (toNatAux b base) := by
  have h1 : toNatAux (subAux a b 0 base) base = 0 := by
    rw [toNatAux_eq_of_equivAux (equivAux_subAux_nil_of_equivAux h) hb]
    exact toNatAux_nil_eq
  have h2 : (toNatAux a base) = (toNatAux b base) := toNatAux_eq_of_equivAux h hb
  simp only [h1, h2, Nat.sub_self]

theorem toNatAux_subAux_left_distrib_of_leAux {a b : List Nat} {base : Nat}
  (h : leAux b a) (hntza : noTrailingZeroAux a)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) (hb : 1 < base) :
  toNatAux (subAux a b 0 base) base = (toNatAux a base) - (toNatAux b base) := by
  induction a generalizing b with
  | nil =>
    have : isZeroAux b := by
      unfold isZeroAux
      exact equivAux_nil_of_leAux_nil h
    simp only [toNatAux_subAux_nil_zero_eq_zero, toNatAux_eq_zero_of_isZeroAux this, toNatAux_nil_eq]
  | cons x xs ih =>
    match b with
    | [] => simp only [subAux_nil_eq, toNatAux_nil_eq, Nat.sub_zero]
    | y::ys =>
      have h1 : noTrailingZeroAux xs := (noTrailingZeroAux_cons_iff_noTrailingZeroAux_and.mp hntza).left
      have h2 : x < base ∧ allDigitsLtBase xs base := allDigitsLtBase_cons_iff.mp halt
      have h3 : y < base ∧ allDigitsLtBase ys base := allDigitsLtBase_cons_iff.mp hblt
      if g1 : equivAux ys xs then
        have h4 : y ≤ x := by
          simp only [leAux_cons_iff, g1, reduceIte] at h
          exact h
        have h5 : leAux ys xs := leAux_of_equivAux g1
        have h6 : toNatAux ys base ≤ toNatAux xs base := toNatAux_le_of_leAux h5 hb h3.right h2.right
        simp only [subAux_cons_cons_eq, Nat.add_zero, h4, reduceIte, Nat.sub_zero]
        simp only [toNatAux_cons_eq, ih h5 h1 h2.right h3.right]
        exact Nat.sub_add_mul_sub_eq_of h6 h4
      else
        have h4 : leAux ys xs := by
          simp only [leAux_cons_iff, g1, reduceIte] at h
          exact h
        if g2 : y ≤ x then
          have h5 : toNatAux ys base ≤ toNatAux xs base := toNatAux_le_of_leAux h4 hb h3.right h2.right
          simp only [subAux_cons_cons_eq, Nat.add_zero, g2, reduceIte, Nat.sub_zero]
          simp only [toNatAux_cons_eq, ih h4 h1 h2.right h3.right]
          exact Nat.sub_add_mul_sub_eq_of h5 g2
        else
          have h5 : ltAux ys xs := ltAux_iff_leAux_and_not_equivAux.mpr (And.intro h4 g1)
          have h6 : toNatAux ys base < toNatAux xs base := toNatAux_lt_toNatAux_of_ltAux h5 hb h3.right h2.right
          simp only [subAux_cons_cons_eq, Nat.add_zero, g2, reduceIte, Nat.sub_zero, toNatAux_cons_eq]
          simp only [toNatAux_subAux_one_eq_of h5 h1 h2.right h3.right hb, ih h4 h1 h2.right h3.right]
          exact Nat.add_sub_add_mul_sub_sub_eq_of h6 h3.left hb

end ToNatAux_SubAux

section AllDigitsLtBase_SubAux

theorem allDigitsLtBase_subAux {n base : Nat} (a b : List Nat) (halt : allDigitsLtBase a base) :
  allDigitsLtBase (subAux a b n base) base := by
  induction a generalizing b n with
  | nil => rwa [subAux_nil_eq_nil]
  | cons x xs ih =>
    have h1 : x < base ∧ allDigitsLtBase xs base := allDigitsLtBase_cons_iff.mp halt
    match b with
    | [] =>
      rw [subAux_cons_nil_eq]
      if g : n ≤ x then
        simp only [g, reduceIte]
        have h2 : x - n < base := Nat.sub_lt_of_lt h1.left
        have h3 : allDigitsLtBase (subAux xs [] 0 base) base := ih [] h1.right
        exact allDigitsLtBase_cons_iff.mpr (And.intro h2 h3)
      else -- n > x
        simp only [g, reduceIte]
        have h2 : base + x - n < base := Nat.add_sub_lt_of (h1.left) (Nat.lt_of_not_le g)
        have h3 : allDigitsLtBase (subAux xs [] 1 base) base := ih [] h1.right
        exact allDigitsLtBase_cons_iff.mpr (And.intro h2 h3)
    | y::ys =>
      rw [subAux_cons_cons_eq]
      if g : y + n ≤ x then
        simp only [g, reduceIte]
        have h2 : x - y - n = x - (y + n) := Nat.sub_sub x y n
        have h3 : x - y - n < base := by rw [h2]; exact Nat.sub_lt_of_lt h1.left
        have h4 : allDigitsLtBase (subAux xs ys 0 base) base := ih ys h1.right
        exact allDigitsLtBase_cons_iff.mpr (And.intro h3 h4)
      else -- y + n > x
        simp only [g, reduceIte]
        have h2: base + x - (y + n) < base := Nat.add_sub_lt_of (h1.left) (Nat.lt_of_not_le g)
        have h3: base + x - (y + n) = base + x - y - n := Nat.sub_add_eq (base + x) y n
        have h4: base + x - y - n < base := by rwa [h3] at h2
        have h5 : allDigitsLtBase (subAux xs ys 1 base) base := ih ys h1.right
        exact allDigitsLtBase_cons_iff.mpr (And.intro h4 h5)

end AllDigitsLtBase_SubAux

end NumeralAux
