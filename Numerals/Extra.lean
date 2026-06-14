/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

namespace  Classical

theorem imp_iff_not_imp_not {p q : Prop} : (p → q) ↔ (¬q → ¬p) := by
  rw [← Classical.or_iff_not_imp_left, or_comm, Classical.or_iff_not_imp_left, Classical.not_not]

theorem iff_iff_not_iff_not {p q : Prop} : (p ↔ q) ↔ (¬p ↔ ¬q) := by
  constructor
  · intro h
    exact not_congr h
  · intro h
    have : ¬¬p ↔ ¬¬q := not_congr h
    simp only [Classical.not_not] at this
    assumption

end Classical

namespace Nat

/--
This lemma is often used for asserting that `basis` is greater than `0`.
`1 < basis` is always requested but sometimes `0 < basis` is need as assumption
for theorems used in proofs.
-/
theorem pos_of_one_lt {a : Nat} (h : 1 < a) : 0 < a := (Nat.lt_trans (by decide)) h

theorem add_sub_lt_of {a b c : Nat} (h1 : b < a) (h2 : b < c) : a + b - c < a := by
  if g1 : c ≤ a then
    have h3 : a + b - c = a - (c - b) := Nat.Simproc.add_sub_le a (Nat.le_of_lt h2)
    have h4 : 0 < a := Nat.lt_of_le_of_lt (Nat.zero_le b) h1
    have h5 : 0 < c - b := Nat.sub_pos_of_lt h2
    rw [h3]
    exact (Nat.sub_lt h4) h5
  else -- c > a
    have h3 : a < c := Nat.lt_of_not_le g1
    if g2 : b = 0 then
      have h4 : a + b - c = 0 := by
        simp only [g2, Nat.add_zero, Nat.sub_eq_zero_of_le (Nat.le_of_lt h3)]
      have h5 : 0 < a := Nat.lt_of_le_of_lt (Nat.zero_le b) h1
      rwa [h4]
    else
      have h4 : 0 < b := Nat.pos_of_ne_zero g2
      have h5 : a + 0 < a + b := Nat.add_lt_add_left h4 a
      have h6 : a < a + b := by rwa [Nat.add_zero] at h5
      have h7 : a + b - a = b := by simp only [Nat.add_sub_cancel_left]
      have h8 : a + b - c < a + b - a := Nat.sub_lt_sub_left h6 h3
      have h9 : a + b - c < b := by rw (occs := .pos [2]) [← h7]; exact h8
      exact Nat.lt_trans h9 h1

theorem eq_zero_of_one_lt_of_mod_eq_zero_of_lt {a b : Nat}
  (h1 : 1 < b) (h2 : a % b = 0) (h3 : a < b) : a = 0 := by
  have h4 : b ∣ a  := Nat.dvd_iff_mod_eq_zero.mpr h2
  have h5 : a < b := Or.resolve_left (.inr h3) (Nat.ne_zero_of_lt h1)
  exact Nat.eq_zero_of_dvd_of_lt h4 h5

theorem mod_ne_zero_of_one_lt_of_div_zero_of_ne {a b : Nat}
  (h1 : 1 < b) (h2 : a / b = 0) (h3 : a ≠ 0) : a % b ≠ 0 := by
  have h4 : a < b := Nat.lt_of_div_eq_zero (Nat.pos_of_one_lt h1) h2
  false_or_by_contra; rename _ => h5
  have h6 : a = 0 := eq_zero_of_one_lt_of_mod_eq_zero_of_lt h1 h5 h4
  contradiction

theorem add_mul_mod_eq {a b base : Nat} (halt : a < base) : (a + base * b) % base = a := by
  rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt halt]

theorem add_mul_mod_eq_iff_eq_of {a b c d base : Nat} (halt : a < base) (hclt : c < base) :
  (a + base * b) % base = (c + base * d) % base ↔ a = c := by
  rw [add_mul_mod_eq halt, add_mul_mod_eq hclt]

theorem add_mul_div_eq_iff_eq_of {a b c d base : Nat} (halt : a < base) (hclt : c < base) :
  (a + base * b) / base = (c + base * d) / base ↔ b = d := by
  have : 0 < base := Nat.lt_of_le_of_lt (Nat.zero_le a) halt
  rw [Nat.add_mul_div_left a b this, Nat.add_mul_div_left c d this]
  rw [(Nat.div_eq_zero_iff_lt this).mpr halt, Nat.zero_add]
  rw [(Nat.div_eq_zero_iff_lt this).mpr hclt, Nat.zero_add]

theorem mod_eq_mod_of_eq {a b base : Nat} (h: a = b) : a % base = b % base := by
  rw [h]

theorem div_eq_div_of_eq {a b base : Nat} (h: a = b) : a / base = b / base := by
  rw [h]

theorem add_mul_eq_iff_eq_and_eq_of {a b c d base : Nat} (halt : a < base) (hclt : c < base) :
  a + base * b = c + base * d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h1 : (a + base * b) % base = (c + base * d) % base := mod_eq_mod_of_eq h
    have h2 : (a + base * b) / base = (c + base * d) / base := div_eq_div_of_eq h
    exact And.intro ((add_mul_mod_eq_iff_eq_of halt hclt).mp h1) ((add_mul_div_eq_iff_eq_of halt hclt).mp h2)
  · intro h
    rw [h.left, h.right]

theorem add_mul_lt_of_lt_of_lt {a b x y base : Nat} (hab : a < b) (hx : x < base) :
  x + base * a < y + base * b := by
  calc x + base * a < base + base * a := Nat.add_lt_add_right hx (base * a)
    _ = base * 1 + base * a := by rw [Nat.mul_one]
    _ = base * (a + 1) := by rw [← Nat.left_distrib base 1 a, Nat.add_comm]
    _ ≤ base * b := Nat.mul_le_mul_left base (Nat.succ_le_of_lt hab)
    _ ≤ y + base * b := Nat.le_add_left (base * b) y

theorem add_mul_le_iff_le_of {a b x y base : Nat} (hab: a ≠ b) (hx : x < base) (hy : y < base)  :
  x + base * a ≤ y + base * b ↔ a ≤ b := by
  constructor
  · intro h
    false_or_by_contra; rename _ => hc
    have : y + base * b < x + base * a := add_mul_lt_of_lt_of_lt (Nat.lt_of_not_le hc) hy
    exact absurd h (Nat.not_le_of_lt this)
  · intro h
    have : x + base * a < y + base * b := add_mul_lt_of_lt_of_lt (Nat.lt_of_le_of_ne h hab) hx
    exact Nat.le_of_lt this

theorem sub_add_mul_sub_eq_of {a b x y base : Nat} (hab: b ≤ a) (hxy : y ≤ x):
  x - y + base * (a - b) = x + base * a - (y + base * b) := by
  have : base * b ≤ base * a := Nat.mul_le_mul_left base hab
  simp only [Nat.mul_sub_left_distrib, ← Nat.add_sub_assoc this]
  simp only [← Nat.sub_add_comm hxy, Nat.sub_sub]

theorem add_sub_add_mul_sub_sub_eq_of {a b x y base : Nat}
  (hab: b < a ) (hy : y < base) (hb : 1 < base):
  base + x - y + base * (a - b - 1) = x + base * a - (y + base * b) := by
  have h1 : 0 < base := Nat.lt_trans (by decide) hb
  have h2 : b ≤ a := Nat.le_of_lt hab
  have h3 : 0 < a - b :=  Nat.sub_pos_of_lt hab
  have h4 : 1 ≤ a - b := Nat.succ_le_iff.mpr h3
  have h5 : base ≤ base * (a - b) := by
    rw (occs := .pos [1]) [← Nat.mul_one base]
    exact (Nat.mul_le_mul_left_iff h1).mpr h4
  have h6 : y ≤ base + x := Nat.le_of_lt (Nat.lt_add_right x hy)
  have h7 : base + base * b ≤ base * a := by
    rwa [Nat.mul_sub_left_distrib base a b, Nat.le_sub_iff_add_le (Nat.mul_le_mul_left base h2)] at h5
  have h8 : y + base * b ≤ base * a := Nat.le_trans (Nat.add_le_add_right (Nat.le_of_lt hy) (base * b)) h7
  have h9 : y + base * b ≤ x + base * a := Nat.le_trans h8 (Nat.le_add_left (base * a) x)
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.add_sub_assoc h5 (base + x - y)]
  rw [sub_add_mul_sub_eq_of h2 h6]
  rw (occs := .pos [1]) [Nat.add_assoc]
  rw [Nat.add_sub_assoc h9 base, Nat.add_sub_cancel_left base]

end Nat

section List

namespace List

/--
asserts the obvious fact that if `p` is true for all elements of a non-empty
list `l`, it particular holds for the last element in the list provided by `List.getLast`.
-/
theorem getLast_true_of_all_true_of_ne_nil {α : Type} (l : List α) (p : α → Bool)
  (ha : l.all p) (hn : l ≠ []) : p (l.getLast hn) := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    rw [List.all_cons, Bool.and_eq_true] at ha
    match xs with
    | [] =>
      rw [List.getLast_singleton]
      exact ha.left
    | xxs::xss =>
      have : xxs::xss ≠ [] := List.cons_ne_nil xxs xss
      rw [List.getLast_cons_cons]
      exact ih ha.right this

end List
end List
