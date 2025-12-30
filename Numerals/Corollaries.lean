/-
Copyright (c) 2025 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

@[simp]
theorem or_elim_of_not {p q : Prop} (h : p ∨ q) (g : ¬ p) : q :=
  Or.elim h (fun t : p => False.elim (g t)) id

@[simp]
theorem iff_iff_iff_not_not {p q : Prop} : (p ↔ q) ↔ (¬p ↔ ¬q) := by
  constructor
  · intro h
    exact not_congr h
  · intro h
    have : ¬¬p ↔ ¬¬q := not_congr h
    simp only [Classical.not_not] at this
    assumption

namespace Nat

@[simp]
theorem gt_zero_of_gt_one {n : Nat} (h : 1 < n) : 0 < n := Nat.lt_trans (by decide) h

@[simp]
theorem pos_of_one_lt {a : Nat} (h : 1 < a) : 0 < a := (Nat.lt_trans (by decide)) h

@[simp]
theorem div_ne_zero {a b : Nat} (h1 : b ≠ 0) (h2 : ¬ a < b) : ¬ a / b = 0  :=
  Nat.div_ne_zero_iff.mpr (And.intro h1 (Nat.le_of_not_lt h2))

@[simp]
theorem eq_zero_of_lt_of_mod_eq_zero {a b : Nat}
  (h1 : 1 < b) (h2 : a % b = 0) (h3 : b = 0 ∨ a < b) : a = 0 := by
  have h4 : b ∣ a  := Nat.dvd_iff_mod_eq_zero.mpr h2
  have h5 : a < b := or_elim_of_not h3 (Nat.ne_zero_of_lt h1)
  exact Nat.eq_zero_of_dvd_of_lt h4 h5

@[simp]
theorem ne_zero_mod_of_ne_zero {a b : Nat}
  (h1 : 1 < b) (h2 : a / b = 0) (h3 : a ≠ 0) : a % b ≠ 0 := by
  have h4 : a < b := Nat.lt_of_div_eq_zero (Nat.pos_of_one_lt h1) h2
  false_or_by_contra; rename _ => h5
  have h6 : a = 0 := Nat.eq_zero_of_lt_of_mod_eq_zero h1 h5 (Or.inr h4)
  contradiction

@[simp]
theorem lt_sub_3_mul_3_mul {a : Nat}
  (h : 2 ≤ a) : 3 * a - 3 < a * a := by
  if g : a = 2 then
    rw [g]
    decide
  else
    have h1 : 2 < a :=
      or_elim_of_not
        (Nat.lt_or_gt_of_ne (by simp only [ne_eq, g, not_false_eq_true]))
        (by simp only [Nat.not_lt, h])
    have h2 : 3 ≤ a := Nat.le_of_pred_lt h1
    have h3 : 3 * a ≤ a * a := Nat.mul_le_mul_right a h2
    have h4 : 3 * 1 ≤ 3 * a := Nat.mul_le_mul_left 3 (Nat.le_trans (by decide) h)
    have h5 : 3 * 1 ≤ a * a := Nat.le_trans h4 h3
    have h6 : 3 * a - 3 ≤ a * a - 3 := (Nat.sub_le_sub_iff_right h5).mpr h3
    have h7 : a * a - 3 < a * a := Nat.div_rec_lemma (And.intro (by decide) h5)
    exact Nat.lt_of_le_of_lt h6 h7

@[simp]
theorem lt_sum_div_base_of_lt_base {a b c base : Nat}
  (hab : a < base) (hbb : b < base) (hcb : c < base) (hb : 1 < base) :
  (a + b + c) / base < base := by
  have h1 : a + b + c ≤ 3 * base - 3 := by
    calc a + b + c ≤ a + b + (base - 1) := Nat.add_le_add_left (Nat.le_sub_one_of_lt hcb) (a + b)
      _ = (base - 1) + (a + b) := Nat.add_comm (a + b) (base - 1)
      _ = (base - 1) + a + b := by rw [← Nat.add_assoc (base - 1) a b]
      _ ≤ (base - 1) + a + (base - 1) := Nat.add_le_add_left (Nat.le_sub_one_of_lt hbb) ((base - 1) + a)
      _ = (base - 1) + ((base - 1) + a) := Nat.add_comm ((base - 1) + a) (base - 1)
      _ = (base - 1) + (base - 1) + a := by rw [← Nat.add_assoc (base - 1) (base - 1) a]
      _ ≤ (base - 1) + (base - 1) + (base - 1) := Nat.add_le_add_left (Nat.le_sub_one_of_lt hab) ((base - 1) + (base - 1))
      _ = 2 * (base - 1) + (base - 1) := by rw [← Nat.two_mul (base -1)]
      _ = 3 * (base - 1) := by rw [← Nat.succ_mul 2 (base -1)]
      _ = 3 * base - 3 := by rw [Nat.mul_sub 3 base 1]
  have h2 : a + b + c < base * base := Nat.lt_of_le_of_lt h1 (Nat.lt_sub_3_mul_3_mul (Nat.succ_le_iff.mpr hb))
  exact Nat.div_lt_of_lt_mul h2

@[simp]
theorem mod_add_mul_eq (n m : Nat) {base : Nat} (hn: n < base) : (n + m * base) % base = n := by
  induction m with
  | zero => simp only [Nat.zero_mul, Nat.add_zero]; exact Nat.mod_eq_of_lt hn
  | succ m ih =>
    have : (n + m * base) % base + base % base < base := by simp only [Nat.mod_self base, Nat.add_zero, ih, hn]
    have hd : n + (m + 1) * base = n + m * base + base := by
      rw [Nat.add_mul m 1 base, Nat.one_mul base, ← Nat.add_assoc n (m * base) base]
    calc (n + (m + 1) * base) % base = (n + m * base + base) % base := by rw [hd]
      _ = (n + m * base) % base + base % base - if (n + m * base) % base + base % base < base then 0 else base := Nat.add_mod_eq_sub
      _ = (n + m * base) % base + 0 - if (n + m * base) % base + 0 < base then 0 else base := by rw [Nat.mod_self base]
      _ = (n + m * base) % base - if (n + m * base) % base < base then 0 else base := by rw [Nat.add_zero]
      _ = n - if n < base then 0 else base := by rw [ih]
      _ = n - 0 := by simp only [hn, ↓reduceIte, Nat.sub_zero]
      _ = n := by rw [Nat.sub_zero]

@[simp]
theorem div_add_mul_eq (n m : Nat) {base : Nat} (hn: n < base) : (n + m * base) / base = m := by
  induction m with
  | zero => simp only [Nat.zero_mul, Nat.add_zero]; exact Nat.div_eq_of_lt hn
  | succ m ih =>
    have hd : n + (m + 1) * base = n + m * base + base := by
      rw [Nat.add_mul m 1 base, Nat.one_mul base, ← Nat.add_assoc n (m * base) base]
    have : (n + m * base + base) / base = (n + m * base) / base + 1 :=
      Nat.add_div_right (n + m * base) (Nat.lt_of_le_of_lt (zero_le n) hn)
    rw [hd, this, ih]

end Nat

namespace List

@[simp]
theorem cons_singleton_iff_and_eq_nil {α : Type} {a b : α} {as : List α} :
  (a::as = [b]) ↔ (a = b ∧ as = []) := by simp only [cons.injEq]

@[simp]
theorem getLast_cons_of_singleton {α : Type} (a: α) {b: α} {as : List α} (h : as = [b]) :
  (a::as).getLast (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) = b := by
  have g : as ≠ [] := by simp only [h, ne_eq, cons_ne_self, not_false_eq_true]
  have : as.getLast g = b := by simp only [h, getLast_singleton]
  rwa [List.getLast_cons g]

end List
