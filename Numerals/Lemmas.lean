/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

/-!
# Numerals.Lemmas

This file contains definitions and theorems that are used to define types for
[numerals in positional notation](https://en.wikipedia.org/wiki/Positional_notation#Mathematics)
in file `Numerals.Basic`.

In particular, it provides non-primitive functions for basic operations such as addition and subtraction
of numerals and theorems that ensure that these functions are consistent with the respective operations on
[`Nat`](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/#Nat).
This is useful for proofing theorems that refer to the representation of natural numbers as
numerals in positional notation.

Most of the functions and theorems defined here use one or several parameter of `List Nat` as input,
which represent numerals in [little-endian notation](https://en.wikipedia.org/wiki/Endianness) with the
elements in the lists as digits. Additionally, a parameter `base : Nat` is used whenever the
[base (i.e. radix)](https://en.wikipedia.org/wiki/Radix) of the numeral matters.
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

section ToNatAux

/--
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

section EquivAux

/--
Equivalence for lists of natural numbers - two lists are _equivalent_ if they only
differ with respect to _trailing zeros_.

`equivAux` is an [equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation) on
`List Nat` - which is asserted by theorems `equivAux_refl`, `equivAux_symm` and `equivAux_trans`.

Examples:
```
#eval equivAux [0, 1, 0] [0, 1] -- true
#eval equivAux [0, 1, 0] [1, 0] -- false
#eval equivAux [1, 1, 0] [11] -- false
```
-/
def equivAux (a b : List Nat) : Prop :=
  match a, b with
  | [], [] => True
  | x::xs, [] => x = 0 ∧ equivAux xs []
  | [], y::ys => y = 0 ∧ equivAux [] ys
  | x::xs, y::ys => x = y ∧ equivAux xs ys

/--
[Reflexivity](https://en.wikipedia.org/wiki/Reflexive_relation) for `equivAux`.

Together with `equivAux_symm` and `equivAux_trans` this ensures that `equivAux` is an
[equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation).
-/
theorem equivAux_refl {a : List Nat} : equivAux a a := by
  induction a with
  | nil => simp only [equivAux]
  | cons x xs ih =>
    simp only [equivAux, ih, true_and]

/--
[Symmetry](https://en.wikipedia.org/wiki/Symmetric_relation) for `equivAux`.

Together with `equivAux_refl` and `equivAux_trans` this ensures that `equivAux` is an
[equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation).
-/
theorem equivAux_symm {a b : List Nat} (hab : equivAux a b) : equivAux b a := by
  induction a generalizing b with
  | nil =>
    induction b with
    | nil => exact hab
    | cons y ys ihy =>
      unfold equivAux at ⊢ hab
      exact And.intro hab.left (ihy hab.right)
  | cons x xs ihx =>
    match b with
    | [] | y::ys =>
      unfold equivAux at ⊢ hab
      rw [hab.left]
      exact And.intro rfl (ihx hab.right)

/--
This lemma makes it possible to apply the `rw`-tactic.
-/
theorem equivAux_iff_equivAux {a b : List Nat} : equivAux a b ↔ equivAux b a := by
  constructor
  · intro h
    exact equivAux_symm h
  · intro h
    exact equivAux_symm h

/--
[Transitivity](https://en.wikipedia.org/wiki/Transitive_relation) for `equivAux` with
`[] : List Nat` as first and two arbitrary parameters of type `List Nat` as second
and third element.
-/
theorem equivAux_trans_nil {a b : List Nat} (ha : equivAux [] a) (hab : equivAux a b) : equivAux [] b := by
  induction a generalizing b with
    | nil => exact hab
    | cons x xs ih =>
      unfold equivAux at ha hab
      match b with
      | [] =>
        simp only at hab
        exact ih ha.right hab.right
      | z::zs =>
        unfold equivAux
        simp only at ⊢ hab
        have : z = 0 := by rw [ha.left] at hab; exact (Eq.symm hab.left)
        exact And.intro this (ih ha.right hab.right)

/--
[Transitivity](https://en.wikipedia.org/wiki/Transitive_relation) for `equivAux`.

Together with `equivAux_refl` and `equivAux_symm` this ensures that `equivAux` is an
[equivalence relation](https://en.wikipedia.org/wiki/Equivalence_relation).
-/
theorem equivAux_trans {a b c : List Nat} (hab : equivAux a b) (hbc :  equivAux b c) : equivAux a c := by
  induction a generalizing b c with
  | nil => exact equivAux_trans_nil hab hbc
  | cons x xs ihx =>
    unfold equivAux at ⊢ hab hbc
    match b, c with
    | [], [] => simp only at ⊢ hab hbc; exact hab
    | y::ys, [] =>
      simp only at ⊢ hab hbc
      rw [hbc.left] at hab
      exact And.intro hab.left (ihx hab.right hbc.right)
    | [], z::zs =>
      simp only at ⊢ hab hbc
      rw [hab.left, hbc.left]
      exact And.intro rfl (ihx hab.right hbc.right)
    | y::ys, z::zs =>
      simp only at ⊢ hab hbc
      rw [hab.left, ← hbc.left]
      exact And.intro rfl (ihx hab.right hbc.right)

theorem not_equivAux_iff_not_equivAux {a b : List Nat} : ¬ equivAux a b ↔ ¬ equivAux b a :=
  Classical.iff_iff_not_iff_not.mp equivAux_iff_equivAux

theorem equivAux_cons_nil_of_equivAux_nil {xs : List Nat} (h : equivAux xs []) : equivAux (0::xs) [] := by
  unfold equivAux
  exact And.intro rfl h

theorem all_eq_zero_of_equivAux_nil {a : List Nat} (h : equivAux a []) : a.all (· = 0) := by
  induction a with
  | nil => exact List.all_nil
  | cons x xs ih =>
    simp only [equivAux] at h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact And.intro h.left (ih h.right)

theorem not_equivAux_cons_of_lt {x y : Nat} {xs ys : List Nat} (h : x < y) : ¬ equivAux (x::xs) (y::ys) := by
  have : x ≠ y := Nat.ne_of_lt h
  simp only [equivAux, Classical.not_and_iff_not_or_not]
  exact .inl this

theorem not_equivAux_of_equivAux_of_not_equivAux {a b c : List Nat}
  (hab : equivAux a b) (hbc : ¬ equivAux b c) : ¬ equivAux a c := by
  false_or_by_contra; rename _ => hac
  have : equivAux b c := equivAux_trans (equivAux_symm hab) hac
  contradiction

theorem not_equivAux_of_not_equivAux_of_equivAux {a b c : List Nat}
  (hab : ¬ equivAux a b) (hbc : equivAux b c) : ¬ equivAux a c := by
  false_or_by_contra; rename _ => hac
  have : equivAux a b := equivAux_trans hac (equivAux_symm hbc)
  contradiction

theorem equivAux_cons_iff_eq_and_equivAux {x y : Nat} {xs ys : List Nat} :
  equivAux (x::xs) (y::ys) ↔ x = y ∧ equivAux xs ys := by
  rw [equivAux]

/--
Decidable equivalence as defined by `equivAux` of a parameter
of type `List Nat` with `[] : List Nat`.
-/
def decEquivAux_nil (a : List Nat) : Decidable (equivAux [] a)  :=
  match a with
  | [] =>
    have : equivAux [] [] := by simp only [equivAux]
    isTrue this
  | x::xs =>
    if gx : x = 0 then
      match ge : decEquivAux_nil xs with
      | isTrue p =>
        have : equivAux [] (x::xs) := by
          unfold equivAux
          exact And.intro gx p
        isTrue this
      | isFalse p =>
        have : ¬ equivAux [] (x::xs) := by
          unfold equivAux
          rw [not_and]
          exact fun _ : x = 0 => p
        isFalse this
    else
      have : ¬ equivAux [] (x::xs) := by
        unfold equivAux
        rw [not_and]
        intro gx'
        contradiction
      isFalse this

/--
Decidable equivalence as defined by `equivAux` for two arbitrary parameters of type `List Nat`.
-/
def decEquivAux (a b : List Nat) : Decidable (equivAux a b)  :=
  match a, b with
  | [], [] =>
    have : equivAux [] [] := by simp only [equivAux]
    isTrue this
  | x::xs, [] =>
    match decEquivAux_nil (x::xs) with
    | isFalse p =>
      have : ¬ equivAux (x::xs) [] := by
        intro h
        exact absurd (equivAux_symm h) p
      isFalse this
    | isTrue p =>
      have : equivAux (x::xs) [] := equivAux_symm p
      isTrue this
  | [], y::ys => decEquivAux_nil (y::ys)
  | x::xs, y::ys =>
    if gxy : x = y then
      match decEquivAux xs ys with
      | isFalse p =>
        have : ¬ equivAux (x::xs) (y::ys) := by
          intro h
          simp only [equivAux] at h
          exact absurd h.right p
        isFalse this
      | isTrue p =>
        have : equivAux (x::xs) (y::ys) := by
          simp only [equivAux]
          exact And.intro gxy p
        isTrue this
    else
      have : ¬ equivAux (x::xs) (y::ys) := by
        intro h
        simp only [equivAux] at h
        exact absurd h.left gxy
      isFalse this
  termination_by a.length + b.length

instance instEquiv (a b: List Nat) : Decidable (equivAux a b) := decEquivAux a b

end EquivAux

section IsZeroAux

/--
A value of type `List Nat` is considered a representation of _zero_, if is is
equivalent with respect to `equivAux` to the empty list, means means that all elements of
the list must be `0 : Nat`.

This property is independent of the `base` of the respective numeral.
-/
abbrev isZeroAux (a : List Nat) : Prop := equivAux [] a

/--
`[] : List Nat` is itself a representation of _zero_.
-/
theorem isZeroAux_nil : isZeroAux [] := equivAux_refl

theorem ne_nil_of_not_isZeroAux {a : List Nat} (h : ¬ isZeroAux a) : a ≠ [] :=
  match a with
  | [] => absurd isZeroAux_nil h
  | x::xs => List.cons_ne_nil x xs

/--
A non-empty list can only be a representation of _zero_, if its head is `0 : Nat`
and the tail is also a representation of _zero_.
-/
theorem isZeroAux_cons_iff_eq_zero_and_isZeroAux {x : Nat} {xs : List Nat} :
  isZeroAux (x::xs) ↔ x = 0 ∧ isZeroAux xs:= by
  unfold isZeroAux
  rw [equivAux.eq_def]

/--
This lemma is used in the proof of `toNatAux_eq_zero_iff_isZeroAux`.
-/
theorem isZeroAux_of_toNatAux_eq_zero {a : List Nat} {base : Nat} (h: toNatAux a base = 0) (hb : 1 < base) :
  isZeroAux a := by
  induction a with
  | nil =>
    rw [toNatAux] at h
    simp only [isZeroAux, equivAux_refl]
  | cons x xs ih =>
    rw [toNatAux_cons_eq] at h
    have h1 : x = 0 ∧ base * (toNatAux xs base) = 0 := Nat.eq_zero_of_add_eq_zero h
    have h2 : toNatAux xs base = 0 :=
      Or.resolve_left (Nat.zero_eq_mul.mp (Eq.symm h1.right)) (Nat.ne_zero_of_lt hb)
    have h3 : isZeroAux xs := ih h2
    exact isZeroAux_cons_iff_eq_zero_and_isZeroAux.mpr (And.intro h1.left h3)

/--
This lemma is used in the proofs of `toNatAux_eq_zero_iff_isZeroAux`
and `toNatAux_subAux_left_distrib_of_leAux`.

It is inverse implication of `isZeroAux_of_toNatAux_eq_zero`.
-/
theorem toNatAux_eq_zero_of_isZeroAux {a : List Nat} {base : Nat} (h: isZeroAux a) :
  toNatAux a base = 0 := by
  induction a with
  | nil => exact toNatAux_nil_eq
  | cons x xs ih =>
    rw [isZeroAux_cons_iff_eq_zero_and_isZeroAux] at h
    rw [toNatAux_cons_eq]
    have : toNatAux xs base = 0 := ih h.right
    rw [this, h.left, Nat.zero_add, Nat.mul_zero]

/--
This lemma makes it possible to use the `rw`-tactic.
-/
theorem toNatAux_eq_zero_iff_isZeroAux {a : List Nat} {base : Nat} (hb : 1 < base) :
  toNatAux a base = 0 ↔ isZeroAux a := by
  constructor
  · intro h
    exact isZeroAux_of_toNatAux_eq_zero h hb
  · intro h
    exact toNatAux_eq_zero_of_isZeroAux h

def decIsZeroAux (a : List Nat) : Decidable (isZeroAux a) := decEquivAux [] a

instance instIsZero (a : List Nat) : Decidable (isZeroAux a) := decIsZeroAux a

end IsZeroAux

section AllDigitsLtBase

/--
True, if all elements (i.e. _digits_) in a list of natural numbers are all
less than the given `base`.
-/
def allDigitsLtBase (a : List Nat) (base : Nat) : Prop := a.all (· < base)

def decAllDigitsLtBase (a : List Nat) (base : Nat) : Decidable (allDigitsLtBase a base) :=
  match ga : a with
  | [] =>
    have : [].all (· < base) := List.all_nil
    isTrue this
  | x::xs =>
    have h : ¬ x < base ∨ ¬ xs.all (· < base) → ¬ (x::xs).all (· < base) := by
      intro g
      rwa [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, Classical.not_and_iff_not_or_not]
    if hx : x < base then
      if hxs : xs.all (· < base) then
        have : x < base ∧ xs.all (· < base) → (x::xs).all (· < base) := by
          intro g
          rwa [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
        isTrue (this (And.intro hx hxs))
      else
        isFalse (h (.inr hxs))
    else
      isFalse (h (.inl hx))

/-- -/
instance instAllDigitsLtBase (a : List Nat) (base : Nat) : Decidable (allDigitsLtBase a base) :=
  decAllDigitsLtBase a base

/-- -/
theorem allDigitsLtBase_nil {base : Nat}  :
  allDigitsLtBase [] base := by
  rw [allDigitsLtBase.eq_def]
  exact List.all_nil

/-- -/
theorem allDigitsLtBase_cons_iff {x base : Nat} {xs : List Nat} :
  allDigitsLtBase (x::xs) base ↔ x < base ∧ allDigitsLtBase xs base := by
  unfold allDigitsLtBase
  simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]

/-- -/
theorem allDigitsLtBase_singleton {n : Nat} {base : Nat} (hn : n < base) :
  allDigitsLtBase [n] base := by
  exact allDigitsLtBase_cons_iff.mpr (And.intro hn allDigitsLtBase_nil)

end AllDigitsLtBase

section ToNatAux_Equiv

theorem toNatAux_eq_of_equivAux {a b : List Nat} {base : Nat} (h : equivAux a b) (hb : 1 < base) :
  toNatAux a base = toNatAux b base := by
  induction a generalizing b with
  | nil =>
    have : toNatAux b base = 0 ↔ isZeroAux b := toNatAux_eq_zero_iff_isZeroAux hb
    rw [isZeroAux.eq_def, eq_comm] at this
    simp only [toNatAux_nil_eq, this, h]
  | cons x xs ih =>
    match b with
    | [] =>
      have : toNatAux (x::xs) base = 0 ↔ isZeroAux (x::xs) := toNatAux_eq_zero_iff_isZeroAux hb
      rw [isZeroAux.eq_def,  equivAux_iff_equivAux] at this
      simp only [toNatAux_nil_eq, this, h]
    | y::ys =>
      simp only [equivAux] at h
      simp only [toNatAux_cons_eq, h.left, ih h.right]

theorem equivAux_of_toNatAux_eq {a b : List Nat} {base : Nat}
  (h : toNatAux a base = toNatAux b base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) (hb : 1 < base) :
  equivAux a b := by
  induction a generalizing b with
  | nil =>
    have : toNatAux b base = 0 ↔ isZeroAux b := toNatAux_eq_zero_iff_isZeroAux hb
    rw [isZeroAux.eq_def, eq_comm] at this
    rw [toNatAux_nil_eq] at h
    exact this.mp h
  | cons x xs ih =>
    match b with
    | [] =>
      have : toNatAux (x::xs) base = 0 ↔ isZeroAux (x::xs) := toNatAux_eq_zero_iff_isZeroAux hb
      rw [isZeroAux.eq_def,  equivAux_iff_equivAux] at this
      rw [toNatAux_nil_eq] at h
      exact this.mp h
    | y::ys =>
      have halt' : x < base ∧ allDigitsLtBase xs base := allDigitsLtBase_cons_iff.mp halt
      have hblt' : y < base ∧ allDigitsLtBase ys base := allDigitsLtBase_cons_iff.mp hblt
      simp only [toNatAux_cons_eq] at h
      simp only [equivAux]
      have : x = y ∧ toNatAux xs base = toNatAux ys base :=
        (Nat.add_mul_eq_iff_eq_and_eq_of halt'.left hblt'.left).mp h
      exact And.intro this.left (ih this.right halt'.right hblt'.right)

theorem toNatAux_eq_iff_equivAux {a b : List Nat} {base : Nat}
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) (hb : 1 < base) :
  toNatAux a base = toNatAux b base ↔ equivAux a b := by
  constructor
  · intro h
    exact equivAux_of_toNatAux_eq h halt hblt hb
  · intro h
    exact toNatAux_eq_of_equivAux h hb

example {a b : List Nat} {base : Nat} (ha : a = [11]) (hb : b = [1,1]) (hbase : base = 10) :
  toNatAux a base = toNatAux b base ∧ ¬ equivAux a b := by
  have : toNatAux a base = toNatAux b base := by rw [ha, hb, hbase]; decide
  match decEquivAux a b with
  | isFalse q => exact And.intro this q
  | isTrue q =>
    rw [ha, hb] at q
    simp only [equivAux, Nat.succ_ne_self, false_and, and_false] at q

end ToNatAux_Equiv

section NoTrailingZero

/-- -/
def noTrailingZero (a : List Nat) : Prop := (h : a ≠ []) → a.getLast h ≠ 0

/-- -/
def decNoTrailingZero (a : List Nat) : Decidable (noTrailingZero a) :=
  if g1 : a = [] then
    have : noTrailingZero a := by
      rw [noTrailingZero.eq_def]
      intro _
      contradiction
    isTrue this
  else
    if g2 : a.getLast g1 = 0 then
      have : ¬ noTrailingZero a := by
        rw [noTrailingZero.eq_def]
        intro h
        exact absurd g2 (h g1)
      isFalse this
    else
      have : noTrailingZero a := by
        rw [noTrailingZero.eq_def]
        intro _
        exact g2
      isTrue this

/-- -/
instance instNoTrailingZero (a : List Nat) : Decidable (noTrailingZero a) := decNoTrailingZero a

/-- -/
theorem noTrailingZero_nil : noTrailingZero [] := by
  rw [noTrailingZero.eq_def]
  intro hnn
  contradiction

theorem noTrailingZero_singleton_iff_ne_zero {n : Nat} : noTrailingZero [n] ↔ n ≠ 0 := by
  rw [noTrailingZero.eq_def]
  constructor
  · intro h
    have : [n] ≠ [] := List.cons_ne_nil n []
    have : [n].getLast this ≠ 0 := h this
    rwa [List.getLast_singleton] at this
  · intro h _
    rwa [List.getLast_singleton]

/-- -/
theorem noTrailingZero_tail_and_of {x : Nat} {xs : List Nat}
  (h : noTrailingZero (x::xs)) : noTrailingZero xs ∧ (xs = [] → x ≠ 0) := by
  simp only [noTrailingZero] at h ⊢
  have h1 : x :: xs ≠ [] := List.cons_ne_nil x xs
  have h2 : (x :: xs).getLast h1 ≠ 0 := h h1
  if g : xs = [] then
    have h3 : [x].getLast (List.cons_ne_nil x []) ≠ 0 := by
      simp only [g] at h2
      exact h2
    have h4 : [x].getLast (List.cons_ne_nil x []) = x := List.getLast_singleton (List.cons_ne_nil x [])
    have h5 : x ≠ 0 := by rwa [← h4] at h3
    exact And.intro (fun t : xs ≠ [] => absurd g t) (fun _ : xs = [] => h5)
  else
    rw [List.getLast_cons g] at h2
    exact And.intro (fun _ : xs ≠ [] => h2) (fun t : xs = [] => absurd t g)

theorem noTrailingZero_cons_of {x : Nat} {xs : List Nat}
  (h : noTrailingZero xs ∧ (xs = [] → x ≠ 0)) : noTrailingZero (x::xs) := by
  simp only [noTrailingZero] at h ⊢
  intro _
  if g : xs = [] then
    simp only [g, List.getLast_singleton (List.cons_ne_nil x [])]
    exact h.right g
  else
    rw [List.getLast_cons g]
    exact h.left g

/-- -/
theorem noTrailingZero_cons_iff_noTrailingZero_and {x : Nat} {xs : List Nat} :
  noTrailingZero (x::xs) ↔ noTrailingZero xs ∧ (xs = [] → x ≠ 0) := by
  constructor
  · intro h
    exact noTrailingZero_tail_and_of h
  · intro h
    exact noTrailingZero_cons_of h

end NoTrailingZero

section NoTrailingZero_EquivAux

theorem eq_nil_of_noTrailingZero_of_equivAux {a : List Nat}
  (hantz : noTrailingZero a) (hea: equivAux a []) : a = [] := by
  match a with
  | [] => rfl
  | x::xs =>
    have : (x::xs).all (· = 0) := all_eq_zero_of_equivAux_nil hea
    have h : (x::xs).getLast (List.cons_ne_nil x xs) = 0 := by
      rw [← beq_iff_eq]
      exact List.getLast_true_of_all_true_of_ne_nil (x::xs) (· == 0) this (List.cons_ne_nil x xs)
    have h': (x::xs).getLast (List.cons_ne_nil x xs) ≠ 0 := by
      unfold noTrailingZero at hantz
      exact hantz (List.cons_ne_nil x xs)
    exact absurd h h'

theorem eq_of_noTrailingZero_of_equivAux {a b : List Nat}
  (hantz : noTrailingZero a) (hbntz : noTrailingZero b) (habe: equivAux a b) : a = b := by
  induction a generalizing b with
  | nil =>
    have : equivAux b [] := equivAux_symm habe
    exact Eq.symm (eq_nil_of_noTrailingZero_of_equivAux hbntz this)
  | cons x xs ih =>
    match b with
    | [] => exact eq_nil_of_noTrailingZero_of_equivAux hantz habe
    | y::ys =>
      have hxs : noTrailingZero xs := (noTrailingZero_tail_and_of hantz).left
      have hys : noTrailingZero ys := (noTrailingZero_tail_and_of hbntz).left
      have heq : x = y ∧ equivAux xs ys := by
        simp only [equivAux] at habe
        exact habe
      have hes : xs = ys := ih hxs hys heq.right
      have he : x = y := heq.left
      exact List.cons_eq_cons.mpr (And.intro he hes)

theorem eq_iff_equivAux_of_noTrailingZero {a b : List Nat}
  (hantz : noTrailingZero a) (hbntz : noTrailingZero b) :
  a = b ↔ equivAux a b := by
  constructor
  · intro h
    rw [← h]
    exact equivAux_refl
  · intro h
    exact eq_of_noTrailingZero_of_equivAux hantz hbntz h

end NoTrailingZero_EquivAux

section NoTrailingZero_IsZeroAux

theorem isZeroAux_iff_eq_nil_of_noTrailingZero {a : List Nat} (hantz : noTrailingZero a) :
  isZeroAux a ↔ a = [] := by
  constructor
  · intro h
    induction a with
    | nil => rfl
    | cons x xs ih =>
      rw [noTrailingZero_cons_iff_noTrailingZero_and] at hantz
      rw [isZeroAux_cons_iff_eq_zero_and_isZeroAux] at h
      exact absurd h.left (hantz.right (ih hantz.left h.right))
  · intro h
    rw [h]
    exact isZeroAux_nil

end NoTrailingZero_IsZeroAux

section ConsAux

def consAux (n : Nat) (a : List Nat) : List Nat :=
  match n, a with
  | 0, [] => []
  | k + 1, [] => [k + 1]
  | n, x::xs => n::x::xs

theorem consAux_zero_nil_eq : consAux 0 [] = [] := by
  simp only [consAux]

theorem consAux_succ_nil_eq {n : Nat} : consAux (n + 1) [] = [n + 1] := by
  simp only [consAux]

theorem consAux_cons_eq {n x : Nat} {xs : List Nat} : consAux n (x::xs) = n::x::xs := by
  simp only [consAux]

theorem equivAux_consAux_cons {n : Nat} {a : List Nat} :
  equivAux (consAux n a) (n::a) := by
  match gn : n, ga : a with
  | 0, [] => simp only [consAux_zero_nil_eq, equivAux, true_and]
  | k + 1, [] => simp only [consAux_succ_nil_eq, equivAux, true_and]
  | n, x::xs => simp only [consAux, equivAux_refl]

theorem equivAux_consAux_consAux_nil_of_equivAux_nil {n : Nat} {a : List Nat} (h : equivAux a []) :
  equivAux (consAux n a) (consAux n []) := by
  match n, a with
  | _, [] => exact equivAux_refl
  | 0, x::xs =>
    simp only [consAux_cons_eq, consAux_zero_nil_eq]
    exact equivAux_cons_nil_of_equivAux_nil h
  | k + 1, x::xs  =>
    simp only [consAux_cons_eq, consAux_succ_nil_eq]
    exact equivAux_cons_iff_eq_and_equivAux.mpr (And.intro rfl h)

theorem equivAux_consAux_consAux_of_equivAux {n : Nat} {a b : List Nat} (h : equivAux a b) :
  equivAux (consAux n a) (consAux n b) := by
  match n, a, b with
  | _, _, [] => exact equivAux_consAux_consAux_nil_of_equivAux_nil h
  | _, [], _ =>
    rw [equivAux_iff_equivAux] at ⊢ h
    exact equivAux_consAux_consAux_nil_of_equivAux_nil h
  | _, x::xs, y::ys =>
    simp only [equivAux_cons_iff_eq_and_equivAux] at h
    simp only [consAux, equivAux_cons_iff_eq_and_equivAux, true_and]
    assumption

theorem equivAux_consAux_singleton_of_equivAux_nil {n : Nat} {a : List Nat} (h : equivAux a []) :
  equivAux (consAux n a) [n] := by
  match n, a with
  | 0, [] =>
    simp only [consAux_zero_nil_eq]
    exact equivAux_iff_equivAux.mp (equivAux_cons_nil_of_equivAux_nil h)
  | k + 1, [] =>
    simp only [consAux_succ_nil_eq]
    exact equivAux_refl
  | _, x::xs =>
    simp only [consAux_cons_eq]
    exact equivAux_cons_iff_eq_and_equivAux.mpr (And.intro rfl h)

theorem equivAux_consAux_cons_of_equivAux {n : Nat} {a b : List Nat} (h : equivAux a b) :
  equivAux (consAux n a) (n::b) := by
  match n, a, b with
  | _, _, [] => exact equivAux_consAux_singleton_of_equivAux_nil h
  | 0, [], _ =>
    simp only [consAux_zero_nil_eq]
    exact equivAux_iff_equivAux.mp (equivAux_cons_nil_of_equivAux_nil (equivAux_iff_equivAux.mp h))
  | k + 1, [], _ =>
    simp only [consAux_succ_nil_eq]
    exact equivAux_cons_iff_eq_and_equivAux.mpr (And.intro rfl h)
  | _, x::xs, y::ys =>
    simp only [consAux_cons_eq]
    exact equivAux_cons_iff_eq_and_equivAux.mpr (And.intro rfl h)

theorem allDigitsLtBase_consAux_of {n base: Nat} {a : List Nat}
  (hn : n < base) (ha : allDigitsLtBase a base) :
  allDigitsLtBase (consAux n a) base := by
  unfold consAux
  match gn: n, ga: a with
  | 0, [] => simp only; exact allDigitsLtBase_nil
  | k + 1, [] => simp only; exact allDigitsLtBase_singleton hn
  | n, x::xs => simp only; exact allDigitsLtBase_cons_iff.mpr (And.intro hn ha)

theorem noTrailingZero_consAux_of {n : Nat} {a : List Nat} (ha : noTrailingZero a) :
  noTrailingZero (consAux n a) := by
  unfold consAux
  match gn: n, ga: a with
  | 0, [] => simp only; exact noTrailingZero_nil
  | k + 1, [] => simp only; exact noTrailingZero_singleton_iff_ne_zero.mpr (Nat.succ_ne_zero k)
  | n, x::xs =>
    simp only
    have : x::xs = [] → n ≠ 0 := fun t : x::xs = [] => absurd t (List.cons_ne_nil x xs)
    exact noTrailingZero_cons_of (And.intro ha this)

end ConsAux

section DiscardTrailingZeros

def discardTrailingZeros (a : List Nat) :=
  match a with
  | [] => []
  | x::xs => consAux x (discardTrailingZeros xs)

theorem discardTrailingZeros_nil_eq_nil : discardTrailingZeros [] = [] := by
  unfold discardTrailingZeros
  rfl

theorem noTrailingZero_discardTrailingZeros {a : List Nat} :
  noTrailingZero (discardTrailingZeros a) := by
  induction a with
  | nil => simp only [discardTrailingZeros_nil_eq_nil, noTrailingZero_nil]
  | cons x xs ih =>
    unfold discardTrailingZeros
    exact noTrailingZero_consAux_of ih

theorem allDigitsLtBase_discardTrailingZeros {base: Nat} {a : List Nat} (ha : allDigitsLtBase a base) :
  allDigitsLtBase (discardTrailingZeros a) base := by
  induction a with
  | nil => exact allDigitsLtBase_nil
  | cons x xs ih =>
    unfold discardTrailingZeros
    have hx : x < base := (allDigitsLtBase_cons_iff.mp ha).left
    have hxs : allDigitsLtBase (discardTrailingZeros xs) base := ih (allDigitsLtBase_cons_iff.mp ha).right
    exact allDigitsLtBase_consAux_of hx hxs

theorem equivAux_discardTrailingZeros {a : List Nat} : equivAux (discardTrailingZeros a) a := by
  induction a with
  | nil => simp only [discardTrailingZeros, equivAux_refl]
  | cons x xs ih =>
    simp only [discardTrailingZeros]
    exact equivAux_consAux_cons_of_equivAux ih

end DiscardTrailingZeros

section LeAux

def leAux (a b : List Nat) : Prop :=
  match a, b with
  | [], _ => True
  | x::xs, [] => x = 0 ∧ leAux xs []
  | x::xs, y::ys => if equivAux xs ys then x ≤ y else leAux xs ys

def leAux_nil {a : List Nat} : leAux [] a := by simp only [leAux]

theorem leAux_refl {a : List Nat} : leAux a a := by
  match a with
  | [] => simp only [leAux]
  | x::xs => simp only [leAux, equivAux_refl, reduceIte, Nat.le_refl]

theorem leAux_cons_iff {x y : Nat} {xs ys : List Nat} :
  leAux (x::xs) (y::ys) ↔ if equivAux xs ys then x ≤ y else leAux xs ys := by
  rw [leAux.eq_def]

section Equiv_LeAux

theorem not_equivAux_of_leAux_cons_of_ne_le {x y : Nat} {xs ys : List Nat}
  (hl : leAux (x::xs) (y::ys)) (hn : ¬ x ≤ y) : ¬ equivAux xs ys := by
  have : if equivAux xs ys then x ≤ y else leAux xs ys := leAux_cons_iff.mp hl
  false_or_by_contra; rename _ => hc
  simp only [hc, reduceIte] at this
  contradiction

theorem leAux_of_equivAux {a b : List Nat} (h : equivAux a b) : leAux a b := by
  induction a generalizing b with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b with
    | [] =>
      simp only [equivAux] at h
      simp only [leAux]
      exact And.intro h.left (ih h.right)
    | y::ys =>
      simp only [equivAux] at h
      simp only [leAux, h.right, reduceIte, h.left, Nat.le_refl]

theorem equivAux_nil_of_leAux_nil {a : List Nat} (h : leAux a []) : equivAux [] a  := by
  induction a with
  | nil  => exact equivAux_refl
  | cons x xs ih =>
    rw [equivAux.eq_def]
    rw [leAux.eq_def] at h
    simp only at ih h ⊢
    exact And.intro h.left (ih h.right)

theorem leAux_nil_iff_equivAux_nil {a : List Nat} : leAux a [] ↔ equivAux [] a := by
  constructor
  · intro h
    exact equivAux_nil_of_leAux_nil h
  · intro h
    exact leAux_of_equivAux (equivAux_symm h)

end Equiv_LeAux

/--
`leAux` is _almost_ antisymmetric
-/
theorem equivAux_iff_leAux_and_leAux {a b : List Nat}:
  equivAux a b ↔ leAux a b ∧ leAux b a := by
  constructor
  · intro h
    have h1 : leAux a b := leAux_of_equivAux h
    have h2 : leAux b a := leAux_of_equivAux (equivAux_symm h)
    exact And.intro h1 h2
  · intro h
    induction a generalizing b with
    | nil =>
      unfold leAux at h
      match b with
      | [] => exact equivAux_refl
      | x::xs =>
        rw [equivAux.eq_def]
        simp only [true_and] at ⊢ h
        exact And.intro h.left (equivAux_nil_of_leAux_nil h.right)
    | cons x xs ih =>
      match b with
      | [] =>
        have : equivAux [] (x :: xs) := equivAux_nil_of_leAux_nil h.left
        exact equivAux_symm this
      | y::ys =>
        unfold leAux at h
        unfold equivAux
        if g : equivAux xs ys then
          simp only [g, equivAux_symm, reduceIte] at h
          simp only [Nat.le_antisymm h.left h.right, g, true_and]
        else
          have : ¬ equivAux ys xs := not_equivAux_iff_not_equivAux.mp g
          simp only [g, reduceIte, this] at h
          have : equivAux xs ys := ih h
          contradiction

theorem leAux_total {a b : List Nat} : leAux a b ∨ leAux b a := by
  induction a generalizing b with
  | nil => exact .inl (leAux_nil)
  | cons x xs ih =>
    match b with
    | [] => exact .inr (leAux_nil)
    | y::ys =>
      if g1 : equivAux xs ys then
        if g2 : x ≤ y then
          have : leAux (x::xs) (y::ys) := by simp only [leAux, g1, g2, reduceIte]
          exact .inl this
        else
          have h1 : equivAux ys xs := equivAux_symm g1
          have h2 : y ≤ x := Nat.le_of_not_le g2
          have : leAux (y::ys) (x::xs) := by simp only [leAux, h1, h2, reduceIte]
          exact .inr this
      else
        have g2 : ¬ equivAux ys xs := not_equivAux_iff_not_equivAux.mp g1
        simp only [leAux, g1, g2, reduceIte]
        exact ih

section LeAux_Equiv

theorem leAux_of_leAux_of_equivAux {a b c : List Nat} (hab : leAux a b) (hbc : equivAux b c): leAux a c := by
  induction a generalizing b c with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b, c with
    | [], [] => simp_all only
    | y::ys, [] =>
      unfold leAux at hab ⊢
      unfold equivAux at hbc
      if g : equivAux xs ys then
        simp only [g, reduceIte, hbc.left] at hab
        have h1 : x = 0 := Nat.eq_zero_of_le_zero hab
        have h2 : leAux xs ys := leAux_of_equivAux g
        have h3 : leAux xs [] := ih  h2 hbc.right
        exact And.intro h1 h3
      else
        simp only [g, reduceIte, hbc.left] at hab
        have h1 : leAux xs [] := ih hab hbc.right
        have h2 : equivAux xs [] := equivAux_symm (equivAux_nil_of_leAux_nil h1)
        have h3 : equivAux xs ys := equivAux_trans h2 (equivAux_symm hbc.right)
        contradiction
    | [], z::zs =>
      have : equivAux (x :: xs) [] := equivAux_symm (equivAux_nil_of_leAux_nil hab)
      have : equivAux (x :: xs) (z :: zs) := equivAux_trans this hbc
      exact leAux_of_equivAux this
    | y::ys, z::zs =>
      unfold leAux at hab ⊢
      unfold equivAux at hbc
      if g1 : equivAux xs ys then
        simp only [g1, reduceIte, hbc.left] at hab
        if g2 : equivAux xs zs then
          simp only [g2, reduceIte]
          exact hab
        else
          simp only [g2, reduceIte]
          have : equivAux xs zs := equivAux_trans g1 hbc.right
          contradiction
      else
        simp only [g1, reduceIte] at hab
        if g2 : equivAux xs zs then
          simp only [g2, reduceIte]
          have : equivAux xs ys := equivAux_trans g2 (equivAux_symm hbc.right)
          contradiction
        else
          simp only [g2, reduceIte]
          exact ih hab hbc.right

theorem leAux_of_equivAux_of_leAux {a b c : List Nat} (hab : equivAux a b) (hbc : leAux b c): leAux a c := by
  induction a generalizing b c with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b, c with
    | [], [] =>
      simp only [equivAux] at hab
      simp only [leAux, And.intro hab.left (ih hab.right hbc), and_true]
    | y::ys, [] =>
      simp only [equivAux] at hab
      simp only [leAux] at hbc ⊢
      simp only [hab.left, hbc.left, true_and, (ih hab.right hbc.right)]
    | [], z::zs =>
      simp only [equivAux] at hab
      simp only [leAux] at hbc ⊢
      if h : equivAux xs zs then
        simp only [h, reduceIte, hab.left, Nat.zero_le]
      else
        simp only [h, reduceIte]
        have : leAux [] zs := leAux_nil
        exact ih hab.right this
    | y::ys, z::zs =>
      simp only [equivAux] at hab
      simp only [leAux] at hbc
      if h : equivAux ys zs then
        simp only [h, reduceIte] at hbc
        simp only [leAux, equivAux_trans hab.right h, reduceIte]
        rwa [hab.left]
      else
        simp only [h, reduceIte] at hbc
        have : ¬ equivAux xs zs := not_equivAux_of_equivAux_of_not_equivAux hab.right h
        simp only [leAux, this, reduceIte, ih hab.right hbc]

theorem equivAux_and_equivAux_of_leAux_of_leAux_of_equivAux {a b c : List Nat}
  (hab : leAux a b) (hbc : leAux b c) (hac : equivAux a c) : equivAux a b ∧ equivAux b c := by
  have h1 : leAux b a := leAux_of_leAux_of_equivAux hbc (equivAux_symm hac)
  have h2 : equivAux a b := equivAux_iff_leAux_and_leAux.mpr (And.intro hab h1)
  have h3 : leAux c b := leAux_of_equivAux_of_leAux (equivAux_symm hac) hab
  have h4 : equivAux b c := equivAux_iff_leAux_and_leAux.mpr (And.intro hbc h3)
  exact And.intro h2 h4

end LeAux_Equiv

section ToNatAux_LeAux

theorem toNatAux_le_of_leAux {a b : List Nat} {base : Nat} (h : leAux a b) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  toNatAux a base ≤ toNatAux b base := by
  induction a generalizing b with
  | nil => simp only [toNatAux_nil_eq, Nat.zero_le]
  | cons x xs ih =>
    match b with
    | [] =>
      have : isZeroAux (x::xs) := equivAux_nil_of_leAux_nil h
      have : toNatAux (x :: xs) base = 0 := (toNatAux_eq_zero_iff_isZeroAux hb).mpr this
      simp only [this, Nat.zero_le]
    | y::ys =>
      simp only [leAux_cons_iff] at h
      simp only [toNatAux_cons_eq]
      if g : equivAux xs ys then
        simp only [g, reduceIte] at h
        simp only [toNatAux_eq_of_equivAux g hb, Nat.add_le_add_right h (base * toNatAux ys base)]
      else
        simp only [g, reduceIte] at h
        have h1 : x < base ∧ xs.all (· < base) := allDigitsLtBase_cons_iff.mp halt
        have h2 : y < base ∧ ys.all (· < base) := allDigitsLtBase_cons_iff.mp hblt
        have h3 : toNatAux xs base ≤ toNatAux ys base := ih h h1.right h2.right
        have h4 : toNatAux xs base ≠ toNatAux ys base :=
          (Classical.iff_iff_not_iff_not.mp (toNatAux_eq_iff_equivAux h1.right h2.right hb)).mpr g
        have h3 : toNatAux xs base < toNatAux ys base := Nat.lt_of_le_of_ne h3 h4
        exact Nat.le_of_lt (Nat.add_mul_lt_of_lt_of_lt h3 h1.left)

theorem leAux_of_toNatAux_le_toNatAux_of {a b : List Nat} {base : Nat}
  (h : toNatAux a base ≤ toNatAux b base) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) : leAux a b := by
  induction a generalizing b with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b with
    | [] =>
      have : toNatAux [] base = 0 := toNatAux_nil_eq
      simp only [toNatAux_nil_eq, Nat.le_zero, toNatAux_eq_zero_iff_isZeroAux hb, isZeroAux, equivAux_iff_equivAux] at h
      exact leAux_of_equivAux h
    | y::ys =>
      simp only [toNatAux_cons_eq] at h
      simp only [leAux]
      if g : equivAux xs ys then
        simp only [g, reduceIte]
        rw [toNatAux_eq_of_equivAux g hb] at h
        exact Nat.le_of_add_le_add_right h
      else
        have halt' : x < base ∧ xs.all (· < base) := allDigitsLtBase_cons_iff.mp halt
        have hblt' : y < base ∧ ys.all (· < base) := allDigitsLtBase_cons_iff.mp hblt
        simp only [g, reduceIte]
        have : toNatAux xs base ≠ toNatAux ys base := by
          false_or_by_contra; rename _ => hc
          exact absurd (equivAux_of_toNatAux_eq hc halt'.right hblt'.right hb) g
        have : toNatAux xs base ≤ toNatAux ys base :=
          (Nat.add_mul_le_iff_le_of this halt'.left hblt'.left).mp h
        exact ih this halt'.right hblt'.right

theorem leAux_iff_toNatAux_le_toNatAux {a b : List Nat} {base : Nat} (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  leAux a b ↔ (toNatAux a base) ≤ (toNatAux b base) := by
  constructor
  · intro h
    exact toNatAux_le_of_leAux h hb halt hblt
  · intro h
    exact leAux_of_toNatAux_le_toNatAux_of h hb halt hblt

end ToNatAux_LeAux

theorem leAux_trans {a b c : List Nat} (hab : leAux a b) (hbc : leAux b c) : leAux a c := by
  induction a generalizing b c with
  | nil => exact leAux_nil
  | cons x xs ihx =>
    match b, c with
    | [], [] => unfold leAux at hab ⊢; simp_all only [and_true]
    | y::ys, [] =>
      have : equivAux (y::ys) [] := equivAux_symm (equivAux_nil_of_leAux_nil hbc)
      exact leAux_of_leAux_of_equivAux hab this
    | [], z::zs =>
      have : equivAux (x::xs) [] := equivAux_symm (equivAux_nil_of_leAux_nil hab)
      exact leAux_of_equivAux_of_leAux this hbc
    | y::ys, z::zs =>
      unfold leAux at hab hbc ⊢
      if gxy : equivAux xs ys then
        if gyz : equivAux ys zs then
          have : equivAux xs zs := equivAux_trans gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact Nat.le_trans hab hbc
        else
          have : ¬ equivAux xs zs := not_equivAux_of_equivAux_of_not_equivAux gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact ihx (leAux_of_equivAux gxy) hbc
      else
        if gyz : equivAux ys zs then
          have : ¬ equivAux xs zs := not_equivAux_of_not_equivAux_of_equivAux gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact ihx hab (leAux_of_equivAux gyz)
        else
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          have : ¬ equivAux xs zs := by
            false_or_by_contra; rename _ => hc
            exact absurd (equivAux_and_equivAux_of_leAux_of_leAux_of_equivAux hab hbc hc).left gxy
          simp only [this, reduceIte]
          exact ihx hab hbc

def decLeAux (a b : List Nat) : Decidable (leAux a b) :=
  match a, b with
  | [], [] =>
    have : leAux [] [] := leAux_refl
    isTrue this
  | x::xs, [] =>
    if g : x = 0 then
      match decLeAux xs [] with
      | isFalse p =>
        have : ¬ leAux (x::xs) [] := by
          simp only [leAux, not_and]
          intro _
          exact p
        isFalse this
      | isTrue p =>
        have : leAux (x::xs) [] := by
          simp only [leAux, g, p, true_and]
        isTrue this
    else
      have : ¬ leAux (x::xs) [] := by
        simp only [leAux, not_and]
        intro _
        contradiction
      isFalse this
  | [], y::ys =>
    have : leAux [] (y::ys) := by simp only [leAux]
    isTrue this
  | x::xs, y::ys =>
    match decEquivAux xs ys with
    | isFalse p =>
      match decLeAux xs ys with
      | isFalse q =>
        have : ¬ leAux (x::xs) (y::ys) := by
          simp only [leAux, p, reduceIte, q, not_false_eq_true]
        isFalse this
      | isTrue q =>
        have : leAux (x::xs) (y::ys) := by
          simp only [leAux, p, reduceIte, q]
        isTrue this
    | isTrue p =>
      if g : x ≤ y then
        have : leAux (x::xs) (y::ys) := by
          simp only [leAux, p, reduceIte, g]
        isTrue this
      else
        have : ¬ leAux (x::xs) (y::ys) := by
          simp only [leAux, p, reduceIte, g, not_false_eq_true]
        isFalse this

instance instLeAux (a b : List Nat) : Decidable (leAux a b) := decLeAux a b

end LeAux

section LtAux

def ltAux (a b : List Nat) : Prop :=
  match a, b with
  | _, [] => False
  | [], y::ys => 0 < y ∨ ltAux [] ys
  | x::xs, y::ys => x < y ∧ ¬ ltAux ys xs ∨ ltAux xs ys
  termination_by a.length + b.length

theorem not_ltAux_cons_nil {x : Nat} {xs : List Nat} : ¬ ltAux (x::xs) [] := by
  simp only [ltAux, not_false_eq_true]

theorem ltAux_irrefl {a : List Nat} : ¬ ltAux a a  := by
  induction a with
  | nil => simp only [ltAux, not_false_eq_true]
  | cons x xs ih =>
    rw [ltAux.eq_def]
    match ga: x::xs, gb : x::xs with
    | _, [] => simp only [not_false_eq_true]
    | [], v::vs => rw [← gb]; simp only [not_or, ih, not_false_eq_true, and_true, Nat.lt_irrefl]
    | u::us, v::vs =>
      have : xs = vs := (List.cons.inj gb).right
      intro h
      simp only [← this, Nat.lt_irrefl, false_and, false_or] at h
      contradiction

theorem lt_of {x y : Nat} {xs ys : List Nat}
  (ha : x < y ∧ ¬ltAux ys xs ∨ ltAux xs ys) (hbl : y < x ∧ ¬ltAux xs ys) : x < y := by
  have : ¬ltAux xs ys := hbl.right
  have : x < y ∧ ¬ltAux ys xs := Or.resolve_right ha this
  exact this.left

theorem not_ltAux_of {x y : Nat} {xs ys : List Nat} (ha : x < y ∧ ¬ltAux ys xs ∨ ltAux xs ys)
  (ih: ∀ {b : List Nat}, ltAux xs b → ¬ ltAux b xs) (hbr : ltAux ys xs) : ¬ ltAux ys xs := by
  have : ¬ ltAux xs ys := by
    intro h
    exact absurd hbr (ih h)
  have : x < y ∧ ¬ltAux ys xs := Or.resolve_right ha this
  exact this.right

theorem ltAux_asymm {a b : List Nat} (ha : ltAux a b) : ¬ ltAux b a := by
  induction a generalizing b with
  | nil => simp only [ltAux, not_false_eq_true]
  | cons x xs ih =>
    match b with
    | [] => simp only [ltAux] at ⊢ ha
    | y::ys =>
      intro hb
      simp only [ltAux] at ha hb
      cases hb with
      | inl hbl => exact absurd (lt_of ha hbl) (Nat.not_lt_of_lt hbl.left)
      | inr hbr => exact absurd hbr (not_ltAux_of ha ih hbr)

theorem ltAux_nil_of_ltAux {a b : List Nat} (h : ltAux a b) : ltAux [] b := by
  induction a generalizing b with
  | nil => assumption
  | cons x xs ih =>
    rw [ltAux.eq_def] at ⊢ h
    match gb : b with
    | [] => simp only at ⊢ h
    | y::ys =>
      simp only at ⊢ h
      cases h with
      | inl hl =>
        have : 0 < y := Nat.zero_lt_of_lt hl.left
        exact .inl this
      | inr hr =>
        have : ltAux [] ys := ih hr
        exact .inr this

theorem ltAux_nil_iff_ltAux_zero {a : List Nat} : ltAux [] a ↔ ltAux [0] a:= by
  constructor <;>
  · intro h
    match a with
    | [] => simp only [ltAux] at h
    | x::xs => simp only [ltAux, not_false_eq_true, and_true] at ⊢ h; exact h

theorem ltAux_of_ltAux_cons {x : Nat} {xs ys : List Nat} (h : ltAux (x::xs) (x::ys)) : ltAux xs ys := by
  unfold ltAux at h
  have : ¬ (x < x ∧ ¬ltAux ys xs) := by
    simp only [not_and, Nat.lt_irrefl x]
    intro
    contradiction
  exact Or.resolve_left h this

section Equiv_LtAux

theorem not_equivAux_nil_of_ltAux_nil {a : List Nat} (h : ltAux [] a) : ¬ equivAux [] a := by
  induction a with
  | nil =>
    have : ¬ ltAux [] [] := ltAux_irrefl
    contradiction
  | cons y ys ih =>
    simp only [ltAux] at h
    have : ¬ y = 0 ↔ 0 < y := by
      constructor
      · intro hl
        rw [← ne_eq] at hl
        exact Nat.pos_of_ne_zero hl
      · intro hr
        have : y ≠ 0 := Nat.ne_zero_of_lt hr
        rwa [ne_eq y 0] at this
    simp only [equivAux, Classical.not_and_iff_not_or_not, this]
    cases h with
    | inl hl => exact .inl hl
    | inr hr => exact .inr (ih hr)

theorem not_equivAux_of_ltAux {a b : List Nat} (h : ltAux a b) : ¬ equivAux a b := by
  induction a generalizing b with
  | nil => exact not_equivAux_nil_of_ltAux_nil h
  | cons x xs ih =>
    match b with
    | [] => rw [ltAux.eq_def] at h; contradiction
    | y::ys =>
      simp only [ltAux] at h
      simp only [equivAux, Classical.not_and_iff_not_or_not]
      cases h with
      | inl hl => exact .inl (Nat.ne_of_lt hl.left)
      | inr hr => exact .inr (ih hr)

theorem not_ltAux_nil_of_equivAux_nil {a : List Nat} (h : equivAux [] a) : ¬ ltAux [] a := by
  induction a with
  | nil => exact ltAux_irrefl
  | cons y ys ih =>
    unfold equivAux at h
    simp only [ltAux, not_or, Nat.not_lt, Nat.le_zero]
    exact And.intro h.left (ih h.right)

theorem not_ltAux_of_equivAux {a b : List Nat} (h : equivAux a b) : ¬ ltAux a b := by
  induction a generalizing b with
  | nil => exact not_ltAux_nil_of_equivAux_nil h
  | cons x xs ih =>
    match b with
    | [] => simp only [ltAux, not_false_eq_true]
    | y::ys =>
      simp only [equivAux] at h
      simp only [ltAux, not_or, Classical.not_and_iff_not_or_not, Classical.not_not]
      have : ¬ x < y := by rw [h.left]; exact Nat.lt_irrefl y
      exact And.intro (.inl this) (ih h.right)

theorem ltAux_nil_of_not_equivAux_nil_of_not_ltAux_nil {a : List Nat}
  (h1 : ¬ equivAux [] a) (h2 : ¬ ltAux a []) : ltAux [] a := by
  induction a with
  | nil => unfold equivAux at h1; simp only [not_true] at h1
  | cons x xs ih =>
    unfold equivAux at h1
    simp only [Classical.not_and_iff_not_or_not] at h1
    unfold ltAux
    cases h1 with
    | inl h1l =>
      have : 0 < x := Nat.zero_lt_of_ne_zero h1l
      exact .inl this
    | inr h1r =>
      have : ¬ ltAux xs [] := by simp only [ltAux, not_false_eq_true]
      exact .inr (ih h1r this)

theorem ltAux_of_not_equivAux_of_not_ltAux {a b : List Nat}
  (h1 : ¬ equivAux a b) (h2 : ¬ ltAux b a) : ltAux a b := by
  induction a generalizing b with
  | nil => exact ltAux_nil_of_not_equivAux_nil_of_not_ltAux_nil h1 h2
  | cons x xs ihx =>
    unfold equivAux at h1
    match b with
    | [] =>
      simp only [Classical.not_and_iff_not_or_not] at h1
      unfold ltAux at ⊢ h2
      simp only [not_or, Nat.not_lt, Nat.le_zero_eq] at h1 h2
      have : ¬¬x = 0 := not_not_intro h2.left
      have : ¬equivAux xs [] := Or.resolve_left h1 this
      have : ltAux xs [] := ihx this h2.right
      have : False := by simp only [ltAux] at this
      contradiction
    | y::ys =>
      simp only [Classical.not_and_iff_not_or_not] at h1
      unfold ltAux at ⊢ h2
      simp_all only [not_or, not_and, Classical.not_not, not_false_eq_true, and_true]
      if g : x < y then
        exact .inl g
      else
        cases h1 with
        | inl h1l =>
          have h1l' : ¬y = x := by rwa [← ne_eq, ne_comm, ne_eq] at h1l
          have : y ≤ x := Nat.le_of_not_lt g
          have : y < x := Nat.lt_of_le_of_ne this h1l'
          exact .inr (h2.left this)
        | inr h1r => exact .inr (ihx h1r h2.right)

theorem equivAux_of_not_ltAux_and_not_ltAux {a b : List Nat} (h : ¬ ltAux a b ∧ ¬ ltAux b a) : equivAux a b := by
  false_or_by_contra; rename _ => hc
  exact absurd (ltAux_of_not_equivAux_of_not_ltAux hc h.right) h.left

end Equiv_LtAux

section LeAux_LtAux

theorem leAux_of_ltAux {a b : List Nat} (h : ltAux a b) : leAux a b := by
  induction a generalizing b with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b with
    | [] => exact absurd h (not_ltAux_cons_nil)
    | y::ys =>
      simp only [ltAux] at h
      simp only [leAux]
      if g : ltAux xs ys then
        have : ¬ equivAux xs ys := not_equivAux_of_ltAux g
        simp only [this, reduceIte, ih g]
      else
        have h1 : x < y ∧ ¬ltAux ys xs := Or.resolve_right h g
        have h2 : equivAux xs ys := equivAux_of_not_ltAux_and_not_ltAux (And.intro g h1.right)
        simp only [h2, reduceIte, Nat.le_of_lt h1.left]

theorem leAux_iff_not_ltAux {a b : List Nat} : leAux a b ↔ ¬ ltAux b a := by
  induction a generalizing b with
  | nil => unfold leAux ltAux; simp only [not_false_eq_true]
  | cons x xs ih =>
    unfold leAux ltAux
    match b with
    | [] =>
      have : x = 0 ↔ x ≤ 0 := by
        constructor
        · intro h
          simp only [h, Nat.le_refl]
        · intro h
          exact Nat.eq_zero_of_le_zero h
      simp only [not_or, Nat.not_lt, this, ih]
    | y::ys =>
      simp only [not_or, Classical.not_and_iff_not_or_not, Classical.not_not, Nat.not_lt, ih]
      constructor
      · intro h
        if g : equivAux xs ys then
          simp [g] at h
          have : ¬ltAux ys xs := ih.mp (leAux_of_equivAux g)
          exact And.intro (.inl h) this
        else
          simp [g] at h
          have : ltAux xs ys := ltAux_of_not_equivAux_of_not_ltAux g h
          exact And.intro (.inr this) h
      · intro h
        if g : ltAux xs ys then
          have : ¬ equivAux xs ys := not_equivAux_of_ltAux g
          simp only [this, reduceIte, h.right, not_false_eq_true]
        else
          have : equivAux xs ys := equivAux_of_not_ltAux_and_not_ltAux (And.intro g h.right)
          simp only [this, reduceIte]
          exact Or.resolve_right h.left g

theorem ltAux_iff_leAux_and_not_equivAux {a b : List Nat} : ltAux a b ↔ leAux a b ∧ ¬ equivAux a b := by
  constructor
  · intro h
    exact And.intro (leAux_of_ltAux h) (not_equivAux_of_ltAux h)
  · intro h
    have : ¬ ltAux b a := leAux_iff_not_ltAux.mp h.left
    exact ltAux_of_not_equivAux_of_not_ltAux h.right this

theorem ltAux_of_ltAux_of_leAux {a b c : List Nat} (hab : ltAux a b) (hbc : leAux b c) : ltAux a c := by
  have h1 : leAux a c := leAux_trans (leAux_of_ltAux hab) hbc
  have h2 : equivAux a c → equivAux a b ∧ equivAux b c := by
    intro h
    exact equivAux_and_equivAux_of_leAux_of_leAux_of_equivAux (leAux_of_ltAux hab) hbc h
  have h3 : equivAux a c → ¬ ltAux a b := by
    intro h
    exact not_ltAux_of_equivAux (h2 h).left
  have h4 : ¬ equivAux a c := fun h : equivAux a c => absurd hab (h3 h)
  exact ltAux_iff_leAux_and_not_equivAux.mpr (And.intro h1 h4)

theorem ltAux_of_leAux_of_ltAux {a b c : List Nat} (hab : leAux a b) (hbc : ltAux b c) : ltAux a c := by
  have h1 : leAux a c := leAux_trans hab (leAux_of_ltAux hbc)
  have h2 : equivAux a c → equivAux a b ∧ equivAux b c := by
    intro h
    exact equivAux_and_equivAux_of_leAux_of_leAux_of_equivAux hab (leAux_of_ltAux hbc) h
  have h3 : equivAux a c → ¬ ltAux b c := by
    intro h
    exact not_ltAux_of_equivAux (h2 h).right
  have h4 : ¬ equivAux a c := fun h : equivAux a c => absurd hbc (h3 h)
  exact ltAux_iff_leAux_and_not_equivAux.mpr (And.intro h1 h4)

end LeAux_LtAux

theorem ltAux_trans {a b c : List Nat} (hab : ltAux a b) (hbc : ltAux b c) : ltAux a c := by
  induction a generalizing b c with
  | nil => exact ltAux_nil_of_ltAux hbc
  | cons x xs ihx =>
    unfold ltAux at hab hbc ⊢
    match b, c with
    | [], [] | y::ys, [] | [], z::zs => simp_all only
    | y::ys, z::zs =>
      simp only at hab hbc ⊢
      rw [← leAux_iff_not_ltAux] at hab hbc ⊢
      if gxy : ltAux xs ys then
        if gyz : ltAux ys zs then
          exact .inr (ihx gxy gyz)
        else
          simp only [gyz, or_false] at hbc
          exact .inr (ltAux_of_ltAux_of_leAux gxy hbc.right)
      else
        if gyz : ltAux ys zs then
          simp only [gxy, or_false] at hab
          exact .inr (ltAux_of_leAux_of_ltAux hab.right gyz)
        else
          simp only [gxy, gyz, or_false] at hab hbc
          exact .inl (And.intro (Nat.lt_trans hab.left hbc.left) (leAux_trans hab.right hbc.right))

def decLtAux (a b : List Nat) : Decidable (ltAux a b) :=
  match ga : a, gb : b with
  | x, [] =>
    have : ¬ ltAux x [] := by rw [ltAux.eq_def]; simp only [not_false_eq_true]
    isFalse this
  | [], y::ys =>
    if g : 0 < y then
      have : ltAux [] (y::ys) := by
        rw [ltAux.eq_def]
        simp only [g, true_or]
      isTrue this
    else
      match decLtAux [] ys with
      | isFalse p =>
        have : ¬ ltAux [] (y::ys) := by
          rw [ltAux.eq_def]
          simp only [g, p, false_or, not_false_eq_true]
        isFalse this
      | isTrue p =>
        have : ltAux [] (y::ys) := by
          rw [ltAux.eq_def]
          simp only [g, p, false_or]
        isTrue this
  | x::xs, y::ys =>
    if gxy : x < y then
      match gxsys : decLtAux ys xs with
      | isFalse p =>
        have : ltAux (x::xs) (y::ys) := by
          rw [ltAux.eq_def]
          simp only [gxy, p, not_false_eq_true, true_and, true_or]
        isTrue this
      | isTrue p =>
        have : ¬ ltAux (x::xs) (y::ys) := by
          rw [ltAux.eq_def]
          simp only [gxy, p, not_true_eq_false, and_false, false_or]
          exact ltAux_asymm p
        isFalse this
    else
      match decLtAux xs ys with
      | isFalse p =>
        have : ¬ ltAux (x::xs) (y::ys) := by
          rw [ltAux.eq_def]
          simp only [gxy, false_and, false_or, p, not_false_eq_true]
        isFalse this
      | isTrue p =>
        have : ltAux (x::xs) (y::ys) := by
          rw [ltAux.eq_def]
          simp only [gxy, false_and, false_or, p]
        isTrue this
  termination_by a.length + b.length

instance instLtAux (a b : List Nat) : Decidable (ltAux a b) := decLtAux a b

end LtAux

section ToNatAux_LtAux

theorem toNatAux_lt_toNatAux_of_ltAux {a b : List Nat} {base : Nat} (h : ltAux a b) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  toNatAux a base < toNatAux b base := by
  have h1 : toNatAux a base ≤ toNatAux b base := toNatAux_le_of_leAux (leAux_of_ltAux h) hb halt hblt
  have h2 : ¬ equivAux a b := not_equivAux_of_ltAux h
  have h3 : toNatAux a base = toNatAux b base ↔ equivAux a b := toNatAux_eq_iff_equivAux halt hblt hb
  have h4 : ¬ toNatAux a base = toNatAux b base := (Classical.iff_iff_not_iff_not.mp h3).mpr h2
  exact Nat.lt_of_le_of_ne h1 h4

theorem ltAux_of_toNatAux_lt_toNatAux {a b : List Nat} {base : Nat}
  (h : toNatAux a base < toNatAux b base) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  ltAux a b := by
  have h1 : toNatAux a base ≤ toNatAux b base := Nat.le_of_lt h
  have h2 : ¬ toNatAux a base = toNatAux b base := Nat.ne_of_lt h
  have h3 : toNatAux a base = toNatAux b base ↔ equivAux a b := toNatAux_eq_iff_equivAux halt hblt hb
  have h4 : ¬ equivAux a b := (Classical.iff_iff_not_iff_not.mp h3).mp h2
  exact ltAux_iff_leAux_and_not_equivAux.mpr (And.intro (leAux_of_toNatAux_le_toNatAux_of h1 hb halt hblt) h4)

theorem ltAux_iff_toNatAux_lt_toNtAux {a b : List Nat} {base : Nat} (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  ltAux a b ↔ toNatAux a base < toNatAux b base := by
  constructor
  · intro h
    exact toNatAux_lt_toNatAux_of_ltAux h hb halt hblt
  · intro h
    exact ltAux_of_toNatAux_lt_toNatAux h hb halt hblt

end ToNatAux_LtAux

section Prune

/-- -/
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

/-- -/
theorem prune_eq_nil_of_eq_nil_of_eq_zero {a : List Nat} {n base : Nat}
  (ha : a = []) (hn : n = 0) (hb : 1 < base) :
  prune a n base hb = [] := by
  rw [prune.eq_def]
  match a, n with | [], 0 => simp only

/-- -/
theorem prune_eq_nil_iff_eq_nil_and_eq_zero {a : List Nat} {n base : Nat}  (hb : 1 < base) :
  prune a n base hb = [] ↔ a = [] ∧ n = 0 := by
  constructor
  · intro h
    rw [prune.eq_def] at h
    match ga : a, gn : n with | [], 0 => exact And.intro rfl rfl
  · intro h
    exact prune_eq_nil_of_eq_nil_of_eq_zero h.left h.right hb

theorem prune_nil_eq_cons_of_pos {n base : Nat} (hn : 0 < n) (hb : 1 < base) :
  prune [] n base hb = (n % base)::(prune [] (n / base) base hb) := by
  match n with | 0 => contradiction | k + 1 => rw [prune.eq_def]

end Prune

section AllDigitsLtBase_Prune

/-- -/
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

/-- -/
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

section OfNatAux

abbrev ofNatAux (n : Nat) (base : Nat) (hb : 1 < base) := prune [] n base hb

theorem isZeroAux_ofNatAux_iff_eq_zero {n base : Nat} (hb : 1 < base) :
  isZeroAux (ofNatAux n base hb) ↔ n = 0 := by
  constructor
  · intro h
    simp only [ofNatAux] at h
    have h1 : noTrailingZero (prune [] n base hb) := noTrailingZero_prune_nil
    have h2 : (prune [] n base hb) = [] := (isZeroAux_iff_eq_nil_of_noTrailingZero h1).mp h
    exact ((prune_eq_nil_iff_eq_nil_and_eq_zero hb).mp h2).right
  · intro h
    simp only [h, ofNatAux, prune, isZeroAux, equivAux]

end OfNatAux

section AddDigits

/-- -/
def addDigits : List Nat → List Nat → List Nat
  | [], [] => []
  | x::xs, [] => x::xs
  | [], y::ys => y::ys
  | x::xs, y::ys => (x + y)::(addDigits xs ys)

theorem addDigits_nil_eq {a : List Nat} : addDigits a [] = a := by
  rw [addDigits.eq_def]
  match ha : a with
  | [] | x::xs => rfl

/-- -/
theorem addDigits_eq_nil_iff_eq_nil_and_eq_nil {a b : List Nat} :
  addDigits a b = [] ↔ a = [] ∧ b = [] := by
  constructor
  · intro h
    match ga : a, gb : b with
    | [], [] => exact And.intro rfl rfl
    | x::xs, [] | [], y::ys | x::xs, y::ys => contradiction
  . intro h
    match a, b with | [], [] => rfl

theorem addDigits_cons_cons_eq_add_cons_addDigits {x y : Nat} {xs ys : List Nat} :
  addDigits (x::xs) (y::ys) = (x + y)::addDigits xs ys := rfl

/-- -/
theorem addDigits_comm {a b : List Nat} : addDigits a b = addDigits b a := by
  induction a generalizing b with
  | nil => match b with | [] | v::vs => rfl
  | cons u us iha =>
    match b with
    | [] => rfl
    | v::vs  =>
      unfold addDigits
      rw [List.cons.injEq, Nat.add_comm u v]
      exact And.intro rfl iha

end AddDigits

section NoTrailingZero_AddDigits

/-- -/
theorem noTrailingZero_addDigits_of {a b : List Nat}
  (hantz : noTrailingZero a) (hbntz : noTrailingZero b) :
  noTrailingZero (addDigits a b) := by
  induction a generalizing b with
  | nil =>
    match b with
    | [] => intro _ ; contradiction
    | y::ys =>
      simp only [addDigits_comm, addDigits_nil_eq]
      exact hbntz
  | cons x xs ih =>
    match b with
    | [] => simp only [addDigits_nil_eq]; exact hantz
    | y::ys =>
      rw [noTrailingZero_cons_iff_noTrailingZero_and] at hantz hbntz
      have : noTrailingZero (addDigits xs ys) := ih hantz.left hbntz.left
      simp only [addDigits_cons_cons_eq_add_cons_addDigits, noTrailingZero_cons_iff_noTrailingZero_and]
      simp only [this, true_and, addDigits_eq_nil_iff_eq_nil_and_eq_nil]
      intro h
      have h1 : 0 < x := Nat.pos_iff_ne_zero.mpr (hantz.right h.left)
      have h2 : 0 < x + y := Nat.add_pos_left h1 y
      exact Nat.pos_iff_ne_zero.mp h2

end NoTrailingZero_AddDigits

section ToNatAux_AddDigits

/-- -/
theorem toNatAux_addDigits_left_distrib {a b : List Nat} {base : Nat} :
  toNatAux (addDigits a b) base = (toNatAux a base) + (toNatAux b base) := by
  have h1 : toNatAux [] base = 0 := by rw [toNatAux.eq_def, toNatAux.helper.eq_def]
  induction a generalizing b with
  | nil =>
    have h2 : addDigits [] b = b := by rw [addDigits.eq_def]; match b with | [] | v::vs => rfl
    rw [h2, h1, Nat.zero_add]
  | cons u us iha =>
    rw [addDigits.eq_def]
    match b with
    | [] => simp only [h1, Nat.add_zero]
    | v::vs =>
      simp only [toNatAux_cons_eq, iha]
      rw [Nat.add_assoc, Nat.add_comm, Nat.mul_add]
      rw (occs := .pos [3]) [Nat.add_comm]
      rw [← Nat.add_assoc]
      rw (occs := .pos [2, 1]) [Nat.add_comm]
      rw (occs := .pos [2]) [Nat.add_comm]
      rw [← Nat.add_assoc]

end ToNatAux_AddDigits

section AddAux

/-- -/
def addAux (a b : List Nat) (n base : Nat) (hb : 1 < base) : List Nat :=
  match a, b, hn: n with
  | [], [], 0 => []
  | [], [], k + 1 =>
    -- for asserting termination
    have h : 0 < (k + 1) := Nat.zero_lt_succ k
    have : (k + 1) / base < k + 1 := Nat.div_lt_self h hb
    ((k + 1) % base)::(addAux [] [] ((k + 1) / base) base hb)
  | x::xs, [], n => ((x + n) % base)::(addAux xs [] ((x + n) / base) base hb)
  | [], y::ys, n => ((y + n) % base)::(addAux [] ys ((y + n) / base) base hb)
  | x::xs, y::ys, n => ((x + y + n) % base)::(addAux xs ys ((x + y + n) / base) base hb)
  termination_by (a.length + b.length, n)

/-- -/
theorem addAux_eq_nil_iff {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = [] ↔ n = 0 ∧ a = [] ∧ b = [] := by
  constructor
  · intro h
    match ga : a, gb : b, gn : n with
    | [], [], 0 => simp only [and_self]
    | [], [], k + 1
    | x::xs, [], n
    | [], y::ys, n
    | x::xs, y::ys, n => simp only [addAux, reduceCtorEq] at h
  · intro h
    simp only [h.right.left, h.right.right, h.left, addAux]

/-- -/
theorem addAux_eq_singleton_of {a b : List Nat} (n : Nat) {base : Nat}
  (han : a = []) (hbn : b = []) (hb : 1 < base) (hn : 0 < n ∧ n < base) :
  addAux a b n base hb = [n] := by
  have h1 : n % base = n := Nat.mod_eq_of_lt hn.right
  have h2 : 0 < n := hn.left
  have h3 : n / base = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hn.right)
  rw [addAux.eq_def]
  match ga : a, gb : b, gn: n with
  | [], [], k + 1 => simp only [List.cons.injEq, h1, true_and, h3, addAux_eq_nil_iff hb]

theorem addAux_comm {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = addAux b a n base hb := by
  fun_induction addAux a b n base hb with
  | case1 => rw [addAux]
  | case2 => rw [addAux]
  | case3 _ _ _ ih => rw [addAux]; rw [ih]
  | case4 _ _ _ ih => rw [addAux]; rw [ih]
  | case5 x _ y _ _ ih => rw [addAux]; rw [ih]; rw [Nat.add_comm y x]

end AddAux

section AddAux_Prune_AddDigits

theorem addAux_nil_eq_prune_addDigits_nil {a : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux [] a n base hb = prune (addDigits [] a) n base hb := by
  induction a generalizing n with
  | nil =>
    induction n using Nat.strongRecOn with
    | _ l ihk =>
      rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
      if hl : l = 0 then
        rw [hl]
      else
        have h1 : l / base < l := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hl) hb
        have h2 : addAux [] [] (l / base) base hb = prune [] (l / base) base hb := by
          rw [ihk (l / base) h1, addDigits.eq_def]
        match hl : l with
        | 0 => simp only
        | k + 1 => simp only [h2]
  | cons y ys ihy =>
    rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
    simp only
    rw [List.cons.injEq]
    have h1 : addDigits [] ys = ys := by rw [addDigits_comm]; exact addDigits_nil_eq
    have h2 : addAux [] ys ((y + n) / base) base hb = prune ys ((y + n) / base) base hb := by
      rw [h1] at ihy
      exact ihy
    exact And.intro rfl h2

/-- -/
theorem addAux_eq_prune_addDigits {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = prune (addDigits a b) n base hb := by
  induction a generalizing b n with
  | nil => exact addAux_nil_eq_prune_addDigits_nil hb
  | cons x xs ihx =>
    rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
    match hb : b with
    | [] =>
      simp only
      rw [List.cons.injEq]
      have : addDigits xs [] = xs := addDigits_nil_eq
      rw (occs := .pos [2]) [← this]
      exact And.intro rfl ihx
    | y::ys  =>
      simp only
      rw [List.cons.injEq]
      exact And.intro rfl ihx

/--
alternative proof for `addAux_comm`
-/
example {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = addAux b a n base hb := by
  rw [addAux_eq_prune_addDigits, addDigits_comm, addAux_eq_prune_addDigits]

end AddAux_Prune_AddDigits

section AllDigitsLtBase_AddAux

/-- -/
theorem allDigitsLtBase_addAux {a b : List Nat} (n : Nat) {base : Nat} {hb : 1 < base} :
  allDigitsLtBase (addAux a b n base hb) base := by
  rw [addAux_eq_prune_addDigits hb]
  exact allDigitsLtBase_prune

end AllDigitsLtBase_AddAux

section NoTrailingZero_AddAux

/-- -/
theorem noTrailingZero_addAux_of {a b : List Nat} {n base : Nat}
  (hantz : noTrailingZero a) (hbntz : noTrailingZero b) (hb : 1 < base) :
  noTrailingZero (addAux a b n base hb) := by
  have : noTrailingZero (addDigits a b) := noTrailingZero_addDigits_of hantz hbntz
  rw [addAux_eq_prune_addDigits hb]
  exact noTrailingZero_prune_of_noTrailingZero this

end NoTrailingZero_AddAux

section ToNatAux_AddAux

/-- -/
theorem toNatAux_addAux_left_distrib {a b : List Nat} {base : Nat} {hb : 1 < base} :
  toNatAux (addAux a b 0 base hb) base = (toNatAux a base) + (toNatAux b base) := by
  rw [addAux_eq_prune_addDigits hb, toNatAux_prune_eq_add_toNatAux hb, toNatAux_addDigits_left_distrib, Nat.zero_add]

end ToNatAux_AddAux

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

theorem toNatAux_subAux_nil_zero_eq_zero {a : List Nat} {base : Nat} :
  toNatAux (subAux [] a 0 base) base = 0 := by
  unfold subAux toNatAux toNatAux.helper
  rfl

example {a : List Nat} {base : Nat} (ha : a = [0]) (hb: base = 10) :
  toNatAux (subAux a [] 1 base) base ≠ (toNatAux a base) - 1 := by
  have h1 : toNatAux (subAux a [] 1 base) base = 9 := by
    simp only [ha, hb, subAux, subAux.helper, toNatAux]
    decide
  have h2 : (toNatAux a base) - 1 = 0 := by
    simp only [ha, hb, toNatAux]
    decide
  rw [h1, h2]
  decide

theorem toNatAux_subAux_nil_one_eq_of {a : List Nat} {base : Nat} (hntza : noTrailingZero a) (hb : 1 < base) :
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
      have h3 : noTrailingZero xs ∧ (xs = [] → x ≠ 0) := noTrailingZero_tail_and_of hntza
      have h4 : xs ≠ [] := by
        false_or_by_contra; rename _ => hc
        exact absurd h2 (h3.right hc)
      have h5 : ¬ isZeroAux xs := by
        false_or_by_contra; rename _ => hc
        exact absurd ((isZeroAux_iff_eq_nil_of_noTrailingZero h3.left).mp hc) h4
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

theorem lt_toNatAux_subAux_of_ltAux_of {a b : List Nat} {base : Nat} (h : ltAux b a)
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
  (h : ltAux b a) (hntza : noTrailingZero a)
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
          have h3 : noTrailingZero xs := (noTrailingZero_tail_and_of hntza).left
          have h4 : allDigitsLtBase xs base := (allDigitsLtBase_cons_iff.mp halt).right
          have h5 : allDigitsLtBase ys base := (allDigitsLtBase_cons_iff.mp hblt).right
          have h6 : toNatAux (subAux xs ys 1 base) base = toNatAux (subAux xs ys 0 base) base - 1 :=
            ih h2 h3 h4 h5
          have h7 : ¬ equivAux xs ys := by
            rw [equivAux_iff_equivAux]
            exact not_equivAux_of_ltAux h2
          have h8 : 1 ≤ toNatAux (subAux xs ys 0 base) base :=
            Nat.succ_le_of_lt (lt_toNatAux_subAux_of_ltAux_of h2 hb h4 h5)
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
  (h : leAux b a) (hntza : noTrailingZero a)
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
      have h1 : noTrailingZero xs := (noTrailingZero_cons_iff_noTrailingZero_and.mp hntza).left
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

end SubAux

section Sub

def sub (a b : List Nat) (base : Nat) : List Nat :=
  if leAux a b then
    []
  else
    discardTrailingZeros (subAux a b 0 base)

end Sub

section ListFinBase

def toListFinBase {base : Nat} (a : List Nat) (h : allDigitsLtBase a base) : List (Fin base) :=
  match a with
  | [] => []
  | x::xs =>
    have : x < base := (allDigitsLtBase_cons_iff.mp h).left
    ⟨x,this⟩ :: toListFinBase xs (allDigitsLtBase_cons_iff.mp h).right

def fromListFinBase {base : Nat} (a : List (Fin base)) : List Nat :=
  match a with
  | [] => []
  | x::xs => ↑x :: fromListFinBase xs

theorem allDigitsLtBase_fromListFinBase {base : Nat} (a : List (Fin base)) :
  allDigitsLtBase (fromListFinBase a) base := by
  induction a with
  | nil => unfold fromListFinBase; simp only [allDigitsLtBase_nil]
  | cons x xs ih =>
    have hx : x < base := Fin.isLt x
    exact allDigitsLtBase_cons_iff.mpr (And.intro hx ih)

theorem fromListFinBase_toListFinBase_cancel {base : Nat} (a : List Nat) (h : allDigitsLtBase a base) :
  fromListFinBase (toListFinBase a h) = a := by
  induction a with
  | nil => simp only [toListFinBase, fromListFinBase]
  | cons x xs ih =>
    simp only [toListFinBase, fromListFinBase, ih]

theorem toListFinBase_fromListFinBase_cancel {base : Nat} (a : List (Fin base)) :
  toListFinBase (fromListFinBase a) (allDigitsLtBase_fromListFinBase a) = a := by
  induction a with
  | nil => simp only [toListFinBase, fromListFinBase]
  | cons x xs ih =>
    simp only [toListFinBase, fromListFinBase, ih]

end ListFinBase
