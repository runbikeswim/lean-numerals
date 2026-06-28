/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.NoTrailingZero
import Numerals.Prune

namespace NumeralAux

section OfNatAux

abbrev ofNatAux (n : Nat) (base : Nat) (hb : 1 < base) := prune [] n base hb

theorem ofNatAux_zero_eq_nil {base : Nat} {hb : 1 < base} : ofNatAux 0 base hb = [] := by
  simp only [ofNatAux, prune]

theorem eq_zero_of_iZeroAux_ofNatAux {n base : Nat} {hb : 1 < base} (h: isZeroAux (ofNatAux n base hb)) :
  n = 0 := by
  simp only [ofNatAux] at h
  have h1 : noTrailingZeroAux (prune [] n base hb) := noTrailingZeroAux_prune_nil
  have h2 : (prune [] n base hb) = [] := (isZeroAux_iff_eq_nil_of_noTrailingZeroAux h1).mp h
  exact ((prune_eq_nil_iff_eq_nil_and_eq_zero hb).mp h2).right

theorem isZeroAux_ofNatAux_iff_eq_zero {n base : Nat} {hb : 1 < base} :
  isZeroAux (ofNatAux n base hb) ↔ n = 0 := by
  constructor
  · intro h
    exact eq_zero_of_iZeroAux_ofNatAux h
  · intro h
    simp only [h, ofNatAux_zero_eq_nil, isZeroAux, equivAux]

theorem ofNatAux_eq_of_lt_base {n base : Nat} {hb : 1 < base} (hn : n < base) :
  ofNatAux n base hb = if n = 0 then [] else [n] := by
  unfold ofNatAux
  if g : n = 0 then
    simp only [g, reduceIte]
    exact prune_nil_eq_nil hb
  else
    have h1 : n % base = n := Nat.mod_eq_of_lt hn
    have h2 : n / base = 0 := Nat.div_eq_of_lt hn
    simp only [g, reduceIte]
    rw [prune_nil_eq_cons_of_pos (Nat.pos_of_ne_zero g) hb, h1, h2, prune_nil_eq_nil hb]

theorem ofNatAux_add_mul_eq_of {x y base : Nat} {hb : 1 < base} (hx : x < base) :
  ofNatAux (x + base * y) base hb =
    if x = 0 ∧ y = 0 then
      []
    else
      x :: (ofNatAux y base hb) := by
  if g : x = 0 ∧ y = 0 then
    simp only [g.right, Nat.mul_zero, Nat.add_zero, g.left, and_true, reduceIte]
    exact ofNatAux_zero_eq_nil
  else
    simp only [g, reduceIte, ofNatAux]
    have h1 : 0 < (x + base * y) := by
      rw [Decidable.not_and_iff_or_not] at g
      cases g with
      | inl gl => exact Nat.add_pos_left (Nat.pos_of_ne_zero gl) (base * y)
      | inr gr => exact Nat.add_pos_right x (Nat.mul_pos (Nat.pos_of_one_lt hb) (Nat.pos_of_ne_zero gr))
    have h2 : (x + base * y) % base = x := Nat.add_mul_mod_eq hx
    have h3 : (x + base * y) / base = y := Nat.add_mul_div_eq hx
    rw (occs := .pos [2]) [← h2]
    rw (occs := .pos [3]) [← h3]
    exact prune_nil_eq_cons_of_pos h1 hb

theorem toNatAux_ofNatAux_cancel (n : Nat) {base: Nat} (hb : 1 < base) :
  toNatAux (ofNatAux n base hb) base = n := by
    simp only [ofNatAux, toNatAux_prune_eq_add_toNatAux hb, toNatAux_nil_eq, Nat.add_zero]

theorem noTrailingZeroAux_ofNatAux {n base : Nat} {hb : 1 < base} : noTrailingZeroAux (ofNatAux n base hb) := by
  unfold ofNatAux
  exact noTrailingZeroAux_prune_nil

end OfNatAux

end NumeralAux
