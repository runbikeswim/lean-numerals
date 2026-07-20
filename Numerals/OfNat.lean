/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Extra
import Numerals.Basic
import Numerals.ToNat
import Numerals.Prune

section OfNat

namespace TZNumeral

abbrev ofNat {base : NatGtOne} (n : Nat) : TZNumeral base := prune [] n

theorem ofNat_zero_eq_zero {base : NatGtOne} : @ofNat base 0 = 0 := by
  simp only [ofNat, zero_eq_zero, prune_nil_zero_eq_zero]

theorem eq_zero_of_ofNat_eq_zero {base : NatGtOne} {n : Nat} (h: ofNat n = @zero base) :
  n = 0 := by
  simp only [ofNat] at h
  exact (prune_eq_zero_iff_eq_nil_and_eq_zero.mp h).right

theorem ofNat_eq_zero_iff_eq_zero {base : NatGtOne} {n : Nat} : ofNat n = @zero base ↔ n = 0 := by
  constructor
  · intro h
    exact eq_zero_of_ofNat_eq_zero h
  · intro h
    rw [h]
    exact ofNat_zero_eq_zero

theorem ofNat_eq_of_lt_base {base : NatGtOne} {n : Nat} (hn : n < base.val) :
  ofNat n = if n = 0 then 0 else ⟨[⟨n, hn⟩]⟩   := by
  simp only [ofNat, prune_of_lt hn]

theorem ofNat_add_mul_eq_of {base : NatGtOne} {x y : Nat} (hx : x < base.val) :
  ofNat (x + base.val * y) =
    if x = 0 ∧ y = 0 then
      @zero base
    else
      cons (FinBase.ofNat x) (ofNat y) := by
  if g : x = 0 ∧ y = 0 then
    simp only [g.right, Nat.mul_zero, Nat.add_zero, g.left, and_true, reduceIte]
    exact ofNat_zero_eq_zero
  else
    have h1 : 0 < (x + base.val * y) := by
      rw [Decidable.not_and_iff_or_not] at g
      cases g with
      | inl gl => exact Nat.add_pos_left (Nat.pos_of_ne_zero gl) (base.val * y)
      | inr gr => exact Nat.add_pos_right x (Nat.mul_pos (Nat.pos_of_one_lt base.property) (Nat.pos_of_ne_zero gr))
    have h2 : (@FinBase.ofNat base (x + base.val * y)) = (FinBase.ofNat x) := by
      simp only [FinBase.ofNat, Nat.add_mul_mod_eq hx, (Nat.mod_eq_iff_lt base.val_ne_zero).mpr hx]
    have h3 : (x + base.val * y) / base.val = y := Nat.add_mul_div_eq hx
    simp only [g, reduceIte, ofNat, prune_nil_eq_cons_of_pos h1, h2, h3]

theorem toNat_ofNat_cancel {base : NatGtOne} (n : Nat) :
  @toNat base (ofNat n) = n := by
  simp only [ofNat]
  exact toNat_prune_nil_eq_add_toNat

theorem ofNat_noTrailingZero {base : NatGtOne} {n : Nat} : (@ofNat base n).noTrailingZero := by
  unfold ofNat
  exact prune_nil_noTrailingZero

end TZNumeral

end OfNat
