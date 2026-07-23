/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic
import Numerals.Equiv

namespace TZNumeral

section Tonz

/--
returns `n::a` if no additional trailing zero is created by using `n` as first digit, otherwise
`[] = a` is returned
-/
def tonz {base : NatGtOne} (n : base.Fin) : List base.Fin → List base.Fin
  | [] => if n = 0 then [] else [n]
  | x::xs => n::x::xs

theorem tonz_zero_nil_eq {base : NatGtOne} : @tonz base 0 [] = [] := by
  simp only [tonz, reduceIte]

theorem tonz_succ_nil_eq {base : NatGtOne} {n : base.Fin} (h : n ≠ 0) :
  tonz n [] = [n] := by
  simp only [tonz, h, reduceIte]

theorem tonz_cons_eq {base : NatGtOne} {n x : base.Fin} {xs : List base.Fin} : tonz n (x::xs) = n::x::xs := by
  simp only [tonz]

theorem equiv_helper_tonz_cons {base : NatGtOne} {n : base.Fin} {a : List base.Fin} :
  equiv.helper base (tonz n a) (n::a) := by
  match a with
  | [] =>
    if g : n = 0 then
      simp only [g, tonz_zero_nil_eq, equiv_helper_nil_iff, List.all, BEq.rfl, Bool.and_self]
    else
      simp only [tonz, g, reduceIte, equiv_helper_refl]
  | x::xs =>
    simp only [tonz, equiv_helper_refl]

theorem equiv_helper_tonz_nil_tonz_of_equiv_helper_nil {base : NatGtOne} {n : base.Fin} {a : List base.Fin}
  (h : equiv.helper base [] a) : equiv.helper base (tonz n []) (tonz n a) := by
  match a with
  | [] => exact equiv_helper_refl
  | x::xs =>
    if g : n = 0 then
      simp only [tonz_cons_eq, g, tonz_zero_nil_eq]
      rw [equiv_helper_nil_iff, List.all_cons]
      rw [equiv_helper_nil_iff] at h
      simp only [h, BEq.rfl, Bool.and_self]
    else
      simp only [tonz, g, reduceIte]
      simp only [equiv_helper_cons_iff, true_and]
      assumption

theorem equiv_helper_tonz_tonz_of_equiv_helper {base : NatGtOne} {n : base.Fin} {a b : List base.Fin}
  (h : equiv.helper base a b) : equiv.helper base (tonz n a) (tonz n b) := by
  match a, b with
  | [], _ => exact equiv_helper_tonz_nil_tonz_of_equiv_helper_nil h
  | _, [] =>
    rw [equiv_helper_iff_equiv_helper] at ⊢ h
    exact equiv_helper_tonz_nil_tonz_of_equiv_helper_nil h
  | x::xs, y::ys =>
    rw [tonz_cons_eq, tonz_cons_eq, equiv_helper_cons_iff]
    exact And.intro rfl h

theorem equiv_helper_tonz_singleton_of_equiv_helper_nil {base : NatGtOne} {n : base.Fin} {a : List base.Fin}
  (h : equiv.helper base a []) : equiv.helper base (tonz n a) [n] := by
  match a with
  | [] =>
    if g : n = 0 then
      simp only [g, tonz_zero_nil_eq, equiv_helper_nil_iff, List.all, BEq.refl, Bool.true_and]
    else
      simp only [tonz_succ_nil_eq g, equiv_helper_refl]
  | x::xs =>
    simp only [tonz_cons_eq]
    exact equiv_helper_cons_iff.mpr (And.intro rfl h)

theorem equiv_helper_tonz_cons_of_equiv_helper {base : NatGtOne} {n : base.Fin} {a b : List base.Fin}
  (h : equiv.helper base a b) : equiv.helper base (tonz n a) (n::b) := by
  match a, b with
  | _, [] => exact equiv_helper_tonz_singleton_of_equiv_helper_nil h
  | [], _ =>
    if g : n = 0 then
      simp only [g, tonz_zero_nil_eq]
      rw [equiv_helper_nil_iff] at ⊢ h
      simp only [List.all_cons, BEq.refl, Bool.true_and]
      assumption
    else
      simp only [tonz_succ_nil_eq g, equiv_helper_cons_iff, true_and]
      assumption
  | x::xs, y::ys =>
    simp only [tonz_cons_eq]
    rw [equiv_helper_cons_iff]
    exact And.intro rfl h

theorem noTrailingZeroAux_tonz_of {base : NatGtOne} {n : base.Fin} {a : List base.Fin} (ha : noTrailingZeroAux a) :
  noTrailingZeroAux (tonz n a) := by
  unfold tonz
  match a with
  | [] =>
    if g : n = 0 then
      simp only [g, reduceIte]
      assumption
    else
      simp only [g, reduceIte]
      exact noTrailingZero_singleton_of g
  | x::xs =>
    simp only
    have : x::xs = [] → n ≠ 0 := fun t : x::xs = [] => absurd t (List.cons_ne_nil x xs)
    exact noTrailingZeroAux_cons_of (And.intro ha this)

end Tonz

section DiscardTZ

def discardTZ {base : NatGtOne} (n : TZNumeral base) : TZNumeral base :=
  ⟨helper base n.digits⟩ where
  helper (base : NatGtOne) : List base.Fin → List base.Fin
  | [] => []
  | x::xs => tonz x (helper base xs)

theorem discardTZ_helper_nil_eq_nil {base : NatGtOne} : discardTZ.helper base [] = [] := by
  unfold discardTZ.helper
  rfl

theorem discardTZ_zero_eq_zero {base : NatGtOne} : @discardTZ base zero = zero := by
  simp only [discardTZ, discardTZ_helper_nil_eq_nil]

theorem noTrailingZeroAux_discardTZ_helper {base : NatGtOne} {l : List base.Fin} :
  noTrailingZeroAux (discardTZ.helper base l) := by
  induction l with
  | nil => simp only [discardTZ_helper_nil_eq_nil]; exact noTrailingZeroAux_nil
  | cons x xy ih =>
    simp only [discardTZ.helper]
    exact noTrailingZeroAux_tonz_of ih

theorem discardTZ_noTrailingZero {base : NatGtOne} {n : TZNumeral base} :
  n.discardTZ.noTrailingZero := by
  unfold noTrailingZero discardTZ
  exact noTrailingZeroAux_discardTZ_helper

theorem equiv_helper_discardTZ_helper {base : NatGtOne} {l : List base.Fin} :
  equiv.helper base (discardTZ.helper base l) l := by
  induction l with
  | nil => simp only [discardTZ.helper, equiv_helper_refl]
  | cons x xs ih =>
    simp only [discardTZ.helper]
    exact equiv_helper_tonz_cons_of_equiv_helper ih

theorem discardTZ_equiv {base : NatGtOne} {n : TZNumeral base} :
  n.discardTZ ≈ n := by
  unfold discardTZ
  exact equiv_helper_discardTZ_helper

end DiscardTZ

namespace TZNumeral
