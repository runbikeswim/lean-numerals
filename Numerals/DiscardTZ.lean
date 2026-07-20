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
returns `n::a` if no additional trailing zero is created by using `n` as first digit
-/
def tonz {base : NatGtOne} (n : base.Fin) (a : List base.Fin) : List base.Fin :=
  match a with
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
  equiv.helper (tonz n a) (n::a) := by
  match a with
  | [] =>
    if g : n = 0 then
      simp only [g, tonz_zero_nil_eq, equiv_helper_nil_iff, List.all, BEq.rfl, Bool.and_self]
    else
      simp only [tonz, g, reduceIte, equiv_helper_refl]
  | x::xs =>
    simp only [tonz, equiv_helper_refl]

theorem equiv_helper_tonz_nil_tonz_of_equiv_helper_nil {base : NatGtOne} {n : base.Fin} {a : List base.Fin}
  (h : equiv.helper [] a) : equiv.helper (tonz n []) (tonz n a) := by
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
  (h : equiv.helper a b) : equiv.helper (tonz n a) (tonz n b) := by
  match a, b with
  | [], _ => exact equiv_helper_tonz_nil_tonz_of_equiv_helper_nil h
  | _, [] =>
    rw [equiv_helper_iff_equiv_helper] at ⊢ h
    exact equiv_helper_tonz_nil_tonz_of_equiv_helper_nil h
  | x::xs, y::ys =>
    rw [tonz_cons_eq, tonz_cons_eq, equiv_helper_cons_iff]
    exact And.intro rfl h

theorem equiv_helper_tonz_singleton_of_equiv_helper_nil {base : NatGtOne} {n : base.Fin} {a : List base.Fin}
  (h : equiv.helper a []) : equiv.helper (tonz n a) [n] := by
  match a with
  | [] =>
    if g : n = 0 then
      simp only [g, tonz_zero_nil_eq, equiv_helper_nil_iff, List.all, BEq.refl, Bool.true_and]
    else
      simp only [tonz_succ_nil_eq g, equiv_helper_refl]
  | x::xs =>
    simp only [tonz_cons_eq]
    exact equiv_helper_cons_iff.mpr (And.intro rfl h)

/-
theorem equivAux_tonz_cons_of_equivAux {n : Nat} {a b : List Nat} (h : equivAux a b) :
  equivAux (tonz n a) (n::b) := by
  match n, a, b with
  | _, _, [] => exact equivAux_tonz_singleton_of_equivAux_nil h
  | 0, [], _ =>
    simp only [tonz_zero_nil_eq]
    exact equivAux_iff_equivAux.mp (equivAux_cons_nil_of_equivAux_nil (equivAux_iff_equivAux.mp h))
  | k + 1, [], _ =>
    simp only [tonz_succ_nil_eq]
    exact equivAux_cons_iff_eq_and_equivAux.mpr (And.intro rfl h)
  | _, x::xs, y::ys =>
    simp only [tonz_cons_eq]
    exact equivAux_cons_iff_eq_and_equivAux.mpr (And.intro rfl h)

theorem allDigitsLtBase_tonz_of {n base: Nat} {a : List Nat}
  (hn : n < base) (ha : allDigitsLtBase a base) :
  allDigitsLtBase (tonz n a) base := by
  unfold tonz
  match gn: n, ga: a with
  | 0, [] => simp only; exact allDigitsLtBase_nil
  | k + 1, [] => simp only; exact allDigitsLtBase_singleton hn
  | n, x::xs => simp only; exact allDigitsLtBase_cons_iff.mpr (And.intro hn ha)

theorem noTrailingZeroAux_tonz_of {n : Nat} {a : List Nat} (ha : noTrailingZeroAux a) :
  noTrailingZeroAux (tonz n a) := by
  unfold tonz
  match gn: n, ga: a with
  | 0, [] => simp only; exact noTrailingZeroAux_nil
  | k + 1, [] => simp only; exact noTrailingZeroAux_singleton_iff_ne_zero.mpr (Nat.succ_ne_zero k)
  | n, x::xs =>
    simp only
    have : x::xs = [] → n ≠ 0 := fun t : x::xs = [] => absurd t (List.cons_ne_nil x xs)
    exact noTrailingZeroAux_cons_of (And.intro ha this)

-/

end Tonz

section DiscardTZ

def discardTZ {base : NatGtOne} (n : TZNumeral base) : TZNumeral base :=
  ⟨helper base n.digits⟩ where
  helper (base : NatGtOne) (l : List base.Fin) : List base.Fin :=
  match l with
  | [] => []
  | x::xs => tonz x (helper base xs)

end DiscardTZ

namespace TZNumeral
