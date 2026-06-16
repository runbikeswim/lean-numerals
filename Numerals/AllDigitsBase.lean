/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

namespace NumeralAux

section AllDigitsLtBase

/-
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

instance instAllDigitsLtBase (a : List Nat) (base : Nat) : Decidable (allDigitsLtBase a base) :=
  decAllDigitsLtBase a base

theorem allDigitsLtBase_nil {base : Nat}  :
  allDigitsLtBase [] base := by
  rw [allDigitsLtBase.eq_def]
  exact List.all_nil

theorem allDigitsLtBase_cons_iff {x base : Nat} {xs : List Nat} :
  allDigitsLtBase (x::xs) base ↔ x < base ∧ allDigitsLtBase xs base := by
  unfold allDigitsLtBase
  simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]


theorem allDigitsLtBase_singleton {n : Nat} {base : Nat} (hn : n < base) :
  allDigitsLtBase [n] base := by
  exact allDigitsLtBase_cons_iff.mpr (And.intro hn allDigitsLtBase_nil)

end AllDigitsLtBase

end NumeralAux
