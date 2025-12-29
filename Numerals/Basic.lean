/-
Copyright (c) 2025 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Corollaries

set_option linter.all true
/-
TODO: remove and resolve
-/
set_option linter.missingDocs false

section Numerals

/-!
`Numeral` provides a representation of a natural number in positional notation for `base`, with `digits`
in _reverse_ (little-endian) order. `base` can be any number larger than one, which is ensured by `baseGtOne`.
`allDigitsLtBase` asserts that every digit is less than `base`.
Via `noTrailingZeros`, it is ensured that there are no trailing zeros, so except for zero, every natural
number has a unique representation for the given `base`.
`0` can be represented in two ways: either digits equals`[]` or `[0]`, which is independent of `base`
-/
structure Numeral where
  digits : List Nat
  base: Nat := 10
  baseGtOne : 1 < base
  allDigitsLtBase : digits.all (· < base)
  noTrailingZeros : (h : digits ≠ []) → digits ≠ [0] → digits.getLast h ≠ 0
deriving Repr, DecidableEq

namespace Numeral

section Groundwork

/-!
`isZero` covers the two representations of zero as `Numeral`
-/
def isZero (a : Numeral) : Prop := a.digits = [] ∨ a.digits = [0]

def decIsZero (a : Numeral) : Decidable a.isZero :=
  if h : a.digits = [] ∨ a.digits = [0] then
    isTrue h
  else
    isFalse h

instance instDecidableIsZero {a : Numeral} : Decidable a.isZero := a.decIsZero

instance instInhabitedNumeral : Inhabited Numeral := ⟨{
    digits := [0],
    base := 10,
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, List.cons_ne_self,
                        not_false_eq_true, not_true_eq_false,
                        List.getLast_singleton, imp_self]
  }⟩

def toString (n : Numeral) : String :=
  let digits : List Nat := if n.digits = [] then [0] else n.digits.reverse
  helper digits n.base where
  helper (l : List Nat) (b : Nat) :=
    match b with
    | 2 | 8 => s!"{String.join (l.map (s!"{·}"))}({b})"
    | 10 => s!"{String.join (l.map (s!"{·}"))}"
    | 16 =>
      let toHexDigit (d : Nat) : String :=
        match d with
        | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => s!"{d}"
        | 10 => "a"
        | 11 => "b"
        | 12 => "c"
        | 13 => "d"
        | 14 => "e"
        | 15 => "f"
        | _  => "😞"
      s!"{String.join (l.map toHexDigit)}(16)"
    | _ => ",".intercalate (l.map (fun d : Nat => s!"{d}")) ++ s!"({b})"

instance instToStringNumeral : ToString Numeral := ⟨toString⟩

@[simp]
def allDigitsLtBase_cons {n base : Nat} {d : List Nat} :
  (n::d).all (· < base) ↔ n < base ∧ d.all (· < base) := by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]

end Groundwork

section TrailingZeros

@[simp]
theorem noTrailingZeros_cons_of_ne_zero (n : Nat) {d : List Nat} (hdnz : d ≠ [0])
  (hdntz : (hdnn : d ≠ []) → d ≠ [0] → d.getLast hdnn ≠ 0):
  (h : n::d ≠ []) → n::d ≠ [0] → (n::d).getLast h ≠ 0 := by
  intro h hndnz
  match d with
  | [] =>
    have hnn : ¬n = 0 := by rwa [← List.singleton_inj]
    rwa [List.getLast_singleton h]
  | head::tail =>
    rw [List.getLast_cons_cons]
    exact (hdntz (List.cons_ne_nil head tail)) hdnz

@[simp]
theorem ne_zero_of_noTrailingZeros_cons {n : Nat} {d : List Nat}
  (hntz : (h : n::d ≠ []) → n::d ≠ [0] → (n::d).getLast h ≠ 0) : d ≠ [0] := by
  have h : n::d ≠ [] := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  if g : n::d = [0] then
    simp only [(List.cons_singleton_iff_and_eq_nil.mp g).right,
      ne_eq, List.ne_cons_self, not_false_eq_true]
  else
    false_or_by_contra; rename _ => hc
    have h1 : d ≠ [] := by simp only [hc, ne_eq, List.cons_ne_self, not_false_eq_true]
    have h2 : (n :: d).getLast h ≠ 0 := hntz h g
    have h3 : d.getLast h1 ≠ 0 := by rwa [List.getLast_cons h1] at h2
    have h4 : d.getLast h1 = 0 := by simp only [hc, List.getLast_singleton]
    contradiction

@[simp]
theorem noTrailingZeros_of_noTrailingZeros_cons {n : Nat} {d : List Nat}
  (hntc : (h : n::d ≠ []) → n::d ≠ [0] → (n::d).getLast h ≠ 0) :
  (hdnn : d ≠ []) → d ≠ [0] → d.getLast hdnn ≠ 0 := by
  intro hdnn hdnz
  have h1 : n::d ≠ [] := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  have h2 : n::d ≠ [0] := by
    false_or_by_contra; rename _ => hc
    exact absurd (List.cons_singleton_iff_and_eq_nil.mp hc).right hdnn
  have h3 : (n::d).getLast h1 = d.getLast hdnn := List.getLast_cons hdnn
  have h4 : (n::d).getLast h1 ≠ 0 := hntc h1 h2
  rwa [h3] at h4

end TrailingZeros

/-
section MulDivBase

def mul_base (a : Numeral) : Numeral :=
  if h : a.isZero then
    a
  else {
    digits := 0::a.digits
    base := a.base
    baseGtOne := a.baseGtOne
    allDigitsLtBase := allDigitsLtBase_cons.mpr (
        And.intro
          (Nat.lt_trans (by decide) a.baseGtOne)
          a.allDigitsLtBase
      )
    noTrailingZeros := noTrailingZeros_cons_of_ne_zero 0 (not_or.mp h).right a.noTrailingZeros
  }

@[simp]
theorem mul_base_eq_cons_zero_of_ne_zero {a : Numeral} (h : ¬ a.isZero) : a.mul_base.digits = 0::(a.digits) := by
  simp only [mul_base, h, ↓reduceDIte]

def div_base (a : Numeral) : Numeral :=
  match h : a.digits with
  | [] => a
  | head::tail =>
    {
      digits := tail,
      base := a.base,
      baseGtOne := a.baseGtOne,
      allDigitsLtBase := by
        let := a.allDigitsLtBase
        rw [h] at this
        exact (allDigitsLtBase_cons.mp this).right
      noTrailingZeros := by
        let := a.noTrailingZeros
        rw [h] at this
        exact noTrailingZeros_of_noTrailingZeros_cons this
    }

end MulDivBase
-/

section ToNat

def toNat (n : Numeral) : Nat :=
  (helper n.digits n.base 1 0).snd where
    helper (digits : List Nat) (base factor acc : Nat) : Nat × Nat :=
      match digits with
      | [] => (factor, acc)
      | a::as => helper as base (factor * base) (a * factor + acc)

@[simp]
theorem toNat_helper_nil {base factor acc : Nat} : (toNat.helper [] base factor acc) = (factor, acc) := by
  unfold toNat.helper
  rfl

@[simp]
theorem toNat_helper_acc_factor (digits : List Nat) (base factor acc : Nat)  :
  (toNat.helper digits base factor acc).snd = acc + factor * (toNat.helper digits base 1 0).snd := by
  induction digits generalizing factor acc with
  | nil => simp_all only [toNat_helper_nil, Nat.mul_zero, Nat.add_zero]
  | cons head tail ih =>
    unfold toNat.helper
    simp only [Nat.one_mul, Nat.mul_one, Nat.add_zero]
    rw [ih base head]
    rw [Nat.left_distrib factor head, ← Nat.add_assoc, ← Nat.mul_assoc factor base]
    rw [Nat.add_comm acc (factor * head)]
    rw [Nat.mul_comm factor head]
    rw [ih (factor * base) (head * factor + acc)]

@[simp]
theorem toNat_helper_cons (digits : List Nat) (n base : Nat) :
  (toNat.helper (n::digits) base 1 0).snd = n + base * (toNat.helper digits base 1 0).snd := by
  rw [toNat.helper.eq_def]
  simp only [Nat.one_mul, Nat.mul_one, Nat.add_zero]
  exact toNat_helper_acc_factor digits base base n

end ToNat

section AddNatAux

/-
def addNatAux (n : Nat) (digits : List Nat) (base : Nat) (hb : 1 < base) : List Nat :=
  match digits with
  | [] =>
    if g : n = 0 then
      []
    else
      -- for proofing termination
      have : n / base < n := Nat.div_lt_self (Nat.pos_iff_ne_zero.mpr g) hb
      (n % base)::(addNatAux (n / base) [] base hb)
  | d::ds =>
    let s := n + d
    (s % base)::(addNatAux (s / base) ds base hb)
  termination_by (digits.length, n)

@[simp]
theorem addNatAux_cons {n base : Nat} {digits : List Nat} (hb : 1 < base) :
  addNatAux 0 (n::digits) base hb = addNatAux n (0::digits) base hb := by
  unfold addNatAux
  simp only [Nat.zero_add, Nat.add_zero]

@[simp]
theorem addNatAux_nil_iff_and_zero_nil (n : Nat) {base : Nat} (digits : List Nat) (hb : 1 < base) :
  addNatAux n digits base hb = [] ↔ n = 0 ∧ digits = [] := by
  unfold addNatAux
  constructor
  · intro h
    match hd : digits with
    | [] | d::ds =>
    simp_all only [
      dite_eq_ite, ite_eq_left_iff, reduceCtorEq, imp_false,
      Decidable.not_not, and_self
    ]
  · intro h
    simp only [h, ↓reduceDIte]

@[simp]
theorem addNatAux_zero_iff_and_zero_zero (n : Nat) {base : Nat} (digits : List Nat) (hb : 1 < base) :
  (addNatAux n digits base hb) = [0] ↔ n = 0 ∧ digits = [0] := by
  constructor
  · intro g
    unfold addNatAux at g
    if hn : n = 0 then
      match hd: digits with
      | [] => simp_all only [↓reduceDIte, List.ne_cons_self]
      | d::ds =>
        simp only [hn, true_and, List.cons.injEq]
        simp only [hn, Nat.zero_add, List.cons.injEq, addNatAux_nil_iff_and_zero_nil] at g
        have : d < base := Nat.lt_of_div_eq_zero (Nat.pos_of_one_lt hb) g.right.left
        have : d = 0 := Nat.eq_zero_of_lt_of_mod_eq_zero hb g.left (Or.inr this)
        exact And.intro this g.right.right
    else
      match hd: digits with
      | [] =>
        simp_all only [↓reduceDIte, List.cons.injEq, addNatAux_nil_iff_and_zero_nil,
          Nat.div_eq_zero_iff, and_true, List.ne_cons_self, and_self]
        have h1 : n = 0 := Nat.eq_zero_of_lt_of_mod_eq_zero hb g.left g.right
        contradiction
      | d::ds =>
        simp_all only [List.cons.injEq, addNatAux_nil_iff_and_zero_nil,
          Nat.div_eq_zero_iff, and_true, false_and]
        have h1 : n = 0 := (Nat.eq_zero_of_add_eq_zero (Nat.eq_zero_of_lt_of_mod_eq_zero hb g.left g.right.left)).left
        contradiction
  · intro g
    simp only [g.left, g.right]
    unfold addNatAux addNatAux
    simp only [Nat.add_zero, Nat.zero_mod, Nat.zero_div, ↓reduceDIte]

@[simp]
theorem addNatAux_ne_zero_of_ne_zero (n : Nat) {base : Nat} (digits : List Nat) (hb : 1 < base) (hd: digits ≠ [0]):
  (addNatAux n digits base hb) ≠ [0] := by
  have h1 : ¬(n = 0 ∧ digits = [0]) := Classical.not_and_iff_not_or_not.mpr (Or.inr hd)
  exact (iff_iff_iff_not_not.mp (addNatAux_zero_iff_and_zero_zero n digits hb)).mpr h1

@[simp]
theorem addNatAux_nil_noTrailingZeros_of_zero {n base : Nat} (hb : 1 < base) (hn : n = 0):
  (h : addNatAux n [] base hb ≠ []) → addNatAux n [] base hb ≠ [0]
      → (addNatAux n [] base hb).getLast h ≠ 0  := by
  intro h
  have : addNatAux n [] base hb = [] := by
    simp only [addNatAux_nil_iff_and_zero_nil, and_true]; exact hn
  contradiction

@[simp]
theorem addNatAux_nil_noTrailingZeros_of_ne_zero {n base : Nat} (hb : 1 < base) (hn : n ≠ 0):
  (addNatAux n [] base hb).getLast (by simp only [ne_eq, addNatAux_nil_iff_and_zero_nil, and_true]; exact hn) ≠ 0  := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold addNatAux
    simp only [hn, ↓reduceDIte, ne_eq]
    if g : n < base then
      have h1 : n / base = 0 := Nat.div_eq_zero_iff.mpr (Or.inr g)
      have h2 : addNatAux (n / base) [] base hb = [] :=
        (addNatAux_nil_iff_and_zero_nil (n / base) [] hb).mpr (And.intro h1 rfl)
      simp only [h2, List.getLast_singleton, ne_eq]
      exact Nat.ne_zero_mod_of_ne_zero hb h1 hn
    else
      have h1 : n / base ≠ 0 := Nat.div_ne_zero_iff.mpr (And.intro (Nat.ne_zero_of_lt hb) (Nat.not_lt.mp g))
      have h2 : ¬(n / base = 0 ∧ ([] : List Nat) = []) := Classical.not_and_iff_not_or_not.mpr (Or.inl h1)
      have h3 : addNatAux (n / base) [] base hb ≠ [] :=
        (iff_iff_iff_not_not.mp (addNatAux_nil_iff_and_zero_nil (n / base) [] hb)).mpr h2
      have h4 : 0 < n := Nat.lt_of_lt_of_le (Nat.lt_trans (by decide) hb) (Nat.le_of_not_lt g)
      have h5 : n / base < n := Nat.div_lt_self h4 hb
      rw [List.getLast_cons h3]
      exact ih (n / base) h5 h1

@[simp]
theorem addNatAux_nil_noTrailingZeros {n base : Nat} (hb : 1 < base) :
  (h : addNatAux n [] base hb ≠ []) → addNatAux n [] base hb ≠ [0]
      → (addNatAux n [] base hb).getLast h ≠ 0  := by
  if hn : n = 0 then
    exact addNatAux_nil_noTrailingZeros_of_zero hb hn
  else
    intro h g
    exact addNatAux_nil_noTrailingZeros_of_ne_zero hb hn

@[simp]
theorem cons_addNatAux_nil_noTrailingZeros (n m : Nat) {base : Nat} (hb : 1 < base) :
  (h : m :: addNatAux n [] base hb ≠ []) →
    m :: addNatAux n [] base hb ≠ [0] →
      (m :: addNatAux n [] base hb).getLast h ≠ 0 := by
  have h1 : addNatAux n [] base hb ≠ [0] := by
    false_or_by_contra; rename _ => hx
    have : [] = [0] := ((addNatAux_zero_iff_and_zero_zero n [] hb).mp hx).right
    simp only [List.ne_cons_self] at this
  have h2 : (h : addNatAux n [] base hb ≠ []) →
            addNatAux n [] base hb ≠ [0]  →
              (addNatAux n [] base hb).getLast h ≠ 0 := addNatAux_nil_noTrailingZeros hb
  exact noTrailingZeros_cons_of_ne_zero m h1 h2

@[simp]
theorem addNatAux_noTrailingZeros_of_noTrailingZeros (n : Nat) {base : Nat} {digits : List Nat} (hb : 1 < base)
  (hd : (hdnn : digits ≠ []) → digits ≠ [0] → digits.getLast hdnn ≠ 0) :
  (h : addNatAux n digits base hb ≠ []) →
    addNatAux n digits base hb ≠ [0] →
      (addNatAux n digits base hb).getLast h ≠ 0 := by
  fun_induction addNatAux with
  | case1 => exact hd
  | case2 n hn ht ih => exact cons_addNatAux_nil_noTrailingZeros (n / base) (n % base) hb
  | case3 n d ds s ih =>
    if g : ds = [] then
      rw [g]
      exact cons_addNatAux_nil_noTrailingZeros (s / base) (s % base) hb
    else
      have h1 : d :: ds ≠ [0] := by simp only [ne_eq, List.cons.injEq, g, and_false, not_false_eq_true]
      have h2 : (d :: ds).getLast (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) ≠ 0 :=
        hd (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) h1
      have h3 : (d::ds).getLast (by simp) = ds.getLast g := List.getLast_cons g
      have h4 : ds ≠ [0] := by
        false_or_by_contra; rename _ => hx
        have : (d :: ds).getLast (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) = 0 :=
          List.getLast_cons_of_singleton d hx
        contradiction
      have h5 : addNatAux (s / base) ds base hb ≠ [0] := addNatAux_ne_zero_of_ne_zero (s / base) ds hb h4
      have h6 : ds.getLast g ≠ 0 := by rwa [← h3]
      have h7 : (h : addNatAux (s / base) ds base hb ≠ []) →
            addNatAux (s / base) ds base hb ≠ [0] →
              (addNatAux (s / base) ds base hb).getLast h ≠ 0 :=
        ih (fun _ : ds ≠ [] => fun _ : ds ≠ [0] => h6 )
      exact noTrailingZeros_cons_of_ne_zero (s % base) h5 h7

@[simp]
theorem all_addNatAux_lt_base {n base : Nat} {digits : List Nat} (hb : 1 < base) :
  (addNatAux n digits base hb).all (· < base) := by
  fun_induction addNatAux with
  | case1 => exact List.all_nil
  | case2 n g _ ih =>
    have hn : n % base < base := Nat.mod_lt n (Nat.pos_of_one_lt hb)
    exact allDigitsLtBase_cons.mpr (And.intro hn ih)
  | case3 n d ds s ih =>
    have hs : s % base < base := Nat.mod_lt s (Nat.pos_of_one_lt hb)
    exact allDigitsLtBase_cons.mpr (And.intro hs ih)

@[simp]
theorem addNatAux_eq_singleton (n : Nat) {base : Nat} (hb : 1 < base) (hn : 0 < n ∧ n < base) :
  addNatAux n [] base hb = [n] := by
  have he : n % base = n := Nat.mod_eq_of_lt hn.right
  have hne : n ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr hn.left
  have hdz : n / base = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hn.right)
  have hnil : addNatAux 0 [] base hb = [] := (addNatAux_nil_iff_and_zero_nil 0 [] hb).mpr (And.intro rfl rfl)
  rw [addNatAux, he]
  simp only [hne, ↓reduceDIte, hdz, hnil]

@[simp]
theorem addNatAux_eq_cons_zero_addNatAux (n : Nat) {base : Nat} (hb : 1 < base) (hn : base ≤ n ∧ n % base = 0) :
  addNatAux n [] base hb = 0::(addNatAux (n / base) [] base hb) := by
  rw [addNatAux]
  have hne : n ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr (Nat.pos_of_one_lt (Nat.lt_of_lt_of_le hb hn.left))
  simp only [hne, ↓reduceDIte, hn.right]

@[simp]
theorem addNatAux_add_eq_append_addNatAux_addNatAux (n m : Nat) {base : Nat} (hb : 1 < base) (hn : 0 < n ∧ n < base) :
  addNatAux (n + m * base) [] base hb = addNatAux n [] base hb ++ addNatAux m [] base hb := by
  have hb': 0 < base := Nat.lt_trans (by decide) hb
  have hs : addNatAux n [] base hb = [n] := addNatAux_eq_singleton n hb hn
  have hac : addNatAux n [] base hb ++ addNatAux m [] base hb = n::(addNatAux m [] base hb) := by
    rw [hs, List.singleton_append]
  have hnz : 0 < n + m * base := by
    calc 0 < n := hn.left
      _ ≤ n + m * base := Nat.le_add_right n (m * base)
  have hnr : ¬base ≤ n := by simp only [Nat.not_le, hn.right]
  have hme: (n + m * base) % base = n := Nat.mod_add_mul_eq n m hn.right
  have hde : (n + m * base) / base = m := Nat.div_add_mul_eq n m hn.right
  rw [hac, addNatAux, hme]
  simp only [Nat.ne_zero_of_lt hnz, ↓reduceDIte, hde]

@[simp]
theorem addNatAux_zero_eq_of_all_lt_base {digits : List Nat} {base : Nat} (hb : 1 < base) (hd : digits.all (· < base)) :
  addNatAux 0 digits base hb = digits := by
  induction digits with
  | nil => simp only [addNatAux_nil_iff_and_zero_nil, and_self]
  | cons head tail ih =>
    unfold addNatAux
    have h1 : head < base := (allDigitsLtBase_cons.mp hd).left
    have h2 : head / base = 0 := Nat.div_eq_zero_iff.mpr (Or.inr h1)
    have h3 : head % base = head := Nat.mod_eq_of_lt h1
    simp only [Nat.zero_add, List.cons.injEq, h2, h3, true_and]
    exact ih (allDigitsLtBase_cons.mp hd).right

-/

end AddNatAux

section AddAux

def addAux (a b : List Nat) (n base : Nat) (hb : 1 < base) : List Nat :=
  match a, b, hn: n with
  | [], [], 0 => []
  | [], [], k + 1 =>
    have hn0 : 0 < n := by rw [hn]; exact Nat.zero_lt_succ k
    -- for asserting termination
    have hltn : n / base < n := Nat.div_lt_self hn0 hb
    (n % base)::(addAux [] [] (n / base) base hb)
  | x::xs, [], n =>
    ((x + n) % base)::(addAux xs [] ((x + n) / base) base hb)
  | [], y::ys, n =>
    ((y + n) % base)::(addAux [] ys ((y + n) / base) base hb)
  | x::xs, y::ys, n =>
    ((x + y + n) % base)::(addAux xs ys ((x + y + n) / base) base hb)
  termination_by (a.length + b.length, n)

theorem addAux_nil_zero_eq {a b : List Nat} (hbn : b = []) {n base : Nat} (hn : n = 0) (hb : 1 < base) (halt : a.all (· < base)) :
  addAux a b n base hb = a := by
  fun_induction addAux a b n base hb with
  | case1 => rfl
  | case2 => contradiction
  | case3 x xs n ih =>
    have hxm : x % base = x := Nat.mod_eq_of_lt (allDigitsLtBase_cons.mp halt).left
    have hxd : (x + n) / base = 0 := by rw [hn, Nat.add_zero]; exact Nat.div_eq_of_lt (allDigitsLtBase_cons.mp halt).left
    rw [ih hbn hxd (allDigitsLtBase_cons.mp halt).right, hn, Nat.add_zero, hxm]
  | case4 => contradiction
  | case5 => contradiction

theorem addAux_comm {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base  hb = addAux b a n base  hb := by
  fun_induction addAux a b n base hb with
  | case1 => rw [addAux]
  | case2 => rw [addAux]
  | case3 _ _ _ ih => rw [addAux]; rw [ih]
  | case4 _ _ _ ih => rw [addAux]; rw [ih]
  | case5 x _ y _ _ ih => rw [addAux]; rw [ih]; rw [Nat.add_comm y x]

theorem all_addAux_digits_lt_base {a b : List Nat} {n base : Nat}  (hb : 1 < base) :
  (addAux a b n base hb ).all (· < base) := by
  have hb0 : 0 < base := Nat.lt_trans (by decide) hb
  fun_induction addAux with
  | case1 => exact List.all_nil
  | case2 k _ _ ih =>
    simp only [Nat.succ_eq_add_one, List.all_cons, Nat.mod_lt k.succ hb0, decide_true, ih, Bool.and_self]
  | case3 x _ n ih =>
    simp only [List.all_cons, Nat.mod_lt (x + n) hb0, decide_true, ih, Bool.and_self]
  | case4 y _ n ih =>
    simp only [List.all_cons, Nat.mod_lt (y + n) hb0, decide_true, ih, Bool.and_self]
  | case5 x _ y _ n ih =>
    simp only [List.all_cons, Nat.mod_lt (x + y + n) hb0, decide_true, ih, Bool.and_self]

/-

@[simp]
theorem addAux_nil_iff_and_zero_nil_nil (a b : List Nat) (base carry : Nat)
  (halt : a.all (· < base)) (hblt : b.all (· < base))
  (hb : 1 < base) (hc : carry < base) :
  (addAux a b base carry halt hblt hb hc) = [] ↔ carry = 0 ∧ a = [] ∧ b = []  := by
  constructor
  · intro h
    unfold addAux at h
    match a, b with
    | [], [] =>
      simp only [addNatAux_nil_iff_and_zero_nil, and_true] at h
      exact And.intro h (And.intro rfl rfl)
    | x::xs, [] | [], y::ys | x::xs, y::ys =>
      simp only [addNatAux_nil_iff_and_zero_nil, reduceCtorEq, and_false] at h
  · intro h
    unfold addAux
    match a, b with
    | [], [] =>
      simp only [addNatAux_nil_iff_and_zero_nil, and_true]
      exact h.left
    | x::xs, [] | x::xs, y::ys =>
      have : False := absurd h.right.left (List.cons_ne_nil x xs)
      contradiction
    | [], y::ys =>
      have : False := absurd h.right.right (List.cons_ne_nil y ys)
      contradiction
-/

@[simp]
theorem addAux_eq_zero_iff {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb  = [0] ↔ n = 0 ∧ (a = [0] ∧ b = [] ∨ a = [] ∧ b = [0] ∨ a = [0] ∧ b = [0]) := by
  unfold addAux
  constructor
  · intro h
    match ga : a, gb : b, hn : n with
    | [], [], 0 => simp only [List.ne_cons_self] at h
    | [], [], k + 1 =>
      have : (k + 1) % base ≠ 0 := sorry
      simp only [List.cons.injEq] at h

      sorry
    | x::xs, [], n => sorry
    | [], y::ys, n => sorry
    | x::xs, y::ys, n => sorry
  · intro h
    match ga : a, gb : b, hn : n with
    | [], [], 0 => sorry
    | [], [], k + 1 => sorry
    | x::xs, [], n => sorry
    | [], y::ys, n => sorry
    | x::xs, y::ys, n => sorry


theorem addAux_noTrailingZeros_of_noTrailingZeros
  (a b : List Nat) (n base : Nat)
  (hantz : (h : a ≠ []) → a ≠ [0] → a.getLast h ≠ 0)
  (hbntz : (h : b ≠ []) → b ≠ [0] → b.getLast h ≠ 0)
  (hb : 1 < base) :
  (h : addAux a b n base hb ≠ [])
    → addAux a b n base hb ≠ [0]
      → (addAux a b n base hb).getLast h ≠ 0 := by
  fun_induction addAux with
  | case1 => intro _; contradiction
  | case2 k hn0 hltn ih =>

    sorry
  | case3 =>
    sorry
  | case4 =>
    sorry
  | case5 =>
    sorry


/-

@[simp]
theorem addAux_nil_eq {digits : List Nat} {base : Nat} (hb : 1 < base) (hd : digits.all (· < base)) :
  addAux [] digits base 0 (List.all_nil) hd hb (Nat.lt_trans (by decide) hb) = digits := by
  have h1 : addNatAux 0 digits base hb = digits := addNatAux_zero_eq_of_all_lt_base hb hd
  unfold addAux
  match digits with
  | [] | y::ys => simp only [h1]

theorem addAux_carry_eq_addNatAux_carry_addAux_zero {a b : List Nat} {base carry : Nat}
  (halt : a.all (· < base)) (hblt : b.all (· < base)) (hb : 1 < base) (hc : carry < base) :
  addAux a b base carry halt hblt hb hc
    = addNatAux carry (addAux a b base 0 halt hblt hb (Nat.lt_trans (by decide) hb)) base hb := by
  fun_induction addAux with
  | case1 => simp only [addAux_nil_eq]
  | case2 => rw [addAux_comm]; simp only [addAux_nil_eq]
  | case3 => simp only [addAux_nil_eq]
  | case4 carry hc x xs y ys halt hblt s carry' hc' ih =>
    have h1 : ¬(0 = 0 ∧ x::xs = [] ∧ y::ys = []) := by simp only [reduceCtorEq, and_self, and_false, not_false_eq_true]
    have h2 : addAux (x::xs) (y::ys) base 0 halt hblt hb (Nat.lt_trans (by decide) hb) ≠ [] :=
      (iff_iff_iff_not_not.mp
        (addAux_nil_iff_and_zero_nil_nil (x::xs) (y::ys) base 0 halt hblt hb (Nat.lt_trans (by decide) hb))
      ).mpr h1
    match g : addAux (x::xs) (y::ys) base 0 halt hblt hb (Nat.lt_trans (by decide) hb) with
    | [] => contradiction
    | d::ds =>
      simp_all only [reduceCtorEq, and_self, and_false, not_false_eq_true, ne_eq, List.cons.injEq]
      rw [ih]
      sorry

theorem addAux_cons {xs ys : List Nat} {x y base carry : Nat} (hxlt : (x::xs).all (· < base)) (hylt : (y::ys).all (· < base)) (hb : 1 < base) (hc : carry < base) :
  addAux (x::xs) (y::ys) base carry hxlt hylt hb hc
    = addNatAux (x + y + carry)
        (0::(addAux xs ys base 0 (allDigitsLtBase_cons.mp hxlt).right (allDigitsLtBase_cons.mp hylt).right hb (Nat.lt_trans (by decide) hb)))
        base hb := by
  rw [addAux, addNatAux, Nat.add_zero, Numeral.addNatAux.eq_def]
  simp_all
  sorry
-/

end AddAux

section OfNat

def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : Numeral where
  digits := addAux [] [] n base hb
  base := base
  baseGtOne := hb
  allDigitsLtBase := sorry -- all_addNatAux_lt_base hb
  noTrailingZeros := sorry -- addNatAux_nil_noTrailingZeros hb

@[simp]
theorem ofNat_base_eq_base (n : Nat) (base : Nat) (hb : 1 < base) : (ofNat n base hb).base = base := by
  unfold ofNat
  rfl

/-
@[simp]
theorem toNat_leftInverse_ofNat {n base : Nat} (hb : 1 < base) : toNat (ofNat n base hb) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    if h : n = 0 then
      unfold ofNat
      have : addNatAux 0 [] base hb = [] := (addNatAux_nil_iff_and_zero_nil 0 [] hb).mpr (And.intro rfl rfl)
      simp only [h, this]
      unfold toNat toNat.helper
      rfl
    else
      have h0 : 0 < n := Nat.pos_iff_ne_zero.mpr h
      have h1 : n / base * base ≤ n := Nat.div_mul_le_self n base
      have h2 : n = n % base + (n / base) * base := by rw [Nat.mod_eq_sub_div_mul, Nat.sub_add_cancel h1]
      unfold ofNat toNat at ⊢ ih
      simp only at ⊢ ih
      if g: n % base = 0 then
        have h3 : base ≤ n := Nat.le_of_mod_lt (by rwa [← g] at h0)
        rw [addNatAux_eq_cons_zero_addNatAux n hb (And.intro h3 g)]
        rw [toNat_helper_cons (addNatAux (n / base) [] base hb) 0 base]
        rw [ih (n / base) (Nat.div_lt_self h0 hb)]
        simp only [Nat.zero_add, Nat.mul_div_eq_iff_dvd.mpr (Nat.dvd_of_mod_eq_zero g)]
      else
        have h4 : 0 < n % base := Nat.pos_iff_ne_zero.mpr g
        have h5 : n % base < base := Nat.mod_lt n (Nat.lt_trans (by decide) hb)
        rw [h2, addNatAux_add_eq_append_addNatAux_addNatAux (n % base) (n / base) hb (And.intro h4 h5)]
        rw [addNatAux_eq_singleton (n % base) hb (And.intro h4 h5), List.singleton_append]
        rw [toNat_helper_cons (addNatAux (n / base) [] base hb) (n % base) base]
        rw [ih (n / base) (Nat.div_lt_self h0 hb)]
        simp only [Nat.mul_comm]
-/
end OfNat

section Rebase

def rebase (n : Numeral) (base : Nat) (hb : 1 < base) : Numeral :=
  ofNat (n.toNat) base hb

@[simp]
theorem rebase_base_eq_base (n : Numeral) (base : Nat) (hb : 1 < base) : (rebase n base hb).base = base := by
  unfold rebase ofNat toNat
  rfl

end Rebase

section Add

def add (a b : Numeral) (h : a.base = b.base) : Numeral where
  digits := addAux a.digits b.digits 0 a.base a.baseGtOne
  base := a.base
  baseGtOne := a.baseGtOne
  allDigitsLtBase := sorry /-
    all_addAux_digits_lt_base a.digits b.digits a.base 0
      a.allDigitsLtBase (by simp only [h, b.allDigitsLtBase])
      a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne)
    -/
  noTrailingZeros := sorry /-
    addAux_noTrailingZeros_of_noTrailingZeros
      a.digits b.digits a.base 0
      a.allDigitsLtBase (by simp only [h, b.allDigitsLtBase])
      a.noTrailingZeros b.noTrailingZeros
      a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne)
    -/

/-
@[simp]
theorem add_nil_iff_and_nil_nil (a b : Numeral) (h : a.base = b.base) :
  (add a b h).digits = [] ↔ a.digits = [] ∧ b.digits = [] := by
  unfold add
  simp only [addAux_nil_iff_and_zero_nil_nil, true_and]

@[simp]
theorem add_zero_iff_or_zero_zero (a b : Numeral) (h : a.base = b.base) :
  (add a b h).digits = [0]
    ↔ a.digits = [0] ∧ b.digits = [] ∨ a.digits = [] ∧ b.digits = [0] ∨ a.digits = [0] ∧ b.digits = [0] := by
  unfold add
  simp only [addAux_eq_zero_iff, true_and]

@[simp]
theorem add_comm (a b : Numeral) (h : a.base = b.base) : add a b h = add b a (by simp only [h]) := by
  have hblt : (b.digits.all fun x ↦ decide (x < b.base)) = true := b.allDigitsLtBase
  have hblt' : (b.digits.all fun x ↦ decide (x < a.base)) = true := by rwa [← h] at hblt
  have hd : addAux a.digits b.digits a.base 0
              a.allDigitsLtBase (by simp only [h, b.allDigitsLtBase])
              a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne)
              = addAux b.digits a.digits a.base 0
                  hblt' a.allDigitsLtBase
                  a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne) :=
                addAux_comm a.digits b.digits a.base 0
                  a.allDigitsLtBase hblt'
                  a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne)
  unfold add
  simp only [hd]
  simp only [h]

/-
theorem add_cons ()

-/
def hAdd (a b : Numeral) : Numeral :=
  if h : a.base = b.base then
    add a b h
  else
    if a.base < b.base then
      add (rebase a b.base b.baseGtOne) b rfl
    else
      add a (rebase b a.base a.baseGtOne) rfl

@[simp]
theorem hAdd_comm (a b : Numeral) : hAdd a b = hAdd b a := by
  unfold hAdd
  if  h : a.base = b.base then
    simp only [h]
    exact add_comm a b h
  else
    if g : a.base < b.base then
      have g' : ¬ b.base < a.base := Nat.not_lt_of_gt g
      simp only [h, ↓reduceDIte, g, ↓reduceIte, eq_comm, g']
      have harb : (rebase a b.base b.baseGtOne).base = b.base := rebase_base_eq_base a b.base b.baseGtOne
      exact add_comm (rebase a b.base b.baseGtOne) b harb
    else
      have he : a.base = b.base ↔ b.base = a.base := eq_comm
      have h' : ¬b.base = a.base := (iff_iff_iff_not_not.mp he).mp h
      have g' : b.base ≤ a.base := Nat.le_of_not_lt g
      have g'' : b.base < a.base := Nat.lt_of_le_of_ne g' h'
      simp only [h, g, g'', ↓reduceDIte, ↓reduceIte, eq_comm]
      have hbrb : (rebase b a.base a.baseGtOne).base = a.base := rebase_base_eq_base b a.base a.baseGtOne
      exact add_comm (rebase b a.base a.baseGtOne) a hbrb

instance instCommutativeHAddNumerals : Std.Commutative hAdd := ⟨hAdd_comm⟩
instance instHAddNumerals : HAdd Numeral Numeral Numeral := ⟨hAdd⟩

-- @[simp]
theorem toNat_add_left_distrib (a b : Numeral) (h : a.base = b.base) : toNat (add a b h) = a.toNat + b.toNat := by
  have h0 : 0 < a.base := Nat.lt_trans (by decide) a.baseGtOne
  induction ga : a.digits with
  | nil =>
    have : addAux [] b.digits a.base 0 (by simp [List.all_nil]) (by simp only [h, b.allDigitsLtBase])
            a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne)
              = b.digits := addAux_nil_eq a.baseGtOne (by simp only [h, b.allDigitsLtBase])
    simp only [add, toNat, ga, this, toNat_helper_nil, Nat.zero_add]
    rw [h]
  | cons head tail ih =>
    simp only [add, toNat]
    simp only [ga]
    rw [Numeral.addAux.eq_def]
    sorry

  /-
  match ga : a.digits, gb : b.digits with
  | [], [] =>
    have : (addNatAux 0 [] a.base a.baseGtOne) = [] := by simp only [addNatAux_nil_iff_and_zero_nil, and_self]
    simp only  [add, toNat, ga, gb, addAux, this, toNat_helper_nil]
  | x::xs, [] =>
    have : (addNatAux 0 (x::xs) a.base a.baseGtOne) = x::xs := by
      rw [← ga]
      exact addNatAux_zero_eq_of_all_lt_base a.baseGtOne a.allDigitsLtBase
    simp only [add, toNat, this, ga, gb, addAux, toNat_helper_nil, Nat.add_zero]
  | [], y::ys =>
    have : (addNatAux 0 (y::ys) b.base b.baseGtOne) = y::ys := by
      rw [← gb]
      exact addNatAux_zero_eq_of_all_lt_base b.baseGtOne b.allDigitsLtBase
    simp only [add, toNat, ga, gb, addAux, toNat_helper_nil, h, this, Nat.zero_add]
  | x::xs, y::ys =>
    simp only [add, toNat, ga, gb, addAux]
    sorry
  -/
-/

end Add


end Numeral
end Numerals
