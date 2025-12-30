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

theorem addAux_nil_iff_and_zero_nil_nil {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = [] ↔ n = 0 ∧ a = [] ∧ b = []  := by
  constructor
  · intro h
    unfold addAux at h
    sorry
  · intro h
    unfold addAux
    sorry

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
  | case2 k hn0 hltn ih => sorry
  | case3 => sorry
  | case4 => sorry
  | case5 => sorry

end AddAux

section OfNat

def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : Numeral where
  digits := addAux [] [] n base hb
  base := base
  baseGtOne := hb
  allDigitsLtBase := sorry
  noTrailingZeros := sorry

theorem toNat_leftInverse_ofNat {n base : Nat} (hb : 1 < base) : toNat (ofNat n base hb) = n := by
  sorry

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
  allDigitsLtBase := sorry
  noTrailingZeros := sorry

theorem add_nil_iff_and_nil_nil (a b : Numeral) (h : a.base = b.base) :
  (add a b h).digits = [] ↔ a.digits = [] ∧ b.digits = [] := by
  unfold add
  simp only [addAux_nil_iff_and_zero_nil_nil, true_and]

theorem add_zero_iff_or_zero_zero (a b : Numeral) (h : a.base = b.base) :
  (add a b h).digits = [0]
    ↔ a.digits = [0] ∧ b.digits = [] ∨ a.digits = [] ∧ b.digits = [0] ∨ a.digits = [0] ∧ b.digits = [0] := by
  unfold add
  simp only [addAux_eq_zero_iff, true_and]

theorem add_comm (a b : Numeral) (h : a.base = b.base) : add a b h = add b a (by simp only [h]) := by
  have hblt : (b.digits.all fun x ↦ decide (x < b.base)) = true := b.allDigitsLtBase
  have hblt' : (b.digits.all fun x ↦ decide (x < a.base)) = true := by rwa [← h] at hblt
  sorry

def hAdd (a b : Numeral) : Numeral :=
  if h : a.base = b.base then
    add a b h
  else
    if a.base < b.base then
      add (rebase a b.base b.baseGtOne) b rfl
    else
      add a (rebase b a.base a.baseGtOne) rfl

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

theorem toNat_add_left_distrib (a b : Numeral) (h : a.base = b.base) : toNat (add a b h) = a.toNat + b.toNat := by
  have h0 : 0 < a.base := Nat.lt_trans (by decide) a.baseGtOne
  induction ga : a.digits with
  | nil => sorry
  | cons head tail ih =>
    simp only [add, toNat]
    simp only [ga]
    rw [Numeral.addAux.eq_def]
    sorry

end Add

end Numeral
end Numerals
