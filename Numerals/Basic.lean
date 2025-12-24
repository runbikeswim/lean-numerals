/-
Copyright (c) 2025 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

section BasicLemmas

@[simp]
theorem or_elim_of_not {p q : Prop} (h : p ∨ q) (g : ¬ p) : q :=
  Or.elim h (fun t : p => False.elim (g t)) id

@[simp]
theorem iff_iff_iff_not_not {p q : Prop} : (p ↔ q) ↔ (¬p ↔ ¬q) := by
  constructor
  · intro h
    exact not_congr h
  · intro h
    have h' : ¬¬p ↔ ¬¬q := not_congr h
    rwa [Classical.not_not, Classical.not_not] at h'

end BasicLemmas

section NatLemmas

@[simp]
theorem Nat.pos_of_one_lt {a : Nat} (h : 1 < a) : 0 < a := (Nat.lt_trans (by decide)) h

@[simp]
theorem Nat.div_ne_zero {a b : Nat} (h1 : b ≠ 0) (h2 : ¬ a < b) : ¬ a / b = 0  :=
  Nat.div_ne_zero_iff.mpr (And.intro h1 (Nat.le_of_not_lt h2))

@[simp]
theorem Nat.eq_zero_of_lt_of_mod_eq_zero {a b : Nat}
  (h1 : 1 < b) (h2 : a % b = 0) (h3 : b = 0 ∨ a < b) : a = 0 := by
  have h4 : b ∣ a  := Nat.dvd_iff_mod_eq_zero.mpr h2
  have h5 : a < b := or_elim_of_not h3 (Nat.ne_zero_of_lt h1)
  exact Nat.eq_zero_of_dvd_of_lt h4 h5

@[simp]
theorem Nat.ne_zero_mod_of_ne_zero {a b : Nat}
  (h1 : 1 < b) (h2 : a / b = 0) (h3 : a ≠ 0) : a % b ≠ 0 := by
  have h4 : a < b := Nat.lt_of_div_eq_zero (Nat.pos_of_one_lt h1) h2
  false_or_by_contra; rename _ => h5
  have h6 : a = 0 := Nat.eq_zero_of_lt_of_mod_eq_zero h1 h5 (Or.inr h4)
  contradiction

@[simp]
theorem Nat.lt_sub_3_mul_3_mul {a : Nat}
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
theorem Nat.lt_sum_div_base_of_lt_base {a b c base : Nat}
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

theorem div_add_mul_eq (n m : Nat) {base : Nat} (hn: n < base) : (n + m * base) / base = m := by
  induction m with
  | zero => simp only [Nat.zero_mul, Nat.add_zero]; exact Nat.div_eq_of_lt hn
  | succ m ih => sorry

end NatLemmas

section ListLemmas

@[simp]
theorem List.cons_singleton_iff_and_eq_nil {α : Type} {a b : α} {as : List α} :
  (a::as = [b]) ↔ (a = b ∧ as = []) := by simp only [cons.injEq]

@[simp]
theorem List.getLast_cons_of_singleton {α : Type} (a: α) {b: α} {as : List α} (h : as = [b]) :
  (a::as).getLast (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) = b := by
  have g : as ≠ [] := by simp only [h, ne_eq, cons_ne_self, not_false_eq_true]
  have : as.getLast g = b := by simp only [h, getLast_singleton]
  rwa [List.getLast_cons g]

end ListLemmas

section Numerals

structure Numeral where
  digits : List Nat
  base: Nat := 10
  baseGtOne : 1 < base
  allDigitsLtBase : digits.all (· < base)
  noTrailingZeros : (h : digits ≠ []) → digits ≠ [0] → digits.getLast h ≠ 0
deriving Repr, DecidableEq

namespace Numeral

instance : Inhabited Numeral := ⟨{
    digits := [0],
    base := 10,
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, List.cons_ne_self,
                        not_false_eq_true, not_true_eq_false,
                        List.getLast_singleton, imp_self]
  }⟩

def isZero (a : Numeral) : Prop := a.digits = [] ∨ a.digits = [0]

def nil : Numeral := {
              digits := [],
              baseGtOne := by decide,
              allDigitsLtBase := by decide,
              noTrailingZeros := by simp only [ne_eq, not_true_eq_false, List.ne_cons_self,
                                  not_false_eq_true, forall_const, forall_false]
            }

def zero : Numeral := default

def one : Numeral := {
              digits := [1],
              baseGtOne := by decide,
              allDigitsLtBase := by decide,
              noTrailingZeros := by simp only [ne_eq, List.cons_ne_self, not_false_eq_true,
                                  List.cons.injEq, Nat.succ_ne_self, and_true,
                                  List.getLast_singleton, imp_self]
            }

def four : Numeral := {
                digits := [0, 0, 1],
                base := 2
                baseGtOne := by decide,
                allDigitsLtBase := by decide,
                noTrailingZeros := by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                                    List.cons.injEq, and_false, List.getLast_cons_cons, and_true,
                                    List.getLast_cons_of_singleton, Nat.succ_ne_self, imp_self]
              }

def twelve : Numeral := {
                digits := [2, 1],
                baseGtOne := by decide,
                allDigitsLtBase := by decide,
                noTrailingZeros := by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                                    List.cons.injEq, List.cons_ne_self, and_self, and_true,
                                    List.getLast_cons_of_singleton, Nat.succ_ne_self, imp_self]
              }

def thirteen : Numeral := {
                digits := [5, 1],
                base := 8
                baseGtOne := by decide,
                allDigitsLtBase := by decide,
                noTrailingZeros := by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                                    List.cons.injEq, List.cons_ne_self, and_self, and_true,
                                    List.getLast_cons_of_singleton, Nat.succ_ne_self, imp_self]
              }

def abcdef : Numeral := {
                digits := [15, 14, 13, 12, 11, 10],
                base := 16,
                baseGtOne := by decide,
                allDigitsLtBase := by decide,
                noTrailingZeros := by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                                    List.cons.injEq, and_self, List.getLast_cons_cons, and_true,
                                    List.getLast_cons_of_singleton, imp_self]
              }

def threeHundredSixty : Numeral := {
                digits := [0, 6],
                base := 60,
                baseGtOne := by decide,
                allDigitsLtBase := by decide,
                noTrailingZeros := by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                                    List.cons.injEq, List.cons_ne_self, and_false, and_true,
                                    List.getLast_cons_of_singleton, imp_self]
              }

def toString (n : Numeral) : String :=
  helper n.digits.reverse n.base where
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
          | _ => "?"
        s!"{String.join (l.map toHexDigit)}(16)"
    | _ => ",".intercalate (l.map (fun d : Nat => s!"{d}")) ++ s!"({b})"

instance : ToString Numeral := ⟨toString⟩

@[simp]
def allDigitsLtBase_cons {n base : Nat} {d : List Nat} :
  (n::d).all (· < base) ↔ n < base ∧ d.all (· < base) := by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]

@[simp]
theorem noTrailingZeros_cons_of_ne_zero (n : Nat) {d : List Nat} (hdnz : d ≠ [0])
  (hdntz : (hdnn : d ≠ []) → d ≠ [0] → d.getLast hdnn ≠ 0):
  (h : n::d ≠ []) → n::d ≠ [0] → (n::d).getLast h ≠ 0 := by
  intro h hndnz
  match d with
  | [] =>
    have hnn : ¬ n = 0 := by rwa [← List.singleton_inj]
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

def mul_base (a : Numeral) : Numeral :=
  if h : a.digits = [] ∨ a.digits = [0] then
    a
  else {
    digits := 0::a.digits
    base := a.base
    baseGtOne := a.baseGtOne
    allDigitsLtBase := allDigitsLtBase_cons.mpr (
        And.intro
          (Nat.lt_trans (by decide) (a.baseGtOne))
          a.allDigitsLtBase
      )
    noTrailingZeros := (noTrailingZeros_cons_of_ne_zero 0 (not_or.mp h).right a.noTrailingZeros)
  }

def div_base (a : Numeral) : Numeral :=
  match g : a.digits with
  | [] | [0] => a
  | head::tail => {
      digits := tail,
      base := a.base,
      baseGtOne := a.baseGtOne,
      allDigitsLtBase := by
        have h0 : (a.digits.all fun x ↦ decide (x < a.base)) = true := a.allDigitsLtBase
        have h1 : (head::tail).all (· < a.base) := by rwa [g] at h0
        exact (allDigitsLtBase_cons.mp h1).right
      noTrailingZeros := by
        have h0 : ∀ (h : a.digits ≠ []), a.digits ≠ [0] → a.digits.getLast h ≠ 0 := a.noTrailingZeros
        have h1 : (h: head::tail ≠ []) → head::tail ≠ [0] → (head::tail).getLast h ≠ 0 := by rwa [g] at h0
        exact noTrailingZeros_of_noTrailingZeros_cons h1
    }

def toNat (n : Numeral) : Nat :=
  (helper n.digits 1 0).1 where
    helper (d : List Nat) (b : Nat) (r : Nat) : Nat × Nat :=
      match d with
      | [] => (r, b)
      | a::as => helper as (b * n.base) (a * b + r)

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
theorem addNatAux_eq_cons_zero_addNatAux (n : Nat) {base : Nat} (hb : 1 < base) (hn : base ≤ n ∧ n % base = 0) :
  addNatAux n [] base hb = 0::(addNatAux (n / base) [] base hb) := by
  rw [addNatAux]
  have hne : n ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr (Nat.pos_of_one_lt (Nat.lt_of_lt_of_le hb hn.left))
  simp only [hne, ↓reduceDIte, hn.right]

@[simp]
theorem addNatAux_eq_singleton (n : Nat) {base : Nat} (hb : 1 < base) (hn : 0 < n ∧ n < base) :
  addNatAux n [] base hb = [n] := by
  have he : n % base = n := Nat.mod_eq_of_lt hn.right
  have hne : n ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr hn.left
  have hdz : n / base = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hn.right)
  have hnil : addNatAux 0 [] base hb = [] := (addNatAux_nil_iff_and_zero_nil 0 [] hb).mpr (And.intro rfl rfl)
  rw [addNatAux, he]
  simp only [hne, ↓reduceDIte, hdz, hnil]

theorem addNatAux_add_eq_append_addNatAux_addNatAux (n m : Nat) {base : Nat} (hb : 1 < base) (hn : 0 < n ∧ n < base) :
  addNatAux (n + m * base) [] base hb = addNatAux n [] base hb ++ addNatAux m [] base hb := by
  have hb': 0 < base := Nat.lt_trans (by decide) hb
  have hs : addNatAux n [] base hb = [n] := addNatAux_eq_singleton n hb hn
  have hac : addNatAux n [] base hb ++ addNatAux m [] base hb = n::(addNatAux m [] base hb) := by
    rw [hs, List.singleton_append]
  have hnz : 0 < n + m * base := by
    calc 0 < n := hn.left
      _ ≤ n + m * base := Nat.le_add_right n (m * base)
  have hnr : ¬ base ≤ n := by simp only [Nat.not_le, hn.right]
  have hme: (n + m * base) % base = n := mod_add_mul_eq n m hn.right
  have hde : (n + m * base) / base = m := div_add_mul_eq n m hn.right
  rw [hac, addNatAux, hme]
  simp only [Nat.ne_zero_of_lt hnz, ↓reduceDIte, hde]

def ofNat (n : Nat) (base : Nat) (hb : 1 < base) : Numeral where
  digits := addNatAux n [] base hb
  base := base
  baseGtOne := hb
  allDigitsLtBase := all_addNatAux_lt_base hb
  noTrailingZeros := addNatAux_nil_noTrailingZeros hb

@[simp]
theorem ofNat_base_eq_base (n : Nat) (base : Nat) (hb : 1 < base) : (ofNat n base hb).base = base := by
  unfold ofNat
  rfl

-- @[simp]
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
      have : n / base * base ≤ n := Nat.div_mul_le_self n base
      have : n = n % base + (n / base) * base := by rw [Nat.mod_eq_sub_div_mul, Nat.sub_add_cancel this]
      unfold ofNat
      sorry

def rebase (n : Numeral) (base : Nat) (hb : 1 < base) : Numeral :=
  ofNat (n.toNat) base hb

@[simp]
theorem rebase_base_eq_base (n : Numeral) (base : Nat) (hb : 1 < base) : (rebase n base hb).base = base := by
  unfold rebase ofNat toNat
  rfl

def addAux (a b : List Nat) (base carry : Nat)
  (halt : a.all (· < base)) (hblt : b.all (· < base))
  (hb : 1 < base) (hc : carry < base) : List Nat :=
  match a, b with
  | [], [] => addNatAux carry [] base hb
  | x::xs, [] => addNatAux carry (x::xs) base hb
  | [], y::ys => addNatAux carry (y::ys) base hb
  | x::xs, y::ys =>
    let s := x + y + carry
    let carry' := s / base
    have hc' : carry' < base := by
      simp only [carry', s]
      exact (Nat.lt_sum_div_base_of_lt_base
              (allDigitsLtBase_cons.mp halt).left (allDigitsLtBase_cons.mp hblt).left hc hb)
    (s % base) :: (addAux xs ys base carry'
      (allDigitsLtBase_cons.mp halt).right (allDigitsLtBase_cons.mp hblt).right hb hc')

@[simp]
theorem addAux_comm (a b : List Nat) (base carry : Nat)
  (halt : a.all (· < base)) (hblt : b.all (· < base))
  (hb : 1 < base) (hc : carry < base) :
  addAux a b base carry halt hblt hb hc = addAux b a base carry hblt halt hb hc := by
  fun_induction addAux a b base carry halt hblt hb hc with
  | case1 => unfold addAux; rfl
  | case2 => unfold addAux; rfl
  | case3 => unfold addAux; rfl
  | case4 carry hc x xs y ys halt hblt s carry' hc' ih =>
    unfold addAux
    simp only [List.cons.injEq]
    simp only [s, carry'] at hc'
    have halt' : xs.all (· < base) := (allDigitsLtBase_cons.mp halt).right
    have hblt' : ys.all (· < base) := (allDigitsLtBase_cons.mp hblt).right
    have hxy : x + y = y + x := Nat.add_comm x y
    have hcarry' : (y + x + carry) / base = carry' := by rw [← hxy]
    have hc'' : (y + x + carry) / base < base := by rwa [← hxy];
    have hl : (x + y + carry) % base = (y + x + carry) % base := by rw [hxy]
    have hr : addAux xs ys base ((x + y + carry) / base) halt' hblt' hb hc' = addAux ys xs base ((y + x + carry) / base) hblt' halt' hb hc'' := by
      simp_all only []
    exact And.intro hl hr

@[simp]
theorem all_addAux_digits_lt_base (a b : List Nat) (base carry: Nat)
  (halt : a.all (· < base)) (hblt : b.all (· < base))
  (hb : 1 < base) (hc : carry < base) :
  (addAux a b base carry halt hblt hb hc).all (· < base) := by
  fun_induction addAux with
  | case1 => exact all_addNatAux_lt_base hb
  | case2 => simp_all only [all_addNatAux_lt_base]
  | case3 => simp_all only [List.all_nil, all_addNatAux_lt_base]
  | case4 carry hc x xs y ys halt' hblt' s carry' hc' ih =>
    have h1 : s % base < base := Nat.mod_lt s (Nat.pos_of_one_lt hb)
    exact allDigitsLtBase_cons.mpr (And.intro h1 ih)

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

@[simp]
theorem addAux_eq_zero_iff (a b : List Nat) (base carry : Nat)
  (halt : a.all (· < base)) (hblt : b.all (· < base))
  (hb : 1 < base) (hc : carry < base) :
  addAux a b base carry halt hblt hb hc = [0] ↔
    carry = 0 ∧ (a = [0] ∧ b = [] ∨ a = [] ∧ b = [0] ∨ a = [0] ∧ b = [0]) := by
  unfold addAux
  constructor
  · intro h
    match ga : a, gb : b, halt, hblt with
    | [], [], halt, hblt => simp only [addNatAux_zero_iff_and_zero_zero, List.ne_cons_self, and_false] at h
    | x::xs, [], halt, hblt =>
      simp_all only [addNatAux_zero_iff_and_zero_zero, List.cons.injEq, and_self, List.cons_ne_self,
        List.ne_cons_self, and_false, or_self, or_false]
    | [], y::ys, halt, hblt =>
      simp_all only [or_true, addNatAux_zero_iff_and_zero_zero, List.cons.injEq, List.ne_cons_self,
        List.cons_ne_self, and_self, and_true, or_false]
    | x::xs, y::ys, halt, hblt =>
      simp only [List.cons.injEq] at h
      simp only [List.cons.injEq]
      have hc' : (x + y + carry) / base < base :=
        (Nat.lt_sum_div_base_of_lt_base
        (allDigitsLtBase_cons.mp halt).left (allDigitsLtBase_cons.mp hblt).left hc hb)
      have halt' : xs.all (· < base) := (allDigitsLtBase_cons.mp halt).right
      have hblt' : ys.all (· < base) := (allDigitsLtBase_cons.mp hblt).right
      have h1 : (x + y + carry) / base = 0 ∧ xs = [] ∧ ys = [] :=
        (addAux_nil_iff_and_zero_nil_nil xs ys base ((x + y + carry) / base) halt' hblt' hb hc').mp h.right
      have h2 : x + y + carry < base := Nat.lt_of_div_eq_zero (Nat.lt_trans (by decide) hb) h1.left
      have h3 : x + y + carry = 0 := Nat.eq_zero_of_lt_of_mod_eq_zero hb h.left (Or.inr h2)
      have h4 : x + y = 0 := (Nat.eq_zero_of_add_eq_zero h3).left
      have h5 : x = 0 ∧ y = 0 := Nat.eq_zero_of_add_eq_zero h4
      have h6 : (x = 0 ∧ xs = []) ∧ y = 0 ∧ ys = [] := And.intro (And.intro h5.left h1.right.left) (And.intro h5.right h1.right.right)
      have h7 : carry = 0 := (Nat.eq_zero_of_add_eq_zero h3).right
      exact And.intro h7 (Or.inr (Or.inr h6))
  · intro h
    have h1 : carry = 0 := h.left
    match ga: a, gb : b with
    | [], [] => simp_all only [List.ne_cons_self, and_true, and_false, and_self, or_self]
    | x::xs, [] => simp_all only [List.cons.injEq, and_true, reduceCtorEq, List.ne_cons_self, and_self,
        and_false, or_self, or_false, addNatAux_zero_iff_and_zero_zero]
    | [], y::ys => simp_all only [List.ne_cons_self, reduceCtorEq, and_self, List.cons.injEq,
        true_and, false_and, or_false, false_or, addNatAux_zero_iff_and_zero_zero]
    | x::xs, y::ys => simp_all only [List.cons.injEq, reduceCtorEq, and_false, false_and,
        false_or, Nat.add_zero, Nat.zero_mod, Nat.zero_div, addAux_nil_iff_and_zero_nil_nil, and_self]

@[simp]
theorem addAux_noTrailingZeros_of_noTrailingZeros
  (a b : List Nat) (base carry: Nat)
  (halt : a.all (· < base)) (hblt : b.all (· < base))
  (hantz : (h : a ≠ []) → a ≠ [0] → a.getLast h ≠ 0)
  (hbntz : (h : b ≠ []) → b ≠ [0] → b.getLast h ≠ 0)
  (hb : 1 < base) (hc : carry < base) :
  (h : addAux a b base carry halt hblt hb hc ≠ [])
    → addAux a b base carry halt hblt hb hc ≠ [0]
      → (addAux a b base carry halt hblt hb hc).getLast h ≠ 0 := by
  fun_induction addAux with
  | case1 carry =>
    exact addNatAux_noTrailingZeros_of_noTrailingZeros carry hb hantz
  | case2 carry hc xs =>
    intro h g
    simp only [ne_eq] at ⊢ h g
    exact (addNatAux_noTrailingZeros_of_noTrailingZeros carry hb hantz) h g
  | case3 carry hc ys =>
    intro h g
    simp only [ne_eq] at ⊢ h g
    exact (addNatAux_noTrailingZeros_of_noTrailingZeros carry hb hbntz) h g
  | case4 carry hc x xs y ys halt hblt s carry' hc' ih =>
    simp only [ne_eq]
    have halt' : xs.all (· < base) := (allDigitsLtBase_cons.mp halt).right
    have hblt' : ys.all (· < base) := (allDigitsLtBase_cons.mp hblt).right
    have hantz' : ∀ (hdnn : xs ≠ []), xs ≠ [0] → xs.getLast hdnn ≠ 0 := noTrailingZeros_of_noTrailingZeros_cons hantz
    have hbntz' : ∀ (hdnn : ys ≠ []), ys ≠ [0] → ys.getLast hdnn ≠ 0 := noTrailingZeros_of_noTrailingZeros_cons hbntz
    have hxsnz : xs ≠ [0] := ne_zero_of_noTrailingZeros_cons hantz
    have hysnz : ys ≠ [0] := ne_zero_of_noTrailingZeros_cons hbntz
    have h1 : ¬((x + y + carry) / base = 0 ∧ (xs = [0] ∧ ys = [] ∨ xs = [] ∧ ys = [0] ∨ xs = [0] ∧ ys = [0])) := by
      simp only [Nat.div_eq_zero_iff, hxsnz, false_and, hysnz, and_false, and_self, or_self, not_false_eq_true]
    have h2 : addAux xs ys base ((x + y + carry) / base) halt' hblt' hb hc'≠ [0] :=
      (iff_iff_iff_not_not.mp (addAux_eq_zero_iff xs ys base ((x + y + carry) / base) halt' hblt' hb hc')).mpr h1
    exact noTrailingZeros_cons_of_ne_zero ((x + y + carry) % base) h2 (ih hantz' hbntz')

def add (a b : Numeral) (h : a.base = b.base) : Numeral where
    digits := addAux a.digits b.digits a.base 0
                a.allDigitsLtBase (by simp only [h, b.allDigitsLtBase])
                a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne)
    base := a.base
    baseGtOne := a.baseGtOne
    allDigitsLtBase := all_addAux_digits_lt_base a.digits b.digits a.base 0
                        a.allDigitsLtBase (by simp only [h, b.allDigitsLtBase])
                        a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne)
    noTrailingZeros := addAux_noTrailingZeros_of_noTrailingZeros
                        a.digits b.digits a.base 0
                        a.allDigitsLtBase (by simp only [h, b.allDigitsLtBase])
                        a.noTrailingZeros b.noTrailingZeros
                        a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne)

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

theorem tbd_05 {n : Nat} {a : Numeral} :
  addNatAux n a.digits a.base a.baseGtOne
    = (add (ofNat n a.base a.baseGtOne) a (ofNat_base_eq_base n a.base a.baseGtOne)).digits := by
  sorry

theorem add_eq_left (a b : Numeral) (h : a.base = b.base) : add a b h = a ↔ (b.isZero) := by
  constructor
  · intro g
    unfold isZero
    -- unfold add at g
    have hd : addAux a.digits b.digits a.base 0
                a.allDigitsLtBase (by simp only [h, b.allDigitsLtBase])
                a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne) = a.digits := by

      simp_all
      sorry
    sorry
  · intro g
    unfold isZero at g
    unfold add
    sorry

@[simp]
theorem add_comm (a b : Numeral) (h : a.base = b.base) : add a b h = add b a (by simp only [h]) := by
  have hblt : (b.digits.all fun x ↦ decide (x < b.base)) = true := b.allDigitsLtBase
  have hblt' : (b.digits.all fun x ↦ decide (x < a.base)) = true := by rwa [← h] at hblt
  have hd : addAux a.digits b.digits a.base 0
              a.allDigitsLtBase (by simp only [h, b.allDigitsLtBase])
              a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne) =
            addAux b.digits a.digits a.base 0
              hblt' a.allDigitsLtBase
              a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne) :=
            addAux_comm a.digits b.digits a.base 0
              a.allDigitsLtBase hblt'
              a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne)
  unfold add
  simp only [hd]
  simp only [h]

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
      have h' : ¬ b.base = a.base := (iff_iff_iff_not_not.mp he).mp h
      have g' : b.base ≤ a.base := Nat.le_of_not_lt g
      have g'' : b.base < a.base := Nat.lt_of_le_of_ne g' h'
      simp only [h, g, g'', ↓reduceDIte, ↓reduceIte, eq_comm]
      have hbrb : (rebase b a.base a.baseGtOne).base = a.base := rebase_base_eq_base b a.base a.baseGtOne
      exact add_comm (rebase b a.base a.baseGtOne) a hbrb

instance : Std.Commutative hAdd := ⟨hAdd_comm⟩
instance : HAdd Numeral Numeral Numeral := ⟨hAdd⟩

-- @[simp]
theorem toNat_left_distrib (a b : Numeral) (h : a.base = b.base) : toNat (add a b h) = a.toNat + b.toNat := by
  match ga : a.digits, gb : b.digits with
  | [], [] =>
    unfold add toNat
    simp only [ga, gb]
    have hblt : (b.digits.all fun x ↦ decide (x < b.base)) = true := b.allDigitsLtBase
    have hblt' : (b.digits.all fun x ↦ decide (x < a.base)) = true := by rwa [← h] at hblt
    have x := addAux_nil_iff_and_zero_nil_nil a.digits b.digits a.base 0 a.allDigitsLtBase hblt' a.baseGtOne (Nat.lt_trans (by decide) a.baseGtOne)
    sorry
  | x::xs, [] => sorry
  | [], y::ys => sorry
  | x::xs, y::ys => sorry


end Numeral

end Numerals
