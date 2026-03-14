/-
Copyright (c) 2025 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

theorem eq_symm {α : Type} {a b : α} : a = b ↔ b = a := by
  constructor
  · intro h
    exact Eq.symm h
  · intro h
    exact Eq.symm h

theorem not_imp_not_and {p q: Prop} : ¬q → ¬(p ∧ q) := by
  intro h
  rw [not_and]
  exact fun t: p => h

namespace  Classical

/-- -/
theorem iff_iff_iff_not_not {p q : Prop} : (p ↔ q) ↔ (¬p ↔ ¬q) := by
  constructor
  · intro h
    exact not_congr h
  · intro h
    have : ¬¬p ↔ ¬¬q := not_congr h
    simp only [Classical.not_not] at this
    assumption

theorem imp_iff_imp_not_not {p q : Prop} : (p → q) ↔ (¬q → ¬p) := by
  rw [← Classical.or_iff_not_imp_left, or_comm, Classical.or_iff_not_imp_left, Classical.not_not]

end Classical

namespace Nat

/-- -/
theorem pos_of_one_lt {a : Nat} (h : 1 < a) : 0 < a := (Nat.lt_trans (by decide)) h

/-- -/
theorem eq_zero_of_lt_of_mod_eq_zero {a b : Nat}
  (h1 : 1 < b) (h2 : a % b = 0) (h3 : a < b) : a = 0 := by
  have h4 : b ∣ a  := Nat.dvd_iff_mod_eq_zero.mpr h2
  have h5 : a < b := Or.resolve_left (.inr h3) (Nat.ne_zero_of_lt h1)
  exact Nat.eq_zero_of_dvd_of_lt h4 h5

/-- -/
theorem ne_zero_mod_of_ne_zero {a b : Nat}
  (h1 : 1 < b) (h2 : a / b = 0) (h3 : a ≠ 0) : a % b ≠ 0 := by
  have h4 : a < b := Nat.lt_of_div_eq_zero (Nat.pos_of_one_lt h1) h2
  false_or_by_contra; rename _ => h5
  have h6 : a = 0 := Nat.eq_zero_of_lt_of_mod_eq_zero h1 h5 h4
  contradiction

theorem add_mul_mod {a b base : Nat} (halt : a < base) : (a + base * b) % base = a := by
  rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt halt]

theorem add_mul_mod_eq_iff_eq_of {a b c d base : Nat} (halt : a < base) (hclt : c < base) :
  (a + base * b) % base = (c + base * d) % base ↔ a = c := by
  rw [add_mul_mod halt, add_mul_mod hclt]

theorem add_mul_div_eq_iff_eq_of {a b c d base : Nat} (halt : a < base) (hclt : c < base) :
  (a + base * b) / base = (c + base * d) / base ↔ b = d := by
  have : 0 < base := Nat.lt_of_le_of_lt (Nat.zero_le a) halt
  rw [Nat.add_mul_div_left a b this, Nat.add_mul_div_left c d this]
  rw [(Nat.div_eq_zero_iff_lt this).mpr halt, Nat.zero_add]
  rw [(Nat.div_eq_zero_iff_lt this).mpr hclt, Nat.zero_add]

theorem add_mod_div_mul {a base : Nat} : a % base + a / base * base = a := by
  rw [Nat.mul_comm]
  exact Nat.mod_add_div a base

theorem eq_mod_of_eq {a b base : Nat} (h: a = b) : a % base = b % base := by
  rw [h]

theorem eq_div_of_eq {a b base : Nat} (h: a = b) : a / base = b / base := by
  rw [h]

theorem add_mul_eq_iff_and_eq_eq_of {a b c d base : Nat} (halt : a < base) (hclt : c < base) :
  a + base * b = c + base * d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h1 : (a + base * b) % base = (c + base * d) % base := eq_mod_of_eq h
    have h2 : (a + base * b) / base = (c + base * d) / base := eq_div_of_eq h
    exact And.intro ((add_mul_mod_eq_iff_eq_of halt hclt).mp h1) ((add_mul_div_eq_iff_eq_of halt hclt).mp h2)
  · intro h
    rw [h.left, h.right]

theorem lt_of_lt_of_ltBase {a b x y base : Nat} (hab : a < b) (hx : x < base) :
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
    have : y + base * b < x + base * a := lt_of_lt_of_ltBase (Nat.lt_of_not_le hc) hy
    exact absurd h (Nat.not_le_of_lt this)
  · intro h
    have : x + base * a < y + base * b := lt_of_lt_of_ltBase (Nat.lt_of_le_of_ne h hab) hx
    exact Nat.le_of_lt this

end Nat

namespace List

/-- -/
theorem cons_singleton_iff_and_eq_nil {α : Type} {a b : α} {as : List α} :
  (a::as = [b]) ↔ (a = b ∧ as = []) := by simp only [cons.injEq]

/-- -/
theorem cons_ne_singleton_iff_or_ne_ne {α : Type} {a b : α} {as : List α} :
  (a::as ≠ [b]) ↔ (a ≠ b ∨ as ≠ []) := by
  have : (a::as = [b]) ↔ (a = b ∧ as = []) := cons_singleton_iff_and_eq_nil
  rw [Classical.iff_iff_iff_not_not, Classical.not_and_iff_not_or_not] at this
  simp_all only [cons.injEq, not_and, ne_eq]

/-- -/
def mapWithAll {α β : Type} (a: List α) (p : α → Bool) (ha : a.all p) (f : (x : α) → (hp : p x) → β): List β :=
  match a with
  | [] => []
  | x::xs =>
    have : p x ∧ xs.all p = true := by rwa [all_cons, Bool.and_eq_true] at ha
    (f x this.left)::(mapWithAll xs p this.right f)

end List

section ToNatAux

/-- -/
def toNatAux (a : List Nat) (base : Nat) : Nat :=
  (helper a base 1 0).snd where
    helper (a : List Nat) (base factor acc : Nat) : Nat × Nat :=
      match a with
      | [] => (factor, acc)
      | x::xs => helper xs base (factor * base) (x * factor + acc)

/-- -/
theorem toNatAux_helper_nil_eq {base factor acc : Nat} : toNatAux.helper [] base factor acc = (factor, acc) := by
  unfold toNatAux.helper
  rfl

/-- -/
theorem toNatAux_helper_eq {a : List Nat} {base factor acc : Nat} :
  (toNatAux.helper a base factor acc).snd = acc + factor * (toNatAux.helper a base 1 0).snd := by
  induction a generalizing factor acc with
  | nil => simp_all only [toNatAux_helper_nil_eq, Nat.mul_zero, Nat.add_zero]
  | cons head tail ih =>
    unfold toNatAux.helper
    simp only [Nat.one_mul, Nat.mul_one, Nat.add_zero]
    rw [ih, Nat.add_comm (head * factor) acc]
    rw (occs := .pos [2]) [ih]
    rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm]

/-- -/
theorem toNatAux_nil {base : Nat} : toNatAux [] base = 0 := by
  unfold toNatAux
  rfl

/-- -/
theorem toNatAux_cons {xs : List Nat} {x base : Nat} :
  toNatAux (x::xs) base = x + base * (toNatAux xs base) := by
  rw [toNatAux.eq_def, toNatAux.helper.eq_def]
  simp only
  rw [toNatAux.eq_def, toNatAux_helper_eq, Nat.mul_one, Nat.one_mul, Nat.add_zero]

end ToNatAux

section Equiv

def equiv (a b : List Nat) : Prop :=
  match a, b with
  | [], [] => True
  | x::xs, [] => x = 0 ∧ equiv xs []
  | [], y::ys => y = 0 ∧ equiv [] ys
  | x::xs, y::ys => x = y ∧ equiv xs ys

theorem equiv_refl {a : List Nat} : equiv a a := by
  induction a with
  | nil => simp only [equiv]
  | cons x xs ih =>
    simp only [equiv, ih, true_and]

theorem equiv_symm {a b : List Nat} (hab : equiv a b) : equiv b a := by
  induction a generalizing b with
  | nil =>
    induction b with
    | nil => exact hab
    | cons y ys ihy =>
      unfold equiv at ⊢ hab
      exact And.intro hab.left (ihy hab.right)
  | cons x xs ihx =>
    match b with
    | [] | y::ys =>
      unfold equiv at ⊢ hab
      rw [hab.left]
      exact And.intro rfl (ihx hab.right)

theorem equiv_iff {a b : List Nat} : equiv a b ↔ equiv b a := by
  constructor
  · intro h
    exact equiv_symm h
  · intro h
    exact equiv_symm h

theorem not_equiv_iff {a b : List Nat} : ¬ equiv a b ↔ ¬ equiv b a :=
  Classical.iff_iff_iff_not_not.mp equiv_iff

theorem equiv_cons_of_equiv {xs : List Nat} (h : equiv xs []) : equiv (0::xs) [] := by
  unfold equiv at ⊢
  exact And.intro rfl h

theorem not_equiv_cons_of_lt {x y : Nat} {xs ys : List Nat} (h : x < y) : ¬ equiv (x::xs) (y::ys) := by
  have : x ≠ y := Nat.ne_of_lt h
  simp only [equiv, Classical.not_and_iff_not_or_not]
  exact .inl this

theorem equiv_trans_nil {a b : List Nat} (ha : equiv [] a) (hab : equiv a b) : equiv [] b := by
  induction a generalizing b with
    | nil => exact hab
    | cons x xs ih =>
      unfold equiv at ha hab
      match b with
      | [] =>
        simp only at hab
        exact ih ha.right hab.right
      | z::zs =>
        unfold equiv
        simp only at ⊢ hab
        have : z = 0 := by rw [ha.left] at hab; exact (Eq.symm hab.left)
        exact And.intro this (ih ha.right hab.right)

theorem equiv_trans {a b c : List Nat} (hab : equiv a b) (hbc :  equiv b c) : equiv a c := by
  induction a generalizing b c with
  | nil => exact equiv_trans_nil hab hbc
  | cons x xs ihx =>
    unfold equiv at ⊢ hab hbc
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

theorem not_equiv_of_equiv_of_not_equiv {a b c : List Nat}
  (hab : equiv a b) (hbc : ¬ equiv b c) : ¬ equiv a c := by
  false_or_by_contra; rename _ => hac
  have : equiv b c := equiv_trans (equiv_symm hab) hac
  contradiction

theorem not_equiv_of_not_equiv_of_equiv {a b c : List Nat}
  (hab : ¬ equiv a b) (hbc : equiv b c) : ¬ equiv a c := by
  false_or_by_contra; rename _ => hac
  have : equiv a b := equiv_trans hac (equiv_symm hbc)
  contradiction

theorem equiv_cons_iff {x y : Nat} {xs ys : List Nat} : equiv (x::xs) (y::ys) ↔ x = y ∧ equiv xs ys := by
  rw [equiv]

def decEquiv_nil (a : List Nat) : Decidable (equiv [] a)  :=
  match a with
  | [] =>
    have : equiv [] [] := by simp only [equiv]
    isTrue this
  | x::xs =>
    if gx : x = 0 then
      match ge : decEquiv_nil xs with
      | isTrue p =>
        have : equiv [] (x::xs) := by
          unfold equiv
          exact And.intro gx p
        isTrue this
      | isFalse p =>
        have : ¬ equiv [] (x::xs) := by
          unfold equiv
          rw [not_and]
          exact fun _ : x = 0 => p
        isFalse this
    else
      have : ¬ equiv [] (x::xs) := by
        unfold equiv
        rw [not_and]
        intro gx'
        contradiction
      isFalse this

def decEquiv (a b : List Nat) : Decidable (equiv a b)  :=
  match a, b with
  | [], [] =>
    have : equiv [] [] := by simp only [equiv]
    isTrue this
  | x::xs, [] =>
    match decEquiv_nil (x::xs) with
    | isFalse p =>
      have : ¬ equiv (x::xs) [] := by
        intro h
        exact absurd (equiv_symm h) p
      isFalse this
    | isTrue p =>
      have : equiv (x::xs) [] := equiv_symm p
      isTrue this
  | [], y::ys => decEquiv_nil (y::ys)
  | x::xs, y::ys =>
    if gxy : x = y then
      match decEquiv xs ys with
      | isFalse p =>
        have : ¬ equiv (x::xs) (y::ys) := by
          intro h
          simp only [equiv] at h
          exact absurd h.right p
        isFalse this
      | isTrue p =>
        have : equiv (x::xs) (y::ys) := by
          simp only [equiv]
          exact And.intro gxy p
        isTrue this
    else
      have : ¬ equiv (x::xs) (y::ys) := by
        intro h
        simp only [equiv] at h
        exact absurd h.left gxy
      isFalse this
  termination_by a.length + b.length

instance instEquiv (a b: List Nat) : Decidable (equiv a b) := decEquiv a b

end Equiv

section IsZeroAux

abbrev isZeroAux (a : List Nat) : Prop := equiv [] a

/-- -/
theorem isZeroAux_of_nil : isZeroAux [] := equiv_refl

theorem isZeroAux_cons_iff {x : Nat} {xs : List Nat} : isZeroAux (x::xs) ↔ x = 0 ∧ isZeroAux xs:= by
  unfold isZeroAux
  rw [equiv.eq_def]

theorem isZeroAux_of_toNatAux_eq_zero {a : List Nat} {base : Nat} (h: toNatAux a base = 0) (hb : 1 < base) :
  isZeroAux a := by
  induction a with
  | nil =>
    rw [toNatAux] at h
    simp only [isZeroAux, equiv_refl]
  | cons x xs ih =>
    rw [toNatAux_cons] at h
    have h1 : x = 0 ∧ base * (toNatAux xs base) = 0 := Nat.eq_zero_of_add_eq_zero h
    have h2 : toNatAux xs base = 0 :=
      Or.resolve_left (Nat.zero_eq_mul.mp (Eq.symm h1.right)) (Nat.ne_zero_of_lt hb)
    have h3 : isZeroAux xs := ih h2
    exact isZeroAux_cons_iff.mpr (And.intro h1.left h3)

theorem toNatAux_eq_zero_of_isZeroAux {a : List Nat} {base : Nat} (h: isZeroAux a) :
  toNatAux a base = 0 := by
  induction a with
  | nil => exact toNatAux_nil
  | cons x xs ih =>
    rw [isZeroAux_cons_iff] at h
    rw [toNatAux_cons]
    have : toNatAux xs base = 0 := ih h.right
    rw [this, h.left, Nat.zero_add, Nat.mul_zero]

theorem toNatAux_eq_zero_iff {a : List Nat} {base : Nat} (hb : 1 < base) :
  toNatAux a base = 0 ↔ isZeroAux a := by
  constructor
  · intro h
    exact isZeroAux_of_toNatAux_eq_zero h hb
  · intro h
    exact toNatAux_eq_zero_of_isZeroAux h

/-- -/
def decIsZeroAux (a : List Nat) : Decidable (isZeroAux a) := decEquiv [] a

end IsZeroAux

section AllDigitsLtBase

/-- -/
def allDigitsLtBase (a : List Nat) (base : Nat) : Prop := a.all (· < base)

/-- -/
def decAllDigitsLtBase (a : List Nat) (base : Nat) : Decidable (allDigitsLtBase a base) :=
  match ga : a with
  | [] =>
    have : [].all (· < base) := List.all_nil
    isTrue this
  | x::xs =>
    have h1 : x < base ∧ xs.all (· < base) → (x::xs).all (· < base) := by
      intro g
      rwa [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    have h2 : ¬ x < base ∨ ¬ xs.all (· < base) → ¬ (x::xs).all (· < base) := by
      intro g
      rwa [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, Classical.not_and_iff_not_or_not]
    if hx : x < base then
      if hxs : xs.all (· < base) then
        isTrue (h1 (And.intro hx hxs))
      else
        isFalse (h2 (.inr hxs))
    else
      isFalse (h2 (.inl hx))

/-- -/
instance instAllDigitsLtBase (a : List Nat) (base : Nat) : Decidable (allDigitsLtBase a base) := decAllDigitsLtBase a base

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

section ToStringAux

def digitToString (digit base : Nat) (hd : digit < base) : String :=
  if g : base = 16 ∧ 10 ≤ digit then
    /- needed for avoiding "Missing cases"-error in the following match -/
    have : decide (digit < 16) := by
      rw [g.left] at hd
      simp only [hd, decide_true]
    match digit with
    | 10 => "a"
    | 11 => "b"
    | 12 => "c"
    | 13 => "d"
    | 14 => "e"
    | 15 => "f"
  else
    s!"{digit}"

def toStringAux (digits : List Nat) (base : Nat) (ha : allDigitsLtBase digits base) : String:=
  let s := natsToStrings (digits : List Nat) (base : Nat) (ha : allDigitsLtBase digits base)
  let r := if s = [] then ["0"] else s.reverse
  match base with
  | 2 => s!"0b{String.join r}"
  | 8 => s!"0o{String.join r}"
  | 10 => s!"{ String.join r}"
  | 16 => s!"0x{String.join r}"
  | _ => s!"{",".intercalate r}({base})"
  where natsToStrings (digits : List Nat) (base : Nat) (ha : allDigitsLtBase digits base) : List String :=
    match digits with
    | [] => []
    | x::xs =>
      have hxs : x < base ∧ allDigitsLtBase xs base := allDigitsLtBase_cons_iff.mp ha
      (digitToString x base hxs.left)::(natsToStrings xs base hxs.right)

end ToStringAux

section ToNatAux_Equiv

theorem toNatAux_eq_of_equiv {a b : List Nat} {base : Nat} (h : equiv a b) (hb : 1 < base) :
  toNatAux a base = toNatAux b base := by
  induction a generalizing b with
  | nil =>
    have : toNatAux b base = 0 ↔ isZeroAux b := toNatAux_eq_zero_iff hb
    rw [isZeroAux.eq_def, eq_symm] at this
    simp only [toNatAux_nil, this, h]
  | cons x xs ih =>
    match b with
    | [] =>
      have : toNatAux (x::xs) base = 0 ↔ isZeroAux (x::xs) := toNatAux_eq_zero_iff hb
      rw [isZeroAux.eq_def,  equiv_iff] at this
      simp only [toNatAux_nil, this, h]
    | y::ys =>
      simp only [equiv] at h
      simp only [toNatAux_cons, h.left, ih h.right]

theorem equiv_of_toNatAux_eq {a b : List Nat} {base : Nat}
  (h : toNatAux a base = toNatAux b base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) (hb : 1 < base) :
  equiv a b := by
  induction a generalizing b with
  | nil =>
    have : toNatAux b base = 0 ↔ isZeroAux b := toNatAux_eq_zero_iff hb
    rw [isZeroAux.eq_def, eq_symm] at this
    rw [toNatAux_nil] at h
    exact this.mp h
  | cons x xs ih =>
    match b with
    | [] =>
      have : toNatAux (x::xs) base = 0 ↔ isZeroAux (x::xs) := toNatAux_eq_zero_iff hb
      rw [isZeroAux.eq_def,  equiv_iff] at this
      rw [toNatAux_nil] at h
      exact this.mp h
    | y::ys =>
      have halt' : x < base ∧ allDigitsLtBase xs base := allDigitsLtBase_cons_iff.mp halt
      have hblt' : y < base ∧ allDigitsLtBase ys base := allDigitsLtBase_cons_iff.mp hblt
      simp only [toNatAux_cons] at h
      simp only [equiv]
      have : x = y ∧ toNatAux xs base = toNatAux ys base :=
        (Nat.add_mul_eq_iff_and_eq_eq_of halt'.left hblt'.left).mp h
      exact And.intro this.left (ih this.right halt'.right hblt'.right)

theorem toNatAux_eq_iff {a b : List Nat} {base : Nat}
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) (hb : 1 < base) :
  toNatAux a base = toNatAux b base ↔ equiv a b := by
  constructor
  · intro h
    exact equiv_of_toNatAux_eq h halt hblt hb
  · intro h
    exact toNatAux_eq_of_equiv h hb

example {a b : List Nat} {base : Nat} (ha : a = [11]) (hb : b = [1,1]) (hbase : base = 10) :
  toNatAux a base = toNatAux b base ∧ ¬ equiv a b := by
  have : toNatAux a base = toNatAux b base := by rw [ha, hb, hbase]; decide
  match decEquiv a b with
  | isFalse q => exact And.intro this q
  | isTrue q =>
    rw [ha, hb] at q
    simp only [equiv, Nat.succ_ne_self, false_and, and_false] at q

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

theorem noTrailingZero_singleton_iff {n : Nat} : noTrailingZero [n] ↔ n ≠ 0 := by
  rw [noTrailingZero.eq_def]
  constructor
  · intro h
    have : [n] ≠ [] := List.cons_ne_nil n []
    have : [n].getLast this ≠ 0 := h this
    rwa [List.getLast_singleton] at this
  · intro h _
    rwa [List.getLast_singleton]

/-- -/
theorem noTrailingZero_tail_of {x : Nat} {xs : List Nat}
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
  have h1 : x :: xs ≠ [] := List.cons_ne_nil x xs
  intro _
  if g : xs = [] then
    simp only [g, List.getLast_singleton (List.cons_ne_nil x [])]
    exact h.right g
  else
    rw [List.getLast_cons g]
    exact h.left g

/-- -/
theorem noTrailingZero_cons_iff {x : Nat} {xs : List Nat} :
  noTrailingZero (x::xs) ↔ noTrailingZero xs ∧ (xs = [] → x ≠ 0) := by
  constructor
  · intro h
    exact noTrailingZero_tail_of h
  · intro h
    exact noTrailingZero_cons_of h

end NoTrailingZero

section NoTrailingZero_IsZeroAux

theorem isZeroAux_iff_of_noTrailingZero {a : List Nat} (hantz : noTrailingZero a) :
  isZeroAux a ↔ a = [] := by
  constructor
  · intro h
    induction a with
    | nil => rfl
    | cons x xs ih =>
      rw [noTrailingZero_cons_iff] at hantz
      rw [isZeroAux_cons_iff] at h
      exact absurd h.left (hantz.right (ih hantz.left h.right))
  · intro h
    rw [h]
    exact isZeroAux_of_nil

end NoTrailingZero_IsZeroAux

section ConsAux

def consAux (n : Nat) (a : List Nat) : List Nat :=
  match n, a with
  | 0, [] => []
  | k + 1, [] => [k + 1]
  | n, x::xs => n::x::xs

theorem allDigitsLtBase_consAux_of {n base: Nat} {a : List Nat}
  (hn : n < base) (ha : allDigitsLtBase a base) :
  allDigitsLtBase (consAux n a) base := by
  unfold consAux
  match gn: n, ga: a with
  | 0, [] => simp only; exact allDigitsLtBase_nil
  | k + 1, [] => simp only; exact allDigitsLtBase_singleton hn
  | n, x::xs => simp only; exact allDigitsLtBase_cons_iff.mpr (And.intro hn ha)

theorem noTrailingZero_consAux {n : Nat} {a : List Nat} (ha : noTrailingZero a) :
  noTrailingZero (consAux n a) := by
  unfold consAux
  match gn: n, ga: a with
  | 0, [] => simp only; exact noTrailingZero_nil
  | k + 1, [] => simp only; exact noTrailingZero_singleton_iff.mpr (Nat.succ_ne_zero k)
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

theorem discardTrailingZeros_nil : discardTrailingZeros [] = [] := by
  unfold discardTrailingZeros
  rfl

theorem noTrailingZero_discardTrailingZeros {a : List Nat} :
  noTrailingZero (discardTrailingZeros a) := by
  induction a with
  | nil => simp only [discardTrailingZeros_nil, noTrailingZero_nil]
  | cons x xs ih =>
    unfold discardTrailingZeros
    exact noTrailingZero_consAux ih

end DiscardTrailingZeros

section LeAux

def leAux (a b : List Nat) : Prop :=
  match a, b with
  | [], _ => True
  | x::xs, [] => x = 0 ∧ leAux xs []
  | x::xs, y::ys => if equiv xs ys then x ≤ y else leAux xs ys

theorem leAux_refl {a : List Nat} : leAux a a := by
  induction a with
  | nil => simp only [leAux]
  | cons x xs ih => simp only [leAux, equiv_refl, reduceIte, Nat.le_refl]

theorem leAux_nil {a : List Nat} : leAux [] a := by
  induction a with
  | nil => exact leAux_refl
  | cons x xs ih => simp only [leAux]

theorem leAux_cons_iff {x y : Nat} {xs ys : List Nat} :
  leAux (x::xs) (y::ys) ↔ if equiv xs ys then x ≤ y else leAux xs ys := by
  rw [leAux.eq_def]

section Equiv_LeAux

theorem not_equiv_of_leAux_cons_of_ne_le {x y : Nat} {xs ys : List Nat}
  (hl : leAux (x::xs) (y::ys)) (hn : ¬ x ≤ y) : ¬ equiv xs ys := by
  have : if equiv xs ys then x ≤ y else leAux xs ys := leAux_cons_iff.mp hl
  false_or_by_contra; rename _ => hc
  simp only [hc, reduceIte] at this
  contradiction

theorem leAux_of_equiv {a b : List Nat} (h : equiv a b) : leAux a b := by
  induction a generalizing b with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b with
    | [] =>
      simp only [equiv] at h
      simp only [leAux]
      exact And.intro h.left (ih h.right)
    | y::ys =>
      simp only [equiv] at h
      simp only [leAux, h.right, reduceIte, h.left, Nat.le_refl]

theorem equiv_nil_of_leAux_nil {a : List Nat} (h : leAux a []) : equiv [] a  := by
  induction a with
  | nil  => exact equiv_refl
  | cons x xs ih =>
    rw [equiv.eq_def]
    rw [leAux.eq_def] at h
    simp only at ih h ⊢
    exact And.intro h.left (ih h.right)

theorem leAux_nil_iff_equiv_nil {a : List Nat} : leAux a [] ↔ equiv [] a := by
  constructor
  · intro h
    exact equiv_nil_of_leAux_nil h
  · intro h
    exact leAux_of_equiv (equiv_symm h)

end Equiv_LeAux

theorem leAux_antiysmm {a b : List Nat}:
  equiv a b ↔ leAux a b ∧ leAux b a := by
  constructor
  · intro h
    have h1 : leAux a b := leAux_of_equiv h
    have h2 : leAux b a := leAux_of_equiv (equiv_symm h)
    exact And.intro h1 h2
  · intro h
    induction a generalizing b with
    | nil =>
      unfold leAux at h
      match b with
      | [] => exact equiv_refl
      | x::xs =>
        rw [equiv.eq_def]
        simp only [true_and] at ⊢ h
        exact And.intro h.left (equiv_nil_of_leAux_nil h.right)
    | cons x xs ih =>
      match b with
      | [] =>
        have : equiv [] (x :: xs) := equiv_nil_of_leAux_nil h.left
        exact equiv_symm this
      | y::ys =>
        unfold leAux at h
        unfold equiv
        if g : equiv xs ys then
          simp only [g, equiv_symm, reduceIte] at h
          simp only [Nat.le_antisymm h.left h.right, g, true_and]
        else
          have : ¬ equiv ys xs := not_equiv_iff.mp g
          simp only [g, reduceIte, this] at h
          have : equiv xs ys := ih h
          contradiction

theorem leAux_nil_of_leAux {a b : List Nat} (h : leAux a b) : leAux [] b := by
  induction a generalizing b with
  | nil => exact leAux_nil
  | cons x xs ihx =>
    unfold leAux at h;
    match b with
    | [] => exact ihx h.right
    | y::ys => unfold leAux; simp_all only

section LeAux_Equiv

theorem leAux_of_leAux_of_equiv {a b c : List Nat} (hab : leAux a b) (hbc : equiv b c): leAux a c := by
  induction a generalizing b c with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b, c with
    | [], [] => simp_all only
    | y::ys, [] =>
      unfold leAux at hab ⊢
      unfold equiv at hbc
      if g : equiv xs ys then
        simp only [g, reduceIte, hbc.left] at hab
        have h1 : x = 0 := Nat.eq_zero_of_le_zero hab
        have h2 : leAux xs ys := leAux_of_equiv g
        have h3 : leAux xs [] := ih  h2 hbc.right
        exact And.intro h1 h3
      else
        simp only [g, reduceIte, hbc.left] at hab
        have h1 : leAux xs [] := ih hab hbc.right
        have h2 : equiv xs [] := equiv_symm (equiv_nil_of_leAux_nil h1)
        have h3 : equiv xs ys := equiv_trans h2 (equiv_symm hbc.right)
        contradiction
    | [], z::zs =>
      have : equiv (x :: xs) [] := equiv_symm (equiv_nil_of_leAux_nil hab)
      have : equiv (x :: xs) (z :: zs) := equiv_trans this hbc
      exact leAux_of_equiv this
    | y::ys, z::zs =>
      unfold leAux at hab ⊢
      unfold equiv at hbc
      if g1 : equiv xs ys then
        simp only [g1, reduceIte, hbc.left] at hab
        if g2 : equiv xs zs then
          simp only [g2, reduceIte]
          exact hab
        else
          simp only [g2, reduceIte]
          have : equiv xs zs := equiv_trans g1 hbc.right
          contradiction
      else
        simp only [g1, reduceIte] at hab
        if g2 : equiv xs zs then
          simp only [g2, reduceIte]
          have : equiv xs ys := equiv_trans g2 (equiv_symm hbc.right)
          contradiction
        else
          simp only [g2, reduceIte]
          exact ih hab hbc.right

theorem leAux_of_equiv_of_leAux {a b c : List Nat} (hab : equiv a b) (hbc : leAux b c): leAux a c := by
  induction a generalizing b c with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b, c with
    | [], [] =>
      simp only [equiv] at hab
      simp only [leAux, And.intro hab.left (ih hab.right hbc), and_true]
    | y::ys, [] =>
      simp only [equiv] at hab
      simp only [leAux] at hbc ⊢
      simp only [hab.left, hbc.left, true_and, (ih hab.right hbc.right)]
    | [], z::zs =>
      simp only [equiv] at hab
      simp only [leAux] at hbc ⊢
      if h : equiv xs zs then
        simp only [h, reduceIte, hab.left, Nat.zero_le]
      else
        simp only [h, reduceIte]
        have : leAux [] zs := leAux_nil
        exact ih hab.right this
    | y::ys, z::zs =>
      simp only [equiv] at hab
      simp only [leAux] at hbc
      if h : equiv ys zs then
        simp only [h, reduceIte] at hbc
        simp only [leAux, equiv_trans hab.right h, reduceIte]
        rwa [hab.left]
      else
        simp only [h, reduceIte] at hbc
        have : ¬ equiv xs zs := not_equiv_of_equiv_of_not_equiv hab.right h
        simp only [leAux, this, reduceIte, ih hab.right hbc]

theorem and_equiv_equiv_of_leAux {a b c : List Nat}
  (hab : leAux a b) (hbc : leAux b c) (hac : equiv a c) : equiv a b ∧ equiv b c := by
  have : leAux b a := leAux_of_leAux_of_equiv hbc (equiv_symm hac)
  have h1 : equiv a b := leAux_antiysmm.mpr (And.intro hab this)
  have : leAux c b := leAux_of_equiv_of_leAux (equiv_symm hac) hab
  have h2 : equiv b c := leAux_antiysmm.mpr (And.intro hbc this)
  exact And.intro h1 h2

end LeAux_Equiv

theorem leAux_trans {a b c : List Nat} (hab : leAux a b) (hbc : leAux b c) : leAux a c := by
  induction a generalizing b c with
  | nil => exact leAux_nil
  | cons x xs ihx =>
    match b, c with
    | [], [] => unfold leAux at hab ⊢; simp_all only [and_true]
    | y::ys, [] =>
      have : equiv (y::ys) [] := equiv_symm (equiv_nil_of_leAux_nil hbc)
      exact leAux_of_leAux_of_equiv hab this
    | [], z::zs =>
      have : equiv (x::xs) [] := equiv_symm (equiv_nil_of_leAux_nil hab)
      exact leAux_of_equiv_of_leAux this hbc
    | y::ys, z::zs =>
      unfold leAux at hab hbc ⊢
      if gxy : equiv xs ys then
        if gyz : equiv ys zs then
          have : equiv xs zs := equiv_trans gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact Nat.le_trans hab hbc
        else
          have : ¬ equiv xs zs := not_equiv_of_equiv_of_not_equiv gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact ihx (leAux_of_equiv gxy) hbc
      else
        if gyz : equiv ys zs then
          have : ¬ equiv xs zs := not_equiv_of_not_equiv_of_equiv gxy gyz
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          simp only [this, reduceIte]
          exact ihx hab (leAux_of_equiv gyz)
        else
          simp only [gxy, reduceIte] at hab
          simp only [gyz, reduceIte] at hbc
          have : ¬ equiv xs zs := by
            false_or_by_contra; rename _ => hc
            exact absurd (and_equiv_equiv_of_leAux hab hbc hc).left gxy
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
    match decEquiv xs ys with
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

section ToNatAux_LeAux

theorem toNatAux_le_of_leAux {a b : List Nat} {base : Nat} (h : leAux a b) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  toNatAux a base ≤ toNatAux b base := by
  induction a generalizing b with
  | nil => simp only [toNatAux_nil, Nat.zero_le]
  | cons x xs ih =>
    match b with
    | [] =>
      have : isZeroAux (x::xs) := equiv_nil_of_leAux_nil h
      have : toNatAux (x :: xs) base = 0 := (toNatAux_eq_zero_iff hb).mpr this
      simp only [this, Nat.zero_le]
    | y::ys =>
      simp only [leAux_cons_iff] at h
      simp only [toNatAux_cons]
      if g : equiv xs ys then
        simp only [g, reduceIte] at h
        simp only [toNatAux_eq_of_equiv g hb, Nat.add_le_add_right h (base * toNatAux ys base)]
      else
        simp only [g, reduceIte] at h
        have halt' : x < base ∧ xs.all (· < base) := allDigitsLtBase_cons_iff.mp halt
        have hblt' : y < base ∧ ys.all (· < base) := allDigitsLtBase_cons_iff.mp hblt
        have h1 : toNatAux xs base ≤ toNatAux ys base := ih h halt'.right hblt'.right
        have h2 : toNatAux xs base ≠ toNatAux ys base :=
          (Classical.iff_iff_iff_not_not.mp (toNatAux_eq_iff halt'.right hblt'.right hb)).mpr g
        have h3 : toNatAux xs base < toNatAux ys base := Nat.lt_of_le_of_ne h1 h2
        exact Nat.le_of_lt (Nat.lt_of_lt_of_ltBase h3 halt'.left)

theorem leAux_of_toNatAux_le {a b : List Nat} {base : Nat}
  (h : toNatAux a base ≤ toNatAux b base) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) : leAux a b := by
  induction a generalizing b with
  | nil => exact leAux_nil
  | cons x xs ih =>
    match b with
    | [] =>
      have : toNatAux [] base = 0 := toNatAux_nil
      simp only [toNatAux_nil, Nat.le_zero, toNatAux_eq_zero_iff hb, isZeroAux, equiv_iff] at h
      exact leAux_of_equiv h
    | y::ys =>
      simp only [toNatAux_cons] at h
      simp only [leAux]
      if g : equiv xs ys then
        simp only [g, reduceIte]
        rw [toNatAux_eq_of_equiv g hb] at h
        exact Nat.le_of_add_le_add_right h
      else
        have halt' : x < base ∧ xs.all (· < base) := allDigitsLtBase_cons_iff.mp halt
        have hblt' : y < base ∧ ys.all (· < base) := allDigitsLtBase_cons_iff.mp hblt
        simp only [g, reduceIte]
        have : toNatAux xs base ≠ toNatAux ys base := by
          false_or_by_contra; rename _ => hc
          exact absurd (equiv_of_toNatAux_eq hc halt'.right hblt'.right hb) g
        have : toNatAux xs base ≤ toNatAux ys base :=
          (Nat.add_mul_le_iff_le_of this halt'.left hblt'.left).mp h
        exact ih this halt'.right hblt'.right

theorem leAux_iff_le_toNat {a b : List Nat} {base : Nat} (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  leAux a b ↔ (toNatAux a base) ≤ (toNatAux b base) := by
  constructor
  · intro h
    exact toNatAux_le_of_leAux h hb halt hblt
  · intro h
    exact leAux_of_toNatAux_le h hb halt hblt

end ToNatAux_LeAux

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

theorem not_equiv_nil_of_ltAux_nil {a : List Nat} (h : ltAux [] a) : ¬ equiv [] a := by
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
    simp only [equiv, Classical.not_and_iff_not_or_not, this]
    cases h with
    | inl hl => exact .inl hl
    | inr hr => exact .inr (ih hr)

theorem not_equiv_of_ltAux {a b : List Nat} (h : ltAux a b) : ¬ equiv a b := by
  induction a generalizing b with
  | nil => exact not_equiv_nil_of_ltAux_nil h
  | cons x xs ih =>
    match b with
    | [] => rw [ltAux.eq_def] at h; contradiction
    | y::ys =>
      simp only [ltAux] at h
      simp only [equiv, Classical.not_and_iff_not_or_not]
      cases h with
      | inl hl => exact .inl (Nat.ne_of_lt hl.left)
      | inr hr => exact .inr (ih hr)

theorem not_ltAux_nil_of_equiv_nil {a : List Nat} (h : equiv [] a) : ¬ ltAux [] a := by
  induction a with
  | nil => exact ltAux_irrefl
  | cons y ys ih =>
    unfold equiv at h
    simp only [ltAux, not_or, Nat.not_lt, Nat.le_zero]
    exact And.intro h.left (ih h.right)

theorem not_ltAux_of_equiv {a b : List Nat} (h : equiv a b) : ¬ ltAux a b := by
  induction a generalizing b with
  | nil => exact not_ltAux_nil_of_equiv_nil h
  | cons x xs ih =>
    match b with
    | [] => simp only [ltAux, not_false_eq_true]
    | y::ys =>
      simp only [equiv] at h
      simp only [ltAux, not_or, Classical.not_and_iff_not_or_not, Classical.not_not]
      have : ¬ x < y := by rw [h.left]; exact Nat.lt_irrefl y
      exact And.intro (.inl this) (ih h.right)

theorem ltAux_nil_of_not_equiv_nil_of_not_ltAux {a : List Nat}
  (h1 : ¬ equiv [] a) (h2 : ¬ ltAux a []) : ltAux [] a := by
  induction a with
  | nil => unfold equiv at h1; simp only [not_true] at h1
  | cons x xs ih =>
    unfold equiv at h1
    simp only [Classical.not_and_iff_not_or_not] at h1
    unfold ltAux
    cases h1 with
    | inl h1l =>
      have : 0 < x := Nat.zero_lt_of_ne_zero h1l
      exact .inl this
    | inr h1r =>
      have : ¬ ltAux xs [] := by simp only [ltAux, not_false_eq_true]
      exact .inr (ih h1r this)

theorem ltAux_of_not_equiv_of_not_ltAux {a b : List Nat}
  (h1 : ¬ equiv a b) (h2 : ¬ ltAux b a) : ltAux a b := by
  induction a generalizing b with
  | nil => exact ltAux_nil_of_not_equiv_nil_of_not_ltAux h1 h2
  | cons x xs ihx =>
    unfold equiv at h1
    match b with
    | [] =>
      simp only [Classical.not_and_iff_not_or_not] at h1
      unfold ltAux at ⊢ h2
      simp only [not_or, Nat.not_lt, Nat.le_zero_eq] at h1 h2
      have : ¬¬x = 0 := not_not_intro h2.left
      have : ¬equiv xs [] := Or.resolve_left h1 this
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

theorem equiv_of_and_not_ltAux_not_ltAux {a b : List Nat} (h : ¬ ltAux a b ∧ ¬ ltAux b a) : equiv a b := by
  false_or_by_contra; rename _ => hc
  exact absurd (ltAux_of_not_equiv_of_not_ltAux hc h.right) h.left

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
        have : ¬ equiv xs ys := not_equiv_of_ltAux g
        simp only [this, reduceIte, ih g]
      else
        have h1 : x < y ∧ ¬ltAux ys xs := Or.resolve_right h g
        have h2 : equiv xs ys := equiv_of_and_not_ltAux_not_ltAux (And.intro g h1.right)
        simp only [h2, reduceIte, Nat.le_of_lt h1.left]

theorem leAux_iff_not_ltAux {a b : List Nat} : leAux a b ↔ ¬ ltAux b a := by
  induction a generalizing b with
  | nil => unfold leAux ltAux; simp only [not_false_eq_true]
  | cons x xs ih =>
    unfold leAux ltAux
    match b with
    | [] =>
      have h1 : x = 0 ↔ x ≤ 0 := by
        constructor
        · intro h
          simp only [h, Nat.le_refl]
        · intro h
          exact Nat.eq_zero_of_le_zero h
      simp only [not_or, Nat.not_lt, h1, ih]
    | y::ys =>
      simp only [not_or, Classical.not_and_iff_not_or_not, Classical.not_not, Nat.not_lt, ih]
      constructor
      · intro h
        if g : equiv xs ys then
          simp [g] at h
          have : ¬ltAux ys xs := ih.mp (leAux_of_equiv g)
          exact And.intro (.inl h) this
        else
          simp [g] at h
          have : ltAux xs ys := ltAux_of_not_equiv_of_not_ltAux g h
          exact And.intro (.inr this) h
      · intro h
        if g : ltAux xs ys then
          have : ¬ equiv xs ys := not_equiv_of_ltAux g
          simp only [this, reduceIte, h.right, not_false_eq_true]
        else
          have : equiv xs ys := equiv_of_and_not_ltAux_not_ltAux (And.intro g h.right)
          simp only [this, reduceIte]
          exact Or.resolve_right h.left g

theorem ltAux_iff_and_leAux_not_equiv {a b : List Nat} : ltAux a b ↔ leAux a b ∧ ¬ equiv a b := by
  constructor
  · intro h
    exact And.intro (leAux_of_ltAux h) (not_equiv_of_ltAux h)
  · intro h
    have : ¬ ltAux b a := leAux_iff_not_ltAux.mp h.left
    exact ltAux_of_not_equiv_of_not_ltAux h.right this

theorem ltAux_of_ltAux_of_leAux {a b c : List Nat} (hab : ltAux a b) (hbc : leAux b c) : ltAux a c := by
  have h1 : leAux a c := leAux_trans (leAux_of_ltAux hab) hbc
  have h2 : equiv a c → equiv a b ∧ equiv b c := by
    intro h
    exact and_equiv_equiv_of_leAux (leAux_of_ltAux hab) hbc h
  have h3 : equiv a c → ¬ ltAux a b := by
    intro h
    exact not_ltAux_of_equiv (h2 h).left
  have h4 : ¬ equiv a c := fun h : equiv a c => absurd hab (h3 h)
  exact ltAux_iff_and_leAux_not_equiv.mpr (And.intro h1 h4)

theorem ltAux_of_leAux_of_ltAux {a b c : List Nat} (hab : leAux a b) (hbc : ltAux b c) : ltAux a c := by
  have h1 : leAux a c := leAux_trans hab (leAux_of_ltAux hbc)
  have h2 : equiv a c → equiv a b ∧ equiv b c := by
    intro h
    exact and_equiv_equiv_of_leAux hab (leAux_of_ltAux hbc) h
  have h3 : equiv a c → ¬ ltAux b c := by
    intro h
    exact not_ltAux_of_equiv (h2 h).right
  have h4 : ¬ equiv a c := fun h : equiv a c => absurd hbc (h3 h)
  exact ltAux_iff_and_leAux_not_equiv.mpr (And.intro h1 h4)

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

section toNatAux_LtAux

theorem toNatAux_lt_of_ltAux {a b : List Nat} {base : Nat} (h : ltAux a b) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  toNatAux a base < toNatAux b base := by
  have h1 : toNatAux a base ≤ toNatAux b base := toNatAux_le_of_leAux (leAux_of_ltAux h) hb halt hblt
  have h2 : ¬ equiv a b := not_equiv_of_ltAux h
  have h3 : toNatAux a base = toNatAux b base ↔ equiv a b := toNatAux_eq_iff halt hblt hb
  have h4 : ¬ toNatAux a base = toNatAux b base := (Classical.iff_iff_iff_not_not.mp h3).mpr h2
  exact Nat.lt_of_le_of_ne h1 h4

theorem ltAux_of_toNatAux_lt {a b : List Nat} {base : Nat} (h : toNatAux a base < toNatAux b base) (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  ltAux a b := by
  have h1 : toNatAux a base ≤ toNatAux b base := Nat.le_of_lt h
  have h2 : ¬ toNatAux a base = toNatAux b base := Nat.ne_of_lt h
  have h3 : toNatAux a base = toNatAux b base ↔ equiv a b := toNatAux_eq_iff halt hblt hb
  have h4 : ¬ equiv a b := (Classical.iff_iff_iff_not_not.mp h3).mp h2
  exact ltAux_iff_and_leAux_not_equiv.mpr (And.intro (leAux_of_toNatAux_le h1 hb halt hblt) h4)

theorem ltAux_iff_toNatAux_lt {a b : List Nat} {base : Nat} (hb : 1 < base)
  (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  ltAux a b ↔ toNatAux a base < toNatAux b base := by
  constructor
  · intro h
    exact toNatAux_lt_of_ltAux h hb halt hblt
  · intro h
    exact ltAux_of_toNatAux_lt h hb halt hblt

end toNatAux_LtAux

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
theorem prune_of_nil_zero {a : List Nat} {n base : Nat} (ha : a = []) (hn : n = 0) (hb : 1 < base) :
  prune a n base hb = [] := by
  rw [prune.eq_def]
  match a, n with | [], 0 => simp only

/-- -/
theorem prune_eq_nil_iff {a : List Nat} {n base : Nat}  (hb : 1 < base) :
  prune a n base hb = [] ↔ a = [] ∧ n = 0 := by
  constructor
  · intro h
    rw [prune.eq_def] at h
    match ga : a, gn : n with | [], 0 => exact And.intro rfl rfl
  · intro h
    exact prune_of_nil_zero h.left h.right hb

theorem prune_nil_eq_of_pos {n base : Nat} (hn : 0 < n) (hb : 1 < base) :
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

theorem noTrailingZero_prune_nil_of {n base : Nat} {hb : 1 < base} : noTrailingZero (prune [] n base hb) := by
  induction n using Nat.strongRecOn with
  | _ l ihl =>
    match gl : l with
      | 0 => rw [prune.eq_def]; simp only [noTrailingZero_nil]
      | k + 1 =>
        simp only [prune]
        have h1 : (k + 1) / base < k + 1  := Nat.div_lt_self (Nat.succ_pos k) hb
        if g : (k + 1) / base = 0 then
          have h2 : prune [] ((k + 1) / base) base hb = [] := (prune_eq_nil_iff hb).mpr (And.intro rfl g)
          have h3 : (k + 1) % base ≠ 0 := Nat.ne_zero_mod_of_ne_zero hb g (Nat.succ_ne_zero k)
          have h4 : noTrailingZero (prune [] ((k + 1) / base) base hb)
                      ∧ (prune [] ((k + 1) / base) base hb = [] → (k + 1) % base ≠ 0) :=
            And.intro (ihl ((k + 1) / base) h1) (fun _ : prune [] ((k + 1) / base) base hb = [] => h3)
          exact noTrailingZero_cons_of h4
        else
          have h2 : ¬(([] : List Nat) = [] ∧ (k + 1) / base = 0) := by
            intro h
            exact absurd h.right g
          have h3 : prune [] ((k + 1) / base) base hb ≠ [] :=
            Classical.imp_iff_imp_not_not.mp (prune_eq_nil_iff hb).mp h2
          have h4 : noTrailingZero (prune [] ((k + 1) / base) base hb)
                      ∧ (prune [] ((k + 1) / base) base hb = [] → (k + 1) % base ≠ 0) :=
            And.intro (ihl ((k + 1) / base) h1) (fun t : prune [] ((k + 1) / base) base hb = [] => absurd t h3)
          exact noTrailingZero_cons_of h4

theorem noTrailingZero_prune_of {a : List Nat} {n base : Nat} {hb : 1 < base} (hntz : noTrailingZero a) :
  noTrailingZero (prune a n base hb) := by
  induction a generalizing n with
  | nil => exact noTrailingZero_prune_nil_of
  | cons x xs iha =>
    simp only [prune]
    have h1 : noTrailingZero xs ∧ (xs = [] → x ≠ 0) := noTrailingZero_cons_iff.mp hntz
    have h2 : noTrailingZero (prune xs ((x + n) / base) base hb) := iha h1.left
    simp only [noTrailingZero_cons_iff, h2, true_and]
    intro h
    simp only [prune_eq_nil_iff] at h
    have h3 : x ≠ 0 := h1.right h.left
    have h4 : 0 < x := Nat.pos_of_ne_zero h3
    have h5 : 0 < x + n := Nat.add_pos_left h4 n
    have h6 : x + n ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr h5
    exact Nat.ne_zero_mod_of_ne_zero hb h.right h6

end NoTrailingZero_Prune

section ToNatAux_Prune

/-- -/
theorem toNatAux_prune_eq {a : List Nat} {n base : Nat} (hb : 1 < base) :
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
        have h1 : (k + 1) / base < k + 1 := Nat.div_lt_self (Nat.succ_pos k) hb
        rw [prune.eq_def, toNatAux_cons, ihl ((k + 1) / base) h1, Nat.mul_add, ← Nat.add_assoc]
        rw [Nat.mod_add_div (k + 1) base, toNatAux_nil, Nat.mul_zero]
  | cons x xs iha =>
    rw [prune.eq_def, toNatAux_cons, iha, Nat.mul_add, ← Nat.add_assoc]
    rw [Nat.mod_add_div, toNatAux_cons, ← Nat.add_assoc]
    rw (occs := [2]) [Nat.add_comm]

end ToNatAux_Prune

section ofNatAux

abbrev ofNatAux (n : Nat) (base : Nat) (hb : 1 < base) := prune [] n base hb

theorem isZeroAux_ofNatAux_iff {n base : Nat} (hb : 1 < base) :
  isZeroAux (ofNatAux n base hb) ↔ n = 0 := by
  constructor
  · intro h
    simp only [ofNatAux] at h
    have h1 : noTrailingZero (prune [] n base hb) := noTrailingZero_prune_nil_of
    have h2 : (prune [] n base hb) = [] := (isZeroAux_iff_of_noTrailingZero h1).mp h
    exact ((prune_eq_nil_iff hb).mp h2).right
  · intro h
    simp only [h, ofNatAux, prune, isZeroAux, equiv]

end ofNatAux

section AddDigits

/-- -/
def addDigits : List Nat → List Nat → List Nat
  | [], [] => []
  | x::xs, [] => x::xs
  | [], y::ys => y::ys
  | x::xs, y::ys => (x + y)::(addDigits xs ys)

/-- -/
theorem addDigits_eq_nil_iff {a b : List Nat} : addDigits a b = [] ↔ a = [] ∧ b = [] := by
  constructor
  · intro h
    match ga : a, gb : b with
    | [], [] => exact And.intro rfl rfl
    | x::xs, [] | [], y::ys | x::xs, y::ys => contradiction
  . intro h
    match a, b with | [], [] => rfl

/-- -/
theorem addDigits_nil_eq {a : List Nat} : addDigits a [] = a := by
  rw [addDigits.eq_def]
  match ha : a with
  | [] | x::xs => rfl

/-- -/
theorem addDigits_cons_eq {x y : Nat} {xs ys : List Nat} : addDigits (x::xs) (y::ys) = (x + y)::addDigits xs ys := rfl

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

/-- -/
theorem addDigits_eq_zero_iff {a b : List Nat} :
  addDigits a b = [0] ↔ a = [0] ∧ b = [] ∨ a = [] ∧ b = [0] ∨ a = [0] ∧ b = [0] := by
  constructor
  · intro h
    match ga : a, gb : b with
    | [], [] => contradiction
    | x::xs, [] =>
      have h1 : x::xs = [0] := by rwa [addDigits_nil_eq] at h
      exact .inl (And.intro h1 rfl)
    | [], y::ys =>
      have h1 : y::ys = [0] := by rwa [addDigits_comm, addDigits_nil_eq] at h
      exact .inr (.inl (And.intro rfl h1))
    | x::xs, y::ys =>
      rw [addDigits_cons_eq] at h
      have h1 : x + y = 0 ∧ addDigits xs ys = [] := List.cons.inj h
      have h2 : x = 0 ∧ y = 0 := Nat.add_eq_zero_iff.mp h1.left
      have h3 : xs = [] ∧ ys = [] := addDigits_eq_nil_iff.mp h1.right
      have h4 : x::xs = [0] := by rw [h2.left, h3.left]
      have h5 : y::ys = [0] := by rw [h2.right, h3.right]
      exact .inr (.inr (And.intro h4 h5))
  · intro h
    match ga : a, gb : b with | [0], [] | [], [0] | [0], [0] => decide

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
      rw [noTrailingZero_cons_iff] at hantz hbntz
      have : noTrailingZero (addDigits xs ys) := ih hantz.left hbntz.left
      simp only [addDigits_cons_eq, noTrailingZero_cons_iff, this, true_and, addDigits_eq_nil_iff]
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
      simp only [toNatAux_cons, iha]
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
theorem addAux_eq_singleton {a b : List Nat} (n : Nat) {base : Nat}
  (han : a = []) (hbn : b = []) (hb : 1 < base) (hn : 0 < n ∧ n < base) :
  addAux a b n base hb = [n] := by
  have h1 : n % base = n := Nat.mod_eq_of_lt hn.right
  have h2 : 0 < n := hn.left
  have h3 : n / base = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hn.right)
  rw [addAux.eq_def]
  match ga : a, gb : b, gn: n with
  | [], [], k + 1 => simp only [List.cons.injEq, h1, true_and, h3, addAux_eq_nil_iff hb]

/-- -/
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

/-- -/
theorem addAux_eq_prune_addDigits {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = prune (addDigits a b) n base hb := by
  induction a generalizing b n with
  | nil =>
    induction b generalizing n with
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
  | cons x xs ihx =>
    rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
    match hb : b with
    | [] =>
      simp only
      rw [List.cons.injEq]
      have h1 : addDigits xs [] = xs := addDigits_nil_eq
      rw (occs := .pos [2]) [← h1]
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
  have h1 : noTrailingZero (addDigits a b) := noTrailingZero_addDigits_of hantz hbntz
  rw [addAux_eq_prune_addDigits hb]
  exact noTrailingZero_prune_of h1

end NoTrailingZero_AddAux

section ToNatAux_AddAux

/-- -/
theorem toNatAux_addAux_left_distrib {a b : List Nat} {base : Nat} {hb : 1 < base} :
  toNatAux (addAux a b 0 base hb) base = (toNatAux a base) + (toNatAux b base) := by
  rw [addAux_eq_prune_addDigits hb, toNatAux_prune_eq hb, toNatAux_addDigits_left_distrib, Nat.zero_add]

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

theorem nil_subAux_eq {a : List Nat} {n base : Nat} : subAux [] a n base = [] := by
  simp only [subAux]

theorem subAux_nil_eq {a : List Nat} {base : Nat} : subAux a [] 0 base = a := by
  induction a with
  | nil => simp only [subAux]
  | cons x xs ih =>
    simp only [subAux, subAux.helper, Nat.zero_add, Nat.zero_le, reduceIte, Nat.sub_zero, ih]

theorem cons_subAux_cons_eq {x y n base : Nat} {xs ys : List Nat} :
  subAux (x::xs) (y::ys) n base =
    (if y + n ≤ x then
      (x - y - n)::(subAux xs ys 0 base)
    else
      (base + x - y - n)::(subAux xs ys 1 base)) := by
  simp only [subAux, subAux.helper]

theorem succ_cons_subAux_succ_cons_eq {x y n base : Nat} {xs ys : List Nat} :
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

theorem subAux_cons_succ_eq {y n base : Nat} {a ys : List Nat} :
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

theorem subAux_cons_add_eq {y n m base : Nat} {a ys : List Nat} :
  subAux a ((y + m)::ys) n base = subAux a (y::ys) (n + m) base := by
  induction m generalizing a y ys n with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
    rw [← Nat.add_assoc, subAux_cons_succ_eq, ih, Nat.add_assoc, Nat.add_comm 1 k, ← Nat.add_assoc]

theorem succ_cons_subAux_succ_eq {x n base : Nat} {xs b : List Nat} :
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
      rw [subAux_cons_succ_eq]
    have h2 : subAux ((x + 1)::xs) ((y + 1)::ys) n base = subAux (x::xs) (y::ys) n base := by
      rw [succ_cons_subAux_succ_cons_eq]
    rw [h1, h2]

theorem cons_subAux_eq_cons_sub {x n base : Nat} {xs b : List Nat} (h : n ≤ x) :
  subAux (x::xs) b n base = subAux ((x - n)::xs) b 0 base := by
  induction n generalizing x xs b with
  | zero => simp only [Nat.sub_zero]
  | succ k ih =>
    have h1 : 1 ≤ x := Nat.le_trans (Nat.le_add_left 1 k) h
    have h2 : x - 1 + 1 = x := Nat.sub_add_cancel h1
    have h3 : k ≤ x - 1 := Nat.le_sub_of_add_le h
    have h4 : subAux (x::xs) b (k + 1) base = subAux ((x - 1)::xs) b k base := by
      rw [← h2, succ_cons_subAux_succ_eq, Nat.add_sub_cancel]
    rw [h4, ih h3, Nat.add_comm, Nat.sub_add_eq x 1 k]

theorem subAux_singleton_eq {a : List Nat} {n base : Nat} : subAux a [n] 0 base = subAux a [] n base := by
  unfold subAux subAux.helper
  match a with
  | [] => simp only
  | x::xs => simp only [Nat.add_zero, Nat.zero_add, Nat.sub_zero]

theorem equiv_subAux_nil_of_equiv {a b : List Nat} {base : Nat} (h: equiv a b) :
  equiv (subAux a b 0 base) [] := by
  induction b generalizing a with
  | nil => rwa [subAux_nil_eq]
  | cons y ys ih =>
    match a with
    | [] => simp only [nil_subAux_eq, equiv_refl]
    | x::xs =>
      rw [equiv_cons_iff] at h
      simp only [← h.left, cons_subAux_cons_eq, Nat.add_zero, Nat.le_refl, reduceIte, Nat.sub_zero, Nat.sub_self]
      exact equiv_cons_of_equiv (ih h.right)

/-
theorem subAux_0_subAux_1_eq {a b : List Nat} {base : Nat} :
  subAux (subAux a b 0 base) [] 1 base = subAux a b 1 base := by
  induction a generalizing b with
  | nil => simp only [nil_subAux_eq]
  | cons x xs ih =>
    match b with
    | [] => simp only [subAux_nil_eq]
    | y::ys =>
      simp only [cons_subAux_cons_eq, Nat.add_zero, Nat.sub_zero]
      if g1: y ≤ x then
        if g2: y + 1 ≤ x then
          have : 1 ≤ x - y := by sorry
          simp only [g1, g2, reduceIte, cons_subAux_eq_cons_sub this, subAux_nil_eq]
        else
          simp only [g1, g2, reduceIte]
          sorry
      else
        if g2: y + 1 ≤ x then
          simp only [g1, g2, reduceIte]
          sorry
        else
          simp only [g1, g2, reduceIte]
          sorry

theorem subAux_eq_subAux_subAux {a b : List Nat} {n base : Nat} :
  subAux a b n base = subAux (subAux a b 0 base) [] n base := by
  induction n generalizing a b with
  | zero => rw [subAux_nil_eq]
  | succ k ihn =>
    induction a generalizing b with
    | nil => simp only [nil_subAux_eq]
    | cons x xs iha =>
      match b with
      | [] => simp only [subAux_nil_eq]
      | y::ys =>
        simp only [cons_subAux_cons_eq, Nat.add_zero, Nat.sub_zero]
        if g1 : y ≤ x then
          if g2 : y + (k + 1) ≤ x then
            have : k + 1 ≤ x - y := by
              rw [Nat.add_comm] at g2
              exact Nat.le_sub_of_add_le g2
            simp only [g1, g2, reduceIte, cons_subAux_eq_cons_sub this, subAux_nil_eq]
          else
            have : ¬ k + 1 ≤ x - y := by sorry
            simp only [g1, g2, reduceIte]
            rw (occs := .pos [2]) [subAux.eq_def]
            simp only [subAux.helper, Nat.zero_add, Nat.sub_zero, this, reduceIte]
            sorry
        else
          sorry
-/

#eval toNatAux (subAux [0,0,0] [0,0,1] 10 10) 10
#eval (toNatAux [0,0,0] 10) - (toNatAux [0,0,1] 10)

theorem toNatAux_subAux_nil_left_distrib {a : List Nat} {base : Nat} :
  toNatAux (subAux [] a 0 base) base = 0 := by
  unfold subAux toNatAux toNatAux.helper
  rfl

#eval toNatAux (subAux [0,1] [9] 0 10) 10
#eval (toNatAux [0,1] 10) - (toNatAux [9] 10)

#eval subAux [0,1] [9] 1 10

example {a : List Nat} {base : Nat} (ha : a = [0]) (hb: base = 10) :
  toNatAux (subAux a [] 1 base) base ≠ (toNatAux a base) - 1 := by
  have : toNatAux (subAux a [] 1 base) base = 9 := by
    simp only [ha, hb, subAux, subAux.helper, toNatAux]
    decide
  rw [this]
  have : (toNatAux a base) - 1 = 0 := by
    simp only [ha, hb, toNatAux]
    decide
  rw [this]
  decide

theorem toNatAux_subAux_nil_one_eq {a : List Nat} {base : Nat} (hntza : noTrailingZero a) (hb : 1 < base) :
  toNatAux (subAux a [] 1 base) base = toNatAux a base - 1 := by
  induction a with
  | nil => simp only [nil_subAux_eq, toNatAux_nil]
  | cons x xs ih =>
    simp only [subAux,subAux.helper, Nat.zero_add, Nat.sub_zero]
    if g : 1 ≤ x then
      simp only [g, reduceIte, subAux_nil_eq, toNatAux_cons, Nat.sub_add_comm g]
    else
      have h1 : 1 ≤ base := Nat.le_of_lt hb
      have h2 : x = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp g)
      have h3 : noTrailingZero xs ∧ (xs = [] → x ≠ 0) := noTrailingZero_tail_of hntza
      have h4 : xs ≠ [] := by
        false_or_by_contra; rename _ => hc
        exact absurd h2 (h3.right hc)
      have h5 : ¬ isZeroAux xs := by
        false_or_by_contra; rename _ => hc
        exact absurd ((isZeroAux_iff_of_noTrailingZero h3.left).mp hc) h4
      have h6 : toNatAux xs base ≠ 0 := by
         false_or_by_contra; rename _ => hc
         exact absurd ((toNatAux_eq_zero_iff hb).mp hc) h5
      have h7 : 1 ≤ toNatAux xs base := Nat.one_le_iff_ne_zero.mpr h6
      have h8 : base ≤ base * toNatAux xs base := by
        rw (occs := .pos [1]) [← Nat.mul_one base]
        exact Nat.mul_le_mul_left base h7
      have h9 : base * toNatAux xs base + (base - 1) = base * toNatAux xs base - 1 + base := by
        rw [← Nat.add_sub_assoc h1 (base * toNatAux xs base)]
        rw [Nat.sub_add_comm (Nat.le_trans h1 h8)]
      simp only [h2, Nat.le_zero_eq, Nat.succ_ne_self, reduceIte, Nat.add_zero]
      simp only [toNatAux_cons, Nat.zero_add]
      simp only [ih h3.left, Nat.mul_sub_left_distrib, Nat.mul_one, Nat.add_comm]
      simp only [← Nat.sub_add_comm h8, h9, Nat.add_sub_cancel]

theorem lt_toNatAux_subAux_of_ltAux {a b : List Nat} {base : Nat} (h : ltAux b a)
  (hb : 1 < base) (halt : allDigitsLtBase a base) (hblt : allDigitsLtBase b base) :
  0 < toNatAux (subAux a b 0 base) base := by
  induction b generalizing a with
  | nil => simp only [subAux_nil_eq]; exact toNatAux_lt_of_ltAux h hb hblt halt
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
        simp only [cons_subAux_cons_eq, Nat.add_zero, Nat.sub_zero, g1, Nat.le_refl]
        simp only [reduceIte, toNatAux_cons, Nat.sub_self, Nat.zero_add]
        rw [← Nat.mul_zero base]
        simp only [Nat.mul_lt_mul_left h4]
        exact ih h1 h2 h3
      else
        simp only [cons_subAux_cons_eq, Nat.add_zero, Nat.sub_zero]
        if g2 : y ≤ x then
          have h1 : y < x := Nat.lt_of_le_of_ne g2 g1
          have h2 : 0 < x - y := Nat.sub_pos_of_lt h1
          simp only [g2, reduceIte, toNatAux_cons]
          exact Nat.lt_add_right (base * toNatAux (subAux xs ys 0 base) base) h2
        else
          have h1 : y < base := (allDigitsLtBase_cons_iff.mp hblt).left
          have h2 : 0 < base - y := Nat.sub_pos_of_lt h1
          have h3 : 0 < base - y + x := Nat.lt_add_right x h2
          have h4 : 0 < base + x - y := by rwa [Nat.sub_add_comm (Nat.le_of_lt h1)]
          simp only [g2, reduceIte, toNatAux_cons]
          exact Nat.lt_add_right (base * toNatAux (subAux xs ys 1 base) base) h4

#eval toNatAux (subAux [0] [] 1 10) 10
#eval toNatAux (subAux [0] [] 0 10) 10 - 1

theorem toNatAux_subAux_one_eq {a b : List Nat} {base : Nat}
  (h : ltAux b a) (hntza : noTrailingZero a) (hb : 1 < base) :
  toNatAux (subAux a b 1 base) base = toNatAux (subAux a b 0 base) base - 1 := by
  induction b generalizing a with
  | nil =>
    rw [subAux_nil_eq]
    exact toNatAux_subAux_nil_one_eq hntza hb
  | cons y ys ih =>
    match a with
    | [] => simp only [nil_subAux_eq, toNatAux_nil]
    | x::xs =>
      simp only [cons_subAux_cons_eq]
      if g1 : y + 1 ≤ x then
        have h1 : 1 ≤ x - y := by
          rw [Nat.add_comm] at g1
          exact Nat.le_sub_of_add_le g1
        have h2 : y ≤ y + 1 := Nat.le_succ y
        have h3 : y ≤ x := Nat.le_trans h2 g1
        simp only [g1, Nat.add_zero, Nat.sub_zero, h3, reduceIte, toNatAux_cons, Nat.sub_add_comm h1]
      else
        have h1 : x < y + 1 := Nat.lt_of_not_le g1
        have h2 : x ≤ y := Nat.le_of_lt_succ h1
        simp only [g1, reduceIte, Nat.add_zero, Nat.sub_zero]
        if g2 : x = y then
          have h3 : 1 ≤ base := Nat.le_of_lt hb
          have h4 : noTrailingZero xs := by sorry
          have h5 : ltAux ys xs := by
            rw [g2] at h
            exact ltAux_of_ltAux_cons h
          have h6 : toNatAux (subAux xs ys 1 base) base = toNatAux (subAux xs ys 0 base) base - 1 := ih h5 h4
          have h7 : ¬ equiv xs ys := by
            rw [equiv_iff]
            exact not_equiv_of_ltAux h5
          have h8 : ¬ equiv (subAux xs ys 0 base) [] := by sorry

          have h9 : 1 ≤ toNatAux (subAux xs ys 0 base) base := by

            sorry
          -- have h7 :
          /-
            ¬ equiv xs ys via not_equiv_of_ltAux and

          -/
          simp only [g2, Nat.le_refl, reduceIte, Nat.add_sub_cancel, toNatAux_cons, Nat.sub_self, Nat.zero_add, h6]
          simp only [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.sub_add_comm h3]
          -- Nat.add_sub_assoc, Nat.add_sub_cancel_left
          sorry
        else
          have h3 : ¬ y ≤ x := by
            false_or_by_contra; rename _ => hc
            exact absurd (Nat.le_antisymm h2 hc) g2
          have h4 : 1 ≤ base + x - y := by sorry
          simp only [h3, reduceIte, toNatAux_cons, Nat.sub_add_comm h4]

theorem toNatAux_subAux_eq {a b : List Nat} {n base : Nat} (hntza : noTrailingZero a) (hb : 1 < base) :
  toNatAux (subAux a b n base) base = toNatAux (subAux a b 0 base) base - n := by
  induction n generalizing a b with
  | zero => simp only [Nat.sub_zero]
  | succ k ih =>
    match a with
    | [] => simp only [nil_subAux_eq, toNatAux_nil, Nat.zero_sub]
    | x::xs =>
      match b with
      | [] =>
        rw [← subAux_singleton_eq, Nat.add_comm, subAux_cons_add_eq, Nat.zero_add, ih hntza]
        rw [subAux_singleton_eq, toNatAux_subAux_nil_one_eq hntza hb, subAux_nil_eq, Nat.sub_add_eq]
      | y::ys =>
        rw [← subAux_cons_succ_eq, ih hntza, subAux_cons_succ_eq, Nat.zero_add, cons_subAux_cons_eq]
        if g1 : y + 1 ≤ x then
          have h1 : 1 ≤ x - y := by
            rw [Nat.add_comm] at g1
            exact Nat.le_sub_of_add_le g1
          have h2 : y ≤ y + 1 := Nat.le_succ y
          have h3 : y ≤ x := Nat.le_trans h2 g1
          simp only [g1, reduceIte, toNatAux_cons, ← Nat.sub_add_comm h1, cons_subAux_cons_eq, Nat.add_zero, h3, Nat.sub_zero]
          rw [Nat.add_comm k 1, Nat.sub_add_eq]
        else
          have h1 : x ≤ y := by sorry
          have h2 : noTrailingZero xs := by sorry
          simp only [g1, reduceIte, toNatAux_cons, cons_subAux_cons_eq, Nat.add_zero]
          if g2 : x = y then
            simp only [g2, Nat.le_refl, reduceIte, Nat.sub_self, toNatAux_cons, Nat.zero_add, Nat.add_sub_assoc, Nat.add_zero]
            -- simp only [ih h2]
            sorry
          else
            sorry

theorem toNatAux_subAux_left_distrib {a b : List Nat} {base : Nat} (h : leAux b a) :
  toNatAux (subAux a b 0 base) base = (toNatAux a base) - (toNatAux b base) := by
  induction a generalizing b with
  | nil =>
    have : isZeroAux b := by
      unfold isZeroAux
      exact equiv_nil_of_leAux_nil h
    simp only [toNatAux_subAux_nil_left_distrib, toNatAux_eq_zero_of_isZeroAux this, toNatAux_nil]
  | cons x xs ih =>
    match b with
    | [] => simp only [subAux_nil_eq, toNatAux_nil, Nat.sub_zero]
    | y::ys =>
      if g : y ≤ x then
        have : leAux ys xs := by sorry
        simp only [cons_subAux_cons_eq, Nat.add_zero, g, reduceIte, Nat.sub_zero, toNatAux_cons, ih this]
        sorry
      else
        simp only [cons_subAux_cons_eq, Nat.add_zero, g, reduceIte, Nat.sub_zero, toNatAux_cons]
        sorry

end SubAux
