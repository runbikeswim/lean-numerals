theorem iff_iff_iff_not_not {p q : Prop} : (p ↔ q) ↔ (¬p ↔ ¬q) := by
  constructor
  · intro h
    exact not_congr h
  · intro h
    have : ¬¬p ↔ ¬¬q := not_congr h
    simp only [Classical.not_not] at this
    assumption

namespace Nat

theorem pos_of_one_lt {a : Nat} (h : 1 < a) : 0 < a := (Nat.lt_trans (by decide)) h

theorem eq_zero_of_lt_of_mod_eq_zero {a b : Nat}
  (h1 : 1 < b) (h2 : a % b = 0) (h3 : a < b) : a = 0 := by
  have h4 : b ∣ a  := Nat.dvd_iff_mod_eq_zero.mpr h2
  have h5 : a < b := Or.resolve_left (.inr h3) (Nat.ne_zero_of_lt h1)
  exact Nat.eq_zero_of_dvd_of_lt h4 h5

theorem ne_zero_mod_of_ne_zero {a b : Nat}
  (h1 : 1 < b) (h2 : a / b = 0) (h3 : a ≠ 0) : a % b ≠ 0 := by
  have h4 : a < b := Nat.lt_of_div_eq_zero (Nat.pos_of_one_lt h1) h2
  false_or_by_contra; rename _ => h5
  have h6 : a = 0 := Nat.eq_zero_of_lt_of_mod_eq_zero h1 h5 h4
  contradiction

end Nat

namespace List

theorem cons_singleton_iff_and_eq_nil {α : Type} {a b : α} {as : List α} :
  (a::as = [b]) ↔ (a = b ∧ as = []) := by simp only [cons.injEq]

theorem cons_ne_singleton_iff_or_ne_ne {α : Type} {a b : α} {as : List α} :
  (a::as ≠ [b]) ↔ (a ≠ b ∨ as ≠ []) := by
  have : (a::as = [b]) ↔ (a = b ∧ as = []) := cons_singleton_iff_and_eq_nil
  rw [iff_iff_iff_not_not, Classical.not_and_iff_not_or_not] at this
  simp_all only [cons.injEq, not_and, ne_eq]

def mapWithAll {α β : Type} (a: List α) (p : α → Bool) (ha : a.all p) (f : (x : α) → (hp : p x) → β): List β :=
  match a with
  | [] => []
  | x::xs =>
    have : p x ∧ xs.all p = true := by rwa [all_cons, Bool.and_eq_true] at ha
    (f x this.left)::(mapWithAll xs p this.right f)

end List

section isZeroAux

def isZeroAux (a : List Nat) : Prop := a = [] ∨ a = [0]

def decIsZeroAux (a : List Nat) : Decidable (isZeroAux a) :=
  if h : a = [] ∨ a = [0] then
    isTrue h
  else
    isFalse h

theorem isZeroAux_of_nil : isZeroAux [] := .inl rfl
theorem isZeroAux_of_zero : isZeroAux [0] := .inr rfl

end isZeroAux

section AllDigitsLtBase

def allDigitsLtBase (a : List Nat) (base : Nat) : Prop := a.all (· < base)

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

instance instAllDigitsLtBase (a : List Nat) (base : Nat) : Decidable (allDigitsLtBase a base) := decAllDigitsLtBase a base

theorem allDigitsLtBase_of_nil {a : List Nat} {base : Nat} (ha : a = []) :
  allDigitsLtBase a base := by
  rw [allDigitsLtBase.eq_def, ha]
  exact List.all_nil

theorem allDigitsLtBase_cons_iff {x base : Nat} {xs : List Nat} :
  allDigitsLtBase (x::xs) base ↔ x < base ∧ allDigitsLtBase xs base := by
  unfold allDigitsLtBase
  simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]

theorem allDigitsLtBase_of_zero {a : List Nat} {base : Nat} (ha : a = [0]) (hb : 1 < base) :
  allDigitsLtBase a base := by
  rw [allDigitsLtBase.eq_def, ha]
  exact allDigitsLtBase_cons_iff.mpr (And.intro (Nat.pos_of_one_lt hb) (allDigitsLtBase_of_nil rfl))

end AllDigitsLtBase

section NoTrailingZeros

def noTrailingZeros (a : List Nat) : Prop := (h : a ≠ []) → a ≠ [0] → a.getLast h ≠ 0

def decNoTrailingZeros (a : List Nat) : Decidable (noTrailingZeros a) :=
  if h1 : a = [] then
    have : noTrailingZeros a := by
      rw [noTrailingZeros.eq_def]
      intro _
      contradiction
    isTrue this
  else
    if h2 : a = [0] then
      have : noTrailingZeros a := by
        rw [noTrailingZeros.eq_def]
        intro _ _
        contradiction
      isTrue this
    else
      if h3 : a.getLast h1 = 0 then
        have : ¬ noTrailingZeros a := by
          rw [noTrailingZeros.eq_def]
          intro h4
          exact absurd h3 (h4 h1 h2)
        isFalse this
      else
        have : noTrailingZeros a := by
          rw [noTrailingZeros.eq_def]
          intro _ _
          exact h3
        isTrue this

instance instNoTrailingZeros (a : List Nat) : Decidable (noTrailingZeros a) := decNoTrailingZeros a

theorem noTrailingZeros_of_nil {a : List Nat} (ha : a = []) : noTrailingZeros a := by
  rw [noTrailingZeros.eq_def]
  intro hnn
  contradiction

theorem noTrailingZeros_of_zero {a : List Nat} (ha : a = [0]) : noTrailingZeros a := by
  rw [noTrailingZeros.eq_def]
  intro _ hnz
  contradiction

theorem noTrailingZeros_of_singleton {a : List Nat} {n : Nat} (ha : a = [n]) : noTrailingZeros a := by
  if hn : n = 0 then
    rw [hn] at ha
    exact noTrailingZeros_of_zero ha
  else
    rw [noTrailingZeros.eq_def, ha]
    intro hnn hnz
    rw [List.getLast_singleton]
    exact hn

theorem noTrailingZeros_cons_of (x : Nat) {xs : List Nat}
  (hnz : xs ≠ [0]) (hntz : noTrailingZeros xs) : noTrailingZeros (x::xs) := by
  rw [noTrailingZeros.eq_def] at ⊢ hntz
  intro h1 h2
  match g : xs with
  | [] =>
    have : ¬x = 0 := by rwa [← List.singleton_inj]
    rwa [List.getLast_singleton h1]
  | x::xs =>
    rw [List.getLast_cons_cons]
    exact (hntz (List.cons_ne_nil x xs)) hnz

theorem tail_ne_zero_of (x : Nat) {xs : List Nat}
  (hntz : noTrailingZeros (x::xs)) : xs ≠ [0] := by
  rw [noTrailingZeros.eq_def] at hntz
  have h1 : x :: xs ≠ [] := List.cons_ne_nil x xs
  have h2 : x :: xs ≠ [0] → (x :: xs).getLast h1 ≠ 0 := hntz h1
  if h3 : x :: xs = [0] then
    rw [(List.cons.inj h3).right]
    exact Ne.symm (List.cons_ne_nil 0 [])
  else
    false_or_by_contra; rename _ => h4 -- : xs = [0]
    have h5 : xs ≠ [] := by rw [h4]; exact List.cons_ne_nil 0 []
    have h6 : (x :: xs).getLast h1 ≠ 0 := hntz h1 h3
    have h7 : xs.getLast h5 ≠ 0 := by rwa [List.getLast_cons h5] at h6
    have h8 : xs.getLast h5 = 0 := by simp only [h4, List.getLast_singleton]
    contradiction

theorem noTrailingZeros_tail_of (x : Nat) {xs : List Nat}
  (hntz : noTrailingZeros (x::xs)) : noTrailingZeros xs := by
  intro h1 h2
  have h3 : x::xs ≠ [] := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  have h4 : x::xs ≠ [0] := by
    false_or_by_contra; rename _ => h5
    exact absurd (List.cons_singleton_iff_and_eq_nil.mp h5).right h1
  have h6 : (x::xs).getLast h3 = xs.getLast h1 := List.getLast_cons h1
  have h7 : (x::xs).getLast h3 ≠ 0 := hntz h3 h4
  rwa [h6] at h7

end NoTrailingZeros

section ToHexDigit

/-!
returns the hexadecimal digit of a number between 0 and 15 (including)

The use of `decide (digit < 16)` as type of `h` - instead of the
more straightforward `digit < 16` - is motivated by
https://github.com/leanprover/lean4/issues/9292.
-/
def toHexDigit (digit : Nat) (h : decide (digit < 16)) : String :=
  match digit with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => s!"{digit}"
  | 10 => "a"
  | 11 => "b"
  | 12 => "c"
  | 13 => "d"
  | 14 => "e"
  | 15 => "f"

end ToHexDigit

section NormalizeDigits

/-!
maps an empty list of digits to `[0]` or reverses them otherwise
-/
def normalizeDigits (a : List Nat) : List Nat := if a = [] then [0] else a.reverse

/-!
asserts that `normalizeDigits` only returns `[0]` or the reversed input
-/
theorem normalizeDigits_eq_or {a : List Nat} :
  normalizeDigits a = [0] ∨ (normalizeDigits a) = a.reverse := by
  by_cases ha : a = [] <;> simp only [normalizeDigits, ha, reduceIte, true_or, or_true]

end NormalizeDigits

section NormalizeDigits_AllDigitsLtBase

/-!
asserts that all digits returned by `normalizeDigits_allLtBase_of_allLtBase` are less than
`base` if this holds true for the input
-/
theorem normalizeDigits_allLtBase_of_allLtBase {a : List Nat} {base : Nat} (hb : 1 < base)
  (haa : allDigitsLtBase a base): allDigitsLtBase (normalizeDigits a) base := by
  have g : normalizeDigits a = [0] ∨ (normalizeDigits a) = a.reverse := normalizeDigits_eq_or
  cases g with
  | inl gl => exact allDigitsLtBase_of_zero gl hb
  | inr gr => rwa [gr, allDigitsLtBase.eq_def, List.all_reverse, ← allDigitsLtBase.eq_def]

end NormalizeDigits_AllDigitsLtBase

section ToNatAux

def toNatAux (a : List Nat) (base : Nat) : Nat :=
  (helper a base 1 0).snd where
  helper (a : List Nat) (base factor acc : Nat) : Nat × Nat :=
    match a with
    | [] => (factor, acc)
    | x::xs => helper xs base (factor * base) (x * factor + acc)

theorem toNatAux_helper_nil_eq {base factor acc : Nat} : toNatAux.helper [] base factor acc = (factor, acc) := by
  unfold toNatAux.helper
  rfl

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

theorem toNatAux_nil_eq_zero {base : Nat} : toNatAux [] base = 0 := by
  unfold toNatAux
  rfl

theorem toNatAux_zero_eq_zero {base : Nat} : toNatAux [0] base = 0 := by
  unfold toNatAux
  rfl

theorem toNatAux_cons_eq {xs : List Nat} {x base : Nat} :
  toNatAux (x::xs) base = x + base * (toNatAux xs base) := by
  rw [toNatAux.eq_def, toNatAux.helper.eq_def]
  simp only []
  rw [toNatAux.eq_def, toNatAux_helper_eq, Nat.mul_one, Nat.one_mul, Nat.add_zero]

theorem toNatAux_eq_zero_iff {a : List Nat} {base : Nat} (ha : noTrailingZeros a) (hb : 1 < base) :
  toNatAux a base = 0 ↔ isZeroAux a := by
  constructor
  · intro h
    induction a with
    | nil =>
      rw [toNatAux] at h
      simp only [isZeroAux, true_or]
    | cons x xs ih =>
      rw [toNatAux_cons_eq] at h
      have h1 : x = 0 ∧ base * (toNatAux xs base) = 0 := Nat.eq_zero_of_add_eq_zero h
      have h2 : toNatAux xs base = 0 :=
        Or.resolve_left (Nat.zero_eq_mul.mp (Eq.symm h1.right)) (Nat.ne_zero_of_lt hb)
      have h3 : isZeroAux xs := ih (noTrailingZeros_tail_of x ha) h2
      have h4 : xs = [] := by
        rw [isZeroAux.eq_def] at h3
        exact Or.resolve_right h3 (tail_ne_zero_of x ha)
      have h5 : x::xs = [0] := by
        rw [List.cons.injEq]
        exact And.intro h1.left h4
      exact .inr h5
  · intro h
    cases h with
    | inl hl => rw [hl, toNatAux_nil_eq_zero]
    | inr hr => rw [hr, toNatAux_zero_eq_zero]

end ToNatAux

section Prune

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

theorem prune_of_nil_zero {a : List Nat} {n base : Nat} (ha : a = []) (hn : n = 0) (hb : 1 < base) :
  prune a n base hb = [] := by
  rw [prune.eq_def]
  match a, n with | [], 0 => simp only []

theorem prune_eq_nil_iff {a : List Nat} {n base : Nat}  (hb : 1 < base) :
  prune a n base hb = [] ↔ a = [] ∧ n = 0 := by
  constructor
  · intro h
    rw [prune.eq_def] at h
    match ga : a, gn : n with | [], 0 => exact And.intro rfl rfl
  · intro h
    exact prune_of_nil_zero h.left h.right hb

theorem prune_ne_zero_of_nil {a : List Nat} {n base : Nat} (ha : a = []) (hb : 1 < base) :
  prune a n base hb ≠ [0] := by
  rw [prune.eq_def]
  match ga : a, gn : n with
  | [], 0 => simp only []; exact Ne.symm (List.cons_ne_nil 0 [])
  | [], k + 1 =>
    simp only []
    false_or_by_contra; rename _ => h1
    rw [List.cons.injEq] at h1
    have : ((k + 1) / base) = 0 := ((prune_eq_nil_iff hb).mp h1.right).right
    have : base = 0 ∨ k + 1 < base := Nat.div_eq_zero_iff.mp this
    have : k + 1 < base := Or.resolve_left this (Nat.ne_zero_of_lt hb)
    have : ¬ base ≤ k + 1 := Nat.not_le_of_lt this
    have h2 : (k + 1) % base = k + 1 := by
      rw [Nat.mod_eq]
      simp only [this, and_false, reduceIte]
    have h3 : (k + 1) % base = 0 := h1.left
    have h4 : k + 1 ≠ 0 := Nat.ne_zero_of_lt (Nat.succ_pos k)
    rw [h2] at h3
    contradiction

theorem and_nil_zero_of_cons_prune_eq_zero {a : List Nat} {n base : Nat} (hb : 1 < base)
  (h : n % base :: prune a (n / base) base hb = [0]) : a = [] ∧ n = 0 := by
  have h1 : n % base = 0 ∧ prune a (n / base) base hb = [] :=
    List.cons_singleton_iff_and_eq_nil.mp h
  have h2 : n / base = 0 := ((prune_eq_nil_iff hb).mp h1.right).right
  have h3 : a = [] := ((prune_eq_nil_iff hb).mp h1.right).left
  have h4 : n < base := Nat.lt_of_div_eq_zero (Nat.lt_trans (by decide) hb) h2
  have h5 : n = 0 := Nat.eq_zero_of_lt_of_mod_eq_zero hb h1.left h4
  exact And.intro h3 h5

theorem prune_eq_zero_iff {a : List Nat} {n base : Nat} (hb : 1 < base) :
  prune a n base hb = [0] ↔ a = [0] ∧ n = 0 := by
  constructor
  · intro h
    rw [prune.eq_def] at h
    match ga : a, gn : n with
    | [], 0 => simp only [List.ne_cons_self] at h
    | [], k + 1 =>
      simp only [] at h
      have : k + 1 = 0 := (and_nil_zero_of_cons_prune_eq_zero hb h).right
      contradiction
    | x::xs, n =>
      simp only [] at h
      have h1 : xs = [] ∧ x + n = 0 := and_nil_zero_of_cons_prune_eq_zero hb h
      have h2 : x = 0 ∧ n = 0 := Nat.add_eq_zero_iff.mp h1.right
      rw [h1.left, h2.left, h2.right]
      exact And.intro rfl rfl
  · intro h
    have h1 : prune [] 0 base hb = [] := prune_of_nil_zero rfl rfl hb
    rw [h.left, h.right, prune.eq_def]
    simp only [Nat.add_zero, Nat.zero_mod, Nat.zero_div, h1]

theorem prune_ne_zero_of_ne_zero {a : List Nat} {n base : Nat} (ha : a ≠ [0]) (hb : 1 < base) :
  prune a n base hb ≠ [0] := by
  false_or_by_contra; rename _ => h1
  have h2 : a = [0] := ((prune_eq_zero_iff hb).mp h1).left
  contradiction

end Prune

section AllDigitsLtBase_Prune

theorem allDigitsLtBase_prune {a : List Nat} {n base : Nat} {hb : 1 < base} :
  allDigitsLtBase (prune a n base hb) base := by
  induction a generalizing n with
  | nil =>
    induction n using Nat.strongRecOn with
    | _ l ihl =>
      match gl : l with
      | 0 =>
        rw [prune.eq_def]
        simp only [allDigitsLtBase_of_nil]
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

section NoTrailingZeros_Prune

theorem noTrailingZeros_prune_of {a : List Nat} {n base : Nat} {hb : 1 < base} (hntz : noTrailingZeros a) :
  noTrailingZeros (prune a n base hb) := by
  induction a generalizing n with
  | nil =>
    induction n using Nat.strongRecOn with
    | _ l ihl =>
      match gl : l with
      | 0 => rw [prune.eq_def]; simp only [noTrailingZeros_of_nil]
      | k + 1 =>
        rw [prune.eq_def]
        simp only []
        have h1 : (k + 1) / base < k + 1  := Nat.div_lt_self (Nat.succ_pos k) hb
        have h2 : noTrailingZeros (prune [] ((k + 1) / base) base hb) := ihl ((k + 1) / base) h1
        have h3 : prune [] ((k + 1) / base) base hb ≠ [0] := prune_ne_zero_of_ne_zero (by decide) hb
        exact noTrailingZeros_cons_of ((k + 1) % base) h3 h2
  | cons x xs iha =>
    rw [prune.eq_def]
    simp only []
    have h1 : noTrailingZeros xs := noTrailingZeros_tail_of x hntz
    have h2 : noTrailingZeros (prune xs ((x + n) / base) base hb) := iha h1
    have h3 : xs ≠ [0] := tail_ne_zero_of x hntz
    have h4 : prune xs ((x + n) / base) base hb ≠ [0] := prune_ne_zero_of_ne_zero h3 hb
    exact noTrailingZeros_cons_of ((x + n) % base) h4 h2

end NoTrailingZeros_Prune

section ToNatAux_Prune

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
        rw [prune.eq_def, toNatAux_cons_eq, ihl ((k + 1) / base) h1, Nat.mul_add, ← Nat.add_assoc]
        rw [Nat.mod_add_div (k + 1) base, toNatAux_nil_eq_zero, Nat.mul_zero]
  | cons x xs iha =>
    rw [prune.eq_def, toNatAux_cons_eq, iha, Nat.mul_add, ← Nat.add_assoc]
    rw [Nat.mod_add_div, toNatAux_cons_eq, ← Nat.add_assoc]
    rw (occs := [2]) [Nat.add_comm]

end ToNatAux_Prune

section AddDigits

def addDigits : List Nat → List Nat → List Nat
  | [], [] => []
  | x::xs, [] => x::xs
  | [], y::ys => y::ys
  | x::xs, y::ys => (x + y)::(addDigits xs ys)

theorem addDigits_eq_nil_iff {a b : List Nat} : addDigits a b = [] ↔ a = [] ∧ b = [] := by
  constructor
  · intro h
    match ga : a, gb : b with
    | [], [] => exact And.intro rfl rfl
    | x::xs, [] | [], y::ys | x::xs, y::ys => contradiction
  . intro h
    match a, b with | [], [] => rfl

theorem addDigits_nil_eq {a : List Nat} : addDigits a [] = a := by
  rw [addDigits.eq_def]
  match ha : a with
  | [] | x::xs => rfl

theorem addDigits_cons_cons_eq {x y : Nat} {xs ys : List Nat} : addDigits (x::xs) (y::ys) = (x + y)::addDigits xs ys := rfl

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
      rw [addDigits_cons_cons_eq] at h
      have h1 : x + y = 0 ∧ addDigits xs ys = [] := List.cons.inj h
      have h2 : x = 0 ∧ y = 0 := Nat.add_eq_zero_iff.mp h1.left
      have h3 : xs = [] ∧ ys = [] := addDigits_eq_nil_iff.mp h1.right
      have h4 : x::xs = [0] := by rw [h2.left, h3.left]
      have h5 : y::ys = [0] := by rw [h2.right, h3.right]
      exact .inr (.inr (And.intro h4 h5))
  · intro h
    match ga : a, gb : b with | [0], [] | [], [0] | [0], [0] => decide

end AddDigits

section NoTrailingZeros_AddDigits

theorem noTrailingZeros_addDigits_of {a b : List Nat}
  (hantz : noTrailingZeros a) (hbntz : noTrailingZeros b) :
  noTrailingZeros (addDigits a b) := by
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
      have h1 : xs ≠ [0] := tail_ne_zero_of x hantz
      have h2 : ys ≠ [0] := tail_ne_zero_of y hbntz
      have h3 : addDigits xs ys ≠ [0] := by
        false_or_by_contra; rename _ => h4
        rcases addDigits_eq_zero_iff.mp h4 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> contradiction
      have h4 : noTrailingZeros (addDigits xs ys) := ih (noTrailingZeros_tail_of x hantz) (noTrailingZeros_tail_of y hbntz)
      rw [addDigits_cons_cons_eq]
      exact noTrailingZeros_cons_of (x + y) h3 h4

end NoTrailingZeros_AddDigits

section ToNatAux_addDigits

theorem toNatAux_addDigits_eq {a b : List Nat} {base : Nat} :
  toNatAux (addDigits a b) base = (toNatAux a base) + (toNatAux b base) := by
  have h2 : toNatAux [] base = 0 := by rw [toNatAux.eq_def, toNatAux.helper.eq_def]
  induction a generalizing b with
  | nil =>
    have h1 : addDigits [] b = b := by rw [addDigits.eq_def]; match b with | [] | v::vs => rfl
    rw [h1, h2, Nat.zero_add]
  | cons u us iha =>
    rw [addDigits.eq_def]
    match b with
    | [] => simp only [h2, Nat.add_zero]
    | v::vs =>
      simp only [toNatAux_cons_eq, iha]
      rw [Nat.add_assoc, Nat.add_comm, Nat.mul_add]
      rw (occs := .pos [3]) [Nat.add_comm]
      rw [← Nat.add_assoc]
      rw (occs := .pos [2, 1]) [Nat.add_comm]
      rw (occs := .pos [2]) [Nat.add_comm]
      rw [← Nat.add_assoc]

end ToNatAux_addDigits

section AddAux

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

theorem addAux_eq_singleton {a b : List Nat} (n : Nat) {base : Nat}
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
          | 0 => simp only []
          | k + 1 => simp only [h2]
    | cons y ys ihy =>
      rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
      simp only []
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
      simp only []
      rw [List.cons.injEq]
      have h1 : addDigits xs [] = xs := addDigits_nil_eq
      rw (occs := .pos [2]) [← h1]
      exact And.intro rfl ihx
    | y::ys  =>
      simp only []
      rw [List.cons.injEq]
      exact And.intro rfl ihx

/-!
alternative proof for `addAux_comm`
-/
example {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = addAux b a n base hb := by
  rw [addAux_eq_prune_addDigits, addDigits_comm, addAux_eq_prune_addDigits]

end AddAux_Prune_AddDigits

section AllDigitsLtBase_AddAux

theorem allDigitsLtBase_addAux {a b : List Nat} (n : Nat) {base : Nat} {hb : 1 < base} :
  allDigitsLtBase (addAux a b n base hb) base := by
  rw [addAux_eq_prune_addDigits hb]
  exact allDigitsLtBase_prune

end AllDigitsLtBase_AddAux

section NoTrailingZeros_AddAux

theorem noTrailingZeros_addAux_of_noTrailingZeros {a b : List Nat} {n base : Nat}
  (hantz : noTrailingZeros a) (hbntz : noTrailingZeros b) (hb : 1 < base) :
  noTrailingZeros (addAux a b n base hb) := by
  have h1 : noTrailingZeros (addDigits a b) := noTrailingZeros_addDigits_of hantz hbntz
  rw [addAux_eq_prune_addDigits hb]
  exact noTrailingZeros_prune_of h1

end NoTrailingZeros_AddAux

section ToNatAux_AddAux

theorem toNatAux_addAux_left_distrib {a b : List Nat} {base : Nat} {hb : 1 < base} :
  toNatAux (addAux a b 0 base hb) base = (toNatAux a base) + (toNatAux b base) := by
  rw [addAux_eq_prune_addDigits hb, toNatAux_prune_eq hb, toNatAux_addDigits_eq, Nat.zero_add]

end ToNatAux_AddAux

section SubAux

def subAuxCarry (x y base carry: Nat) (hb : 1 < base) : Nat × Nat :=
  if h : y ≤ x then
    (x - y, carry)
  else
    have h1 : x < y := Nat.lt_of_not_le h
    have h2 : x < x + base := Nat.lt_add_of_pos_right (Nat.lt_trans (by decide) hb)
    have : y - (x + base) < y - x := Nat.sub_lt_sub_left h1 h2
    subAuxCarry (x + base) y base (carry + 1) hb
  termination_by y - x

def cons? {α : Type} (a : α) (b : Option (List α)) : Option (List α) :=
  match b with
  | none => none
  | some l => some (a::l)

def subAux (a b : List Nat) (n base : Nat) (hb : 1 < base) : Option (List Nat) :=
  match a, b, n with
  | [], [], 0 => some []
  | [], [], _ + 1 => none
  | x::xs, [], n =>
    let (s, carry) := subAuxCarry x n base 0 hb
    cons? s (subAux xs [] carry base hb)
  | [], y::ys, n =>
    let (s, carry) := subAuxCarry y n base 0 hb
    cons? s (subAux ys [] carry base hb)
  | x::xs, y::ys, n =>
    let (s, carry) := subAuxCarry x (y + n) base 0 hb
    cons? s (subAux xs ys carry base hb)
  termination_by a.length + b.length

def discardTrailingZeros (a : List Nat) :=
  (helper a.reverse).reverse where
    helper : List Nat → List Nat
    | [] => []
    | [0] => [0]
    | 0::r => helper r
    | r => r

end SubAux
