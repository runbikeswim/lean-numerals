namespace List

theorem cons_singleton_iff_and_eq_nil {α : Type} {a b : α} {as : List α} :
  (a::as = [b]) ↔ (a = b ∧ as = []) := by simp only [cons.injEq]

end List

section AllDigitsLtBase

def allDigitsLtBase (a : List Nat) (base : Nat) : Prop := a.all (· < base)

theorem allDigitsLtBase_of_nil {a : List Nat} {base : Nat} (ha : a = []) :
  allDigitsLtBase a base := by
  rw [allDigitsLtBase.eq_def, ha]
  exact List.all_nil

theorem allDigitsLtBase_cons_iff {x base : Nat} {xs : List Nat} :
  allDigitsLtBase (x::xs) base ↔ x < base ∧ allDigitsLtBase xs base := by
  unfold allDigitsLtBase
  simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]

#check allDigitsLtBase_cons_iff

end AllDigitsLtBase

section NoTrailingZeros

def noTrailingZeros (a : List Nat) : Prop := (h : a ≠ []) → a ≠ [0] → a.getLast h ≠ 0

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

theorem noTrailingZeros_cons_of_ne_zero_noTrailingZeros (x : Nat) {xs : List Nat}
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

theorem noTrailingZeros_of_noTrailingZeros_cons (x : Nat) {xs : List Nat}
  (hntz : noTrailingZeros (x::xs)) : noTrailingZeros xs := by
  intro h1 h2
  have h3 : x::xs ≠ [] := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  have h4 : x::xs ≠ [0] := by
    false_or_by_contra; rename _ => hc
    exact absurd (List.cons_singleton_iff_and_eq_nil.mp hc).right h1
  have h5 : (x::xs).getLast h3 = xs.getLast h1 := List.getLast_cons h1
  have h6 : (x::xs).getLast h3 ≠ 0 := hntz h3 h4
  rwa [h5] at h6

end NoTrailingZeros

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

theorem toNatAux_cons_eq {xs : List Nat} {x base : Nat} :
  toNatAux (x::xs) base = x + base * (toNatAux xs base) := by
  rw [toNatAux.eq_def, toNatAux.helper.eq_def]
  simp only []
  rw [toNatAux.eq_def, toNatAux_helper_eq, Nat.mul_one, Nat.one_mul, Nat.add_zero]

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

theorem allDigitsLtBase_prune {a : List Nat} {n base : Nat} (hb : 1 < base) :
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

theorem noTrailingZeros_prune_of_noTrailingZeros {a : List Nat} {n base : Nat}
  (hntz : noTrailingZeros a) (hb : 1 < base) :
  noTrailingZeros (prune a n base hb) := by
  induction ha : a generalizing n with
  | nil =>
    induction n using Nat.strongRecOn with
    | _ l ihl =>
      match gl : l with
      | 0 => rw [prune.eq_def]; simp only [noTrailingZeros_of_nil]
      | k + 1 => sorry
  | cons x xs iha => sorry

theorem toNatAux_prune_eq_add_toNatAux {a : List Nat} {n base : Nat} (hb : 1 < base) :
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

end Prune

section AddDigits

def addDigits : List Nat → List Nat → List Nat
  | [], [] => []
  | x::xs, [] => x::xs
  | [], y::ys => y::ys
  | x::xs, y::ys => (x + y)::(addDigits xs ys)

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

theorem toNatAux_addDigits_eq_add_toNatAux_toNatAux {a b : List Nat} {base : Nat} :
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

end AddDigits

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

theorem addAux_eq_prune_addDigits {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = prune (addDigits a b) n base hb := by
  induction a generalizing b n with
  | nil =>
    induction b generalizing n with
    | nil =>
      induction n using Nat.strongRecOn with
      | _ l ihk =>
        if hl : l = 0 then
          rw [hl, addDigits.eq_def, addAux.eq_def, prune.eq_def]
        else
          rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
          have h1 : 0 < l := Nat.zero_lt_of_ne_zero hl
          have h2 : l / base < l := Nat.div_lt_self h1 hb
          have h3 : addAux [] [] (l / base) base hb = prune [] (l / base) base hb := by
            rw [ihk (l / base) h2, addDigits.eq_def]
          match hl : l with
          | 0 => simp only []
          | k + 1 => simp only [h3]
    | cons y ys ihy =>
      rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
      simp only []
      have h1 : addDigits [] ys = ys := by
          rw [addDigits.eq_def]
          match hys : ys with
          | [] => simp only []
          | y'::ys' => simp only []
      have h2 : addAux [] ys ((y + n) / base) base hb = prune ys ((y + n) / base) base hb := by
        rw [h1] at ihy
        exact ihy
      rw [List.cons.injEq]
      exact And.intro rfl h2
  | cons x xs ihx =>
    match hb : b with
    | [] =>
      rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
      simp only []
      have h1 : addDigits xs [] = xs := by
        rw [addDigits.eq_def]
        match hxs : xs with
        | [] => simp only []
        | x'::xs' => simp only []
      rw [List.cons.injEq]
      rw (occs := .pos [2]) [← h1]
      exact And.intro rfl ihx
    | y::ys  =>
      rw [addDigits.eq_def, addAux.eq_def, prune.eq_def]
      simp only []
      rw [List.cons.injEq]
      exact And.intro rfl ihx

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

/-!
alternative proof for `addAux_comm`
-/
example {a b : List Nat} {n base : Nat} (hb : 1 < base) :
  addAux a b n base hb = addAux b a n base hb := by
  rw [addAux_eq_prune_addDigits, addDigits_comm, addAux_eq_prune_addDigits]


end AddAux
