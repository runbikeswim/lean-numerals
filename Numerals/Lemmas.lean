
def allDigitsLtBase_cons {n base : Nat} {a : List Nat} :
  (n::a).all (· < base) ↔ n < base ∧ a.all (· < base) := by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]


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

theorem noTrailingZeros_cons_of_ne_zero_of_noTrailingZeros (n : Nat) {a : List Nat}
  (hanz : a ≠ [0]) (hantz : noTrailingZeros a) : noTrailingZeros (n::a) := by
  rw [noTrailingZeros.eq_def] at ⊢ hantz
  intro hnn hnz
  match ha : a with
  | [] =>
    have hnne : ¬n = 0 := by rwa [← List.singleton_inj]
    rwa [List.getLast_singleton hnn]
  | x::xs =>
    rw [List.getLast_cons_cons]
    exact (hantz (List.cons_ne_nil x xs)) hanz

#check noTrailingZeros_cons_of_ne_zero_of_noTrailingZeros

end NoTrailingZeros


section ToNatAux

def toNatAux (a : List Nat) (base : Nat) : Nat :=
  (helper a base 1 0).snd where
  helper (a : List Nat) (base factor acc : Nat) : Nat × Nat :=
    match a with
    | [] => (factor, acc)
    | x::xs => helper xs base (factor * base) (x * factor + acc)

theorem toNatAux_helper_nil {base factor acc : Nat} : toNatAux.helper [] base factor acc  = (factor, acc) := by
  unfold toNatAux.helper
  rfl

theorem toNatAux_helper_factor_acc {a : List Nat} {base factor acc : Nat} :
  (toNatAux.helper a base factor acc).snd = acc + factor * (toNatAux.helper a base 1 0).snd := by
  induction a generalizing factor acc with
  | nil => simp_all only [toNatAux_helper_nil, Nat.mul_zero, Nat.add_zero]
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
  rw [toNatAux.eq_def, toNatAux_helper_factor_acc, Nat.mul_one, Nat.one_mul, Nat.add_zero]

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

theorem prune_allDigitsLtBase {a : List Nat} {n base : Nat} (hb : 1 < base) :
  (prune a n base hb).all (· < base) := by
  induction a generalizing n with
  | nil =>
    induction n using Nat.strongRecOn with
    | _ l ihl =>
      match gl : l with
      | 0 =>
        rw [prune.eq_def]
        simp only [List.all_nil]
      | k + 1 =>
        rw [prune.eq_def]
        simp only [allDigitsLtBase_cons]
        have h1 : (k + 1) / base < (k + 1) := Nat.div_lt_self (Nat.succ_pos k) hb
        exact And.intro (Nat.mod_lt (k + 1) (Nat.lt_trans (by decide) hb)) (ihl ((k + 1) / base) h1)
  | cons x xs iha =>
    rw [prune.eq_def]
    simp only [allDigitsLtBase_cons]
    exact And.intro (Nat.mod_lt (x + n) (Nat.lt_trans (by decide) hb)) iha

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
  | nil => match hb : b with | [] | v::vs => rfl
  | cons u us iha =>
    match hb : b with
    | [] => rfl
    | v::vs  =>
      unfold addDigits
      rw [List.cons.injEq, Nat.add_comm u v]
      exact And.intro rfl iha

end AddDigits
