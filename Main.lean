import Numerals

/-
TODO: uncomment

open Numeral

def nilBase10 : Numeral := {
    digits := [],
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, not_true_eq_false, List.ne_cons_self,
                        not_false_eq_true, forall_const, forall_false]
  }

def zeroBase10 : Numeral := default

def oneBase10 : Numeral := {
    digits := [1],
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, List.cons_ne_self, not_false_eq_true,
                        List.cons.injEq, Nat.succ_ne_self, and_true,
                        List.getLast_singleton, imp_self]
  }

def twoBase3 : Numeral := {
    digits := [2],
    base := 3,
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, List.cons_ne_self, not_false_eq_true,
                        List.cons.injEq, and_true, List.getLast_singleton, imp_self]
  }

def threeBase2 : Numeral := {
    digits := [1, 1],
    base := 2,
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.cons.injEq,
                        Nat.succ_ne_self, List.cons_ne_self, and_self, and_true,
                        List.getLast_cons_of_singleton, imp_self]
  }

def fourBase2 : Numeral := {
    digits := [0, 0, 1],
    base := 2
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                        List.cons.injEq, and_false, List.getLast_cons_cons, and_true,
                        List.getLast_cons_of_singleton, Nat.succ_ne_self, imp_self]
  }

def twelveBase10 : Numeral := {
    digits := [2, 1],
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                        List.cons.injEq, List.cons_ne_self, and_self, and_true,
                        List.getLast_cons_of_singleton, Nat.succ_ne_self, imp_self]
  }

def thirteenBase8 : Numeral := {
    digits := [5, 1],
    base := 8
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                        List.cons.injEq, List.cons_ne_self, and_self, and_true,
                        List.getLast_cons_of_singleton, Nat.succ_ne_self, imp_self]
  }

def abcdefBase16 : Numeral := {
    digits := [15, 14, 13, 12, 11, 10],
    base := 16,
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                        List.cons.injEq, and_self, List.getLast_cons_cons, and_true,
                        List.getLast_cons_of_singleton, imp_self]
  }

def threeHundredSixtyBase60 : Numeral := {
    digits := [0, 6],
    base := 60,
    baseGtOne := by decide,
    allDigitsLtBase := by decide,
    noTrailingZeros := by simp only [ne_eq, reduceCtorEq, not_false_eq_true,
                        List.cons.injEq, List.cons_ne_self, and_false, and_true,
                        List.getLast_cons_of_singleton, imp_self]
  }

def numerals := [
    nilBase10, zeroBase10, oneBase10, twoBase3, threeBase2,
    fourBase2, twelveBase10, thirteenBase8, abcdefBase16, threeHundredSixtyBase60
  ]

def main : IO Unit := do
  for n in numerals do
    println! s!"{repr n}: {n} : {n.rebase 10 (by decide)}"

  for (b, a) in numerals.tail.zip numerals do
    println! s!"{a} + {b}: {a + b}"

-/

def main : IO Unit := do
  println! "done!"
