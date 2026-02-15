/-
Copyright (c) 2025 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic

open Numeral

def nilBase10 : Numeral10 := {
    digits := [],
    allDigitsLtBase := by decide,
    noTrailingZero := by decide
  }

#eval nilBase10
#eval s!"{nilBase10}"

def zeroBase10 : Numeral10 := default

#eval zeroBase10
#eval s!"{zeroBase10}"

def oneBase10 : Numeral10 := {
    digits := [1],
    allDigitsLtBase := by decide,
    noTrailingZero := by decide
  }

#eval oneBase10
#eval s!"{oneBase10}"

def twoBase3 : Numeral 3 (by decide) := {
    digits := [2],
    allDigitsLtBase := by decide,
    noTrailingZero := by decide
  }

#eval twoBase3
#eval s!"{twoBase3}"

def threeBase2 : Numeral2 := {
    digits := [1, 1],
    allDigitsLtBase := by decide,
    noTrailingZero := by decide
  }

#eval threeBase2
#eval s!"{threeBase2}"

def fourBase2 : Numeral2 := {
    digits := [0, 0, 1],
    allDigitsLtBase := by decide,
    noTrailingZero := by decide
  }

#eval fourBase2
#eval s!"{fourBase2}"

def twelveBase10 : Numeral10 := {
    digits := [2, 1],
    allDigitsLtBase := by decide,
    noTrailingZero := by decide
  }

#eval twelveBase10
#eval s!"{twelveBase10}"

def thirteenBase8 : Numeral8 := {
    digits := [5, 1],
    allDigitsLtBase := by decide,
    noTrailingZero := by decide
  }

#eval thirteenBase8
#eval s!"{thirteenBase8}"

def abcdefBase16 : Numeral16 := {
    digits := [15, 14, 13, 12, 11, 10],
    allDigitsLtBase := by decide,
    noTrailingZero := by decide
  }

#eval abcdefBase16
#eval s!"{abcdefBase16}"

def threeHundredSixtyBase60 : Numeral 60 (by decide):= {
    digits := [0, 6],

    allDigitsLtBase := by decide,
    noTrailingZero := by decide
  }

#eval threeHundredSixtyBase60
#eval s!"{threeHundredSixtyBase60}"

def fibonacci (n : Nat) : Numeral10 :=
  (helper n zeroBase10 oneBase10).fst where
  helper (n : Nat) (a b : Numeral10) : Numeral10 × Numeral10 :=
  match n with
  | 0 => (a, b)
  | k + 1 => helper k b (a + b)

def main : IO Unit := do
  println! s!"fibonacci 100: {fibonacci 100}"
