/-
Copyright (c) 2025 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.NatGtOne
import Numerals.Basic

open TZNumeral

def zeroBase10 : Numeral10 := Numeral.ofNat 0 NumeralAux.base10

#eval @TZNumeral.toString NumeralAux.base10 zeroBase10

def oneBase10 : Numeral10 where
  digits := [1]
  noTZ := by
    simp only [TZNumeral.noTrailingZero]
    decide

#eval @TZNumeral.toString NumeralAux.base10 oneBase10

def twoBase3 : Numeral ⟨3, by decide⟩ where
  digits := [2]
  noTZ := by
    simp only [TZNumeral.noTrailingZero]
    decide

def threeBase2 : Numeral2 where
  digits := [1, 1]
  noTZ := by
    simp only [TZNumeral.noTrailingZero]
    decide

def fourBase2 : Numeral2 where
  digits := [0, 0, 1]
  noTZ := by
    simp only [TZNumeral.noTrailingZero]
    decide
def twelveBase10 : Numeral10 where
  digits := [2, 1]
  noTZ := by
    simp only [TZNumeral.noTrailingZero]
    decide

def thirteenBase8 : Numeral8 where
  digits := [5, 1]
  noTZ := by
    simp only [TZNumeral.noTrailingZero]
    decide


def abcdefBase16 : Numeral16 where
  digits := [15, 14, 13, 12, 11, 10]
  noTZ := by
    simp only [TZNumeral.noTrailingZero]
    decide

def threeHundredSixtyBase60 : Numeral ⟨60, by decide⟩ where
  digits := [0, 6]
  noTZ := by
    simp only [TZNumeral.noTrailingZero]
    decide

def fibonacci (n : Nat) : Numeral10 :=
  (helper n zeroBase10 oneBase10).fst where
  helper (n : Nat) (a b : Numeral10) : Numeral10 × Numeral10 :=
  match n with
  | 0 => (a, b)
  | k + 1 => helper k b (a.hAdd b)

def main : IO Unit := do
  let n := 123
  let m := fibonacci n

  println! s!"{m.toNat}"
