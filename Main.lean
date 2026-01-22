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
    noTrailingZeros := by decide
  }

def zeroBase10 : Numeral10 := default

def oneBase10 : Numeral10 := {
    digits := [1],
    allDigitsLtBase := by decide,
    noTrailingZeros := by decide
  }

def twoBase3 : Numeral 3 (by decide) := {
    digits := [2],
    allDigitsLtBase := by decide,
    noTrailingZeros := by decide
  }

def threeBase2 : Numeral2 := {
    digits := [1, 1],
    allDigitsLtBase := by decide,
    noTrailingZeros := by decide
  }

def fourBase2 : Numeral2 := {
    digits := [0, 0, 1],
    allDigitsLtBase := by decide,
    noTrailingZeros := by decide
  }

def twelveBase10 : Numeral10 := {
    digits := [2, 1],
    allDigitsLtBase := by decide,
    noTrailingZeros := by decide
  }

def thirteenBase8 : Numeral8 := {
    digits := [5, 1],
    allDigitsLtBase := by decide,
    noTrailingZeros := by decide
  }

def abcdefBase16 : Numeral16 := {
    digits := [15, 14, 13, 12, 11, 10],
    allDigitsLtBase := by decide,
    noTrailingZeros := by decide
  }

def threeHundredSixtyBase60 : Numeral 60 (by decide):= {
    digits := [0, 6],

    allDigitsLtBase := by decide,
    noTrailingZeros := by decide
  }

def numerals : List NumeralWithBase := [
    nilBase10.toWithBase,
    zeroBase10.toWithBase,
    oneBase10.toWithBase,
    twoBase3.toWithBase,
    threeBase2.toWithBase,
    fourBase2.toWithBase,
    twelveBase10.toWithBase,
    thirteenBase8.toWithBase,
    abcdefBase16.toWithBase,
    threeHundredSixtyBase60.toWithBase
  ]

def main : IO Unit := do
  for n in numerals do
    println! s!"{repr n.val}: {n.val} : {n.val.rebase 10 (by decide)}"

  for i in [0:15] do
    for j in [i:15] do
      let a : Numeral10 := ofNat i 10 (by decide)
      let b : Numeral10 := ofNat j 10 (by decide)
      println! s!"{i} + {j}: {a + b}"
