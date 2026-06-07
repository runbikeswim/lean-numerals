/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Lemmas

open NumeralAux

section ToString

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
  | 10 => s!"{String.join r}"
  | 16 => s!"0x{String.join r}"
  | _ => s!"({base}){",".intercalate r}"
  where natsToStrings (digits : List Nat) (base : Nat) (ha : allDigitsLtBase digits base) : List String :=
    match digits with
    | [] => []
    | x::xs =>
      have hxs : x < base ∧ allDigitsLtBase xs base := allDigitsLtBase_cons_iff.mp ha
      (digitToString x base hxs.left)::(natsToStrings xs base hxs.right)

#eval toStringAux [59,59] 60 (by decide)

end ToString

section OfString

namespace String.Slice

/--
`String.Slice` has no `Repr` but uses `ToString` instead.
However, the default implementation does not provide the surrounding quotes (") and that's
an own instance is provided that overrides the default.

Before defining an instance for `Repr String.Slice`:
```
#synth (Repr String.Slice) -- failed to synthesize Repr Slice
#synth (ToString String.Slice) -- instToString
#eval "abc" -- "abc"
#eval "abc".toSlice -- abc without surrounding quotes
```

After defining the own instance:
```
#synth (Repr String.Slice) -- instRepr_semVer
#eval "abc".toSlice -- "abc" with surrounding quotes
```
-/
instance : Repr String.Slice where
  reprPrec s _ := s.toString.quote

/--
Returns the `n` preceding characters of `s` in underlying string as `String.Slice`.
If there are less then `n` characters before `s`, all characters preceding `s` are returned.
```
def s : String.Slice := "red green blue".slice ⟨⟨4⟩, by decide⟩ ⟨⟨9⟩, by decide⟩ (by decide)

#eval s -- "green"
#eval s.getPrefixn 2 -- "d "
#eval s.getPrefixn 10 -- "red "
```
-/
def getPrefixn (s : String.Slice) (n : Nat) : String.Slice :=
  let p := s.startInclusive.prevn n
  have : p ≤ s.startInclusive := by
    unfold p
    exact String.Pos.prevn_le
  s.str.slice p s.startInclusive this

/--
Returns the full prefix of `s` (i.e. all characters before `s`) in the underlying string
as `String.Slice`.
-/
def getPrefix (s : String.Slice) : String.Slice :=
  have : s.str.startPos ≤ s.startInclusive := by
    simp only [String.Pos.startPos_le]
  s.str.slice s.str.startPos s.startInclusive this

/--
Returns the `n` succeeding characters of `s` in underlying string as `String.Slice`.
If there are less then `n` characters after `s`, all characters following `s` are returned.
```
def s : String.Slice := "red green blue".slice ⟨⟨4⟩, by decide⟩ ⟨⟨9⟩, by decide⟩ (by decide)

#eval s -- "green"
#eval s.getSuffixn 2 -- " b"
#eval s.getSuffixn 10 -- " blue"
```
-/
def getSuffixn (s : String.Slice) (n : Nat) : String.Slice :=
  let p := s.endExclusive.nextn n
  have : s.endExclusive ≤ p := by
    unfold p
    exact String.Pos.le_nextn
  s.str.slice s.endExclusive p this

/--
Returns the full suffix of `s` (i.e. all characters after `s`) within the underlying string
as `String.Slice`.
-/
def getSuffix (s : String.Slice) : String.Slice :=
  have : s.endExclusive ≤ s.str.endPos := String.Pos.le_endPos s.endExclusive
  s.str.slice s.endExclusive s.str.endPos this

end String.Slice

structure ParserError where
  input : Option String.Slice
  message : String
deriving Repr

namespace ParserError

/--
Returns a formatted string that contains the error message some context if some slice is provided.
-/
def toString (e : ParserError) : String :=
  match e.input with
  | some slice => s!"'{slice}' {e.message}"
  | none => e.message

instance : ToString ParserError := ⟨toString⟩

/--
unknown error
-/
instance : Inhabited ParserError := ⟨{input := none, message := "unknown error"}⟩

end ParserError

/--
Parsers return a `ParserResult`. If parsing was successful, some value of type `α` is included,
which has by retrieved from the input. If the input was incorrect, `ParserResult` is wrapper of a `ParserError`.
-/
inductive ParserResult (α : Type) where
  | success : α → ParserResult α
  | failure : ParserError → ParserResult α

namespace ParserResult

def toString {α : Type} [ToString α] (res : ParserResult α) : String :=
  match res with
  | .success val => ToString.toString val
  | .failure errors => ToString.toString errors

instance {α : Type} [ToString α] : ToString (ParserResult α) := ⟨toString⟩

end ParserResult

structure DigitsOfBase where
  base : Nat
  digits : List Nat
deriving Repr

def baseParser (s : String.Slice) : String.Slice × (ParserResult Nat) :=
  match s.front with
  | '0' =>
    let t := s.drop 1
    match t.front with
    | 'b' => (t.drop 1, .success 2)
    | 'o' => (t.drop 1, .success 8)
    | 'x' => (t.drop 1, .success 16)
    | _ => (s, .success 10)
  | '(' =>
    let u := (s.drop 1).takeWhile (· != ')')
    match u.toNat? with
    | some n => (s.drop (2 + u.positions.length), .success n)
    | none => (s, .failure { input := s, message := "does not start with a decimal numeral enclosed in '(' and ')'" })
  | _ => (s, .success 10)

def charToValue? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then
    some (c.toNat - '0'.toNat)
  else if 'a' <= c && c <= 'f' then
    some (10 + c.toNat - 'a'.toNat)
  else none

def singleDigitParser (s : String.Slice) (base : Nat) : String.Slice × (ParserResult Nat) :=
  match charToValue? s.front with
  | some n =>
    if n < base then
      (s.take 1, .success n)
    else
      (
        s,
        .failure {
          input := s
          message := s!"starts with a digit that is larger than {base}",

        }
      )
  | none => (
      s,
      .failure {
        input := s
        message := "starts with a character that is not a digit of base 2, 8, 10 or 16",
      }
    )

def digitsParser (s : String.Slice) (base : Nat) : String.Slice × (ParserResult DigitsOfBase) :=
  helper s.positions.toList base where
  helper (l : List { p // p ≠ s.endPos}) (base : Nat) :=
    match l with
    | [] => (s.sliceFrom s.endPos, .success {base := base, digits := []})
    | x::xs =>
      match singleDigitParser (s.sliceFrom x) base with
      | (t, .failure e) => (t, .failure e)
      | (_, .success n) =>
        match helper xs base with
        | (u, .success d) => (u, .success {d with digits := n :: d.digits})
        | (u, .failure e) => (u, .failure e)

def decimalNumbersParser (s : String.Slice) (base : Nat) : String.Slice × (ParserResult DigitsOfBase) :=
  helper (s.split ',').toList base where
  helper (l : List String.Slice) (base : Nat) :=
    match l with
    | [] => (s.sliceFrom s.endPos, .success {base := base, digits := []})
    | x::xs =>
      match x.toNat? with
      | none => (s.sliceFrom s.endPos, .failure {input := x, message := "is not a decimal number"})
      | some n =>
        if n < base then
          match helper xs base with
          | (u, .failure e) => (u, .failure e)
          | (u, .success d) => (u, .success {d with digits := n :: d.digits})
        else
          (
            s.sliceFrom s.endPos,
            .failure {input := s, message := s!"contains '{n}' with is not less than base '{base}'"}
          )

def parser (s : String.Slice) : String.Slice × (ParserResult DigitsOfBase) :=
  match baseParser s with
  | (t, .success b) =>
    match b with
    | 2 | 8 | 10 | 16 => digitsParser t b
    | _ => decimalNumbersParser t b
  | (t, .failure e) => (t, .failure e)

def ofStringAux? (s: String) : Option (Nat × (List Nat)) :=
  match parser s.toSlice with
  | (_, .success d) => some (d.base, d.digits)
  | (_, .failure _) => none

#eval ofStringAux? "0b10100"
#eval ofStringAux? "0o01234567"
#eval ofStringAux? "1234567890"
#eval ofStringAux? "0x0123456789abcdef"
#eval ofStringAux? "(60)12,34,56"

end OfString
