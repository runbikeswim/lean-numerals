/-
Copyright (c) 2025, 2026 Dr. Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Stefan Kusterer
-/

import Numerals.Basic

namespace Numeral

section OfString

namespace String.Slice

/-
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

/-
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

/-
Returns the full prefix of `s` (i.e. all characters before `s`) in the underlying string
as `String.Slice`.
-/
def getPrefix (s : String.Slice) : String.Slice :=
  have : s.str.startPos ≤ s.startInclusive := by
    simp only [String.Pos.startPos_le]
  s.str.slice s.str.startPos s.startInclusive this

/-
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

/-
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

/-
Returns a formatted string that contains the error message some context if some slice is provided.
-/
def toString (e : ParserError) : String :=
  match e.input with
  | some slice => s!"'{slice}' {e.message}"
  | none => e.message

instance : ToString ParserError := ⟨toString⟩

/-
unknown error
-/
instance : Inhabited ParserError := ⟨{input := none, message := "unknown error"}⟩

end ParserError

/-
Parsers return a `ParserResult`. If parsing was successful, some value of type `α` is included,
which has by retrieved from the input. If the input was incorrect, `ParserResult` is wrapper of a `ParserError`.
-/
inductive ParserResult (α : Type) where
  | success : α → ParserResult α
  | failure : ParserError → ParserResult α

namespace ParserResult

instance (α : Type) : Inhabited (ParserResult α) := ⟨.failure default⟩

def val? {α : Type} (res : ParserResult α) : Option α :=
  match res with
  | .success val => some val
  | .failure _ => none

def val! {α : Type} [Inhabited α] (res : ParserResult α) : α :=
  match res with
  | .success val => val
  | .failure _ => panic! "cannot return a value because the parser returned failure"

def toString {α : Type} [ToString α] (res : ParserResult α) : String :=
  match res with
  | .success val => s!".success {val}"
  | .failure error => s!".failure {error}"

instance {α : Type} [ToString α] : ToString (ParserResult α) := ⟨toString⟩

end ParserResult

def parseBase (s : String.Slice) : String.Slice × (ParserResult NatGtOne) :=
  match s.front with
  | '0' =>
    let t := s.drop 1
    match t.front with
    | 'b' => (t.drop 1, .success ⟨2, by decide⟩)
    | 'o' => (t.drop 1, .success ⟨8, by decide⟩)
    | 'x' => (t.drop 1, .success ⟨16, by decide⟩)
    | _ => (s, .success ⟨10, by decide⟩)
  | '(' =>
    let u := (s.drop 1).takeWhile (· != ')')
    match u.toNat? with
    | some n =>
      if g : 1 < n then
        (s.drop (2 + u.positions.length), .success ⟨n,g⟩ )
      else
        (s, .failure { input := s, message := "the number enclosed in '(' and ')' is 1 or less" })
    | none => (s, .failure {input := s, message := "does not start with a decimal numeral enclosed in '(' and ')'"})
  | _ => (s, .success ⟨10, by decide⟩)

def charToDigit? (c : Char) (base : NatGtOne) : Option (Fin base.val) :=
  let iteLtBase (n : Nat) : Option (Fin base.val) := if h : n < base.val then some ⟨n,h⟩ else none
  if '0' <= c && c <= '9' then
    iteLtBase (c.toNat - '0'.toNat)
  else if 'a' <= c && c <= 'f' then
    iteLtBase (10 + c.toNat - 'a'.toNat)
  else none

def parseDigit (s : String.Slice) (base : NatGtOne) : String.Slice × (ParserResult (Fin base.val)) :=
  match charToDigit? s.front base with
  | some n => (s.take 1, .success n)
  | none => (
      s,
      .failure {
        input := s
        message := "starts with a character that is not a digit of base 2, 8, 10 or 16",
      }
    )

def parseDigits (s : String.Slice) (base : NatGtOne) : String.Slice × (ParserResult (List (Fin base.val))) :=
  helper s.positions.toList where
  helper (l : List { p // p ≠ s.endPos}) :=
  match l with
  | [] => (s.sliceFrom s.endPos, .success [])
  | x::xs =>
    match parseDigit (s.sliceFrom x) base with
    | (t, .failure e) => (t, .failure e)
    | (_, .success n) =>
      match helper xs with
      | (u, .success d) => (u, .success (n :: d))
      | (u, .failure e) => (u, .failure e)

def parseDecimalNumberSeq (s : String.Slice) (base : NatGtOne) : String.Slice × (ParserResult (List (Fin base.val))) :=
  helper (s.split ',').toList where
  helper (l : List String.Slice) :=
    match l with
    | [] => (s.sliceFrom s.endPos, .success [])
    | x::xs =>
      match x.toNat? with
      | none => (
          s.sliceFrom s.endPos,
          .failure {input := x, message := "is not a decimal number"}
        )
      | some n =>
        if g : n < base.val then
          match helper xs  with
          | (u, .failure e) => (u, .failure e)
          | (u, .success d) => (u, .success (⟨n, g⟩ :: d))
        else
          (
            s.sliceFrom s.endPos,
            .failure {
              input := s,
              message := s!"contains '{n}' with is not less than base '{base.val}'"
            }
          )

structure DigitsOfBase where
  base : NatGtOne
  digits : List (Fin base.val)

def parse (s : String.Slice) (base : NatGtOne) : String.Slice × (ParserResult (TZNumeral base)) :=
  match parseBase s with
  | (t, .success b) =>
    if base == b then
      match base.val with
      | 2 | 8 | 10 | 16 =>
        match parseDigits t base with
        | (u, .success l) => (u, .success {digits := l.reverse})
        | (u, .failure e) => (u, .failure e)
      | _ =>
        match parseDecimalNumberSeq t base with
        | (u, .success l) => (u, .success {digits := l.reverse})
        | (u, .failure e) => (u, .failure e)
    else
      (t, .failure {input := t, message := s!"found '{b.val}' as base instead of the expected value '{base.val}'"})
  | (t, .failure e) => (t, .failure e)

#eval (((parse "0b11000000" base2).snd).val!).toNat
#eval (((parse "123" base10).snd).val!).toNat
#eval (((parse "0o700" base8).snd).val!).toNat
#eval (((parse "0xaffe" base16).snd).val!).toNat

def base60 : NatGtOne := ⟨60, by decide⟩
#eval (parseBase "(60)1,45").snd
#eval (parseDecimalNumberSeq "1,45" base60)
#eval (((parse "(60)23,59" base60).snd).val!).toNat

end OfString

end Numeral
