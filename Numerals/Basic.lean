/-
Copyright (c) 2025 Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

section BasicLemmas

@[simp]
theorem or_elim_of_not {p q : Prop} (h : p ∨ q) (g : ¬ p) : q :=
  Or.elim h (fun t : p => False.elim (g t)) id

@[simp]
theorem iff_iff_iff_not_not {p q : Prop} : (p ↔ q) ↔ (¬p ↔ ¬q) := by
  constructor
  · intro h
    exact not_congr h
  · intro h
    have h' : ¬¬p ↔ ¬¬q := not_congr h
    rwa [Classical.not_not, Classical.not_not] at h'

end BasicLemmas

section NatLemmas

end NatLemmas

section ListLemmas

end ListLemmas

section Numerals

end Numerals
