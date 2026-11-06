module

public import Mathlib

@[expose] public section

namespace RAF.Polymer

/-- A binary word of fixed positive length, represented by its bit pattern. -/
abbrev Word (length : Nat) := Fin $ 2 ^ length

variable (n : Nat)

/-- Nonempty binary words of length at most `n`. The `Fin n` index `k`
represents length `k+1`. -/
abbrev Molecule  := Σ k : Fin n, Word $ k.val + 1

theorem card_molecule_sigma  :
    Fintype.card (Molecule n) = ∑ k : Fin n, 2 ^ (k.val + 1) := by
  simp_all

end RAF.Polymer
