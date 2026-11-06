module

public import Mathlib

@[expose] public section

namespace RAF.Polymer

/-- A binary word of fixed positive length, represented by its bit pattern. -/
abbrev Word (length : Nat) := Fin (2 ^ length)

/-- Nonempty binary words of length at most `n`. The `Fin n` index `k`
represents length `k+1`. -/
abbrev Molecule (n : Nat) := Σ k : Fin n, Word (k.val + 1)

theorem card_molecule_sigma (n : Nat) :
    Fintype.card (Molecule n) = ∑ k : Fin n, 2 ^ (k.val + 1) := by
  simp [Molecule, Word]

end RAF.Polymer
