module

public import Mathlib

@[expose] public section


namespace RAF.Polymer

section

/-- A binary word of fixed positive length, represented by its bit pattern. -/
abbrev Word (length : Nat) := Fin (2 ^ length)

/-- Nonempty binary words of length at most `n`. The `Fin n` index `k`
represents length `k+1`. -/
abbrev Molecule (n : Nat) := Σ k : Fin n, Word (k.val + 1)

theorem card_molecule_sigma (n : Nat) :
    Fintype.card (Molecule n) = ∑ k : Fin n, 2 ^ (k.val + 1) := by
    simp 
/-- A split-position bidirectional reaction. The index `k` represents a
product of length `k+1`; `split : Fin k` records one of its `k` splits. -/
abbrev Reaction (n : Nat) := Σ k : Fin n, Word (k.val + 1) × Fin k.val

theorem card_reaction_sigma (n : Nat) :
    Fintype.card (Reaction n) = ∑ k : Fin n, 2 ^ (k.val + 1) * k.val := by
    simp 
end

end RAF.Polymer
