module

public import proofs.RAF.Polymer.Words

@[expose] public section

namespace RAF.Polymer

variable (n : Nat)

/-- A split-position bidirectional reaction. The index `k` represents a
product of length `k+1`; `split : Fin k` records one of its `k` splits. -/
abbrev Reaction  := Σ k : Fin n, Word (k.val + 1) × Fin k.val

theorem card_reaction_sigma  :
    Fintype.card (Reaction n) = ∑ k : Fin n, 2 ^ (k.val + 1) * k.val := by
  simp_all

end RAF.Polymer
