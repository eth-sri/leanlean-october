module

public import proofs.RAF.Polymer.Reactions

public section

namespace HordijkSteelThreshold

open RAF.Polymer

variable (n : Nat)

private theorem sum_binary_words  :
    (∑ k ∈ Finset.range n, 2 ^ (k + 1)) = 2 ^ (n + 1) - 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- Exact number of nonempty binary words of length at most `n`. -/
theorem card_molecules_exact  :
    Fintype.card (Molecule n) = 2 ^ (n + 1) - 2 := by
  rw [card_molecule_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun k : Nat => 2 ^ (k + 1))]
  exact sum_binary_words n


private theorem sum_binary_reactions_shift (m : Nat) :
    (∑ k ∈ Finset.range $ m + 2, 2 ^ (k + 1) * k) =
      m * 2 ^ (m + 3) + 4 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [ Finset.sum_range_succ]
    grind

/-- Exact split-position reversible reaction count. -/
theorem card_reactions_exact {n : Nat} (hn : 2 ≤ n) :
    Fintype.card (Reaction n) = (n - 2) * 2 ^ (n + 1) + 4 := by
  rw [card_reaction_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun k : Nat => 2 ^ (k + 1) * k)]
  have h := sum_binary_reactions_shift $ n - 2
  simp_all

end HordijkSteelThreshold
