
import proofs.RAF.Polymer.Reactions



namespace HordijkSteelThreshold

open RAF.Polymer

variable (n : Nat)

/-- Exact number of nonempty binary words of length at most `n`. -/
theorem card_molecules_exact  :
    Fintype.card (Molecule n) = 2 ^ (n + 1) - 2 := by
  simp
  rw [Fin.sum_univ_eq_sum_range fun k : Nat => 2 ^ (k + 1)]
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- Exact split-position reversible reaction count. -/
theorem card_reactions_exact {n : Nat} (hn : 2 ≤ n) :
    Fintype.card (Reaction n) = (n - 2) * 2 ^ (n + 1) + 4 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  simp
  rw [Fin.sum_univ_eq_sum_range fun k : ℕ => 2 ^ (k+1)*k]
  clear hn
  induction m with
  | zero => norm_num
  | succ m ih => rw [← Nat.add_assoc, Finset.sum_range_succ]; grind

end HordijkSteelThreshold
