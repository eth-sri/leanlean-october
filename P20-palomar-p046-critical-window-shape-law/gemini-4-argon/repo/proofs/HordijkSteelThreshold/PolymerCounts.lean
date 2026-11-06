module

public import proofs.RAF.Polymer.Counts

@[expose] public section

namespace HordijkSteelThreshold

open RAF.Polymer

theorem card_molecules_exact (n : Nat) :
    Fintype.card (Molecule n) = 2 ^ (n + 1) - 2 := by
  simp only [Molecule, Word, Fintype.card_sigma, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun k : Nat => 2 ^ (k + 1))]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ, pow_succ]
    have : 0 < 2 ^ n := by positivity
    omega

theorem card_reactions_exact {n : Nat} (hn : 2 ≤ n) :
    Fintype.card (Reaction n) = (n - 2) * 2 ^ (n + 1) + 4 := by
  simp only [Reaction, Word, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun k : Nat => 2 ^ (k + 1) * k)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn; simp only [Nat.add_sub_cancel]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show m + 1 + 2 = m + 2 + 1 from rfl, Finset.sum_range_succ, ih,
      show m + 1 + 2 + 1 = m + 2 + 1 + 1 by omega, pow_succ (2 : ℕ) (m + 2 + 1)]
    ring

end HordijkSteelThreshold
