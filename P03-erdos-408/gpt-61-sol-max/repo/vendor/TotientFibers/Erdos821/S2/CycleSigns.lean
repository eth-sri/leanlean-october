module
public import Mathlib.Tactic

public import Erdos821.S2.CycleBlocks
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Equality rank and the signs of cycle decompositions. -/

@[expose] public section

section
open scoped BigOperators

namespace Erdos821.S2

/-- Rank plus the number of nonsingleton blocks is the number of addresses used. -/
theorem birthRank_add_card {a : ℕ} (π : Finset (Finset (Fin a)))
    (hπ : BirthCollection π) :
    birthRank π + π.card = (π.biUnion id).card := by
  classical
  have he : (∑ B ∈ π, B.card) = birthRank π + π.card := by
    calc
      (∑ B ∈ π, B.card) = ∑ B ∈ π, (B.card - 1 + 1) := by
        apply Finset.sum_congr rfl
        intro B hB
        have := hπ.1 B hB
        omega
      _ = birthRank π + π.card := by
        simp [birthRank, Finset.sum_add_distrib]
  exact he.symm.trans (Finset.card_biUnion hπ.2).symm

section
variable {a : ℕ} (σ : Equiv.Perm (Fin a))

theorem cycleFactors_support_injective     :
    Set.InjOn (fun c : Equiv.Perm (Fin a) => c.support)
      (σ.cycleFactorsFinset : Set (Equiv.Perm (Fin a))) := by
  classical
  intro c hc d hd hsd
  by_contra hcd
  have hdis := (σ.cycleFactorsFinset_pairwise_disjoint hc hd hcd).disjoint_support
  simp_all

theorem cycleBirthBlocks_card     :
    (cycleBirthBlocks σ).card = σ.cycleFactorsFinset.card := Finset.card_image_of_injOn (Erdos821.S2.cycleFactors_support_injective σ)

theorem cycleBirthBlocks_rank_add_card     :
    birthRank (cycleBirthBlocks σ) + σ.cycleFactorsFinset.card = σ.support.card := by
  simpa only [cycleBirthBlocks_card, cycleBirthBlocks_union] using
    birthRank_add_card (cycleBirthBlocks σ) (cycleBirthBlocks_collection σ)

/-- The sign of a permutation is (-1) to its equality rank. -/
theorem cycleBirthBlocks_sign     :
    (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ birthRank (cycleBirthBlocks σ) := by
  classical
  have hs : (Equiv.Perm.sign σ : ℤ) =
      (-1 : ℤ) ^ (σ.support.card + σ.cycleFactorsFinset.card) := by
    have hp := congrArg (fun u : ℤˣ => (u : ℤ)) (Equiv.Perm.sign_of_cycleType σ)
    rw [Equiv.Perm.sum_cycleType] at hp
    simpa [Equiv.Perm.cycleType] using hp
  have he : σ.support.card + σ.cycleFactorsFinset.card =
      birthRank (cycleBirthBlocks σ) + 2 * σ.cycleFactorsFinset.card := by
    have := cycleBirthBlocks_rank_add_card σ
    omega
  rw [hs, he, pow_add, pow_mul]
  simp

end


end Erdos821.S2
