module
public import Mathlib.Tactic

public import Erdos821.S2.BirthExpansion
public import Erdos821.S2.RankEncoding

/-! The total absolute Möbius coefficient at equality rank r. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2

lemma birthMobius_natAbs_eq_card {a : ℕ} (π : Finset (Finset (Fin a)))
    (hπ : BirthCollection π) : (birthMobius π).natAbs = (permutationsWithBlocks π).card := by
  rw [birthMobius_eq_sign_mul_factorials, ← Nat.cast_prod]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
    one_pow, one_mul, Int.natAbs_natCast]
  exact (permutationsWithBlocks_card π hπ).symm

/-- Absolute rank-r coefficients count rank-r permutations. -/
theorem rank_coefficient_eq_card  a r  :
    (∑ π ∈ Finset.univ.powerset.powerset.filter
      (fun π : Finset (Finset (Fin a)) => BirthCollection π ∧ birthRank π = r),
        (birthMobius π).natAbs) = (rankPermutations a r).card := by
  let C : Finset (Finset (Finset (Fin a))) := Finset.univ.powerset.powerset.filter
    (fun π => BirthCollection π ∧ birthRank π = r)
  have hmap : (rankPermutations a r : Set (Equiv.Perm (Fin a))).MapsTo cycleBirthBlocks C := by
    intro σ hσ
    have hr := (Finset.mem_filter.mp hσ).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, cycleBirthBlocks_collection σ, hr⟩
    intro B _
    exact Finset.mem_powerset.mpr (Finset.subset_univ _)
  have hfiber (π : Finset (Finset (Fin a))) (hπ : π ∈ C) :
      (rankPermutations a r).filter (fun σ => cycleBirthBlocks σ = π) = permutationsWithBlocks π := by
    grind [birthRank, rankPermutations, permutationsWithBlocks]
  calc
    _ = ∑ π ∈ C, (permutationsWithBlocks π).card := by
      apply Finset.sum_congr rfl
      simp_all [birthMobius_natAbs_eq_card]
    _ = ∑ π ∈ C, ((rankPermutations a r).filter (fun σ => cycleBirthBlocks σ = π)).card :=
      Finset.sum_congr rfl (fun π hπ => congrArg Finset.card (hfiber π hπ).symm)
    _ = _ := (Finset.card_eq_sum_card_fiberwise hmap).symm

/-- eq:rank-coefficient-count, including rank zero and empty address sets. -/
theorem rank_coefficient_count  a r  :
    (∑ π ∈ Finset.univ.powerset.powerset.filter
      (fun π : Finset (Finset (Fin a)) => BirthCollection π ∧ birthRank π = r),
        (birthMobius π).natAbs) ≤ a ^ (2 * r) := by
  rw [rank_coefficient_eq_card]
  exact rankPermutations_card_le a r


end Erdos821.S2
