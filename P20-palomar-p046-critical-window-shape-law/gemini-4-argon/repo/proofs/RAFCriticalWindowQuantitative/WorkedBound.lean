module

public import proofs.RAFCriticalWindowQuantitative.SmallOpenness
public import proofs.HordijkSteelThreshold.PolymerCounts

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold unitInterval

theorem worked_low_openness_bound (a : I) (ha : (a : ℝ) ≤ 1/10^20) :
    (staticSurvival a).toReal < 8/10^26 := by
  have hc : splitSparseCoefficient 2 = 712483666919430 := by
    unfold splitSparseCoefficient sparseWitnessCap
    rw [card_reactions_exact (by norm_num)]
    norm_num [Nat.choose_two_right]
  have h : (staticSurvival a).toReal ≤ 712483666919430 * (a : ℝ) ^ 2 := by
    simpa only [hc, Nat.cast_ofNat] using split_sparse_real a 2
  exact h.trans_lt ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ a.property.1 ha 2) (by norm_num)).trans_lt (by norm_num))

end RAFCriticalWindowQuantitative
