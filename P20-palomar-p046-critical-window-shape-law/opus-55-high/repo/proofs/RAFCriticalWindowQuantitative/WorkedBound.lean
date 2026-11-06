module

public import proofs.RAFCriticalWindowQuantitative.SmallOpenness
public import proofs.HordijkSteelThreshold.PolymerCounts

public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold unitInterval

theorem split_second_coefficient : splitSparseCoefficient 2 = 712483666919430 := by
  unfold splitSparseCoefficient sparseWitnessCap
  rw [card_reactions_exact $ by norm_num]
  norm_num [Nat.choose_two_right]

variable (a : I)

theorem split_quadratic_bound  :
    (staticSurvival a).toReal ≤ 712483666919430*(a : ℝ)^2 := by
  simpa only [split_second_coefficient,Nat.cast_ofNat] using sparse_real split_sparse_probability a 2

/-- A fully symbolic certificate, requiring no enumeration of channel fields. -/
theorem worked_low_openness_bound  (ha : (a : ℝ) ≤ 1/10^20) :
    (staticSurvival a).toReal < 8/10^26 := by
  have h := split_quadratic_bound a
  have hp := pow_le_pow_left₀ a.property.1 ha 2
  have hnum : (712483666919430 : ℝ)*(1/10^20)^2 < 8/10^26 := by norm_num
  grind

end RAFCriticalWindowQuantitative
