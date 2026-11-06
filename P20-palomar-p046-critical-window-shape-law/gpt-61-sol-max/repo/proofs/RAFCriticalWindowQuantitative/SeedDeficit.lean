import proofs.HordijkSteelThreshold.WordEffectiveClosure

import proofs.RAFCriticalWindowQuantitative.EffectiveSeed



namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold unitInterval

variable (a : I) (k : ℕ)



theorem contourBudget_real  :
    (contourBudget a k).toReal = molecularContourConstant * (1-a^2)^k := by
  have ha : (toNNReal a : ENNReal)^2 ≤ 1 := pow_le_one₀ (by positivity) (by exact_mod_cast a.property.2)
  simp_all [contourBudget]


end RAFCriticalWindowQuantitative
