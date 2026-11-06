module

public import PottsDiscontinuity.Potts.Parameters
public import PottsDiscontinuity.Duality.FiniteDuality
public import PottsDiscontinuity.FK.FrozenBridge

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts

section
variable (q : ℕ) (hq : 4 < q)
include hq
theorem pottsCriticalBeta_pos  : 0 < pottsCriticalBeta q := by
  apply Real.log_pos
  have hs : 0 < Real.sqrt (q : ℝ) := by positivity
  linarith

noncomputable def criticalFKParameters  : FK.Parameters :=
  fkParameters q (by omega) (pottsCriticalBeta q) (pottsCriticalBeta_pos q hq)

theorem fkCritical_toP_toQ  :
    (criticalFKParameters q hq).toP =
        (PottsDiscontinuity.FK.criticalParameters
          ⟨(q : ℝ), by
            change (1 : ℝ) ≤ (q : ℝ)
            exact_mod_cast (show 1 ≤ q by omega)⟩).toP ∧
    (criticalFKParameters q hq).toQ =
        (PottsDiscontinuity.FK.criticalParameters
          ⟨(q : ℝ), by
            change (1 : ℝ) ≤ (q : ℝ)
            exact_mod_cast (show 1 ≤ q by omega)⟩).toQ := by
  constructor
  · apply Subtype.ext
    exact bondProbability_pottsCriticalBeta q (by omega)
  rfl
end

end PottsDiscontinuity.PottsThm
