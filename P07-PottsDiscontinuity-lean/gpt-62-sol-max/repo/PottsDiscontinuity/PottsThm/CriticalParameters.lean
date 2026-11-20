module

public import PottsDiscontinuity.Potts.Parameters
public import PottsDiscontinuity.Duality.FiniteDuality
public import PottsDiscontinuity.FK.FrozenBridge

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts

theorem pottsCriticalBeta_pos (q : ℕ) (hq : 4 < q) : 0 < pottsCriticalBeta q := by
  apply Real.log_pos
  have hqreal : (4 : ℝ) < q := by exact_mod_cast hq
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 (by linarith)
  linarith

theorem fkParameters_pottsCriticalBeta (q : ℕ) (hq : 2 ≤ q) (hβ : 0 < pottsCriticalBeta q) :
    fkParameters q hq (pottsCriticalBeta q) hβ =
      FK.criticalParameters ⟨q, Set.mem_Ici.2 (by exact_mod_cast (show 1 ≤ q by omega))⟩ := by
  unfold fkParameters FK.criticalParameters
  congr 1
  exact Subtype.ext (bondProbability_pottsCriticalBeta q hq)

end PottsDiscontinuity.PottsThm
