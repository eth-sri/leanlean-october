module
public import Mathlib

public import PottsDiscontinuity.Potts.Parameters
public import PottsDiscontinuity.Duality.FiniteDuality
public import PottsDiscontinuity.FK.FrozenBridge

@[expose] public section

namespace PottsDiscontinuity.PottsThm



open PottsDiscontinuity.Potts

theorem pottsCriticalBeta_pos (q : ℕ) (hq : 4 < q) : 0 < pottsCriticalBeta q := by
  apply Real.log_pos
  have hqreal : (4 : ℝ) < q := by exact_mod_cast hq
  have hs  := Real.sqrt_pos.2 (by linarith)
  linarith

noncomputable def criticalFKParameters (q : ℕ) (hq : 4 < q) : FK.Parameters :=
  fkParameters q (by omega) (pottsCriticalBeta q) (pottsCriticalBeta_pos q hq)

theorem fkCritical_toP_toQ (q : ℕ) (hq : 4 < q) :
    (criticalFKParameters q hq).toP =
        (PottsDiscontinuity.FK.criticalParameters
          ⟨(q : ℝ), by
            simp_all <;> omega ⟩).toP ∧
    (criticalFKParameters q hq).toQ =
        (PottsDiscontinuity.FK.criticalParameters
          ⟨(q : ℝ), by
            simp_all <;> omega ⟩).toQ := by
  constructor
  · apply Subtype.ext
    
    exact bondProbability_pottsCriticalBeta q (by omega)
  · 
    rfl

end PottsDiscontinuity.PottsThm
