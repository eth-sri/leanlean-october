module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitSumHorizon

/-! # Source position visit counts and q-power sum

The time-bin and position-cell bounds control the power sum over a finite horizon.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Bounds on the time-bin counts, position counts and their power sum. -/
theorem positionVisitsStatement_holds :
    PositionVisitsStatement := by
  intro lam Lam hlam hLam alpha ha
  obtain ⟨Cp, hCp, hcell⟩ := position_cell_count hlam hLam alpha ha
  obtain ⟨Ct, hCt, htime⟩ := timeBinCount_holds hlam hLam
  have hg := enlargedAdmissibleAlpha_gamma_range hlam hLam alpha ha
  constructor
  · refine ⟨Ct + Cp, add_pos hCt hCp, ?_⟩
    intro A c J T P hbar hJ hT hvel j
    constructor
    · apply (htime A c J T P hbar hJ hT hvel j).trans
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCp.le)
        (Real.rpow_nonneg (by positivity) _)
    · intro k
      apply (hcell A c J T P hbar hJ hT hvel j k).trans
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCt.le)
        (Real.rpow_nonneg (by positivity) _)
  · intro q hq
    let g := 2 - alpha
    let F := (1 + 1 / (1 - (1 + g * (q - 1)) / 2)) *
      (3 : ℝ) ^ (1 - (1 + g * (q - 1)) / 2)
    have hprod : g * (q - 1) < 1 := by
      have hh := mul_lt_mul_of_pos_right hg.2 (by linarith [hq.1] : 0 < q - 1)
      change (2 - alpha) * (q - 1) < 1
      linarith [hq.2]
    have hb : 0 < 1 - (1 + g * (q - 1)) / 2 := by linarith
    have hF : 0 < F := by dsimp only [F]; positivity
    refine ⟨Cp ^ (q - 1) * Ct * F, by positivity, ?_⟩
    intro A c J R T P hR hT hTR hbar hJ hvel
    have : IsFiniteMeasure (visitsFromZero A c J T P) :=
      visitsFromZero_isFiniteMeasure A c J T P hbar hJ hT hvel
    apply enlargedPositionVisitMass_power_sum_horizon_le
      (visitsFromZero A c J T P) c P.time 0 R T hR hT hTR
    · exact (enlargedVisitStarts_ae_support A c J P.time (P.time + T)
        P le_rfl (by linarith)).mono fun _ hp => hp.2.1
    · exact hCt.le
    · exact hCp.le
    · exact hg
    · exact hq
    · exact htime A c J T P hbar hJ hT hvel
    · exact hcell A c J T P hbar hJ hT hvel

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
