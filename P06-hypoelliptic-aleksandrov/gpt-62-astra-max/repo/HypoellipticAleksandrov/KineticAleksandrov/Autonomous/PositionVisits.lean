module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitSumHorizon

/-! # Source position visit counts and q-power sum

The exact source start identity and time-bin count remain named conditional
inputs until their assigned results are present. No mass or domination
premise is used: canonical finiteness is proved by the enlarged recursion.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The position-visits statement, given the smooth autonomous estimates and a start time. -/
theorem positionVisitsStatement_holds_of_start_time
    (hp6 : ∀ (lam Lam : ℝ), 0 < lam → lam ≤ Lam → SmoothAutonomousP6Statement lam Lam)
    (hTime : ∀
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ Ct : ℝ, 0 < Ct ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ j : ℕ,
        enlargedTimeVisitMass (visitsFromZero hlam hLam A c J T P) c P.time j ≤
          Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ))
    (hStart : ∀
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ A0 Cs : ℝ, 0 < A0 ∧ 0 < Cs ∧
      ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ (a b : ℝ) (k : ℤ),
      0 ≤ a → a < b → b - a ≤ c.r ^ 2 → b ≤ T →
      enlargedPositionSlabMass (visitsFromZero hlam hLam A c J T P)
        c P.time 0 a b k ≤ Cs *
          ((kernelXV (fullSpaceEvolution hlam hLam A) (Real.toNNReal b)
            (P.position 0, P.velocity 0)
              (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal +
           c.r ^ (-2 : ℤ) * ∫ t in Ioc a b,
             (kernelXV (fullSpaceEvolution hlam hLam A) (Real.toNNReal t)
               (P.position 0, P.velocity 0)
                 (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal)) :
    PositionVisitsStatement := by
  intro lam Lam hlam hLam alpha ha
  have ht := hTime lam Lam hlam hLam
  have hstart := hStart lam Lam hlam hLam
  obtain ⟨Cp, hCp, hcell⟩ := position_cell_count_of_start_time
    hlam hLam alpha ha (hp6 lam Lam hlam hLam) ht hstart
  obtain ⟨Ct, hCt, htime⟩ := ht
  have hg := enlargedAdmissibleAlpha_gamma_range hlam hLam alpha ha
  constructor
  · refine ⟨Ct + Cp, add_pos hCt hCp, ?_⟩
    intro A c J T P hbar hJ hT hvel j
    constructor
    · apply (htime A c J T P hbar hJ hT hvel j).trans
      bound
    · intro k
      apply (hcell A c J T P hbar hJ hT hvel j k).trans
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCt.le)
        (Real.rpow_nonneg (by positivity) _)
  · intro q hq
    let g := 2 - alpha
    let F := (1 + 1 / (1 - (1 + g * (q - 1)) / 2)) *
      3 ^ (1 - (1 + g * (q - 1)) / 2)
    have hprod : g * (q - 1) < 1 := by
      nlinarith
    have hb : 0 < 1 - (1 + g * (q - 1)) / 2 := by linarith
    refine ⟨Cp ^ (q - 1) * Ct * F, by positivity, ?_⟩
    intro A c J R T P hR hT hTR hbar hJ hvel
    have  :=
      visitsFromZero_isFiniteMeasure hlam hLam A c J T P hbar hJ hT hvel
    apply enlargedPositionVisitMass_power_sum_horizon_le
      (visitsFromZero hlam hLam A c J T P) c P.time 0 R T hR hT hTR
    · exact (enlargedVisitStarts_ae_support hlam hLam A c J P.time (P.time + T)
        P le_rfl (by linarith)).mono fun _ hp => hp.2.1
    · exact hCt.le
    · exact hCp.le
    · exact hg
    · exact hq
    · apply htime <;> assumption
    · apply hcell <;> assumption

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
