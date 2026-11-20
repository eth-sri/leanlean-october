module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCoefficientIntegral

/-! # Integrability of the position-localized Green test -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (Y : ℝ) (hc : |c.vbar| = 2 * c.r) (mu : Measure Point)

/-- Closed active support bounds the localized test by the exact quadratic maximum. -/
theorem positionStartQuadratic_integrable [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.active) :
    Integrable (fun p => positionStartCutoff Y c.r c.positive (p.position 0) *
      visitQuadratic c (p.velocity 0)) mu := by
  have hx := (continuous_apply (0 : Fin 1)).comp continuous_position
  have hv := (continuous_apply (0 : Fin 1)).comp continuous_velocity
  apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
    (((positionStartCutoff_properties Y c.r c.positive).1.continuous.comp hx).mul ((visitQuadratic_smooth c).continuous.comp hv)).measurable.aestronglyMeasurable
  filter_upwards [hmu] with p hp
  change ‖positionStartCutoff Y c.r c.positive (p.position 0) *
    visitQuadratic c (p.velocity 0)‖ ≤ 9 * c.r ^ 2 / 16
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg ((positionStartCutoff_properties Y c.r c.positive).2 _).1,
    abs_of_nonneg (visitQuadratic_nonneg c hp)]
  exact (mul_le_mul_of_nonneg_right
    ((positionStartCutoff_properties Y c.r c.positive).2 _).2
    (visitQuadratic_nonneg c hp)).trans (by
      simpa using visitQuadratic_le c (p.velocity 0))

/-- The exact spatially localized operator is continuous. -/
theorem positionStartQuadratic_operator_continuous :
    Continuous (fun p : Point => forwardScalarOperator A.a
      (fun q => positionStartCutoff Y c.r c.positive (q.position 0) *
        visitQuadratic c (q.velocity 0)) p) := by
  have he := (positionStartCutoff_properties Y c.r c.positive).1
  have hx := (continuous_apply (0 : Fin 1)).comp continuous_position
  have hv := (continuous_apply (0 : Fin 1)).comp continuous_velocity
  have hh := funext (positionStartQuadratic_operator c (positionStartCutoff Y c.r c.positive) he A.a)
  rw [hh]
  exact ((hv.mul ((he.continuous_deriv (by norm_num)).comp hx)).mul
    ((visitQuadratic_smooth c).continuous.comp hv)).sub
      ((continuous_const.mul (visitCoefficient_continuous A)).mul (he.continuous.comp hx))

include hlam hLam hc in
/-- Finite active occupation makes the exact position-localized operator integrable. -/
theorem positionStartQuadratic_operator_integrable [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ c.active) :
    Integrable (fun p => forwardScalarOperator A.a
      (fun q => positionStartCutoff Y c.r c.positive (q.position 0) *
        visitQuadratic c (q.velocity 0)) p) mu := by
  obtain ⟨C, hC, hb⟩ := positionStartQuadratic_operator_bound hlam hLam
  apply Integrable.mono' (integrable_const C)
    (positionStartQuadratic_operator_continuous A c Y).measurable.aestronglyMeasurable
  filter_upwards [hmu] with p hp
  rw [Real.norm_eq_abs]
  apply (hb A c Y p hc hp).trans
  by_cases hbox : (p.position 0, p.velocity 0) ∈ box 4 c.r Y
  · rw [indicator_of_mem hbox, mul_one]
  · rw [indicator_of_notMem hbox, mul_zero]
    exact hC.le

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
