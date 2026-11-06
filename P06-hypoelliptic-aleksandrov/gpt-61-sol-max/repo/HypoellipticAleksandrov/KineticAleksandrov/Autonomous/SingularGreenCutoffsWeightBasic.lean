module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsMollifier
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationGeometry
import Mathlib.MeasureTheory.Integral.Prod

/-! # The literal regularized singular weight, with all measurability discharged -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- A measurable position convolution is a measurable physical-plane function. -/
theorem positionConvolution_measurable (eta : ℝ → ℝ) (heta : Measurable eta)
    (Phi : Z → ℝ) (hPhi : Measurable Phi) : Measurable (positionConvolution eta Phi) := by
  have hm  :=
    (heta.comp ((measurable_fst.comp measurable_fst).sub measurable_snd)).mul
      (hPhi.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

variable (alpha : ℝ) (n : ℕ)

/-- The actual source singular-weight regularization at the n-th position scale. -/
def regularizedBarrierWeight  : Z → ℝ :=
  positionConvolution (barrierMollifier n) (fun q => bellmanGauge q ^ (alpha - 2))

/-- The regularized weight is measurable in the physical plane. -/
theorem regularizedBarrierWeight_measurable  :
    Measurable (regularizedBarrierWeight alpha n) :=
  positionConvolution_measurable _ (barrierMollifier_spec n).1.continuous.measurable _
    (bellmanGauge_continuous.measurable.pow_const _)

/-- On the zero-velocity axis, the weight has precisely the integrable position power. -/
theorem barrier_weight_position_axis (beta X : ℝ) :
    bellmanGauge (X, 0) ^ beta = |X| ^ (beta / 3) := by

  simp only [bellmanGauge, bellmanGaugePower, zero_pow (by decide : 6 ≠ 0),
    add_zero, ((sq_abs X).symm)]
  rw [← Real.rpow_natCast_mul (abs_nonneg X), ← Real.rpow_mul (abs_nonneg X)]
  congr 1
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
