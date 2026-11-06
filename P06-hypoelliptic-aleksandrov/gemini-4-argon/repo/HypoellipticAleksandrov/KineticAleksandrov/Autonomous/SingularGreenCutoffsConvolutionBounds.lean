module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionJets
import Mathlib.Analysis.Normed.Operator.Prod

/-! # Transparent norm bounds for the position-convolution parameter jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/- A scalar combination of the two coordinate projections has its elementary norm bound. -/
theorem barrier_projection_norm_le (a b : ℝ) :
    ‖a • barrierPositionProjection + b • barrierVelocityProjection‖ ≤ |a| + |b| := by
  exact (norm_add_le _ _).trans_eq (by
    simp only [norm_smul, Real.norm_eq_abs, barrierPositionProjection,
      barrierVelocityProjection, ContinuousLinearMap.norm_fst, ContinuousLinearMap.norm_snd,
      mul_one])

/- The first convolution jet only needs the value and first velocity fiber majorants. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
