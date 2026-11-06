module

public import HypoellipticAleksandrov.Coefficients.Ellipticity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Everywhere ellipticity of continuous time--velocity coefficients -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.Elementwise

variable {d : ℕ}

/-- A continuous coefficient's almost-everywhere lower bound holds everywhere. -/
theorem lowerEllipticity_of_continuous_ae  {lam : ℝ}
    {A : CoefficientField d} (hA : IsContinuousCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) : HasLowerEllipticity lam A := (fun t v => IsClosed.closure_subset (isClosed_le continuous_const hA) (Measure.dense_of_ae hlo (t, v)))

/-- A continuous coefficient's almost-everywhere upper bound holds everywhere. -/
theorem upperEllipticity_of_continuous_ae  {Lam : ℝ}
    {A : CoefficientField d} (hA : IsContinuousCoefficient A)
    (hhi : HasUpperEllipticityAE Lam A) : HasUpperEllipticity Lam A := (fun t v => IsClosed.closure_subset (isClosed_le hA continuous_const) (Measure.dense_of_ae hhi (t, v)))

/-- Smoothness supplies the continuity needed to recover both pointwise bounds. -/
theorem ellipticity_of_smooth_ae  {lam Lam : ℝ}
    {A : CoefficientField d} (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A) :
    HasLowerEllipticity lam A ∧ HasUpperEllipticity Lam A :=
  ⟨lowerEllipticity_of_continuous_ae hA.continuous hlo,
    upperEllipticity_of_continuous_ae hA.continuous hhi⟩

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
