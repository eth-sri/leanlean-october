module

public import HypoellipticAleksandrov.Coefficients.Ellipticity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Everywhere ellipticity of continuous time--velocity coefficients -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.Elementwise

section
variable {d : ℕ} {lam : ℝ} {Lam : ℝ} {A : CoefficientField d} (hA : IsContinuousCoefficient A)
include hA

/-- A continuous coefficient's almost-everywhere lower bound holds everywhere. -/
theorem lowerEllipticity_of_continuous_ae
    (hlo : HasLowerEllipticityAE lam A) : HasLowerEllipticity lam A := by
  have hd := volume.dense_of_ae hlo
  intro t v
  exact (isClosed_le continuous_const hA).closure_subset (hd (t, v))

/-- A continuous coefficient's almost-everywhere upper bound holds everywhere. -/
theorem upperEllipticity_of_continuous_ae
    (hhi : HasUpperEllipticityAE Lam A) : HasUpperEllipticity Lam A := by
  have hd := volume.dense_of_ae hhi
  intro t v
  exact (isClosed_le hA continuous_const).closure_subset (hd (t, v))

end

/-- Smoothness supplies the continuity needed to recover both pointwise bounds. -/
theorem ellipticity_of_smooth_ae {d : ℕ} {lam Lam : ℝ}
    {A : CoefficientField d} (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A) :
    HasLowerEllipticity lam A ∧ HasUpperEllipticity Lam A :=
  ⟨lowerEllipticity_of_continuous_ae hA.continuous hlo,
    upperEllipticity_of_continuous_ae hA.continuous hhi⟩

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
