module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCutoff
public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives
import Mathlib.Tactic.Ring

/-! # Integrability of local spatial value-energy terms

Interior compact cutoffs control every principal and coefficient-derivative term in the
spatial integration by parts, even when solution derivatives are unbounded at the boundary.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Matrix.Norms.Elementwise

/-- Both sides of the local spatial value-energy identity are globally integrable. -/
theorem integrable_scalar_local_spatial_value_energy_terms {d : ℕ}
    {U : Set (TimeVelocity d)} (hU : IsOpen U) (u ρ : TimeVelocity d → ℝ)
    (hu : IsScalarC12On u U) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hc : HasCompactSupport ρ) (hsub : tsupport ρ ⊆ U)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A) (i j : Fin d) :
    Integrable (fun z => A z.1 z.2 i j * scalarSpatialGradient u z j *
      (ρ z ^ 2 * scalarSpatialGradient u z i +
        2 * ρ z * scalarSpatialGradient ρ z i * u z)) ∧
    Integrable (fun z =>
      (spatialPartial i (fun y => A z.1 y i j) z.2 * scalarSpatialGradient u z j +
        A z.1 z.2 i j * scalarSpatialHessian u z i j) * (u z * ρ z ^ 2)) := by
  have hcoeff : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => A z.1 z.2 i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hA
  have hcoeffc := hcoeff.continuous
  have hρ12 := isScalarC12On_of_contDiff_two (hρ.of_le (by simp)) univ
  have hA12 := isScalarC12On_of_contDiff_two (hcoeff.of_le (by simp)) univ
  have hρgrad : Continuous (fun z => scalarSpatialGradient ρ z i) :=
    (continuous_apply i).comp (continuousOn_univ.mp hρ12.continuousOn_scalarSpatialGradient)
  have hdA : Continuous (fun z : TimeVelocity d =>
      spatialPartial i (fun y => A z.1 y i j) z.2) :=
    (continuous_apply i).comp (continuousOn_univ.mp hA12.continuousOn_scalarSpatialGradient)
  have hgrad (k : Fin d) : ContinuousOn (fun z => scalarSpatialGradient u z k) U :=
    (continuous_apply k).comp_continuousOn hu.continuousOn_scalarSpatialGradient
  have hhess : ContinuousOn (fun z => scalarSpatialHessian u z i j) U :=
    (continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialHessian)
  obtain ⟨hpowc, hpows⟩ := cutoff_square_support hc
  have hp := integrable_local_cutoff_mul hU
    (fun z => A z.1 z.2 i j * scalarSpatialGradient u z j * scalarSpatialGradient u z i)
    (fun z => ρ z ^ 2) ((hcoeffc.continuousOn.mul (hgrad j)).mul (hgrad i))
    (hρ.continuous.pow 2) hpowc (hpows.trans hsub)
  have he := integrable_local_cutoff_mul hU
    (fun z => 2 * A z.1 z.2 i j * scalarSpatialGradient u z j * u z)
    (fun z => ρ z * scalarSpatialGradient ρ z i)
    (((continuousOn_const.mul hcoeffc.continuousOn).mul (hgrad j)).mul hu.continuousOn)
    (hρ.continuous.mul hρgrad) (HasCompactSupport.mul_right hc)
    (tsupport_mul_subset_left.trans hsub)
  have hr := integrable_local_cutoff_mul hU
    (fun z => (spatialPartial i (fun y => A z.1 y i j) z.2 * scalarSpatialGradient u z j +
      A z.1 z.2 i j * scalarSpatialHessian u z i j) * u z)
    (fun z => ρ z ^ 2)
    (((hdA.continuousOn.mul (hgrad j)).add (hcoeffc.continuousOn.mul hhess)).mul
      hu.continuousOn) (hρ.continuous.pow 2) hpowc (hpows.trans hsub)
  constructor
  · exact (hp.add he).congr (Eventually.of_forall (fun z => by
      simp only [Pi.add_apply]
      ring))
  · exact hr.congr (Eventually.of_forall (fun z => by dsimp only; ring))

end HypoellipticAleksandrov.Parabolic.LocalHolder
