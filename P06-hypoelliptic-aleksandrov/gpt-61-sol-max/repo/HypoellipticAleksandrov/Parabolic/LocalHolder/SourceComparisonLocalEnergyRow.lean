module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCutoff
public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
public import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives
public import HypoellipticAleksandrov.Coefficients.Ellipticity
import Mathlib.Analysis.Normed.Group.Bounded
public import PDEFoundation.Calculus.RegularityOrder


/-! # The compact coefficient and cutoff error row

The actual error row depends on the coefficient and cutoff, and has a finite uniform bound
independent of the classical solution whose energy is being tested.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set
open scoped BigOperators Matrix.Norms.Elementwise

variable {d : ℕ} (A : CoefficientField d)

/-- The literal row collecting both spatial cutoff and coefficient derivative terms. -/
def localValueEnergyErrorRow
    (ρ : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) (j : Fin d) : ℝ :=
  ∑ i, (2 * A z.1 z.2 i j * scalarSpatialGradient ρ z i +
    ρ z * spatialPartial i (fun y => A z.1 y i j) z.2)

/-- Smooth coefficients and cutoff make the error row continuous. -/
theorem continuous_localValueEnergyErrorRow
    (hA : IsSmoothCoefficient A) (ρ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hρ : ContDiff ℝ PDE.smoothOrder ρ) : Continuous (localValueEnergyErrorRow A ρ) := by
  apply continuous_pi
  intro j
  apply continuous_finsetSum
  intro i _
  have hcoeff : ContDiff ℝ PDE.smoothOrder (fun z : TimeVelocity d => A z.1 z.2 i j) :=
    (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)


  have hρgrad := (continuous_apply i).comp
    (continuousOn_univ.mp (isScalarC12On_of_contDiff_two (hρ.of_le (by simp)) univ).continuousOn_scalarSpatialGradient)
  have hAgrad := (continuous_apply i).comp
    (continuousOn_univ.mp (isScalarC12On_of_contDiff_two (hcoeff.of_le (by simp)) univ).continuousOn_scalarSpatialGradient)
  exact ((continuous_const.mul hcoeff.continuous).mul hρgrad).add
    (hρ.continuous.mul hAgrad)

/-- The error row vanishes outside the cutoff support, hence is compactly supported. -/
theorem hasCompactSupport_localValueEnergyErrorRow
    (ρ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hc : HasCompactSupport ρ) :
    HasCompactSupport (localValueEnergyErrorRow A ρ) := by
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro z hz
  by_contra hnot
  apply hz
  ext j

  simp only [localValueEnergyErrorRow, scalarSpatialGradient_eq_zero_of_notMem_tsupport
    ρ z _ hnot, (image_eq_zero_of_notMem_tsupport hnot), mul_zero, zero_mul, add_zero, Finset.sum_const_zero, Pi.zero_apply]

/-- There is one finite error-row bound for all points and coordinate indices. -/
theorem exists_localValueEnergyErrorRow_bound
    (hA : IsSmoothCoefficient A) (ρ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hρ : ContDiff ℝ PDE.smoothOrder ρ) (hc : HasCompactSupport ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z j, |localValueEnergyErrorRow A ρ z j| ≤ K := by

  obtain ⟨C, hC⟩ := (continuous_localValueEnergyErrorRow A hA ρ hρ).bounded_above_of_compact_support
    (hasCompactSupport_localValueEnergyErrorRow A ρ hc)
  refine ⟨max C 0, le_max_right _ _, fun z j => ?_⟩
  calc
    _ = ‖localValueEnergyErrorRow A ρ z j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖localValueEnergyErrorRow A ρ z‖ := norm_le_pi_norm _ j
    _ ≤ C := hC z
    _ ≤ max C 0 := le_max_left _ _

end HypoellipticAleksandrov.Parabolic.LocalHolder
