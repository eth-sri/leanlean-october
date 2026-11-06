module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import Aesop
public import PDEFoundation.Calculus.RegularityOrder




/-! # Signed-source comparison on bounded parabolic cylinders

The affine time barrier bounds supplied zero-boundary backward corrections. The
replacement construction reflects this estimate to the forward initial/lateral problem.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

variable {n : ℕ}

variable (M T : ℝ)

/-- The backward source barrier, independent of velocity. -/
def sourceTimeBarrier   (z : TimeVelocity n) : ℝ := M * (T - z.1)

/-- The source time barrier is smooth. -/
theorem contDiff_sourceTimeBarrier   :
    ContDiff ℝ PDE.smoothOrder (@sourceTimeBarrier n M T) :=
  contDiff_const.mul (contDiff_const.sub contDiff_fst)

variable (z : TimeVelocity n)

/-- The barrier's scalar time derivative is minus its amplitude. -/
theorem scalarTimeDerivative_sourceTimeBarrier    :
    scalarTimeDerivative (sourceTimeBarrier M T) z = -M := by
  change deriv (fun r  => M * (T - r)) z.1 = -M
  simp_all

/-- Velocity differentiation annihilates the time barrier. -/
theorem scalarSpatialGradient_sourceTimeBarrier    :
    scalarSpatialGradient (sourceTimeBarrier M T) z = 0 := by
  simp_all [scalarSpatialGradient, sourceTimeBarrier, PDE.classicalGradient] <;> aesop

/-- The time barrier has zero spatial Hessian. -/
theorem scalarSpatialHessian_sourceTimeBarrier    :
    scalarSpatialHessian (sourceTimeBarrier M T) z = 0 := by
  let sharedTerm_15744baf01 := ((fun y : PDE.Vec n => PDE.classicalGradient (fun w => sourceTimeBarrier M T (z.1, w)) y))
  have heq : (sharedTerm_15744baf01) =
      fun _ => (0 : PDE.Vec n) := by
    funext y
    exact scalarSpatialGradient_sourceTimeBarrier M T (z.1, y)
  ext i j
  change (fderiv ℝ sharedTerm_15744baf01 z.2
      (PDE.basisVec i)) j = 0
  rw [heq, fderiv_const_apply]
  rfl

variable (A : CoefficientField n)

/-- The scalar backward operator of the barrier is the constant source minus M. -/
theorem scalarOperator_sourceTimeBarrier
    (M T : ℝ) (z : TimeVelocity n) :
    scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
      (sourceTimeBarrier M T) z = -M := by
  simp_all [scalarTimeDerivative_sourceTimeBarrier, scalarSpatialGradient_sourceTimeBarrier, scalarSpatialHessian_sourceTimeBarrier, matrixContraction, PDE.vecDot]

/-- The barrier has its literal terminal and lateral boundary data. -/
theorem sourceTimeBarrier_isClassicalBackward
    (a T M : ℝ) (Ω : PDE.VelocityRegion n) :
    IsClassicalBackwardDirichletSolution a T Ω A (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => -M) (fun _ => 0) (sourceTimeBarrier M T) (sourceTimeBarrier M T) := by
  refine ⟨(contDiff_sourceTimeBarrier M T).continuous.continuousOn,
    isScalarC12On_of_contDiff_two
      ((contDiff_sourceTimeBarrier M T).of_le (by simp)) _, ?_, ?_, ?_⟩
  · intro z hz
    exact scalarOperator_sourceTimeBarrier A M T z
  · intro y hy
    simp only [sourceTimeBarrier, sub_self, mul_zero]
  · intro z hz
    rfl

/-- A signed bounded source gives the sharp finite-horizon bound for zero-boundary solutions. -/
theorem abs_zeroBoundary_solution_le_time  {Ω : PDE.VelocityRegion n} {a T : ℝ}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (haT : a < T)
    (A : CoefficientField n) (hAc : IsContinuousCoefficient A)
    (hApsd : ∀ t v, (A t v).PosSemidef)
    (F : PDE.TimeScalarField n) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |F z.1 z.2| ≤ M)
    (u : HypoellipticAleksandrov.Parabolic.ScalarField n)
    (hu : IsClassicalBackwardDirichletSolution a T Ω A
      (fun _ _ => 0) (fun _ _ => 0) F (fun _ => 0) (fun _ => 0) u) :
    ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |u z| ≤ M * (T - z.1) := by
  have hupper := le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
    hΩo hΩb haT A (fun _ _ => 0) (fun _ _ => 0) hAc continuous_const hApsd
    (fun _ _ => le_rfl) F (fun _ _ => -M) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (sourceTimeBarrier M T) u (sourceTimeBarrier M T)
    hu (sourceTimeBarrier_isClassicalBackward A a T M Ω)
    (fun z hz => (abs_le.mp (hF z hz)).1) (fun _ _ => le_rfl)
    (fun z hz => mul_nonneg hM (sub_nonneg.mpr hz.1.2))
  have hlower := le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
    hΩo hΩb haT A (fun _ _ => 0) (fun _ _ => 0) hAc continuous_const hApsd
    (fun _ _ => le_rfl) (fun _ _ => -(-M)) F (fun _ => 0) (fun _ => 0)
    (sourceTimeBarrier (-M) T) (fun _ => 0) (sourceTimeBarrier (-M) T) u
    (sourceTimeBarrier_isClassicalBackward A a T (-M) Ω) hu
    (fun z hz => by simpa only [neg_neg] using (abs_le.mp (hF z hz)).2) (fun _ _ => le_rfl)
    (fun z hz => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hM)
      (sub_nonneg.mpr hz.1.2))
  intro z hz
  apply abs_le.mpr
  constructor
  · simpa only [sourceTimeBarrier, neg_mul] using hlower z hz
  · exact hupper z hz

end HypoellipticAleksandrov.Parabolic.LocalHolder
