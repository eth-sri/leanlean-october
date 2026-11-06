module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSmoothResidual
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import Mathlib.Tactic.Ring
public import PDEFoundation.Calculus.RegularityOrder


/-! # Smooth terminal lifting for the ellipsoidal Dirichlet construction -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.Parabolic.LocalHolder Set Filter
open scoped Topology Matrix

variable {n : ℕ}

section
variable {u v : HypoellipticAleksandrov.Parabolic.ScalarField n} {D : HypoellipticAleksandrov.Parabolic.Region n} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D) {z : TimeVelocity n} (hz : z ∈ D)

include hu hv hz
private theorem scalarTimeDerivative_add   :
    scalarTimeDerivative (fun q => u q + v q) z =
      scalarTimeDerivative u z + scalarTimeDerivative v z := ((hu.timeSlice_hasDerivAt hz).add (hv.timeSlice_hasDerivAt hz)).deriv

private theorem scalarSpatialGradient_add   :
    scalarSpatialGradient (fun q => u q + v q) z =
      scalarSpatialGradient u z + scalarSpatialGradient v z := by
  ext i
  change fderiv ℝ (fun y  => u (z.1, y) + v (z.1, y)) z.2
      (PDE.basisVec i) = _
  rw [fderiv_fun_add ((hu.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))
    ((hv.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))]
  rfl
end


private theorem scalarSpatialHessian_apply_eq_sndFDeriv
    {u : HypoellipticAleksandrov.Parabolic.ScalarField n} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y  => u (z.1, y)) z.2)
    (i j : Fin n) :
    scalarSpatialHessian u z i j =
      fderiv ℝ (fderiv ℝ (fun y  => u (z.1, y))) z.2
        (PDE.basisVec i) (PDE.basisVec j) := by
  let g  := fun y => u (z.1, y)
  have hsecond : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z.2) z.2 :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt

  change (fderiv ℝ (fun y  => fun j =>
      fderiv ℝ g y (PDE.basisVec j)) z.2 (PDE.basisVec i)) j = _
  rw [fderiv_pi (by
      intro j
      exact (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).differentiableAt)]


  simpa [ContinuousLinearMap.flip_apply] using (congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) ((hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).fderiv))

section
variable {u v : HypoellipticAleksandrov.Parabolic.ScalarField n} {D : HypoellipticAleksandrov.Parabolic.Region n} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)

include hu hv
private theorem scalarSpatialHessian_add
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarSpatialHessian (fun q => u q + v q) z =
      scalarSpatialHessian u z + scalarSpatialHessian v z := by
  let g_u  := fun y => u (z.1, y)
  let g_v  := fun y => v (z.1, y)

  have huSecond : HasFDerivAt ((fderiv ℝ g_u))
      (fderiv ℝ (fderiv ℝ g_u) z.2) z.2 :=
    ((hu.spatialSlice_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hvSecond : HasFDerivAt ((fderiv ℝ g_v))
      (fderiv ℝ (fderiv ℝ g_v) z.2) z.2 :=
    ((hv.spatialSlice_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hsecond : fderiv ℝ (fderiv ℝ (fun y => g_u y + g_v y)) z.2 =
      fderiv ℝ (fderiv ℝ g_u) z.2 + fderiv ℝ (fderiv ℝ g_v) z.2 := by
    calc
      fderiv ℝ (fderiv ℝ (fun y => g_u y + g_v y)) z.2 =
          fderiv ℝ (fun y => fderiv ℝ g_u y + fderiv ℝ g_v y) z.2 :=
        (show fderiv ℝ (fun y => g_u y + g_v y) =ᶠ[𝓝 z.2]
      fun y => fderiv ℝ g_u y + fderiv ℝ g_v y by
            filter_upwards [(hu.spatialSlice_contDiffAt hz).eventually (by norm_num),
              (hv.spatialSlice_contDiffAt hz).eventually (by norm_num)] with y huy hvy
            exact fderiv_fun_add (huy.differentiableAt (by norm_num))
              (hvy.differentiableAt (by norm_num))).fderiv_eq
      _ = fderiv ℝ (fderiv ℝ g_u) z.2 + fderiv ℝ (fderiv ℝ g_v) z.2 :=
        fderiv_fun_add huSecond.differentiableAt hvSecond.differentiableAt
  ext i j
  rw [Matrix.add_apply,
    scalarSpatialHessian_apply_eq_sndFDeriv
    ((hu.spatialSlice_contDiffAt hz).add (hv.spatialSlice_contDiffAt hz)) i j,
    scalarSpatialHessian_apply_eq_sndFDeriv (hu.spatialSlice_contDiffAt hz) i j,
    scalarSpatialHessian_apply_eq_sndFDeriv (hv.spatialSlice_contDiffAt hz) i j,
    hsecond]
  rfl

private theorem isScalarC12On_add   :
    IsScalarC12On (fun q => u q + v q) D := by
  refine ⟨hu.continuousOn.add hv.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hu.timeSlice_differentiableAt hz).add (hv.timeSlice_differentiableAt hz)
  · intro z hz
    exact (hu.spatialSlice_contDiffAt hz).add (hv.spatialSlice_contDiffAt hz)
  · apply (hu.continuousOn_scalarTimeDerivative.add
      hv.continuousOn_scalarTimeDerivative).congr
    intro z hz
    exact scalarTimeDerivative_add hu hv hz
  · apply (hu.continuousOn_scalarSpatialGradient.add
      hv.continuousOn_scalarSpatialGradient).congr
    intro z hz
    exact scalarSpatialGradient_add hu hv hz
  · apply (hu.continuousOn_scalarSpatialHessian.add
      hv.continuousOn_scalarSpatialHessian).congr
    intro z hz
    exact scalarSpatialHessian_add hu hv hz
end


private theorem scalarParabolicZeroOrderOperator_add
    (a : CoefficientField n) (b : PDE.TimeVectorField n)
    (c : PDE.TimeScalarField n) {u v : HypoellipticAleksandrov.Parabolic.ScalarField n}
    {D : HypoellipticAleksandrov.Parabolic.Region n} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarParabolicZeroOrderOperator a b c (fun q => u q + v q) z =
      scalarParabolicZeroOrderOperator a b c u z +
        scalarParabolicZeroOrderOperator a b c v z := by
  rw [scalarParabolicZeroOrderOperator_apply, scalarParabolicZeroOrderOperator_apply,
    scalarParabolicZeroOrderOperator_apply, scalarTimeDerivative_add hu hv hz,
    scalarSpatialGradient_add hu hv hz, scalarSpatialHessian_add hu hv hz]
  have hHessian : matrixContraction (a z.1 z.2)
      (scalarSpatialHessian u z + scalarSpatialHessian v z) =
      matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) +
        matrixContraction (a z.1 z.2) (scalarSpatialHessian v z) := by
    unfold matrixContraction
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  have hGradient : PDE.vecDot (b z.1 z.2)
      (scalarSpatialGradient u z + scalarSpatialGradient v z) =
      PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z) +
        PDE.vecDot (b z.1 z.2) (scalarSpatialGradient v z) := by
    unfold PDE.vecDot
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hHessian, hGradient]
  ring

variable {d : ℕ}

/-- The negative operator of a smooth stationary terminal lift is smooth. -/
theorem contDiff_terminal_lift_source
    (A : CoefficientField d) (b : PDE.TimeVectorField d)
    (φ : PDE.ScalarField d) (hA : IsSmoothCoefficient A)
    (hb : ContDiff ℝ PDE.smoothOrder (fun z : TimeVelocity d => b z.1 z.2))
    (hφ : ContDiff ℝ PDE.smoothOrder φ) :
    ContDiff ℝ PDE.smoothOrder (fun z  =>
      -scalarParabolicZeroOrderOperator A b (fun _ _ => 0) (fun p => φ p.2) z) := by
  let sharedTerm_6f97d52da6 := ((fun z : TimeVelocity d => φ z.2))
  have hw : ContDiff ℝ PDE.smoothOrder sharedTerm_6f97d52da6 :=
    hφ.comp contDiff_snd
  have hg (j : Fin d) : ContDiff ℝ PDE.smoothOrder
      (fun z  => scalarSpatialGradient sharedTerm_6f97d52da6 z j) := by
    have heq  :=
      funext (fun z => scalarSpatialGradient_apply_eq_coordinateIteratedFDeriv_of_contDiff_two
        (hw.of_le (by simp)) z j)
    rw [heq]
    exact contDiff_coordinateIteratedFDeriv_infty _ _ hw


  simpa only [scalarParabolicZeroOrderOperator_apply, coefficientAt, zero_mul, add_zero]
    using ((contDiff_smooth_backward_residual A hA sharedTerm_6f97d52da6 hw).add (show ContDiff ℝ PDE.smoothOrder (fun z  =>
      PDE.vecDot (b z.1 z.2) (scalarSpatialGradient sharedTerm_6f97d52da6 z)) by
        unfold PDE.vecDot
        apply ContDiff.sum
        intro j _
        exact ((contDiff_apply ℝ ℝ j).comp hb).mul (hg j))).neg

/-- Adding the smooth terminal lift cancels the correction's negative source. -/
theorem terminal_lift_assembly  {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)
    (a T : ℝ) (A : CoefficientField d) (b : PDE.TimeVectorField d)
    (φ : PDE.ScalarField d) (hφ : ContDiff ℝ PDE.smoothOrder φ) (hs : tsupport φ ⊆ Ω)
    (W : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hW : IsClassicalBackwardDirichletSolution a T Ω A b (fun _ _ => 0)
      (fun t y => -scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
        (fun p => φ p.2) (t, y)) (fun _ => 0) (fun _ => 0) W) :
    IsClassicalBackwardDirichletSolution a T Ω A b
      (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) (fun z => φ z.2 + W z) := by
  have hreg : IsScalarC12On (fun z  => φ z.2)
      (scalarParabolicOpenCylinder a T Ω) := isScalarC12On_of_contDiff_two
    ((hφ.comp (contDiff_snd : ContDiff ℝ PDE.smoothOrder (Prod.snd : TimeVelocity d → _))).of_le
      (by simp)) (scalarParabolicOpenCylinder a T Ω)
  refine ⟨(hφ.continuous.comp continuous_snd).continuousOn.add hW.1,
    isScalarC12On_add hreg hW.2.1, ?_, ?_, ?_⟩
  · intro z hz
    rw [scalarParabolicZeroOrderOperator_add A b (fun _ _ => 0) hreg hW.2.1 hz,
      hW.2.2.1 z hz]
    exact add_neg_cancel _
  · intro y hy
    change φ y + W (T, y) = φ y
    rw [hW.2.2.2.1 y hy, add_zero]
  · intro z hz


    change φ z.2 + W z = 0
    rw [(image_eq_zero_of_notMem_tsupport (fun h => (show z.2 ∉ Ω by
        have hf := hz.2
        rw [hΩ.frontier_eq] at hf
        exact hf.2) (hs h))), hW.2.2.2.2 z hz, zero_add]

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
