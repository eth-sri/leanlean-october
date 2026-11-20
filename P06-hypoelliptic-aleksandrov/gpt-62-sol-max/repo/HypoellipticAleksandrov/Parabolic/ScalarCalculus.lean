module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import HypoellipticAleksandrov.Parabolic.Derivatives
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring

/-! Hessian coordinates and subtraction for classical scalar parabolic functions. -/

@[expose] public section
noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set Matrix
open scoped MatrixOrder Topology

section
variable {n : ℕ} {u v : TimeVelocity n → ℝ} {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D)
  (hv : IsScalarC12On v D) {z : TimeVelocity n} (hz : z ∈ D)
include D hu hv hz

theorem scalarTimeDerivative_sub :
    scalarTimeDerivative (fun q => u q - v q) z =
      scalarTimeDerivative u z - scalarTimeDerivative v z := by
  exact ((hu.timeSlice_hasDerivAt hz).sub (hv.timeSlice_hasDerivAt hz)).deriv

theorem scalarSpatialGradient_sub :
    scalarSpatialGradient (fun q => u q - v q) z =
      scalarSpatialGradient u z - scalarSpatialGradient v z := by
  ext i
  change fderiv ℝ (fun y : PDE.Vec n => u (z.1, y) - v (z.1, y)) z.2
      (PDE.basisVec i) = _
  rw [fderiv_fun_sub ((hu.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))
    ((hv.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))]
  rfl

end

theorem scalarSpatialHessian_apply_eq_sndFDeriv {n : ℕ}
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (i j : Fin n) :
    scalarSpatialHessian u z i j =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2
        (PDE.basisVec i) (PDE.basisVec j) := classicalGradient_fderiv_apply hu i j

section
variable {n : ℕ} {u v : TimeVelocity n → ℝ} {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D)
  (hv : IsScalarC12On v D)
include hu hv

theorem scalarSpatialHessian_sub
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarSpatialHessian (fun q => u q - v q) z =
      scalarSpatialHessian u z - scalarSpatialHessian v z := by
  have hu' := hu.spatialSlice_contDiffAt hz
  have hv' := hv.spatialSlice_contDiffAt hz
  have hsecond := fderiv_fderiv_fun_sub hu' hv'
  ext i j
  rw [Matrix.sub_apply,
    scalarSpatialHessian_apply_eq_sndFDeriv
    ((hu.spatialSlice_contDiffAt hz).sub (hv.spatialSlice_contDiffAt hz)) i j,
    scalarSpatialHessian_apply_eq_sndFDeriv (hu.spatialSlice_contDiffAt hz) i j,
    scalarSpatialHessian_apply_eq_sndFDeriv (hv.spatialSlice_contDiffAt hz) i j,
    hsecond]
  rfl

theorem isScalarC12On_sub :
    IsScalarC12On (fun q => u q - v q) D := by
  refine ⟨hu.continuousOn.sub hv.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hu.timeSlice_differentiableAt hz).sub (hv.timeSlice_differentiableAt hz)
  · intro z hz
    exact (hu.spatialSlice_contDiffAt hz).sub (hv.spatialSlice_contDiffAt hz)
  · apply (hu.continuousOn_scalarTimeDerivative.sub
      hv.continuousOn_scalarTimeDerivative).congr
    intro z hz
    exact scalarTimeDerivative_sub hu hv hz
  · apply (hu.continuousOn_scalarSpatialGradient.sub
      hv.continuousOn_scalarSpatialGradient).congr
    intro z hz
    exact scalarSpatialGradient_sub hu hv hz
  · apply (hu.continuousOn_scalarSpatialHessian.sub
      hv.continuousOn_scalarSpatialHessian).congr
    intro z hz
    exact scalarSpatialHessian_sub hu hv hz

end

theorem scalarParabolicZeroOrderOperator_sub {n : ℕ}
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ) {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarParabolicZeroOrderOperator a b c (fun q => u q - v q) z =
      scalarParabolicZeroOrderOperator a b c u z -
        scalarParabolicZeroOrderOperator a b c v z := by
  simp only [scalarParabolicZeroOrderOperator_apply, scalarTimeDerivative_sub hu hv hz,
    scalarSpatialGradient_sub hu hv hz, scalarSpatialHessian_sub hu hv hz,
    matrixContraction, PDE.vecDot, Matrix.sub_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Classical parabolic regularity restricts to subsets. -/
theorem IsScalarC12On.mono {d : ℕ} {u : TimeVelocity d → ℝ}
    {s t : Set (TimeVelocity d)} (h : IsScalarC12On u t) (hst : s ⊆ t) : IsScalarC12On u s :=
  ⟨h.continuousOn.mono hst, fun _ hz => h.timeSlice_differentiableAt (hst hz),
    fun _ hz => h.spatialSlice_contDiffAt (hst hz), h.continuousOn_scalarTimeDerivative.mono hst,
    h.continuousOn_scalarSpatialGradient.mono hst, h.continuousOn_scalarSpatialHessian.mono hst⟩

end HypoellipticAleksandrov.Parabolic
