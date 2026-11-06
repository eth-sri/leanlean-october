module

public import HypoellipticAleksandrov.Parabolic.ScalarZeroOrderMaximum
public import Mathlib.Tactic.Ring

/-!
# Classical scalar backward Dirichlet comparison

This module derives comparison and uniqueness for supplied classical solutions
of the bounded scalar backward Dirichlet problem from the zero-order maximum
principle.  It constructs neither solutions nor a Dirichlet solver.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open Filter Set Matrix
open scoped MatrixOrder Topology

variable {n : ℕ} {Ω : Set (PDE.Vec n)} {r₀ r₁ : ℝ} {u v : TimeVelocity n → ℝ} {D : Set (TimeVelocity n)}

private theorem scalarTimeDerivative_sub  (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarTimeDerivative (fun q => u q - v q) z =
      scalarTimeDerivative u z - scalarTimeDerivative v z := ((hu.timeSlice_hasDerivAt hz).sub (hv.timeSlice_hasDerivAt hz)).deriv

private theorem scalarSpatialGradient_sub  (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarSpatialGradient (fun q => u q - v q) z =
      scalarSpatialGradient u z - scalarSpatialGradient v z := by
  ext i
  change fderiv ℝ (fun y : PDE.Vec n => u _ - v _) z.2
      _ = _
  rw [fderiv_fun_sub ((hu.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))
    ((hv.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))]
  rfl

private theorem scalarSpatialHessian_sub  (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarSpatialHessian (fun q => u q - v q) z =
      scalarSpatialHessian u z - scalarSpatialHessian v z := by
  let g_u  := fun y => u (z.1, y)
  let g_v  := fun y => v (z.1, y)
  have hfirst : fderiv ℝ (fun y => g_u y - g_v y) =ᶠ[𝓝 z.2]
      fun y => fderiv ℝ g_u y - fderiv ℝ g_v y := by
    filter_upwards [(hu.spatialSlice_contDiffAt hz).eventually (by norm_num),
      (hv.spatialSlice_contDiffAt hz).eventually (by norm_num)] with y huy hvy
    exact fderiv_fun_sub (huy.differentiableAt (by norm_num))
      (hvy.differentiableAt (by norm_num))
  have huSecond : HasFDerivAt (fun y : PDE.Vec n => fderiv ℝ g_u y)
      (fderiv ℝ (fderiv ℝ g_u) z.2) z.2 :=
    ((hu.spatialSlice_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hvSecond : HasFDerivAt (fun y : PDE.Vec n => fderiv ℝ g_v y)
      (fderiv ℝ (fderiv ℝ g_v) z.2) z.2 :=
    ((hv.spatialSlice_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hsecond : fderiv ℝ (fderiv ℝ (fun y => g_u y - g_v y)) z.2 =
      fderiv ℝ (fderiv ℝ g_u) z.2 - fderiv ℝ (fderiv ℝ g_v) z.2 := by
    calc
      fderiv ℝ _ z.2 =
          fderiv ℝ _ z.2 :=
        hfirst.fderiv_eq
      _ = fderiv ℝ _ z.2 - fderiv ℝ _ z.2 :=
        fderiv_fun_sub huSecond.differentiableAt hvSecond.differentiableAt
  ext i j
  rw [Matrix.sub_apply,
    scalarSpatialHessian_apply_eq_sndFDeriv
    ((hu.spatialSlice_contDiffAt hz).sub (hv.spatialSlice_contDiffAt hz)),
    scalarSpatialHessian_apply_eq_sndFDeriv (hu.spatialSlice_contDiffAt hz),
    scalarSpatialHessian_apply_eq_sndFDeriv (hv.spatialSlice_contDiffAt hz),
    hsecond]
  rfl

private theorem isScalarC12On_sub  (hu : IsScalarC12On u D) (hv : IsScalarC12On v D) :
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

private theorem scalarParabolicZeroOrderOperator_sub 
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ) {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarParabolicZeroOrderOperator a b c (fun q => u q - v q) z =
      scalarParabolicZeroOrderOperator a b c u z -
        scalarParabolicZeroOrderOperator a b c v z := by
  rw [scalarParabolicZeroOrderOperator_apply, scalarParabolicZeroOrderOperator_apply,
    scalarParabolicZeroOrderOperator_apply, scalarTimeDerivative_sub hu hv hz,
    scalarSpatialGradient_sub hu hv hz, scalarSpatialHessian_sub hu hv hz]
  have hHessian : matrixContraction (a z.1 z.2)
      (scalarSpatialHessian u z - scalarSpatialHessian v z) =
      matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) -
        matrixContraction (a z.1 z.2) (scalarSpatialHessian v z) := by
    unfold matrixContraction
    simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hGradient : PDE.vecDot (b z.1 z.2)
      (scalarSpatialGradient u z - scalarSpatialGradient v z) =
      PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z) -
        PDE.vecDot (b z.1 z.2) (scalarSpatialGradient v z) := by
    unfold PDE.vecDot
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  linarith

/-- Ordered source, terminal, and lateral data order supplied classical backward solutions. -/
theorem le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
    
    (hΩOpen : IsOpen Ω)
    (hΩBounded : Bornology.IsBounded Ω)
    (hr : r₀ < r₁)
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ)
    (haContinuous : IsContinuousCoefficient a)
    (hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω, c z.1 z.2 ≤ 0)
    (F_u F_v : ℝ → PDE.Vec n → ℝ)
    (phi_u phi_v : PDE.Vec n → ℝ)
    (h_u h_v u v : TimeVelocity n → ℝ)
    (hu : IsClassicalBackwardDirichletSolution r₀ r₁ Ω a b c F_u phi_u h_u u)
    (hv : IsClassicalBackwardDirichletSolution r₀ r₁ Ω a b c F_v phi_v h_v v)
    (hF : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      F_v z.1 z.2 ≤ F_u z.1 z.2)
    (hPhi : ∀ y ∈ closure Ω, phi_u y ≤ phi_v y)
    (hLat : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, h_u z ≤ h_v z) :
    ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, u z ≤ v z := by
  have hzero : ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, u z - v z ≤ 0 := by
    apply scalar_le_zero_on_closedCylinder_of_zeroOrderOperator_nonneg
      hΩOpen hΩBounded hr a b c haContinuous hbContinuous haPsd hc _
    · exact hu.1.sub hv.1
    · exact isScalarC12On_sub hu.2.1 hv.2.1
    · intro z hz
      rw [scalarParabolicZeroOrderOperator_sub a b c hu.2.1 hv.2.1 hz,
        hu.2.2.1 z hz, hv.2.2.1 z hz]
      grind
    · rintro ⟨r, y⟩ ⟨hr, hy⟩
      simp only [mem_singleton_iff] at hr
      subst r
      rw [hu.2.2.2.1 y hy, hv.2.2.2.1 y hy]
      simp_all
    · intro z hz
      rw [hu.2.2.2.2 z hz, hv.2.2.2.2 z hz]
      grind
  simp_all

/-- Classical backward Dirichlet solutions with identical data agree on the closed cylinder. -/
theorem eqOn_closedCylinder_of_isClassicalBackwardDirichletSolution
    
    (hΩOpen : IsOpen Ω)
    (hΩBounded : Bornology.IsBounded Ω)
    (hr : r₀ < r₁)
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c F : ℝ → PDE.Vec n → ℝ)
    (phi : PDE.Vec n → ℝ) (h u v : TimeVelocity n → ℝ)
    (haContinuous : IsContinuousCoefficient a)
    (hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω, c z.1 z.2 ≤ 0)
    (hu : IsClassicalBackwardDirichletSolution r₀ r₁ Ω a b c F phi h u)
    (hv : IsClassicalBackwardDirichletSolution r₀ r₁ Ω a b c F phi h v) :
    Set.EqOn u v (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
  intro z hz
  apply le_antisymm
  · exact le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
      hΩOpen hΩBounded hr a b c haContinuous hbContinuous haPsd hc F F phi phi h h u v
      hu hv (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) z hz
  · exact le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
      hΩOpen hΩBounded hr a b c haContinuous hbContinuous haPsd hc F F phi phi h h v u
      hv hu (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) z hz

end HypoellipticAleksandrov.Parabolic
