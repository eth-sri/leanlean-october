module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import HypoellipticAleksandrov.Parabolic.ScalarMaximum

/-!
# Scalar zero-order backward parabolic maximum principle

This file proves the scalar backward maximum principle with a nonpositive
zero-order coefficient on an arbitrary open bounded velocity domain.  The
initial face is handled by compact cylinders whose lower time is strictly later
than the original initial time, followed by closed-cylinder continuity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set Matrix
open scoped MatrixOrder Topology

/--
If the backward scalar operator with a nonpositive zero-order coefficient is
nonnegative on the open cylinder, then nonpositive terminal and lateral data
control the whole closed cylinder.  The proof uses strictly inset cylinders
before passing to the initial face by continuity.
-/
theorem scalar_le_zero_on_closedCylinder_of_zeroOrderOperator_nonneg
    {n : ℕ} {Ω : Set (PDE.Vec n)} {r₀ r₁ : ℝ}
    (hΩOpen : IsOpen Ω)
    (hΩBounded : Bornology.IsBounded Ω)
    (hr : r₀ < r₁)
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ)
    (_haContinuous : IsContinuousCoefficient a)
    (_hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      c z.1 z.2 ≤ 0)
    (w : TimeVelocity n → ℝ)
    (hw : ContinuousOn w (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hwC12 : IsScalarC12On w (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (hPDE : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      0 ≤ scalarParabolicZeroOrderOperator a b c w z)
    (hTerminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, w z ≤ 0)
    (hLateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, w z ≤ 0) :
    ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, w z ≤ 0 := by
  refine scalar_le_on_closedCylinder_of_operator_nonneg_above hΩOpen hΩBounded hr a b haPsd w
    hw hwC12 ?_ hTerminal hLateral
  intro z hz hwz
  have hcz := mul_nonpos_of_nonpos_of_nonneg (hc z hz) hwz.le
  have hp := hPDE z hz
  unfold scalarParabolicZeroOrderOperator at hp
  linarith

end HypoellipticAleksandrov.Parabolic
