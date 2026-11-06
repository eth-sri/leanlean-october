module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourcePairing
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalPairingIdentity

open private HypoellipticAleksandrov.Parabolic.Dirichlet.integrable_reverseTimeNegativeSourceRaw_mul_test from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalPairingIdentity


/-!
# Reverse-time separated variational residual

This module records the separated-test residual supplied directly by the reverse-time
variational energy solution.
-/

 public section

open MeasureTheory Set
open scoped ENNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet




private theorem integral_sub_add_eq_zero_of_pairing
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (mass form source dual : α → ℝ)
    (hmass : Integrable mass μ) (hform : Integrable form μ)
    (hsource : Integrable source μ)
    (hmassEq : (∫ x, mass x ∂μ) = -(∫ x, dual x ∂μ))
    (hformEq : (∫ x, form x ∂μ) = (∫ x, source x ∂μ) - ∫ x, dual x ∂μ) :
    (∫ x, mass x - form x + source x ∂μ) = 0 := by
  change (∫ x, (mass - form) x + source x ∂μ) = 0
  rw [integral_add (hmass.sub hform) hsource]
  change (∫ x, mass x - form x ∂μ) + ∫ x, source x ∂μ = 0
  rw [integral_sub hmass hform, hmassEq, hformEq]
  ring

/-- A reverse-time variational energy solution satisfies the separated-test residual identity. -/
theorem reverseTime_separated_residual_of_variationalEnergy
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 ))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu)
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (v : H10HilbertGraph hΩ) :
    Integrable (fun tau =>
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau -
        reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau +
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau)
      (reverseTimeVolume (r₁ - r₀)) ∧
    (∫ tau,
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau -
        reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau +
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau
      ∂reverseTimeVolume (r₁ - r₀)) = 0 := by

  let sharedTerm_2a2377c46e := ((reverseTimeVolume (r₁ - r₀)))
  obtain ⟨hmassLift, hg, hmassLiftEq⟩ := hdu v eta
  have hmass : Integrable (fun tau =>
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau)
      sharedTerm_2a2377c46e := by
    refine hmassLift.congr ?_
    filter_upwards [coeFn_reverseTimeValueCLM hΩ (r₁ - r₀) u] with tau huValue
    rw [huValue]

  have hsource := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.integrable_reverseTimeNegativeSourceRaw_mul_test r₀ r₁ h₀₁ hΩ hΩbounded F
    hFSmooth eta v
  have hformEq : ∀ᵐ tau ∂reverseTimeVolume (r₁ - r₀),
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau =
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau -
          (g tau) v * eta tau := by
    filter_upwards [hu.2, ae_restrict_mem measurableSet_Ioo] with tau hEquation htau
    have hRaw  :=
      reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
        tau ⟨le_of_lt htau.1, le_of_lt htau.2⟩
    have hPoint := hEquation htau v
    rw [← hRaw] at hPoint
    calc
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau =
          ((g tau) v + reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v - (g tau) v) * eta tau := by
            ring
      _ = (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v -
          (g tau) v) * eta tau := by
            rw [hPoint]
      _ = _ := sub_mul _ _ _
  have hform : Integrable (fun tau =>
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau)
      sharedTerm_2a2377c46e :=
    (hsource.sub hg).congr (by
      filter_upwards [hformEq] with tau htau
      exact htau.symm)

  constructor
  · exact (hmass.sub hform).add hsource
  · exact integral_sub_add_eq_zero_of_pairing sharedTerm_2a2377c46e _ _ _ _
      hmass hform hsource (by
          calc
            _ = ∫ tau,
                inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ (r₁ - r₀) u tau) * eta.deriv tau
                ∂reverseTimeVolume (r₁ - r₀) := by
              apply integral_congr_ae
              filter_upwards [coeFn_reverseTimeValueCLM hΩ (r₁ - r₀) u] with tau huValue
              rw [huValue]
            _ = _ := hmassLiftEq) (by
          calc
            _ = ∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau -
                (g tau) v * eta tau ∂reverseTimeVolume (r₁ - r₀) := integral_congr_ae hformEq
            _ = _ := integral_sub hsource hg)

end HypoellipticAleksandrov.Parabolic.Dirichlet
