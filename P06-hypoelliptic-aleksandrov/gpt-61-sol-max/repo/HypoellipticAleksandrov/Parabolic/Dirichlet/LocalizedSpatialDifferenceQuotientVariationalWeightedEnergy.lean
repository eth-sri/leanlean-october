module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalWeightedEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientEnergyTestH10

 public section

open scoped ENNReal Matrix.Norms.Elementwise

/-!
# Localized reverse-time variational weighted energy identity

This module specializes the reverse-time variational weighted identity
to the totalized localized spatial quotient and its literal energy test.
-/



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

namespace IsReverseTimeVariationalEnergySolution

/-- A reverse-time variational energy solution satisfies the weighted identity
for the localized quotient and its energy test. -/
theorem
    integral_localizedSpatialDifferenceQuotient_norm_sq_mul_reverseTimeScalarTest_deriv_eq
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 ))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
    {inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) : type_of% (integral_value_norm_sq_mul_reverseTimeScalarTest_deriv_eq
        r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
        initial u g hdu hu
        (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift)
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM
          hΩ η k h hηΩ hηshift)
        (fun x y =>
          inner_value_localizedSpatialDifferenceQuotientEnergyTestH10CLM_eq
            hΩ η k h x y hηΩ hηshift)
        ζ) := integral_value_norm_sq_mul_reverseTimeScalarTest_deriv_eq
        r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
        initial u g hdu hu
        (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift)
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM
          hΩ η k h hηΩ hηshift)
        (fun x y =>
          inner_value_localizedSpatialDifferenceQuotientEnergyTestH10CLM_eq
            hΩ η k h x y hηΩ hηshift)
        ζ

end IsReverseTimeVariationalEnergySolution

end HypoellipticAleksandrov.Parabolic.Dirichlet
