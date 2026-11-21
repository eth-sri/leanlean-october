module

public import DedekindZetaZeroFree.Theta.Unfolding.SmoothingMassFubini

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem reverseAbsolute_of_orbit (N : TraceHaarTransport R)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (hs : ∀ v (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) (hZ : 0 < Z),
      letI := N.groupHaar_isHaar;
      Summable (fun i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A =>
        ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
          ∫ t : PositiveAxis, ∫ z : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩,
            ‖P.kernel t.val * digitWeight R m d *
              orbitFrequencyValue R Q T v i (signedArgument R m b z.val d)‖
            ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar ⟨t.val / Z, div_pos t.property hZ⟩
            ∂positiveHaar))
    (hp : ∀ v (m : ThetaReflectionData.Row R.A) b Z (hZ : 0 < Z) i d,
      letI := N.groupHaar_isHaar;
      Integrable (fun p : PositiveAxis × R.A.G1 =>
        P.kernel p.1.val * digitWeight R m d * orbitFrequencyValue R Q T v i
          (signedArgument R m b (sheetTranslation R.A P.v₀
            ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2).val d))
        (positiveHaar.prod ((kernelHaar R.A P.v₀ N.groupHaar).restrict (pregroupingDomain R.A).carrier))) :
    ReverseAbsolute R N Q T P := by
  exact {
    orbit_period_integrable := orbitFrequencyIntegrand_integrable R T
    orbit_pregrouping := hs
    orbit_smoothing_integrable := fun v m b Z hZ i d =>
      smoothing_mass_integrable_of_product R N P.v₀ Z hZ
        (fun t z => P.kernel t.val * digitWeight R m d *
          orbitFrequencyValue R Q T v i (signedArgument R m b z.val d)) (hp v m b Z hZ i d)
    orbit_sheet_integrable := orbit_sheet_integrable R N T P
    orbit_product_integrable := hp
  }

end DedekindZetaZeroFree.OrbitFrequencies

end
