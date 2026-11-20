module

public import DedekindZetaZeroFree.Theta.Digits.Exterior.ProductAverageCoefficients

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

theorem exterior_digit_coefficient {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (m : ThetaReflectionData.Row R.A)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed m) (x : Fˣ) :
    exteriorDigitCoefficient R C m x =
      ThetaBranch.exteriorCoefficient R.A R.probe.allowed R.σ (Characters.psi R) m D x := by
  exact DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits.coefficient_exact R C m D x

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
