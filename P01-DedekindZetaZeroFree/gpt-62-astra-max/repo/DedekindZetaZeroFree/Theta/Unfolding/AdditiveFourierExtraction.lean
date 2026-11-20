module

public import DedekindZetaZeroFree.Theta.Unfolding.AbsoluteOrbitExtraction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

alias absolute_extraction := DedekindZetaZeroFree.OrbitExpansion.absolute_extraction

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
