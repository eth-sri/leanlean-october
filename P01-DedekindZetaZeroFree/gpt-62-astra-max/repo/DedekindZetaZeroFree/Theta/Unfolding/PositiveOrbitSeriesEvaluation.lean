module

public import DedekindZetaZeroFree.Theta.Unfolding.GroupedForwardOrbitEvaluation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.SignedExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

alias forward_orbit_evaluation := DedekindZetaZeroFree.OrbitExpansion.forward_orbit_evaluation

end DedekindZetaZeroFree.ThetaExpansion.SignedExpansion

end
