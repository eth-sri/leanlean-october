module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteWeylUniformBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
open ThetaRawSheetEnvelope.WeightedWhittakerSheets
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

alias finite_weyl_value_bounds := DedekindZetaZeroFree.SheetRescaling.finite_weyl_bounds
end DedekindZetaZeroFree.ThetaExpansion

end
