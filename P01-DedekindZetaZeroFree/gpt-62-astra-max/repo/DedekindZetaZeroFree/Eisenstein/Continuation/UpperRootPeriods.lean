module

public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarGermUniqueness
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactRestrictionUpperRootPeriods

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.ThetaExpansion.ChamberPeriods
open MomentSources
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

alias selected_upper_period_continuation := DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation.selected_upper_period_continuation_proved

end DedekindZetaZeroFree.ThetaExpansion.ChamberPeriods

end
