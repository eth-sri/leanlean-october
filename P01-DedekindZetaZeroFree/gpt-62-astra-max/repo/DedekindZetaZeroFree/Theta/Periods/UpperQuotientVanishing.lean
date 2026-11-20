module

public import DedekindZetaZeroFree.Theta.Unfolding.ReverseAbsoluteConvergence
public import DedekindZetaZeroFree.Theta.Unfolding.UpperVanishingCertificates

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

alias both_upper_averages_zero := DedekindZetaZeroFree.IdeleInsertion.jointUpperVanishingSources_of_jointReverseAbsoluteSources

end DedekindZetaZeroFree.ThetaExpansion
