module

public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedResidualFunctionals
public import DedekindZetaZeroFree.Theta.Whittaker.SphericalCRTProduct

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

alias exterior_spherical_factors_crt := DedekindZetaZeroFree.ExteriorWhittakerValues.NumericalSpherical.sphericalProduct

end DedekindZetaZeroFree.ThetaExpansion

end
