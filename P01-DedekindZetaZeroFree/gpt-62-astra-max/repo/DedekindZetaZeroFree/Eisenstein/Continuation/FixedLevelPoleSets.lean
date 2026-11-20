module

public import DedekindZetaZeroFree.Eisenstein.Continuation.FiniteWordResolventPoleSets

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

alias selected_scalar_pole_set_exists := DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource.selected_pole_set

end DedekindZetaZeroFree.ThetaExpansion

end
