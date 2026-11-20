module

public import DedekindZetaZeroFree.Eisenstein.Residues.EvaluationSimplePoleBounds

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

alias selected_scalar_order_at_zero_ge_neg_one := DedekindZetaZeroFree.EisensteinSmoothGerms.ScalarSource.selected_scalar_order_zero

end DedekindZetaZeroFree.ThetaExpansion
