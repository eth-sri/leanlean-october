module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowNonprincipal

noncomputable section

open DedekindZetaZeroFree NumberField
open PrincipalMellinComparison.NonprincipalContinuation

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)


end

end DedekindZetaZeroFree.Quantitative.RowNonprincipal
