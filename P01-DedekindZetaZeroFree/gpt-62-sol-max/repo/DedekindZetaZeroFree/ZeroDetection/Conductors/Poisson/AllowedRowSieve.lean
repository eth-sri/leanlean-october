module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ActualConductorSieve

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical







variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)



end

end DedekindZetaZeroFree.Quantitative.ActualConductorSieve
