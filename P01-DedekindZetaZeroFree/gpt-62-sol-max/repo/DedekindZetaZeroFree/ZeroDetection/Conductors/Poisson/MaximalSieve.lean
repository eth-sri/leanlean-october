module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Definitions
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.AllowedRowSieve

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorSieve

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)





end

end DedekindZetaZeroFree.Quantitative.DetectorSieve
