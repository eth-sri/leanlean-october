module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencySumBound

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.OmittedProbeBound

open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

alias omittedSum_bound := DedekindZetaZeroFree.Quantitative.RawOmittedRowsAssembly31.rawOmittedSum_bound

end DedekindZetaZeroFree.Quantitative.OmittedProbeBound
