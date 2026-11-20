module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInductionAndBorelRetraction

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPActualScalarBinding

noncomputable section

variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : HeightOneSpectrum (𝓞 F))

abbrev ActualKPBinding := @DedekindZetaZeroFree.KPExceptionalRaw.RawFiniteInducingData

end
end DedekindZetaZeroFree.KPActualScalarBinding
