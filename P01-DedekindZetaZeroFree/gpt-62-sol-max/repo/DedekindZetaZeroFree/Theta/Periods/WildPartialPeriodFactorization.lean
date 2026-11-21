module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.FiniteExceptionalRepresentationData
public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedFiniteTensorProducts

@[expose] public section

noncomputable section

open scoped NumberField

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPWildPartialPeriodFactorization

open KPLocalExceptionalConstruction

variable (F : Type) [Field F] [NumberField F]

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def wildPlaces : Set (HeightOneSpectrum (𝓞 F)) :=
  {q | (3 : 𝓞 F) ∈ q.asIdeal}


abbrev WildPlace := ↥(wildPlaces F)


end DedekindZetaZeroFree.KPWildPartialPeriodFactorization

end
