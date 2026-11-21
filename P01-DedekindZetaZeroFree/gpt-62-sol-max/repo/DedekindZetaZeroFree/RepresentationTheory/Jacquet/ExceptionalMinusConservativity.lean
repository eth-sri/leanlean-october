module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ExceptionalPlusSubmoduleMonotonicity

@[expose] public section

namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.MinusLengthSteps
open scoped NumberField Valued
open NumberField IsDedekindDomain KPLocalPrincipalSeries KPLocalStoneVonNeumann PlusLengthSteps
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (q : HeightOneSpectrum (𝓞 F)) (S : RawFiniteInducingData F ζ hζ q)

theorem independent_minus_jacquet_strictMono (P : Polarization S.heisenberg) : by
    letI : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance
    exact StrictMono (jacquetSubmoduleImage S.borel (IMinus S.borel P)) :=
  jacquet_strictMono F ζ hζ q S P .minus

end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.ImagesIrreducibilitySteps.MinusLengthSteps
