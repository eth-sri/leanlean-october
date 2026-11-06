module

public import DedekindZetaZeroFree.Theta.Periods.WildPartialPeriodFactorization
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint
public import DedekindZetaZeroFree.Theta.Profiles.ResidualCoreAndUnitRotations
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPWildActualCompactKernel

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

instance rawImageAdd (U : Submodule ℂ (KPGlobalTorusFunctionData.G F ζ hζ → ℂ)) :
    AddCommGroup U := Submodule.addCommGroup U

end DedekindZetaZeroFree.KPWildActualCompactKernel

end
