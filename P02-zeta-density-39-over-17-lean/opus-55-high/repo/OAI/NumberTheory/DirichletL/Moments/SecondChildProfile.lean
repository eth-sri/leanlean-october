module
public import OAI.NumberTheory.DirichletL.Moments.FirstChildProfile
public import OAI.NumberTheory.DirichletL.Moments.SecondScaled
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondChildProfile
open HeckeFamily HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow CenteredMomentChildAssembly
open CenteredMomentSecondScaled CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

theorem child_ideal_primary (η : Character) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (childCharacter η χ) I=idealCoeff η I*rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  pm_111 hn supported_primaryGenerator_ne_zero I hI hs primary_span_supported
  have hc := idealCoeff_span (childCharacter η χ) hn
  have he := idealCoeff_span η hn
  rw [hs] at hc he
  rw [hc,childCharacter_primary η χ _ (by grind)
    (CompletedGauss.primaryGenerator_spec I hn).2,←he]

end SevenEighths.CenteredMomentSecondChildProfile

end

end OAI
