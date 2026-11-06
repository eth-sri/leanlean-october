module
public import OAI.NumberTheory.DirichletL.Moments.FirstChildProfile
public import OAI.NumberTheory.DirichletL.Moments.SecondScaled

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondChildProfile
open HeckeFamily HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSourceRow CenteredMomentChildAssembly CenteredMomentSecondScaled CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion ConcretePrimeRowBridge CenteredMomentCommonSupport

theorem child_ideal_primary (η : Character) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (childCharacter η χ) I=idealCoeff η I*rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have hc := idealCoeff_span (childCharacter η χ) hn
  have he := idealCoeff_span η hn
  rw [hs] at hc he
  rw [hc,childCharacter_primary η χ _ (by rw [hs];exact hI)
    (CompletedGauss.primaryGenerator_spec I hn).2,←he]
