module

public import OAI.NumberTheory.DirichletL.Detector.GramFrequency
public import OAI.NumberTheory.DirichletL.Detector.LowGramPoisson

@[expose] public section

namespace OAI


open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson


lemma gcd_generator_left  I J  :
    primaryGenerator I.val=primaryGenerator (gcdCommon I J).val*primaryGenerator (gcdLeft I J).val := by
  rw [←primaryGenerator_mul,gcd_common_left]

lemma gcd_generator_right  I J  :
    primaryGenerator J.val=primaryGenerator (gcdCommon I J).val*primaryGenerator (gcdRight I J).val := by
  rw [←primaryGenerator_mul,gcd_common_right]

end SevenEighths.ProbeGramCommon


end OAI
