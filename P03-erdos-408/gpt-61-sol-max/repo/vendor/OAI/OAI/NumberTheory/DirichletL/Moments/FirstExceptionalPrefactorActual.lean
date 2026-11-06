module

public import OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactor
public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstExceptionalPrefactor
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentFirstNonexceptionalPrefactor CenteredMomentFirstScale IdealMobiusDivisorSum


section
variable (C D E : Ideal ActualEisensteinCubic.O) (hC : C≠0) (hD : D≠0) (hCD : primeSupport C=primeSupport D)


include hC hCD in
lemma commonPart_of_equal_support   
     :commonPart C D=C := by
  have he:commonPart C D=commonPart C C:=by
    simp only [commonPart,commonSupport,←hCD]
  exact he.trans (commonPart_self C hC)

include hC hD hCD in
lemma nominal_equal_support    
      K V :
    firstNominalScale C D E K V=
      (E.absNorm:ℝ)*(Ideal.span {activeConductor C D}).absNorm*V^2/
        (K*(C.absNorm:ℝ)*D.absNorm) := by
  rw [firstNominalScale,commonPart_of_equal_support C D hC hCD,
    commonPart_of_equal_support D C hD hCD.symm]

end

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentFirstExceptionalPrefactor



end OAI
