module

public import OAI.NumberTheory.DirichletL.Moments.FirstMixedRoot
public import OAI.NumberTheory.DirichletL.Moments.FirstMixedCommonRadius
public import OAI.NumberTheory.DirichletL.Moments.FirstCommonTransport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedRightTransport
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstPhysicalSource CenteredMomentFirstMixedRoot
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstMixedCommonRadius CenteredMomentFirstMixedAllowance
open CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius CenteredMomentDescentLedger


def swapIndex (C D : Ideal ActualEisensteinCubic.O) : CommonIndex C D ≃ CommonIndex D C where
  toFun P := ⟨P.val,by rw [commonSupport_comm];exact P.property⟩
  invFun P := ⟨P.val,by rw [commonSupport_comm];exact P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma swapIndex_val  C D   P  :
    (swapIndex C D P).val=P.val := rfl

def swapSubset (C D ) (E : Finset (CommonIndex C D))  := E.map (swapIndex C D).toEmbedding

section
variable (η : Character) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (E : Finset (CommonIndex C D))

lemma swapSubset_product     :
    (∏P∈swapSubset C D E,P.val)=∏P∈E,P.val := by
  simp only [swapSubset,Finset.prod_map,Equiv.toEmbedding_apply,swapIndex_val]

lemma swapSubset_generator     :
    primeSubsetGenerator (fun P : CommonIndex D C=>P.val) (swapSubset C D E)=
      primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E := by
  unfold primeSubsetGenerator
  rw [swapSubset_product]

lemma swapped_modulus_factor     :
    Ideal.span {(primeSubsetGenerator (fun P : CommonIndex D C=>P.val)
      (swapSubset C D E)*activeConductor D C)}=
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D} := by
  rw [swapSubset_generator,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_mul_span_singleton,active_span_swap]

theorem right_modulus      
      (ξ₁ ξ₂ : RayFourExpansion.RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    F.right.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:ActualEisensteinCubic.O)}*
      Ideal.span {(primeSubsetGenerator (fun P : CommonIndex D C=>P.val)
        (swapSubset C D E)*activeConductor D C)} := by
  rw [swapped_modulus_factor]
  exact F.right_modulus

end

lemma nominal_swap  C D E   K X  :
    firstNominalScale D C E K X=firstNominalScale C D E K X := by
  unfold firstNominalScale
  rw [active_span_swap]
  congr 1
  ring

end SevenEighths.CenteredMomentFirstMixedRightTransport

end

end OAI
