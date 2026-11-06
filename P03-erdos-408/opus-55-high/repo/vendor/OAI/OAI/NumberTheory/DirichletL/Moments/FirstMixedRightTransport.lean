module

public import OAI.NumberTheory.DirichletL.Moments.FirstMixedRoot
public import OAI.NumberTheory.DirichletL.Moments.FirstMixedCommonRadius
public import OAI.NumberTheory.DirichletL.Moments.FirstCommonTransport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstMixedRightTransport
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstPhysicalSource CenteredMomentFirstMixedRoot
open CenteredMomentFirstScale

def swapIndex (C D : Ideal ActualEisensteinCubic.O) : CommonIndex C D ≃ CommonIndex D C where
  toFun P := ⟨P.val,by rw [commonSupport_comm];exact P.property⟩
  invFun P := ⟨P.val,by rw [commonSupport_comm];exact P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma swapIndex_val (C D : Ideal ActualEisensteinCubic.O) (P : CommonIndex C D) :
    (swapIndex C D P).val=P.val := rfl

def swapSubset (C D : Ideal ActualEisensteinCubic.O) (E : Finset (CommonIndex C D)) :
    Finset (CommonIndex D C) := E.map (swapIndex C D).toEmbedding

lemma swapSubset_product (C D : Ideal ActualEisensteinCubic.O) (E : Finset (CommonIndex C D)) :
    (∏P∈swapSubset C D E,P.val)=∏P∈E,P.val := by
  simp only [swapSubset,Finset.prod_map,Equiv.toEmbedding_apply,swapIndex_val]

lemma swapSubset_generator (C D : Ideal ActualEisensteinCubic.O) (E : Finset (CommonIndex C D)) :
    primeSubsetGenerator (fun P : CommonIndex D C=>P.val) (swapSubset C D E)=
      primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E := by
  unfold primeSubsetGenerator
  rw [swapSubset_product]

lemma swapped_modulus_factor (C D : Ideal ActualEisensteinCubic.O) (E : Finset (CommonIndex C D)) :
    Ideal.span {(primeSubsetGenerator (fun P : CommonIndex D C=>P.val)
      (swapSubset C D E)*activeConductor D C)}=
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D} := by
  rw [swapSubset_generator,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_mul_span_singleton,active_span_swap]

theorem right_modulus (η : Character) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayFourExpansion.RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    F.right.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:ActualEisensteinCubic.O)}*
      Ideal.span {(primeSubsetGenerator (fun P : CommonIndex D C=>P.val)
        (swapSubset C D E)*activeConductor D C)} := by
  rw [swapped_modulus_factor]
  exact F.right_modulus

lemma nominal_swap (C D E : Ideal ActualEisensteinCubic.O) (K X : ℝ) :
    firstNominalScale D C E K X=firstNominalScale C D E K X := by
  unfold firstNominalScale
  rw [active_span_swap]
  ring

end SevenEighths.CenteredMomentFirstMixedRightTransport

end

end OAI
