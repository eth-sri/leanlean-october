module

public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
public import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalSourceFamily
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalKernel
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
open CenteredExceptionalProfile


section
variable (η : Character) (χ₀ : RayCharacter) (Q : Ideal HeckeFamily.O) (hQ : Q≤Ideal.span {(72:HeckeFamily.O)}) (m : HeckeFamily.O) (hm : m≠0) (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:HeckeFamily.O)∣m) (C D : Ideal HeckeFamily.O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D)) (τ : RayCharacter→Character) (hf : Family η C D hC hD U τ) (R : ℝ) (z : HeckeFamily.O) (hz : z∈partRows true η χ₀ Q m C D U R)

include hz in
lemma exceptional_part_nonzero     
        
     :z≠0:=
  sourceRows_nonzero C D U R z (Finset.mem_filter.mp hz).1

include hz in
lemma exceptional_part_inducing     
        
     :
    FixedInducingRow (childCharacter η χ₀) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z:=
  (Finset.mem_filter.mp hz).2

include hQ hm hml hm2 hf in
lemma actual_family_both_rows    
       
      
        
       :
    (∀χ:RayCharacter,∀z∈partRows true η χ₀ Q m C D U R,
      FixedInducingRow (τ χ) Q fixedBadMask 1 z) ∧
    (∀χ:RayCharacter,∀z∈partRows true η χ₀ Q m C D U R,
      FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)):=by
  have hz0:=exceptional_part_nonzero η χ₀ Q m C D U R
  have hex:=exceptional_part_inducing η χ₀ Q m C D U R
  constructor
  · intro χ z hz
    have hh:=(exceptional_rows_pair η χ₀ χ χ Q hQ m _ hml hm2 _ hex).1 z hz
    exact (hf.inducing_iff χ Q m z hm (hz0 z hz) hml hm2).mp hh
  · intro χ z hz
    have hh:=(exceptional_rows_pair η χ₀ χ (χ⁻¹) Q hQ m _ hml hm2 _ hex).2 z hz
    simp only [inv_inv] at hh
    exact (hf.inducing_iff χ Q m (-z) hm (neg_ne_zero.mpr (hz0 z hz)) hml hm2).mp hh

lemma exceptional_part_live     
       :
    liveRows C D U R (partRows true η χ₀ Q m C D U R)=
      partRows true η χ₀ Q m C D U R:=by
  apply Finset.filter_eq_self.mpr
  intro z hz
  exact liveRows_weight C D U R _ z (Finset.mem_filter.mp hz).1

end

end SevenEighths.CenteredMomentSecondExceptionalSourceFamily



end OAI
