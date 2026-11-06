module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SecondRadicalColumns
public import OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport
public import OAI.NumberTheory.DirichletL.Moments.FixedRowMask

@[expose] public section

namespace OAI


open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondReducedPredicate
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredExceptionalProfile CenteredMomentFixedRowMask CenteredMomentRestrictedEnergy
open CenteredMomentSecondFamilyTransport CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSixthReduction CenteredMomentCanonicalFirst RayFourExpansion


section
variable (η τ : Character) (χ : RayCharacter) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (U : Finset (CommonIndex C D)) (hτ : ∀n:ActualEisensteinCubic.O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n) (Q : Ideal ActualEisensteinCubic.O) (m n A z : ActualEisensteinCubic.O) (hm : m≠0) (hn : n≠0) (hA : A≠0) (hz : z≠0) (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:ActualEisensteinCubic.O)∣m)

include hm hn hA hz hmLam hm2 in
theorem fixed_mask_change      
           
       
    (hnLam:ConcretePrimeRowBridge.goodLambda∣n) (hn2:(2:ActualEisensteinCubic.O)∣n) :
    FixedInducingRow η Q m A z ↔ FixedInducingRow η Q n A z := by
  have h1:=fixedInducingRow_mul_mask_iff η Q m n A z hm hn hA hz hmLam hm2
  have h2:=fixedInducingRow_mul_mask_iff η Q n m A z hn hm hA hz hnLam hn2
  rw [mul_comm n m] at h2
  exact h1.symm.trans h2

include hC hτ hm hz hmLam hm2 in
theorem actual_reduced_inducing_iff    
         
     
           
        :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [fixed_sixth_inducing_iff _ Q m z hm hz hmLam hm2 C D hC U]
  exact (fixed_mask_change (childCharacter η χ) Q m fixedBadMask (reducedNumerator C D U) z
    hm fixedBadMask_ne_zero (reducedNumerator_ne_zero C D hC U) hz hmLam hm2
    (dvd_mul_right _ _) (dvd_mul_left _ _)).trans
      (fixedInducingRow_transport η τ χ _ hτ Q z).symm

include hC hτ hm hmLam hm2 in
theorem actual_nonexceptional_iff    
         
     
         
        :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  grind [nonexceptional, actual_reduced_inducing_iff]

end

end SevenEighths.CenteredMomentSecondReducedPredicate



end OAI
