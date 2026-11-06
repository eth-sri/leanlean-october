module

public import OAI.NumberTheory.DirichletL.Moments.SecondRadicalColumns
public import OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport
public import OAI.NumberTheory.DirichletL.Moments.FixedRowMask

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondReducedPredicate
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredExceptionalProfile CenteredMomentFixedRowMask CenteredMomentRestrictedEnergy
open CenteredMomentSecondFamilyTransport CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSixthReduction CenteredMomentCanonicalFirst RayFourExpansion

theorem fixed_mask_change (η : Character) (Q : Ideal ActualEisensteinCubic.O) (m n A z : ActualEisensteinCubic.O)
    (hm:m≠0) (hn:n≠0) (hA:A≠0) (hz:z≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:ActualEisensteinCubic.O)∣m)
    (hnLam:ConcretePrimeRowBridge.goodLambda∣n) (hn2:(2:ActualEisensteinCubic.O)∣n) :
    FixedInducingRow η Q m A z ↔ FixedInducingRow η Q n A z := by
  have h1:=fixedInducingRow_mul_mask_iff η Q m n A z hm hn hA hz hmLam hm2
  have h2:=fixedInducingRow_mul_mask_iff η Q n m A z hn hm hA hz hnLam hn2
  rw [mul_comm n m] at h2
  simp_all

theorem actual_reduced_inducing_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal ActualEisensteinCubic.O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:ActualEisensteinCubic.O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal ActualEisensteinCubic.O) (m z:ActualEisensteinCubic.O) (hm:m≠0) (hz:z≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:ActualEisensteinCubic.O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [fixed_sixth_inducing_iff _ Q m z hm hz hmLam hm2 C D hC U]
  exact (fixed_mask_change (childCharacter η χ) Q m fixedBadMask (reducedNumerator C D U) z
    hm fixedBadMask_ne_zero (reducedNumerator_ne_zero C D hC U) hz hmLam hm2
    (dvd_mul_right _ _) (dvd_mul_left _ _)).trans
      (fixedInducingRow_transport η τ χ _ hτ Q z).symm

theorem actual_nonexceptional_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal ActualEisensteinCubic.O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:ActualEisensteinCubic.O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal ActualEisensteinCubic.O) (m z:ActualEisensteinCubic.O) (hm:m≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:ActualEisensteinCubic.O)∣m) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  unfold nonexceptional
  by_cases hz:z=0
  · simp_all
  · rw [actual_reduced_inducing_iff η τ χ C D hC U hτ Q m z hm hz hmLam hm2]

end SevenEighths.CenteredMomentSecondReducedPredicate

end

end OAI
