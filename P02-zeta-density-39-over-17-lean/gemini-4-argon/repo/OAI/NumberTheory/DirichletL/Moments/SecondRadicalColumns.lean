module
public import OAI.NumberTheory.DirichletL.Moments.SecondRadicalFamily

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondRadicalColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondRadicalFamily CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion CenteredMomentCanonicalFirst

theorem sixthFactor_span_dvd_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣D := by
  conv_rhs => rw [←right_ideal_product C D hC hD hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hd := rightExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤rightExponent C D P := min_le_right _ _
  unfold fixedExponent
  split_ifs <;> omega

theorem residual_sixth_coefficient_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime D I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,ite_eq_left
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd_right C D hC hD hCD U)),mul_one]
