module
public import OAI.NumberTheory.DirichletL.Moments.SecondRadicalFamily
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondRadicalColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentSecondSixthSource CenteredMomentSecondRadicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

section
variable (C D : Ideal O) (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
include C D hC hD hCD U
theorem sixthFactor_span_dvd_right :
    Ideal.span {sixthFactor C D U}∣D := by
  conv_rhs => rw [←right_ideal_product C D hC hD hCD]
  pm_6455
  have hd := rightExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤ rightExponent C D P := min_le_right _ _
  unfold fixedExponent
  grind

theorem residual_sixth_coefficient_right
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime D I) :
    idealRowHom (commonFrequencyGenerator C D *nonunitFrequencyGenerator C D U) I =
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,ite_eq_left
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd_right C D hC hD hCD U)),mul_one]
end

end SevenEighths.CenteredMomentSecondRadicalColumns

end

end OAI
