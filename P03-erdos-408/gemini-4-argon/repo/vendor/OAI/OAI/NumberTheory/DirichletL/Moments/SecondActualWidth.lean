module

public import OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget
public import OAI.NumberTheory.DirichletL.Moments.SectorLocalization

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondActualWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondRadicalBudget CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentSupport CenteredMomentDescentLedger
open CenteredMomentPartitionNorm CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem actual_common_log_ge_unit (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)≤Real.logb Z (normValue (commonFrequencyGenerator C D)) := by
  have hh:=common_log_ge_unit (commonPrime C D) (commonPrime_supported C D hC)
    (leftExponent C D) (rightExponent C D) (leftExponent_pos C D) (rightExponent_pos C D) U Z hZ
  rw [←commonFrequencyGenerator_span C D hC] at hh
  simpa only [unitIdeal,commonPrime_span C D hC,normValue] using hh

end SevenEighths.CenteredMomentSecondActualWidth

end

end OAI
