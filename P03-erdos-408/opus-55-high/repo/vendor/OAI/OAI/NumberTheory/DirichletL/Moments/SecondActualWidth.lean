module

public import OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget
public import OAI.NumberTheory.DirichletL.Moments.SectorLocalization

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondActualWidth
open CanonicalQuadraticSieve
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalLedger
open CenteredMomentSectorLocalization CenteredMomentDescentLedger
open CenteredMomentPartitionNorm

theorem actual_common_log_ge_unit (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)≤Real.logb Z (normValue (commonFrequencyGenerator C D)) := by
  have hh:=common_log_ge_unit (commonPrime C D) (commonPrime_supported C D hC)
    (leftExponent C D) (rightExponent C D) (leftExponent_pos C D) (rightExponent_pos C D) U Z hZ
  rw [←commonFrequencyGenerator_span C D hC] at hh
  simpa only [unitIdeal,commonPrime_span C D hC,normValue] using hh

end SevenEighths.CenteredMomentSecondActualWidth

end

end OAI
