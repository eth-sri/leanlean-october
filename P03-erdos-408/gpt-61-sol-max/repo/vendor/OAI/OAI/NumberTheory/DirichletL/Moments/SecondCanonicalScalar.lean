module

public import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
public import OAI.NumberTheory.DirichletL.Moments.SectorLocalization

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalScalar
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSectorLocalization CenteredMomentSupport


def normalizer (C D ) (U : Finset (CommonIndex C D))  :=
  partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U

theorem normalizer_pos  C D  (hC : Supported C)  U  :
    0<normalizer C D U := by
  rw [normalizer,partitionNormalizer_eq_norm_ratio _ (commonPrime_supported C D hC) _ _
    (leftExponent_pos C D) (rightExponent_pos C D)]
  exact div_pos (commonIdeal_norm_pos _ (commonPrime_supported C D hC) _ _)
    (unitIdeal_norm_pos _ (commonPrime_supported C D hC) _)

def retainedScalar (C D ) (U : Finset (CommonIndex C D)) (R : ℝ) (h : ActualEisensteinCubic.O)  :=
  canonicalPartitionScalar C D U (nonunitFrequencyGenerator C D U*h)*
    (retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)):ℂ)

theorem actual_retained_scalar_norm  C D   hC   hD 
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
     U   R   h  :
    ‖retainedScalar C D U R h*idealCorrelation C D hC hD
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)‖≤1 := by
  have hs := actual_ideal_partition_scalar C D hC hD hCD U (nonunitFrequencyGenerator C D U*h)
  have hw := retainedWeight_bounds R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))
  rw [retainedScalar,mul_right_comm,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.1]
  exact (mul_le_of_le_one_left hw.1 (by simpa only [mul_assoc] using hs)).trans hw.2

end SevenEighths.CenteredMomentSecondCanonicalScalar

end

end OAI
