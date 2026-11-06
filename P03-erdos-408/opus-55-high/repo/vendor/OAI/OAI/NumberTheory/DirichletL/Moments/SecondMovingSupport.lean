module

public import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondMovingSupport
open CanonicalQuadraticSieve
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition
open CenteredMomentSupport CenteredMomentSupportedCorrelation CenteredMomentUnequal

theorem actual_unequal_min_six (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (w : ActualEisensteinCubic.O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (P : CommonIndex C D) (hneq : leftExponent C D P≠rightExponent C D P) :
    6∣min (leftExponent C D P) (rightExponent C D P) := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P];infer_instance
  have hglobal : actualCorrelation (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)
      (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      ((∏ P : CommonIndex C D,commonPrime C D P^min (leftExponent C D P) (rightExponent C D P))*w)≠0 := by
    simpa only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD,
      commonFrequencyGenerator,idealCorrelation] using hne
  have hl := local_nonzero_of_global (commonPrime C D) (commonPrime_supported C D hC)
    (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D) w hglobal P
  exact nonzero_unequal_min_six (commonPrime C D P) (commonPrime_supported C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_good C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_odd C D hC P)
    _ _ (leftExponent_pos C D P) (rightExponent_pos C D P) hneq _ hl

def fixedExponent (C D : Ideal ActualEisensteinCubic.O) (U : Finset (CommonIndex C D)) (P : CommonIndex C D) : ℕ :=
  min (leftExponent C D P) (rightExponent C D P)+if P∈nonunitPartitionSet C D U then 1 else 0

def fixedActiveSet (C D : Ideal ActualEisensteinCubic.O) (U : Finset (CommonIndex C D)) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P=>¬6∣fixedExponent C D U P)

theorem fixedActiveSet_subset (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : ActualEisensteinCubic.O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    fixedActiveSet C D U⊆U∪nonunitPartitionSet C D U := by
  intro P hP
  have ha := (Finset.mem_filter.mp hP).2
  by_contra hn
  have hU : P∉U := by grind
  have hV : P∉nonunitPartitionSet C D U := by grind
  have heq : ¬(leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P) := by
    intro he
    exact hV (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr (by grind),hU⟩)
  rw [fixedExponent,ite_eq_right hV,add_zero] at ha
  by_cases hc : leftExponent C D P=rightExponent C D P
  · omega
  · exact ha (actual_unequal_min_six C D hC hD hCD w hne P hc)

end SevenEighths.CenteredMomentSecondMovingSupport

end

end OAI
