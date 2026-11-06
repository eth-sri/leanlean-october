module

public import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalNonunit
public import OAI.NumberTheory.DirichletL.Moments.RankinLabels

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalLedger
open CanonicalQuadraticSieve CompletedGauss CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm CenteredMomentSupport CenteredMomentForcing
local notation "O" => ActualEisensteinCubic.O

theorem span_finset_product {ι : Type*} (S : Finset ι) (p : ι→O) :
    Ideal.span {∏ i∈S,p i}=∏ i∈S,Ideal.span {p i} := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => rw [Finset.prod_insert hi,Finset.prod_insert hi,
      ←Ideal.span_singleton_mul_span_singleton,ih]

theorem commonFrequencyGenerator_span (C D : Ideal O) (_hC : Supported C) :
    Ideal.span {commonFrequencyGenerator C D}=
      commonIdeal (commonPrime C D) (leftExponent C D) (rightExponent C D) := by
  simp only [commonFrequencyGenerator,span_finset_product,←Ideal.span_singleton_pow,commonIdeal]

theorem nonunitFrequencyGenerator_span (C D : Ideal O)
    (U : Finset (CommonIndex C D)) :
    Ideal.span {nonunitFrequencyGenerator C D U}=
      unitIdeal (commonPrime C D) (nonunitPartitionSet C D U) := by
  simp only [nonunitFrequencyGenerator,span_finset_product,unitIdeal]

theorem actual_partitionNormalizer (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) :
    partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U=
      (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/
        Ideal.absNorm (∏ P∈U,P.val) := by
  rw [partitionNormalizer_eq_norm_ratio _ (commonPrime_supported C D hC) _ _
    (leftExponent_pos C D) (rightExponent_pos C D),←commonFrequencyGenerator_span C D hC]
  simp only [unitIdeal,commonPrime_span C D hC]

theorem actual_second_ledger_lower (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O) (hpart : canonicalPartition C D U w)
    (Z : ℝ) (hZ : 1<Z)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    (Real.logb Z (Ideal.absNorm C:ℝ)+Real.logb Z (Ideal.absNorm D:ℝ))/3≤
      Real.logb Z (Ideal.absNorm C:ℝ)+Real.logb Z (Ideal.absNorm D:ℝ)-
      5*Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/6-
      Real.logb Z (Ideal.absNorm (∏ P : CommonIndex C D,P.val):ℝ)+
      Real.logb Z (Ideal.absNorm (∏ P∈U,P.val):ℝ)+
      Real.logb Z (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ)/6+
      Real.logb Z (Ideal.absNorm (forcingIdeal (fun P : CommonIndex C D=>P.val)
        (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ)/3 := by
  have hh := actual_ideal_secondSaving_lower C D hC hD hCD w Z hZ hne
  rw [secondSaving_eq_norm_ledger _ (commonPrime_supported C D hC)] at hh
  rw [left_ideal_product C D hC hCD,right_ideal_product C D hC hD hCD,
    ←commonFrequencyGenerator_span C D hC] at hh

  rw [hpart,←nonunitPartitionSet_eq_actual C D U w hpart,
    ←nonunitFrequencyGenerator_span C D U] at hh
  simpa only [unitIdeal,commonPrime_span C D hC,forcingIdeal] using hh

end SevenEighths.CenteredMomentSecondCanonicalLedger

end

end OAI
