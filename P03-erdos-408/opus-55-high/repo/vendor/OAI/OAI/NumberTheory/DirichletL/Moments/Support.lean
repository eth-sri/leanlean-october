module

public import OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

def supportExtract (I : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O)) : Ideal ActualEisensteinCubic.O :=
  ((normalizedFactors I).filter (fun P => P ∈ S)).prod

def supportResidual (I : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O)) : Ideal ActualEisensteinCubic.O :=
  ((normalizedFactors I).filter (fun P => P ∉ S)).prod

theorem supportExtract_factors (I : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    normalizedFactors (supportExtract I S) = (normalizedFactors I).filter (fun P => P ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_factors (I : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    normalizedFactors (supportResidual I S) = (normalizedFactors I).filter (fun P => P ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportExtract_ne_zero (I : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O)) : supportExtract I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_ne_zero (I : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O)) : supportResidual I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem support_reconstruct (I : Ideal ActualEisensteinCubic.O) (hI : I ≠ 0) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    supportExtract I S * supportResidual I S = I := by
  rw [supportExtract, supportResidual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_support (I : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    primeSupport (supportExtract I S) = primeSupport I ∩ S := by
  ext P
  simp [primeSupport, supportExtract_factors]

theorem supportResidual_support (I : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    primeSupport (supportResidual I S) = primeSupport I \ S := by
  ext P
  simp [primeSupport, supportResidual_factors]

theorem supportExtract_count (I P : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    (normalizedFactors (supportExtract I S)).count P =
      if P ∈ S then (normalizedFactors I).count P else 0 := by
  rw [supportExtract_factors, Multiset.count_filter]

theorem supportExtract_supported (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    Supported (supportExtract I S) := by
  refine ⟨supportExtract_ne_zero I S, ?_⟩
  intro P hP
  rw [supportExtract_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

theorem supportResidual_supported (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    Supported (supportResidual I S) := by
  refine ⟨supportResidual_ne_zero I S, ?_⟩
  intro P hP
  rw [supportResidual_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

theorem extracted_residual_coprime (I J : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    IsCoprime (supportExtract I S) (supportResidual J S) := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportExtract_ne_zero I S) (supportResidual_ne_zero J S)).mp
  rw [supportExtract_support, supportResidual_support]
  exact Finset.disjoint_left.mpr (by
    simp_all)

theorem common_support_residual_coprime (I J : Ideal ActualEisensteinCubic.O) :
    let S := primeSupport I ∩ primeSupport J
    IsCoprime (supportResidual I S) (supportResidual J S) := by
  dsimp only
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportResidual_ne_zero I _) (supportResidual_ne_zero J _)).mp
  rw [supportResidual_support, supportResidual_support]
  apply Finset.disjoint_left.mpr
  simp_all

theorem supportExtract_mul (I J : Ideal ActualEisensteinCubic.O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal ActualEisensteinCubic.O)) :
    supportExtract (I * J) S = supportExtract I S * supportExtract J S := by
  simp only [supportExtract, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportResidual_mul (I J : Ideal ActualEisensteinCubic.O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal ActualEisensteinCubic.O)) :
    supportResidual (I * J) S = supportResidual I S * supportResidual J S := by
  simp only [supportResidual, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportExtract_prime (P : Ideal ActualEisensteinCubic.O) (hP : Prime P) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    supportExtract P S = if P ∈ S then P else 1 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal ActualEisensteinCubic.O)))
      (by simp_all))
  simp only [supportExtract, hf, Multiset.filter_singleton]
  split_ifs <;> simp

theorem supportExtract_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal ActualEisensteinCubic.O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    supportExtract (∏ i ∈ T, p i) S = ∏ i ∈ T, supportExtract (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportExtract, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportExtract_mul _ _ (by grind)
        (Finset.prod_ne_zero_iff.mpr (by grind)) S,
      ih (by grind)]

theorem supportResidual_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal ActualEisensteinCubic.O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    supportResidual (∏ i ∈ T, p i) S = ∏ i ∈ T, supportResidual (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportResidual, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportResidual_mul _ _ (by grind)
        (Finset.prod_ne_zero_iff.mpr (by grind)) S,
      ih (by grind)]

open CompletedGauss hiding primeSupport
open CenteredMomentSupportedCorrelation

def idealCorrelation (I J : Ideal ActualEisensteinCubic.O) (hI : Supported I) (hJ : Supported J) (j : ActualEisensteinCubic.O) : ℂ :=
  actualCorrelation (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) j

end SevenEighths.CenteredMomentSupport
end

end OAI
