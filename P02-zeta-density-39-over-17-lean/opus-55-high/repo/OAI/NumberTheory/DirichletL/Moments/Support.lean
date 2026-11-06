module
public import OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

def supportExtract (I : Ideal O) (S : Finset (Ideal O)) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P ∈ S)).prod

def supportResidual (I : Ideal O) (S : Finset (Ideal O)) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P ∉ S)).prod

section
variable (I : Ideal O) (S : Finset (Ideal O))
include I S
theorem supportExtract_factors :
    normalizedFactors (supportExtract I S) = (normalizedFactors I).filter (fun P => P ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_factors :
    normalizedFactors (supportResidual I S) = (normalizedFactors I).filter (fun P => P ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportExtract_ne_zero : supportExtract I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_ne_zero : supportResidual I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)
end

section
variable (I : Ideal O)
include I
theorem support_reconstruct (hI : I ≠ 0) (S : Finset (Ideal O)) :
    supportExtract I S * supportResidual I S = I := by
  rw [supportExtract, supportResidual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_support (S : Finset (Ideal O)) :
    primeSupport (supportExtract I S) = primeSupport I ∩ S := by
  ext P
  simp [primeSupport, supportExtract_factors]

theorem supportResidual_support (S : Finset (Ideal O)) :
    primeSupport (supportResidual I S) = primeSupport I \ S := by
  ext P
  simp [primeSupport, supportResidual_factors]
end

theorem supportExtract_count (I P : Ideal O) (S : Finset (Ideal O)) :
    (normalizedFactors (supportExtract I S)).count P =
      if P ∈ S then (normalizedFactors I).count P else 0 := by
  rw [supportExtract_factors, Multiset.count_filter]

section
variable (I : Ideal O) (hI : Supported I) (S : Finset (Ideal O))
include I hI S
theorem supportExtract_supported :
    Supported (supportExtract I S) := by
  pm_6360 supportExtract_ne_zero supportExtract_factors

theorem supportResidual_supported :
    Supported (supportResidual I S) := by
  pm_6360 supportResidual_ne_zero supportResidual_factors
end

section
variable (I J : Ideal O)
include I J
theorem extracted_residual_coprime (S : Finset (Ideal O)) :
    IsCoprime (supportExtract I S) (supportResidual J S) := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportExtract_ne_zero I S) (supportResidual_ne_zero J S)).mp
  rw [supportExtract_support, supportResidual_support]
  exact Finset.disjoint_left.mpr (by grind)

theorem common_support_residual_coprime :
    let S := primeSupport I ∩ primeSupport J
    IsCoprime (supportResidual I S) (supportResidual J S) := by
  dsimp only
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportResidual_ne_zero I _) (supportResidual_ne_zero J _)).mp
  rw [supportResidual_support, supportResidual_support]
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  grind

theorem supportExtract_mul (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportExtract (I * J) S = supportExtract I S * supportExtract J S := by
  pm_8553 supportExtract

theorem supportResidual_mul (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportResidual (I * J) S = supportResidual I S * supportResidual J S := by
  pm_8553 supportResidual
end

theorem supportExtract_prime (P : Ideal O) (hP : Prime P) (S : Finset (Ideal O)) :
    supportExtract P S = if P ∈ S then P else 1 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP))
  simp only [supportExtract, hf, Multiset.filter_singleton]
  split_ifs <;> simp

section
variable {ι : Type*} (T : Finset ι) (p : ι → Ideal O) (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal O))
include ι T p hp S
theorem supportExtract_prod :
    supportExtract (∏ i ∈ T, p i) S = ∏ i ∈ T, supportExtract (p i) S := by pm_2891 supportExtract supportExtract_mul

theorem supportResidual_prod :
    supportResidual (∏ i ∈ T, p i) S = ∏ i ∈ T, supportResidual (p i) S := by pm_2891 supportResidual supportResidual_mul
end

open CompletedGauss hiding primeSupport
open CenteredMomentSupportedCorrelation

def idealCorrelation (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (j : O) : ℂ :=
  actualCorrelation (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) j

end SevenEighths.CenteredMomentSupport
end

end OAI
