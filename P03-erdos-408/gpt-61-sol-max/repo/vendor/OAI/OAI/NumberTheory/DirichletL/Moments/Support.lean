module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

def supportExtract (I : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O))  :=
  ((normalizedFactors I).filter (fun P => P ∈ S)).prod

def supportResidual (I : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O))  :=
  ((normalizedFactors I).filter (fun P => P ∉ S)).prod

section
variable (I : Ideal ActualEisensteinCubic.O) (S : Finset (Ideal ActualEisensteinCubic.O))

theorem supportExtract_factors     :
    normalizedFactors (supportExtract I S) = (normalizedFactors I).filter (fun P => P ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_factors     :
    normalizedFactors (supportResidual I S) = (normalizedFactors I).filter (fun P => P ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportExtract_ne_zero     : supportExtract I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_ne_zero     : supportResidual I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem support_reconstruct  I  (hI : I ≠ 0)  S  :
    supportExtract I S * supportResidual I S = I := by
  rw [supportExtract, supportResidual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_support     :
    primeSupport (supportExtract I S) = primeSupport I ∩ S := by
  ext P
  simp [primeSupport, supportExtract_factors]

theorem supportResidual_support     :
    primeSupport (supportResidual I S) = primeSupport I \ S := by
  ext P
  simp [primeSupport, supportResidual_factors]

end

theorem supportExtract_count  I P   S  :
    (normalizedFactors (supportExtract I S)).count P =
      if P ∈ S then (normalizedFactors I).count P else 0 := by
  rw [supportExtract_factors, Multiset.count_filter]

theorem supportExtract_supported  I  (hI : Supported I)  S  :
    Supported (supportExtract I S) := by
  refine ⟨supportExtract_ne_zero I S, ?_⟩
  intro P hP
  rw [supportExtract_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

theorem supportResidual_supported  I  (hI : Supported I)  S  :
    Supported (supportResidual I S) := by
  refine ⟨supportResidual_ne_zero I S, ?_⟩
  intro P hP
  rw [supportResidual_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

section
variable (I J : Ideal ActualEisensteinCubic.O)

theorem extracted_residual_coprime    S  :
    IsCoprime (supportExtract I S) (supportResidual J S) := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportExtract_ne_zero I S) (supportResidual_ne_zero J S)).mp
  rw [supportExtract_support, supportResidual_support]
  exact Finset.disjoint_left.mpr (by
    simp_all)

theorem common_support_residual_coprime   :
    let S := primeSupport I ∩ primeSupport J
    IsCoprime (supportResidual I S) (supportResidual J S) := by
  dsimp only
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportResidual_ne_zero I _) (supportResidual_ne_zero J _)).mp
  rw [supportResidual_support, supportResidual_support]
  apply Finset.disjoint_left.mpr
  simp_all

theorem supportExtract_mul   (hI : I ≠ 0) (hJ : J ≠ 0)
     S  :
    supportExtract (I * J) S = supportExtract I S * supportExtract J S := by
  simp_all [supportExtract]

theorem supportResidual_mul   (hI : I ≠ 0) (hJ : J ≠ 0)
     S  :
    supportResidual (I * J) S = supportResidual I S * supportResidual J S := by
  simp_all [supportResidual]

end

theorem supportExtract_prime  P  (hP : Prime P)  S  :
    supportExtract P S = if P ∈ S then P else 1 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal ActualEisensteinCubic.O)))
      (by simp_all))
  simp only [supportExtract, hf, Multiset.filter_singleton]
  split_ifs <;> simp

section
variable {ι : Type*} (T : Finset ι) (p : ι → Ideal ActualEisensteinCubic.O)

theorem supportExtract_prod      
    (hp : ∀ i ∈ T, p i ≠ 0)  S  :
    supportExtract (∏ i ∈ T, p i) S = ∏ i ∈ T, supportExtract (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportExtract, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportExtract_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

theorem supportResidual_prod      
    (hp : ∀ i ∈ T, p i ≠ 0)  S  :
    supportResidual (∏ i ∈ T, p i) S = ∏ i ∈ T, supportResidual (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportResidual, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportResidual_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

end

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

def idealCorrelation (I J ) (hI : Supported I) (hJ : Supported J) (j : ActualEisensteinCubic.O)  :=
  actualCorrelation (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) j

end SevenEighths.CenteredMomentSupport
end

end OAI
