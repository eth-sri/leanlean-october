module

public import OAI.NumberTheory.DirichletL.Moments.CommonSectors
public import OAI.NumberTheory.DirichletL.Moments.HeckeExpansion

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentCommonAllocation
open CenteredMomentSupport CenteredMomentCommonSectors
open IdealMobiusDivisorSum

theorem extract_coprime_product (C a : Ideal ActualEisensteinCubic.O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportExtract (C*a) (primeSupport C)=C := by
  rw [supportExtract_mul C a hC ha,
    supportExtract_of_subset C hC _ (Finset.Subset.refl _),
    supportExtract_of_disjoint a _ ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa).symm,
    mul_one]

theorem residual_coprime_product (C a : Ideal ActualEisensteinCubic.O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) : supportResidual (C*a) (primeSupport C)=a := by
  apply mul_left_cancel₀ hC
  have he := support_reconstruct (C*a) (by positivity) (primeSupport C)
  rwa [extract_coprime_product C a hC ha hCa] at he

theorem tuple_products {ι : Type*} [Fintype ι] (v : ι → Ideal ActualEisensteinCubic.O) (C a : Ideal ActualEisensteinCubic.O)
    (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hv : ∏ i,v i=C*a) :
    (∏ i,supportExtract (v i) (primeSupport C))=C ∧
      (∏ i,supportResidual (v i) (primeSupport C))=a := by
  have hv0 := hv.symm ▸ mul_ne_zero hC ha
  have hi (i : ι) : v i≠0 := Finset.prod_ne_zero_iff.mp hv0 i (Finset.mem_univ _)
  constructor
  · rw [← supportExtract_prod Finset.univ v (by grind),hv]
    exact extract_coprime_product C a hC ha hCa
  · rw [← supportResidual_prod Finset.univ v (by grind),hv]
    exact residual_coprime_product C a hC ha hCa

theorem residual_factor_coprime (C I : Ideal ActualEisensteinCubic.O) (hC : C≠0) :
    IsCoprime C (supportResidual I (primeSupport C)) := by
  have hh := extracted_residual_coprime C I (primeSupport C)
  rwa [supportExtract_of_subset C hC _ (Finset.Subset.refl _)] at hh

end SevenEighths.CenteredMomentCommonAllocation

end

end OAI
