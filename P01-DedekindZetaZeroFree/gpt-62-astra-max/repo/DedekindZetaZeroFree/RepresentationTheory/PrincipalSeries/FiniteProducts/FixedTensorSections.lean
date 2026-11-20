module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.FixedLevelSections
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteProducts.LocalFixedLevelSampling

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.NativeScalarFiniteFixedTensorSection
open _root_.DedekindZetaZeroFree.NativeScalarFiniteTensorEvaluation (Cover Fiber Source ProductCover ProductFiber ProductFunctions tensorEvaluation tensorEvaluation_covariant)
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductLocalFixedLevel (localFixedLevel tensorCosetSampling tensorCosetSampling_formula fixedTensorEvaluation_injective fixedTensorInclusion fixedTensorInclusion_comp)
open _root_.DedekindZetaZeroFree.NativeScalarFiniteProductFixedLevel (productFixedLevel compactCosetSampling compactCosetSampling_injective)
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (M : FourierContinuation.SourceReconstruction.InducingData F ζ hζ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

 variable (U : ∀ q : S, OpenSubgroup (Cover F ζ hζ S q))

theorem fixedTensorEvaluation_mem
    (x : PiTensorProduct ℂ (fun q => localFixedLevel F ζ hζ M S U q)) :
    tensorEvaluation F ζ hζ M S
      (PiTensorProduct.mapIncl (fun q => localFixedLevel F ζ hζ M S U q) x) ∈
      productFixedLevel F ζ hζ M S U := by
  refine ⟨tensorEvaluation_covariant F ζ hζ M S _, ?_⟩
  intro j hj g
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, PiTensorProduct.mapIncl, PiTensorProduct.map_tprod]
    change c • PiTensorProduct.map _ (PiTensorProduct.tprod ℂ _) =
      c • PiTensorProduct.map _ (PiTensorProduct.tprod ℂ _)
    simp only [PiTensorProduct.map_tprod]
    congr 1
    congr 1
    funext q
    exact (x q).property (j q) (hj q) (g q)
  | add x y hx hy =>
    simpa using congrArg₂ (· + ·) hx hy

 def fixedTensorSection :
    PiTensorProduct ℂ (fun q => localFixedLevel F ζ hζ M S U q) →ₗ[ℂ]
      productFixedLevel F ζ hζ M S U :=
  ((tensorEvaluation F ζ hζ M S).comp
    (PiTensorProduct.mapIncl (fun q => localFixedLevel F ζ hζ M S U q))).codRestrict
      (productFixedLevel F ζ hζ M S U) (fixedTensorEvaluation_mem F ζ hζ M S U)

private theorem fixedTensorSection_sampling :
    (compactCosetSampling F ζ hζ M S U).comp
      (fixedTensorSection F ζ hζ M S U) = tensorCosetSampling F ζ hζ M S U := by
  apply LinearMap.ext
  intro x
  funext c
  exact (tensorCosetSampling_formula F ζ hζ M S U x c).symm

 theorem fixedTensorSection_mem_range_iff
    (f : productFixedLevel F ζ hζ M S U) :
    f ∈ (fixedTensorSection F ζ hζ M S U).range ↔
      compactCosetSampling F ζ hζ M S U f ∈ (tensorCosetSampling F ζ hζ M S U).range := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    exact congrArg (fun A => A x) (fixedTensorSection_sampling F ζ hζ M S U).symm
  · rintro ⟨x, hx⟩
    refine ⟨x, compactCosetSampling_injective F ζ hζ M S U ?_⟩
    change ((compactCosetSampling F ζ hζ M S U).comp
      (fixedTensorSection F ζ hζ M S U)) x = _
    rw [fixedTensorSection_sampling]
    exact hx

end DedekindZetaZeroFree.NativeScalarFiniteFixedTensorSection

end
