module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedJacquetImage

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ENNReal
open MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P₀ : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C₀ : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P₀)
variable (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))




def complexIntegrand (s : ℂ) (x : ℂ) : ℂ :=
  KPComplexIntertwinerParameterMajorant.forwardSection s
    KPComplexStandardIntertwinerGerm.compactSpherical
      (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent x * 1)

def archCylinder (s : ℂ) (a : NumberField.InfiniteAdeleRing F) : ℂ :=
  TateTensorProfile.archTensor F (fun _ => complexIntegrand s)
    (PoissonArch.infiniteAdeleToSpace F a)

include ζ hζ in

theorem arch_cylinder_integral (s : ℂ) :
    (∫ a, archCylinder F s a ∂KPAdditiveHaar.archMeasure F) =
      ∏ w : {w : NumberField.InfinitePlace F // w.IsComplex},
        ∫ x : ℂ, complexIntegrand s x ∂((2 : ℝ≥0∞) • KPCplxCharacterHaar.euclideanArea) := by
  letI := primitive12_totallyComplex F ζ hζ
  have he : MeasurableEmbedding ((PoissonArch.infiniteAdeleToSpace F).symm :
      PoissonArch.Space F → NumberField.InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).symm.toHomeomorph.measurableEmbedding
  rw [KPAdditiveHaar.archMeasure, he.integral_map]
  simp only [archCylinder, ContinuousLinearEquiv.apply_symm_apply]
  rw [TateTensorProfile.archTensor_integral]
  simp only [integral_smul_measure, ENNReal.toReal_ofNat, RCLike.real_smul_eq_coe_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  simp [PoissonArch.haarScalar, NumberField.InfinitePlace.nrComplexPlaces]

def adelicBox : Set (A F) :=
  {a | a.2 ∈ Set.range (KPAdditiveHaar.chartMap F E)}

 theorem finite_measure_sigmaFinite : SigmaFinite (KPAdditiveHaar.finiteMeasure F) := by
  letI := KPAdditiveHaar.finiteMeasure_isAddHaarMeasure F
  infer_instance

 theorem arch_measure_sigmaFinite : SigmaFinite (KPAdditiveHaar.archMeasure F) := by
  letI := KPAdditiveHaar.archMeasure_isAddHaarMeasure F
  letI : SecondCountableTopology (NumberField.InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.secondCountableTopology
  infer_instance

 theorem adelic_measure_box :
    (KPAdditiveHaar.adelicMeasure F).restrict (adelicBox F E) =
      @Measure.map (NumberField.InfiniteAdeleRing F ×
        IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (A F) inferInstance inferInstance
        (fun a => a)
        ((KPAdditiveHaar.archMeasure F).prod
          ((KPAdditiveHaar.finiteMeasure F).restrict (Set.range (KPAdditiveHaar.chartMap F E)))) := by
  letI := finite_measure_sigmaFinite F
  letI := arch_measure_sigmaFinite F
  let e : (NumberField.InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ≃ₜ A F := Homeomorph.refl _
  have he : @MeasurableEmbedding (NumberField.InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (A F) inferInstance inferInstance
      (fun a => a) := e.measurableEmbedding
  rw [KPAdditiveHaar.adelicMeasure, he.restrict_map]
  have hpre : (fun a : NumberField.InfiniteAdeleRing F ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 F) F => (a : A F)) ⁻¹' adelicBox F E =
      Set.univ ×ˢ Set.range (KPAdditiveHaar.chartMap F E) := by
    ext a
    exact (and_iff_right (Set.mem_univ a.1)).symm
  rw [hpre, ← Measure.prod_restrict, Measure.restrict_univ]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.TraceBox

end
