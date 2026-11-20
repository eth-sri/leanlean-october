module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Cusps.LevelCompatibleAngularMeasures
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineL2.LineNormDisintegration

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

open _root_.DedekindZetaZeroFree.KPMsFixedHaar (angular_measurable kernel_angular_lintegral angular_marginal_of_disintegration cross_section_inclusion_measurable weighted_section_measure)

namespace DedekindZetaZeroFree.KPMsActualNativeWeightedShapeMeasure

open KPMsFixedHaarDisintegration
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : SphericalTransport F ζ hζ}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

theorem angularProjection_measurable : Measurable (angularProjection A) :=
  angular_measurable A

section

variable (D : Disintegration A R P)

def actualKernel : KPMsFixedHaar.FiberKernel A where
  unipotent := D.unipotent
  probability_unipotent := D.probability_unipotent
  fiber_support := D.fiber_support
  measurable_kernel := D.measurable_kernel
  fiber_formula := D.fiber_formula

theorem kernel_angular (ω : Omega A)
    (f : Omega A → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (angularProjection A x) ∂D.unipotent ω) = f ω :=
  kernel_angular_lintegral A (actualKernel A D) ω f hf

abbrev sectionMeasure : Measure (CrossSection A) :=
  KPMsFixedHaar.WeightedSectionGlobalization.weightedSectionMeasure A D.componentWeight

theorem section_shape_measure :
    Measure.map (angularProjection A) (sectionMeasure A D) = D.beta :=
  angular_marginal_of_disintegration A (actualKernel A D) D.componentWeight D.beta
    D.section_disintegration

theorem offset_section_shape_measure
    (density : Omega A → ℝ≥0∞) (hdensity : Measurable density) :
    Measure.map (angularProjection A)
      ((sectionMeasure A D).withDensity (density ∘ angularProjection A)) =
        D.beta.withDensity density := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (angularProjection_measurable A)]
  change (∫⁻ x, (f ∘ angularProjection A) x
    ∂(sectionMeasure A D).withDensity (density ∘ angularProjection A)) = _
  rw [lintegral_withDensity_eq_lintegral_mul (sectionMeasure A D)
      (hdensity.comp (angularProjection_measurable A)) (hf.comp (angularProjection_measurable A)),
    lintegral_withDensity_eq_lintegral_mul D.beta hdensity hf]
  have hmap := congrArg (fun μ : Measure (Omega A) => ∫⁻ ω, density ω * f ω ∂μ)
    (section_shape_measure A D)
  change (∫⁻ ω, (density * f) ω ∂Measure.map (angularProjection A) (sectionMeasure A D)) = _ at hmap
  rw [lintegral_map (hdensity.mul hf) (angularProjection_measurable A)] at hmap
  exact hmap

end

theorem spherical_shell_shape_measure (D : Disintegration A R P) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y) :
    ∃ s : KPMsFixedHaarDisintegration.Spherical F ζ hζ U →
        KPMsFixedHaarDisintegration.Omega A,
      Measurable s ∧
      (∀ x r, s (D.chart Y hY (x,r)) =
        KPMsFixedHaarDisintegration.angularProjection _ x) := by
  let DD := D
  let AA := A
  let E := {v | Y < DD.modulus v ∧ DD.modulus v ≤ 2 * Y}
  have hE : MeasurableSet E :=
    (measurableSet_lt measurable_const DD.measurable_modulus).inter
      (measurableSet_le DD.measurable_modulus measurable_const)
  have he : MeasurableSet (KPMsFixedHaarDisintegration.cuspEnds AA Y) := by
    apply IsOpen.measurableSet
    apply isOpen_iUnion
    intro j
    have hm : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U
        (AA.representative j.1)) := by
      have heq : KPFiniteCuspAtlas.componentMap F ζ hζ U
          (AA.representative j.1) = AA.components ∘ Sigma.mk j.1 := by
        funext x
        exact (AA.components_formula j.1 x).symm
      rw [heq]
      exact AA.components.isOpenMap.comp isOpenMap_sigmaMk
    exact hm _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ _)
  letI : Nonempty (KPMsFixedHaarDisintegration.CrossSection AA) := by
    let i : Fin AA.componentCount := ⟨0, AA.positive_componentCount⟩
    let j : KPMsFixedHaarDisintegration.CuspIndex AA :=
      ⟨i, ⟨0, (AA.cuspAtlas i).positive_cuspCount⟩⟩
    exact ⟨⟨j, Quotient.mk _ (0 : KPCuspCharts.Cross F)⟩⟩
  letI : Nonempty (Set.Ioi Y) := ⟨⟨Y + 1, by simp⟩⟩
  let emb := (DD.chart_embedding Y hY).measurableEmbedding (DD.chart_range Y hY ▸ he)
  let s := KPMsFixedHaarDisintegration.angularProjection AA ∘ Prod.fst ∘ emb.invFun
  have hs : Measurable s := (angularProjection_measurable A).comp
    (measurable_fst.comp emb.measurable_invFun)
  have hsc : ∀ x r, s (DD.chart Y hY (x,r)) =
      KPMsFixedHaarDisintegration.angularProjection AA x := by
    intro x r
    simp only [s, Function.comp_apply, emb.leftInverse_invFun (x,r)]
  refine ⟨s, hs, hsc⟩

theorem cuspDensity_measurable (c : CuspIndex A → ℝ≥0∞) :
    Measurable (fun ω : Omega A => c ω.1) := by
  have hc : Continuous (fun ω : Omega A => c ω.1) := continuous_sigma (σ := fun j : CuspIndex A =>
      KPCuspCharts.Base F hF (Parabolic A j).E (Parabolic A j).integralUnits)
      (fun j => (continuous_const (X := KPCuspCharts.Base F hF
        (Parabolic A j).E (Parabolic A j).integralUnits) (y := c j)))
  exact hc.measurable

section

variable (D : Disintegration A R P) (c : CuspIndex A → ℝ≥0∞)

def cuspWeightedSection :
    Measure (CrossSection A) :=
  ∑ j : CuspIndex A,
    (c j * (D.componentWeight j.1 /
      ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ)))) •
      Measure.map (fun x => (⟨j,x⟩ : CrossSection A)) (Geometry A j).sectionMeasure

theorem cuspWeightedSection_eq_withDensity :
    cuspWeightedSection A D c = (sectionMeasure A D).withDensity
      (fun x => c (angularProjection A x).1) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hc : Measurable (fun x : CrossSection A => c (angularProjection A x).1) :=
    (cuspDensity_measurable A c).comp (angularProjection_measurable A)
  rw [lintegral_withDensity_eq_lintegral_mul (sectionMeasure A D) hc hf]
  simp only [cuspWeightedSection, sectionMeasure,
    KPMsFixedHaar.WeightedSectionGlobalization.weightedSectionMeasure,
    weighted_section_measure, lintegral_finsetSum_measure, lintegral_smul_measure]
  apply Finset.sum_congr rfl
  intro j _
  rw [lintegral_map hf (cross_section_inclusion_measurable A j),
    lintegral_map (hc.mul hf) (cross_section_inclusion_measurable A j)]
  change (c j * (D.componentWeight j.1 / ENNReal.ofReal
    (2 * (KPCuspLogShape.dimension F : ℝ)))) * (∫⁻ x, f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure) =
    (D.componentWeight j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
      (∫⁻ x, c j * f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure)
  have hfj := hf.comp (cross_section_inclusion_measurable A j)
  change Measurable (fun x => f (⟨j,x⟩ : CrossSection A)) at hfj
  rw [lintegral_const_mul (c j) hfj]
  ring

theorem cusp_section_shape_measure :
    Measure.map (angularProjection A) (cuspWeightedSection A D c) =
      D.beta.withDensity (fun ω => c ω.1) := by
  rw [cuspWeightedSection_eq_withDensity A D c]
  exact offset_section_shape_measure A D (fun ω => c ω.1) (cuspDensity_measurable A c)

end

variable (D : Disintegration A R P) (Y : ℝ)

def sphericalShell : Set (Spherical F ζ hζ U) :=
  cuspEnds A Y ∩ {v | Y < D.modulus v ∧ D.modulus v ≤ 2 * Y}

theorem sphericalShell_measurable :
    MeasurableSet (sphericalShell A D Y) := by
  apply MeasurableSet.inter
  · apply IsOpen.measurableSet
    apply isOpen_iUnion
    intro j
    have hm : IsOpenMap (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)) := by
      have heq : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) =
          A.components ∘ Sigma.mk j.1 := by
        funext x
        exact (A.components_formula j.1 x).symm
      rw [heq]
      exact A.components.isOpenMap.comp isOpenMap_sigmaMk
    exact hm _ (KPFiniteAdelicCuspEnds.component_open_end F _ _ _)
  · exact (measurableSet_lt measurable_const D.measurable_modulus).inter
      (measurableSet_le D.measurable_modulus measurable_const)

end DedekindZetaZeroFree.KPMsActualNativeWeightedShapeMeasure

end
