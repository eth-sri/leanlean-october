module

public import DedekindZetaZeroFree.Adeles.Quotients.GroupCharts.TubeMeasureComparison
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.GroupCharts.AEL2TubeTransfer
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
open MeasureTheory Topology
open scoped Classical NumberField ENNReal
namespace DedekindZetaZeroFree.FourierContinuation.ResidualOutputSobolev
open KPContActualSphericalRightFieldIdentification KPMsGreenFlux KPGroupChartFullTubeHaarL2
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
theorem exists_original_chart_l2_bound
    (chart : GroupChart F ζ hζ U R P H)
    (A : Set (KPContLocalNorm.Space (groupDimension F)))
    (hA : IsCompact A) (hAT : A ⊆ chart.T.carrier) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : KPSmoothLocalQuotientCharts.X F ζ hζ → ℂ,
      MemLp f 2 R.quotientHaar →
      (∀ (v : U.toOpenSubgroup) (g : Cover F ζ hζ),
        f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (g * v.val.val)) =
        f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) →
      MemLp (fun x => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (chart.groupLift x))) 2 (volume.restrict A) ∧
      lpNorm (fun x => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (chart.groupLift x))) 2 (volume.restrict A) ≤ C * lpNorm f 2 R.quotientHaar := by
  obtain ⟨μArch, ν, D, hμArch, hν, hprod, hmass, hmassT, hD, hdom⟩ :=
    group_chart_full_tube_haar_domination chart A hA hAT
  let V := U.toOpenSubgroup
  let μ : Measure (KPContLocalNorm.Space (groupDimension F)) := volume.restrict A
  let σ := ν.restrict V
  haveI : SFinite μ := inferInstance
  haveI : IsFiniteMeasure σ := isFiniteMeasure_restrict.mpr hmassT.ne
  have hσ : σ Set.univ ≠ 0 := by
    simpa only [σ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, V] using hmass.ne'
  have hc : ContinuousOn chart.groupLift chart.T.carrier := by
    obtain ⟨E, he, hi⟩ := chart.inverse_smooth
    have hmaps : Set.MapsTo (groupCoordinates F) chart.T.carrier E.source := by
      intro x hx
      rw [he]
      exact chart.closure_source ⟨x, subset_closure hx, rfl⟩
    letI : IsTopologicalGroup (Cover F ζ hζ) :=
      (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
    convert ((((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1).continuousOn.comp (E.continuousOn.comp (groupCoordinates F).continuous.continuousOn hmaps)
      (fun x hx => Set.mem_univ _)).mul_const chart.finiteRepresentative) using 1
    funext x
    rw [GroupChart.groupLift, ← he]
    rfl
  have htube : AEMeasurable (chartTube chart) (μ.prod σ) := by
    letI : IsTopologicalGroup (Cover F ζ hζ) :=
      (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
    have hcont : ContinuousOn (chartTube chart) (A ×ˢ V) := by
      exact continuous_quotient_mk'.continuousOn.comp (((hc.mono hAT).comp continuousOn_fst (fun x hx => hx.1)).mul (continuous_subtype_val.continuousOn.comp continuousOn_snd (fun x hx => Set.mem_univ _))) (fun x hx => Set.mem_univ _)
    have hae : ∀ᵐ p ∂μ.prod σ, p ∈ A ×ˢ V := by
      exact ((Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem hA.measurableSet)).and ((Measure.quasiMeasurePreserving_snd).ae
        (ae_restrict_mem U.toOpenSubgroup.isOpen.measurableSet))
    have hm := hcont.aemeasurable (μ := μ.prod σ)
      (hA.measurableSet.prod U.toOpenSubgroup.isOpen.measurableSet)
    rw [Measure.restrict_eq_self_of_ae_mem hae] at hm
    exact hm
  obtain ⟨C, hC, hbound⟩ := exists_full_tube_l2_transfer_constant_ae μ σ R.quotientHaar
    (chartTube chart) htube ENNReal.ofReal_ne_top hdom hσ
  refine ⟨C,hC,?_⟩
  intro f hf hlevel
  apply hbound f hf (fun x => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
    (chart.groupLift x)))
  have hae : ∀ᵐ p ∂μ.prod σ, p ∈ A ×ˢ V := by
    exact ((Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem hA.measurableSet)).and ((Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem U.toOpenSubgroup.isOpen.measurableSet))
  filter_upwards [hae] with p hp
  exact hlevel ⟨p.2,hp.2⟩ (chart.groupLift p.1)
end DedekindZetaZeroFree.FourierContinuation.ResidualOutputSobolev

end
