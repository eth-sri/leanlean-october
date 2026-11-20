module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.CoveredLifts
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.SharpTruncation.CuspFramesAndIntrinsicTruncation
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.SharpTruncation.FrameSpectralEquations
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicQuotients.CompactCoreAndFiniteVolume
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.QuotientFlows.WeakDivergence

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.IntrinsicFrameSpectral (finitePart_eq_chart)
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient (finite_projection)
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames (finiteSubgroup_eq)
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem intrinsic_level
    (f : Cover F ζ hζ → ℂ) (ha : AutomorphicAtLevel (U := U) f)
    (f₀ : X F ζ hζ → ℂ) (hp : IntrinsicAveraging.pullback f₀ = f) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ g (b : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
        f₀ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (g * b.val)) =
          f₀ (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  have hfin : KPGlobalTorusFunctionData.finitePart F ζ hζ =
      KPFiniteCuspAtlas.FiniteCover F ζ hζ :=
    (finitePart_eq_chart (F := F) (ζ := ζ) (hζ := hζ)).trans finiteSubgroup_eq
  let e := MulEquiv.subgroupCongr hfin
  let J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨U.toOpenSubgroup.comap e.toMonoidHom (continuous_subtype_val.subtype_mk _),
      (Homeomorph.setCongr (congrArg (fun H : Subgroup (Cover F ζ hζ) =>
        (H : Set (Cover F ζ hζ))) hfin)).isCompact_preimage.mpr U.isCompact⟩
  refine ⟨J, ?_⟩
  intro g b
  obtain ⟨a,ha',hab⟩ := b.property
  have hab' := hab
  change IntrinsicAveraging.pullback f₀ (g * b.val) = IntrinsicAveraging.pullback f₀ g
  rw [hp, ← hab']
  exact ha.right_level ⟨e a,ha'⟩ g

 theorem normalRadial_finite_right
    (c g : Cover F ζ hζ) (b : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    NormalCoefficient.normalRadial c (g * b.val) =
      NormalCoefficient.normalRadial c g := by
  simp only [NormalCoefficient.normalRadial, mul_assoc, map_mul, finite_projection, mul_one]

 theorem continuous_core_integrable
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (f : X F ζ hζ → ℂ) (hc : Continuous f) :
    IntegrableOn f (quotientCore A P Y) R.quotientHaar := by
  let : BorelSpace (X F ζ hζ) := ⟨rfl⟩
  obtain ⟨hk,hm,hfin⟩ := TruncatedL2Geometry.quotientCore_compact_measurable_finite A R P Y hY
  let : IsFiniteMeasure (R.quotientHaar.restrict (quotientCore A P Y)) :=
    ⟨by simpa using hfin⟩
  obtain ⟨C,hC⟩ := hk.bddAbove_image hc.norm.continuousOn
  apply memLp_one_iff_integrable.mp
  apply MemLp.of_bound hc.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hm] with x hx
  exact hC ⟨x,hx,rfl⟩

end DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes

end
