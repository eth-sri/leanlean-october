module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.CutoffGraphConvergence
public import DedekindZetaZeroFree.Eisenstein.Continuation.Spherical.HolomorphicSmoothSectionGluing

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAverageDomain
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry KPContActualSectorCutoffGraphLimit
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem graph_eigen_of_l2
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (Z : smoothSections F ζ hζ U R P H) (a : ℂ)
    (h2 : normIntegral F ζ hζ U R P H Z.val < ⊤) (he : localLaplacian Z = a • Z.val) :
    ∃ z : KPContSectorClosedLpSubspace.H F ζ hζ R U,
      KPContActualSmoothLineGluing.Represents F ζ hζ U R P H Z.val z ∧
      (z,a • z) ∈ (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H
        R.adelicHaar R.adelic_isHaar rfl realization).graph := by
  let B : BorelL2Sections F ζ hζ U R P H :=
    ⟨Z.val, ⟨fun i => (Z.property i).continuous.measurable, h2⟩⟩
  have hΔ : normIntegral F ζ hζ U R P H (localLaplacian Z) < ⊤ :=
    he ▸ ((BorelL2Sections F ζ hζ U R P H).smul_mem a B.property).2
  let W : GraphSection (U := U) (H := H) := ⟨Z, h2,
    squareFinite_gradient_of_laplacian F ζ hζ U R P H R.adelicHaar R.adelic_isHaar rfl
      realization Z h2 hΔ, hΔ⟩
  obtain ⟨hd, hdv⟩ := kp_cont_actual_sector_cutoff_graph_limit F ζ hζ
    R.adelicHaar R.adelic_isHaar U R rfl P H realization W
  have hl : laplacianClass W = a • sectionClass W := by
    unfold laplacianClass sectionClass
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    exact he
  refine ⟨sectionClass W, ?_, ?_⟩
  · exact ⟨representative_memLp F ζ hζ U R P H B, rfl⟩
  · have hg := (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H
        R.adelicHaar R.adelic_isHaar rfl realization).mem_graph ⟨sectionClass W, hd⟩
    simpa only [hdv, hl] using hg
end DedekindZetaZeroFree.FourierContinuation.ResidualAverageDomain

end
