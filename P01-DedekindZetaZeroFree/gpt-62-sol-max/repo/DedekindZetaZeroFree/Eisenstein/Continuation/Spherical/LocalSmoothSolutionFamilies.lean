module

public import DedekindZetaZeroFree.Analysis.Elliptic.WeightedSmoothRepresentatives
public import DedekindZetaZeroFree.Analysis.Elliptic.WeightedSolutionJetContinuity
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.WeakChartEquations
public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothResolventHolomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualLocalSolutionFamily

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorScalarLineAlgebra KPContSectorSmoothFramesSupport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

set_option maxHeartbeats 1000000 in

structure Promotion (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (chart : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x chart)
    (Ω : Set ℂ) (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U) where
  representative : ℂ → Space (KPCuspLogShape.dimension F * 3) → ℂ
  smooth : ∀ s ∈ Ω, ContDiffOn ℝ (⊤ : ℕ∞) (representative s) A.carrier
  represents : ∀ s ∈ Ω, representative s =ᵐ[volume.restrict A.carrier]
    (fun p => restriction F ζ hζ U R P H i x chart m A hA (u s) p)
  holomorphic : KPCutoffSource.ChartSmoothHolomorphicOn A representative Ω

  disks : ∀ (c : ℂ) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ Ω →
    ∃ b : ℕ → Space (KPCuspLogShape.dimension F * 3) → ℂ,
      (∀ j, b j =ᵐ[volume.restrict A.carrier]
        (fun p => restriction F ζ hζ U R P H i x chart m A hA
          ((cauchyPowerSeries u c r j) (fun _ => 1)) p)) ∧
      SmoothPowerSeriesOn A c r b representative ∧
      (∀ j (f : Space (KPCuspLogShape.dimension F * 3) → ℂ),
        ContDiffOn ℝ (⊤ : ℕ∞) f A.carrier →
        (f =ᵐ[volume.restrict A.carrier]
          (fun p => restriction F ζ hζ U R P H i x chart m A hA
            ((cauchyPowerSeries u c r j) (fun _ => 1)) p)) →
        Set.EqOn f (b j) A.carrier)


end DedekindZetaZeroFree.KPContActualLocalSolutionFamily

namespace DedekindZetaZeroFree

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContActualLocalSolutionFamily

theorem kp_cont_actual_local_solution_family
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (chart : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x chart)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (a : ℂ → ℂ) (ha : DifferentiableOn ℂ a Ω)
    (u : ℂ → KPContSectorClosedLpSubspace.H F ζ hζ R U) (hu : DifferentiableOn ℂ u Ω)
    (h : ℂ → Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hforcing_smooth : KPCutoffSource.ChartSmoothHolomorphicOn A h Ω)
    (hdom : ∀ s ∈ Ω, u s ∈
      (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization).domain)
    (hsource : ∀ s (hs : s ∈ Ω),
      h s =ᵐ[volume.restrict A.carrier]
        (fun p => restriction F ζ hζ U R P H i x chart m A hA
          ((KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization)
            ⟨u s, hdom s hs⟩ - a s • u s) p)) :
    Nonempty (Promotion F ζ hζ U R P H i x chart m A hA Ω u) := by
  classical
  let RA := restriction F ζ hζ U R P H i x chart m A hA
  let D := KPContActualFriedrichsWeakChart.chartCoefficients F A
  have hweak : ∀ s ∈ Ω, ∃ w : IntegerSobolev A 1,
      KPContLocalEnergy.value w = RA (u s) ∧ ∃ g : BallL2 A,
        (h s =ᵐ[volume.restrict A.carrier] (fun p => g p)) ∧
          KPContLocalEnergy.WeakEquation D.data (a s) w g := by
    intro s hs
    obtain ⟨w, hw, heq⟩ := KPContFriedrichsChartVariational.exists_xi F ζ hζ U R P H
      μG hμG hR realization i x chart m A hA D.data D.density_exact rfl ⟨u s, hdom s hs⟩ (a s)
    exact ⟨w, hw, _, hsource s hs, heq⟩
  have hex : ∀ s ∈ Ω, ∃ f : Space (KPCuspLogShape.dimension F * 3) → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) f A.carrier ∧
        (f =ᵐ[volume.restrict A.carrier] (fun p => RA (u s) p)) := by
    intro s hs
    obtain ⟨w, hw, g, hg, heq⟩ := hweak s hs
    obtain ⟨f, hf, hrep⟩ := CoefficientRestriction.weighted_smooth_representative A D.data
      D.lowerDensity_pos D.lowerEllipticity_pos
      (a s) w g (h s) (hforcing_smooth.1 s hs) hg heq
    exact ⟨f, hf, by simpa only [hw] using hrep⟩
  let f : ℂ → Space (KPCuspLogShape.dimension F * 3) → ℂ := fun s =>
    if hs : s ∈ Ω then (hex s hs).choose else 0
  have hf : ∀ s ∈ Ω, ContDiffOn ℝ (⊤ : ℕ∞) (f s) A.carrier ∧
      (f s =ᵐ[volume.restrict A.carrier] (fun p => RA (u s) p)) := by
    intro s hs
    simpa only [f, dif_pos hs] using (hex s hs).choose_spec
  have hjets := CoefficientRestriction.weighted_solution_jet_continuity A D.data
    D.lowerDensity_pos D.lowerEllipticity_pos Ω hΩ a ha.continuousOn
    (fun s => RA (u s)) (RA.continuous.comp_continuousOn hu.continuousOn)
    h hforcing_smooth hweak f hf
  have hhol := KPContLocalHolomorphyUpgrade.CauchyAssembly.holomorphy_of_jet_continuity
    A RA Ω hΩ u hu f hf hjets
  refine ⟨⟨f, fun s hs => (hf s hs).1, fun s hs => (hf s hs).2,
    KPContSmoothPromotion.power_series_jet_holomorphy A Ω hΩ f hhol.1, ?_⟩⟩
  intro c r hr hclosed
  obtain ⟨b, hspec, hseries⟩ := hhol.2 c r hr hclosed
  exact ⟨b, fun j => (hspec j).1, hseries, fun j => (hspec j).2⟩

end DedekindZetaZeroFree

end
