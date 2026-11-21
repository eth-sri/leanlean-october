module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.UniformL2Tails
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.CutoffGraphConvergence

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberDomainEquations

open KPContActualChamberThreeL2Tails

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (level F ζ hζ C R P H U) R P H)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
  KPContinuation.spectralDomain f χ)

local notation "Δ" => KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ
  (level F ζ hζ C R P H U) R P H μG hμG hR realization
local notation "u" => UJet F ζ hζ C R P H U ι f buffer χ source hι hf
local notation "h" => HJet F ζ hζ C R P H U ι f buffer χ source hι hf
local notation "dloc" => DeltaJet F ζ hζ C R P H U ι f buffer χ source hι hf
local notation "w" => smoothG F ζ hζ C R P H U ι f buffer χ source hι hf

/-- Apply closed graph convergence to the undifferentiated defect. -/
theorem domain_equation : ∀ s ∈ V,
    ∃ hd : u 0 s ∈ (Δ).domain,
      Δ ⟨u 0 s, hd⟩ - KPContActualChamberCasimirJets.lambda F s • u 0 s = -h 0 s := by
  intro s hs
  have hi := integrability F ζ hζ C R P H U ι f buffer χ source hι hf 0 s
  let G : KPContActualSectorCutoffGraphLimit.GraphSection (U := level F ζ hζ C R P H U) (H := H) :=
    ⟨w 0 s, hi.1.2,
      KPContActualSectorCutoffGraphLimit.squareFinite_gradient_of_laplacian F ζ hζ
        (level F ζ hζ C R P H U) R P H μG hμG hR realization (w 0 s) hi.1.2 hi.2.2.2,
      hi.2.2.2⟩
  obtain ⟨hd, he⟩ := kp_cont_actual_sector_cutoff_graph_limit F ζ hζ μG hμG
    (level F ζ hζ C R P H U) R hR P H realization G
  change u 0 s ∈ (Δ).domain at hd
  change Δ ⟨u 0 s, hd⟩ = dloc 0 s at he
  refine ⟨hd, ?_⟩
  rw [he, deltaJet_zero F ζ hζ C R P H U ι f buffer χ source hι hf s hs]
  abel

end DedekindZetaZeroFree.KPContActualChamberDomainEquations

end
