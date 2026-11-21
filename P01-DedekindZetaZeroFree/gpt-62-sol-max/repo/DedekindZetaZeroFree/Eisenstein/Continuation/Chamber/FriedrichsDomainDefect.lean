module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.DomainJetEquations

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberDomainDefect

abbrev V : Set ℂ := KPContActualChamberNormalSeries.V

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev level := KPContActualAllCuspSource.level F ζ hζ C R P H U
abbrev Covered := KPContActualAllCuspSource.Covered F ζ hζ C R P H U
abbrev Sector := KPContActualAllCuspSource.Sector F ζ hζ C R P H U
abbrev SmoothSections := KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
abbrev measure := KPContActualAllCuspSource.measure F ζ hζ C R P H U

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S)

def seriesScalar (s : ℂ) : Covered F ζ hζ C R P H U → ℂ :=
  KPChamberL2Defect.series (KPContActualChamberNormalSeries.lift F ζ hζ)
    (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U)
    (KPContActualSphericalFlatStage.L F ζ hζ U ι) f s

variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U →
  KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B
  KPContinuation.spectralDomain f χ)

def defectScalar (s : ℂ) : Covered F ζ hζ C R P H U → ℂ :=
  seriesScalar F ζ hζ C R P H U ι f s -
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff s)

variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (level F ζ hζ C R P H U) R P H)

abbrev laplacian := KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ
  (level F ζ hζ C R P H U) R P H μG hμG hR realization

local notation "Δ" => laplacian F ζ hζ C R P H U μG hμG hR realization
local notation "HU" => Sector F ζ hζ C R P H U
local notation "L2" => KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R
  (level F ζ hζ C R P H U)
local notation "lam" => KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ)

structure DomainConclusions where
  series : ℂ → SmoothSections F ζ hζ C R P H U
  series_formula : ∀ s ∈ V,
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (series s) =
      seriesScalar F ζ hζ C R P H U ι f s

  series_lift : ∀ s ∈ V, ∀ g : KPContActualChamberNormalSeries.G F ζ hζ,
    KPContActualCutoffSmoothDescent.lift F ζ hζ C R P H U (series s)
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
        KPContActualChamberNormalSeries.E F ζ hζ U ι f s g

  u : ℂ → (Δ).domain
  defect_ae : ∀ s ∈ V,
    ((u s : HU) : L2) =ᵐ[measure F ζ hζ C R P H U]
      defectScalar F ζ hζ C R P H U ι f B χ source s
  equation : ∀ s ∈ V, Δ (u s) - lam s • (u s : HU) = -source.h s

end DedekindZetaZeroFree.KPContActualChamberDomainDefect

namespace DedekindZetaZeroFree

set_option maxHeartbeats 4000000 in

open KPContActualChamberDomainDefect in
open KPContActualChamberThreeL2Tails (UJet HJet jets_actual_ae g h) in
theorem kp_cont_actual_chamber_domain_defect
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualChamberDomainDefect.level F ζ hζ C R P H U) R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (T : ℝ)
    (hT : (H.atlas (KPContActualChamberDomainDefect.level F ζ hζ C R P H U)).threshold < T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T) :
    ∃ B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
        (KPContActualChamberDomainDefect.level F ζ hζ C R P H U) R P H T,
      ∃ source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B
          KPContinuation.spectralDomain f χ,
        Nonempty (KPContActualChamberDomainDefect.DomainConclusions F ζ hζ C R P H U
          ι f B χ source μG hμG hR realization) := by
  classical
  obtain ⟨B, ⟨source⟩⟩ := kp_cont_actual_all_cusp_source F ζ hζ C R P H U realization
    ι hι
    KPContinuation.spectralDomain KPContinuation.spectralDomain_isOpen Set.Subset.rfl f hf T hT χ
  have hd := KPContActualChamberDomainEquations.domain_equation
    F ζ hζ C R P H U μG hμG hR realization ι hι f hf B χ source
  let v := UJet F ζ hζ C R P H U ι f B χ source hι hf 0
  let u (s : ℂ) : (laplacian F ζ hζ C R P H U μG hμG hR realization).domain :=
    if hs : s ∈ KPContActualChamberDomainDefect.V then ⟨v s, (hd s hs).choose⟩ else 0
  let series : ℂ → KPContActualChamberDomainDefect.SmoothSections F ζ hζ C R P H U := fun s =>
    if hs : s ∈ KPContActualChamberDomainDefect.V then
      ⟨KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 s,
        KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf 0 s hs⟩
    else 0
  have hseries : ∀ s ∈ KPContActualChamberDomainDefect.V,
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (series s) =
        KPContActualChamberDomainDefect.seriesScalar F ζ hζ C R P H U ι f s := by
    intro s hs
    have hline : (series s).val = KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 s := by
      simp [series, hs]
    have hscalar : KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (series s) =
        (KPContActualChamberCasimirJets.coveredJet F ζ hζ C R P H U ι f hι hf 0 s).val := by
      unfold KPContActualCutoffSmoothDescent.scalar
      change ((KPContSectorScalarLineAlgebra.S F ζ hζ
        (KPContActualChamberDomainDefect.level F ζ hζ C R P H U) R P H).symm (series s).val).val = _
      rw [hline]
      simp only [KPContActualChamberCasimirJets.lineJet, LinearEquiv.symm_apply_apply]
    rw [hscalar]
    funext x
    simp [KPContActualChamberCasimirJets.coveredJet, hs, KPContActualChamberCasimirJets.jet,
      KPContActualChamberDomainDefect.seriesScalar, KPContActualChamberNormalSeries.E,
      KPChamberL2Defect.series, KPContActualChamberNormalSeries.term]
  refine ⟨B, source, ⟨⟨series, hseries, ?_, u, ?_, ?_⟩⟩⟩
  · intro s hs g
    unfold KPContActualCutoffSmoothDescent.lift
    rw [hseries s hs]
    obtain ⟨e, he, heval, _⟩ := KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf
    change KPContActualChamberDomainDefect.seriesScalar F ζ hζ C R P H U ι f s _ = _
    unfold KPContActualChamberDomainDefect.seriesScalar
    rw [← heval s hs]
    exact he s hs g
  · intro s hs
    have hg : g F ζ hζ C R P H U ι f B χ source 0 s = defectScalar F ζ hζ C R P H U ι f B χ source s := by
      funext x
      simp [g, defectScalar, seriesScalar, KPChamberL2Defect.series,
        KPContActualChamberNormalSeries.E, KPContActualChamberNormalSeries.term]
    rw [show u s = ⟨v s, (hd s hs).choose⟩ by simp [u, hs], ← hg]
    exact (jets_actual_ae F ζ hζ C R P H U ι f B χ source hι hf 0 s hs).1
  · intro s hs
    have hsΩ : s ∈ KPContinuation.spectralDomain := by
      change (1 : ℝ) / 3 < s.re at hs
      change -(1 : ℝ) / 6 < s.re
      linarith
    have hh : HJet F ζ hζ C R P H U ι f B χ source hι hf 0 s = source.h s := by
      apply Subtype.ext
      apply Lp.ext
      have he : h F ζ hζ C R P H U ι f B χ source 0 s =
          KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.commutator s) := by
        funext x
        simp [h]
      have hae := (jets_actual_ae F ζ hζ C R P H U ι f B χ source hι hf 0 s hs).2.1
      rw [he] at hae
      exact hae.trans (source.source_ae s hsΩ).symm
    simpa [u, hs, v, hh, KPContActualChamberCasimirJets.lambda] using (hd s hs).choose_spec

end DedekindZetaZeroFree

end
