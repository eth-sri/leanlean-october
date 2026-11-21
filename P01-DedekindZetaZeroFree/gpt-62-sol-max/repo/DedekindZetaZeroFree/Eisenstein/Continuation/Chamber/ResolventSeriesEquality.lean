module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.FriedrichsDomainDefect
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.HolomorphicResolventInverse
public import DedekindZetaZeroFree.Eisenstein.Continuation.Resolvent.CutoffAndClearedGerms

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberFormulaEquality

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "HU" => KPContActualAllCuspSource.Sector F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "μ" => KPContActualAllCuspSource.measure F ζ hζ C R P H U
local notation "Ω" => KPContinuation.spectralDomain
local notation "V" => KPContActualChamberDomainDefect.V
local notation "scalar" => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
local notation "Represents" => KPContActualSmoothLineGluing.Represents F ζ hζ level R P H

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (f : ℂ → S)
variable {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer KPContinuation.spectralDomain f χ)
variable (domain : KPContActualChamberDomainDefect.DomainConclusions F ζ hζ C R P H U ι f buffer χ source μG hμG hR realization)
local notation "v" => KPContActualHilbertSimpleGerms.v F ζ hζ C R P H U μG hμG hR realization ι buffer Ω f χ source
local notation "poles" => KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization Ω

include H in
theorem actual_spectralCoordinate : KPContActualChamberInverse.a_U F =
    KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) := by
  funext s
  unfold KPContActualChamberInverse.a_U KPContinuation.spectralCoordinate
  congr 1
  have ht : NumberField.IsTotallyComplex F := NumberField.nrRealPlaces_eq_zero_iff.mp H.totallyComplex
  have hfin := @NumberField.IsTotallyComplex.finrank F _ _ ht
  have hnat : Module.finrank ℚ F / 2 = NumberField.InfinitePlace.nrComplexPlaces F := by rw [hfin]; omega
  rw [hnat, hfin]
  push_cast
  ring

include realization in
theorem chamber_regular_actual : V ⊆ Ω \ poles := by
  have hi := kp_cont_actual_chamber_inverse F ζ hζ μG hμG level R hR P H realization
  have ht : NumberField.IsTotallyComplex F := NumberField.nrRealPlaces_eq_zero_iff.mp H.totallyComplex
  have hfin := @NumberField.IsTotallyComplex.finrank F _ _ ht
  have hd : ((Module.finrank ℚ F / 2 : ℕ) : ℝ) = (Module.finrank ℚ F : ℝ) / 2 := by
    rw [hfin, Nat.mul_div_right _ (by norm_num)]; push_cast; ring
  intro s hs
  have hr := (hi.chamber_regular s hs).1
  unfold KPContActualChamberInverse.Sigma_U at hr
  rw [actual_spectralCoordinate F ζ hζ R P H] at hr
  simpa only [KPContActualHilbertSimpleGerms.Sigma, hd, Nat.cast_ofNat, Nat.cast_mul,
    Int.natCast_div, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] using hr

include realization buffer in
theorem domain_class_correction : ∀ s ∈ V, (domain.u s : HU) = v s := by
  have hi := kp_cont_actual_chamber_inverse F ζ hζ μG hμG level R hR P H realization
  intro s hs
  have hh := (hi.genuine_inverse s hs).choose_spec.2
  rw [actual_spectralCoordinate F ζ hζ R P H] at hh
  have ht := hh (domain.u s)
  rw [domain.equation s hs, map_neg] at ht
  exact ht.symm

include realization buffer in
theorem domain_defect_represents (s : ℂ) (hs : s ∈ V) :
    Represents (domain.series s - source.descent.cutoff s).val (domain.u s : HU) := by
  have hae := domain.defect_ae s hs
  have hr : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H
      (domain.series s - source.descent.cutoff s).val).val =
      KPContActualChamberDomainDefect.defectScalar F ζ hζ C R P H U ι f buffer χ source s := by
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    change ((KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm
      ((domain.series s).val - (source.descent.cutoff s).val)).val = _
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (source.descent.cutoff s).val,
      (KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm.map_add,
      (KPContSectorScalarLineAlgebra.S F ζ hζ level R P H).symm.map_smul]
    change scalar (domain.series s) + (-1 : ℂ) • scalar (source.descent.cutoff s) = _
    rw [neg_one_smul, ← sub_eq_add_neg]
    rw [domain.series_formula s hs]
    rfl
  have hmem := MemLp.ae_eq hae (Lp.memLp ((domain.u s : HU) : Lp ℂ 2 μ))
  have hf' : MemLp (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H
      (domain.series s - source.descent.cutoff s).val).val 2 μ := hr ▸ hmem
  refine ⟨hf', ?_⟩
  apply Lp.ext
  refine hf'.coeFn_toLp.trans ?_
  have ht : _ =ᵐ[μ] _ := Filter.Eventually.of_forall (congrFun hr)
  exact ht.trans hae.symm
variable (W : ℂ → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
variable (hW : KPContActualCutoffPlusClearedGerm.Properties F ζ hζ C R P H U μG hμG hR ι Ω f χ realization buffer source W)

include hW in
theorem literal_sections_equal : ∀ s ∈ V,
    KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U Ω poles source.descent.cutoff W s = domain.series s := by
  intro s hs
  have hr := chamber_regular_actual F ζ hζ C R P H U μG hμG hR realization hs
  apply Eq.symm
  apply hW.off_pole_unique s hr
  rw [← domain_class_correction F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source domain s hs]
  exact domain_defect_represents F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source domain s hs

end DedekindZetaZeroFree.KPContActualChamberFormulaEquality

namespace DedekindZetaZeroFree

theorem kp_cont_actual_chamber_formula_equality
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (T : ℝ)
    (hT : (H.atlas (KPContActualAllCuspSource.level F ζ hζ C R P H U)).threshold < T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T) :
    ∃ buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T,
      ∃ source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
          KPContinuation.spectralDomain f χ,
        ∃ W : ℂ → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U,
          KPContActualCutoffPlusClearedGerm.Properties
            F ζ hζ C R P H U μG hμG hR ι KPContinuation.spectralDomain f χ realization buffer source W ∧
          ∀ s ∈ KPContActualChamberDomainDefect.V, ∀ g : KPContActualChamberNormalSeries.G F ζ hζ,
            KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ C R P H U
              (KPContActualCutoffPlusClearedGerm.E F ζ hζ C R P H U KPContinuation.spectralDomain
                (KPContActualHilbertSimpleGerms.Sigma F ζ hζ C R P H U μG hμG hR realization
                  KPContinuation.spectralDomain) source.descent.cutoff W s) g =
              KPContActualChamberNormalSeries.E F ζ hζ U ι f s g := by
  obtain ⟨buffer,source,⟨domain⟩⟩ := kp_cont_actual_chamber_domain_defect
    F ζ hζ C μG hμG R hR P H U realization ι hι f hf T hT χ
  obtain ⟨W,hW⟩ := kp_cont_actual_cutoff_plus_cleared_germ F ζ _ C R P H U μG hμG hR realization
    ι hι KPContinuation.spectralDomain KPContinuation.spectralDomain_isOpen Set.Subset.rfl
    f hf buffer χ source
  refine ⟨buffer, source, W, hW, ?_⟩
  intro s hs g
  rw [KPContActualChamberFormulaEquality.literal_sections_equal
    F ζ hζ C R P H U μG hμG hR realization ι f buffer χ source domain W hW s hs]
  exact domain.series_lift s hs g

end DedekindZetaZeroFree

end
