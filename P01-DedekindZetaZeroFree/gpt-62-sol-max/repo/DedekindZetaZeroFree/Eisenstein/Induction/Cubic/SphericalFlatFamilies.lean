module

public import DedekindZetaZeroFree.Eisenstein.Induction.Cusps.IncomingCasimirEquation

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
open scoped Classical NumberField BigOperators

namespace DedekindZetaZeroFree.KPContActualSphericalFlatStage

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Stage (U : KPMsRationalCompactCrossPairing.Level F ζ hζ) :=
  KPContFlatCommonLevelKernel.CommonSphericalStage F ζ hζ U

variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
variable [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] Stage F ζ hζ U)

abbrev coreInclusion := (Stage F ζ hζ U).subtype.comp ι

abbrev L := KPContFlatCommonLevelKernel.L F ζ hζ U ι

theorem stage_smooth (v : S) :
    (coreInclusion F ζ hζ U ι v).val ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
  have h := (coreInclusion F ζ hζ U ι v).property
  change (coreInclusion F ζ hζ U ι v).val ∈ KPGlobalEisensteinData.hcHeckeCore _ _ _ at h
  apply (show KPGlobalEisensteinData.hcHeckeCore _ _ _ ≤
    KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) from ?_) h
  unfold KPGlobalEisensteinData.hcHeckeCore
  exact iSup_le fun _ => iSup_le fun _ => inf_le_left.trans inf_le_left


def Covariance : Prop :=
  ∀ (s : ℂ), s ∈ KPContinuation.spectralDomain →
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
      L F ζ hζ U ι s v (g * u.val) = L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (k : KPContSectorArchSphericalFibers.KInfinity F),
      L F ζ hζ U ι s v
        (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) =
          L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ) (ε : rootsOfUnity 3 F),
      L F ζ hζ U ι s v (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (a : KPGlobalResidualKernel.rationalBorel F ζ hζ),
      L F ζ hζ U ι s v (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ a.val * g) =
        L F ζ hζ U ι s v g) ∧
    (∀ (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (h : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H)
      (x : KPGlobalTorusFunctionData.Adeles F),
      L F ζ hζ U ι s v ((h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
        KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
          ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character h : ℂ) *
            L F ζ hζ U ι s v g)

theorem covariance : Covariance F ζ hζ U ι := by
  intro s hs
  obtain ⟨hU, hK, hχ, _, hB⟩ := KPContFlatCommonLevelKernel.stage_properties F ζ hζ U ι s hs
  refine ⟨hU, hK, fun v g ε => hχ v ε g, ?_, fun v g h x => hB v h x g⟩
  intro v g a
  exact KPContFlatRationalCosetCovariance.L_rationalBorel F ζ hζ s
    (coreInclusion F ζ hζ U ι v) a g

def SmoothHolomorphy : Prop :=
  (∀ (s : ℂ) (v : S) (g : KPGlobalTorusFunctionData.G F ζ hζ),
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => L F ζ hζ U ι s v
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) ∧
  (∀ (f : ℂ → S), DifferentiableOn ℂ f KPContinuation.spectralDomain →
    ∀ (g : KPGlobalTorusFunctionData.G F ζ hζ) (n : ℕ)
      (Q : KPGlobalTorusFunctionData.JetCompact
        (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)),
    letI : CompactSpace Q.set := isCompact_iff_compactSpace.mp Q.compact
    DifferentiableOn ℂ
      (fun s => KPContFlatStageJetHolomorphy.compactJet F ζ hζ
        (coreInclusion F ζ hζ U ι) (stage_smooth F ζ hζ U ι) g n Q s (f s))
      KPContinuation.spectralDomain)


abbrev Cusps := KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U

variable (a : Cusps F ζ hζ C R P H U)

theorem incoming_formula (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (t : ℝ) (b : KPCuspCharts.Shape F) :
    KPContFlatCuspIncomingEvaluation.W F ζ hζ C R P H U a ι s v t b =
      Complex.exp (((Module.finrank ℚ F / 2 : ℕ) : ℂ) * ((4 : ℂ) / 3 + 2 * s) * (t : ℂ)) •
        (KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs v).val b := by
  exact KPContFlatCuspIncomingEvaluation.incoming_formula F ζ hζ C R P H U a ι s hs v t b

end DedekindZetaZeroFree.KPContActualSphericalFlatStage

namespace DedekindZetaZeroFree.KPContActualSphericalFlatStage

def coordinateDirection (d : ℕ) (i : Fin d) (j : Fin 3) : KPArch.Space d :=
  Pi.single i (if j = 0 then (1, 0) else if j = 1 then (Complex.I, 0) else (0, 1))

def inverseMetricWeight (d : ℕ) (z : KPArch.Space d) (i : Fin d) (j : Fin 3) : ℝ :=
  if j = 2 then 1 else KPArch.height (z i) ^ 2

def localLaplacian (d : ℕ) (f : KPArch.Space d → ℂ) (z : KPArch.Space d) : ℂ :=
  -((KPArch.volumeDensity d z : ℂ)⁻¹ *
    ∑ i : Fin d, ∑ j : Fin 3,
      fderiv ℝ (fun y =>
        ((KPArch.volumeDensity d y * inverseMetricWeight d y i j : ℝ) : ℂ) *
          fderiv ℝ f y (coordinateDirection d i j)) z (coordinateDirection d i j))

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] Stage F ζ hζ U)
variable (a : Cusps F ζ hζ C R P H U)


end DedekindZetaZeroFree.KPContActualSphericalFlatStage

namespace DedekindZetaZeroFree

open KPContActualSphericalFlatStage

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

end DedekindZetaZeroFree

end
