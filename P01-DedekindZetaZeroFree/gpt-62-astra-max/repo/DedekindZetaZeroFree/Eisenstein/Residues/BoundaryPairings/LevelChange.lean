module

public import DedekindZetaZeroFree.Eisenstein.Residues.SourceVanishing
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.DifferentialWordBoundaryPairing

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
open KPContSectorCoveredQuotientVocabulary KPContFlatCuspIncomingEvaluation
open KPGlobalResidualConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)
    (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
    (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
variable (D : KPGlobalTorusInducingPlan.ModelData F R.A.zeta12 R.A.primitive_zeta12)
    (HR : KPSmoothLocalQuotientCharts.HaarRecipe F R.A.zeta12 R.A.primitive_zeta12)
    (HP : KPMsFixedHaarDisintegration.SphericalTransport F R.A.zeta12 R.A.primitive_zeta12)
    (M : NativeMeasuredSource F R.A.zeta12 R.A.primitive_zeta12 HR HP)
    (U : Level F R.A.zeta12 R.A.primitive_zeta12)
local notation "H" => nativeFamily F ζ hζ HR HP
local notation "V" => EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U
local instance ResidualCoreBoundaryRelevelMeasurable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance ResidualCoreBoundaryRelevelBorel (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge

include M in
theorem finiteBoundaryPair_core_relevel
    (U₁ U₂ : Level F ζ hζ) (dk : Measure (KPMsGreenFlux.K F))
    [IsFiniteMeasure dk] [dk.IsHaarMeasure] (x : Core)
    (hs₁ : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U₁ →
      quotientCoreEvaluator R.A P C x (g*u)=quotientCoreEvaluator R.A P C x g)
    (hs₂ : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U₂ →
      quotientCoreEvaluator R.A P C x (g*u)=quotientCoreEvaluator R.A P C x g)
    (hx₁ : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U₁ →
      coreResidue R P C x (g*u)=coreResidue R P C x g)
    (hx₂ : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U₂ →
      coreResidue R P C x (g*u)=coreResidue R P C x g) :
    finiteBoundaryPair R HR HP U₁ dk (quotientCoreEvaluator R.A P C x) (coreResidue R P C x) =
    finiteBoundaryPair R HR HP U₂ dk (quotientCoreEvaluator R.A P C x) (coreResidue R P C x) := by
  obtain ⟨t,ht⟩ := core_source_zero_exists R P C x
  have ht₀ (g) : t.val.val g = quotientCoreEvaluator R.A P C x g := by
    simpa only [KPContFlatSourceRecipe.flatR_formula, zero_mul, Complex.exp_zero, one_mul] using ht g
  simpa only [finiteBoundaryPair, boundaryProduct, ht, KPGlobalResidualConstruction.upperConstantTerm] using ((boundary_full_mass_eq_beta R P C M U₁ dk t x
    (fun g u hu => by rw [ht₀, ht₀]; exact hs₁ g u hu) hx₁).symm.trans (boundary_full_mass_eq_beta R P C M U₂ dk t x
    (fun g u hu => by rw [ht₀, ht₀]; exact hs₂ g u hu) hx₂))

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
