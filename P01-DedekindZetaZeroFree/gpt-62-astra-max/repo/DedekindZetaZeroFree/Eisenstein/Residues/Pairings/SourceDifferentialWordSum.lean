module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.BoundaryPairings.SliceLinearity
public import DedekindZetaZeroFree.Eisenstein.Residues.Source.CompactDifferentialExpansion

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
local instance ResidualSourceWordSumMeasurable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance ResidualSourceWordSumBorel (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge

open _root_.DedekindZetaZeroFree.KPMsAngularSourceRecipe (finitePart_eq_finiteCover)

theorem finiteBoundaryPair_source_words_sum
    (Vnew : Level F ζ hζ) (dk : Measure (KPMsGreenFlux.K F)) [IsFiniteMeasure dk]
    {ι : Type} [Fintype ι] (a : ι → ℂ)
    (v : ι → KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (w : ι → List (Fin (groupDimension F))) (x : Core) :
    finiteBoundaryPair R HR HP Vnew dk
      (fun g => ∑i, a i * actualRightWord F ζ hζ (w i) (v i).val.val g) (coreResidue R P C x) =
      ∑i, a i * finiteBoundaryPair R HR HP Vnew dk
        (actualRightWord F ζ hζ (w i) (v i).val.val) (coreResidue R P C x) := by
  apply finiteBoundaryPair_source_sum_of_slices
  intro i j
  exact ResidualPrincipalSlices.source_word_compact_continuous F ζ hζ (v i)
    ⟨(KPBoundedCuspFrames.actualFiniteRepresentative
      (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) j).val, by
        rw [finitePart_eq_finiteCover F ζ hζ]
        exact (KPBoundedCuspFrames.actualFiniteRepresentative
          (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) j).property⟩ (w i)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
