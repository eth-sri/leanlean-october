module

public import DedekindZetaZeroFree.Eisenstein.Residues.CuspidalCenterVanishing
public import DedekindZetaZeroFree.Eisenstein.Continuation.SphericalScalarPoleClearing

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff
open MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "level" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "G" => KPContSectorCoveredQuotientVocabulary.ActualCover F ζ hζ

theorem center_memLp_original
    (Z : Smooth) (z : KPContActualAllCuspSource.Sector F ζ hζ C R P H U)
    (hz : KPContActualSmoothLineGluing.Represents F ζ hζ level R P H Z.val z) :
    MemLp (fun x => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U Z
      (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ level x)) 2 R.quotientHaar := by
  obtain ⟨hm, he⟩ := hz
  have hs : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ level R P H Z.val).val =
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U Z := by
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    rfl
  rw [hs] at hm
  exact hm.comp_measurePreserving (⟨(KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ level).measurable, rfl⟩)

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
