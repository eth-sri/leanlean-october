module
public import OAI.NumberTheory.DirichletL.Energy.OriginalSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPhysicalEntry
open HeckeFamily CenteredMomentEnergyOriginalSource CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform CenteredMomentSourceRow CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSecondHeightFamily CenteredMomentExceptionalAmplitudePair CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance physicalEntryDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma natural_inverse_scale {Z Bmask bΦ:ℝ} (state:NaturalState Z Bmask bΦ)
    (B:ℝ)(hB:0≤B):state.radial.scale⁻¹≤Z^B:=by
  have hscale:1≤state.radial.scale:=by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  exact (inv_le_one_of_one_le₀ hscale).trans (Real.one_le_rpow state.base_ge_one hB)

end SevenEighths.CenteredMomentEnergyPhysicalEntry

end

end OAI
