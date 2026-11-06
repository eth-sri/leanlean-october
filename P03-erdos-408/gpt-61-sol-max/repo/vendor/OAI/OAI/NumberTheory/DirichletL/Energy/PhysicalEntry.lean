module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Energy.OriginalSource

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPhysicalEntry
open HeckeFamily CenteredMomentEnergyOriginalSource CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentSecondHeightFamily CenteredMomentExceptionalAmplitudePair
open CenteredMomentInductionEnergy

variable {ι:Type*}[Fintype ι][DecidableEq ι]


lemma natural_inverse_scale {Z Bmask bΦ:ℝ} (state:NaturalState Z Bmask bΦ)
    (B:ℝ)(hB:0≤B):state.radial.scale⁻¹≤Z^B:=LE.le.trans (inv_le_one_of_one_le₀ (Eq.mpr (congrArg (LE.le 1) state.scale_eq) (Real.one_le_rpow state.base_ge_one state.row_nonneg))) (Real.one_le_rpow state.base_ge_one hB)

end SevenEighths.CenteredMomentEnergyPhysicalEntry

end

end OAI
