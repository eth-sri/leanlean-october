module

public import DedekindZetaZeroFree.Eisenstein.Induction.RepeatedTensorSourcesAndFiniteLevel
public import DedekindZetaZeroFree.Theta.Periods.NondegenerateCovariantTensorSource

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages MomentSources ThetaExpansion TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local notation "V" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)



























end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
