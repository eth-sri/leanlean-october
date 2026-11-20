module

public import DedekindZetaZeroFree.Eisenstein.Residues.Cofactors.NonzeroUpperCoefficient

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators Topology
open Filter
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber
open KPLocalPrincipalSeries KPGlobalTorusFiniteStages KPLocalExceptionalConstruction
open KPGlobalResidualConstruction
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)
    (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
    (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

alias exists_coreResidue_ne_zero_unconditional := exists_coreResidue_ne_zero

end DedekindZetaZeroFree.FourierContinuation.LiteralSource.CofactorChamber

end
