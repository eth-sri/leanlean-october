module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactInvariance
public import DedekindZetaZeroFree.Eisenstein.Induction.ArchimedeanSectionSmoothness

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceKFinite
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "f" => RawSource.scalarValue F ζ hζ P C
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology






















































































end DedekindZetaZeroFree.EisensteinReferenceSections.SourceKFinite

end
