module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactOpenLevels
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicMaximalCompactness
public import DedekindZetaZeroFree.Adeles.Quotients.PrincipalTorusCoordinateInjectivity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.CompactSource
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12




















































end DedekindZetaZeroFree.EisensteinReferenceSections.CompactSource

end
