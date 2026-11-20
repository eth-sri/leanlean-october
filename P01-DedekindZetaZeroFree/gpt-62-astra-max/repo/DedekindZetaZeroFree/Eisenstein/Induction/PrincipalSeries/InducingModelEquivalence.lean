module

public import DedekindZetaZeroFree.Metaplectic.Kubota.Induction.UnitaryRationalFiberComparison
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Borel.TorusRetraction
public import DedekindZetaZeroFree.Theta.Profiles.ResidualCoreAndUnitRotations

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalInducingAdapter
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)

 instance level_nonempty {J : Type*} (E : Finset J) :
    Nonempty (RestrictedTensorSimple.Level E) := ⟨⟨E, le_rfl⟩⟩

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalInducingAdapter

end
