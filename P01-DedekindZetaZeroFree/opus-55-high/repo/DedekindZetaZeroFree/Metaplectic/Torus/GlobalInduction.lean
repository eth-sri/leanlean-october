module

public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusInducingPlan
noncomputable section
attribute [local instance] KPGlobalProductPolarizationCharacter.localCoverTopology

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev ModelData := KPGlobalTorusPeriodizationInverse.ModelData F ζ hζ
