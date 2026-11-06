module

public import DedekindZetaZeroFree.Eisenstein.Induction.ArchimedeanSectionSmoothness
public import DedekindZetaZeroFree.Theta.Whittaker.Complex.NegativeSlotCompactBounds

set_option linter.privateModule false

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal BigOperators Matrix.Norms.Elementwise ContDiff
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines.CanonicalStageSlot
open KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPLiteralChamber
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
local notation "Raw" => KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ
variable (s : RestrictedTensorSimple.Level (bad A P C))


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end DedekindZetaZeroFree.FourierContinuation.ComplexLines.CanonicalStageSlot

end
