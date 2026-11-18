module
public import OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller
public import OAI.NumberTheory.DirichletL.Descent.FirstRetainedFamily

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight InversePrincipalEnergy RayFourExpansion
open InverseSecondPrincipalCaller
local notation "Eis" => ActualEisensteinCubic.O

end SevenEighths.InverseMoment

end

end OAI
