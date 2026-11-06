module

public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfilePhysical
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileAssembly
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileWindows

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
