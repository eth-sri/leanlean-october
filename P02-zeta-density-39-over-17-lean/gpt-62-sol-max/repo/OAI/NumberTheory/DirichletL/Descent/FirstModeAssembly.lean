module
public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalIdealFamily
public import OAI.NumberTheory.DirichletL.Descent.FirstModeColumns

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic FirstPassCubeLabels FourierBridge JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [OAI.PrincipalIdealFamily.Maximal p]
  (hcop : OAI.PrincipalIdealFamily.PairwiseCoprime p)
  (hg : OAI.PrincipalIdealFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

end
end SevenEighths.InverseMoment

end OAI
