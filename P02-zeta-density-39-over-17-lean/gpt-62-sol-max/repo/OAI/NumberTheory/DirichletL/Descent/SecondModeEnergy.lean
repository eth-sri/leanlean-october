module
public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalIdealFamily
public import OAI.NumberTheory.DirichletL.Descent.SecondModeCanonical
public import OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRows

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [OAI.PrincipalIdealFamily.Maximal p]
  (hcop : OAI.PrincipalIdealFamily.PairwiseCoprime p)
  (hg : OAI.PrincipalIdealFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

end
end SevenEighths.InverseMoment

end OAI
