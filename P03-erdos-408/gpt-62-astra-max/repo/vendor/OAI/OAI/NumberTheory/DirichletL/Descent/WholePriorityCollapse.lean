module

public import OAI.NumberTheory.DirichletL.Descent.WholePriorityRays
public import OAI.NumberTheory.DirichletL.Descent.WholePriorityPrincipal
public import OAI.NumberTheory.DirichletL.Inversion.WholePriorityRapidTail

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseMoment

end

end OAI
