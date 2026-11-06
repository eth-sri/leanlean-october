module

public import OAI.NumberTheory.DirichletL.Descent.SecondVariablePrincipal
public import OAI.NumberTheory.DirichletL.Descent.FirstWholeCubePriority
public import OAI.NumberTheory.DirichletL.Descent.FirstWholeMarkedColumns

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.InverseMoment
local notation "O" => ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseMoment

end

end OAI
