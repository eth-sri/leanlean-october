module
public import OAI.NumberTheory.DirichletL.Descent.SecondVariablePrincipal
public import OAI.NumberTheory.DirichletL.Descent.FirstWholeCubePriority
public import OAI.NumberTheory.DirichletL.Descent.FirstWholeMarkedColumns

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion InverseSecondPrincipalCaller InversePrincipalEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseMoment

end

end OAI
