module

public import OAI.NumberTheory.DirichletL.Descent.CanonicalChildSupport
public import OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStep

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.InverseMoment
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→ActualEisensteinCubic.O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseMoment

end

end OAI
