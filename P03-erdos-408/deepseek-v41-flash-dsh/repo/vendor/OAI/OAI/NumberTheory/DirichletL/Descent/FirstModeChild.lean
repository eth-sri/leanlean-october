module

public import OAI.NumberTheory.DirichletL.Descent.FirstModeColumns
public import OAI.NumberTheory.DirichletL.Descent.FirstPass

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment


noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
