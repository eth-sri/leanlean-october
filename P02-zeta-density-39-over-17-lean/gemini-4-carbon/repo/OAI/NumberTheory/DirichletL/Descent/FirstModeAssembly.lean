module
public import OAI.NumberTheory.DirichletL.Descent.FirstModeColumns


@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels FourierBridge JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
