module
public import OAI.NumberTheory.DirichletL.Descent.SecondAssignedSum
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

section
variable {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn)
include Jo Jn u v x
theorem actualSecondChild_erase :
    actualSecondChild p u v (eraseSecondSlots x) = actualSecondChild p u v x := rfl

theorem actualSecondChild_neg_frequency :
    actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}} =
      ((actualSecondChild p u v x).1,(actualSecondChild p u v x).2.1,-(actualSecondChild p u v x).2.2) := by
  pm_3780 actualSecondChild secondChild originalSecondTuple markedSecondOriginal cubeSecondSource secondUnitFrequency_neg mul_neg
end

end
end SevenEighths.InverseMoment

end OAI
