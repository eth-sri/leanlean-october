module

public import OAI.NumberTheory.DirichletL.Descent.SecondAssignedSum

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
noncomputable section
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondChild_erase {Jo Jn : ℕ} (u v : ActualEisensteinCubic.Oˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v (eraseSecondSlots x) = actualSecondChild p u v x := rfl

theorem actualSecondChild_neg_frequency {Jo Jn : ℕ} (u v : ActualEisensteinCubic.Oˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}} =
      ((actualSecondChild p u v x).1,(actualSecondChild p u v x).2.1,-(actualSecondChild p u v x).2.2) := by
  simp only [actualSecondChild,secondChild,originalSecondTuple,markedSecondOriginal,cubeSecondSource,
    secondUnitFrequency_neg,mul_neg]

end
end SevenEighths.InverseMoment

end OAI
