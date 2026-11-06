module

public import OAI.NumberTheory.DirichletL.Descent.FirstEnergy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation FourierBridge ActualEisensteinCubic FirstPassCubeLabels


variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem firstOuterPhase_norm  h   a  :
    ‖firstOuterPhase h a‖ = 1 := by
  simp [firstOuterPhase,norm_prod,logPhase_norm]


end SevenEighths.InverseMoment

end OAI
