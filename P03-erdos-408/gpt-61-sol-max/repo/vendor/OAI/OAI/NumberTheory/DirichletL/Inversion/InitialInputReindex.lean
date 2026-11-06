module

public import OAI.NumberTheory.DirichletL.Inversion.InitialTotalFourier

@[expose] public section

namespace OAI



open scoped Classical BigOperators
namespace SevenEighths.InverseInitialInputReindex
open ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic InverseMoment
open InverseInitialArithmetic


theorem input_puncture_span {ι:Type*}[DecidableEq ι](p:ι→ActualEisensteinCubic.O)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
     pool  Ψ  j₁ j₂ (hspan:Ideal.span {j₁}=Ideal.span {j₂})
     test  u :
    inputConjugateRow p hg pool Ψ j₁ 1 1 test u=
      inputConjugateRow p hg pool Ψ j₂ 1 1 test u:=by
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [rowCoprimeMask_eq_of_span_eq (fun i=>Ideal.span {p i}) A hspan]

end SevenEighths.InverseInitialInputReindex



end OAI
