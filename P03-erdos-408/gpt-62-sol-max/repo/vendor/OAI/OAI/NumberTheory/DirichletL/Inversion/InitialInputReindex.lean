module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Inversion.InitialInputRadial
public import OAI.NumberTheory.DirichletL.Inversion.InitialAssignments
public import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapHeight
public import OAI.NumberTheory.DirichletL.Inversion.InitialMarkedInputEnergy

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
namespace SevenEighths.InverseInitialInputReindex
open ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic InverseMoment
open InverseInitialArithmetic
local notation "O"=>ActualEisensteinCubic.O

theorem input_puncture_span {ι:Type*}[DecidableEq ι](p:ι→O)
    [OAI.PrincipalFamily.Maximal p]
    (hg:OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)
    (pool:Finset ι)(Ψ:O→*ℂ)(j₁ j₂:O)(hspan:Ideal.span {j₁}=Ideal.span {j₂})
    (test:Finset ι→ℂ)(u:O):
    inputConjugateRow p hg pool Ψ j₁ 1 1 test u=
      inputConjugateRow p hg pool Ψ j₂ 1 1 test u:=by
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [rowCoprimeMask_eq_of_span_eq (fun i=>Ideal.span {p i}) A hspan]

end SevenEighths.InverseInitialInputReindex

end

end OAI
