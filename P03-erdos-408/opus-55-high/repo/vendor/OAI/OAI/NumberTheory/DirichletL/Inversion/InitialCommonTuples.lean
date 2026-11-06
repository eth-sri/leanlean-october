module

public import OAI.NumberTheory.DirichletL.Inversion.InitialCommonForcing

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
open ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonTuples
open InverseInitialOverlap
open InverseInitialArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {κ ι : Type*} [DecidableEq ι]

theorem input_finset_sum (p:ι→ActualEisensteinCubic.O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,goodLambda∉Ideal.span {p i})(F:Finset ι)(Ψ:ActualEisensteinCubic.O→*ℂ)(j u:ActualEisensteinCubic.O)
    (T:Finset κ)(a:κ→ℂ)(H:κ→Finset ι→ℂ) :
    inputConjugateRow p hg F Ψ j 1 1 (fun A=>∑k∈T,a k*H k A) u=
      ∑k∈T,a k*inputConjugateRow p hg F Ψ j 1 1 (H k) u := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  grind

def tupleColumns (S:Finset (Ideal ActualEisensteinCubic.O))(T:Finset κ)(P:κ→Ideal ActualEisensteinCubic.O)(j:Ideal ActualEisensteinCubic.O) :
    Finset (Ideal ActualEisensteinCubic.O) := T.biUnion (fun k=>columns S (P k) j)

end SevenEighths.InverseInitialCommonTuples

end

end OAI
