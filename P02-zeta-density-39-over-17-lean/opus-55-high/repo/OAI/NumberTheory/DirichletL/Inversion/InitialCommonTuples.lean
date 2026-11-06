module
public import OAI.NumberTheory.DirichletL.Inversion.InitialCommonForcing
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing
local notation "Eis"=>ActualEisensteinCubic.O
variable {κ ι : Type*} [DecidableEq ι]

theorem input_finset_sum (p:ι→ Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,goodLambda∉Ideal.span {p i})(F:Finset ι)(Ψ:Eis→*ℂ)(j u:Eis)
    (T:Finset κ)(a:κ→ℂ)(H:κ→ Finset ι→ℂ) :
    inputConjugateRow p hg F Ψ j 1 1 (fun A=>∑k∈T,a k*H k A) u=
      ∑k∈T,a k*inputConjugateRow p hg F Ψ j 1 1 (H k) u := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  pm_3397 k hk A hA
  ring

def tupleColumns (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→ Ideal Eis)(j:Ideal Eis) :
    Finset (Ideal Eis) := T.biUnion (fun k=>columns S (P k) j)

end SevenEighths.InverseInitialCommonTuples

end

end OAI
