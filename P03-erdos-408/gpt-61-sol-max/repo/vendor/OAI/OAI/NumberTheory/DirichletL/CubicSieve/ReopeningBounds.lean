module

public import OAI.NumberTheory.DirichletL.Eisenstein.BarrierPotential

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    
open ActualEisensteinCubic
 
open   RationalPrimeExtraction ShortDraftLatticeCount
 
 
 
open EisensteinEmbedding ConcreteTraceCRT  
 
 
open scoped LSeries.notation ArithmeticFunction.Moebius
 
 
 
 
 
 
 
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal      
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
open scoped ContDiff    
 
 
 
 
 
 
 
 
 
 
 
 
 
open   Set
 
 
 
 
 
 
 
 

 
namespace SecondPassArithmetic
 

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

end SecondPassArithmetic

namespace CanonicalRowCompletion
 
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation

def progressingCubes (S ) (D ) (H₀ )
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ)) :=
  Q.filter (fun v=>H₀≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ))

end CanonicalRowCompletion

namespace SecondPassArithmetic




 
 
 
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)



end SecondPassArithmetic

end

end OAI
