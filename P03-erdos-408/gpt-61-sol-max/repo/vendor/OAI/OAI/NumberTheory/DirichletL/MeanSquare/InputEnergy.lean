module

public import OAI.NumberTheory.DirichletL.Eisenstein.DirichletForm

@[expose] public section

namespace OAI



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
 
 
 
 
 

 
namespace InitialMeanSquare
open   ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm columnLog)

section
variable (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (S : Finset (primePool F))
include F hF S

theorem poolProduct_admissible    
      : Admissible (∏ i ∈ S,i.val) := by
  have hp (i : primePool F) : Prime i.val :=
    Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏ i ∈ S,i.val) ≠ (0 : Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  refine ⟨hn, ?_, ?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (Ideal.isCoprime_of_isMaximal (fun he => hij (Subtype.ext he))).isRelPrime
    · intro i hi
      exact (hp i).squarefree
  · intro P hP
    obtain ⟨hprime, hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
    obtain ⟨i, hi, hPi⟩ := (hprime.dvd_finsetProd_iff (fun i : primePool F => i.val)).mp hdiv
    have he : P=i.val := (prime_dvd_prime_iff_eq hprime (hp i)).mp hPi
    rw [he]
    exact ⟨poolGood F hF i, poolOdd F hF i⟩

theorem poolPrimary_norm    
      :
    primeProductNorm (poolPrimary F) S = (Ideal.absNorm (∏ i ∈ S,i.val) : ℝ) := by
  rw [primeProductNorm, eisEmbedding_norm_sq_eq_absNorm_span, FiniteGaussPhase.span_finset_prod]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact poolPrimary_span F hF i

end

end InitialMeanSquare

 
namespace SecondPassArithmetic





 
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

end SecondPassArithmetic

 
 
namespace SecondPassArithmetic
 
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

end SecondPassArithmetic

 
 
namespace SecondPassArithmetic
 
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})



end SecondPassArithmetic



end OAI
