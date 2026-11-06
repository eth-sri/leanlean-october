module

public import OAI.NumberTheory.DirichletL.RowCompletion.CubicReopening
public import OAI.NumberTheory.DirichletL.RowCompletion.CompletedEnergy

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
 
 
 
 
 
 
 
 

 
namespace CanonicalRowCompletion





 
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation
open ConcreteTraceCRT (eisEmbedding)

end CanonicalRowCompletion

section

 
 
namespace CanonicalRowCompletion
 
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels (primeProductNorm)
open InitialMeanSquare hiding O
open CanonicalCoefficientClass (IsBaseRayTwist)
open ConcreteTraceCRT (eisEmbedding)

end CanonicalRowCompletion

namespace SecondPassIntegration
open   SecondPassArithmetic  

end SecondPassIntegration
end

 
namespace QuadraticAllOddCRT
 
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O
open FiniteGaussPhase hiding O

theorem quadratic_ray_cross (a b : ActualEisensteinCubic.O) (ha : a≠0) (hb : b≠0)
    [(Ideal.span {a}).IsMaximal] [(Ideal.span {b}).IsMaximal]
    (hab : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (hca : ringChar (ActualEisensteinCubic.O⧸Ideal.span {a})≠2)
    (hcb : ringChar (ActualEisensteinCubic.O⧸Ideal.span {b})≠2) :
    quadraticRayValue (residue (a*b))=
      character (Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)*
      character (Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) a)*
      quadraticRayValue (residue a)*quadraticRayValue (residue b) := by
  let p : Bool→ActualEisensteinCubic.O:=fun i=>if i then a else b
  have hp : ∀i,p i≠0:=by
    intro i
    cases i
    · exact hb
    · exact ha
  let (i : Bool) : (Ideal.span {p i}).IsMaximal := by
    cases i <;> dsimp [p] <;> infer_instance
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [p,Function.onFun,isCoprime_comm]
  have hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2 := by
    intro i
    cases i
    · exact hcb
    · exact hca
  have h:=quadraticGamma_product p hp hcop hc
  simp only [quadraticGammaO_eq_rayValue] at h
  have ht : cofactor p true=b:=by
    apply mul_left_cancel₀ ha
    simpa [p] using prime_mul_cofactor p true
  have hf : cofactor p false=a:=by
    apply mul_left_cancel₀ hb
    simpa [p,mul_comm] using prime_mul_cofactor p false
  simp only [Fintype.prod_bool,ht,hf] at h
  simpa [p,mul_comm,mul_left_comm,mul_assoc] using h

theorem quadraticRayValue_ne_zero_of_odd (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : quadraticRayValue r≠0 := by
  rcases r with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [EisensteinEPrimaryPhase.odd,quadraticRayValue,breveGaussianFourTerms_formula,
      zpow_neg,Complex.I_sq,Complex.I_pow_three,Complex.inv_I,ZMod.val] at * <;>
      intro h <;> solve | (have hh:=congrArg Complex.re h; norm_num at hh) | (have hh:=congrArg Complex.im h; norm_num at hh)

end QuadraticAllOddCRT



end OAI
