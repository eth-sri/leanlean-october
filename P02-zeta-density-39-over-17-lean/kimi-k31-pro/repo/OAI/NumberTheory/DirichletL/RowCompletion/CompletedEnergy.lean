module
public import OAI.NumberTheory.DirichletL.Eisenstein.UnitNormalization

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCoefficientClass (IsBaseRayTwist)

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

lemma embedding_lambda_ne_zero : eisEmbedding lambda≠0 :=
  by
    intro hz
    apply PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
    apply ConcreteTraceCRT.eisEmbedding_injective
    simpa only [map_zero] using hz

end

section
open ActualEisensteinCubic CompletedDyadic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)

end

open ActualEisensteinCubic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)

def paperLambda : ActualEisensteinCubic.O := 1+2*omega

def paperLambdaUnit : ActualEisensteinCubic.Oˣ where
  val := -omega
  inv := -omega^2
  val_inv := by
    calc
      (-omega)*(-omega^2)=omega^3:=by ring
      _=1:=omega_primitive.pow_eq_one
  inv_val := by
    calc
      (-omega^2)*(-omega)=omega^3:=by ring
      _=1:=omega_primitive.pow_eq_one

lemma paperLambda_eq : paperLambda=paperLambdaUnit.val*lambda := by
  change 1+2*omega=(-omega)*lambda
  change (1+2*omega:ActualEisensteinCubic.O)=(-omega)*(omega-1)
  have hw:=omega_primitive.geom_sum_eq_zero (by decide : 1<(3:ℕ))
  norm_num [Finset.sum_range_succ] at hw
  linear_combination hw

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalCubeSeparation

end CanonicalCubeSeparation

namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

end CanonicalRowCompletion

namespace CanonicalCubeSeparation

end CanonicalCubeSeparation

open scoped BigOperators Classical
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisTraceModChar finite_quotient_span)
open FiniteGaussPhase hiding O

def character (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : MulChar (ActualEisensteinCubic.O⧸P) ℂ := by
  letI : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  letI : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  exact (quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ℂ)

theorem normalized_prime_eq_square_sum (p : ActualEisensteinCubic.O) (hp : p≠0)
    [(Ideal.span {p}).IsMaximal] (hc : ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2) :
    ConcreteBreveE.normalizedTraceGauss p hp (character (Ideal.span {p}))=
      quadraticGammaO p hp := by
  let : Field (ActualEisensteinCubic.O⧸Ideal.span {p}):=Ideal.Quotient.field _
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {p}):=Fintype.ofFinite _
  let ψ:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates p hp
  have hψ:ψ≠1:=by
    have hprim:=GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
    simpa only [AddChar.mulShift_one] using hprim (a:=1) one_ne_zero
  change gaussSum (character (Ideal.span {p})) ψ/(‖eisEmbedding p‖:ℂ)=
    (∑x:ActualEisensteinCubic.O⧸Ideal.span {p},ψ (x^2))/(‖eisEmbedding p‖:ℂ)
  congr 1
  exact ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase ψ hc hψ

theorem normalized_product_eq_square_sum {ι : Type*} [Fintype ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2) :
    normalizedProductTraceGauss p hp hcop (fun i=>character (Ideal.span {p i}))=
      quadraticGammaO (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)) := by
  let c:=∏i,p i
  have hc0:c≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {c}):=finite_quotient_span hc0
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {c}):=Fintype.ofFinite _
  let (i:ι) : Fintype (ActualEisensteinCubic.O⧸Ideal.span {p i}):=Fintype.ofFinite _
  let (i:ι) : Field (ActualEisensteinCubic.O⧸Ideal.span {p i}):=Ideal.Quotient.field _
  let e:=productElementCRT p hcop
  let ψ:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0
  change (∑x:ActualEisensteinCubic.O⧸Ideal.span {c},(∏i,character (Ideal.span {p i}) (e x i))*ψ x)/(‖eisEmbedding c‖:ℂ)=
    (∑x:ActualEisensteinCubic.O⧸Ideal.span {c},ψ (x^2))/(‖eisEmbedding c‖:ℂ)
  congr 1
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i=>ActualEisensteinCubic.O⧸Ideal.span {p i}) e ψ (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0) hc

theorem quadraticGamma_product {ι : Type*} [Fintype ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2) :
    quadraticGammaO (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))=
      ∏i,character (Ideal.span {p i}) (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i))*
        quadraticGammaO (p i) (hp i) := by
  rw [←normalized_product_eq_square_sum p hp hcop hc,normalizedProductTraceGauss_crt]
  apply Finset.prod_congr rfl
  intro i hi
  rw [normalized_prime_eq_square_sum _ _ (hc i)]

end QuadraticAllOddCRT

end

end OAI
