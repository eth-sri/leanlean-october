module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.ChineseRemainder.FrequencyLifts

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
 
 
 
 
 
 
 
 

 

namespace CanonicalRowCompletion
open   CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

section
variable (u : Eisˣ) (a b : ℕ) (r : Eis) (hr : Supported (Ideal.span {r})) (Ψ : Eis→*ℂ) (m f z n : Eis) (hmLam : lambda∣m) (hm2 : (2:Eis)∣m) (hn : ¬Supported (Ideal.span {n}))


include hn in
lemma numeratorBadTwist_zero_of_not_supported      
          :
    numeratorBadTwist u a b r hr n=0 := by
  have hu:unitSupplement u n=0:=by
    change (if Supported (Ideal.span {n}) then _ else 0)=0
    rw [ite_eq_right hn]
  change ((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n=0
  rw [hu,zero_mul,zero_mul,zero_mul]

include hmLam hm2 hn in
lemma rowTwist_zero_of_not_supported    
          :
    rowTwist Ψ m f z n=0 := by
  have hu:unitSupplement (1:Eisˣ) n=0:=by
    change (if Supported (Ideal.span {n}) then _ else 0)=0
    rw [ite_eq_right hn]
  have h:=congrArg (fun T:Eis→*ℂ=>T n) (rowTwist_unitSupplement Ψ m f z (1:Eisˣ) hmLam hm2)
  simp_all

end

def actualPeriodicRow (Ψ:Eis→*ℂ) (m:Eis) (u:Eisˣ) (a b:ℕ) (r)
    (hr:Supported (Ideal.span {r}))  :=
  Ψ * coprimalityMask m * numeratorBadTwist u a b r hr * movingNumeratorRow r hr

lemma actualPeriodicRow_norm  Ψ  (hΨ:∀n,‖Ψ n‖≤1)
     m   u   a b   r   hr   n  :
    ‖actualPeriodicRow Ψ m u a b r hr n‖≤1 := by
  change ‖((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n‖≤1
  simp only [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
    (hΨ n)).trans (coprimalityMask_norm m n))).trans (numeratorBadTwist_norm u a b r hr n))).trans
    (movingNumeratorRow_norm r hr n)

section
variable (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hQ : Q≠0) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm : ∀n,‖Ψ n‖≤1) (m f z : Eis) (hm : m≠0) (hf : f≠0) (hz : z≠0) (hmLam : lambda∣m) (hm2 : (2:Eis)∣m) (u : Eisˣ) (a b : ℕ) (r : Eis) (hr : Supported (Ideal.span {r}))


include hΨ in
lemma actualPeriodicRow_periodic    
     
              :
    CanonicalCoefficientClass.FactorsModulo
      (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})
      (actualPeriodicRow Ψ m u a b r hr) := by
  intro x y hxy
  have hQ:x-y∈Q:=Ideal.mul_le_left (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hm:x-y∈Ideal.span {m}:=Ideal.mul_le_right (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have h72:x-y∈Ideal.span {(72:Eis)}:=Ideal.mul_le_right (Ideal.mul_le_left hxy)
  have hrxy:x-y∈Ideal.span {r}:=Ideal.mul_le_right hxy
  change ((Ψ x*coprimalityMask m x)*numeratorBadTwist u a b r hr x)*movingNumeratorRow r hr x=
    ((Ψ y*coprimalityMask m y)*numeratorBadTwist u a b r hr y)*movingNumeratorRow r hr y
  rw [hΨ x y hQ,coprimalityMask_periodic m x y hm,numeratorBadTwist_periodic u a b r hr x y h72,
    movingNumeratorRow_periodic r hr x y hrxy]

include hmLam hm2 in
theorem rowTwist_eq_actualPeriodicRow_primary    
             
      (hpr:lambda^2∣r-1)
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
     n  (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=actualPeriodicRow Ψ m u a b r hr n := by
  by_cases hn:Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ m f z n hn,hx,
      idealRowHom_factor_numerator u a b r n hr hpr hn hpn]
    change _=((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n
    ring
  · rw [rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]
    change 0=((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n
    simp_all [numeratorBadTwist_zero_of_not_supported]

include hQ hΨ hΨnorm hm hf hz hmLam hm2 in
theorem exists_actual_periodic_row    
         
                :
    ∃(u:Eisˣ)(a b:ℕ)(r:Eis)(hr:Supported (Ideal.span {r})),
      lambda^2∣r-1 ∧ f^4*z=u.val*lambda^a*(2:Eis)^b*r ∧
      (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})≠0 ∧
      CanonicalCoefficientClass.FactorsModulo
        (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})
        (actualPeriodicRow Ψ m u a b r hr) ∧
      (∀n,‖actualPeriodicRow Ψ m u a b r hr n‖≤1) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=actualPeriodicRow Ψ m u a b r hr n) := by
  obtain ⟨u,a,b,r,hr,hpr,hx⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  refine ⟨u,a,b,r,hr,hpr,hx,?_,actualPeriodicRow_periodic Ψ Q hΨ m u a b r hr,
    actualPeriodicRow_norm Ψ hΨnorm m u a b r hr,?_⟩
  · exact mul_ne_zero (mul_ne_zero ((by simp_all))
      (by simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot];norm_num)) hr.1
  solve_by_elim [rowTwist_eq_actualPeriodicRow_primary]

end

end CanonicalRowCompletion

namespace CompletedGauss

section
open   IdealMobiusDivisorSum  
local notation "Eis" => ActualEisensteinCubic.O

def completedReflectionPool (I Q:Ideal Eis)  :=
  (primeSupport (I*Q)).filter (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2 ∧ ¬P∣rowResidualPart I Q)

lemma mem_completedReflectionPool  I Q P  (hI:I≠0) (hQ:Q≠0) :
    P∈completedReflectionPool I Q ↔
      Prime P ∧ P∣I*Q ∧ lambda∉P ∧ ringChar (Eis⧸P)≠2 ∧ ¬P∣rowResidualPart I Q := by
  simp only [completedReflectionPool,Finset.mem_filter,primeSupport,Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff (mul_ne_zero hI hQ)]
  aesop

section
variable (I J F Q : Ideal Eis) (hI : I≠0) (hJ : J≠0) (hQ : Q≠0) (hA : rowPowerfulPart I=rowPowerfulPart J) (hT : rowMaskPart I Q=rowMaskPart J Q) (P : completedReflectionPool I Q)


lemma completedReflectionPool_maximal     :
    P.val.IsMaximal := by
  have hm: P.val∈normalizedFactors (I*Q):=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp P.property).1
  have hp:=prime_of_normalized_factor P.val hm
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

lemma completedReflectionPool_good     :
    lambda∉P.val := (Finset.mem_filter.mp P.property).2.1

lemma completedReflectionPool_odd     :
    ringChar (Eis⧸P.val)≠2 := (Finset.mem_filter.mp P.property).2.2.1

lemma completedReflectionPool_nonresidual     :
    ¬P.val∣rowResidualPart I Q := (Finset.mem_filter.mp P.property).2.2.2

include hI hQ in
lemma completedReflectionPool_divides      
      : P.val∣I*Q :=
  ((mem_completedReflectionPool I Q P.val hI hQ).mp P.property).2.1

include hI hJ hQ hA hT in
theorem completedReflectionPool_eq_on_fiber  
         
     
      :
    completedReflectionPool I Q=completedReflectionPool J Q := by
  ext P
  rw [mem_completedReflectionPool I Q P hI hQ,mem_completedReflectionPool J Q P hJ hQ]
  constructor
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivJ,hresJ,_⟩:=nonresidual_prime_transport I J 1 Q P hI hJ hP hA hT hdiv hres
    exact ⟨hP,hdivJ,hgood,hodd,hresJ⟩
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivI,hresI,_⟩:=nonresidual_prime_transport J I 1 Q P hJ hI hP hA.symm hT.symm hdiv hres
    exact ⟨hP,hdivI,hgood,hodd,hresI⟩

include hI hJ hQ hA hT in
lemma completedReflectionPool_exponent_eq  
         
     
     
      :
    completedLocalExponent I F P.val=completedLocalExponent J F P.val := by
  rcases (mem_completedReflectionPool I Q P.val hI hQ).mp P.property with
    ⟨hP,hdiv,_,_,hres⟩
  exact (nonresidual_prime_transport I J F Q P.val hI hJ hP hA hT hdiv hres).2.2

end

end





open   CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O




end CompletedGauss

end

end OAI
