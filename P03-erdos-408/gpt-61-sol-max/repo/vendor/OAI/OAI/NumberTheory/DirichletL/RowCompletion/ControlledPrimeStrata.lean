module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Eisenstein.ReflectionFibers

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
open   CompletedGauss CanonicalQuadraticSieve  
local notation "Eis" => ActualEisensteinCubic.O

def freePrimaryPrime (I Q) (P:FreePrimeIndex I Q)  := primaryPrime P.val.val

section
variable (I Q:Ideal Eis) (hI:Supported I)
include I Q hI

section
variable (P:FreePrimeIndex I Q)
include P

lemma freePrimaryPrime_ne_zero       :
    freePrimaryPrime I Q P≠0 :=
  primaryPrime_ne_zero P.val.val
    (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

lemma freePrimaryPrime_span       :
    Ideal.span {freePrimaryPrime I Q P}=P.val.val :=
  (primaryPrime_spec P.val.val (freePrimaryPrime_ne_zero I Q hI P)).2.2.1

lemma freePrimaryPrime_primary       :
    lambda^2∣freePrimaryPrime I Q P-1 :=
  (primaryPrime_spec P.val.val (freePrimaryPrime_ne_zero I Q hI P)).2.2.2

lemma freePrimaryPrime_maximal       :
    (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal := by
  rw [freePrimaryPrime_span I Q hI P]
  infer_instance

lemma freePrimaryPrime_good       :
    lambda∉(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) := by
  rw [freePrimaryPrime_span I Q hI P]
  exact (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

end

lemma freePrimaryPrime_coprime     :
    Pairwise (fun P R:FreePrimeIndex I Q =>
      IsCoprime (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) (Ideal.span {freePrimaryPrime I Q R})) := by
  intro P R hPR
  rw [freePrimaryPrime_span I Q hI P,freePrimaryPrime_span I Q hI R]
  exact freePrimeIndex_pairwise_coprime I Q hPR

lemma freePrimaryPrime_coprime_fixed      P  :
    IsCoprime Q (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) := by
  rw [freePrimaryPrime_span I Q hI P]
  exact freePrimeIndex_coprime I Q P

end

end CanonicalRowCompletion

namespace FixedRayActiveSet

theorem fourier_inversion_by_active_set {ι:Type*} [Fintype ι]
    (F:ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (ψ:∀i,AddChar (F i) ℂ) (hψ:∀i,(ψ i).IsPrimitive)
    (φ:∀i,F i→ℂ) (x:∀i,F i) :
    (∏i,φ i (x i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0)*
        (∑v:∀i:A,(F i.val)ˣ,
          (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
            (∏i:A,ψ i.val ((v i:F i.val)*x i.val))) := by
  let f:=fun i (a:F i)=>CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) a*ψ i (a*x i)
  have he: (∑h:∀i,F i,∏i,f i (h i))=∏i,φ i (x i):=by
    rw [←Fintype.prod_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact CubicEisenstein.finiteAdditiveFourier_inversion (ψ i) (hψ i) (φ i) (x i)
  rw [←he,sum_by_active_strata]
  apply Finset.sum_congr rfl
  intro A hA
  rw [sum_active_stratum]
  have hz:(∏i∈(Finset.univ:Finset ι)\A,f i 0)=
      ∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0:=by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [f,zero_mul,AddChar.map_zero_eq_one,mul_one]
  rw [hz,mul_comm]
  congr 1
  rw [show (∑v:∀i:A,(F i.val)ˣ,
      (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
        (∏i:A,ψ i.val ((v i:F i.val)*x i.val)))=
      ∑v:∀i:A,(F i.val)ˣ,∏i:A,f i.val (v i) by
    apply Finset.sum_congr rfl
    intro v hv
    exact (Finset.prod_mul_distrib).symm]
  calc
    _=∏i:A,∑u:(F i.val)ˣ,f i.val (u:F i.val):=
      (Finset.prod_coe_sort A (fun i=>∑u:(F i)ˣ,f i (u:F i))).symm
    _=_:=Fintype.prod_sum (fun (i:A) (u:(F i.val)ˣ)=>f i.val (u:F i.val))

end FixedRayActiveSet

 

namespace CubicEisenstein



open scoped     MatrixGroups

open     CompletedGauss CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma theta_lifted_phase  c   hc   lift n  :
    ShortDraftTrace.breveE (-cuspFrequency n*(eisLam^2*eisEmbedding lift/eisEmbedding c))=
      quotientTrace c hc (Ideal.Quotient.mk _ lift*Ideal.Quotient.mk _ n) := by
  rw [←map_mul]
  simp only [quotientTrace,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency
  rw [map_mul]
  have hc0:=eisEmbedding_ne_zero hc
  have hl:=eisLam_ne_zero
  field_simp
  linear_combination -(eisEmbedding n*eisEmbedding lift)*TraceLambdaPhase.eisLam_sq

section
variable {ι:Type*}
include ι

lemma breveE_finset_sum   (s:Finset ι) (z:ι→ℂ) :
    ShortDraftTrace.breveE (∑i∈s,z i)=∏i∈s,ShortDraftTrace.breveE (z i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty,AddChar.map_zero_eq_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,AddChar.map_add_eq_mul,ih]

lemma ControlledStratumArithmetic.datum_fourier_phase   [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
    (D:ControlledStratumArithmetic p N a0 c0 mode)
     hN  (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
     s 
     hp   hc0   v   n  :
    ShortDraftTrace.breveE (-cuspFrequency n*(D.datum hN hr hbase s hp hc0 v).point)=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        ∏i,quotientTrace (p i) (hp i) ((v i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ n) := by
  rw [D.datum_point]
  have he:-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i))=
      -cuspFrequency n*(eisEmbedding a0/eisEmbedding c0)+
        ∑i,-cuspFrequency n*(eisLam^2*eisEmbedding (D.lift v i)/eisEmbedding (p i)):=by
    simp only [Finset.mul_sum,neg_mul,mul_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he,AddChar.map_add_eq_mul,breveE_finset_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [theta_lifted_phase,D.lift_residue]

end

end CubicEisenstein

 

namespace CompletedGauss
open   CubicEisenstein CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

namespace CubicEisenstein

section
open   CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

end FixedFourierGeometry
end

open   CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

end FixedFourierGeometry
end CubicEisenstein

 

namespace CanonicalRowCompletion
open   CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

section
variable (I Q:Ideal Eis) (hI:Supported I) (c:Eis) (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
include I Q hI c hcQ

lemma freePrimaryPrime_coprime_completion    
       
     P  : IsCoprime ((9:Eis)*c) (freePrimaryPrime I Q P) := by
  have h9:IsCoprime (9:Eis) (freePrimaryPrime I Q P):=
    (ShortDraftCRT.primary_coprime_nine _ (freePrimaryPrime_primary I Q hI P)).symm
  have h9ideal:IsCoprime (Ideal.span {(9:Eis)}:Ideal Eis)
      (Ideal.span {freePrimaryPrime I Q P}):=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr h9
  have hcideal:IsCoprime (Ideal.span {c}:Ideal Eis)
      (Ideal.span {freePrimaryPrime I Q P}):=by
    rw [hcQ]
    exact h9ideal.mul_left (freePrimaryPrime_coprime_fixed I Q hI P)
  exact h9.mul_left ((Ideal.isCoprime_span_singleton_iff _ _).mp hcideal)

theorem exists_freePrimary_controlled_stratum    
       
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex I Q)) :
    Nonempty (ControlledStratumArithmetic
      (fun i:A=>freePrimaryPrime I Q i.val) ((9:Eis)*c) G.a0 G.c0 G.mode) := by
  let : ∀i:A,(Ideal.span {freePrimaryPrime I Q i.val}:Ideal Eis).IsMaximal:=
    fun i=>freePrimaryPrime_maximal I Q hI i.val
  apply exists_controlledStratumArithmetic
    (fun i:A=>freePrimaryPrime I Q i.val)
    (fun i=>freePrimaryPrime_ne_zero I Q hI i.val)
  · intro i j hij
    exact freePrimaryPrime_coprime I Q hI (fun he=>hij (Subtype.ext he))
  · exact fun i=>freePrimaryPrime_primary I Q hI i.val
  · exact G.denominator_ne_zero
  · exact mul_dvd_mul_left 9 G.denominator_dvd
  · exact G.primary
  · exact G.coprime
  solve_by_elim [freePrimaryPrime_coprime_completion]

end

noncomputable def freePrimaryControlledStratum (I Q) (hI:Supported I)
    (c) (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (h) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex I Q))  :=
  Classical.choice (exists_freePrimary_controlled_stratum I Q hI c hcQ h G A)

end CanonicalRowCompletion

end

end OAI
