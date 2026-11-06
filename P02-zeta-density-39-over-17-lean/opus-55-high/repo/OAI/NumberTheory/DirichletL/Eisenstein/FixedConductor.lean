module
public import OAI.NumberTheory.DirichletL.GaussSum.ReflectionPool
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic
open ActualEisensteinCubic
open ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped Classical SchwartzMap


namespace CubicEisenstein

section
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspLevelBound (c:Eis) : ℝ :=
  243*(Ideal.absNorm (Ideal.span {c}):ℝ)^2

end

section
open scoped Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_traceLambda_pow_four : ramifiedTraceLambda^4=(9:Eis) := by
  apply eisEmbedding_injective
  rw [map_pow,map_ofNat,ramifiedEmbedding_traceLambda]
  calc
    _=(eisLam^2)^2:=by ring
    _=9:=by rw [TraceLambdaPhase.eisLam_sq];norm_num

structure PrincipalStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→ Eis) (N a0 c0:Eis) where
  lift : (∀i,(Eis⧸Ideal.span {p i})ˣ)→ι→ Eis
  lift_period : ∀v i,N^2∣lift v i
  lift_residue : ∀v i,Ideal.Quotient.mk (Ideal.span {p i}) (lift v i)=(v i:Eis⧸Ideal.span {p i})
  U : Eis
  w : Eis
  bezout : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1
  sigma : ∀i,(Eis⧸Ideal.span {p i})ˣ
  epsilon : ∀i,(Eis⧸Ideal.span {p i})ˣ
  sigma_value : ∀i,(sigma i:Eis⧸Ideal.span {p i})=
    Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)
  epsilon_value : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
    (sigma i:Eis⧸Ideal.span {p i})*(epsilon i:Eis⧸Ideal.span {p i})=-1
  gamma : (∀i,(Eis⧸Ideal.span {p i})ˣ)→ levelThree
  numerator : ∀v,(gamma v:SL(2,Eis)) 0 0=finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  denominator : ∀v,(gamma v:SL(2,Eis)) 1 0=c0*∏i,p i
  numerator_fixed : ∀v,(9:Eis)*c0∣(gamma v:SL(2,Eis)) 0 0-(gamma (fun _=>1):SL(2,Eis)) 0 0
  inverse_fixed : ∀v,ramifiedTraceLambda^3*c0∣(gamma v:SL(2,Eis)) 1 1-(gamma (fun _=>1):SL(2,Eis)) 1 1

end

open scoped Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open CubicKubota ShortDraftCusp FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace PrincipalStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→ Eis} {N a0 c0:Eis}

end PrincipalStratumArithmetic

end CubicEisenstein


namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

abbrev BasePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I// Q≤P.val}
abbrev FreePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I// ¬Q≤P.val}

def basePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:BasePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp_all
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

def freePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:FreePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

section
variable (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
include I hI Q
lemma basePrimeRow_norm (n:Eis) :
    ‖basePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:BasePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

lemma basePrimeRow_periodic :
    CanonicalCoefficientClass.FactorsModulo Q (basePrimeRow I hI Q) := by
  intro x y hxy
  change (∏P:BasePrimeIndex I Q,_)=∏P:BasePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  have he:Ideal.Quotient.mk P.val.val x=Ideal.Quotient.mk P.val.val y:=
    Ideal.Quotient.eq.mpr (P.property hxy)
  rw [he]

lemma idealRowHom_fixed_conductor_split (n:Eis) :
    idealRowHom n I=basePrimeRow I hI Q n*freePrimeRow I hI Q n := by
  rw [idealRowHom_eq_prime_count_product I hI n]
  exact (Fintype.prod_subtype_mul_prod_subtype (fun P:PrimeIndex I=>Q≤P.val)
    (fun P:PrimeIndex I=>(actualSextic P.val ((supported_factors_good I hI P.val
      (Multiset.mem_toFinset.mp P.property)).2.1)^((normalizedFactors I).count P.val%6))
      (Ideal.Quotient.mk P.val n))).symm
end

lemma freePrimeIndex_pairwise_coprime (I Q:Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (fun P:FreePrimeIndex I Q=>P.val.val)) := by
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPR (Subtype.ext (Subtype.ext he)))

lemma freePrimeIndex_coprime (I Q:Ideal Eis) (P:FreePrimeIndex I Q) :
    IsCoprime Q P.val.val := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra ht
  have he:P.val.val=Q⊔P.val.val:=
    (show P.val.val.IsMaximal from inferInstance).eq_of_le ht le_sup_right
  exact P.property (le_sup_left.trans he.symm.le)

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def goodMaskMovingIdeal (g r:Eis) : Ideal Eis := (Ideal.span {g})^6*Ideal.span {r}

lemma goodMaskMovingIdeal_supported (g r:Eis)
    (hg:Supported (Ideal.span {g})) (hr:Supported (Ideal.span {r})) :
    Supported (goodMaskMovingIdeal g r) := by
  exact (supported_mul_iff _ _).mpr ⟨supported_pow hg 6,hr⟩

section
variable (P:Ideal Eis)
include P
lemma good_odd_prime_two_not_mem [P.IsMaximal]
    (hodd:ringChar (Eis⧸P)≠2) : (2:Eis)∉P := by
  intro ht
  have he:=maximal_ideal_eq_span_of_mem P inferInstance (2:Eis) twoIdeal_maximal ht
  exact hodd (he ▸ twoIdeal_characteristic)

lemma count_span_eq_zero_of_not_mem (x:Eis) (hx:x∉P) :
    (normalizedFactors (Ideal.span {x})).count P=0 := by
  apply Multiset.count_eq_zero.mpr
  intro hm
  have h0:(Ideal.span {x}:Ideal Eis)≠0:=by
    apply Ideal.span_singleton_eq_bot.not.mpr
    intro he
    exact hx (he ▸ P.zero_mem)
  exact hx (Ideal.dvd_span_singleton.mp
    ((UniqueFactorizationMonoid.mem_normalizedFactors_iff h0).mp hm).2)

lemma good_factor_count [P.IsMaximal]
    (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    (normalizedFactors (Ideal.span {u.val*lambda^a*(2:Eis)^b*r})).count P=
      (normalizedFactors (Ideal.span {r})).count P := by
  have hl:(Ideal.span {lambda}:Ideal Eis)≠0:=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have ht:(Ideal.span {(2:Eis)}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hcl:=count_span_eq_zero_of_not_mem P lambda hgood
  have hct:=count_span_eq_zero_of_not_mem P 2 (good_odd_prime_two_not_mem P hodd)
  rw [show u.val*lambda^a*(2:Eis)^b*r=u.val*(lambda^a*(2:Eis)^b*r) by ring,
    Ideal.span_singleton_mul_left_unit u.isUnit,
    ←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_pow,←Ideal.span_singleton_pow,
    normalizedFactors_mul (mul_ne_zero (pow_ne_zero _ hl) (pow_ne_zero _ ht)) hr.1,
    normalizedFactors_mul (pow_ne_zero _ hl) (pow_ne_zero _ ht)]
  pm_545 Multiset.count_add normalizedFactors_pow Multiset.count_nsmul hcl hct mul_zero zero_add
end

theorem goodMaskMovingIdeal_count (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P=
      6*(normalizedFactors (Ideal.span {m})).count P+
        4*(normalizedFactors F).count P+(normalizedFactors I).count P := by
  have hmc:(normalizedFactors (Ideal.span {m})).count P=(normalizedFactors (Ideal.span {g})).count P:=by
    rw [hm]
    exact good_factor_count P hgood hodd um am bm g hg
  have hrc:(normalizedFactors (Ideal.span {r})).count P=
      4*(normalizedFactors F).count P+(normalizedFactors I).count P:=by
    have hh:=good_factor_count P hgood hodd u a b r hr
    rw [←hx,←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,hf,hz,
      normalizedFactors_mul (pow_ne_zero 4 hF) hI] at hh
    simpa only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul] using hh.symm
  rw [goodMaskMovingIdeal,normalizedFactors_mul (pow_ne_zero 6 hg.1) hr.1]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,←hmc,hrc]
  omega

lemma squarefree_prime_count_indicator (F P:Ideal Eis) (hF:Squarefree F) (hP:Prime P) :
    (normalizedFactors F).count P=if P∣F then 1 else 0 := by
  have hle:=Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hF.ne_zero).mp hF) P
  by_cases hPF:P∣F
  · rw [ite_eq_left hPF]
    have hp:=Multiset.count_pos.mpr
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mpr ⟨hP,hPF⟩)
    omega
  · rw [ite_eq_right hPF]
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hPF ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mp hm).2

theorem goodMaskMovingIdeal_exponent (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P%6=completedLocalExponent I F P := by
  rw [goodMaskMovingIdeal_count I F hI hF.ne_zero m f z hf hz um am bm g hg hm u a b r hr hx P hgood hodd,
    squarefree_prime_count_indicator F P hF (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance)]
  unfold completedLocalExponent
  omega

end CanonicalRowCompletion

end

end OAI
