module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.GaussSum.FixedRayFibers

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
 
 
 
 
 
 
 
 

namespace CubicEisenstein

section
open scoped       MatrixGroups

open   CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal  
open LocalReflectionBrackets ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

end FixedFourierGeometry
end

open   CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

 

namespace CompletedGauss
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def mandatoryActiveEquiv (R:Finset ι) :
    {A:Finset ι // R⊆A}≃Finset {i:ι // i∉R} where
  toFun A:=A.val.subtype (fun i=>i∉R)
  invFun B:=⟨R∪B.image Subtype.val,Finset.subset_union_left⟩
  left_inv A:=by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_union,Finset.mem_image,Finset.mem_subtype]
    constructor
    · grind
    · intro hi
      by_cases hr:i∈R
      · exact Or.inl hr
      · exact Or.inr ⟨⟨i,hr⟩,hi,rfl⟩
  right_inv B:=by
    grind

section
variable (R : Finset ι) (z : ι→ℂ) (hz : ∀i∈R,z i=0) (F : Finset ι→ℂ)


lemma sum_mandatory_active {V:Type*} [AddCommMonoid V]
    (R:Finset ι) (F:Finset ι→V) (hz:∀A,¬R⊆A→F A=0) :
    (∑A:Finset ι,F A)=
      ∑B:Finset {i:ι // i∉R},F (R∪B.image Subtype.val) := by
  calc
    _=∑A:Finset ι,if R⊆A then F A else 0:=by
      grind
    _=∑A:{A:Finset ι // R⊆A},F A.val:=by
      rw [←Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (fun A:Finset ι=>R⊆A)) (by simp) F
    _=_:=by
      apply Fintype.sum_equiv (mandatoryActiveEquiv R)
      intro A
      exact congrArg F (congrArg Subtype.val ((mandatoryActiveEquiv R).left_inv A)).symm

include hz in
theorem inactive_weight_mandatory_active    
        :
    (∑A:Finset ι,(∏i∈(Finset.univ:Finset ι)\A,z i)*F A)=
      ∑B:Finset {i:ι // i∉R},
        (∏i∈(Finset.univ:Finset ι)\(R∪B.image Subtype.val),z i)*
          F (R∪B.image Subtype.val) := by
  apply sum_mandatory_active R
  intro A hA
  have hex:∃i∈R,i∉A:=by
    by_contra! hn
    exact hA hn
  obtain ⟨i,hi,hni⟩:=hex
  have hm:i∈(Finset.univ:Finset ι)\A:=by simp [hni]
  rw [Finset.prod_eq_zero hm (hz i hi),zero_mul]

lemma inactive_product_complement    
     B  :
    (∏i∈(Finset.univ:Finset ι)\(R∪B.image Subtype.val),z i)=
      ∏i∈(Finset.univ:Finset {i:ι // i∉R})\B,z i.val := by
  symm
  apply Finset.prod_bij (fun i _=>i.val)
  · simp_all
  · intro i hi j hj he
    exact Subtype.ext he
  · aesop
  · intro i hi
    rfl

include hz in
theorem inactive_weight_optional_active    
        :
    (∑A:Finset ι,(∏i∈(Finset.univ:Finset ι)\A,z i)*F A)=
      ∑B:Finset {i:ι // i∉R},
        (∏i∈(Finset.univ:Finset {i:ι // i∉R})\B,z i.val)*
          F (R∪B.image Subtype.val) := by
  rw [inactive_weight_mandatory_active R z hz F]
  apply Finset.sum_congr rfl
  intro B hB
  rw [inactive_product_complement]

end

end CompletedGauss

namespace CanonicalRowCompletion
open   CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
local notation "Eis" => ActualEisensteinCubic.O

section
variable (q : ℕ) (hq : q≠0) (m : Eis) (F I P : Ideal Eis)


lemma excluded_prime_dvd_row_mask      
    (hP:P∈reflectionExcludedPrimes q) :
    P∣Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F := by
  apply dvd_mul_of_dvd_left
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_le.mpr
  exact Set.singleton_subset_iff.mpr (P.mul_mem_left m (excludedGenerator_mem _ hP))

lemma residual_prime_not_excluded       (hP:Prime P)
    (hres:P∣rowResidualPart I (Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F)) :
    P∉reflectionExcludedPrimes q := by
  intro hmem
  have hn:¬P∣Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F:=
    ((prime_dvd_rowResidualPart_iff _ _ P hP).mp hres).2
  exact hn (excluded_prime_dvd_row_mask q m F P hmem)

include hq in
lemma residual_coprime_fixed_conductor         :
    IsCoprime (Ideal.span {reflectionConductor q})
      (rowResidualPart I (Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F)) := by
  let Q:=Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))
    (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp
  apply Finset.disjoint_left.mpr
  intro P hfixed hres
  have hp:Prime P:=support_prime hfixed
  have hd:P∣Ideal.span {reflectionConductor q}:=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hfixed)
  have hr:P∣rowResidualPart I Q:=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hres)
  exact residual_prime_not_excluded q m F I P hp hr (reflectionConductor_prime_mem q hq P hp hd)

end

end CanonicalRowCompletion

 

namespace CompletedGauss

section
open   CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

def representativeRowFiber (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)  :=
  completedRowFiber rows Q (rowPowerfulPart I) (rowMaskPart I Q)

def reconstructFiberRow (I Q k:Ideal Eis)  :=
  rowPowerfulPart I*rowMaskPart I Q*k

section
variable (rows : Finset (Ideal Eis)) (I Q J : Ideal Eis)


lemma reconstructFiberRow_of_original    
    (hJ:J∈representativeRowFiber rows I Q) (hJ0:J≠0) :
    reconstructFiberRow I Q (rowResidualPart J Q)=J := by
  obtain ⟨_,hA,hT⟩:=Finset.mem_filter.mp hJ
  rw [reconstructFiberRow,←hA,←hT]
  exact row_powerful_mask_residual_product J Q hJ0

lemma representativeRowFiber_injective    
    (hrows:∀J∈rows,J≠0) :
    Set.InjOn (fun J=>rowResidualPart J Q) (representativeRowFiber rows I Q) :=
  rowResidualPart_injective_on_fiber rows Q (rowPowerfulPart I) (rowMaskPart I Q) hrows

end

end

open   CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

 

namespace CompletedGauss.FreeReflection
open   CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection

end

end OAI
