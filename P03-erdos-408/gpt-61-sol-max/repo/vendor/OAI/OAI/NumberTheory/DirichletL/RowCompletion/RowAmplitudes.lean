module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.GaussSum.ResidualEquivalence

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

section
open   CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)
variable (Q:Ideal Eis) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})))

abbrev activeStratum :=
  freePrimaryControlledStratum D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported c hcQ h G A

end GoodMaskRowData
end
section

open   CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)

end GoodMaskRowData
end

variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def residualActivePrimes (e:α⊕β ≃ γ)  :=
  Finset.univ.image (fun a:α=>e (Sum.inl a))

omit [Fintype β] [Fintype γ] in
lemma residualActivePrimes_not_inr (e:α⊕β ≃ γ)  b  :
    e (Sum.inr b)∉residualActivePrimes e := by
  intro h
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp h
  cases e.injective ha

def nonresidualComplementMap (e:α⊕β ≃ γ) : β → {g:γ // g∉residualActivePrimes e} :=
  fun b=>⟨e (Sum.inr b),residualActivePrimes_not_inr e b⟩

omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementMap_bijective (e:α⊕β ≃ γ) :
    Function.Bijective (nonresidualComplementMap e) := by
  constructor
  · intro a b hab
    exact Sum.inr.inj (e.injective (congrArg Subtype.val hab))
  · intro g
    obtain ⟨x,hx⟩:=e.surjective g.val
    cases x with
    | inl a=>
      exact (g.property (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,hx⟩)).elim
    | inr b=>exact ⟨b,Subtype.ext hx⟩

noncomputable def nonresidualComplementEquiv (e:α⊕β ≃ γ)  :=
  Equiv.ofBijective (nonresidualComplementMap e) (nonresidualComplementMap_bijective e)

omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementEquiv_val (e:α⊕β ≃ γ)  b  :
    (nonresidualComplementEquiv e b).val=e (Sum.inr b) := rfl

omit [Fintype β] [Fintype γ] in
lemma complementActive_image (e:α⊕β ≃ γ) (B:Finset β) :
    (B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val=
      B.image (fun b=>e (Sum.inr b)) := by
  simp only [Finset.map_eq_image,Finset.image_image,Function.comp_def,
    Equiv.toEmbedding_apply,nonresidualComplementEquiv_val]

section
variable (e : α⊕β ≃ γ) (z : γ → ℂ)

lemma inactive_product_nonresidual      B  :
    (∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
      B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)=
      ∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)) := by
  symm
  apply Finset.prod_equiv (nonresidualComplementEquiv e)
  · simp_all
  · intro b hb
    rfl

theorem inactive_weight_nonresidual_subsets    
    (hz:∀a:α,z (e (Sum.inl a))=0) (F:Finset γ → ℂ) :
    (∑A:Finset γ,(∏g∈(Finset.univ:Finset γ)\A,z g)*F A)=
      ∑B:Finset β,(∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)))*
        F (residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))) := by
  have hres:∀g∈residualActivePrimes e,z g=0:=by
    intro g hg
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hg
    exact hz a
  rw [CompletedGauss.inactive_weight_optional_active (residualActivePrimes e) z hres F]
  symm
  apply Fintype.sum_equiv (nonresidualComplementEquiv e).finsetCongr
  intro B
  change _=(∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
    B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)*
    F (residualActivePrimes e∪(B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val)
  rw [inactive_product_nonresidual,complementActive_image]

end

end CanonicalRowCompletion

 

namespace CompletedGauss
open   CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

namespace CubicEisenstein
open   CompletedGauss CompletedDyadic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

end FixedFourierGeometry
end CubicEisenstein

 

namespace CanonicalRowCompletion
open   CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass
open ConcretePrimeRowBridge SecondPassArithmetic
local notation "Eis" => ActualEisensteinCubic.O

lemma normTwistedSource_contDiff  W  (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)  t  :
    ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W t) := by
  have he:(CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t:ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t:=by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  rw [←he]
  exact (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t).smooth ⊤

end CanonicalRowCompletion

 

namespace CompletedGauss.ReflectedBranchData
open   CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
variable {levelBound K:ℝ} {I F Q:Ideal Eis}
variable (d:ReflectedBranchData levelBound K I F Q)
variable (η:ℕ→Ideal Eis→Ideal Eis→ℂ)
variable (σ τ:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
variable (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q))

end CompletedGauss.ReflectedBranchData

 

namespace CanonicalRowCompletion
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def completeActiveSet (e:α⊕β ≃ γ) (B:Finset β)  :=
  residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))

omit [Fintype β] [Fintype γ] in
lemma completeActiveSet_residual (e:α⊕β ≃ γ)  B   a  :
    e (Sum.inl a)∈completeActiveSet e B :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩)

omit [Fintype γ] in
lemma optionalPrimeActive_completeActiveSet (e:α⊕β ≃ γ)  B  :
    optionalPrimeActive e (completeActiveSet e B)=B := by
  ext b
  rw [mem_optionalPrimeActive]
  change e (Sum.inr b)∈residualActivePrimes e∪B.image (fun b=>e (Sum.inr b)) ↔ b∈B
  simp only [Finset.mem_union,residualActivePrimes_not_inr,false_or,Finset.mem_image]
  simp_all

noncomputable def selectedActiveEquiv (e:α⊕β ≃ γ) (B:Finset β) :
    α⊕B ≃ completeActiveSet e B := by
  let t : B ≃ optionalPrimeActive e (completeActiveSet e B):={
    toFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    invFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  exact (Equiv.sumCongr (Equiv.refl _) t).trans
    (activePrimeUnionEquiv e (completeActiveSet e B) (completeActiveSet_residual e B))

end CanonicalRowCompletion

 

namespace CanonicalRowCompletion.ActualFiber
open   CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def maskElement (q:ℕ) (m:Eis)  := m*excludedGenerator (reflectionExcludedPrimes q)
def maskIdeal (q:ℕ) (m:Eis) (F:Ideal Eis)  := Ideal.span {maskElement q m}*F
abbrev RowIndex (q) (m) (rows) (R F) :=
  representativeRowFiber rows R (maskIdeal q m F)

section
variable (q : ℕ) (m : Eis) (hm : m≠0) (F : Ideal Eis)

include hm in
lemma maskElement_ne_zero       : maskElement q m≠0 :=
  mul_ne_zero hm (reflectionExcludedGenerator_ne_zero q)
include hm in
lemma maskIdeal_ne_zero         (hF:F≠0) : maskIdeal q m F≠0 :=
  mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (maskElement_ne_zero q m hm)) hF
lemma mask_bad       : ∀P∈fixedBadPrimes,P∣maskIdeal q m F :=
  reflection_row_mask_bad q m F

end

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)



variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

end CanonicalRowCompletion.ActualFiber

end

end OAI
