module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Eisenstein.IntegralCover

@[expose] public section

namespace OAI

noncomputable section

namespace CubicEisenstein

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
 
 
 
 
 
 
 
 

section
 
open scoped       MatrixGroups Pointwise ENNReal InnerProductSpace
 

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverSheet_measure  H K   q 
     S  (hS : MeasurableSet S) :
    hyperbolicVolume ((integralOrbitProjection K) ⁻¹' S ∩ integralCoverSheet H K q)=
      integralQuotientVolume K S := by
  have he : (integralOrbitProjection K) ⁻¹' S ∩ integralCoverSheet H K q=
      (fun w=>integralCoverRep H K q • w) ⁻¹'
        ((integralOrbitProjection K) ⁻¹' S ∩ hyperbolicFundamentalSet K) := by
    ext w
    change (integralOrbitProjection K w∈S ∧ integralCoverRep H K q•w∈hyperbolicFundamentalSet K) ↔
      (integralOrbitProjection K (integralCoverRep H K q•w)∈S ∧
        integralCoverRep H K q•w∈hyperbolicFundamentalSet K)
    rw [integralSubgroup_smul,integralOrbitProjection_eq]
  rw [he,measure_preimage_smul]
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection K) hS,
    Measure.restrict_apply ((measurable_integralOrbitProjection K) hS)]

section
variable {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
include H K hHK hK

theorem integralCoverMap_measure  
          :
    Measure.map (integralCoverMap hHK) (integralQuotientVolume H)=
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hH : H≤CubicKubota.levelThree := hHK.trans hK
  rw [←integralQuotientVolume_independent H hH (integralCoverDomain H K)
    (integralCoverDomain_isFundamentalDomain hHK hK)]
  rw [Measure.map_map (integralCoverMap_measurable hHK) (measurable_integralOrbitProjection H)]
  change Measure.map (integralOrbitProjection K) (hyperbolicVolume.restrict (integralCoverDomain H K))=_
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (measurable_integralOrbitProjection K) hS,
    Measure.restrict_apply ((measurable_integralOrbitProjection K) hS),Measure.smul_apply,smul_eq_mul]
  rw [integralCoverDomain,Set.inter_iUnion]
  rw [measure_iUnion]
  · simp_rw [integralCoverSheet_measure H K _ S hS]
    simp_all [Subgroup.relIndex, Subgroup.index]
  · intro q r hqr
    exact (integralCoverSheet_pairwiseDisjoint H K hK hqr).mono Set.inter_subset_right Set.inter_subset_right
  · intro q
    exact ((measurable_integralOrbitProjection K) hS).inter (integralCoverSheet_measurable H K q)

lemma integralCoverMap_measurePreserving  
          :
    MeasurePreserving (integralCoverMap hHK) (integralQuotientVolume H)
      ((H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) :=
  ⟨integralCoverMap_measurable hHK,integralCoverMap_measure hHK hK⟩

end

end

section
 
open scoped       MatrixGroups Pointwise ENNReal InnerProductSpace InnerProduct
 

section
local notation "O" => ActualEisensteinCubic.O

abbrev IntegralQuotientL2 (H ) :=
  Lp ℂ 2 (integralQuotientVolume H)

def integralCoverPullback {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]  :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp : (H.relIndex K:ℝ≥0∞)≠⊤) le_rfl)

section
variable {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
include H K hHK hK

section
variable (F : IntegralQuotientL2 K)
include F

theorem integralCoverPullback_ae  
         
      :
    integralCoverPullback hHK hK F=ᵐ[integralQuotientVolume H]
      fun q=>F (integralCoverMap hHK q) := by
  have hm := integralCoverMap_measurePreserving hHK hK
  have he := dominatedComplexL2_ae
    (by simp : (H.relIndex K:ℝ≥0∞)≠⊤)
    (le_rfl : (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K≤
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) F
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans
    (hm.quasiMeasurePreserving.ae_eq_comp he)

theorem integralCoverPullback_norm_le  
         
      :
    ‖integralCoverPullback hHK hK F‖≤(H.relIndex K:ℝ)^((1:ℝ)/2)*‖F‖ := by
  change ‖Lp.compMeasurePreserving (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)
    (dominatedComplexL2 (by simp : (H.relIndex K:ℝ≥0∞)≠⊤) le_rfl F)‖≤_
  rw [Lp.norm_compMeasurePreserving]
  simpa only [ENNReal.toReal_natCast] using dominatedComplexL2_norm_le
    (by simp : (H.relIndex K:ℝ≥0∞)≠⊤)
    (le_rfl : (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K≤
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) F

def integralCoverTrace {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]  :=
  ContinuousLinearMap.adjoint (integralCoverPullback hHK hK)

theorem integralCoverTrace_pairing  
         
       G  :
    ⟪F,integralCoverTrace hHK hK G⟫_ℂ=⟪integralCoverPullback hHK hK F,G⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right _ _ _

end

theorem integralCoverPullback_opNorm_le  
          :
    ‖integralCoverPullback hHK hK‖≤(H.relIndex K:ℝ)^((1:ℝ)/2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact integralCoverPullback_norm_le hHK hK

theorem integralCoverTrace_opNorm_le  
          :
    ‖integralCoverTrace hHK hK‖≤(H.relIndex K:ℝ)^((1:ℝ)/2) := by
  rw [integralCoverTrace,ContinuousLinearMap.adjoint.norm_map]
  exact integralCoverPullback_opNorm_le hHK hK

end

end

local notation "O" => ActualEisensteinCubic.O

def integralCoverFiberPoint (H K )
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace)  :=
  Quotient.liftOn' q (fun r : K=>integralOrbitProjection H (r⁻¹•w)) (by
    intro a b hab
    have hh : b⁻¹*a∈H.subgroupOf K := by
      have h : a⁻¹*b∈H.subgroupOf K := QuotientGroup.leftRel_apply.mp hab
      simpa only [mul_inv_rev,inv_inv] using (H.subgroupOf K).inv_mem h
    apply Quotient.sound
    refine ⟨⟨((b⁻¹*a:K):SL(2,ActualEisensteinCubic.O)),hh⟩,?_⟩
    change (b⁻¹*a)•(a⁻¹•w)=b⁻¹•w
    simp only [mul_smul,smul_inv_smul])

section
variable (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
include H K

lemma integralCoverFiberPoint_mk  
    (r : K)  w  :
    integralCoverFiberPoint H K r w=integralOrbitProjection H (r⁻¹•w) := rfl

section
variable (q : IntegralCoverCosets H K)
include q

lemma integralCoverFiberPoint_rep  
       w  :
    integralCoverFiberPoint H K q w=
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹•w) := by
  conv_lhs => rw [←QuotientGroup.out_eq' q]
  rfl

lemma integralCoverFiberPoint_smul  
      (k : K)  w  :
    integralCoverFiberPoint H K (k•q) (k•w)=integralCoverFiberPoint H K q w := by
  induction q using Quotient.inductionOn with
  | _ r =>
    change integralOrbitProjection H ((k*r)⁻¹•(k•w))=integralOrbitProjection H (r⁻¹•w)
    rw [mul_inv_rev,mul_smul,inv_smul_smul]

lemma integralCoverFiberPoint_measurable  
      : Measurable (integralCoverFiberPoint H K q) := by
  have he : integralCoverFiberPoint H K q=fun w=>
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹•w) :=
    funext (integralCoverFiberPoint_rep H K q)
  rw [he]
  exact (measurable_integralOrbitProjection H).comp (measurable_const_smul _)

end

def integralCoverTraceLift (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (w : HyperbolicSpace)  :=
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  ∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)

section
variable [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H→ℂ)
include f

lemma integralCoverTraceLift_smul    
      (k : K)  w  :
    integralCoverTraceLift H K f (k•w)=integralCoverTraceLift H K f w := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  unfold integralCoverTraceLift
  rw [←(MulAction.bijective k).sum_comp (fun q=>f (integralCoverFiberPoint H K q (k•w)))]
  simp only [integralCoverFiberPoint_smul]

def integralCoverTraceFunction (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) : IntegralOrbitQuotient K→ℂ :=
  Quotient.lift (integralCoverTraceLift H K f) (by
    rintro w u ⟨k,rfl⟩
    exact (integralCoverTraceLift_smul H K f k w).symm)

lemma integralCoverTraceFunction_measurable    
      (hf : Measurable f) :
    Measurable (integralCoverTraceFunction H K f) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply measurable_from_quotient.mpr
  change Measurable (integralCoverTraceLift H K f)
  unfold integralCoverTraceLift
  exact Finset.measurable_sum Finset.univ (fun q _=>hf.comp (integralCoverFiberPoint_measurable H K q))

end

end

end

section
 
open scoped       MatrixGroups Pointwise ENNReal
 

local notation "O" => ActualEisensteinCubic.O

def IntegralCoverIntertwines {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ))  :=
  ∀h : H,g*integralComplexMatrix (h:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (e h:SL(2,ActualEisensteinCubic.O))*g

section
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))} (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
include H J e g he

lemma integralCoverIntertwines_action  
         
    (h : H) (w : HyperbolicSpace) : g•(h•w)=(e h)•(g•w) := by
  rw [integralSubgroup_smul,integralSubgroup_smul,←mul_smul,he, mul_smul]

lemma integralCoverIntertwines_inverse  
          :
    IntegralCoverIntertwines e.symm g⁻¹ := by
  intro j
  have hh := he (e.symm j)
  rw [e.apply_symm_apply] at hh
  have hh' := congrArg (fun A : SL(2,ℂ)=>g⁻¹*A*g⁻¹) hh
  simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh'.symm

def integralConjugateMap {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g ) (he : IntegralCoverIntertwines e g) :
    IntegralOrbitQuotient H→IntegralOrbitQuotient J :=
  Quotient.map' (fun w=>g•w) (by
    rintro w u ⟨h,rfl⟩
    exact ⟨e h,(integralCoverIntertwines_action e g he h w).symm⟩)

lemma integralConjugateMap_projection  
           w  :
    integralConjugateMap e g he (integralOrbitProjection H w)=
      integralOrbitProjection J (g•w) := rfl

lemma integralConjugateMap_measurable  
          :
    Measurable (integralConjugateMap e g he) := by
  apply measurable_from_quotient.mpr
  exact (measurable_integralOrbitProjection J).comp (measurable_const_smul g)

lemma integralConjugateMap_continuous  
          :
    Continuous (integralConjugateMap e g he) :=
  (continuous_hyperbolic_action g).quotient_map' _

lemma integralConjugateMap_inverse  
         
     q  :
    integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
      (integralConjugateMap e g he q)=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection H (g⁻¹•(g•w))=integralOrbitProjection H w
    rw [inv_smul_smul]

def integralConjugateHomeomorph {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    IntegralOrbitQuotient H≃ₜIntegralOrbitQuotient J where
  toFun := integralConjugateMap e g he
  invFun := integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
  left_inv := integralConjugateMap_inverse e g he
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ w =>
      change integralOrbitProjection J (g•(g⁻¹•w))=integralOrbitProjection J w
      rw [smul_inv_smul]
  continuous_toFun := integralConjugateMap_continuous e g he
  continuous_invFun := integralConjugateMap_continuous e.symm g⁻¹ _

section
variable (hH : H≤CubicKubota.levelThree)
include hH

lemma integralConjugate_fundamentalDomain  
         
      :
    IsFundamentalDomain J ((fun w : HyperbolicSpace=>g•w) '' hyperbolicFundamentalSet H)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain H hH).image_of_equiv
    (MulAction.toPerm g)
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm g).symm
      hyperbolicVolume hyperbolicVolume from
      (measurePreserving_smul g⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    e.symm.toEquiv
  intro j w
  change g•(e.symm j•w)=j•(g•w)
  simpa only [e.apply_symm_apply] using integralCoverIntertwines_action e g he (e.symm j) w

section
variable (hJ : J≤CubicKubota.levelThree)
include hJ

theorem integralConjugateMap_measurePreserving  
         
        :
    MeasurePreserving (integralConjugateMap e g he) (integralQuotientVolume H)
      (integralQuotientVolume J) := by
  refine ⟨integralConjugateMap_measurable e g he,?_⟩
  have hmap := (measurePreserving_smul g hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul g) (hyperbolicFundamentalSet H)
  change Measure.map (integralConjugateMap e g he)
    (Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict (hyperbolicFundamentalSet H)))=_
  rw [Measure.map_map (integralConjugateMap_measurable e g he) (measurable_integralOrbitProjection H)]
  change Measure.map ((integralOrbitProjection J) ∘ (fun w : HyperbolicSpace=>g•w))
    (hyperbolicVolume.restrict (hyperbolicFundamentalSet H))=_
  rw [←Measure.map_map (measurable_integralOrbitProjection J) (measurable_const_smul g),hmap.map_eq]
  exact integralQuotientVolume_independent J hJ _ (integralConjugate_fundamentalDomain e g he hH)

def integralConjugatePullback {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g ) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree) :
    Lp ℂ 2 (integralQuotientVolume J)→ₗᵢ[ℂ]Lp ℂ 2 (integralQuotientVolume H) :=
  Lp.compMeasurePreservingₗᵢ ℂ (integralConjugateMap e g he)
    (integralConjugateMap_measurePreserving e g he hH hJ)

theorem integralConjugatePullback_ae  
         
       
    (F : Lp ℂ 2 (integralQuotientVolume J)) :
    integralConjugatePullback e g he hH hJ F=ᵐ[integralQuotientVolume H]
      fun q=>F (integralConjugateMap e g he q) :=
  Lp.coeFn_compMeasurePreserving F (integralConjugateMap_measurePreserving e g he hH hJ)

end

end

end

end

section
 
open scoped       MatrixGroups

open   CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O

lemma scaled_cusp_periodic_upper
    (F : HyperbolicSpace→ℂ)  v   hv 
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,
      F (upperPoint (3*(z+3*eisEmbedding n)) v hv)=F (upperPoint (3*z) v hv))
     T  (hT : T 1 0=0)  n   z  :
    F (integralComplexMatrix T • upperPoint (3*(z+3*eisEmbedding n)) v hv)=
      F (integralComplexMatrix T • upperPoint (3*z) v hv) := by
  rw [integral_upper_triangular_action T hT,integral_upper_triangular_action T hT]
  have hleft : eisEmbedding (T 0 0)^2*(3*(z+3*eisEmbedding n))+
      eisEmbedding (T 0 0*T 0 1)=
      3*((eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)/3)+
        3*eisEmbedding ((T 0 0)^2*n)) := by
    simp only [map_mul,map_pow]
    ring
  have hright : eisEmbedding (T 0 0)^2*(3*z)+eisEmbedding (T 0 0*T 0 1)=
      3*(eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)/3) := by ring
  rw [hleft,hright]
  exact hp ((T 0 0)^2*n) _

section
variable (M : SL(2,ActualEisensteinCubic.O)) (v : ℝ) (hv : 0<v)
include M v hv

theorem sourceCusp_scaled_periodic      
     n   z  :
    cubicSourceResidualFunction (integralComplexMatrix M •
      upperPoint (3*(z+3*eisEmbedding n)) v hv)=
    cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩ := three_cusp_decomposition M
  have he (w : HyperbolicSpace) : cubicSourceResidualFunction (integralComplexMatrix M • w)=
      levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) • (integralComplexMatrix T • w)) := by
    rw [hM,map_mul,map_mul,mul_smul,mul_smul,cubicSourceResidualFunction_automorphy]
  calc
    _ = levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) •
          (integralComplexMatrix T • upperPoint (3*(z+3*eisEmbedding n)) v hv)) := he _
    _ = levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) •
          (integralComplexMatrix T • upperPoint (3*z) v hv)) :=
      congrArg (fun w : ℂ=>levelTwoComplexCharacter G*w)
        (scaled_cusp_periodic_upper
          (fun w=>cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • w))
          v hv (sourceCuspRepresentative_periodic j v hv) T hT n z)
    _ = _ := (he _).symm

lemma sourceCusp_scaled_continuous       :
    Continuous (fun z : ℂ=>cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*z) v hv)) := by
  let c : ℂ→UpperCoordinates := fun z=>⟨(3*z,v),hv⟩
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_id).prodMk continuous_const
  have ht := (continuous_translatedUpperCoordinates (integralComplexMatrix M)).comp hc
  have hh : Continuous (fun z : ℂ=>integralComplexMatrix M • upperPoint (3*z) v hv) := by
    simpa only [Function.comp_def,c] using ht
  exact cubicSourceResidualFunction_continuous.comp hh

end

end

 
open scoped       MatrixGroups

 
local notation "O" => ActualEisensteinCubic.O

theorem period_integral_eisenstein_affine (f : ℂ→ℂ) (hf : Measurable f)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z)  b  (hb : b≠0)  c  :
    (∫z in periodDomain,f (eisEmbedding b*z+c))=∫z in periodDomain,f z := by
  have hg : Measurable (fun z : ℂ=>f (z+c)) :=
    hf.comp (continuous_id.add continuous_const).measurable
  have hgp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n+c)=f (z+c) := by
    intro n z
    rw [show z+3*eisEmbedding n+c=(z+c)+3*eisEmbedding n by ring,hp]
  rw [period_integral_eisenstein_mul (fun z=>f (z+c)) hg hgp b hb]
  simpa only [add_comm] using period_integral_translation f hp c

section
variable (T : SL(2,ℂ)) (hT : T 1 0=0)
include T hT

lemma complex_upper_triangular_bottom_ne_zero     : T 1 1≠0 := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using T.property
  aesop

lemma complex_upper_triangular_action    
     z   v   hv  :
    T • upperPoint z v hv=
      upperPoint ((T 0 0*z+T 0 1)/T 1 1) (v/‖T 1 1‖^2)
        (div_pos hv (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
          (complex_upper_triangular_bottom_ne_zero T hT)))) := by
  have hd := complex_upper_triangular_bottom_ne_zero T hT
  have hs : star (T 1 1)≠0 := by
    simp_all
  have hprod : T 1 1*star (T 1 1)=((‖T 1 1‖^2:ℝ):ℂ) := by
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq] using Complex.mul_conj (T 1 1)
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · simp only [hT,zero_mul,zero_add,star_zero,mul_zero,add_zero,norm_zero]
    grind
  simp_all

end

end CubicEisenstein

end

end OAI
