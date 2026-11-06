module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
import OAI.NumberTheory.DirichletL.RowCompletion.CubicReopening

public import OAI.NumberTheory.DirichletL.RowCompletion.ThetaNonvanishing
public import OAI.NumberTheory.DirichletL.Eisenstein.CuspResidues

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
 
open scoped       MatrixGroups Matrix Pointwise

open CubicKubota


lemma globalKubotaKernel_conjugate_mem (M : levelThree) (N : globalKubotaKernel) :
    (M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹∈globalKubotaKernel := by
  obtain ⟨n,hn,hnval⟩ := N.property
  change (n:SL(2,ActualEisensteinCubic.O))=(N:SL(2,ActualEisensteinCubic.O)) at hnval
  refine ⟨M*n*M⁻¹,?_,?_⟩
  · change finiteCubicMultiplier (M*n*M⁻¹)=1
    change finiteCubicMultiplier n=1 at hn
    simp only [map_mul,map_inv,hn,mul_one,mul_inv_cancel]
  bound

def kernelConjugate (M : levelThree) : globalKubotaKernel ≃* globalKubotaKernel where
  toFun N := ⟨(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹,globalKubotaKernel_conjugate_mem M N⟩
  invFun N := ⟨(M⁻¹:levelThree)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelThree)⁻¹,globalKubotaKernel_conjugate_mem M⁻¹ N⟩
  left_inv N := by apply Subtype.ext; simp [mul_assoc]
  right_inv N := by apply Subtype.ext; simp [mul_assoc]
  map_mul' N P := by apply Subtype.ext; simp [mul_assoc]

lemma level_action_respects_kernel  M   u v 
    (h : (integralOrbitRel globalKubotaKernel).r u v) :
    (integralOrbitRel globalKubotaKernel).r (complexMatrix M • u) (complexMatrix M • v) := by
  obtain ⟨N,hN⟩ := h
  refine ⟨kernelConjugate M N,?_⟩
  change integralComplexMatrix ((M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹) •
    (complexMatrix M • u)=complexMatrix M • v
  rw [map_mul,map_mul,map_inv,mul_smul,mul_smul]
  simp_all [complexMatrix, integralComplexMatrix, ActualEisensteinCubic.O]

def kernelLevelAction (M : levelThree)  :=
  Quotient.map' (fun w => complexMatrix M • w) (level_action_respects_kernel M)

section
variable (M : levelThree) (a b : ℝ) (s : ℂ) (hs : 2<s.re) (q : KernelQuotient)

lemma kernelLevelAction_mk    w  :
    kernelLevelAction M (integralOrbitProjection globalKubotaKernel w)=
      integralOrbitProjection globalKubotaKernel (complexMatrix M • w) := rfl

lemma kernelLevelAction_continuous   : Continuous (kernelLevelAction M) :=
  (continuous_hyperbolic_action (complexMatrix M)).quotient_map' (level_action_respects_kernel M)

lemma kernelLevelAction_eisenstein      
      :
    kernelQuotientEisenstein s hs (kernelLevelAction M q)=
      complexCharacter M*kernelQuotientEisenstein s hs q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact hyperbolicEisenstein_automorphy M s hs w

lemma kernelLevelAction_seed         :
    kernelQuotientSeed a b s (kernelLevelAction M q)=complexCharacter M*kernelQuotientSeed a b s q := by
  induction q using Quotient.inductionOn with
  | _ w => exact smoothCuspSeed_automorphy a b s M w

lemma kernelLevelAction_fundamentalDomain   :
    IsFundamentalDomain globalKubotaKernel
      ((fun w : HyperbolicSpace => complexMatrix M • w) '' hyperbolicFundamentalSet globalKubotaKernel)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain globalKubotaKernel
    globalKubotaKernel_le_levelThree).image_of_equiv (MulAction.toPerm (complexMatrix M))
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm (complexMatrix M)).symm hyperbolicVolume hyperbolicVolume from (measurePreserving_smul (complexMatrix M)⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    (kernelConjugate M⁻¹).toEquiv
  intro N w
  change complexMatrix M • (integralComplexMatrix
    ((M⁻¹:levelThree)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelThree)⁻¹) • w)=
      integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) • (complexMatrix M • w)
  simp only [Subgroup.coe_inv,map_mul,map_inv]
  change complexMatrix M • (((complexMatrix M)⁻¹*integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O))*
    ((complexMatrix M)⁻¹)⁻¹) • w)=_
  simp only [inv_inv,mul_smul,smul_inv_smul]

lemma kernelLevelAction_measurePreserving   :
    MeasurePreserving (kernelLevelAction M) (integralQuotientVolume globalKubotaKernel)
      (integralQuotientVolume globalKubotaKernel) := by
  refine ⟨(kernelLevelAction_continuous M).measurable,?_⟩
  let act : HyperbolicSpace→HyperbolicSpace := fun w => complexMatrix M • w
  have hmap := (measurePreserving_smul (complexMatrix M) hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul (complexMatrix M)) (hyperbolicFundamentalSet globalKubotaKernel)
  have heq : kernelLevelAction M ∘ integralOrbitProjection globalKubotaKernel=
      integralOrbitProjection globalKubotaKernel ∘ act := by ext w; rfl
  change Measure.map (kernelLevelAction M)
    (Measure.map (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [Measure.map_map (kernelLevelAction_continuous M).measurable
    (measurable_integralOrbitProjection _),heq,
    ←Measure.map_map (measurable_integralOrbitProjection _) (continuous_hyperbolic_action _).measurable]
  change Measure.map (integralOrbitProjection globalKubotaKernel)
    (Measure.map act (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [hmap.map_eq]
  exact integralQuotientVolume_independent globalKubotaKernel globalKubotaKernel_le_levelThree _
    (kernelLevelAction_fundamentalDomain M)

end

end

 
open scoped       MatrixGroups

open CubicKubota

def kernelLevelPullback (M : levelThree) : KernelQuotientL2 →ₗᵢ[ℂ] KernelQuotientL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (kernelLevelAction M) (kernelLevelAction_measurePreserving M)

section
variable (M : levelThree) (a b : ℝ) (s : ℂ) (hs : 2<s.re) (F : KernelQuotientL2)

lemma kernelLevelPullback_ae_eq     :
    kernelLevelPullback M F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => F (kernelLevelAction M q) :=
  Lp.coeFn_compMeasurePreserving F (kernelLevelAction_measurePreserving M)

lemma kernelLevelPullback_of_remainder_ae      
       
    (hF : F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelLevelPullback M F=complexCharacter M • F := by
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hF
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M F,hcomp,hF,Lp.coeFn_smul (complexCharacter M) F]
    with q hp hc hf hsmul
  change _=complexCharacter M*F q at hsmul
  rw [hp,hsmul,hf]
  dsimp only [Function.comp_def] at hc
  rw [hc,kernelLevelAction_eisenstein,kernelLevelAction_seed,mul_sub]

lemma kernelCorrection_character_of_initial_overlap    
     ha   hab 
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    ∀s∈cuspUpperParameterRegion,
      kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s)=
        complexCharacter M • kernelEisensteinL2Correction a b ha hab s := by
  have hc : AnalyticOnNhd ℂ (kernelEisensteinL2Correction a b ha hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelEisensteinL2Correction_analyticAt_nonreal a b ha hab s (by linarith [hs.1]) hs.2.ne'
  have hl : AnalyticOnNhd ℂ (fun s => kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s))
      cuspUpperParameterRegion := by
    intro s hs
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
      (kernelLevelPullback M).toContinuousLinearMap _).comp_of_eq (hc s hs) rfl
  have hr : AnalyticOnNhd ℂ (fun s => complexCharacter M • kernelEisensteinL2Correction a b ha hab s)
      cuspUpperParameterRegion := by
    intro s hs
    exact (hc s hs).const_smul (c := complexCharacter M)
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s))
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s => complexCharacter M • kernelEisensteinL2Correction a b ha hab s) := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact kernelLevelPullback_of_remainder_ae M a b s (by linarith [hs.1]) _ (hoverlap s hs.1 hs.2)
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr cuspUpperParameterRegion_convex.isPreconnected
    (by norm_num [cuspUpperParameterRegion]) hevent

end

lemma thetaApproach_tendsto_complex_punctured :
    Tendsto (fun t : ℝ => (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)
      (𝓝[>] (0:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hh : Continuous (fun t : ℝ => (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I) := by fun_prop
    have ht := (hh.tendsto 0).mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    change (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I≠(4/3:ℂ)
    intro he
    have him := congrArg Complex.im he
    simp at him
    linarith

section
variable (M : levelThree) (a b : ℝ) (ha : 0<a) (hab : a<b) (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q)

include hoverlap in
lemma kernelEisensteinResidueVector_character_of_initial_overlap    
       
      :
    kernelLevelPullback M (kernelEisensteinResidueVector a b ha hab)=
      complexCharacter M • kernelEisensteinResidueVector a b ha hab := by
  have hlim := (kernelEisensteinResidueVector_limit a b ha hab).comp thetaApproach_tendsto_complex_punctured
  have hl := (kernelLevelPullback M).continuous.continuousAt.tendsto.comp hlim
  have hr := hlim.const_smul (complexCharacter M)
  have hevent :
      (fun t : ℝ => kernelLevelPullback M
        (((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
          kernelEisensteinL2Correction a b ha hab ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)))
      =ᶠ[𝓝[>] (0:ℝ)]
      (fun t : ℝ => complexCharacter M •
        (((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
          kernelEisensteinL2Correction a b ha hab ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I∈cuspUpperParameterRegion := by
      simp only [cuspUpperParameterRegion,Set.mem_ofPred_eq,Complex.add_re,Complex.add_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
        Complex.I_im,mul_zero,mul_one,sub_zero,add_zero]
      norm_num
      exact ht
    rw [map_smul,kernelCorrection_character_of_initial_overlap M a b ha hab hoverlap _ hs]
    exact smul_comm _ _ _
  exact tendsto_nhds_unique_of_eventuallyEq hl hr hevent

lemma kernelCuspAverageFamily_eq_of_initial_overlap      
     s  (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspAverageFamily a b ha hab s=
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume := by
  have hcorrected : kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s hs := by
    filter_upwards [hoverlap] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hrestr := ae_restrict_of_ae hcorrected (s := kernelCuspStripSet)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp hrestr
  rw [kernelCuspAverageFamily_actual_integral]
  apply integral_congr_ae
  assumption

include hoverlap in
lemma kernelEisensteinResidueVector_nonzero_character_of_initial_overlap  
       
      :
    kernelEisensteinResidueVector a b ha hab≠0 ∧
      ∀M : levelThree,kernelLevelPullback M (kernelEisensteinResidueVector a b ha hab)=
        complexCharacter M • kernelEisensteinResidueVector a b ha hab := by
  constructor
  · apply kernelEisensteinResidueVector_ne_zero_of_overlap a b ha hab
    intro s hs hi
    solve_by_elim [kernelCuspAverageFamily_eq_of_initial_overlap]
  · intro M
    exact kernelEisensteinResidueVector_character_of_initial_overlap M a b ha hab hoverlap

end

end CubicEisenstein

 
namespace QuadraticAllOddCRT
 
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega
open EisensteinEPrimaryPhase (Coord odd)

def quadraticRayExponent (r : Coord) : ZMod 4 :=
  if r∈({(0,1),(0,3),(1,0),(1,1),(3,0),(3,3)} : Finset Coord) then 0
  else if r∈({(1,2),(1,3),(2,3)} : Finset Coord) then 1 else 3

def fourthRoot (a : ZMod 4)  := Complex.I^(a.val:ℤ)

lemma fourthRoot_add  a b  : fourthRoot (a+b)=fourthRoot a*fourthRoot b := by
  unfold fourthRoot
  rw [←zpow_add₀ Complex.I_ne_zero]
  apply I_zpow_eq_of_mod_four
  push_cast
  simp

lemma quadraticRayValue_eq_fourthRoot  r  (hr : odd r) :
    quadraticRayValue r=fourthRoot (quadraticRayExponent r) := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases r with ⟨a,b⟩
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [quadraticRayExponent,fourthRoot,EisensteinEPrimaryPhase.odd,
      quadraticRayValue,breveGaussianFourTerms_formula,Prod.mk.injEq,hcmp,
      ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf

def quadraticRaySign (r s : Coord)  :=
  if odd r ∧ odd s then
    if quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s then 1 else -1
  else 0

section
variable (r s t : Coord) (hr : odd r) (hs : odd s)

lemma quadraticRaySign_mul_left   :
    quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
      quadraticRaySign r t*quadraticRaySign s t := by
  have h : ∀r s t : Coord,
      quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
        quadraticRaySign r t*quadraticRaySign s t := by decide
  exact h r s t

lemma quadraticRaySign_mul_right   :
    quadraticRaySign r (EisensteinEPrimaryPhase.mul s t)=
      quadraticRaySign r s*quadraticRaySign r t := by
  have h : ∀r s t : Coord,
      quadraticRaySign r (EisensteinEPrimaryPhase.mul s t)=
        quadraticRaySign r s*quadraticRaySign r t := by decide
  exact h r s t

lemma quadraticRaySign_symm   : quadraticRaySign r s=quadraticRaySign s r := by
  have h : ∀r s : Coord,quadraticRaySign r s=quadraticRaySign s r := by decide
  exact h r s

include hr hs in
lemma quadraticRaySign_sq       :
    quadraticRaySign r s^2=1 := by
  simp_all [quadraticRaySign]

include hr hs in
lemma quadraticRaySign_exponent       :
    quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by
  have h : ∀r s : Coord,odd r → odd s →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
        (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by decide
  exact h r s hr hs

include hr hs in
lemma quadraticRaySign_root       :
    fourthRoot (if quadraticRaySign r s=1 then 0 else 2)=(quadraticRaySign r s:ℂ) := by
  by_cases he : quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s
  · simp_all [quadraticRaySign, fourthRoot]
  · norm_num [quadraticRaySign,hr,hs,he,fourthRoot,ZMod.val_zero,ZMod.val_ofNat,Complex.I_sq]

include hr hs in
lemma odd_mul       : odd (EisensteinEPrimaryPhase.mul r s) := by solve_by_elim [_root_.OAI.EisensteinEPrimaryPhase.odd_mul]

include hr hs in
theorem quadraticRayValue_mul       :
    quadraticRayValue (EisensteinEPrimaryPhase.mul r s)=
      (quadraticRaySign r s:ℂ)*quadraticRayValue r*quadraticRayValue s := by
  simp_all [quadraticRayValue_eq_fourthRoot, odd_mul, quadraticRaySign_exponent, fourthRoot_add, quadraticRaySign_root]

end

end QuadraticAllOddCRT

 
namespace CanonicalRowCompletion

section
 
open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O
open CubicJacobiGlobal hiding O
open QuadraticGaussRay hiding O
open QuadraticAllOddCRT
open ActualEisensteinCoordinates hiding O omega
 

section
variable (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) (p q : ActualEisensteinCubic.O) (hp : Prime p) (hs : Supported (Ideal.span {p}))

include hI in
alias supported_factors_good := _root_.SharedProofs.supported_good

include hI in
lemma idealRowHom_one_supported     : idealRowHom 1 I=1 := by
  have h := CanonicalUnitEuler.idealRowHom_unit_norm (1:ActualEisensteinCubic.Oˣ) I hI.1 (supported_factors_good I hI)
  simpa using h

include hp hs in
lemma supported_prime_data       :
    lambda∉(Ideal.span {p}:Ideal ActualEisensteinCubic.O) ∧ ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2 := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  exact hs.2 _ ((Ideal.mem_normalizedFactors_iff hs.1).mpr ⟨inferInstance,le_rfl⟩)

include hs in
lemma supported_residue_odd     : EisensteinEPrimaryPhase.odd (residue p) :=
  (ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd p).mpr ((supported_span_iff p).mp hs).2

include hp in
theorem idealRowHom_prime_reciprocity     (hq : Prime q)
    (hprimaryP : lambda^2∣p-1) (hprimaryQ : lambda^2∣q-1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q})) :
    idealRowHom q (Ideal.span {p})=
      (quadraticRaySign (residue p) (residue q):ℂ)*idealRowHom p (Ideal.span {q}) := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let : (Ideal.span {q}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hq.irreducible
  obtain ⟨hgP,hcP⟩ := supported_prime_data p hp hsP
  obtain ⟨hgQ,hcQ⟩ := supported_prime_data q hq hsQ
  by_cases he : (Ideal.span {p}:Ideal ActualEisensteinCubic.O)=Ideal.span {q}
  · have hqp : q∈(Ideal.span {p}:Ideal ActualEisensteinCubic.O) := by rw [he];exact Ideal.subset_span (by simp)
    have hpq : p∈(Ideal.span {q}:Ideal ActualEisensteinCubic.O) := by rw [←he];exact Ideal.subset_span (by simp)
    rw [idealRowHom_prime q _ hgP,idealRowHom_prime p _ hgQ,
      Ideal.Quotient.eq_zero_iff_mem.mpr hqp,Ideal.Quotient.eq_zero_iff_mem.mpr hpq]
    simp only [MulChar.map_zero,mul_zero]
  · have hcop : IsCoprime (Ideal.span {p}:Ideal ActualEisensteinCubic.O) (Ideal.span {q}) := Ideal.isCoprime_of_isMaximal he
    have hqp : q∉(Ideal.span {p}:Ideal ActualEisensteinCubic.O) := by
      intro h
      apply he
      exact ((inferInstance : (Ideal.span {q}:Ideal ActualEisensteinCubic.O).IsMaximal).eq_of_le
        (Ideal.IsMaximal.ne_top inferInstance)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h))).symm
    have h2 : idealRowHom q (Ideal.span {p})^2=idealRowHom p (Ideal.span {q})^2 := by
      rw [idealRowHom_square,idealRowHom_square]
      exact congrArg ConcreteTraceCRT.eisEmbedding (symbol_reciprocity q p hq.ne_zero hp.ne_zero hprimaryQ hprimaryP)
    have h6 : idealRowHom q (Ideal.span {p})^6=1 := by
      rw [idealRowHom_prime q _ hgP]
      have h := canonicalSextic_sixth_power_mask (Ideal.span {p}) hgP q
      change actualSextic _ hgP (Ideal.Quotient.mk _ (q^6))=_ at h
      simpa only [map_pow,ite_eq_right hqp] using h
    have hcross := quadratic_ray_cross p q hp.ne_zero hq.ne_zero hcop hcP hcQ
    rw [residue_mul,quadraticRayValue_mul _ _ (supported_residue_odd p hsP) (supported_residue_odd q hsQ)] at hcross
    have h3 (x y : ActualEisensteinCubic.O) (hg : lambda∉(Ideal.span {x}:Ideal ActualEisensteinCubic.O)) [(Ideal.span {x}).IsMaximal] :
        idealRowHom y (Ideal.span {x})^3=
          character (Ideal.span {x}) (Ideal.Quotient.mk (Ideal.span {x}) y) := by
      rw [idealRowHom_prime y _ hg,←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
    have hc : idealRowHom q (Ideal.span {p})^3*idealRowHom p (Ideal.span {q})^3=
        (quadraticRaySign (residue p) (residue q):ℂ) := by
      rw [h3 p q hgP,h3 q p hgQ]
      apply mul_right_cancel₀ (quadraticRayValue_ne_zero_of_odd _ (supported_residue_odd p hsP))
      apply mul_right_cancel₀ (quadraticRayValue_ne_zero_of_odd _ (supported_residue_odd q hsQ))
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hcross.symm
    calc
      _ = idealRowHom q (Ideal.span {p})*idealRowHom q (Ideal.span {p})^6 := by rw [h6,mul_one]
      _ = idealRowHom q (Ideal.span {p})^3*(idealRowHom q (Ideal.span {p})^2)^2 := by ring
      _ = idealRowHom q (Ideal.span {p})^3*(idealRowHom p (Ideal.span {q})^2)^2 := by rw [h2]
      _ = (idealRowHom q (Ideal.span {p})^3*idealRowHom p (Ideal.span {q})^3)*idealRowHom p (Ideal.span {q}) := by ring
      _ = _ := by rw [hc]

end

end

 
open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O
open CubicJacobiGlobal hiding O
open QuadraticAllOddCRT
open ActualEisensteinCoordinates hiding O omega

def sexticReciprocityPhase (a b : ActualEisensteinCubic.O)  :=
  (quadraticRaySign (residue a) (residue b):ℂ)

section
variable (a b c : ActualEisensteinCubic.O) (ha : Supported (Ideal.span {a}))

lemma sexticReciprocityPhase_mul_left   :
    sexticReciprocityPhase (a*b) c=sexticReciprocityPhase a c*sexticReciprocityPhase b c := by
  simp only [sexticReciprocityPhase,residue_mul,quadraticRaySign_mul_left,Int.cast_mul]

lemma sexticReciprocityPhase_mul_right   :
    sexticReciprocityPhase a (b*c)=sexticReciprocityPhase a b*sexticReciprocityPhase a c := by
  simp only [sexticReciprocityPhase,residue_mul,quadraticRaySign_mul_right,Int.cast_mul]

include ha in
lemma sexticReciprocityPhase_one_right     :
    sexticReciprocityPhase a 1=1 := by
  have h1 : residue (1:ActualEisensteinCubic.O)=((1:ZMod 4),0) := by
    have h : (1:ActualEisensteinCubic.O)=eval 1 0 := by simp [eval]
    rw [h,residue_eval]
    norm_num
  have ht : ∀r : EisensteinEPrimaryPhase.Coord,EisensteinEPrimaryPhase.odd r →
      quadraticRaySign r ((1:ZMod 4),0)=1 := by decide
  simp_all [sexticReciprocityPhase, supported_residue_odd]

include ha in
lemma sexticReciprocityPhase_one_left     :
    sexticReciprocityPhase 1 a=1 := by
  have he : sexticReciprocityPhase 1 a=sexticReciprocityPhase a 1 := by
    simp only [sexticReciprocityPhase,quadraticRaySign_symm]
  rw [he,sexticReciprocityPhase_one_right a ha]

end

lemma idealRowHom_prime_primary_reciprocity  p b  (hp : Prime p)
    (hprimaryP : lambda^2∣p-1) (hprimaryB : lambda^2∣b-1)
    (hsP : Supported (Ideal.span {p})) (hsB : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {p})=sexticReciprocityPhase p b*idealRowHom p (Ideal.span {b}) := by
  have hb0 : b≠0 := by
    intro h
    apply hsB.1
    simp [h]
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization b hb0 hprimaryB
  rw [←hprod] at hsB ⊢
  clear hprod hb0 hprimaryB b
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,
      idealRowHom_one_supported _ hsP,sexticReciprocityPhase_one_right p hsP,mul_one]
  | @cons q s ih =>
    have hq := hfactors q (Multiset.mem_cons_self _ _)
    have htail : ∀r∈s,Prime r ∧ lambda^2∣r-1 := fun r hr => hfactors r (Multiset.mem_cons_of_mem hr)
    have hsplit : Supported (Ideal.span {q}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hsB
    rw [Multiset.prod_cons,idealRowHom_argument_mul,←Ideal.span_singleton_mul_span_singleton,
      map_mul,sexticReciprocityPhase_mul_right,
      idealRowHom_prime_reciprocity p q hp hq.1 hprimaryP hq.2 hsP hsplit.1,
      ih hsplit.2 htail]
    simp only [sexticReciprocityPhase]
    ring

theorem idealRowHom_primary_reciprocity  a b 
    (hprimaryA : lambda^2∣a-1) (hprimaryB : lambda^2∣b-1)
    (hsA : Supported (Ideal.span {a})) (hsB : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {a})=sexticReciprocityPhase a b*idealRowHom a (Ideal.span {b}) := by
  have ha0 : a≠0 := by
    intro h
    apply hsA.1
    simp [h]
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization a ha0 hprimaryA
  rw [←hprod] at hsA ⊢
  clear hprod ha0 hprimaryA a
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,
      idealRowHom_one_supported _ hsB,sexticReciprocityPhase_one_left b hsB,one_mul]
  | @cons p s ih =>
    have hp := hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀r∈s,Prime r ∧ lambda^2∣r-1 := fun r hr => hfactors r (Multiset.mem_cons_of_mem hr)
    have hsplit : Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hsA
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,
      idealRowHom_argument_mul,sexticReciprocityPhase_mul_left,
      idealRowHom_prime_primary_reciprocity p b hp.1 hp.2 hprimaryB hsplit.1 hsB,
      ih hsplit.2 htail]
    ring

end CanonicalRowCompletion

end

end OAI
