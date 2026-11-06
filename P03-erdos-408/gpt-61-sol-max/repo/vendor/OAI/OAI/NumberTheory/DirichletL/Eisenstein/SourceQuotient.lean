module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Eisenstein.SourceProjection

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
 
open scoped       MatrixGroups Matrix Pointwise

open CubicKubota
local notation "O" => ActualEisensteinCubic.O

abbrev SourceKernelQuotient := IntegralOrbitQuotient globalKubotaKernel

def sourceComplexMatrix  :=
  integralComplexMatrix.comp levelTwo.subtype

lemma globalKubotaKernel_source_conjugate_mem (M : levelTwo) (N : globalKubotaKernel) :
    (M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹∈globalKubotaKernel :=
  CubicKubota.globalKubotaKernel_conjugate M N N.property

def kernelSourceConjugate (M : levelTwo) : globalKubotaKernel ≃* globalKubotaKernel where
  toFun N := ⟨(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹,globalKubotaKernel_source_conjugate_mem M N⟩
  invFun N := ⟨(M⁻¹:levelTwo)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelTwo)⁻¹,globalKubotaKernel_source_conjugate_mem M⁻¹ N⟩
  left_inv N := by apply Subtype.ext; simp [mul_assoc]
  right_inv N := by apply Subtype.ext; simp [mul_assoc]
  map_mul' N P := by apply Subtype.ext; simp [mul_assoc]

lemma source_action_respects_kernel  M   u v 
    (h : (integralOrbitRel globalKubotaKernel).r u v) :
    (integralOrbitRel globalKubotaKernel).r (sourceComplexMatrix M • u) (sourceComplexMatrix M • v) := by
  obtain ⟨N,hN⟩ := h
  refine ⟨kernelSourceConjugate M N,?_⟩
  change integralComplexMatrix ((M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹) •
    (sourceComplexMatrix M • u)=sourceComplexMatrix M • v
  rw [map_mul,map_mul,map_inv,mul_smul,mul_smul]
  simp_all [sourceComplexMatrix, integralComplexMatrix, ActualEisensteinCubic.O]

def kernelSourceAction (M : levelTwo)  :=
  Quotient.map' (fun w => sourceComplexMatrix M • w) (source_action_respects_kernel M)

lemma kernelSourceAction_mk  M   w  :
    kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)=
      integralOrbitProjection globalKubotaKernel (sourceComplexMatrix M • w) := rfl

lemma kernelSourceAction_one  q  : kernelSourceAction 1 q=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (sourceComplexMatrix 1 • w)=integralOrbitProjection globalKubotaKernel w
    rw [map_one,one_smul]

lemma kernelSourceAction_mul  M N   q  :
    kernelSourceAction (M*N) q=kernelSourceAction M (kernelSourceAction N q) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (sourceComplexMatrix (M*N) • w)=
      integralOrbitProjection globalKubotaKernel (sourceComplexMatrix M • (sourceComplexMatrix N • w))
    rw [map_mul,mul_smul]

lemma kernelSourceAction_continuous  M  : Continuous (kernelSourceAction M) :=
  (continuous_hyperbolic_action (sourceComplexMatrix M)).quotient_map' (source_action_respects_kernel M)

def kernelSourceHomeomorph (M : levelTwo) : SourceKernelQuotient ≃ₜ SourceKernelQuotient where
  toFun := kernelSourceAction M
  invFun := kernelSourceAction M⁻¹
  left_inv q := by rw [←kernelSourceAction_mul,inv_mul_cancel,kernelSourceAction_one]
  right_inv q := by rw [←kernelSourceAction_mul,mul_inv_cancel,kernelSourceAction_one]
  continuous_toFun := kernelSourceAction_continuous M
  continuous_invFun := kernelSourceAction_continuous M⁻¹

lemma kernelSourceAction_fundamentalDomain  M  :
    IsFundamentalDomain globalKubotaKernel
      ((fun w : HyperbolicSpace => sourceComplexMatrix M • w) '' hyperbolicFundamentalSet globalKubotaKernel)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain globalKubotaKernel
    globalKubotaKernel_le_levelThree).image_of_equiv (MulAction.toPerm (sourceComplexMatrix M))
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm (sourceComplexMatrix M)).symm hyperbolicVolume hyperbolicVolume from (measurePreserving_smul (sourceComplexMatrix M)⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    (kernelSourceConjugate M⁻¹).toEquiv
  intro N w
  change sourceComplexMatrix M • (integralComplexMatrix
    ((M⁻¹:levelTwo)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelTwo)⁻¹) • w)=
      integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) • (sourceComplexMatrix M • w)
  simp only [Subgroup.coe_inv,map_mul,map_inv]
  change sourceComplexMatrix M • (((sourceComplexMatrix M)⁻¹*integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O))*
    ((sourceComplexMatrix M)⁻¹)⁻¹) • w)=_
  simp only [inv_inv,mul_smul,smul_inv_smul]

lemma kernelSourceAction_measurePreserving  M  :
    MeasurePreserving (kernelSourceAction M) (integralQuotientVolume globalKubotaKernel)
      (integralQuotientVolume globalKubotaKernel) := by
  refine ⟨(kernelSourceAction_continuous M).measurable,?_⟩
  let act : HyperbolicSpace→HyperbolicSpace := fun w => sourceComplexMatrix M • w
  have hmap := (measurePreserving_smul (sourceComplexMatrix M) hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul (sourceComplexMatrix M)) (hyperbolicFundamentalSet globalKubotaKernel)
  have heq : kernelSourceAction M ∘ integralOrbitProjection globalKubotaKernel=
      integralOrbitProjection globalKubotaKernel ∘ act := by ext w; rfl
  change Measure.map (kernelSourceAction M)
    (Measure.map (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [Measure.map_map (kernelSourceAction_continuous M).measurable
    (measurable_integralOrbitProjection _),heq,
    ←Measure.map_map (measurable_integralOrbitProjection _) (continuous_hyperbolic_action _).measurable]
  change Measure.map (integralOrbitProjection globalKubotaKernel)
    (Measure.map act (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [hmap.map_eq]
  exact integralQuotientVolume_independent globalKubotaKernel globalKubotaKernel_le_levelThree _
    (kernelSourceAction_fundamentalDomain M)

end CubicEisenstein

section
 
open scoped       MatrixGroups

namespace CubicEisenstein
open CubicKubota

def kernelSourcePullback (M : levelTwo) : KernelQuotientL2 →ₗᵢ[ℂ] KernelQuotientL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (kernelSourceAction M) (kernelSourceAction_measurePreserving M)

lemma kernelSourcePullback_ae_eq  M   F  :
    kernelSourcePullback M F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => F (kernelSourceAction M q) :=
  Lp.coeFn_compMeasurePreserving F (kernelSourceAction_measurePreserving M)

lemma kernelSourcePullback_one  F  : kernelSourcePullback 1 F=F := by
  apply Lp.ext
  filter_upwards [kernelSourcePullback_ae_eq 1 F] with q hq
  simpa only [kernelSourceAction_one] using hq

lemma kernelSourcePullback_comp  M N   F  :
    kernelSourcePullback M (kernelSourcePullback N F)=kernelSourcePullback (N*M) F := by
  have hcomp := (kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelSourcePullback_ae_eq N F)
  apply Lp.ext
  filter_upwards [kernelSourcePullback_ae_eq M (kernelSourcePullback N F),hcomp,
    kernelSourcePullback_ae_eq (N*M) F] with q hp hn hnm
  rw [hp,hnm]
  exact hn.trans (congrArg F (kernelSourceAction_mul N M q).symm)

lemma kernelSourcePullback_surjective  M  : Function.Surjective (kernelSourcePullback M) := by
  intro F
  refine ⟨kernelSourcePullback M⁻¹ F,?_⟩
  rw [kernelSourcePullback_comp,inv_mul_cancel,kernelSourcePullback_one]

def kernelSourceUnitary (M : levelTwo)  :=
  LinearIsometryEquiv.ofSurjective (kernelSourcePullback M) (kernelSourcePullback_surjective M)

local notation "O" => ActualEisensteinCubic.O

def kernelSourceProjection  :=
  (24:ℂ)⁻¹ • ∑q : levelTwo ⧸ levelThreeInTwo,
    (kernelSourcePullback (rationalLift (sourceRationalSection q))).toContinuousLinearMap

lemma kernelSourceProjection_apply  F  :
    kernelSourceProjection F=(24:ℂ)⁻¹ • ∑q : levelTwo ⧸ levelThreeInTwo,
      kernelSourcePullback (rationalLift (sourceRationalSection q)) F := by
  simp only [kernelSourceProjection,_root_.smul_apply,_root_.sum_apply,
    LinearIsometry.coe_toContinuousLinearMap]

lemma kernelSourceProjection_eq_twentyFour  F  :
    kernelSourceProjection F=(24:ℂ)⁻¹ • ∑i : RationalBruhatIndex,
      kernelSourcePullback (rationalLift (rationalBruhatRep i)) F := by
  rw [kernelSourceProjection_apply]
  congr 1
  rw [←rationalCosetEquiv.sum_comp]
  simp only [sourceRationalSection,Equiv.symm_apply_apply]

end CubicEisenstein

namespace CubicKubota
 

def sourceLevelInclusion : levelThree→*levelTwo where
  toFun n := ⟨(n:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo n.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

lemma sourceLevelInclusion_character  n  :
    levelTwoComplexCharacter (sourceLevelInclusion n)=complexCharacter n :=
  levelTwoComplexCharacter_restrict n

end CubicKubota

namespace CubicEisenstein
open CubicKubota

lemma kernelSourceProjection_ae_eq  F  :
    kernelSourceProjection F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun x => (24:ℂ)⁻¹ * ∑q : levelTwo ⧸ levelThreeInTwo,
        F (kernelSourceAction (rationalLift (sourceRationalSection q)) x) := by
  rw [kernelSourceProjection_apply]
  have hsum := (Lp.coeFn_finsetSum Finset.univ
    (fun q : levelTwo ⧸ levelThreeInTwo =>
      kernelSourcePullback (rationalLift (sourceRationalSection q)) F)).trans
    (eventuallyEq_sum (fun q _ =>
      kernelSourcePullback_ae_eq (rationalLift (sourceRationalSection q)) F))
  filter_upwards [(Lp.coeFn_smul (24:ℂ)⁻¹ _).trans (hsum.const_smul (24:ℂ)⁻¹)] with x hx
  simpa only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul] using hx

end CubicEisenstein
end

 

namespace CubicEisenstein
open CubicKubota

end CubicEisenstein

 
open scoped       ENNReal
 

namespace CubicEisenstein
open EisensteinSchwartzPoisson     Module

def periodVector  := periodBasis.equivFunL.symm

lemma periodVector_apply  x  :
    periodVector x = 3 * ((x 0 : ℂ) + (x 1 : ℂ) * omega3) := by
  change periodBasis.equivFun.symm x = _
  rw [Basis.equivFun_symm_apply, Fin.sum_univ_two, periodBasis_zero, periodBasis_one]
  simp only [Complex.real_smul]
  ring

def periodTorus (z : ℂ) : UnitAddTorus (Fin 2) :=
  fun i => (periodBasis.equivFunL z i : UnitAddCircle)

lemma periodTorus_periodVector  x  :
    periodTorus (periodVector x) = fun i => (x i : UnitAddCircle) := by
  change (fun i => ((periodBasis.equivFunL (periodBasis.equivFunL.symm x)) i : UnitAddCircle)) = _
  rw [periodBasis.equivFunL.apply_symm_apply]

def periodFrequencyEquiv  :=
  (finTwoArrowEquiv ℤ).trans dualFrequencyEquiv

lemma periodFrequencyEquiv_apply  n  :
    periodFrequencyEquiv n = dualFrequencyEquiv (n 0, n 1) := rfl

lemma periodVector_character  n   x  :
    ShortDraftTrace.breveE (cuspFrequency (periodFrequencyEquiv n) * periodVector x) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((n 0 : ℂ) * (x 0 : ℂ) + (n 1 : ℂ) * (x 1 : ℂ))) := by
  have hlam : eisLam ≠ 0 := eisLam_ne_zero
  have harg : cuspFrequency (periodFrequencyEquiv n) * periodVector x =
      (eisEmbedding (dualFrequencyEquiv (n 0,n 1)) *
        ((x 0 : ℂ) + (x 1 : ℂ) * omega3)) / eisLam := by
    rw [cuspFrequency, periodVector_apply, periodFrequencyEquiv_apply]
    field_simp
  rw [harg, ←paperE, paperE_eq_exp, dualFrequencyEquiv_coordinates]
  
  have hw : omega3.re = -(1/2:ℝ) := by norm_num [omega3]
  congr 1
  simp only [complexPoint, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, hw, omega3_im]
  push_cast
  field_simp
  ring

lemma periodTorus_mFourier  n   z  :
    UnitAddTorus.mFourier n (periodTorus z) =
      ShortDraftTrace.breveE (cuspFrequency (periodFrequencyEquiv n) * z) := by
  obtain ⟨x, rfl⟩ := periodVector.surjective z
  rw [periodTorus_periodVector, periodVector_character]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [←Complex.exp_add]
  congr 1
  ring

lemma periodFrequencyEquiv_neg  n  :
    periodFrequencyEquiv (-n) = -periodFrequencyEquiv n := by
  apply eisEmbedding_injective
  change eisEmbedding (ActualEisensteinCoordinates.eval (-n 0 + -n 1) (-n 0)) =
    eisEmbedding (-ActualEisensteinCoordinates.eval (n 0 + n 1) (n 0))
  rw [map_neg, eisEmbedding_eval, eisEmbedding_eval]
  push_cast
  ring

lemma cuspFrequency_neg  h  : cuspFrequency (-h) = -cuspFrequency h := by
  simp only [cuspFrequency, map_neg, neg_div]

lemma periodVector_eq_lattice  x  :
    periodVector x = eisensteinLatticeMap 3 (by norm_num) (Complex.measurableEquivPi.symm x) := rfl

lemma periodVector_map_volume :
    Measure.map periodVector volume = ENNReal.ofReal (2/(9*Real.sqrt 3)) • volume := by
  have heq : (periodVector : (Fin 2 → ℝ) → ℂ) =
      eisensteinLatticeMap 3 (by norm_num) ∘ Complex.measurableEquivPi.symm :=
    funext periodVector_eq_lattice
  rw [heq, ←Measure.map_map (eisensteinLatticeMap 3 (by norm_num)).continuous.measurable
    Complex.measurableEquivPi.symm.measurable, Complex.volume_preserving_equiv_pi.symm.map_eq]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (eisensteinLatticeMap 3 (by norm_num)).toLinearEquiv.isUnit_det'.ne_zero
  change Measure.map (eisensteinLatticeMap 3 (by norm_num)) volume =
    ENNReal.ofReal (inverseJacobian (eisensteinLatticeMap 3 (by norm_num))) • volume at hmap
  rw [hmap, eisenstein_inverseJacobian]
  norm_num [mul_comm]

def periodCube : Set (Fin 2 → ℝ) := {x | ∀i, x i ∈ Set.Ico 0 1}

lemma periodVector_preimage_domain : periodVector ⁻¹' periodDomain = periodCube := by
  ext x
  change (∀i, periodBasis.repr (periodBasis.equivFun.symm x) i ∈ Set.Ico 0 1) ↔ _
  simp only [←Basis.equivFun_apply, periodBasis.equivFun.apply_symm_apply]
  rfl

lemma periodDomain_integral_coordinates (f : ℂ → ℂ) :
    (2/(9*Real.sqrt 3):ℝ) • (∫z in periodDomain, f z) =
      ∫x in periodCube, f (periodVector x) := by
  have h := periodVector.toHomeomorph.toMeasurableEquiv.measurableEmbedding.setIntegral_map
    f periodDomain («μ» := (volume : Measure (Fin 2 → ℝ)))
  change (∫z in periodDomain, f z ∂Measure.map periodVector volume) =
    ∫x in periodVector ⁻¹' periodDomain, f (periodVector x) at h
  rw [periodVector_map_volume, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), periodVector_preimage_domain] at h
  exact h

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩



lemma periodCube_ae_Ioc : periodCube =ᵐ[volume]
    {x : Fin 2 → ℝ | ∀i, x i ∈ Set.Ioc 0 1} := by
  rw [volume_pi]
  have h := Measure.ae_eq_set_pi («μ» := fun _ : Fin 2 => (volume : Measure ℝ))
    (I := Set.univ) (s := fun _ => Set.Ico (0:ℝ) 1) (t := fun _ => Set.Ioc (0:ℝ) 1)
    (fun _ _ => Ico_ae_eq_Ioc)
  simpa only [Set.pi, Set.mem_univ, forall_true_left, periodCube] using h

lemma periodTorus_integral (f : UnitAddTorus (Fin 2) → ℂ) :
    (∫t, f t) = (2/(9*Real.sqrt 3):ℝ) • (∫z in periodDomain, f (periodTorus z)) := by
  rw [periodDomain_integral_coordinates, UnitAddTorus.integral_preimage f (fun _ => 0)]
  simp only [zero_add, periodTorus_periodVector]
  exact setIntegral_congr_set periodCube_ae_Ioc.symm

lemma periodTorus_fourierCoeff  f   n  :
    UnitAddTorus.mFourierCoeff f n = (2/(9*Real.sqrt 3):ℝ) •
      (∫z in periodDomain, f (periodTorus z) *
        ShortDraftTrace.breveE (-cuspFrequency (periodFrequencyEquiv n)*z)) := by
  rw [UnitAddTorus.mFourierCoeff, periodTorus_integral]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [periodTorus_mFourier, periodFrequencyEquiv_neg, cuspFrequency_neg]
    exact mul_comm _ _)

lemma periodTorus_L2_ext (F G : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (h : ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain, F (periodTorus z)*ShortDraftTrace.breveE (-cuspFrequency h*z)) =
      ∫z in periodDomain, G (periodTorus z)*ShortDraftTrace.breveE (-cuspFrequency h*z)) : F=G := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  ext n
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr,
    periodTorus_fourierCoeff, periodTorus_fourierCoeff, h]

end CubicEisenstein

end

end OAI
