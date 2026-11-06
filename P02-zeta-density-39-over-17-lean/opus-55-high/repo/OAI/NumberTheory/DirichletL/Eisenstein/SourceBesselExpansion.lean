module
public import OAI.NumberTheory.DirichletL.Eisenstein.PrimePowerGaussSums
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

namespace CubicEisenstein

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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped Classical SchwartzMap

section
open Filter MeasureTheory
open scoped Classical Topology MatrixGroups

section
local notation "Eis" => ActualEisensteinCubic.O

section
variable (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis)
include a b ha ρ h
lemma opposite_height_fourier_average (s:ℂ) (hs:2< s.re) :
    (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
      cuspWeightedFourierPhase ρ h w∂ hyperbolicVolume)=
      unramifiedCubicGaussSeries s (9*h)*cuspIntervalWhittakerHeightFactor a b ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
    cuspWeightedFourierPhase ρ h w
  have hg:Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  pm_3666
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  pm_3586 hv0
  pm_3654 hvz v hv0.ne'
  have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      ρ v*((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*unramifiedCubicGaussSeries s (9*h) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hv0,hyperbolicEisenstein_opposite_upper,
      cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    have he (z:ℂ) : oppositeEisenstein z v hv0 s*(ρ v*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ρ v*(oppositeEisenstein z v hv0 s*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by ring
    simp_rw [he]
    rw [integral_const_mul,oppositeEisenstein_fourier v hv0 s hs h]
    ring
  have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
    pm_3653
    simp_all
  dsimp only
  rw [hinner,hp]
  ring

lemma oppositeHeight_cross_identity :
    Set.EqOn (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*cuspWhittakerHeightFactor s h)
      (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s *
        cuspIntervalWhittakerHeightFactor a b ρ s h) {s:ℂ|1< s.re ∧ 0< s.im} := by
  pm_3668
  have hf : AnalyticOnNhd ℂ (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s *
      cuspWhittakerHeightFactor s h) domain := fun s hs=>
    (translatedHeightFamily_analyticAt a b ha ρ h oppositeSource s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hg : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s *
      cuspIntervalWhittakerHeightFactor a b ρ s h) domain := fun s hs=>
    (translatedCuspFamily_analyticAt_nonreal h oppositeSource 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by aesop
  have hopen : IsOpen {s:ℂ | 4< s.re ∧ 0< s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*cuspWhittakerHeightFactor s h)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s *
        cuspIntervalWhittakerHeightFactor a b ρ s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [translatedHeightFamily_initial a b ha ρ h oppositeSource s hs.1 hs.2,
      opposite_height_fourier_average a b ha ρ h s (by grind),
      translatedCuspFamily_initial h oppositeSource 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      opposite_cusp_fourier_average s (by grind)]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev

theorem translatedHeightFourier_opposite_residue :
    translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue=
      unramifiedGaussResidue (9*h)*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  have hfixed := (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hvar := (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h (4/3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hl:=((translatedHeightFamily_residue_limit a b ha ρ h oppositeSource).mul hfixed).comp upperVertical_tendsto_cubic_punctured
  have hr:=((translatedCuspFamily_residue_limit h oppositeSource 2 3 (by norm_num) (by norm_num)).mul hvar).comp
    upperVertical_tendsto_cubic_punctured
  have hev : (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedHeightFamily a b ha ρ h oppositeSource ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h)
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspIntervalWhittakerHeightFactor a b ρ ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    pm_3637
    have he:=oppositeHeight_cross_identity a b ha ρ h (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1< s.re ∧ 0< s.im} by
      constructor
      · norm_num
      simp_all)
    grind
  have heq : translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue*cuspWhittakerHeightFactor (4/3:ℂ) h=
      translatedCuspFourier h oppositeSource cubicEisensteinResidue*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hev
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero h)
  rw [heq,translatedCuspFourier_unramified_residue]
  ring
end

end

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

section
variable (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
include a b ha ρ
lemma rational_height_fourier_right_T
    (r:SL(2,ℤ)) (n:ℕ) (h:Eis) (s:ℂ) (hs:2< s.re) :
    (∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)*
        cuspWeightedFourierPhase ρ h w∂ hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*
        ∫w in cuspPeriodStrip a b,
          hyperbolicEisenstein s (rationalComplex r • w)*cuspWeightedFourierPhase ρ h w∂ hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex (r*ModularGroup.T^n) • w)*cuspWeightedFourierPhase ρ h w
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex r • w)*cuspWeightedFourierPhase ρ h w
  have hf : Continuous f := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  change (∫w in cuspPeriodStrip a b,f w∂ hyperbolicVolume)=
    ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫w in cuspPeriodStrip a b,g w∂ hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha f hf.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha f hf),
    cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg),←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  pm_3586 hv0
  have hslice : (∫z in periodDomain,f (cuspCoordinateLift (v,z)))=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫z in periodDomain,g (cuspCoordinateLift (v,z)) := by
    simp only [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper,
      cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    simpa only [mul_assoc] using period_integral_fourier_translation
      (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0)*ρ v)
      (fun m z=>congrArg (fun q:ℂ=>q*ρ v) (hyperbolicEisenstein_rational_periodic r m s hs z v hv0)) h (n:ℂ)
  dsimp only
  rw [hslice]
  ring

lemma translatedHeightFourier_residue_scaled_of_initial (h:Eis) (M N:levelTwo) (c:ℂ)
    (he : ∀s:ℂ,4< s.re→0< s.im→
      (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspWeightedFourierPhase ρ h w∂ hyperbolicVolume)=
      c*∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix N • w)*cuspWeightedFourierPhase ρ h w∂ hyperbolicVolume) :
    translatedHeightFourier a b ha ρ h M cubicEisensteinResidue=
      c*translatedHeightFourier a b ha ρ h N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedHeightFamily a b ha ρ h M
  let g : ℂ→ℂ := fun s=>c*translatedHeightFamily a b ha ρ h N s
  pm_3668
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedHeightFamily_analyticAt a b ha ρ h M s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>analyticAt_const.mul
    (translatedHeightFamily_analyticAt a b ha ρ h N s hs.1.ne' hs.2.ne')
  pm_3612
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    pm_3613
    rw [translatedHeightFamily_initial a b ha ρ h M s hs.1 hs.2,
      translatedHeightFamily_initial a b ha ρ h N s hs.1 hs.2]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedHeightFamily_residue_limit a b ha ρ h M).comp
    upperVertical_tendsto_cubic_punctured
  have hr := ((translatedHeightFamily_residue_limit a b ha ρ h N).const_mul c).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  pm_3637
  pm_3649

lemma translatedHeightFourier_one (h:Eis) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h 1 F=kernelCuspHeightFourier a b ha ρ h F := by
  rw [translatedHeightFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one]

lemma translatedHeightFourier_bruhat (h:Eis) (e:Fin 2) (sector:Fin 3⊕(Fin 3×Fin 3)) :
    translatedHeightFourier a b ha ρ h (rationalLift (rationalBruhatRep (e,sector))) cubicEisensteinResidue=
      match sector with
      | Sum.inl _=>kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue
      | Sum.inr ab=>ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
        translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue := by
  cases sector with
  | inl index =>
    rw [←one_mul (kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue),←translatedHeightFourier_one a b ha ρ h]
    apply translatedHeightFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    simp only [map_one,one_smul,one_mul]
  | inr ab =>
    apply translatedHeightFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    change (∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (rationalComplex ModularGroup.S •
        (rationalComplex (ModularGroup.T^ab.2.val) • w))*cuspWeightedFourierPhase ρ h w∂ hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)*
        cuspWeightedFourierPhase ρ h w∂ hyperbolicVolume
    simpa only [map_mul,mul_smul] using
      rational_height_fourier_right_T a b ha ρ ModularGroup.S ab.2.val h s (by linarith)

theorem kernelSourceProjection_height_fourier (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      (4:ℂ)⁻¹*(kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue+
        sourceRayPhaseSum h*translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue) := by
  rw [kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  change (24:ℂ)⁻¹*(∑i:RationalBruhatIndex,
    translatedHeightFourier a b ha ρ h (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=_
  rw [Fintype.sum_prod_type]
  simp_rw [translatedHeightFourier_bruhat]
  pm_162 Fintype.sum_sum_type Fintype.sum_prod_type Finset.sum_const Finset.card_univ Fintype.card_fin nsmul_eq_mul
  rw [←Finset.sum_mul]
  change (24:ℂ)⁻¹*((2:ℂ)*(3*kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue+
    3*(sourceRayPhaseSum h*translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue)))=_
  ring
end

end

section
open Filter MeasureTheory
open scoped Classical Topology

section
local notation "Eis" => ActualEisensteinCubic.O

lemma cuspIntervalWhittakerHeightFactor_zero_center (a b:ℝ) (_ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) 0=
      (3*(Real.pi:ℂ))*∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ)) := by
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  dsimp only
  simp only [cuspFrequency,map_zero,zero_div,zero_mul,sourceFourierKernel_zero (4/3) (by norm_num)]
  have he : -(4/3:ℂ)-1=-(7/3:ℂ) := by ring
  rw [he]
  ring

lemma kernelCuspHeightFourier_principal_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*principalArithmeticResidue h*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  by_cases hh:h=0
  · subst h
    rw [kernelCuspHeightFourier_zero_residue_seven_thirds,cuspIntervalWhittakerHeightFactor_zero_center a b ha ρ]
    simp only [principalArithmeticResidue,ite_true]
    ring
  · simpa only [principalArithmeticResidue,ite_eq_right hh] using kernelCuspHeightFourier_residue_factor a b ha ρ h hh

lemma principalArithmeticResidue_not_horizontal (h:Eis) (hh:ShortDraftTrace.breveE (cuspFrequency h)≠1) :
    principalArithmeticResidue h=0 := by
  have h0:h≠0 := by intro he;subst h;simp [cuspFrequency] at hh
  rw [principalArithmeticResidue,ite_eq_right h0,nonzeroScatteringResidue,
    kernelCuspFourier_residue_eq_zero_of_not_horizontal h hh,zero_div]

theorem kernelSourceProjection_height_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceArithmeticResidue h*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  rw [kernelSourceProjection_height_fourier,kernelCuspHeightFourier_principal_residue,
    translatedHeightFourier_opposite_residue,sourceRayPhaseSum_eq,sourceArithmeticResidue]
  split_ifs with hh
  · field_simp [cusp_volume_ne_zero]

  · rw [principalArithmeticResidue_not_horizontal h hh]
    ring

def sourceResidualFourierCoefficient (h:Eis) : ℂ := cubicBesselNormalizer h*sourceArithmeticResidue h

def sourceResidualFullModeAmplitude (v:ℝ) (h:Eis) : ℂ :=
  if h=0 then (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)
  else sourceResidualFourierCoefficient h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

section
variable (v:ℝ) (hv:0<v)
include v hv
lemma sourceResidualFullModeAmplitude_zero_density :
    sourceResidualFullModeAmplitude v 0/(v:ℂ)^3=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)) := by
  simpa [sourceResidualFullModeAmplitude,cubicResidualFullModeAmplitude] using
    cubicResidualFullModeAmplitude_zero_density v hv

lemma sourceResidualFullModeAmplitude_nonzero_density (h:Eis) (hh:h≠0) :
    sourceResidualFullModeAmplitude v h/(v:ℂ)^3=sourceResidualFourierCoefficient h*
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [sourceResidualFullModeAmplitude,ite_eq_right hh]
  pm_3654 hv0 v hv.ne'
  field_simp
end

section
variable (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis)
include a b ha ρ h
lemma kernelSourceProjection_height_bessel (hh:h≠0) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFourierCoefficient h*
        ∫v in Set.Icc a b,ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [kernelSourceProjection_height_residue,cuspIntervalWhittakerHeightFactor_center_bessel a b ha ρ h hh,
    sourceResidualFourierCoefficient]
  ring

theorem kernelSourceProjection_height_full :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  by_cases hh:h=0
  · subst h
    rw [kernelSourceProjection_height_residue,sourceArithmeticResidue_zero,
      cuspIntervalWhittakerHeightFactor_zero_center a b ha ρ]
    have he : (∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v 0/(v:ℂ)^3))=
        ((3*(Real.pi:ℂ))*constantArithmeticResidue)*∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ)) := by
      pm_3574
      rw [sourceResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)]
      ring
    rw [he]
    ring
  · rw [kernelSourceProjection_height_bessel a b ha ρ h hh]
    have he : (∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3))=
        sourceResidualFourierCoefficient h*∫v in Set.Icc a b,
          ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
      pm_3574
      pm_8764 sourceResidualFullModeAmplitude_nonzero_density
    rw [he]
    ring
end

end

local notation "O" => ActualEisensteinCubic.O

lemma sourceResidualFourierCoefficient_interval_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖sourceResidualFourierCoefficient h‖*
        ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖≤C := by
  pm_3671
  refine ⟨C*‖(kernelSourceProjection cubicEisensteinResidue)‖/‖area‖,div_nonneg (mul_nonneg hC (norm_nonneg _)) harea.le,?_⟩
  pm_6408 kernelSourceProjection_height_bessel
  have hhbound := hbound (BoundedContinuousFunction.const ℝ (1:ℂ)) h (kernelSourceProjection cubicEisensteinResidue)
  pm_3670

lemma sourceResidualFourierCoefficient_subexponential (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖sourceResidualFourierCoefficient h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by pm_3675 sourceResidualFourierCoefficient_interval_bound sourceResidualFourierCoefficient

def sourceBesselCoefficients : SubexponentialBesselCoefficients where
  value := sourceResidualFourierCoefficient
  growth := sourceResidualFourierCoefficient_subexponential

def sourceBesselFunction : HyperbolicSpace→ℂ :=
  sourceBesselCoefficients.fullFunction ((3*(Real.pi:ℂ))*constantArithmeticResidue)

lemma sourceBesselFunction_continuous : Continuous sourceBesselFunction :=
  sourceBesselCoefficients.fullFunction_continuous _

section
variable (v:ℝ) (hv:0<v)
include v hv
lemma sourceBesselFunction_fourier (h:ActualEisensteinCubic.O) :
    (∫z in periodDomain,sourceBesselFunction (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  rw [sourceBesselFunction,sourceBesselCoefficients.fullFunction_fourier]
  by_cases hh:h=0
  · simp [sourceResidualFullModeAmplitude,hh]
  · simp only [ite_eq_right hh,SubexponentialBesselCoefficients.amplitude,sourceResidualFullModeAmplitude]
    rfl

lemma sourceBesselFunction_period (z:ℂ) (n:ActualEisensteinCubic.O) :
    sourceBesselFunction (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      sourceBesselFunction (upperPoint z v hv) :=
  sourceBesselCoefficients.fullFunction_period _ v hv z n

lemma sourceBesselFunction_height_memLp :
    MemLp (fun z:ℂ=>sourceBesselFunction (cuspCoordinateLift (v,z))) 2 (volume.restrict periodDomain) :=
  sourceBesselCoefficients.fullFunction_height_memLp _ v hv
end

end

open Filter MeasureTheory
open scoped Classical Topology

local notation "O" => ActualEisensteinCubic.O

section
variable (a b : ℝ) (ha : 0<a)
include a b ha
lemma sourceResidualFullMode_density_integrable (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => sourceResidualFullModeAmplitude v h/(v:ℂ)^3)
      (Set.Icc a b) volume := by pm_3682 sourceResidualFullModeAmplitude_zero_density sourceResidualFourierCoefficient sourceResidualFullModeAmplitude_nonzero_density

lemma projectedResidue_slice_coefficient_ae (h : ActualEisensteinCubic.O) :
    kernelCuspSliceCoefficient (kernelSourceProjection cubicEisensteinResidue) h =ᵐ[volume.restrict (Set.Icc a b)]
      (fun v => ((9*Real.sqrt 3/2:ℝ):ℂ)*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3)) := by
  apply interval_ae_eq_of_boundedContinuous_height_tests a b _ _
    (kernelCuspSliceCoefficient_integrable a b ha h (kernelSourceProjection cubicEisensteinResidue))
    ((sourceResidualFullMode_density_integrable a b ha h).const_mul _)
  intro ρ
  rw [←kernelCuspHeightFourier_eq_slice_integral a b ha ρ h (kernelSourceProjection cubicEisensteinResidue),
    kernelSourceProjection_height_full a b ha ρ h,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by ring)

lemma projectedResidue_all_slice_coefficients_ae :
    ∀ᵐv ∂ volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      kernelCuspSliceCoefficient (kernelSourceProjection cubicEisensteinResidue) h v =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  exact ae_all_iff.mpr (fun h => projectedResidue_slice_coefficient_ae a b ha h)

lemma projectedResidue_all_fourier_integrals_ae :
    ∀ᵐv ∂ volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,
        (kernelSourceProjection cubicEisensteinResidue) (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))*
          ShortDraftTrace.breveE (-cuspFrequency h*z)) =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by pm_3683 projectedResidue_all_slice_coefficients_ae
end

theorem projectedResidue_cell_slices_ae (a b:ℝ) (ha:0<a) :
    ∀ᵐv ∂ volume.restrict (Set.Icc a b),
      (fun z:ℂ=>kernelSourceProjection cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z))))
      =ᵐ[volume.restrict periodDomain] (fun z=>sourceBesselFunction (cuspCoordinateLift (v,z))) := by
  filter_upwards [projectedResidue_all_fourier_integrals_ae a b ha,
    kernelCuspSections_memLp a b ha (kernelSourceProjection cubicEisensteinResidue),
    ae_restrict_mem measurableSet_Icc] with v hfour hL hv
  have hpos:0<v:=ha.trans_le hv.1
  pm_7132 sourceBesselFunction_height_memLp
  simpa only [cuspCoordinateLift_positive v _ hpos] using sourceBesselFunction_fourier v hpos h

theorem sourceBesselFunction_represents_projection :
    (fun w=>kernelSourceProjection cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] sourceBesselFunction := by
  apply hyperbolic_eq_ae_of_period_cells _ _
    ((MeasureTheory.Lp.stronglyMeasurable (kernelSourceProjection cubicEisensteinResidue)).measurable.comp
      (measurable_integralOrbitProjection _)) sourceBesselFunction_continuous.measurable
  · intro v hv z n
    exact congrArg (kernelSourceProjection cubicEisensteinResidue) (kernelProjection_upper_period v hv z n)
  · exact sourceBesselFunction_period
  · exact projectedResidue_cell_slices_ae

theorem cubicSourceResidualFunction_eq_bessel : cubicSourceResidualFunction=sourceBesselFunction := by
  have he : cubicSourceResidualFunction=ᵐ[hyperbolicVolume]sourceBesselFunction := by
    filter_upwards [cubicSourceResidualFunction_represents_projection,sourceBesselFunction_represents_projection]
      with w hw hs
    exact hw.symm.trans hs
  exact Measure.eq_of_ae_eq he cubicSourceResidualFunction_continuous sourceBesselFunction_continuous

theorem cubicSourceResidualFunction_bessel (v:ℝ) (hv:0<v) (z:ℂ) :
    cubicSourceResidualFunction (upperPoint z v hv)=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)+
      ∑'h:ActualEisensteinCubic.O,(if h=0 then 0 else sourceResidualFourierCoefficient h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [cubicSourceResidualFunction_eq_bessel,sourceBesselFunction,SubexponentialBesselCoefficients.fullFunction,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    sourceBesselCoefficients.series_bessel v hv z]
  rfl

end CubicEisenstein

end

end OAI
