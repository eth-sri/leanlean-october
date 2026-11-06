module
public import OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierExpansion
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
open scoped Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_omega_relation : omega^2+omega+1=(0:Eis) := by
  apply eisEmbedding_injective
  pm_94 map_add map_pow map_one map_zero eisEmbedding_omega_actual
  exact EisensteinEmbedding.omega3_sq

def lowerCuspMatrix (t : Eis) : SL(2,Eis) :=
  ⟨!![1,0;t,1],by simp_all⟩

def ramifiedParabolic (t x : Eis) : levelThree := by
  let M : SL(2,Eis) := ⟨!![1-3*t*x,3*x;-3*t^2*x,1+3*t*x],by
    rw [Matrix.det_fin_two]
    change (1-3*t*x)*(1+3*t*x)-(3*x)*(-3*t^2*x)=1
    ring⟩
  pm_6726
  · exact ⟨-t*x,by change 1-3*t*x-1=3*(-t*x);ring⟩
  · exact ⟨x,by change 3*x-0=3*x;ring⟩
  · exact ⟨-t^2*x,by change -3*t^2*x-0=3*(-t^2*x);ring⟩
  · exact ⟨t*x,by change 1+3*t*x-1=3*(t*x);ring⟩

lemma ramifiedParabolic_mul_lower (t x : Eis) :
    (ramifiedParabolic t x : SL(2,Eis))*lowerCuspMatrix t=
      lowerCuspMatrix t*(upperTranslation x : SL(2,Eis)) := by
  apply Subtype.ext
  change (ramifiedParabolic t x : Matrix (Fin 2) (Fin 2) Eis) *
    (lowerCuspMatrix t : Matrix (Fin 2) (Fin 2) Eis) =
    (lowerCuspMatrix t : Matrix (Fin 2) (Fin 2) Eis) *
      (upperTranslation x : Matrix (Fin 2) (Fin 2) Eis)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [ramifiedParabolic,lowerCuspMatrix,upperTranslation,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma ramifiedParabolic_character (t x : Eis) :
    complexCharacter (ramifiedParabolic t x)=
      eisEmbedding (symbol (-t) (1-3*t*x)) := by
  simp only [complexCharacter,MonoidHom.comp_apply,character,ramifiedParabolic]
  apply congrArg eisEmbedding
  apply symbol_congr
  refine ⟨t,?_⟩
  change (-3*t^2*x)-(-t)=(1-3*t*x)*t
  ring

lemma ramifiedParabolic_omega_value (A B : ℤ) :
    complexCharacter (ramifiedParabolic omega (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding (cubicExp (A+B)) := by
  rw [ramifiedParabolic_character]
  have hd : 1-3*omega*ActualEisensteinCoordinates.eval A B=primaryCoord B (B-A) := by
    rw [primaryCoord_eq]
    change 1-3*omega*((A:Eis)+(B:Eis)*omega)=_
    push_cast
    linear_combination -3*(B:Eis)*ramified_omega_relation
  rw [hd,symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),linearRay_primaryCoord]
  congr 2
  ring

lemma ramifiedParabolic_omega_sq_value (A B : ℤ) :
    complexCharacter (ramifiedParabolic (omega^2) (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding (cubicExp (-(A+B))) := by
  rw [ramifiedParabolic_character]
  have hd : 1-3*omega^2*ActualEisensteinCoordinates.eval A B=primaryCoord (A-B) A := by
    rw [primaryCoord_eq]
    change 1-3*omega^2*((A:Eis)+(B:Eis)*omega)=_
    push_cast
    linear_combination -3*((A:Eis)+(B:Eis)*omega-(B:Eis))*ramified_omega_relation
  rw [hd,symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) 2,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),linearRay_primaryCoord]
  have he : cubicExp (2*((A-B)*2+(-1)*A))=cubicExp (-(A+B)) := by
    apply cubicExp_eq_of_dvd_sub
    exact ⟨A-B,by ring⟩
  have hs : cubicExp ((A-B)*2+(-1)*A)^2=cubicExp (2*((A-B)*2+(-1)*A)) := by
    rw [pow_two,←cubicExp_add]
    congr 1
    ring
  convert congrArg eisEmbedding (hs.trans he) using 1 ; congr 2 ; ring_nf

def ramifiedSourceFunction (t : Eis) (w : HyperbolicSpace) : ℂ :=
  cubicSourceResidualFunction (integralComplexMatrix (lowerCuspMatrix t) • w)

lemma ramifiedSourceFunction_continuous (t : Eis) : Continuous (ramifiedSourceFunction t) :=
  cubicSourceResidualFunction_continuous.comp (continuous_const_smul _)

lemma ramifiedSourceFunction_translate (t x : Eis) (w : HyperbolicSpace) :
    ramifiedSourceFunction t (complexMatrix (upperTranslation x) • w)=
      eisEmbedding (symbol (-t) (1-3*t*x))*ramifiedSourceFunction t w := by
  have he := cubicSourceResidualFunction_automorphy
    (sourceLevelInclusion (ramifiedParabolic t x))
    (integralComplexMatrix (lowerCuspMatrix t) • w)
  rw [sourceLevelInclusion_character,ramifiedParabolic_character] at he
  change cubicSourceResidualFunction
    (integralComplexMatrix (ramifiedParabolic t x : SL(2,Eis)) •
      (integralComplexMatrix (lowerCuspMatrix t) • w))=_ at he
  rw [←mul_smul,←map_mul,ramifiedParabolic_mul_lower,map_mul,mul_smul] at he
  exact he

section
variable (A B : ℤ) (w : HyperbolicSpace)
include A B w
lemma ramifiedSourceFunction_omega_translate :
    ramifiedSourceFunction omega
      (complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • w)=
      eisEmbedding (cubicExp (A+B))*ramifiedSourceFunction omega w := by
  rw [ramifiedSourceFunction_translate]
  rw [←ramifiedParabolic_character,ramifiedParabolic_omega_value]

lemma ramifiedSourceFunction_omega_sq_translate :
    ramifiedSourceFunction (omega^2)
      (complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • w)=
      eisEmbedding (cubicExp (-(A+B)))*ramifiedSourceFunction (omega^2) w := by
  rw [ramifiedSourceFunction_translate]
  rw [←ramifiedParabolic_character,ramifiedParabolic_omega_sq_value]
end

end

section
open MeasureTheory Filter
open scoped Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CubicRamified
open EisensteinEmbedding (omega3)
local notation "Eis" => ActualEisensteinCubic.O

lemma embedding_cubicExp (n : ℤ) :
    eisEmbedding (cubicExp n)=Complex.exp (2*Real.pi*Complex.I*(n:ℂ)/3) := by
  have hw : omega3=Complex.exp (2*Real.pi*Complex.I/3) := by
    rw [←TraceLambdaPhase.exp_minus_four_pi_div_three]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    exact ⟨-1,by push_cast;ring⟩
  rw [cubicExp,map_pow,eisEmbedding_omega_actual,hw,←Complex.exp_nat_mul]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-(n/3),?_⟩
  have hn : (n%3).toNat=(n%3) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hnc : ((n%3).toNat:ℂ)=((n%3:ℤ):ℂ) := by exact_mod_cast hn
  have he : ((n%3:ℤ):ℂ)=(n:ℂ)-3*((n/3:ℤ):ℂ) := by
    have he0 : n%3=n-3*(n/3) := by omega
    exact_mod_cast he0
  rw [hnc,he]
  push_cast
  ring

def ramifiedShift10 : ℂ := eisEmbedding (omega-1)/(9*eisLam)

def ramifiedShift19 : ℂ := eisEmbedding (-2-omega)/(9*eisLam)

lemma ramifiedShift10_period (A B : ℤ) :
    ShortDraftTrace.breveE (ramifiedShift10*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B)))=
      eisEmbedding (cubicExp (A+B)) := by
  have he : ramifiedShift10*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding ((omega-1)*ActualEisensteinCoordinates.eval A B)/eisLam/3 := by
    rw [ramifiedShift10,map_mul]
    ring
  have ht := breveE_real_trace_of_O (3:ℝ) ((omega-1)*ActualEisensteinCoordinates.eval A B)
  pm_7527
  have hcoords : (ActualEisensteinCoordinates.coords
      ((omega-1)*ActualEisensteinCoordinates.eval A B)).2=A-2*B := by
    have hw : omega-1=ActualEisensteinCoordinates.eval (-1) 1 := by
      simp only [ActualEisensteinCoordinates.eval,Int.cast_neg,Int.cast_one,one_mul]
      change omega-1=-1+omega
      ring
    rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
    ring
  rw [hcoords,←embedding_cubicExp]
  exact congrArg eisEmbedding (cubicExp_eq_of_dvd_sub ⟨-B,by ring⟩)

lemma ramifiedShift19_period (A B : ℤ) :
    ShortDraftTrace.breveE (ramifiedShift19*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B)))=
      eisEmbedding (cubicExp (-(A+B))) := by
  have he : ramifiedShift19*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding ((-2-omega)*ActualEisensteinCoordinates.eval A B)/eisLam/3 := by
    rw [ramifiedShift19,map_mul]
    ring
  have ht := breveE_real_trace_of_O (3:ℝ) ((-2-omega)*ActualEisensteinCoordinates.eval A B)
  pm_7527
  have hcoords : (ActualEisensteinCoordinates.coords
      ((-2-omega)*ActualEisensteinCoordinates.eval A B)).2=-(A+B) := by
    have hw : -2-omega=ActualEisensteinCoordinates.eval (-2) (-1) := by
      pm_382 ActualEisensteinCoordinates.eval Int.cast_neg Int.cast_one Int.cast_ofNat neg_mul one_mul
      change -2-omega=-2+-omega
      ring
    rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
    ring
  rw [hcoords,embedding_cubicExp]

section
variable (x : Eis) (z : ℂ) (v : ℝ) (hv : 0<v)
include x z v hv
lemma ramifiedSourceFunction_upper_shift10 :
    ramifiedSourceFunction omega (upperPoint (z+3*eisEmbedding x) v hv)=
      ShortDraftTrace.breveE (ramifiedShift10*(3*eisEmbedding x))*
        ramifiedSourceFunction omega (upperPoint z v hv) := by pm_3610 ramifiedShift10_period ramifiedSourceFunction_omega_translate

lemma ramifiedSourceFunction_upper_shift19 :
    ramifiedSourceFunction (omega^2) (upperPoint (z+3*eisEmbedding x) v hv)=
      ShortDraftTrace.breveE (ramifiedShift19*(3*eisEmbedding x))*
        ramifiedSourceFunction (omega^2) (upperPoint z v hv) := by pm_3610 ramifiedShift19_period ramifiedSourceFunction_omega_sq_translate
end

end

section
open Filter MeasureTheory
open scoped Classical Topology MatrixGroups ENNReal

def arbitraryCuspCompact (M : SL(2,ℂ)) (a b : ℝ) : Set HyperbolicSpace :=
  (M • ·) '' cuspHeightCompact a b

section
variable (M : SL(2,ℂ)) (a b : ℝ)
include M a b
lemma arbitraryCuspCompact_isCompact (ha : 0<a) :
    IsCompact (arbitraryCuspCompact M a b) :=
  (cuspHeightCompact_isCompact a b ha).image (continuous_const_smul M)

lemma arbitraryCusp_image_restrict_le (ha : 0<a) :
    hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b)≤
      (1:ℝ≥0∞) • hyperbolicVolume.restrict (arbitraryCuspCompact M a b) := by
  simpa only [one_smul,arbitraryCuspCompact] using Measure.restrict_mono_set hyperbolicVolume
    (Set.image_mono (cuspPeriodStrip_subset_heightCompact a b ha))

lemma arbitraryCusp_smul_measurePreserving :
    MeasurePreserving (M • ·) (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      (hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b)) :=
  (measurePreserving_smul M hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul M) _
end

def arbitraryCuspPullback (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    KernelQuotientL2→L[ℂ]CuspHeightStripL2 a b :=
  (Lp.compMeasurePreservingₗᵢ ℂ (M • ·) (arbitraryCusp_smul_measurePreserving M a b)).toContinuousLinearMap.comp
    ((dominatedComplexL2 (by simp : (1:ℝ≥0∞)≠⊤)
      (arbitraryCusp_image_restrict_le M a b ha)).comp
      (kernelCompactPullbackCLM (arbitraryCuspCompact M a b)
        (arbitraryCuspCompact_isCompact M a b ha)))

section
variable (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
include M a b ha
lemma arbitraryCuspPullback_ae
    (F : KernelQuotientL2) :
    arbitraryCuspPullback M a b ha F=ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip a b)]
      fun w => F (integralOrbitProjection globalKubotaKernel (M • w)) := by
  have h1 := dominatedComplexL2_ae (by simp : (1:ℝ≥0∞)≠⊤)
    (arbitraryCusp_image_restrict_le M a b ha)
    (kernelCompactPullbackCLM (arbitraryCuspCompact M a b)
      (arbitraryCuspCompact_isCompact M a b ha) F)
  have h2 := (Measure.absolutelyContinuous_of_le_smul
    (arbitraryCusp_image_restrict_le M a b ha)).ae_eq
      (kernelCompactPullbackCLM_ae (arbitraryCuspCompact M a b)
        (arbitraryCuspCompact_isCompact M a b ha) F)
  exact (Lp.coeFn_compMeasurePreserving _ (arbitraryCusp_smul_measurePreserving M a b)).trans
    ((arbitraryCusp_smul_measurePreserving M a b).quasiMeasurePreserving.ae_eq_comp (h1.trans h2))

lemma arbitraryCusp_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving
      (fun w => integralOrbitProjection globalKubotaKernel (M • w))
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      (integralQuotientVolume globalKubotaKernel) := by
  have hcompact : Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (arbitraryCuspCompact M a b))
      (integralQuotientVolume globalKubotaKernel) :=
    ⟨measurable_integralOrbitProjection _,Measure.absolutelyContinuous_of_le_smul
      (kernelCompactMultiplicity_spec _ (arbitraryCuspCompact_isCompact M a b ha))⟩
  have himage : Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b))
      (integralQuotientVolume globalKubotaKernel) :=
    ⟨hcompact.measurable,((Measure.absolutelyContinuous_of_le_smul
      (arbitraryCusp_image_restrict_le M a b ha)).map
        (measurable_integralOrbitProjection _)).trans hcompact.absolutelyContinuous⟩
  exact himage.comp (arbitraryCusp_smul_measurePreserving M a b).quasiMeasurePreserving
end

def arbitraryCuspQuotientCompact (M : SL(2,ℂ)) (a b : ℝ) : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' arbitraryCuspCompact M a b

section
variable (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
include M a b ha
lemma arbitraryCuspQuotientCompact_isCompact :
    IsCompact (arbitraryCuspQuotientCompact M a b) :=
  (arbitraryCuspCompact_isCompact M a b ha).image (continuous_integralOrbitProjection _)

lemma arbitraryCusp_mem_compact
    (w : HyperbolicSpace) (hw : w∈cuspPeriodStrip a b) :
    integralOrbitProjection globalKubotaKernel (M • w)∈arbitraryCuspQuotientCompact M a b :=
  ⟨M • w,⟨w,cuspPeriodStrip_subset_heightCompact a b ha hw,rfl⟩,rfl⟩
end

end

section
open Filter MeasureTheory
open scoped Classical Topology MatrixGroups InnerProductSpace ENNReal

def arbitraryCuspWeightedPhase (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ)
    (w : HyperbolicSpace) : ℂ :=
  ρ (hyperbolicHeight w)*ShortDraftTrace.breveE (-freq*hyperbolicHorizontal w)

section
variable (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ)
include ρ freq
lemma arbitraryCuspWeightedPhase_continuous :
    Continuous (arbitraryCuspWeightedPhase ρ freq) := by
  unfold arbitraryCuspWeightedPhase
  apply (ρ.continuous.comp hyperbolicHeight_continuous).mul
  change Continuous (fun w : HyperbolicSpace =>
    Complex.exp (2*Real.pi*Complex.I*((-freq*hyperbolicHorizontal w)+
      starRingEnd ℂ (-freq*hyperbolicHorizontal w))))
  have hh := hyperbolicHorizontal_continuous
  fun_prop

lemma arbitraryCuspWeightedPhase_bound
    (w : HyperbolicSpace) : ‖arbitraryCuspWeightedPhase ρ freq w‖≤‖ρ‖ := by
  rw [arbitraryCuspWeightedPhase,norm_mul,breveE_norm,mul_one]
  exact ρ.norm_coe_le_norm _
end

lemma arbitraryCuspFourierTest_memLp (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) :
    MemLp (fun w => star (arbitraryCuspWeightedPhase ρ freq w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) := by
  pm_8500 arbitraryCuspWeightedPhase_continuous freq
  exact Eventually.of_forall (fun w => by rw [norm_star];exact arbitraryCuspWeightedPhase_bound ρ freq w)

def arbitraryCuspFourierTestL2 (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) : CuspHeightStripL2 a b :=
  (arbitraryCuspFourierTest_memLp a b ha ρ freq).toLp
    (fun w => star (arbitraryCuspWeightedPhase ρ freq w))

def arbitraryCuspHeightFourier (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (arbitraryCuspFourierTestL2 a b ha ρ freq)).comp
    (arbitraryCuspPullback M a b ha)

section
variable (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) (F : KernelQuotientL2)
include M a b ha ρ freq F
lemma arbitraryCuspHeightFourier_integral :
    arbitraryCuspHeightFourier M a b ha ρ freq F=
      ∫w in cuspPeriodStrip a b,
        F (integralOrbitProjection globalKubotaKernel (M • w))*
          arbitraryCuspWeightedPhase ρ freq w∂ hyperbolicVolume := by
  change inner ℂ (arbitraryCuspFourierTestL2 a b ha ρ freq) (arbitraryCuspPullback M a b ha F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (arbitraryCuspFourierTest_memLp a b ha ρ freq),
    arbitraryCuspPullback_ae M a b ha F] with w hw hp
  pm_7424 arbitraryCuspFourierTestL2

lemma arbitraryCuspHeightFourier_restrict :
    arbitraryCuspHeightFourier M a b ha ρ freq
      (kernelMassRestrictionCLM (arbitraryCuspQuotientCompact M a b)
        (arbitraryCuspQuotientCompact_isCompact M a b ha).measurableSet F)=
      arbitraryCuspHeightFourier M a b ha ρ freq F := by
  rw [arbitraryCuspHeightFourier_integral,arbitraryCuspHeightFourier_integral]
  have he := (arbitraryCusp_quasiMeasurePreserving M a b ha).ae_eq_comp
    (kernelMassRestriction_coe (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha).measurableSet F)
  pm_3665
  exact congrArg (fun z : ℂ => z*arbitraryCuspWeightedPhase ρ freq w)
    (hw.trans (Set.indicator_of_mem (arbitraryCusp_mem_compact M a b ha w hwm) _))
end

def arbitraryCuspHeightFamily (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) (s : ℂ) : ℂ :=
  arbitraryCuspHeightFourier M a b ha ρ freq
    (kernelLocalCorrectedSeed (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha) 2 3 (by norm_num) (by norm_num) s)

section
variable (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) (ρ : BoundedContinuousFunction ℝ ℂ)
include M a b ha ρ
lemma arbitraryCuspHeightFamily_analyticAt (freq s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (arbitraryCuspHeightFamily M a b ha ρ freq) s :=
  (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (arbitraryCuspHeightFourier M a b ha ρ freq) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _
        (arbitraryCuspQuotientCompact_isCompact M a b ha)
        2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma arbitraryCuspHeightFamily_residue_limit (freq : ℂ) :
    Tendsto (fun s : ℂ => (s-4/3)*arbitraryCuspHeightFamily M a b ha ρ freq s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (arbitraryCuspHeightFourier M a b ha ρ freq cubicEisensteinResidue)) := by
  have hh := (arbitraryCuspHeightFourier M a b ha ρ freq).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (arbitraryCuspQuotientCompact_isCompact M a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,arbitraryCuspHeightFourier_restrict,
    arbitraryCuspHeightFamily] using hh

lemma arbitraryCuspHeightFamily_initial (freq s : ℂ) (hs : 4< s.re) (hi : 0< s.im) :
    arbitraryCuspHeightFamily M a b ha ρ freq s =
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (M • w)*
        arbitraryCuspWeightedPhase ρ freq w∂ hyperbolicVolume := by
  rw [arbitraryCuspHeightFamily,arbitraryCuspHeightFourier_integral]
  have he := (arbitraryCusp_quasiMeasurePreserving M a b ha).ae_eq_comp
    (cubicEisensteinLocalFamily_initial_ae (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha) s hs hi)
  pm_3665
  dsimp only [Function.comp_def] at hw
  rw [hw,Set.indicator_of_mem (arbitraryCusp_mem_compact M a b ha w hwm),kernelQuotientEisenstein_mk]
end

end

open Filter MeasureTheory
open scoped Classical Topology InnerProductSpace

private lemma inner_projection_sandwich {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : E →L[ℂ] G) (K : Submodule ℂ E) [K.HasOrthogonalProjection] (x y : G) :
    inner ℂ x (A (K.starProjection (A.adjoint y))) =
      inner ℂ (A (K.starProjection (A.adjoint x))) y := by
  rw [← A.adjoint_inner_left, ← A.adjoint_inner_right]
  exact (K.inner_starProjection_left_eq_right _ _).symm

lemma kernelThetaMassProjection_symmetric (F D : KernelQuotientL2) :
    inner ℂ F (kernelThetaMassProjection D)=inner ℂ (kernelThetaMassProjection F) D :=
  inner_projection_sandwich kernelEnergyMass kernelThetaNull F D

lemma kernelThetaMassProjection_eigenvector (F : KernelQuotientL2)
    (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph) :
    kernelThetaMassProjection F=(9/17:ℂ) • F := by
  let u : kernelEnergyLaplacian.domain := ⟨F,LinearPMap.mem_domain_of_mem_graph hF⟩
  have hu : kernelEnergyLaplacian u=(8/9:ℂ) • F :=
    kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph u) hF rfl
  let E : KernelEnergyGraph := kernelVariationalSolution (kernelEnergyLaplacian u+u)
  have hE : E∈kernelThetaNull := by
    change kernelSpectralFormOperator (8/9:ℂ) E=0
    dsimp only [E]
    rw [kernelSpectralFormOperator_of_domain,hu]
    change kernelVariationalSolution ((8/9:ℂ) • F-(8/9:ℂ) • F)=0
    rw [sub_self,map_zero]
  have hmass : kernelEnergyMass E=F := kernelEnergyLaplacian_resolvent_relation u
  have hscale : kernelEnergyMass.adjoint F=(9/17:ℂ) • E := by
    dsimp [E]
    rw [hu]
    change kernelVariationalSolution F=(9/17:ℂ) • kernelVariationalSolution ((8/9:ℂ) • F+F)
    rw [map_add,map_smul,smul_add,smul_smul]
    module
  change kernelEnergyMass (kernelThetaNull.starProjection (kernelEnergyMass.adjoint F))=_
  rw [hscale,map_smul,kernelThetaNull.starProjection_eq_self_iff.mpr hE,map_smul,hmass]

theorem kernelEisensteinResidueVector_pairing (a b : ℝ) (ha : 0<a) (hab : a<b)
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph) :
    inner ℂ F (kernelEisensteinResidueVector a b ha hab)=
      (3/2:ℂ)*inner ℂ F (kernelL2Defect a b ha hab (4/3)) := by
  rw [kernelEisensteinResidueVector,inner_smul_right,kernelThetaMassProjection_symmetric,
    kernelThetaMassProjection_eigenvector F hF,inner_smul_left]
  simp only [map_div₀,map_ofNat]
  ring


section
variable (S : Set KernelQuotient) (hS : IsCompact S) (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1< c) (hcd : c<d)
include S hS a b c d ha hab hc hcd
lemma kernelLocalCorrectedSeed_initial_eq
    (s : ℂ) (hs : 4< s.re) (hi : 0< s.im) :
    kernelLocalCorrectedSeed S hS a b (by linarith) hab s =
      kernelLocalCorrectedSeed S hS c d (by linarith) hcd s := by
  have h1 := kernelLocalCorrectedSeed_ae_eq S hS a b (by linarith) hab s
  have h2 := kernelLocalCorrectedSeed_ae_eq S hS c d (by linarith) hcd s
  have h3 := kernelEisensteinL2Correction_initial_overlap a b ha hab s hs hi
  have h4 := kernelEisensteinL2Correction_initial_overlap c d hc hcd s hs hi
  apply Lp.ext
  filter_upwards [h1,h2,h3,h4] with q hq1 hq2 hq3 hq4
  rw [hq1,hq2]
  by_cases hq : q∈S
  · simp only [Set.indicator_of_mem hq,kernelCorrectedSeed,hq3,hq4]
    ring
  · simp only [Set.indicator_of_notMem hq]

lemma kernelLocalCorrectedSeed_cutoff_eq :
    ∀s∈cuspUpperParameterRegion,
      kernelLocalCorrectedSeed S hS a b (by linarith) hab s =
        kernelLocalCorrectedSeed S hS c d (by linarith) hcd s := by
  pm_5319 h1 a b hab
  pm_5319 h2 c d hcd
  pm_3636
  have he : (kernelLocalCorrectedSeed S hS a b (by linarith) hab)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (kernelLocalCorrectedSeed S hS c d (by linarith) hcd) := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact kernelLocalCorrectedSeed_initial_eq S hS a b c d ha hab hc hcd s hs.1 hs.2
  exact h1.eqOn_of_preconnected_of_eventuallyEq h2 cuspUpperParameterRegion_convex.isPreconnected
    (by norm_num [cuspUpperParameterRegion]) he

lemma kernelEisensteinResidueVector_restrict_cutoff_eq :
    kernelMassRestrictionCLM S hS.measurableSet
        (kernelEisensteinResidueVector a b (by linarith) hab)=
      kernelMassRestrictionCLM S hS.measurableSet
        (kernelEisensteinResidueVector c d (by linarith) hcd) := by
  have h1 := (kernelLocalCorrectedSeed_residue_limit S hS a b (by linarith) hab).comp
    thetaApproach_tendsto_complex_punctured
  have h2 := (kernelLocalCorrectedSeed_residue_limit S hS c d (by linarith) hcd).comp
    thetaApproach_tendsto_complex_punctured
  have he : (fun t : ℝ =>
      ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
        kernelLocalCorrectedSeed S hS a b (by linarith) hab
          ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
        kernelLocalCorrectedSeed S hS c d (by linarith) hcd
          ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)) := by
    pm_3637
    rw [kernelLocalCorrectedSeed_cutoff_eq S hS a b c d ha hab hc hcd _
      (by constructor <;> simp [] <;> linarith)]
  exact tendsto_nhds_unique h1 (h2.congr' he.symm)
end

lemma kernelL2_eq_of_compact_restrictions (F G : KernelQuotientL2)
    (h : ∀S : Set KernelQuotient, ∀hS : IsCompact S,
      kernelMassRestrictionCLM S hS.measurableSet F=
        kernelMassRestrictionCLM S hS.measurableSet G) : F=G := by
  let S : ℕ→ Set KernelQuotient := fun n => {q | kernelQuotientBarrier 2 3 q≤n}
  have hS (n : ℕ) : IsCompact (S n) := kernelBarrier_sublevel_isCompact n
  have he (n : ℕ) : ∀ᵐq∂ integralQuotientVolume globalKubotaKernel, q∈S n → F q=G q := by
    have hi := h (S n) (hS n)
    have hf := kernelMassRestriction_coe (S n) (hS n).measurableSet F
    have hg := kernelMassRestriction_coe (S n) (hS n).measurableSet G
    filter_upwards [hf,hg] with q hf hg hq
    rw [Set.indicator_of_mem hq] at hf hg
    pm_8466 F hf
    pm_8466 G hg
    rw [hi] at hf
    exact hf.symm.trans hg
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr he] with q hq
  obtain ⟨n,hn⟩ := exists_nat_ge (kernelQuotientBarrier 2 3 q)
  exact hq n hn

theorem kernelEisensteinResidueVector_cutoff_independent
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1< c) (hcd : c<d) :
    kernelEisensteinResidueVector a b (by linarith) hab=
      kernelEisensteinResidueVector c d (by linarith) hcd := by
  apply kernelL2_eq_of_compact_restrictions
  intro S hS
  exact kernelEisensteinResidueVector_restrict_cutoff_eq S hS a b c d ha hab hc hcd

end CubicEisenstein

end

end OAI
