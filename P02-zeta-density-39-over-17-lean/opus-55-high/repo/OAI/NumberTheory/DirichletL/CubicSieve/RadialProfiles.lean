module
public import OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies
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

namespace SecondPassArithmetic

open scoped Classical SchwartzMap ContDiff Topology
open Filter

def positiveRadialProfile (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0<x then V (Real.log x) else 0

section
variable (V : ℝ → ℂ) (A : ℝ) (hV : ∀s,V s≠0→|s|≤A)
include V A hV
theorem positiveRadialProfile_support (x : ℝ) (hx : positiveRadialProfile V x≠0) :
    x∈Set.Icc (Real.exp (-A)) (Real.exp A) := by
  have hpos : 0<x := by
    pm_1453 hn hx positiveRadialProfile
  have hlog : |Real.log x|≤A := hV _ (by simpa [positiveRadialProfile,hpos] using hx)
  constructor
  · calc
      Real.exp (-A) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (abs_le.mp hlog).1
      _ = x := Real.exp_log hpos
  · calc
      x = Real.exp (Real.log x) := (Real.exp_log hpos).symm
      _ ≤ Real.exp A := Real.exp_le_exp.mpr (abs_le.mp hlog).2

theorem positiveRadialProfile_compact : HasCompactSupport (positiveRadialProfile V) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (fun x hx=>positiveRadialProfile_support V A hV x hx)
end

theorem positiveRadialProfile_smooth (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V)
    (A : ℝ) (hV : ∀s,V s≠0→|s|≤A) : ContDiff ℝ ∞ (positiveRadialProfile V) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hpos : 0<x
  · have he : positiveRadialProfile V=ᶠ[𝓝 x] (fun y=>V (Real.log y)) := by
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      change 0<y at hy
      simp only [positiveRadialProfile,ite_eq_left hy]
    exact (hVs.contDiffAt.comp x (Real.contDiffAt_log.mpr hpos.ne')).congr_of_eventuallyEq he
  · have hx : x<Real.exp (-A) := (le_of_not_gt hpos).trans_lt (Real.exp_pos _)
    have he : positiveRadialProfile V=ᶠ[𝓝 x] (fun _=>0) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      by_contra hn
      have hb := (positiveRadialProfile_support V A hV y hn).1
      exact (not_le_of_gt hy) hb
    exact (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq he

def radialFromLog (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) : 𝓢(ℝ,ℂ) :=
  (positiveRadialProfile_compact V A hV).toSchwartzMap (positiveRadialProfile_smooth V hVs A hV)

section
variable (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ) (hV : ∀s,V s≠0→|s|≤A) (x : ℝ)
include V hVs A hV x
@[simp] theorem radialFromLog_apply_pos (hx : 0<x) :
    radialFromLog V hVs A hV x=V (Real.log x) := by
  change positiveRadialProfile V x=_
  simp only [positiveRadialProfile,ite_eq_left hx]

theorem radialFromLog_support (hx : radialFromLog V hVs A hV x≠0) :
    Real.exp (-A)≤x ∧ x≤Real.exp A := positiveRadialProfile_support V A hV x hx
end

theorem radialFromLog_column {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    (hp : ∀i,p i≠0) (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (X : ℝ) (hX : 0<X) (S : Finset ι) :
    radialFromLog V hVs A hV (FirstPassCubeLabels.primeProductNorm p S/X)=
      V (FirstPassCubeLabels.columnLog p X S) :=
  radialFromLog_apply_pos V hVs A hV _ (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp S) hX)

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped Classical Topology ContDiff Manifold

def kernelTestPartitionTerm {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) : kernelSmoothTests :=
  ⟨fun q => ρ i q • f.1 q,(ρ i).contMDiff.smul f.2.1,
    HasCompactSupport.smul_left (f := fun q => ρ i q) (f' := f.1) f.2.2⟩

lemma kernelTestPartitionTerm_tsupport {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) :
    tsupport (kernelTestPartitionTerm ρ f i).1⊆tsupport (ρ i) :=
  tsupport_smul_subset_left _ _

lemma kernelTestPartition_sum {ι : Type*} [Fintype ι]
    (f : kernelSmoothTests)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient (tsupport f.1)) :
    ∑i,kernelTestPartitionTerm ρ f i=f := by
  apply Subtype.ext
  funext q
  simp only [Submodule.coe_sum,Finset.sum_apply,kernelTestPartitionTerm]
  rw [←Finset.sum_smul]
  by_cases hq : q∈tsupport f.1
  · have hs := ρ.sum_eq_one hq
    rw [finsum_eq_sum_of_fintype] at hs
    rw [hs,one_smul]
  · have hz : f.1 q=0 := image_eq_zero_of_notMem_tsupport hq
    rw [hz,smul_zero]

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical Topology ContDiff SchwartzMap LineDeriv

namespace CubicEisenstein

def kernelFullCutoffFun (χ : PositiveChartCutoff) (p : EuclideanSpatial) : ℝ :=
  Real.smoothTransition (4*χ.func p-1)

section
variable (χ : PositiveChartCutoff)
include χ
lemma kernelFullCutoffFun_smooth :
    ContDiff ℝ ∞ (kernelFullCutoffFun χ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul χ.smooth).sub contDiff_const)

lemma kernelFullCutoffFun_tsupport :
    tsupport (kernelFullCutoffFun χ)⊆tsupport χ.func := by
  apply closure_mono
  intro p hp
  change kernelFullCutoffFun χ p≠0 at hp
  change χ.func p≠0
  intro hz
  apply hp
  simp only [kernelFullCutoffFun,hz,mul_zero,zero_sub]
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)

lemma kernelFullCutoffFun_compact :
    HasCompactSupport (kernelFullCutoffFun χ) :=
  χ.compact.of_isClosed_subset (isClosed_tsupport _) (kernelFullCutoffFun_tsupport χ)
end

def kernelFullCutoff (χ : PositiveChartCutoff) : PositiveChartCutoff where
  func := kernelFullCutoffFun χ
  smooth := kernelFullCutoffFun_smooth χ
  compact := kernelFullCutoffFun_compact χ
  positive := (kernelFullCutoffFun_tsupport χ).trans χ.positive

section
variable (χ : PositiveChartCutoff) (p : EuclideanSpatial) (hp : p∈kernelChartCore χ)
include χ p hp
lemma kernelFullCutoff_one : (kernelFullCutoff χ).func p=1 := by
  apply Real.smoothTransition.one_of_one_le
  change (1/2 : ℝ)<χ.func p at hp
  linarith

lemma kernelFullCutoff_eventually_one : (kernelFullCutoff χ).func =ᶠ[𝓝 p] fun _ => 1 := by
  filter_upwards [(kernelChartCore_open χ).mem_nhds hp] with q hq
  exact kernelFullCutoff_one χ q hq
end

def kernelCoreLift (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    𝓢(EuclideanSpatial,ℂ) := kernelLocalizedSchwartz (kernelFullCutoff χ) f

section
variable (χ : PositiveChartCutoff)
include χ
lemma kernelCoreLift_eventually_eq (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∈kernelChartCore χ) :
    (kernelCoreLift χ f : EuclideanSpatial→ℂ)=ᶠ[𝓝 p] kernelTestField f := by
  filter_upwards [kernelFullCutoff_eventually_one χ p hp] with q hq
  pm_8523 q
  rw [hq,one_smul]

lemma kernelCoreLift_tsupport_outer (f : kernelSmoothTests) :
    tsupport (kernelCoreLift χ f)⊆tsupport χ.func :=
  (kernelLocalizedField_tsupport (kernelFullCutoff χ) f).trans (kernelFullCutoffFun_tsupport χ)

lemma kernelCoreLift_tsupport
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ) :
    tsupport (kernelCoreLift χ f)⊆kernelChartCore χ := by
  intro p hp
  have houter := kernelCoreLift_tsupport_outer χ f hp
  by_contra hn
  have hfp : kernelEuclideanProjection p∉tsupport f.1 := by
    pm_5412 houter hn
  pm_7365 hc houter
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hfp).comp_tendsto hc
  have hzero : (kernelCoreLift χ f : EuclideanSpatial→ℂ)=ᶠ[𝓝 p] 0 := by
    filter_upwards [hz] with q hq
    change (kernelFullCutoff χ).func q • f.1 (kernelEuclideanProjection q)=0
    change f.1 (kernelEuclideanProjection q)=0 at hq
    rw [hq,smul_zero]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hp

lemma kernelCoreLift_eq_on_outer
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ) :
    Set.EqOn (kernelCoreLift χ f) (kernelTestField f) (tsupport χ.func) := by
  intro p hp
  by_cases hc : p∈kernelChartCore χ
  · exact (kernelCoreLift_eventually_eq χ f p hc).self_of_nhds
  · have hz : kernelTestField f p=0 := by
      change f.1 (kernelEuclideanProjection p)=0
      apply image_eq_zero_of_notMem_tsupport
      pm_5412 hp hc
    pm_8523 p
    rw [hz,smul_zero]
end

def euclideanHeightCLM : EuclideanSpatial→L[ℝ]ℂ :=
  Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2)

lemma euclideanHeightCLM_apply (p : EuclideanSpatial) : euclideanHeightCLM p=(p 2:ℂ) := rfl

section
variable (f : 𝓢(EuclideanSpatial,ℂ))
include f
lemma upperHeightDivide_smooth
    (hpos : tsupport f⊆euclideanUpperHalf) :
    ContDiff ℝ ∞ (fun p : EuclideanSpatial => f p/(p 2:ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p 2=0
  · have hn : p∉tsupport f := by
      intro hf
      have hh := hpos hf
      change 0<p 2 at hh
      linarith
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpatial => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    simp only [hq,Pi.zero_apply,zero_div]
  · simpa only [div_eq_mul_inv,Pi.inv_apply,euclideanHeightCLM_apply] using
      (f.smooth ⊤).contDiffAt.mul (euclideanHeightCLM.contDiff.contDiffAt.fun_inv
        (Complex.ofReal_ne_zero.mpr hp))

lemma upperHeightDivide_compact
    (hcompact : HasCompactSupport f) :
    HasCompactSupport (fun p : EuclideanSpatial => f p/(p 2:ℂ)) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hcompact ⊢
  exact hcompact.mono (fun p hp => by simp only [hp,Pi.zero_apply,zero_div])
end

def upperHeightDivide (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    𝓢(EuclideanSpatial,ℂ) :=
  (upperHeightDivide_compact f hcompact).toSchwartzMap (upperHeightDivide_smooth f hpos)

section
variable (f : 𝓢(EuclideanSpatial,ℂ)) (hcompact : HasCompactSupport f)
include f hcompact
lemma upperHeightDivide_apply (hpos : tsupport f⊆euclideanUpperHalf)
    (p : EuclideanSpatial) : upperHeightDivide f hcompact hpos p=f p/(p 2:ℂ) := rfl

lemma upperHeightDivide_tsupport (hpos : tsupport f⊆euclideanUpperHalf) :
    tsupport (upperHeightDivide f hcompact hpos)⊆tsupport f := by
  apply closure_mono
  intro p hp
  change f p/(p 2:ℂ)≠0 at hp
  change f p≠0
  exact fun hz => hp (by rw [hz,zero_div])

lemma upperHeightDivide_lineDeriv (hpos : tsupport f⊆euclideanUpperHalf)
    (p u : EuclideanSpatial) (hp : p 2≠0) :
    (∂_{u} (upperHeightDivide f hcompact hpos)) p=
      ((∂_{u} f) p*(p 2:ℂ)-f p*(u 2:ℂ))/(p 2:ℂ)^2 := by
  have hf := (f.hasFDerivAt p).hasLineDerivAt u
  have hv := (euclideanHeightCLM.hasFDerivAt (x := p)).hasLineDerivAt u
  change HasDerivAt (fun t : ℝ => f (p+t•u)) ((∂_{u} f) p) 0 at hf
  change HasDerivAt (fun t : ℝ => ((p+t•u) 2:ℂ)) (u 2:ℂ) 0 at hv
  have hd := hf.div hv (by simpa using Complex.ofReal_ne_zero.mpr hp)
  have hline : HasLineDerivAt ℝ (upperHeightDivide f hcompact hpos)
      (((∂_{u} f) p*(p 2:ℂ)-f p*(u 2:ℂ))/(p 2:ℂ)^2) p u := by
    simpa only [HasLineDerivAt,upperHeightDivide_apply,Pi.div_apply,zero_smul,add_zero] using! hd
  exact ((upperHeightDivide f hcompact hpos).hasFDerivAt p).hasLineDerivAt u |>.unique hline

lemma upperSchwartz_derivative_compact (u : EuclideanSpatial) :
    HasCompactSupport (∂_{u} f : 𝓢(EuclideanSpatial,ℂ)) :=
  hcompact.fderiv_apply ℝ u
end

def upperWeightedPartial (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) (j : Fin 3) :
    𝓢(EuclideanSpatial,ℂ) :=
  upperHeightDivide (∂_{euclideanCoordinateVector j} f)
    (upperSchwartz_derivative_compact f hcompact _)
    ((SchwartzMap.tsupport_lineDerivOp_subset _ f).trans hpos)

def upperWeightedDivergence (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    𝓢(EuclideanSpatial,ℂ) :=
  -∑j : Fin 3,∂_{euclideanCoordinateVector j} (upperWeightedPartial f hcompact hpos j)

def complexHermitianBilin : ℂ→L[ℝ]ℂ→L[ℝ]ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap

section
variable (f g : 𝓢(EuclideanSpatial,ℂ))
include f g
lemma schwartz_hermitian_integrable :
    Integrable (fun p => star (f p)*g p) volume :=
  (SchwartzMap.bilinLeftCLM complexHermitianBilin g.hasTemperateGrowth f).integrable

lemma schwartz_hermitian_lineGreen (u : EuclideanSpatial) :
    (∫p,star (f p)*(∂_{u} g) p)=-∫p,star ((∂_{u} f) p)*g p :=
  SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left f g complexHermitianBilin u

lemma upperWeighted_green
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    (∫p,∑j : Fin 3,star (upperWeightedPartial f hcompact hpos j p)*
      (∂_{euclideanCoordinateVector j} g) p)=
      ∫p,star (upperWeightedDivergence f hcompact hpos p)*g p := by
  calc
    _ = ∑j : Fin 3,∫p,star (upperWeightedPartial f hcompact hpos j p)*
        (∂_{euclideanCoordinateVector j} g) p :=
      integral_finsetSum _ (fun j hj => schwartz_hermitian_integrable _ _)
    _ = -∑j : Fin 3,∫p,star ((∂_{euclideanCoordinateVector j}
        (upperWeightedPartial f hcompact hpos j)) p)*g p := by
      simp only [schwartz_hermitian_lineGreen,Finset.sum_neg_distrib]
    _ = _ := by
      rw [←integral_finsetSum _ (fun j hj => schwartz_hermitian_integrable _ _),←integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        simp only [upperWeightedDivergence,_root_.neg_apply,_root_.sum_apply,star_neg,star_sum,
          Finset.sum_mul,neg_mul])
end

def upperPositiveLaplacian (f : 𝓢(EuclideanSpatial,ℂ)) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,(∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} f)) p)+
    (p 2:ℂ)*(∂_{euclideanCoordinateVector 2} f) p

section
variable (f : 𝓢(EuclideanSpatial,ℂ)) (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) (p : EuclideanSpatial)
include f hcompact hpos p
lemma upperWeightedDivergence_apply_ne_zero (hp : p 2≠0) :
    upperWeightedDivergence f hcompact hpos p=upperPositiveLaplacian f p/(p 2:ℂ)^3 := by
  have hd (j : Fin 3) : (∂_{euclideanCoordinateVector j} (upperWeightedPartial f hcompact hpos j)) p=
      ((∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} f)) p*(p 2:ℂ)-
        (∂_{euclideanCoordinateVector j} f) p*(euclideanCoordinateVector j 2:ℂ))/(p 2:ℂ)^2 :=
    upperHeightDivide_lineDeriv _ _ _ p _ hp
  simp only [upperWeightedDivergence,Fin.sum_univ_three,_root_.neg_apply,_root_.add_apply]
  rw [hd 0,hd 1,hd 2]
  simp only [upperPositiveLaplacian,Fin.sum_univ_three]
  norm_num [euclideanCoordinateVector]
  field_simp [Complex.ofReal_ne_zero.mpr hp]
  ring

lemma upperWeightedDivergence_apply :
    upperWeightedDivergence f hcompact hpos p=upperPositiveLaplacian f p/(p 2:ℂ)^3 := by
  by_cases hp : p 2=0
  · have hz : ∀j : Fin 3,(∂_{euclideanCoordinateVector j}
        (upperWeightedPartial f hcompact hpos j)) p=0 := by
      intro j
      have hn : p∉tsupport (upperWeightedPartial f hcompact hpos j) := by
        intro hm
        have ht := hpos ((SchwartzMap.tsupport_lineDerivOp_subset _ f)
          (upperHeightDivide_tsupport _ _ _ hm))
        change 0<p 2 at ht
        linarith
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,fderiv_of_notMem_tsupport ℝ hn]
      rfl
    simp only [upperWeightedDivergence,_root_.neg_apply,_root_.sum_apply,hz,Finset.sum_const_zero,neg_zero,
      upperPositiveLaplacian,hp,Complex.ofReal_zero,zero_pow (by decide : 2≠0),
      zero_pow (by decide : 3≠0),zero_mul,zero_add,zero_div]
  · exact upperWeightedDivergence_apply_ne_zero f hcompact hpos p hp
end

theorem upperHyperbolic_green (f g : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    (∫p,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} f) p)*
      (∂_{euclideanCoordinateVector j} g) p/(p 2:ℂ))=
      ∫p,star (upperPositiveLaplacian f p)*g p/(p 2:ℂ)^3 := by
  have hh := upperWeighted_green f g hcompact hpos
  simpa only [upperWeightedPartial,upperHeightDivide_apply,upperWeightedDivergence_apply,
    star_div₀,star_pow,Complex.star_def,Complex.conj_ofReal,div_mul_eq_mul_div] using hh

end CubicEisenstein


namespace CubicEisenstein

section
variable (S : Set EuclideanSpatial) (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
include S hS hpos
lemma kernelEuclideanProjection_integral_complex
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient→ℂ)
    (hg : AEStronglyMeasurable g (integralQuotientVolume globalKubotaKernel)) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)=
      ∫q in kernelEuclideanProjection '' S,g q∂integralQuotientVolume globalKubotaKernel := by
  pm_3679

lemma hyperbolicEuclidean_setIntegral_complex (g : EuclideanSpatial→ℂ) :
    (∫p in S,g p∂hyperbolicEuclideanVolume)=∫p in S,g p/(p 2:ℂ)^3 := by
  rw [hyperbolicEuclideanVolume,MeasureTheory.restrict_withDensity hS,
    Measure.restrict_restrict hS,Set.inter_eq_left.mpr hpos,
    integral_withDensity_eq_integral_toReal_smul hyperbolicDensity_measurable
      (Eventually.of_forall (fun p => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  pm_7133 hpositive
  rw [hyperbolicDensity,ENNReal.toReal_ofReal (by positivity)]
  rw [Complex.real_smul]
  change (↑(((p 2)^3)⁻¹) : ℂ)*g p=g p/(p 2:ℂ)^3
  simp only [Complex.ofReal_inv,Complex.ofReal_pow,div_eq_mul_inv,mul_comm]
end

lemma kernelDirichletPairDensity_zero_of_notMem (f g : kernelSmoothTests) (q : KernelQuotient)
    (hq : q∉tsupport g.1) : kernelDirichletPairDensity f g q=0 := by
  have hz : kernelQuotientEnergyDensity g q=0 := by
    by_contra hn
    exact hq (kernelQuotientEnergyDensity_support g hn)
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)=0
    rw [kernelDirichletPairDensity_coordinate]
    have hg : kernelGradientAt w g=0 := by
      apply norm_eq_zero.mp
      have h := kernelGradientAt_norm_sq w g
      change kernelTestEnergyDensity g w=0 at hz
      rw [hz] at h
      nlinarith [norm_nonneg (kernelGradientAt w g)]
    rw [hg,inner_zero_right]

lemma kernelDirichletPairDensity_euclidean (f g : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelDirichletPairDensity f g (kernelEuclideanProjection p)=
      (p 2:ℂ)^2*∑j : Fin 3,star (fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector j))*
        fderiv ℝ (kernelTestField g) p (euclideanCoordinateVector j) := by
  pm_3678
  change kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))=_
  rw [kernelDirichletPairDensity_coordinate,PiLp.inner_apply]
  change (∑j : Fin 3,inner ℂ ((hyperbolicHeight (euclideanToHyperbolic p):ℂ)*kernelTestPartial f (euclideanToHyperbolic p) j)
    ((hyperbolicHeight (euclideanToHyperbolic p):ℂ)*kernelTestPartial g (euclideanToHyperbolic p) j))=_
  pm_3813 hv Finset.mul_sum Finset.sum_congr j hj
  simp only [kernelTestPartial,hc,←euclideanCoordinateVector_eq_basis,RCLike.inner_apply,
    map_mul,Complex.conj_ofReal,Complex.star_def]
  ring

section
variable (χ : PositiveChartCutoff) (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
include χ hinj
lemma kernelCoreLift_fderiv_eq_on_outer
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ)
    (p : EuclideanSpatial) (hp : p∈tsupport χ.func) :
    fderiv ℝ (kernelCoreLift χ f) p=fderiv ℝ (kernelTestField f) p := by
  by_cases hc : p∈kernelChartCore χ
  · exact (kernelCoreLift_eventually_eq χ f p hc).fderiv_eq
  · have hl : p∉tsupport (kernelCoreLift χ f) := fun h => hc (kernelCoreLift_tsupport χ hinj f hf h)
    have hfp : kernelEuclideanProjection p∉tsupport f.1 := by
      intro hfp
      obtain ⟨q,hq,heq⟩ := hf hfp
      exact hc ((hinj (kernelChartCore_subset χ hq) hp heq) ▸ hq)
    pm_7365 hcont hp
    have hz : kernelTestField f=ᶠ[𝓝 p]0 := (notMem_tsupport_iff_eventuallyEq.mp hfp).comp_tendsto hcont
    rw [fderiv_of_notMem_tsupport ℝ hl,hz.fderiv_eq,fderiv_zero]
    rfl

lemma kernelCoreLift_pair_on_outer
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ)
    (p : EuclideanSpatial) (hp : p∈tsupport χ.func) :
    kernelDirichletPairDensity f g (kernelEuclideanProjection p)=
      (p 2:ℂ)^2*∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p := by
  rw [kernelDirichletPairDensity_euclidean f g p (χ.positive hp)]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [←kernelCoreLift_fderiv_eq_on_outer χ hinj g hg p hp]
  by_cases hc : p∈kernelChartCore χ
  · rw [(kernelCoreLift_eventually_eq χ f p hc).fderiv_eq]
  · have hn : p∉tsupport (kernelCoreLift χ g) := fun h => hc (kernelCoreLift_tsupport χ hinj g hg h)
    rw [fderiv_of_notMem_tsupport ℝ hn]
    simp only [_root_.zero_apply,mul_zero,Finset.sum_const_zero]

theorem kernelDirichletForm_eq_chart_pairing
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ) :
    kernelDirichletForm f g=
      ∫p,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p/(p 2:ℂ) := by
  pm_1367
  pm_6958
  calc
    _ = ∫q in kernelEuclideanProjection '' S,kernelDirichletPairDensity f g q
        ∂integralQuotientVolume globalKubotaKernel := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      exact kernelDirichletPairDensity_zero_of_notMem f g q (fun h => hq (himg (hg h)))
    _ = ∫p in S,kernelDirichletPairDensity f g (kernelEuclideanProjection p)
        ∂hyperbolicEuclideanVolume :=
      (kernelEuclideanProjection_integral_complex S hS χ.positive hinj _
        (kernelDirichletPairDensity_integrable f g).aestronglyMeasurable).symm
    _ = ∫p in S,kernelDirichletPairDensity f g (kernelEuclideanProjection p)/(p 2:ℂ)^3 :=
      hyperbolicEuclidean_setIntegral_complex S hS χ.positive _
    _ = ∫p in S,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p/(p 2:ℂ) := by
      apply setIntegral_congr_fun hS
      intro p hp
      dsimp only
      rw [kernelCoreLift_pair_on_outer χ hinj f g hg p hp,←Finset.sum_div]
      have hv : (p 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (χ.positive hp).ne'
      field_simp [hv]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hn : p∉tsupport (kernelCoreLift χ g) := fun h => hp (kernelCoreLift_tsupport_outer χ g h)
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,fderiv_of_notMem_tsupport ℝ hn,
        _root_.zero_apply,mul_zero,zero_div,Finset.sum_const_zero]

theorem kernelDirichletForm_eq_chart_laplacian
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ) :
    kernelDirichletForm f g=
      ∫p,star (upperPositiveLaplacian (kernelCoreLift χ f) p)*kernelCoreLift χ g p/(p 2:ℂ)^3 := by
  rw [kernelDirichletForm_eq_chart_pairing χ hinj f g hg]
  exact upperHyperbolic_green _ _ (kernelLocalizedField_compact (kernelFullCutoff χ) f)
    ((kernelCoreLift_tsupport_outer χ f).trans χ.positive)
end

end CubicEisenstein

end

end OAI
