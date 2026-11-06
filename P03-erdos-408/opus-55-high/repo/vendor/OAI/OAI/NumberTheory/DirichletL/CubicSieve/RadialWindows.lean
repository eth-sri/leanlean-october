module

public import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich
public import OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open Filter
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped ArithmeticFunction.Moebius
open Filter
open scoped ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open Filter Asymptotics MeasureTheory
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open scoped ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical ContDiff
open scoped Classical ContDiff
open scoped Classical
open scoped Classical ContDiff
open scoped Classical
open scoped Classical ContDiff
open scoped Classical ContDiff
open scoped Classical ContDiff
open scoped Classical
open scoped Classical ContDiff
open Set
open scoped Classical
open scoped Classical

open scoped Classical
namespace SecondPassArithmetic

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

end SecondPassArithmetic

open scoped Classical
namespace FirstPassCubeLabels

variable {ι:Type*} (p:ι→O) (B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)

end FirstPassCubeLabels

namespace SecondPassArithmetic

section

namespace CubeCoordinates
variable {ι:Type*}
def swap (b:CubeCoordinates ι) : CubeCoordinates ι :=
  ⟨b.rightExponent,b.leftExponent,b.rightDivisor,b.leftDivisor⟩
@[simp] lemma swap_swap (b:CubeCoordinates ι) : b.swap.swap=b := by cases b;rfl
end CubeCoordinates
end
section

open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

end

open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped Classical ENNReal

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
local instance : BorelSpace EuclideanSpatial := ⟨rfl⟩

def euclideanC1cToH1 (f : C1c (E := EuclideanSpatial)) :
    h1 (E := EuclideanSpatial) («μ» := (volume : Measure EuclideanSpatial)) := by
  let gr := graph (E := EuclideanSpatial) («μ» := (volume : Measure EuclideanSpatial))
  refine ⟨gr f,?_⟩
  exact (LinearMap.range gr).le_topologicalClosure ⟨f,rfl⟩

lemma euclideanC1c_supported_range (K : Set EuclideanSpatial) (hK : MeasurableSet K)
    (f : C1c (E := EuclideanSpatial)) (hf : Function.support f.1⊆K) :
    toL2 («μ» := volume) f∈LinearMap.range
      (Lp.extendByZeroₗᵢ («μ» := (volume : Measure EuclideanSpatial)) (p := (2:ℝ≥0∞)) hK).toLinearMap := by
  have hmem := memLp_of_mem_C1c («μ» := (volume : Measure EuclideanSpatial)) f.2
  have hres : MemLp f.1 2 (volume.restrict K) := hmem.mono_measure Measure.restrict_le_self
  refine ⟨hres.toLp f.1,?_⟩
  apply Lp.ext
  have hext := Lp.extendByZeroₗᵢ_ae_eq («μ» := (volume : Measure EuclideanSpatial)) hK (hres.toLp f.1)
  have hr : ∀ᵐx ∂(volume : Measure EuclideanSpatial),x∈K→hres.toLp f.1 x=f.1 x :=
    (ae_restrict_iff' hK).mp hres.coeFn_toLp
  have hg : (toL2 («μ» := volume) f : EuclideanSpatial→ℝ)=ᵐ[volume]f.1 := hmem.coeFn_toLp
  filter_upwards [hext,hr,hg] with x hx hrx hgx
  simp only [LinearIsometry.coe_toLinearMap]
  rw [hx,hgx]
  by_cases hxm : x∈K
  · simp_all
  · rw [Set.indicator_of_notMem hxm]
    symm
    by_contra hne
    simp_all

def euclideanC1cToSupportedH1 (K : Set EuclideanSpatial) (hK : MeasurableSet K)
    (f : C1c (E := EuclideanSpatial)) (hf : Function.support f.1⊆K) :
    h1On (E := EuclideanSpatial) K hK :=
  ⟨euclideanC1cToH1 f,euclideanC1c_supported_range K hK f hf⟩

lemma compact_clm_closedBall {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ V] [NormedSpace ℝ W] (T : V →L[ℝ] W)
    (hT : IsCompactOperator T) (R : ℝ) : IsCompact (closure (T '' Metric.closedBall 0 R)) :=
  IsCompactOperator.isCompact_closure_image_closedBall (f := T.toLinearMap) hT R

theorem euclidean_C1c_family_precompact (K : Set EuclideanSpatial) (hK : IsCompact K)
    (family : Set (C1c (E := EuclideanSpatial))) (R : ℝ)
    (hsupp : ∀f∈family,Function.support f.1⊆K)
    (hmass : ∀f∈family,‖toL2 («μ» := volume) f‖≤R)
    (hgrad : ∀f∈family,‖toL2Grad («μ» := volume) f‖≤R) :
    IsCompact (closure (toL2 («μ» := (volume : Measure EuclideanSpatial)) '' family)) := by
  let hKm := hK.measurableSet
  have hc := compact_clm_closedBall
    (V := h1On (E := EuclideanSpatial) K hKm)
    (W := Lp ℝ 2 (volume : Measure EuclideanSpatial))
    (h1OnToL2 (E := EuclideanSpatial) K hKm)
    (isCompactOperator_h1OnToL2 (E := EuclideanSpatial) hK hKm) R
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨euclideanC1cToSupportedH1 K hKm f (hsupp f hf),?_,rfl⟩
  have hn : ‖euclideanC1cToSupportedH1 K hKm f (hsupp f hf)‖≤R :=
    max_le (hmass f hf) (hgrad f hf)
  simpa only [Metric.mem_closedBall,dist_zero_right (euclideanC1cToSupportedH1 K hKm f (hsupp f hf))] using hn

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical ContDiff Manifold ENNReal

namespace CubicEisenstein

abbrev KernelFundamentalVolume : Measure HyperbolicSpace :=
  hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)

abbrev KernelGradientL2 := Lp (EuclideanSpace ℂ (Fin 3)) 2 KernelFundamentalVolume

lemma kernelTestPartial_continuous (f : kernelSmoothTests) (j : Fin 3) :
    Continuous (fun w => kernelTestPartial f w j) := by
  rw [continuous_iff_continuousAt]
  intro w
  exact (((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).continuousAt_fderiv
    (by simp)).clm_apply continuousAt_const).comp
      hyperbolicEuclideanCoordinates_continuous.continuousAt

lemma kernelGradientAt_continuous (f : kernelSmoothTests) :
    Continuous (fun w => kernelGradientAt w f) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  exact (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
    (kernelTestPartial_continuous f j)

lemma kernelGradientAt_memLp (f : kernelSmoothTests) :
    MemLp (fun w => kernelGradientAt w f) 2 KernelFundamentalVolume := by
  apply (memLp_two_iff_integrable_sq_norm
    (kernelGradientAt_continuous f).aestronglyMeasurable).mpr
  have hh := (quotient_projection_measurePreserving globalKubotaKernel).integrable_comp_of_integrable
    (kernelQuotientEnergyDensity_integrable f)
  have he : (fun w => kernelQuotientEnergyDensity f (integralOrbitProjection globalKubotaKernel w))=
      kernelTestEnergyDensity f := rfl
  dsimp only [Function.comp_def] at hh
  rw [he] at hh
  simpa only [kernelGradientAt_norm_sq] using hh

def kernelGradientToL2 (f : kernelSmoothTests) : KernelGradientL2 :=
  (kernelGradientAt_memLp f).toLp (fun w => kernelGradientAt w f)

lemma kernelGradientToL2_coe (f : kernelSmoothTests) :
    (kernelGradientToL2 f : HyperbolicSpace → EuclideanSpace ℂ (Fin 3))=ᵐ[KernelFundamentalVolume]
      fun w => kernelGradientAt w f := (kernelGradientAt_memLp f).coeFn_toLp

lemma kernelGradientToL2_inner (f g : kernelSmoothTests) :
    inner ℂ (kernelGradientToL2 f) (kernelGradientToL2 g)=kernelDirichletForm f g := by
  rw [L2.inner_def,kernelDirichletForm,integralQuotientVolume_integral _ _
    (kernelDirichletPairDensity_integrable f g).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [kernelGradientToL2_coe f,kernelGradientToL2_coe g] with w hf hg
  rw [hf,hg,kernelDirichletPairDensity_coordinate]

lemma kernelGradientToL2_norm_sq (f : kernelSmoothTests) :
    ‖kernelGradientToL2 f‖^2=kernelDirichletEnergy f := by
  have hh := kernelGradientToL2_inner f f
  rw [inner_self_eq_norm_sq_to_K,kernelDirichletForm_self] at hh
  rw [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow] at hh
  exact Complex.ofReal_injective hh

def kernelGradientLinear : kernelSmoothTests →ₗ[ℂ] KernelGradientL2 where
  toFun := kernelGradientToL2
  map_add' f g := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (f+g),kernelGradientToL2_coe f,
      kernelGradientToL2_coe g,Lp.coeFn_add (kernelGradientToL2 f) (kernelGradientToL2 g)]
      with w hfg hf hg hadd
    simp only [hfg,hadd,Pi.add_apply,hf,hg,map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (c•f),kernelGradientToL2_coe f,
      Lp.coeFn_smul c (kernelGradientToL2 f)] with w hcf hf hsmul
    simp only [RingHom.id_apply,hcf,hsmul,Pi.smul_apply,hf,map_smul]

def kernelInitialGradientGraph : Submodule ℂ (KernelQuotientL2 × KernelGradientL2) :=
  LinearMap.range (kernelSmoothTestsToL2.prod kernelGradientLinear)

def kernelInitialGradient : KernelQuotientL2 →ₗ.[ℂ] KernelGradientL2 :=
  kernelInitialGradientGraph.toLinearPMap

end CubicEisenstein

end

end OAI
