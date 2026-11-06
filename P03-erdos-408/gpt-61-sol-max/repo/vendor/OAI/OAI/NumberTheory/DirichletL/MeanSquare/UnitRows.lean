module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.MeanSquare.UniformPolynomialHeight

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
 
 
 
 
 
 
 
 

 
namespace CompletedUnitRows
 
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O
open CanonicalRowCompletion


def unitRowFamily (Ψ : ActualEisensteinCubic.O→*ℂ) (mask : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ) {F }
    (f : idealRange F) (I : Ideal ActualEisensteinCubic.O)  :=
  rowTwist Ψ mask (idealGenerator f.val) (u.val*idealGenerator I)

end CompletedUnitRows

 
namespace SecondPassArithmetic




open   FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

end SecondPassArithmetic

 
 

namespace CubicEisenstein

def euclideanAxisPath (p : EuclideanSpatial) (j : Fin 3) (t : ℝ)  :=
  WithLp.toLp 2 (Function.update p.ofLp j t)

section
variable (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial) (j : Fin 3) (t : ℝ)

lemma euclideanAxisPath_affine       :
    euclideanAxisPath p j t=p+(t-p j)•euclideanCoordinateVector j := by
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext k
  by_cases hk : k=j
  · subst k
    simp [euclideanAxisPath,euclideanCoordinateVector]
  · simp [euclideanAxisPath,euclideanCoordinateVector,Function.update,hk]

lemma euclideanAxisPath_self     :
    euclideanAxisPath p j (p j)=p := by
  rw [euclideanAxisPath_affine,sub_self,zero_smul,add_zero]

lemma euclideanAxisPath_hasDerivAt       :
    HasDerivAt (euclideanAxisPath p j) (euclideanCoordinateVector j) t := by
  have he : euclideanAxisPath p j=(fun t => p+(t-p j)•euclideanCoordinateVector j) :=
    funext (euclideanAxisPath_affine p j)
  rw [he]
  simpa only [sub_zero,one_smul,zero_add,Pi.add_apply,id_eq] using!
    (hasDerivAt_const t p).add (((hasDerivAt_id t).sub_const (p j)).smul_const (euclideanCoordinateVector j))

lemma euclideanAxisSlice_deriv    
        (hf : DifferentiableAt ℝ f (euclideanAxisPath p j t)) :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) t=
      fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j) :=
  (hf.hasFDerivAt.comp_hasDerivAt t (euclideanAxisPath_hasDerivAt p j t)).deriv

lemma euclideanAxisSlice_derivatives  
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p)  p  (hp : 0<p 2)  j  :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) (p j)=
      fderiv ℝ f p (euclideanCoordinateVector j) ∧
    deriv (deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)) (p j)=
      fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p (euclideanCoordinateVector j) := by
  constructor
  · simpa only [euclideanAxisPath_self] using euclideanAxisSlice_deriv f p j (p j)
      (by simpa only [euclideanAxisPath_self] using (hf p hp).differentiableAt (by simp))
  · have hc : ContinuousAt (fun t => euclideanAxisPath p j t 2) (p j) :=
      (by fun_prop)
    have hpos : 0<euclideanAxisPath p j (p j) 2 := by rw [euclideanAxisPath_self]; exact hp
    have he : deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)=ᶠ[𝓝 (p j)]
        (fun t => fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j)) := by
      filter_upwards [hc.eventually_const_lt hpos] with t ht
      exact euclideanAxisSlice_deriv f p j t ((hf _ ht).differentiableAt (by simp))
    rw [he.deriv_eq]
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p :=
      (((hf p hp).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
    have hd' : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j))
        (euclideanAxisPath p j (p j)) := by rwa [euclideanAxisPath_self]
    have hh := hd'.hasFDerivAt.comp_hasDerivAt (p j) (euclideanAxisPath_hasDerivAt p j (p j))
    simpa only [euclideanAxisPath_self,Function.comp_def] using! hh.deriv

end

def positiveEuclideanLaplacian (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial)  :=
  -(p 2:ℂ)^2*(∑j : Fin 3,fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p
    (euclideanCoordinateVector j))+(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector 2)

lemma positiveEuclideanLaplacian_eq_axis  f 
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p)  p  (hp : 0<p 2) :
    positiveEuclideanLaplacian f p=-axisLaplacian (fun q => f (WithLp.toLp 2 q)) p.ofLp := by
  unfold positiveEuclideanLaplacian axisLaplacian
  simp only [(euclideanAxisSlice_derivatives f hf p hp _).1,(euclideanAxisSlice_derivatives f hf p hp _).2]
  ring

lemma positiveEuclideanLaplacian_congr  f g   p 
    (he : f=ᶠ[𝓝 p]g) : positiveEuclideanLaplacian f p=positiveEuclideanLaplacian g p := by
  have hd (j : Fin 3) : (fun q => fderiv ℝ f q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ g q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  simp only [positiveEuclideanLaplacian,he.fderiv_eq,(hd _).fderiv_eq]

end CubicEisenstein

 
open scoped           LineDeriv Manifold

namespace CubicEisenstein

section
variable (χ : PositiveChartCutoff) (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ) (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel)) (heq : ∀p,0<p 2→kernelEuclideanProjection p∈tsupport g.1→
      kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))

lemma kernelTestPartitionTerm_tsupport_right {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
     f  (i : ι) :
    tsupport (kernelTestPartitionTerm ρ f i).1⊆tsupport f.1 :=
  tsupport_smul_subset_right _ _

lemma kernelSmoothTest_finite_chart_partition_subsupport   :
    ∃t : Finset KernelGoodCutoff,∃g : t→kernelSmoothTests,
      (∑i,g i)=f ∧ ∀i,tsupport (g i).1⊆kernelChartCoreImage i.1.1 ∧
        tsupport (g i).1⊆tsupport f.1 := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover (tsupport f.1) f.2.2
  have hc : tsupport f.1⊆⋃χ : t,kernelChartCoreImage χ.1.1 := by
    intro q hq
    obtain ⟨χ,hχ,hqχ⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact Set.mem_iUnion.mpr ⟨⟨χ,hχ⟩,hqχ⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,SpatialCoordinates)
    (isClosed_tsupport f.1) (fun χ : t => kernelChartCoreImage χ.1.1)
    (fun χ => kernelChartCoreImage_open χ.1.1) hc
  refine ⟨t,kernelTestPartitionTerm ρ f,kernelTestPartition_sum f ρ,fun i => ?_⟩
  exact ⟨(kernelTestPartitionTerm_tsupport ρ f i).trans (hρ i),
    kernelTestPartitionTerm_tsupport_right ρ f i⟩

include hinj hg hA heq in
lemma kernelDirichletForm_supported_equation_chart  
     
       
       
      :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have hi : Integrable (fun q => star (A q)*g.1 q) (integralQuotientVolume globalKubotaKernel) :=
    hA.star.integrable_mul (kernelSmoothTests_memLp g)
  have himg : kernelChartCoreImage χ⊆kernelEuclideanProjection '' S :=
    Set.image_mono (kernelChartCore_subset χ)
  rw [kernelDirichletForm_eq_chart_laplacian χ hinj f g hg]
  calc
    _ = ∫p in S,star (upperPositiveLaplacian (kernelCoreLift χ f) p)*kernelCoreLift χ g p/(p 2:ℂ)^3 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (kernelCoreLift_tsupport_outer χ g h))
      rw [hz,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)/(p 2:ℂ)^3 := by
      apply setIntegral_congr_fun hS
      intro p hp
      dsimp only
      rw [kernelCoreLift_eq_on_outer χ hinj g hg hp]
      by_cases hc : p∈kernelChartCore χ
      · by_cases hgp : kernelEuclideanProjection p∈tsupport g.1
        · rw [kernelCoreLift_laplacian χ f p hc,heq p (χ.positive hp) hgp]
          rfl
        · have hz : g.1 (kernelEuclideanProjection p)=0 := image_eq_zero_of_notMem_tsupport hgp
          change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
          rw [hz,mul_zero,zero_div,mul_zero,zero_div]
      · have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
          (fun h => hc (kernelCoreLift_tsupport χ hinj g hg h))
        rw [kernelCoreLift_eq_on_outer χ hinj g hg hp] at hz
        change g.1 (kernelEuclideanProjection p)=0 at hz
        change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
        rw [hz,mul_zero,zero_div,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)
        ∂hyperbolicEuclideanVolume :=
      (hyperbolicEuclidean_setIntegral_complex S hS χ.positive _).symm
    _ = ∫q in kernelEuclideanProjection '' S,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_integral_complex S hS χ.positive hinj _ hi.aestronglyMeasurable
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      have hz : g.1 q=0 := image_eq_zero_of_notMem_tsupport (fun h => hq (himg (hg h)))
      rw [hz,mul_zero]

include hA heq in
theorem kernelDirichletForm_supported_equation  
       
     
    :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  obtain ⟨t,G,hG,hGsupp⟩ := kernelSmoothTest_finite_chart_partition_subsupport g
  calc
    _ = ∑i : t,kernelDirichletForm f (G i) := by
      rw [←hG,kernelDirichletForm_sum_right]
    _ = ∑i : t,∫q,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      apply Finset.sum_congr rfl
      intro i hi
      exact kernelDirichletForm_supported_equation_chart i.1.1 i.1.2 f (G i) (hGsupp i).1 A hA (fun p hp hgp => heq p hp ((hGsupp i).2 hgp))
    _ = ∫q,∑i : t,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      symm
      exact integral_finsetSum _ (fun i hi => hA.star.integrable_mul (kernelSmoothTests_memLp (G i)))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun q => by
        have hq := congrArg (fun k : kernelSmoothTests => k.1 q) hG
        simp only [Submodule.coe_sum,Finset.sum_apply] at hq
        dsimp only
        rw [←Finset.mul_sum,hq])

end

end CubicEisenstein

end

end OAI
