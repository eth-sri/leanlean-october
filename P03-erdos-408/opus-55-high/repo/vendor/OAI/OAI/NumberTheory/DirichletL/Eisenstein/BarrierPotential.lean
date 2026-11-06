module

public import OAI.NumberTheory.DirichletL.MeanSquare.UnitRows
public import OAI.NumberTheory.DirichletL.Eisenstein.CuspHeight

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
open ShortDraftLatticeCount
open Filter
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open Filter
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
open scoped Classical

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped Classical ContDiff

lemma axisLaplacian_const_add (c : ℂ) (f : SpatialCoordinates→ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => c+f q) p=axisLaplacian f p := by
  unfold axisLaplacian axisSlice
  simp

lemma fullCuspProfileField_summable (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    Summable (fun x => F (rowHeight (fullCuspRow x) p)) := by
  simpa only [fullCuspRow_height _ p hp] using
    fullCuspProfileSum_summable F hF (upperPoint (spatialHorizontal p) (p 2) hp)

lemma fullCuspProfileField_add (F G : ℝ→ℝ) (hF : ∀v≤1,F v=0) (hG : ∀v≤1,G v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    fullCuspProfileField (fun v => F v+G v) p=fullCuspProfileField F p+fullCuspProfileField G p :=
  (fullCuspProfileField_summable F hF p hp).tsum_add
    (fullCuspProfileField_summable G hG p hp)

lemma cuspBarrierProfile_laplacian_zero (a b v : ℝ) (ha : 1<a) (hab : a<b) (hv : v≤1) :
    positiveHeightLaplacian (cuspBarrierProfile a b) v=0 := by
  have hh := cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha)
  rw [cuspBarrierDefectProfile,cuspBarrierProfile_zero a b hab v (hv.trans ha.le),sub_zero] at hh
  omega

def cuspBarrierField (a b : ℝ) (p : SpatialCoordinates) : ℝ :=
  1+fullCuspProfileField (cuspBarrierProfile a b) p

def cuspBarrierDefectField (a b : ℝ) (p : SpatialCoordinates) : ℝ :=
  -1+fullCuspProfileField (cuspBarrierDefectProfile a b) p

lemma cuspBarrierField_eq (a b : ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    cuspBarrierField a b p=cuspBarrier a b (upperPoint (spatialHorizontal p) (p 2) hp) := by
  rw [cuspBarrierField,cuspBarrier,fullCuspProfileField_eq _ p hp]

lemma cuspBarrierDefectField_eq (a b : ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    cuspBarrierDefectField a b p=cuspBarrierDefect a b (upperPoint (spatialHorizontal p) (p 2) hp) := by
  rw [cuspBarrierDefectField,cuspBarrierDefect,fullCuspProfileField_eq _ p hp]

lemma cuspBarrierField_laplace_defect (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (fun q => (cuspBarrierField a b q:ℂ)) p-(cuspBarrierField a b p:ℂ)=
      (cuspBarrierDefectField a b p:ℂ) := by
  have hF : ∀v≤1,cuspBarrierProfile a b v=0 :=
    fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha.le)
  have hD : ∀v≤1,cuspBarrierDefectProfile a b v=0 :=
    fun v hv => cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha)
  have hid : positiveHeightLaplacian (cuspBarrierProfile a b)=
      fun v => cuspBarrierDefectProfile a b v+cuspBarrierProfile a b v := by
    funext v
    rw [cuspBarrierDefectProfile,sub_add_cancel]
  have hh := fullCuspProfileField_laplacian _ (cuspBarrierProfile_smooth a b) hF
    (by grind) p hp
  simp only [cuspBarrierField,Complex.ofReal_add,Complex.ofReal_one,axisLaplacian_const_add]
  rw [hh,hid,fullCuspProfileField_add _ _ hD hF p hp]
  simp only [cuspBarrierDefectField,Complex.ofReal_add,Complex.ofReal_neg,Complex.ofReal_one]
  ring

def kernelBarrierPotential (a b : ℝ) (q : KernelQuotient) : ℝ :=
  1+kernelQuotientBarrierDefect a b q/kernelQuotientBarrier a b q

lemma kernelBarrierPotential_lower (a b : ℝ) (ha : 1<a) (hab : a<b) :
    ∃K : Set KernelQuotient,IsCompact K ∧ ∃C : ℝ,0≤C ∧
      ∀q,1-C*(K.indicator (fun _ => (1:ℝ))) q≤kernelBarrierPotential a b q := by
  let D := kernelQuotientBarrierDefect a b
  let K := tsupport D
  have hK : IsCompact K := kernelQuotientBarrierDefect_hasCompactSupport a b ha hab
  obtain ⟨C,hC⟩ := (kernelQuotientBarrierDefect_hasCompactSupport a b ha hab).exists_bound_of_continuous
    (kernelQuotientBarrierDefect_continuous a b ha hab)
  refine ⟨K,hK,max C 0,le_max_right _ _,fun q => ?_⟩
  have hphi := kernelQuotientBarrier_one_le a b ha.le hab q
  have hpos : 0<kernelQuotientBarrier a b q := by linarith
  by_cases hq : q∈K
  · rw [Set.indicator_of_mem hq,mul_one,kernelBarrierPotential]
    have hD : -max C 0≤D q := by
      have hn : -‖D q‖≤D q := neg_abs_le (D q)
      exact by grind
    have hdiv : -max C 0≤D q/kernelQuotientBarrier a b q := by
      apply (le_div_iff₀ hpos).mpr
      have hm : -max C 0*kernelQuotientBarrier a b q≤-max C 0 := by
        nlinarith [mul_nonneg (le_max_right C 0) (sub_nonneg.mpr hphi)]
      exact hm.trans hD
    linarith
  · rw [Set.indicator_of_notMem hq,mul_zero,sub_zero,kernelBarrierPotential]
    have hz := image_eq_zero_of_notMem_tsupport hq
    change 1≤1+D q/kernelQuotientBarrier a b q
    simp_all

lemma cuspBarrier_euclidean_eq (a b : ℝ) (p : EuclideanSpatial) (hp : 0<p 2) :
    cuspBarrier a b (euclideanToHyperbolic p)=cuspBarrierField a b p.ofLp := by
  rw [cuspBarrierField_eq a b p.ofLp hp,euclideanToHyperbolic_positive p hp]
  congr 1
  simp only [spatialHorizontal,mul_comm]

lemma cuspBarrierDefect_euclidean_eq (a b : ℝ) (p : EuclideanSpatial) (hp : 0<p 2) :
    cuspBarrierDefect a b (euclideanToHyperbolic p)=cuspBarrierDefectField a b p.ofLp := by
  rw [cuspBarrierDefectField_eq a b p.ofLp hp,euclideanToHyperbolic_positive p hp]
  congr 1
  simp only [spatialHorizontal,mul_comm]

lemma kernelQuotientBarrier_laplace_defect (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) p=
        ((kernelQuotientBarrier a b (kernelEuclideanProjection p)+
          kernelQuotientBarrierDefect a b (kernelEuclideanProjection p):ℝ):ℂ) := by
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) q :=
    fun q hq => Complex.ofRealCLM.contDiff.contDiffAt.comp q
      (cuspBarrier_euclidean_contDiffAt a b ha.le hab q hq)
  rw [positiveEuclideanLaplacian_eq_axis _ hf p hp]
  have he : ∀q : SpatialCoordinates,0<q 2→
      (kernelQuotientBarrier a b (kernelEuclideanProjection (WithLp.toLp 2 q)):ℂ)=
        (cuspBarrierField a b q:ℂ) := by
    intro q hq
    exact congrArg Complex.ofReal (cuspBarrier_euclidean_eq a b (WithLp.toLp 2 q) hq)
  rw [axisLaplacian_congr_positive _ _ he p.ofLp hp]
  have hh := cuspBarrierField_laplace_defect a b ha hab p.ofLp hp
  change -axisLaplacian _ p.ofLp=((cuspBarrier a b (euclideanToHyperbolic p)+
    cuspBarrierDefect a b (euclideanToHyperbolic p):ℝ):ℂ)
  rw [cuspBarrier_euclidean_eq a b p hp,cuspBarrierDefect_euclidean_eq a b p hp,Complex.ofReal_add]
  grind

end

section
open Filter MeasureTheory
open scoped Classical ContDiff Manifold

lemma kernelBarrierPotential_continuous (a b : ℝ) (ha : 1<a) (hab : a<b) :
    Continuous (kernelBarrierPotential a b) := by
  apply continuous_const.add
  exact (kernelQuotientBarrierDefect_continuous a b ha hab).div
    (kernelQuotientBarrier_continuous a b ha.le hab) (fun q => by
      have hq := kernelQuotientBarrier_one_le a b ha.le hab q
      linarith)

lemma kernelBarrierPotential_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) p=
        ((kernelBarrierPotential a b (kernelEuclideanProjection p)*
          kernelQuotientBarrier a b (kernelEuclideanProjection p):ℝ):ℂ) := by
  rw [kernelQuotientBarrier_laplace_defect a b ha hab p hp]
  apply congrArg Complex.ofReal
  have hn : kernelQuotientBarrier a b (kernelEuclideanProjection p)≠0 := by
    have hq := kernelQuotientBarrier_one_le a b ha.le hab (kernelEuclideanProjection p)
    linarith
  rw [kernelBarrierPotential,add_mul,one_mul,div_mul_cancel₀ _ hn]

lemma kernelSmoothTest_weighted_mass_integrable (V : KernelQuotient→ℝ) (hV : Continuous V)
    (f : kernelSmoothTests) :
    Integrable (fun q => V q*‖f.1 q‖^2) (integralQuotientVolume globalKubotaKernel) := by
  apply (hV.mul (f.2.1.continuous.norm.pow 2)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact f.2.2
  intro q hq
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  simp_all

end

open scoped ComplexConjugate

theorem ground_state_square_completion (a b : ℝ) (ha : a ≠ 0) (z d : ℂ) :
    ‖d‖^2 - b*((2*(conj z*d).re*a - ‖z‖^2*b)/a^2) =
      ‖d - (b/a : ℝ)*z‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  grind

theorem ground_state_directional_inequality (a b : ℝ) (ha : a ≠ 0) (z d : ℂ) :
    b*((2*(conj z*d).re*a - ‖z‖^2*b)/a^2) ≤ ‖d‖^2 := by
  have hh := ground_state_square_completion a b ha z d
  nlinarith

end CubicEisenstein

namespace SecondPassArithmetic

section

open scoped Classical
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

end

section
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

end
section

open FirstPassCubeLabels (columnLog)
open JointLogSeparation (frequencyTwist)

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

end

section
open ConcreteTraceCRT (eisEmbedding)

end


variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
