module

public import OAI.NumberTheory.DirichletL.Eisenstein.LocalCutoffs
public import OAI.NumberTheory.DirichletL.MeanSquare.HarmonicAggregation

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open Real
open scoped SchwartzMap
open Finset
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ShortDraftLatticeCount
open Filter
open scoped Topology
open ConcreteTraceCRT
open Filter Asymptotics
open scoped LSeries.notation
open Filter
open scoped LSeries.notation
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open scoped SchwartzMap
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open scoped Classical SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap
open scoped Classical SchwartzMap
open scoped Classical SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap

open scoped Classical SchwartzMap
namespace SecondPassArithmetic

section
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

end

open ConcreteTraceCRT (eisEmbedding)

def firstFrequencyDisk (R:ℝ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌈R⌉₊).filter (fun h=>‖eisEmbedding h‖^2≤R)

lemma mem_firstFrequencyDisk (R:ℝ) (h:O) :
    h∈firstFrequencyDisk R ↔ ‖eisEmbedding h‖^2≤R := by
  constructor
  · exact fun hh=>(Finset.mem_filter.mp hh).2
  · intro hh
    apply Finset.mem_filter.mpr
    refine ⟨?_,hh⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    rw [eisEmbedding_norm_sq_eq_absNorm_span] at hh
    exact_mod_cast hh.trans (Nat.le_ceil R)

lemma outside_firstFrequencyDisk (R:ℝ) (h:O) (hh:h∉firstFrequencyDisk R) :
    R<‖eisEmbedding h‖^2 := lt_of_not_ge (fun hb=>hh ((mem_firstFrequencyDisk R h).mpr hb))

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped Classical Topology SchwartzMap LineDeriv

lemma euclideanCoordinateVector_eq_basis (j : Fin 3) :
    euclideanCoordinateVector j=EuclideanSpace.basisFun (Fin 3) ℝ j := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

lemma schwartz_toL2_norm_sq (g : 𝓢(EuclideanSpatial,ℂ)) :
    ‖g.toLp 2 volume‖^2=∫p,‖g p‖^2 := by
  calc
    ‖g.toLp 2 volume‖^2=inner ℝ (g.toLp 2 volume) (g.toLp 2 volume) :=
      by simp
    _ = ∫p,inner ℝ (g.toLp 2 volume p) (g.toLp 2 volume p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [g.coeFn_toLp 2 volume] with p hp
      simp_all

def kernelLocalizedDensity (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : ℝ :=
  ‖kernelLocalizedField χ f p‖^2+∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
    (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2

lemma kernelLocalizedDensity_eq_schwartz (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) :
    kernelLocalizedDensity χ f p=‖kernelLocalizedSchwartz χ f p‖^2+
      ∑j : Fin 3,‖(∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)) p‖^2 := by
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,euclideanCoordinateVector_eq_basis,
    kernelLocalizedSchwartz_coe]
  rfl

lemma kernelLocalizedDensity_integrable (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    Integrable (kernelLocalizedDensity χ f) volume := by
  change Integrable (fun p => kernelLocalizedDensity χ f p) volume
  simp_rw [kernelLocalizedDensity_eq_schwartz]
  exact ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq.add
    (integrable_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq))

lemma kernelLocalizedH1_norm_sq (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ‖kernelLocalizedH1 χ f‖^2=∫p,kernelLocalizedDensity χ f p := by
  rw [euclideanH1_norm_sq,kernelLocalizedH1_embedding,PiLp.norm_sq_eq_of_L2]
  simp_rw [kernelLocalizedH1_gradient,schwartz_toL2_norm_sq,kernelLocalizedDensity_eq_schwartz]
  rw [integral_add (((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq)
    (integrable_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq)),
    integral_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq)]

lemma kernelLocalizedDensity_zero (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∉tsupport χ.func) : kernelLocalizedDensity χ f p=0 := by
  have hz : kernelLocalizedField χ f=ᶠ[𝓝 p]0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
    simp only [kernelLocalizedField,hq,Pi.zero_apply,zero_smul]
  simp only [kernelLocalizedDensity,hz.self_of_nhds,hz.fderiv_eq,fderiv_zero,
    Pi.zero_apply,_root_.zero_apply,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero]

lemma kernelLocalizedDensity_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) (M D A : ℝ)
    (hM : (χ.func p)^2≤M)
    (hD : (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hA : (χ.func p)^2≤A*(p 2)^2) :
    kernelLocalizedDensity χ f p≤
      (M+2*D)*‖kernelTestField f p‖^2+
        2*A*kernelTestEnergyDensity f (euclideanToHyperbolic p) := by
  have he := kernelLocalizedField_energy_bound χ f p hp
  have he' : (p 2)^2*(∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤
      (p 2)^2*(2*A*kernelTestEnergyDensity f (euclideanToHyperbolic p)+
        2*D*‖kernelTestField f p‖^2) := by
    refine he.trans ?_
    calc
      _ ≤ 2*(A*(p 2)^2)*kernelTestEnergyDensity f (euclideanToHyperbolic p)+
          2*(p 2)^2*D*‖kernelTestField f p‖^2 := by
        gcongr
        · exact kernelTestEnergyDensity_nonneg _ _
      _ = _ := by ring
  have hs := le_of_mul_le_mul_left he' (sq_pos_of_pos hp)
  have hm : ‖kernelLocalizedField χ f p‖^2≤M*‖kernelTestField f p‖^2 := by
    simp only [kernelLocalizedField,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    exact mul_le_mul_of_nonneg_right hM (sq_nonneg _)
  unfold kernelLocalizedDensity
  nlinarith

lemma kernelEuclideanProjection_volume_integrable (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (b : ℝ) (hb : 0≤b)
    (hheight : ∀p∈S,p 2≤b) (g : KernelQuotient→ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) :
    IntegrableOn (fun p => g (kernelEuclideanProjection p)) S volume := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := (hm.integrable_comp_of_integrable hg.integrableOn).smul_measure
    (c := ENNReal.ofReal (b^3)) ENNReal.ofReal_ne_top
  exact hh.mono_measure (euclideanVolume_le_heightCube_hyperbolic S hS hpos b hb hheight)

theorem kernelLocalizedH1_norm_sq_le (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (M D A b : ℝ) (hM0 : 0≤M) (hD0 : 0≤D) (hA0 : 0≤A) (hb : 0≤b)
    (hheight : ∀p∈tsupport χ.func,p 2≤b)
    (hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M)
    (hD : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hA : ∀p∈tsupport χ.func,(χ.func p)^2≤A*(p 2)^2)
    (f : kernelSmoothTests) :
    ‖kernelLocalizedH1 χ f‖^2≤b^3*((M+2*D)*‖kernelSmoothTestsToL2 f‖^2+
      2*A*kernelDirichletEnergy f) := by
  let G : KernelQuotient→ℝ := fun q =>
    (M+2*D)*‖f.1 q‖^2+2*A*kernelQuotientEnergyDensity f q
  have hG : Integrable G (integralQuotientVolume globalKubotaKernel) :=
    (((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul _).add
      ((kernelQuotientEnergyDensity_integrable f).const_mul _)
  have hGn : ∀q,0≤G q := by
    intro q
    dsimp only [G]
    positivity [kernelQuotientEnergyDensity_nonneg f q]
  have hS := χ.compact.measurableSet
  have hGI := kernelEuclideanProjection_volume_integrable (tsupport χ.func) hS χ.positive
    hinj b hb hheight G hG
  rw [kernelLocalizedH1_norm_sq]
  calc
    (∫p,kernelLocalizedDensity χ f p) =
        ∫p in tsupport χ.func,kernelLocalizedDensity χ f p :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (kernelLocalizedDensity_zero χ f)).symm
    _ ≤ ∫p in tsupport χ.func,G (kernelEuclideanProjection p) := by
      apply setIntegral_mono_on (kernelLocalizedDensity_integrable χ f).integrableOn hGI hS
      intro p hp
      exact kernelLocalizedDensity_le χ f p (χ.positive hp) M D A (by grind) (by grind) (by grind)
    _ ≤ b^3*∫q,G q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_volume_integral_le (tsupport χ.func) hS χ.positive hinj
        b hb hheight G hG hGn
    _ = _ := by
      dsimp only [G]
      rw [integral_add (((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul _)
        ((kernelQuotientEnergyDensity_integrable f).const_mul _),integral_const_mul,integral_const_mul,
        ←kernelSmoothTestsToL2_norm_sq]
      rfl

theorem kernelLocalizedH1_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelLocalizedH1 χ f‖^2≤C*(‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f) := by
  have hgrad : Continuous (fun p : EuclideanSpatial =>
      ∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) := by
    apply continuous_finsetSum
    intro j hj
    exact (((χ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  have hratio : ContinuousOn (fun p : EuclideanSpatial => (χ.func p)^2/(p 2)^2) (tsupport χ.func) :=
    (χ.smooth.continuous.pow 2).continuousOn.div (by fun_prop)
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.positive hp)))
  obtain ⟨m,hm⟩ := χ.compact.bddAbove_image (χ.smooth.continuous.pow 2).continuousOn
  obtain ⟨d,hd⟩ := χ.compact.bddAbove_image hgrad.continuousOn
  obtain ⟨a,ha⟩ := χ.compact.bddAbove_image hratio
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let M := max 0 m
  let D := max 0 d
  let A := max 0 a
  let B := max 0 b
  have hM0 : 0≤M := le_max_left _ _
  have hD0 : 0≤D := le_max_left _ _
  have hA0 : 0≤A := le_max_left _ _
  have hB0 : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb (by grind)).trans (by grind)
  have hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M := fun p hp =>
    (hm ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hD : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D := fun p hp =>
    (hd ⟨p,hp,rfl⟩).trans (by grind)
  have hA : ∀p∈tsupport χ.func,(χ.func p)^2≤A*(p 2)^2 := fun p hp =>
    (div_le_iff₀ (sq_pos_of_pos (χ.positive hp))).mp
      ((ha ⟨p,hp,rfl⟩).trans (by grind))
  refine ⟨B^3*(M+2*D+2*A),by positivity,fun f => ?_⟩
  refine (kernelLocalizedH1_norm_sq_le χ hinj M D A B hM0 hD0 hA0 hB0 hheight hM hD hA f).trans ?_
  rw [mul_assoc (B^3) (M+2*D+2*A)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hm0 := sq_nonneg ‖kernelSmoothTestsToL2 f‖
  have he0 := kernelDirichletEnergy_nonneg f
  nlinarith

def kernelLocalizedSchwartzLinear (χ : PositiveChartCutoff) :
    kernelSmoothTests →ₗ[ℂ] 𝓢(EuclideanSpatial,ℂ) where
  toFun := kernelLocalizedSchwartz χ
  map_add' f g := by
    ext p
    change χ.func p • (kernelTestField f p+kernelTestField g p)=_
    exact smul_add _ _ _
  map_smul' c f := by
    ext p
    change χ.func p • (c • kernelTestField f p)=c • (χ.func p • kernelTestField f p)
    exact smul_comm _ _ _

def kernelLocalizedH1Linear (χ : PositiveChartCutoff) : kernelSmoothTests →ₗ[ℂ] EuclideanH1 where
  toFun := kernelLocalizedH1 χ
  map_add' f g := by
    apply euclideanH1Embedding_injective
    simp only [map_add,kernelLocalizedH1_embedding]
    rw [show kernelLocalizedSchwartz χ (f+g)=kernelLocalizedSchwartz χ f+kernelLocalizedSchwartz χ g
      from (kernelLocalizedSchwartzLinear χ).map_add f g]
    rfl
  map_smul' c f := by
    apply euclideanH1Embedding_injective
    simp only [map_smul,kernelLocalizedH1_embedding,RingHom.id_apply]
    rw [show kernelLocalizedSchwartz χ (c•f)=c•kernelLocalizedSchwartz χ f
      from (kernelLocalizedSchwartzLinear χ).map_smul c f]
    rfl

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical Topology

namespace CubicEisenstein

abbrev KernelEnergyAmbient := WithLp 2 (KernelQuotientL2 × KernelGradientL2)

def kernelEnergyCore : kernelSmoothTests →ₗ[ℂ] KernelEnergyAmbient :=
  (WithLp.linearEquiv 2 ℂ (KernelQuotientL2 × KernelGradientL2)).symm.toLinearMap.comp
    (kernelSmoothTestsToL2.prod kernelGradientLinear)

def kernelEnergyGraphSubmodule : Submodule ℂ KernelEnergyAmbient :=
  (LinearMap.range kernelEnergyCore).topologicalClosure

abbrev KernelEnergyGraph := kernelEnergyGraphSubmodule

instance kernelEnergyGraph_complete : CompleteSpace KernelEnergyGraph :=
  (LinearMap.range kernelEnergyCore).isClosed_topologicalClosure.completeSpace_coe

def kernelEnergyGraphCore : kernelSmoothTests →ₗ[ℂ] KernelEnergyGraph :=
  kernelEnergyCore.codRestrict kernelEnergyGraphSubmodule
    (fun f => (LinearMap.range kernelEnergyCore).le_topologicalClosure ⟨f,rfl⟩)

lemma kernelEnergyGraphCore_dense : DenseRange kernelEnergyGraphCore := by
  rw [DenseRange,Subtype.dense_iff,←Set.range_comp]
  change closure (Set.range kernelEnergyCore)⊆closure (Set.range kernelEnergyCore)
  rfl

def kernelEnergyMass : KernelEnergyGraph →L[ℂ] KernelQuotientL2 :=
  (ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).toContinuousLinearMap.comp
      kernelEnergyGraphSubmodule.subtypeL)

def kernelEnergyGradient : KernelEnergyGraph →L[ℂ] KernelGradientL2 :=
  (ContinuousLinearMap.snd ℂ KernelQuotientL2 KernelGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).toContinuousLinearMap.comp
      kernelEnergyGraphSubmodule.subtypeL)

lemma kernelEnergyMass_core (f : kernelSmoothTests) :
    kernelEnergyMass (kernelEnergyGraphCore f)=kernelSmoothTestsToL2 f := rfl

lemma kernelEnergyGradient_core (f : kernelSmoothTests) :
    kernelEnergyGradient (kernelEnergyGraphCore f)=kernelGradientToL2 f := rfl

lemma kernelEnergyGraph_norm_sq (u : KernelEnergyGraph) :
    ‖u‖^2=‖kernelEnergyMass u‖^2+‖kernelEnergyGradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

lemma kernelEnergyGraphCore_norm_sq (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore f‖^2=‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f := by
  rw [kernelEnergyGraph_norm_sq,kernelEnergyMass_core,kernelEnergyGradient_core,
    kernelGradientToL2_norm_sq]

lemma kernelEnergyMass_dense : DenseRange kernelEnergyMass := by
  apply kernelSmoothTestsToL2_dense.mono
  rintro _ ⟨f,rfl⟩
  exact ⟨kernelEnergyGraphCore f,rfl⟩

lemma kernelLocalizedH1_graph_bound (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,∀f : kernelSmoothTests,
      ‖kernelLocalizedH1Linear χ f‖≤C*‖kernelEnergyGraphCore f‖ := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedH1_bounded χ hinj
  refine ⟨Real.sqrt C,fun f => ?_⟩
  have hh := hbound f
  rw [←kernelEnergyGraphCore_norm_sq] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖kernelLocalizedH1 χ f‖^2≤(Real.sqrt C*‖kernelEnergyGraphCore f‖)^2
  rw [mul_pow,Real.sq_sqrt hC]
  omega

def kernelEnergyLocalize (χ : PositiveChartCutoff) : KernelEnergyGraph →L[ℂ] EuclideanH1 :=
  (kernelLocalizedH1Linear χ).extendOfNorm kernelEnergyGraphCore

lemma kernelEnergyLocalize_core (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (f : kernelSmoothTests) :
    kernelEnergyLocalize χ (kernelEnergyGraphCore f)=kernelLocalizedH1 χ f :=
  LinearMap.extendOfNorm_eq kernelEnergyGraphCore_dense (kernelLocalizedH1_graph_bound χ hinj) f

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical Topology SchwartzMap LineDeriv

namespace CubicEisenstein

def kernelLocalizedL2Linear (χ : PositiveChartCutoff) : kernelSmoothTests →ₗ[ℂ] EuclideanL2 :=
  euclideanH1Embedding.toLinearMap.comp (kernelLocalizedH1Linear χ)

lemma kernelLocalizedL2Linear_apply (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    kernelLocalizedL2Linear χ f=(kernelLocalizedSchwartz χ f).toLp 2 volume := rfl

lemma kernelLocalizedL2_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelLocalizedL2Linear χ f‖^2≤C*‖kernelSmoothTestsToL2 f‖^2 := by
  obtain ⟨m,hm⟩ := χ.compact.bddAbove_image (χ.smooth.continuous.pow 2).continuousOn
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let M := max 0 m
  let B := max 0 b
  have hM0 : 0≤M := le_max_left _ _
  have hB0 : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb (by grind)).trans (by grind)
  have hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M := fun p hp =>
    (hm ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  refine ⟨B^3*M,by positivity,fun f => ?_⟩
  let G : KernelQuotient→ℝ := fun q => M*‖f.1 q‖^2
  have hG : Integrable G (integralQuotientVolume globalKubotaKernel) :=
    ((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul M
  have hGn : ∀q,0≤G q := fun q => by positivity
  have hS := χ.compact.measurableSet
  have hGI := kernelEuclideanProjection_volume_integrable (tsupport χ.func) hS χ.positive
    hinj B hB0 hheight G hG
  have hfi := ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq
  rw [kernelLocalizedL2Linear_apply,schwartz_toL2_norm_sq]
  calc
    (∫p,‖kernelLocalizedSchwartz χ f p‖^2) =
        ∫p in tsupport χ.func,‖kernelLocalizedSchwartz χ f p‖^2 := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro p hp
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).self_of_nhds
      change ‖χ.func p • kernelTestField f p‖^2=0
      simp_all
    _ ≤ ∫p in tsupport χ.func,G (kernelEuclideanProjection p) := by
      apply setIntegral_mono_on hfi.integrableOn hGI hS
      intro p hp
      change ‖χ.func p • kernelTestField f p‖^2≤M*‖kernelTestField f p‖^2
      simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
      exact mul_le_mul_of_nonneg_right (by grind) (sq_nonneg _)
    _ ≤ B^3*∫q,G q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_volume_integral_le (tsupport χ.func) hS χ.positive hinj
        B hB0 hheight G hG hGn
    _ = _ := by
      dsimp only [G]
      rw [integral_const_mul,←kernelSmoothTestsToL2_norm_sq,mul_assoc]

lemma kernelLocalizedL2_bound (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,∀f : kernelSmoothTests,
      ‖kernelLocalizedL2Linear χ f‖≤C*‖kernelSmoothTestsToL2 f‖ := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedL2_bounded χ hinj
  refine ⟨Real.sqrt C,fun f => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt hC]
  grind

def kernelL2Localize (χ : PositiveChartCutoff) : KernelQuotientL2 →L[ℂ] EuclideanL2 :=
  (kernelLocalizedL2Linear χ).extendOfNorm kernelSmoothTestsToL2

lemma kernelL2Localize_core (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (f : kernelSmoothTests) :
    kernelL2Localize χ (kernelSmoothTestsToL2 f)=(kernelLocalizedSchwartz χ f).toLp 2 volume :=
  LinearMap.extendOfNorm_eq kernelSmoothTestsToL2_dense (kernelLocalizedL2_bound χ hinj) f

lemma kernelEnergyLocalize_mass (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph) :
    euclideanH1Embedding (kernelEnergyLocalize χ u)=kernelL2Localize χ (kernelEnergyMass u) := by
  have heq : (fun v => euclideanH1Embedding (kernelEnergyLocalize χ v))=
      fun v => kernelL2Localize χ (kernelEnergyMass v) :=
    kernelEnergyGraphCore_dense.equalizer (by fun_prop) (by fun_prop) (by
      funext f
      simp only [Function.comp_apply,kernelEnergyLocalize_core χ hinj,
        kernelLocalizedH1_embedding,kernelEnergyMass_core,kernelL2Localize_core χ hinj])
  exact congrFun heq u

lemma kernelEnergyLocalize_eq_zero_of_mass_zero (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph)
    (hu : kernelEnergyMass u=0) : kernelEnergyLocalize χ u=0 := by
  apply euclideanH1Embedding_eq_zero
  rw [kernelEnergyLocalize_mass χ hinj u,hu,map_zero]

end CubicEisenstein

end

end OAI
