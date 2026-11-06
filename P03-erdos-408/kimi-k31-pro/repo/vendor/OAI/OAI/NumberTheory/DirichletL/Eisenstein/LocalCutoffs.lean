module

public import OAI.NumberTheory.DirichletL.GaussSum.BranchScaling

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology SchwartzMap LineDeriv ContDiff

structure PositiveChartCutoff where
  func : EuclideanSpatial → ℝ
  smooth : ContDiff ℝ ∞ func
  compact : HasCompactSupport func
  positive : tsupport func ⊆ {p | 0 < p 2}

lemma kernelChartCutoff_exists (p : EuclideanSpatial) (hp : 0<p 2) :
    ∃χ : PositiveChartCutoff, χ.func p=1 ∧ Set.range χ.func ⊆ Set.Icc 0 1 ∧
      Set.InjOn (integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic)
        (tsupport χ.func) := by
  obtain ⟨U,hU,hw,hUinj⟩ :=
    kernelQuotient_localHomeomorph.isLocallyInjective (euclideanToHyperbolic p)
  have hn : {q : EuclideanSpatial | 0<q 2} ∩ euclideanToHyperbolic ⁻¹' U ∈ 𝓝 p :=
    inter_mem ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hp)
      ((euclideanToHyperbolic_contMDiffAt p hp).continuousAt (hU.mem_nhds hw))
  obtain ⟨χ,hχ,hcomp,hsmooth,hrange,hvalue⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hn
  refine ⟨⟨χ,hsmooth,hcomp,fun q hq => (hχ hq).1⟩,hvalue,hrange,?_⟩
  intro q hq r hr heq
  have hwEq := hUinj (hχ hq).2 (hχ hr).2 heq
  have hc := congrArg hyperbolicEuclideanCoordinates hwEq
  simpa only [hyperbolicEuclideanCoordinates_toHyperbolic _ (hχ hq).1,
    hyperbolicEuclideanCoordinates_toHyperbolic _ (hχ hr).1] using hc

def kernelLocalizedField (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : ℂ := χ.func p • kernelTestField f p

lemma kernelLocalizedField_compact (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    HasCompactSupport (kernelLocalizedField χ f) := χ.compact.smul_right

lemma kernelLocalizedField_tsupport (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    tsupport (kernelLocalizedField χ f) ⊆ tsupport χ.func := tsupport_smul_subset_left _ _

lemma kernelLocalizedField_smooth (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ContDiff ℝ ∞ (kernelLocalizedField χ f) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 0 < p 2
  · exact χ.smooth.contDiffAt.smul (kernelTestField_contDiffAt f p hp)
  · have hn : p ∉ tsupport χ.func := fun h => hp (χ.positive h)
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpatial => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    simp only [kernelLocalizedField,hq,Pi.zero_apply,zero_smul]

def kernelLocalizedSchwartz (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    𝓢(EuclideanSpatial,ℂ) :=
  (kernelLocalizedField_compact χ f).toSchwartzMap (kernelLocalizedField_smooth χ f)

lemma kernelLocalizedSchwartz_coe (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    (kernelLocalizedSchwartz χ f : EuclideanSpatial → ℂ)=kernelLocalizedField χ f := rfl

def kernelLocalizedH1 (χ : PositiveChartCutoff) (f : kernelSmoothTests) : EuclideanH1 := by
  let g := kernelLocalizedSchwartz χ f
  let v := WithLp.toLp 2 (fun j => (∂_{euclideanCoordinateVector j} g).toLp 2 volume)
  refine ⟨WithLp.toLp 2 (g.toLp 2 volume,v),?_⟩
  change (g.toLp 2 volume,v)∈euclideanWeakGradientGraph
  exact schwartz_mem_euclideanWeakGradientGraph g

lemma kernelLocalizedH1_embedding (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    euclideanH1Embedding (kernelLocalizedH1 χ f)=
      (kernelLocalizedSchwartz χ f).toLp 2 volume := rfl

lemma kernelLocalizedH1_gradient (χ : PositiveChartCutoff) (f : kernelSmoothTests) (j : Fin 3) :
    euclideanH1Gradient (kernelLocalizedH1 χ f) j=
      (∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).toLp 2 volume := rfl

lemma kernelLocalizedField_fderiv (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0 < p 2) (u : EuclideanSpatial) :
    fderiv ℝ (kernelLocalizedField χ f) p u=
      χ.func p • fderiv ℝ (kernelTestField f) p u+
        (fderiv ℝ χ.func p u) • kernelTestField f p := by
  change fderiv ℝ (χ.func • kernelTestField f) p u=_
  rw [fderiv_smul (χ.smooth.differentiable (by simp)).differentiableAt
    ((kernelTestField_contDiffAt f p hp).differentiableAt (by simp))]
  rfl

lemma complex_norm_add_sq_le (z w : ℂ) :
    ‖z+w‖^2 ≤ 2*‖z‖^2+2*‖w‖^2 := by
  have hh := norm_add_le z w
  have hn := norm_nonneg (z+w)
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

lemma kernelLocalizedField_energy_bound (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    (p 2)^2*(∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) ≤
    2*(χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)+
      2*(p 2)^2*(∑j : Fin 3,‖fderiv ℝ χ.func p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)*‖kernelTestField f p‖^2 := by
  have hsum : (∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) ≤
      ∑j : Fin 3,(2*(χ.func p)^2*‖fderiv ℝ (kernelTestField f) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2+
        2*‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2*
          ‖kernelTestField f p‖^2) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [kernelLocalizedField_fderiv χ f p hp]
    simpa only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,mul_assoc] using
      complex_norm_add_sq_le
        (χ.func p • fderiv ℝ (kernelTestField f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
        (fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j) • kernelTestField f p)
  have he : kernelTestEnergyDensity f (euclideanToHyperbolic p)=
      (p 2)^2*∑j : Fin 3,‖fderiv ℝ (kernelTestField f) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2 := by
    rw [kernelTestEnergyDensity_eq_partials]
    have hc := hyperbolicEuclideanCoordinates_toHyperbolic p hp
    have hv : hyperbolicHeight (euclideanToHyperbolic p)=p 2 := congrArg (fun q : EuclideanSpatial => q 2) hc
    simp only [hv,kernelTestPartial,hc]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (p 2))
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,
    mul_add,mul_assoc,mul_left_comm,mul_comm] using hh

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal

def kernelEuclideanProjection : EuclideanSpatial → KernelQuotient :=
  integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic

lemma euclideanToHyperbolic_measurePreserving_on (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (_hpos : S⊆euclideanUpperHalf) :
    MeasurePreserving euclideanToHyperbolic (hyperbolicEuclideanVolume.restrict S)
      (hyperbolicVolume.restrict (hyperbolicEuclideanCoordinates ⁻¹' S)) := by
  have hU : MeasurableSet (hyperbolicEuclideanCoordinates ⁻¹' S) :=
    hyperbolicEuclideanCoordinates_continuous.measurable hS
  have hset : euclideanToHyperbolic ⁻¹' (hyperbolicEuclideanCoordinates ⁻¹' S)=ᵐ[hyperbolicEuclideanVolume]S := by
    filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
    simp only [Set.mem_preimage,hyperbolicEuclideanCoordinates_toHyperbolic p hp]
  refine ⟨euclideanToHyperbolic_measurable,?_⟩
  rw [hyperbolicVolume,Measure.restrict_map euclideanToHyperbolic_measurable hU,
    Measure.restrict_congr_set hset]

lemma euclideanToHyperbolic_image_positive (S : Set EuclideanSpatial)
    (hpos : S⊆euclideanUpperHalf) :
    euclideanToHyperbolic '' S=hyperbolicEuclideanCoordinates ⁻¹' S := by
  ext w
  constructor
  · rintro ⟨p,hp,rfl⟩
    simpa only [Set.mem_preimage,hyperbolicEuclideanCoordinates_toHyperbolic p (hpos hp)] using hp
  · intro hw
    exact ⟨hyperbolicEuclideanCoordinates w,hw,euclideanToHyperbolic_coordinates w⟩

lemma kernelEuclideanProjection_measurePreserving_on (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) :
    MeasurePreserving kernelEuclideanProjection (hyperbolicEuclideanVolume.restrict S)
      ((integralQuotientVolume globalKubotaKernel).restrict (kernelEuclideanProjection '' S)) := by
  have hU : MeasurableSet (hyperbolicEuclideanCoordinates ⁻¹' S) :=
    hyperbolicEuclideanCoordinates_continuous.measurable hS
  have hi : Set.InjOn (integralOrbitProjection globalKubotaKernel)
      (hyperbolicEuclideanCoordinates ⁻¹' S) := by
    intro u hu v hv heq
    have hh := hinj hu hv (by simpa only [kernelEuclideanProjection,Function.comp_apply,
      euclideanToHyperbolic_coordinates] using heq)
    have hh' := congrArg euclideanToHyperbolic hh
    simpa only [euclideanToHyperbolic_coordinates] using hh'
  have hcomp := (kernelProjection_measurePreserving_on _ hU hi).comp
    (euclideanToHyperbolic_measurePreserving_on S hS hpos)
  have himage : integralOrbitProjection globalKubotaKernel ''
      (hyperbolicEuclideanCoordinates ⁻¹' S)=kernelEuclideanProjection '' S := by
    rw [←euclideanToHyperbolic_image_positive S hpos,Set.image_image]
    rfl
  rwa [himage] at hcomp

lemma kernelEuclideanProjection_integral (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient → ℝ)
    (hg : AEStronglyMeasurable g (integralQuotientVolume globalKubotaKernel)) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)=
      ∫q in kernelEuclideanProjection '' S,g q∂integralQuotientVolume globalKubotaKernel := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := hg.mono_measure (Measure.restrict_le_self (s := kernelEuclideanProjection '' S))
  rw [←hm.map_eq] at hh ⊢
  exact (integral_map hm.measurable.aemeasurable hh).symm

lemma kernelEuclideanProjection_integral_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient → ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) (hgn : ∀q,0≤g q) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)≤
      ∫q,g q∂integralQuotientVolume globalKubotaKernel := by
  rw [kernelEuclideanProjection_integral S hS hpos hinj g hg.aestronglyMeasurable]
  exact setIntegral_le_integral hg (Eventually.of_forall hgn)

lemma kernelSmoothTestsToL2_norm_sq (f : kernelSmoothTests) :
    ‖kernelSmoothTestsToL2 f‖^2=
      ∫q,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel := by
  calc
    ‖kernelSmoothTestsToL2 f‖^2=inner ℝ (kernelSmoothTestsToL2 f) (kernelSmoothTestsToL2 f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫q,inner ℝ (kernelSmoothTestsToL2 f q) (kernelSmoothTestsToL2 f q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(kernelSmoothTests_memLp f).coeFn_toLp] with q hq
      change inner ℝ (((kernelSmoothTests_memLp f).toLp f.1) q)
        (((kernelSmoothTests_memLp f).toLp f.1) q)=_
      rw [hq,real_inner_self_eq_norm_sq]

lemma kernelLocalMass_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (f : kernelSmoothTests) :
    (∫p in S,‖kernelTestField f p‖^2∂hyperbolicEuclideanVolume)≤‖kernelSmoothTestsToL2 f‖^2 := by
  rw [kernelSmoothTestsToL2_norm_sq]
  exact kernelEuclideanProjection_integral_le S hS hpos hinj _
    (kernelSmoothTests_memLp f).norm.integrable_sq (fun _ => sq_nonneg _)

lemma euclideanVolume_le_heightCube_hyperbolic (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf) (b : ℝ) (hb : 0≤b)
    (hheight : ∀p∈S,p 2≤b) :
    volume.restrict S≤ENNReal.ofReal (b^3) • hyperbolicEuclideanVolume.restrict S := by
  have hw : hyperbolicEuclideanVolume.restrict S=(volume.restrict S).withDensity hyperbolicDensity := by
    rw [hyperbolicEuclideanVolume,MeasureTheory.restrict_withDensity hS,
      Measure.restrict_restrict hS,Set.inter_eq_left.mpr hpos]
  rw [hw]
  have hbd : (1 : EuclideanSpatial→ℝ≥0∞)≤ᵐ[volume.restrict S]
      ENNReal.ofReal (b^3) • hyperbolicDensity := by
    filter_upwards [ae_restrict_mem hS] with p hp
    have ht : 0<p 2 := hpos hp
    have hpow : (p 2)^3≤b^3 := pow_le_pow_left₀ ht.le (hheight p hp) 3
    have hreal : 1≤b^3*((p 2)^3)⁻¹ := by
      calc
        1=(p 2)^3*((p 2)^3)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ ht.ne')).symm
        _ ≤b^3*((p 2)^3)⁻¹ := mul_le_mul_of_nonneg_right hpow (by positivity)
    change (1 : ℝ≥0∞)≤ENNReal.ofReal (b^3)*ENNReal.ofReal (((p 2)^3)⁻¹)
    rw [←ENNReal.ofReal_mul (pow_nonneg hb 3)]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hreal
  simpa only [MeasureTheory.withDensity_one,MeasureTheory.withDensity_smul _ hyperbolicDensity_measurable] using
    (MeasureTheory.withDensity_mono hbd)

lemma kernelEuclideanProjection_volume_integral_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (b : ℝ) (hb : 0≤b)
    (hheight : ∀p∈S,p 2≤b) (g : KernelQuotient→ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) (hgn : ∀q,0≤g q) :
    (∫p in S,g (kernelEuclideanProjection p))≤
      b^3*∫q,g q∂integralQuotientVolume globalKubotaKernel := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hgi := hm.integrable_comp_of_integrable hg.integrableOn
  have hh := integral_mono_measure
    (euclideanVolume_le_heightCube_hyperbolic S hS hpos b hb hheight)
    (Eventually.of_forall (fun p => hgn (kernelEuclideanProjection p)))
    (hgi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal (pow_nonneg hb 3)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (kernelEuclideanProjection_integral_le S hS hpos hinj g hg hgn) (pow_nonneg hb 3))

end CubicEisenstein

namespace CompletedGauss


open ActualEisensteinCubic CanonicalQuadraticSieve

structure ReflectedBranchData (levelBound K : ℝ) (I F Q : Ideal O) where
  levelScale : ℝ
  levelScale_pos : 0<levelScale
  levelScale_le : levelScale≤levelBound
  primes : Finset (Ideal O)
  maximal : ∀p : primes,p.val.IsMaximal
  good : ∀p : primes,lambda∉p.val
  coprime : Pairwise (fun p r : primes => IsCoprime p.val r.val)
  divides : ∀p : primes,p.val∣I*Q
  nonresidual : ∀p : primes,¬p.val∣rowResidualPart I Q
  label : primes→Fin 3
  nColumns : (ℕ×ℕ×ℕ)→Finset (Ideal O)
  bColumns : (ℕ×ℕ×ℕ)→Finset (Ideal O)
  nBounds : ∀i,∀J∈nColumns i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2
  bBounds : ∀i,∀J∈bColumns i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1
  amplitude : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ
  amplitude_bound : ∀i,∀n∈nColumns i,∀b∈bColumns i,‖amplitude i n b‖≤1
  rowPhase : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ
  rowPhase_bound : ∀i k,‖rowPhase i k‖≤1

namespace ReflectedBranchData

def value {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedBranchData levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ := by
  letI : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact ∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock (fun p : d.primes => p.val) d.good
    (fun p => completedLocalExponent I F p.val) d.label W
    (completedResidualScale K I Q) (completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes => p.val) d.label)
    ρ q d.nColumns d.bColumns d.amplitude d.rowPhase i k

end ReflectedBranchData

structure ReflectedFiberData (rays : ℕ) (levelBound K : ℝ) (I F Q : Ideal O) where
  pool : Finset (Ideal O)
  maximal : ∀p : pool,p.val.IsMaximal
  divides : ∀p : pool,p.val∣I*Q
  branch : (Fin rays×(pool→Fin 6))→ReflectedBranchData levelBound K I F Q
  weight : (Fin rays×(pool→Fin 6))→ℂ
  weight_bound : ∀b,‖weight b‖≤1

namespace ReflectedFiberData

def value {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ :=
  ∑b,d.weight b*(d.branch b).value W X ρ q k

end ReflectedFiberData


namespace ReflectedFiberData

def idealValue {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (J : Ideal O) : ℂ :=
  if h : J∈idealRange (completedResidualScale K I Q) then d.value W X ρ q ⟨J,h⟩ else 0

end ReflectedFiberData

def HasExactCompletedModels (rays : ℕ) (rows : Finset (Ideal O))
    (K X ρ q levelBound : ℝ) (F Q : Ideal O) (W : ℝ→ℂ) (Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ) : Prop :=
  ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
    (completedRowFiber rows Q A T).Nonempty →
    ∃I∈completedRowFiber rows Q A T,∃d : ReflectedFiberData rays levelBound K I F Q,
      ∀J∈completedRowFiber rows Q A T,
        completedT (Ψ J) W X=lengthScale*d.idealValue W X ρ q (rowResidualPart J Q)

end CompletedGauss

end

end OAI
