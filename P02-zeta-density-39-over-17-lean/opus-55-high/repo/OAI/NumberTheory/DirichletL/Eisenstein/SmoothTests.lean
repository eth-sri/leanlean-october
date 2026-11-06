module
public import OAI.NumberTheory.DirichletL.CubicSieve.RowCaps
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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped Classical Topology MatrixGroups Matrix ContDiff Manifold

instance hyperbolicSpatialChartedSpace : ChartedSpace SpatialCoordinates HyperbolicSpace :=
  hyperbolicSpatialChart.singletonChartedSpace hyperbolicSpatialChart_source

instance hyperbolicSpatialIsManifold : IsManifold 𝓘(ℝ,SpatialCoordinates) ∞ HyperbolicSpace :=
  hyperbolicSpatialChart.isManifold_singleton hyperbolicSpatialChart_source

lemma kernelLocalLift_source_out (q : KernelQuotient) : q∈(kernelLocalLift q.out).source := by
  have h := kernelQuotient_localHomeomorph.apply_self_mem_localInverseAt_source (x := q.out)
  change integralOrbitProjection globalKubotaKernel q.out∈(kernelLocalLift q.out).source at h
  rwa [show integralOrbitProjection globalKubotaKernel q.out=q from Quotient.out_eq q] at h

instance kernelSpatialChartedSpace : ChartedSpace SpatialCoordinates KernelQuotient where
  atlas := Set.range kernelQuotientChart
  chartAt := kernelQuotientChart
  mem_chart_source q := ⟨kernelLocalLift_source_out q,Set.mem_univ _⟩
  chart_mem_atlas q := ⟨q,rfl⟩

instance kernelSpatialIsManifold : IsManifold 𝓘(ℝ,SpatialCoordinates) ∞ KernelQuotient := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨q,rfl⟩ ⟨r,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
    Function.comp_id,Set.preimage_id_eq,Set.range_id,Set.inter_univ,id_eq] using
    kernelQuotientChart_contDiffOn q r

@[simp] lemma hyperbolicSpatial_chartAt (w : HyperbolicSpace) :
    chartAt SpatialCoordinates w=hyperbolicSpatialChart := rfl

@[simp] lemma kernelSpatial_chartAt (q : KernelQuotient) :
    chartAt SpatialCoordinates q=kernelQuotientChart q := rfl

lemma kernelProjection_contMDiff : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
    (integralOrbitProjection globalKubotaKernel) := by
  intro w
  rw [contMDiffAt_iff]
  refine ⟨(continuous_integralOrbitProjection globalKubotaKernel).continuousAt,?_⟩
  pm_7525
  have hq : integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm (hyperbolicSpatialCoordinates w))∈
      (kernelLocalLift (integralOrbitProjection globalKubotaKernel w).out).source := by
    have hleft := hyperbolicSpatialChart.left_inv (Set.mem_univ w)
    change hyperbolicSpatialChart.symm (hyperbolicSpatialCoordinates w)=w at hleft
    rw [hleft]
    exact kernelLocalLift_source_out _
  have h : ContDiffWithinAt ℝ ∞
      (kernelCoordinateTransition (integralOrbitProjection globalKubotaKernel w).out) Set.univ
      (hyperbolicSpatialCoordinates w) :=
    (kernelCoordinateTransition_contDiffAt _ _ hp hq).contDiffWithinAt
  unfold kernelCoordinateTransition at h
  aesop

end

section
open Filter MeasureTheory
open scoped Classical Topology ContDiff Manifold ENNReal NNReal

def kernelSmoothTests : Submodule ℂ (KernelQuotient→ℂ) where
  carrier f := ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f ∧ HasCompactSupport f
  zero_mem' := ⟨contMDiff_const,HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  smul_mem' c f hf := by
    have hc : ContDiff ℝ ∞ (fun z : ℂ => c*z) := contDiff_const.mul contDiff_id
    exact ⟨hc.contMDiff.comp hf.1,hf.2.smul_left⟩

lemma kernelSmoothTests_memLp (f : kernelSmoothTests) :
    MemLp f.1 2 (integralQuotientVolume globalKubotaKernel) :=
  f.2.1.continuous.memLp_of_hasCompactSupport f.2.2

def kernelSmoothTestsToL2 : kernelSmoothTests→ₗ[ℂ]KernelQuotientL2 where
  toFun f := (kernelSmoothTests_memLp f).toLp f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma kernelL2_smooth_compact_approx (f : KernelQuotientL2) (ε : ℝ) (hε : 0<ε) :
    ∃g : kernelSmoothTests,
      eLpNorm ((f : KernelQuotient→ℂ)-g.1) 2 (integralQuotientVolume globalKubotaKernel)≤
        ENNReal.ofReal ε := by
  obtain ⟨g,hgK,hfg,hgc,hgLp⟩ := kernelL2_continuous_compact_approx f
    (ENNReal.ofReal (ε/2)) (by positivity)
  let mass : ℝ≥0∞ := (integralQuotientVolume globalKubotaKernel Set.univ)^((2:ℝ≥0∞).toReal⁻¹)
  have hm : mass≠(∞:ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  let deltaLoss : ℝ := ε/(2*(mass.toReal+1))
  pm_3587 hδ deltaLoss hε
  obtain ⟨k,hkg,hksupp⟩ := hgc.exists_contMDiff_approx 𝓘(ℝ,SpatialCoordinates) ⊤
    (ε := fun _ => deltaLoss) continuous_const (fun _ => hδ)
  have hkK : HasCompactSupport (k : KernelQuotient→ℂ) :=
    HasCompactSupport.of_support_subset_isCompact hgK (hksupp.trans (subset_tsupport g))
  let kt : kernelSmoothTests := ⟨k,k.contMDiff,hkK⟩
  have hkgLp : eLpNorm (g-(k : KernelQuotient→ℂ)) 2 (integralQuotientVolume globalKubotaKernel)≤
      ENNReal.ofReal (ε/2) := by
    have hb : ∀ᵐ q ∂integralQuotientVolume globalKubotaKernel,‖g q-k q‖≤deltaLoss :=
      Filter.Eventually.of_forall fun q => by
        simpa only [dist_eq_norm,norm_sub_rev] using (hkg q).le
    have hmul : mass.toReal*deltaLoss≤ε/2 := by
      have he : deltaLoss*(2*(mass.toReal+1))=ε := div_mul_cancel₀ _ (by positivity)
      have hp := ENNReal.toReal_nonneg (a := mass)
      nlinarith [mul_nonneg hp hδ.le]
    calc
      _ ≤ mass*ENNReal.ofReal deltaLoss := eLpNorm_le_of_ae_bound (hgc.sub k.contMDiff.continuous).aestronglyMeasurable hb
      _ = ENNReal.ofReal (mass.toReal*deltaLoss) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hm]
      _ ≤ ENNReal.ofReal (ε/2) := ENNReal.ofReal_le_ofReal hmul
  refine ⟨kt,?_⟩
  have he : (f : KernelQuotient→ℂ)-kt.1=((f : KernelQuotient→ℂ)-g)+(g-(k : KernelQuotient→ℂ)) := by
    funext q
    change f q-k q=(f q-g q)+(g q-k q)
    ring
  rw [he]
  calc
    _ ≤ eLpNorm ((f : KernelQuotient→ℂ)-g) 2 (integralQuotientVolume globalKubotaKernel)+
        eLpNorm (g-(k : KernelQuotient→ℂ)) 2 (integralQuotientVolume globalKubotaKernel) :=
      eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add hfg hkgLp
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

lemma kernelSmoothTestsToL2_dense : DenseRange kernelSmoothTestsToL2 := by
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  obtain ⟨g,hg⟩ := kernelL2_smooth_compact_approx f (ε/2) (by positivity)
  refine ⟨g,?_⟩
  have he : ‖f-kernelSmoothTestsToL2 g‖=
      (eLpNorm ((f : KernelQuotient→ℂ)-g.1) 2 (integralQuotientVolume globalKubotaKernel)).toReal := by
    rw [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    exact (Lp.coeFn_sub _ _).trans ((Filter.EventuallyEq.refl _ _).sub
      (kernelSmoothTests_memLp g).coeFn_toLp)
  rw [dist_eq_norm,he]
  exact lt_of_le_of_lt ((ENNReal.toReal_mono (by simp) hg).trans_eq (ENNReal.toReal_ofReal (by positivity)))
    (by linarith)

end

open Filter MeasureTheory
open scoped Classical Topology ContDiff Manifold ENNReal

lemma hyperbolicSpatialChart_symm_eq {p : SpatialCoordinates}
    (hp : p∈hyperbolicSpatialChart.target) :
    hyperbolicSpatialChart.symm p=upperPoint (spatialHorizontal p) (p 2)
      (hyperbolicSpatialChart_target_positive hp) := by
  have h := hyperbolicSpatialCoordinates_reconstruct (hyperbolicSpatialChart.symm p)
  have he : hyperbolicSpatialCoordinates (hyperbolicSpatialChart.symm p)=p :=
    hyperbolicSpatialChart.right_inv hp
  simpa only [he,spatialHorizontal] using h.symm

end CubicEisenstein

open scoped Classical SchwartzMap
namespace InitialMeanSquare

section
open ActualEisensteinCubic SecondPassArithmetic
open SecondPassIntegration (elementNorm)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

variable (hp : ∀i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

end

lemma normCharacter_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (a : O) :
    ‖normCharacter χ a‖≤1 := χ.norm_le_one _

end
section

open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm columnLog)
open SecondPassIntegration (elementNorm)

section
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
end

end

open MeasureTheory
open scoped Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (columnLog)

end InitialMeanSquare

namespace SecondPassArithmetic
open ActualEisensteinCubic

theorem descent_ideal_inverse_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀ I∈S,(Ideal.absNorm I : ℝ)≤H) :
    (∑ I∈S,1/(Ideal.absNorm I : ℝ))≤128*Real.exp 1*(normLogBin H+1 : ℝ) := by
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I : ℝ) := by
    pm_5453 Nat.one_le_iff_ne_zero.mpr I hI
  let T := Finset.range (normLogBin H+1)
  let bin (j : ℕ) := S.filter (fun I=> normLogBin (Ideal.absNorm I)=j)
  have hmap : ∀ I∈S,normLogBin (Ideal.absNorm I : ℝ)∈T := by
    intro I hI
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (normLogBin_mono (by linarith [hpos I hI]) (hH I hI)))
  have hbin (j : ℕ) : (∑ I∈bin j,1/(Ideal.absNorm I : ℝ))≤128*Real.exp 1 := by
    have hp := normLogScale_pos j
    have hone := normLogScale_ge_one j
    have he := Real.one_le_exp (show (0 : ℝ)≤1 by norm_num)
    have hc : ((bin j).card : ℝ)≤128*(normLogScale j*Real.exp 1) := by
      apply DescentFiberCost.finite_ideal_count_real _ _ (by nlinarith)
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        simpa only [hj] using (normLogBin_scale_bounds (Ideal.absNorm I : ℝ) (hpos I hIS)).2
    have ht (I : Ideal O) (hI : I∈bin j) : 1/(Ideal.absNorm I : ℝ)≤1/normLogScale j := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (normLogBin_scale_bounds (Ideal.absNorm I : ℝ) (hpos I hIS)).1
      rw [hj] at hb
      exact one_div_le_one_div_of_le hp hb
    calc
      _ ≤ ∑ _I∈bin j,1/normLogScale j := Finset.sum_le_sum ht
      _ = ((bin j).card : ℝ)/normLogScale j := by simp [div_eq_mul_inv]
      _ ≤ (128*(normLogScale j*Real.exp 1))/normLogScale j := div_le_div_of_nonneg_right hc hp.le
      _ = _ := by field_simp
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ _j∈T,128*Real.exp 1 := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp [T]; ring

theorem descent_normLogBin_small_power (ε : ℝ) (hε : 0<ε) (H : ℝ) (hH : 1≤H) :
    (normLogBin H+1 : ℝ)≤(1+1/ε)*H^ε := by
  have hH0 : 0<H := by linarith
  have hb : (normLogBin H : ℝ)≤Real.log H := Nat.floor_le (Real.log_nonneg hH)
  have hl := Real.log_le_rpow_div hH0.le hε
  have hp := Real.one_le_rpow hH hε.le
  calc
    _ ≤ H^ε/ε+1 := by linarith
    _ ≤ H^ε/ε+H^ε := add_le_add le_rfl hp
    _ = _ := by ring

open FirstPassCubeLabels (primeProductNorm primeProduct aLabel squarefreeLabel b0Label j2Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]

def cubeProductIdeal (x : CubeCoordinates ι) : Ideal O :=
  Ideal.span {primeProduct p x.support x.leftExponent}*
    Ideal.span {primeProduct p x.support x.rightExponent}

def cubeParityKey (x : CubeCoordinates ι) : Ideal O × Ideal O :=
  (Ideal.span {squarefreeLabel p x.support (fun i => x.leftExponent i+x.rightExponent i)},
   Ideal.span {(b0Label p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit*
     j2Label p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit)})

def cubeDivisorKey (x : CubeCoordinates ι) : Fin 3 → Ideal O :=
  ![Ideal.span {primeProduct p x.support x.leftExponent},
    Ideal.span {aLabel p x.support x.leftBit},Ideal.span {aLabel p x.support x.rightBit}]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeParityKey_product (x : CubeCoordinates ι) :
    cubeProductIdeal p x=(cubeParityKey p x).2^2*(cubeParityKey p x).1 := by
  have h := FirstPassCubeLabels.cube_pair_product_decomposition p x.support
    x.leftExponent x.rightExponent x.leftBit x.rightBit x.support_pos
  have h' := congrArg (fun z : O => (Ideal.span {z} : Ideal O)) h
  simp only [cubeProductIdeal,cubeParityKey,pow_two,←Ideal.span_singleton_mul_span_singleton] at h' ⊢
  convert h' using 1 ; congr 1 ; ring

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeDivisorKey_dvd (x : CubeCoordinates ι) (i : Fin 3) :
    cubeDivisorKey p x i ∣ cubeProductIdeal p x := by
  pm_7363 hA1 x.leftBit
  pm_7363 hA2 x.rightBit
  rw [primeProduct_add,←Ideal.span_singleton_mul_span_singleton] at hA1 hA2
  fin_cases i
  · exact dvd_mul_right _ _
  · exact hA1
  · exact hA2

variable (hp : ∀ i,p i≠0)
include hp

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeParityKey_ne_zero (x : CubeCoordinates ι) :
    (cubeParityKey p x).1≠0 ∧ (cubeParityKey p x).2≠0 := by
  constructor
  · exact (Ideal.span_singleton_eq_bot.not).mpr (primeProduct_ne_zero p hp _ _)
  · exact (Ideal.span_singleton_eq_bot.not).mpr
      (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))

variable (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem cubeDivisorKey_injective_on_product {x y : CubeCoordinates ι}
    (hx : x.Admissible) (hy : y.Admissible)
    (hprod : cubeProductIdeal p x=cubeProductIdeal p y)
    (hk : cubeDivisorKey p x=cubeDivisorKey p y) : x=y := by
  have h1 := congrFun hk 0
  have hA1 := congrFun hk 1
  have hA2 := congrFun hk 2
  change Ideal.span {primeProduct p x.support x.leftExponent}=
    Ideal.span {primeProduct p y.support y.leftExponent} at h1
  have h2 : Ideal.span {primeProduct p x.support x.rightExponent}=
    Ideal.span {primeProduct p y.support y.rightExponent} := by
    apply mul_left_cancel₀ ((Ideal.span_singleton_eq_bot.not).mpr (primeProduct_ne_zero p hp x.support x.leftExponent))
    simpa only [cubeProductIdeal,h1] using hprod
  have hv1 := primeProduct_span_exponents_eq p hinj x.support y.support
    x.leftExponent y.leftExponent x.left_off y.left_off h1
  have hv2 := primeProduct_span_exponents_eq p hinj x.support y.support
    x.rightExponent y.rightExponent x.right_off y.right_off h2
  change Ideal.span {aLabel p x.support x.leftBit}=Ideal.span {aLabel p y.support y.leftBit} at hA1
  change Ideal.span {aLabel p x.support x.rightBit}=Ideal.span {aLabel p y.support y.rightBit} at hA2
  pm_8465 CubeCoordinates.aLabel_left hA1
  pm_8465 CubeCoordinates.aLabel_right hA2
  exact CubeCoordinates.ext (Finsupp.ext (congrFun hv1)) (Finsupp.ext (congrFun hv2))
    (FirstCauchyArithmetic.family_product_injective _ hinj hA1)
    (FirstCauchyArithmetic.family_product_injective _ hinj hA2)

theorem cubeParityKey_fiber_card (s : Finset (CubeCoordinates ι)) (q : Ideal O × Ideal O)
    (hq1 : q.1≠0) (hq2 : q.2≠0) (hs : ∀ x∈s,x.Admissible)
    (hk : ∀ x∈s,cubeParityKey p x=q) :
    s.card≤(idealDivisors (q.2^2*q.1)).card^3 := by
  let D := idealDivisors (q.2^2*q.1)
  have hprod0 : q.2^2*q.1≠0 := mul_ne_zero (pow_ne_zero _ hq2) hq1
  let encode (x : s) : Fin 3 → D := fun i => ⟨cubeDivisorKey p x.val i,by
    apply (mem_idealDivisors hprod0).mpr
    have h := cubeDivisorKey_dvd p x.val i
    simpa only [cubeParityKey_product,hk x.val x.property] using h⟩
  have hi : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    apply cubeDivisorKey_injective_on_product p hp hinj (hs _ x.property) (hs _ y.property)
    · simp only [cubeParityKey_product,hk _ x.property,hk _ y.property]
    · funext i
      exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin,D] using Fintype.card_le_of_injective encode hi

end SecondPassArithmetic

end

end OAI
