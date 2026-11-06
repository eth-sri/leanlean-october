module
public import OAI.NumberTheory.DirichletL.Eisenstein.CutoffApproximation
public import OAI.NumberTheory.DirichletL.Eisenstein.ConjugateLevelAction
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

def cubicEisensteinResidue : KernelQuotientL2 :=
  kernelEisensteinResidueVector 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_nonzero_character :
    cubicEisensteinResidue≠0 ∧
      ∀M : CubicKubota.levelThree,kernelLevelPullback M cubicEisensteinResidue=
        CubicKubota.complexCharacter M • cubicEisensteinResidue := by
  pm_7709 kernelEisensteinResidueVector_nonzero_character_of_initial_overlap
  pm_6979

lemma cubicEisensteinResidue_character (M : CubicKubota.levelThree) :
    kernelLevelPullback M cubicEisensteinResidue=
      CubicKubota.complexCharacter M • cubicEisensteinResidue :=
  cubicEisensteinResidue_nonzero_character.2 M

lemma cubicEisensteinResidue_eigenvector :
    (cubicEisensteinResidue,(8/9:ℂ) • cubicEisensteinResidue)∈kernelEnergyLaplacian.graph :=
  kernelEisensteinResidueVector_graph 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_cusp_average :
    kernelCuspStripAverage cubicEisensteinResidue=cuspConstantAverageResidue := by
  pm_7709 kernelEisensteinResidueVector_average_of_overlap
  apply kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num) s (by linarith)
  pm_6979

section
variable (S : Set KernelQuotient) (hS : IsCompact S)
include S hS
lemma cubicEisensteinResidue_local_limit :
    Tendsto (fun s : ℂ => (s-4/3) •
      kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num) s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (kernelMassRestrictionCLM S hS.measurableSet cubicEisensteinResidue)) :=
  kernelLocalCorrectedSeed_residue_limit S hS 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinLocalFamily_initial_ae
    (s : ℂ) (hs : 4< s.re) (hi : 0< s.im) :
    (kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num) s : KernelQuotient→ℂ)
      =ᵐ[integralQuotientVolume globalKubotaKernel]
        S.indicator (kernelQuotientEisenstein s (by linarith)) := by
  have hlocal := kernelLocalCorrectedSeed_ae_eq S hS 2 3 (by norm_num) (by norm_num) s
  have hoverlap := kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi
  filter_upwards [hlocal,hoverlap] with q hq hc
  rw [hq]
  by_cases hmem : q∈S
  · rw [Set.indicator_of_mem hmem,Set.indicator_of_mem hmem]
    change kernelQuotientSeed 2 3 s q+kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s q=_
    rw [hc]
    ring
  simp_all
end

end

section
open Filter MeasureTheory
open scoped Classical Topology

def whittakerHeight (v : ℝ) : ℝ := max 5 v
def whittakerBase (p : ℝ × ℂ) : ℝ := whittakerHeight p.1*(1+‖p.2‖^2)
def whittakerIntegrand (freq s : ℂ) (p : ℝ × ℂ) : ℂ :=
  (whittakerHeight p.1:ℂ)⁻¹*(whittakerBase p:ℂ)^(-s)*
    ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2)
def whittakerIntegrandDeriv (freq s : ℂ) (p : ℝ × ℂ) : ℂ :=
  -(Real.log (whittakerBase p):ℂ)*whittakerIntegrand freq s p
def whittakerProductVolume : Measure (ℝ × ℂ) :=
  (volume.restrict (Set.Icc (5:ℝ) 6)).prod volume

lemma whittakerHeight_ge_one (v : ℝ) : 1≤whittakerHeight v := by
  exact (by norm_num : (1:ℝ)≤5).trans (le_max_left _ _)

section
variable (p : ℝ × ℂ)
include p
lemma whittakerBase_ge : 1+‖p.2‖^2≤whittakerBase p := by
  exact le_mul_of_one_le_left (by positivity) (whittakerHeight_ge_one p.1)

lemma whittakerBase_ge_one : 1≤whittakerBase p :=
  (by nlinarith [sq_nonneg ‖p.2‖] : 1≤1+‖p.2‖^2).trans (whittakerBase_ge p)

lemma whittakerBase_pos : 0<whittakerBase p :=
  zero_lt_one.trans_le (whittakerBase_ge_one p)
end

section
variable (freq s : ℂ)
include freq s
lemma whittakerIntegrand_continuous : Continuous (whittakerIntegrand freq s) := by
  have hv : Continuous (fun p : ℝ × ℂ => whittakerHeight p.1) := by
    unfold whittakerHeight
    fun_prop
  have hb : Continuous whittakerBase := by unfold whittakerBase; fun_prop
  have hp : Continuous (fun p : ℝ × ℂ => (whittakerBase p:ℂ)^(-s)) :=
    (Complex.continuous_ofReal.comp hb).cpow continuous_const
      (fun p => Complex.ofReal_mem_slitPlane.mpr (whittakerBase_pos p))
  have hi : Continuous (fun p : ℝ × ℂ => (whittakerHeight p.1:ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp hv).inv₀ (fun p => by
      change (whittakerHeight p.1:ℂ)≠0
      exact_mod_cast (zero_lt_one.trans_le (whittakerHeight_ge_one p.1)).ne')
  have hc : Continuous (fun p : ℝ × ℂ =>
      ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2)) := by
    change Continuous (fun p : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-(freq*whittakerHeight p.1)*p.2)+starRingEnd ℂ (-(freq*whittakerHeight p.1)*p.2))))
    fun_prop
  exact (hi.mul hp).mul hc

lemma whittakerIntegrandDeriv_continuous : Continuous (whittakerIntegrandDeriv freq s) := by
  pm_5020 hb whittakerBase whittakerHeight
  have hl : Continuous (fun p => Real.log (whittakerBase p)) :=
    hb.log (fun p => (whittakerBase_pos p).ne')
  exact (Complex.continuous_ofReal.comp hl).neg.mul (whittakerIntegrand_continuous freq s)

lemma whittakerIntegrand_hasDerivAt (p : ℝ × ℂ) :
    HasDerivAt (fun w => whittakerIntegrand freq w p) (whittakerIntegrandDeriv freq s p) s := by
  have hn : (whittakerBase p:ℂ)≠0 := by exact_mod_cast (whittakerBase_pos p).ne'
  have hh := (((hasDerivAt_id s).neg.const_cpow (Or.inl hn)).const_mul
    ((whittakerHeight p.1:ℂ)⁻¹)).mul_const
      (ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2))
  convert hh using 1
  · rfl
  · rw [←Complex.ofReal_log (whittakerBase_pos p).le]
    unfold whittakerIntegrandDeriv whittakerIntegrand
    simp only [Pi.neg_apply,id_eq]
    ring

lemma whittakerIntegrand_norm (p : ℝ × ℂ) :
    ‖whittakerIntegrand freq s p‖=(whittakerHeight p.1)⁻¹*(whittakerBase p)^(-s.re) := by
  unfold whittakerIntegrand
  rw [norm_mul,norm_mul,breveE_norm,mul_one,norm_inv,
    Complex.norm_of_nonneg (zero_lt_one.trans_le (whittakerHeight_ge_one p.1)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos (whittakerBase_pos p)]
  rfl

lemma whittakerIntegrand_norm_bound (p : ℝ × ℂ)
    (b : ℝ) (hb : 0≤b) (hs : b≤ s.re) :
    ‖whittakerIntegrand freq s p‖≤(1+‖p.2‖^2)^(-b) := by
  rw [whittakerIntegrand_norm]
  calc
    _ ≤ (whittakerBase p)^(-s.re) := by
      exact mul_le_of_le_one_left (Real.rpow_nonneg (whittakerBase_pos p).le _)
        (inv_le_one_of_one_le₀ (whittakerHeight_ge_one p.1))
    _ ≤ (whittakerBase p)^(-b) :=
      Real.rpow_le_rpow_of_exponent_le (whittakerBase_ge_one p) (by linarith)
    _ ≤ (1+‖p.2‖^2)^(-b) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (whittakerBase_ge p) (by linarith)

lemma whittakerIntegrandDeriv_norm_bound (p : ℝ × ℂ)
    (b ε : ℝ) (hb : 0≤b) (hε : 0<ε) (hs : b+ε≤ s.re) :
    ‖whittakerIntegrandDeriv freq s p‖≤ε⁻¹*(1+‖p.2‖^2)^(-b) := by
  have hlog := Real.log_nonneg (whittakerBase_ge_one p)
  unfold whittakerIntegrandDeriv
  rw [norm_mul,norm_neg,Complex.norm_of_nonneg hlog,whittakerIntegrand_norm]
  calc
    _ ≤ Real.log (whittakerBase p)*(whittakerBase p)^(-s.re) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (Real.rpow_nonneg (whittakerBase_pos p).le _)
          (inv_le_one_of_one_le₀ (whittakerHeight_ge_one p.1))) hlog
    _ ≤ ((whittakerBase p)^ε/ε)*(whittakerBase p)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (Real.log_le_rpow_div (whittakerBase_pos p).le hε)
        (Real.rpow_nonneg (whittakerBase_pos p).le _)
    _ = ε⁻¹*(whittakerBase p)^(ε-s.re) := by
      rw [Real.rpow_sub (whittakerBase_pos p),Real.rpow_neg (whittakerBase_pos p).le]
      ring
    _ ≤ ε⁻¹*(whittakerBase p)^(-b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (whittakerBase_ge_one p) (by linarith)) (by positivity)
    _ ≤ ε⁻¹*(1+‖p.2‖^2)^(-b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) (whittakerBase_ge p) (by linarith)) (by positivity)
end

lemma whittaker_bound_integrable (b : ℝ) (hb : 1<b) :
    Integrable (fun p : ℝ × ℂ => (1+‖p.2‖^2)^(-b)) whittakerProductVolume := by
  pm_3594
  have hv : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Set.Icc (5:ℝ) 6)) := integrable_const _
  unfold whittakerProductVolume
  simpa only [one_mul] using hv.mul_prod hk

lemma whittakerIntegrand_integrable (freq s : ℂ) (hs : 1< s.re) :
    Integrable (whittakerIntegrand freq s) whittakerProductVolume := by
  exact (whittaker_bound_integrable s.re hs).mono'
    (whittakerIntegrand_continuous freq s).aestronglyMeasurable
    (Eventually.of_forall (fun p => whittakerIntegrand_norm_bound freq s p s.re (by linarith) le_rfl))

lemma whittakerProduct_differentiableAt (freq s : ℂ) (hs : 1< s.re) :
    DifferentiableAt ℂ (fun w => ∫p,whittakerIntegrand freq w p∂ whittakerProductVolume) s := by
  pm_3595
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := whittakerProductVolume) (F := whittakerIntegrand freq)
    (F' := whittakerIntegrandDeriv freq)
    (bound := fun p => ε⁻¹*(1+‖p.2‖^2)^(-b)) hU
    (Eventually.of_forall (fun w => (whittakerIntegrand_continuous freq w).aestronglyMeasurable))
    (whittakerIntegrand_integrable freq s hs)
    (whittakerIntegrandDeriv_continuous freq s).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => whittakerIntegrandDeriv_norm_bound freq w p b ε (by linarith) hε hw.le))
    ((whittaker_bound_integrable b hb).const_mul ε⁻¹)
    (Eventually.of_forall (fun p w _ => whittakerIntegrand_hasDerivAt freq w p))
  exact h.2.differentiableAt

section
variable (freq s : ℂ)
include freq s
lemma whittakerIntegrand_eq (v : ℝ) (hv : 5≤v) (z : ℂ) :
    whittakerIntegrand freq s (v,z)=
      (v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
  have hvp : 0<v := by linarith
  pm_3596 hvn v hvp.ne'
  have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(-s)*(v:ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hvn,Complex.cpow_one,div_eq_mul_inv]
  unfold whittakerIntegrand whittakerBase whittakerHeight hyperbolicKernel
  simp only [max_eq_right hv,Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hvp.le (by positivity),hp]
  ring

lemma whittakerProduct_eq_average (hs : 1< s.re) :
    (∫p,whittakerIntegrand freq s p∂ whittakerProductVolume)=
      ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := whittakerIntegrand_integrable freq s hs
  unfold whittakerProductVolume at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  calc
    _ = ∫z : ℂ,(v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => whittakerIntegrand_eq freq s v hv.1 z)
    _ = _ := integral_const_mul _ _

theorem cuspWhittakerAverage_differentiableAt (hs : 1< s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have he : (fun w => ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v))
      =ᶠ[𝓝 s](fun w => ∫p,whittakerIntegrand freq w p∂ whittakerProductVolume) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact (whittakerProduct_eq_average freq w hw).symm
  exact (whittakerProduct_differentiableAt freq s hs).congr_of_eventuallyEq he
end

end

section
open scoped Classical

open ActualEisensteinCubic ConcreteTraceCRT

section
variable (h : ActualEisensteinCubic.O)
include h
lemma arithmeticDirichletTerm_differentiable (c : LevelLower) :
    Differentiable ℂ (fun s : ℂ => arithmeticDirichletTerm s h c) := by pm_3081

lemma arithmeticDirichletTerm_norm_mono
    (a : ℝ) (s : ℂ) (ha : a≤ s.re) (c : LevelLower) :
    ‖arithmeticDirichletTerm s h c‖≤‖arithmeticDirichletTerm (a:ℂ) h c‖ := by pm_3082

theorem arithmeticDirichletSeries_differentiableAt
    (s : ℂ) (hs : 2< s.re) :
    DifferentiableAt ℂ (fun z => arithmeticDirichletSeries z h) s := by
  let a : ℝ := (2+s.re)/2
  have ha : 2<a := by dsimp [a]; linarith
  pm_890
  have hsum := arithmeticDirichletTerm_summable_norm (a:ℂ) (by simpa using ha) h
  pm_3083
  have hd : DifferentiableOn ℂ (fun z => arithmeticDirichletSeries z h) {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun c => (arithmeticDirichletTerm_differentiable h c).differentiableOn) hopen
    intro c z hz
    exact arithmeticDirichletTerm_norm_mono h a z hz.le c
  pm_5615

theorem scatteringCoefficient_differentiableAt
    (s : ℂ) (hs : 2< s.re) :
    DifferentiableAt ℂ (fun z => scatteringCoefficient z h) s :=
  (arithmeticDirichletSeries_differentiableAt h s hs).div_const _

theorem scatteringCoefficient_analyticOnNhd :
    AnalyticOnNhd ℂ (fun z => scatteringCoefficient z h) {z : ℂ | 2<z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (scatteringCoefficient_differentiableAt h z hz).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
end

end

section
open Filter MeasureTheory
open scoped Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal

local notation "O" => ActualEisensteinCubic.O

lemma cuspPeriodStrip_measure_ne_top : hyperbolicVolume (cuspPeriodStrip 5 6)≠(⊤:ℝ≥0∞) := by
  pm_4921
  have hh := hm.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simp only [Set.preimage_univ,Measure.restrict_apply_univ] at hh
  rw [hh]
  exact measure_ne_top _ _

instance cuspStripFiniteVolume : IsFiniteMeasure (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) :=
  isFiniteMeasure_restrict.mpr cuspPeriodStrip_measure_ne_top

abbrev CuspStripL2 := Lp ℂ 2 (hyperbolicVolume.restrict (cuspPeriodStrip 5 6))

def kernelCuspPullback : KernelQuotientL2→L[ℂ]CuspStripL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    (kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num))).toContinuousLinearMap.comp
    (LpToLpRestrictCLM KernelQuotient ℂ ℂ (integralQuotientVolume globalKubotaKernel) 2 kernelCuspStripSet)

lemma kernelCuspPullback_ae_eq (F : KernelQuotientL2) :
    kernelCuspPullback F=ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip 5 6)]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  pm_4921
  have hr := LpToLpRestrictCLM_coeFn ℂ kernelCuspStripSet F
  have hc := hm.quasiMeasurePreserving.ae_eq_comp hr
  have hp := Lp.coeFn_compMeasurePreserving
    (LpToLpRestrictCLM KernelQuotient ℂ ℂ (integralQuotientVolume globalKubotaKernel) 2 kernelCuspStripSet F) hm
  filter_upwards [hp,hc] with w hw hc
  exact hw.trans hc

def cuspFourierPhase (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) : ℂ :=
  ShortDraftTrace.breveE (-cuspFrequency h*hyperbolicHorizontal w)

section
variable (h : ActualEisensteinCubic.O)
include h
lemma cuspFourierPhase_continuous : Continuous (cuspFourierPhase h) := by
  have hc : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency h*z)+starRingEnd ℂ (-cuspFrequency h*z))))
    fun_prop
  exact hc.comp hyperbolicHorizontal_continuous

lemma cuspFourierPhase_norm (w : HyperbolicSpace) : ‖cuspFourierPhase h w‖=1 :=
  breveE_norm _

lemma cuspFourierTest_memLp :
    MemLp (fun w => star (cuspFourierPhase h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) := by
  apply MemLp.of_bound (cuspFourierPhase_continuous h).star.aestronglyMeasurable 1
  exact Eventually.of_forall (fun w => by rw [norm_star,cuspFourierPhase_norm])
end

def cuspFourierTestL2 (h : ActualEisensteinCubic.O) : CuspStripL2 :=
  (cuspFourierTest_memLp h).toLp (fun w => star (cuspFourierPhase h w))

def kernelCuspFourier (h : ActualEisensteinCubic.O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspFourierTestL2 h)).comp kernelCuspPullback

lemma kernelCuspFourier_integral (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspFourier h F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)*cuspFourierPhase h w∂ hyperbolicVolume := by
  change inner ℂ (cuspFourierTestL2 h) (kernelCuspPullback F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspFourierTest_memLp h),kernelCuspPullback_ae_eq F] with w hw hp
  pm_7424 cuspFourierTestL2

lemma kernelCuspFourier_restrict (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspFourier h (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspFourier h F := by
  rw [kernelCuspFourier_integral,kernelCuspFourier_integral]
  pm_4921
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelMassRestriction_coe kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet F)
    (s := kernelCuspStripSet))
  pm_3597

def kernelCuspFourierFamily (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : ℂ :=
  kernelCuspFourier h
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)

section
variable (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b)
include h a b ha hab
lemma kernelCuspFourierFamily_residue_limit :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspFourierFamily h a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspFourier h (kernelEisensteinResidueVector a b ha hab))) := by
  have hh := (kernelCuspFourier h).continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)
  pm_124 Function.comp_def map_smul smul_eq_mul kernelCuspFourier_restrict kernelCuspFourierFamily hh

lemma kernelCuspFourierFamily_actual_integral (s : ℂ) :
    kernelCuspFourierFamily h a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s (integralOrbitProjection globalKubotaKernel w)*
        cuspFourierPhase h w∂ hyperbolicVolume := by
  rw [kernelCuspFourierFamily,kernelCuspFourier_integral]
  pm_4921
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelLocalCorrectedSeed_ae_eq kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)
    (s := kernelCuspStripSet))
  pm_3597

lemma kernelCuspFourierFamily_of_initial_overlap
    (s : ℂ) (hs : 2< s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspFourierFamily h a b ha hab s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s w*cuspFourierPhase h w∂ hyperbolicVolume := by
  pm_3582
  have hp := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hcorrected (s := kernelCuspStripSet))
  rw [kernelCuspFourierFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [hp] with w hw
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (kernelQuotientEisenstein_mk s hs w))
end

end

section
open Filter MeasureTheory
open scoped Classical Topology MatrixGroups

local notation "O" => ActualEisensteinCubic.O

lemma hyperbolicEisenstein_cusp_fourier_average (s : ℂ) (hs : 2< s.re) (h : ActualEisensteinCubic.O) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspFourierPhase h w∂ hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((if h=0 then (v:ℂ)^s else 0)+
          (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h)*
          ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3 := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspFourierPhase h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspFourierPhase_continuous h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  pm_3634
  have hh : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
      cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    rw [eisensteinFourierCoefficient]
    exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
  dsimp only
  rw [hh,eisensteinFourierCoefficient_formula v hpos s hs h]

def cuspWhittakerHeightFactor (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)

lemma hyperbolicEisenstein_cusp_fourier_nonzero (s : ℂ) (hs : 2< s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspFourierPhase h w∂ hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h := by
  rw [hyperbolicEisenstein_cusp_fourier_average s hs h]
  simp only [ite_eq_right hh,zero_add]
  have heq : (∫v in Set.Icc (5:ℝ) 6,
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h)*
        ((9*Real.sqrt 3/2:ℝ):ℂ)/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          ((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)) := by
    pm_1163
    pm_3598
    dsimp only
    rw [hp]
    ring
  rw [heq,integral_const_mul]
  rfl

lemma kernelCuspFourierFamily_nonzero_of_initial_overlap (h : ActualEisensteinCubic.O) (hh : h≠0)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : 2< s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspFourierFamily h a b ha hab s =
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h := by
  rw [kernelCuspFourierFamily_of_initial_overlap h a b ha hab s hs hoverlap,
    hyperbolicEisenstein_cusp_fourier_nonzero s hs h hh]

end

open Filter MeasureTheory
open scoped Classical Topology

local notation "O" => ActualEisensteinCubic.O

lemma sourceFourierKernel_continuous_freq (s : ℂ) (hs : 1< s.re) :
    Continuous (sourceFourierKernel s) := by
  change Continuous (fun freq : ℂ => ∫z : ℂ,hyperbolicKernel s z*ShortDraftTrace.breveE (-freq*z))
  apply continuous_of_dominated (bound := fun z => ‖hyperbolicKernel s z‖)
  · exact fun freq => (sourceFourierKernel_integrable s freq hs).aestronglyMeasurable
  · exact fun freq => Eventually.of_forall (fun z => by rw [norm_mul,breveE_norm,mul_one])
  · exact (hyperbolicKernel_integrable s hs).norm
  · filter_upwards with z
    change Continuous (fun freq : ℂ => hyperbolicKernel s z*
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop

lemma schlafliIntegrand_real (nu x t : ℝ) (ht : 0<t) :
    (t:ℂ)^((nu:ℂ)-1)*Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t))=
      ((t^(nu-1)*Real.exp (-t-x^2/(4*t)):ℝ):ℂ) := by
  have hp := Complex.ofReal_cpow ht.le (nu-1)
  simp only [Complex.ofReal_sub,Complex.ofReal_one] at hp
  rw [Complex.ofReal_mul,hp,Complex.ofReal_exp]
  congr 2
  push_cast
  rfl

lemma schlafliIntegral_real_re_pos (nu x : ℝ) (hnu : 0<nu) :
    0<(schlafliIntegral (nu:ℂ) x).re := by
  let f : ℝ→ℂ := fun t => (t:ℂ)^((nu:ℂ)-1)*Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t))
  have hi : IntegrableOn f (Set.Ioi (0:ℝ)) volume := schlafliIntegral_integrable (nu:ℂ) x hnu
  have hp (t : ℝ) (ht : 0<t) : 0<(f t).re := by
    rw [show f t=((t^(nu-1)*Real.exp (-t-x^2/(4*t)):ℝ):ℂ) from schlafliIntegrand_real nu x t ht,
      Complex.ofReal_re]
    exact mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  change 0<RCLike.re (∫t in Set.Ioi (0:ℝ),f t)
  pm_7526
  · have heq : Function.support (fun t => RCLike.re (f t))=ᵐ[volume.restrict (Set.Ioi (0:ℝ))] Set.univ := by
      pm_7594 measurableSet_Ioi t ht
    rw [measure_congr heq,Measure.restrict_apply_univ]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hp t ht).le

lemma sourceFourierKernel_real_re_pos (sigma : ℝ) (hsigma : 1< sigma) (freq : ℂ) :
    0<(sourceFourierKernel (sigma:ℂ) freq).re := by
  have hh := sourceFourierKernel_gamma_schlafli (sigma:ℂ) freq hsigma
  have hre := congrArg Complex.re hh
  have hsch : 0<(schlafliIntegral ((sigma:ℂ)-1) (4*Real.pi*‖freq‖)).re := by
    convert schlafliIntegral_real_re_pos (sigma-1) (4*Real.pi*‖freq‖) (by linarith) using 1 ; push_cast ; rfl
  rw [Complex.Gamma_ofReal] at hre
  pm_1189 Complex.mul_re Complex.ofReal_re Complex.ofReal_im mul_zero zero_mul sub_zero hre
  have hg := Real.Gamma_pos_of_pos (show 0< sigma by linarith)
  have hp := mul_pos Real.pi_pos hsch
  nlinarith

lemma cuspWhittakerHeightFactor_integrable (s : ℂ) (hs : 1< s.re) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))
      (Set.Icc (5:ℝ) 6) volume := by
  apply ContinuousOn.integrableOn_Icc
  intro v hv
  pm_3634
  exact ((Complex.continuousAt_ofReal_cpow_const v (-s-1) (Or.inr hpos.ne')).mul
    ((sourceFourierKernel_continuous_freq s hs).continuousAt.comp
      ((Complex.continuous_ofReal.const_mul (cuspFrequency h)).continuousAt))).continuousWithinAt

lemma cuspWhittakerHeightFactor_real_re_pos (sigma : ℝ) (hsigma : 1< sigma) (h : ActualEisensteinCubic.O) :
    0<(cuspWhittakerHeightFactor (sigma:ℂ) h).re := by
  let f : ℝ→ℂ := fun v => (v:ℂ)^(-(sigma:ℂ)-1)*sourceFourierKernel (sigma:ℂ) (cuspFrequency h*v)
  have hi : IntegrableOn f (Set.Icc (5:ℝ) 6) volume :=
    cuspWhittakerHeightFactor_integrable (sigma:ℂ) hsigma h
  have hp (v : ℝ) (hv : v∈Set.Icc (5:ℝ) 6) : 0<(f v).re := by
    pm_3634
    have he := Complex.ofReal_cpow hpos.le (-sigma-1)
    simp only [Complex.ofReal_sub,Complex.ofReal_neg,Complex.ofReal_one] at he
    change 0<((v:ℂ)^(-(sigma:ℂ)-1)*sourceFourierKernel (sigma:ℂ) (cuspFrequency h*v)).re
    rw [←he,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_pos (Real.rpow_pos_of_pos hpos _) (sourceFourierKernel_real_re_pos sigma hsigma _)
  change 0<RCLike.re (∫v in Set.Icc (5:ℝ) 6,f v)
  pm_7526
  · have heq : Function.support (fun v => RCLike.re (f v))=ᵐ[volume.restrict (Set.Icc (5:ℝ) 6)] Set.univ := by
      pm_7594 measurableSet_Icc v hv
    rw [measure_congr heq,Measure.restrict_apply_univ]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (hp v hv).le

lemma cuspWhittakerHeightFactor_center_ne_zero (h : ActualEisensteinCubic.O) :
    cuspWhittakerHeightFactor (4/3:ℂ) h≠0 := by
  intro he
  have hh := cuspWhittakerHeightFactor_real_re_pos (4/3:ℝ) (by norm_num) h
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hh
  pm_6376 hh

end CubicEisenstein

end

end OAI
